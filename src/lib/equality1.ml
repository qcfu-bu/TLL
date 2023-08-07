open Bindlib
open Names
open Syntax1
open Context1

let rec whnf ?(expand = true) (ctx : Ctx.t) = function
  (* inference *)
  | Ann (m, a) -> whnf ~expand ctx m
  (* core *)
  | Var x when expand -> (
    match Ctx.find_var1 x ctx with
    | Some m -> whnf ~expand ctx m
    | _ -> Var x)
  | Const (x, ss) when expand -> (
    match Ctx.find_const x ctx with
    | Some sch ->
      let m, _ = msubst sch (Array.of_list ss) in
      whnf ~expand ctx m
    | _ -> Const (x, ss))
  | App _ as m -> (
    let hd, ms = unApps m in
    let hd = whnf ~expand ctx hd in
    let ms = List.map (whnf ~expand ctx) ms in
    match hd with
    | Fun (_, bnd) -> (
      let cls = subst bnd hd in
      match match_cls cls ms with
      | Some (Some rhs, rst) -> whnf ~expand ctx (mkApps rhs rst)
      | _ -> mkApps hd ms)
    | _ -> mkApps hd ms)
  | Let (_, m, bnd) ->
    let m = whnf ~expand ctx m in
    whnf ~expand ctx (subst bnd m)
  (* inductive *)
  | Match (ms, a, cls) -> (
    let ms = List.map (whnf ~expand ctx) ms in
    match match_cls cls ms with
    | Some (Some rhs, []) -> whnf ~expand ctx rhs
    | _ -> Match (ms, a, cls))
  (* monadic *)
  | MLet (m, bnd) -> (
    let m = whnf ~expand ctx m in
    match m with
    | Return m ->
      let m = whnf ~expand ctx m in
      whnf ~expand ctx (subst bnd m)
    | _ -> MLet (m, bnd))
  (* other *)
  | m -> m

and match_cls cls ms =
  let rec gather_args p0s ms =
    match (p0s, ms) with
    | [], ms -> Some ([], ms)
    | p0s, [] -> None
    | _ :: p0s, m :: ms -> (
      match gather_args p0s ms with
      | Some (ms, ns) -> Some (m :: ms, ns)
      | None -> None)
  in
  List.fold_left
    (fun acc_opt ((p0s, bnd) as cl) ->
      match acc_opt with
      | Some _ -> acc_opt
      | None -> (
        match gather_args p0s ms with
        | Some (ms, ns) -> (
          try Some (psubst cl ms, ns) with
          | _ -> None)
        | None -> None))
    None cls

let rec eq_sort s1 s2 =
  match (s1, s2) with
  | SVar x, SVar y -> eq_vars x y
  | SMeta (x1, _), SMeta (x2, _) -> SMeta.equal x1 x2
  | _ -> s1 = s2

let rec aeq_tm m1 m2 =
  if m1 == m2 then
    true
  else
    match (m1, m2) with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) -> aeq_tm m1 m2 && aeq_tm a1 a2
    | IMeta (x1, _, _), IMeta (x2, _, _) -> IMeta.equal x1 x2
    (* core *)
    | Type s1, Type s2 -> eq_sort s1 s2
    | Var x1, Var x2 -> eq_vars x1 x2
    | Const (x1, ss1), Const (x2, ss2) ->
      Const.equal x1 x2 && List.equal eq_sort ss1 ss2
    | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2) ->
      relv1 = relv2 && eq_sort s1 s2 && aeq_tm a1 a2
      && eq_binder aeq_tm bnd1 bnd2
    | Fun (a1, bnd1), Fun (a2, bnd2) ->
      aeq_tm a1 a2
      && eq_binder (List.equal (eq_pbinder (Option.equal aeq_tm))) bnd1 bnd2
    | App (m1, n1), App (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) ->
      relv1 = relv2 && aeq_tm m1 m2 && eq_binder aeq_tm bnd1 bnd2
    (* inductive *)
    | Ind (ind1, ss1, ms1, ns1), Ind (ind2, ss2, ms2, ns2) ->
      Ind.equal ind1 ind2 && List.equal eq_sort ss1 ss2
      && List.equal aeq_tm ms1 ms2 && List.equal aeq_tm ns1 ns2
    | Constr (constr1, ss1, ms1, ns1), Constr (constr2, ss2, ms2, ns2) ->
      Constr.equal constr1 constr2
      && List.equal eq_sort ss1 ss2 && List.equal aeq_tm ms1 ms2
      && List.equal aeq_tm ns1 ns2
    | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
      List.equal aeq_tm ms1 ms2 && aeq_tm a1 a2
      && List.equal (eq_pbinder (Option.equal aeq_tm)) cls1 cls1
    (* monad *)
    | IO a1, IO a2 -> aeq_tm a1 a2
    | Return m1, Return m2 -> aeq_tm m1 m2
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      aeq_tm m1 m2 && eq_binder aeq_tm bnd1 bnd2
    (* magic *)
    | Magic _, _ -> true
    | _, Magic _ -> true
    (* other *)
    | _ -> false

let rec eq_tm ?(expand = false) ctx m1 m2 =
  let rec equal m1 m2 =
    if aeq_tm m1 m2 then
      true
    else
      let m1 = whnf ~expand ctx m1 in
      let m2 = whnf ~expand ctx m2 in
      match (m1, m2) with
      (* inference *)
      | IMeta (x1, _, _), IMeta (x2, _, _) -> IMeta.equal x1 x2
      (* core *)
      | Type s1, Type s2 -> eq_sort s1 s2
      | Var x1, Var x2 -> eq_vars x1 x2
      | Const (x1, ss1), Const (x2, ss2) ->
        Const.equal x1 x2 && List.equal eq_sort ss1 ss2
      | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2) ->
        relv1 = relv2 && eq_sort s1 s2 && equal a1 a2
        && eq_binder equal bnd1 bnd2
      | Fun (a1, bnd1), Fun (a2, bnd2) ->
        equal a1 a2
        && eq_binder (List.equal (eq_pbinder (Option.equal equal))) bnd1 bnd2
      | App (m1, n1), App (m2, n2) -> equal m1 m2 && equal n1 n2
      | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) ->
        relv1 = relv2 && equal m1 m2 && eq_binder equal bnd1 bnd2
      (* inductive *)
      | Ind (ind1, ss1, ms1, ns1), Ind (ind2, ss2, ms2, ns2) ->
        Ind.equal ind1 ind2 && List.equal eq_sort ss1 ss2
        && List.equal equal ms1 ms2 && List.equal equal ns1 ns2
      | Constr (constr1, ss1, ms1, ns1), Constr (constr2, ss2, ms2, ns2) ->
        Constr.equal constr1 constr2
        && List.equal eq_sort ss1 ss2 && List.equal equal ms1 ms2
        && List.equal equal ns1 ns2
      | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
        List.equal equal ms1 ms2 && equal a1 a2
        && List.equal (eq_pbinder (Option.equal equal)) cls1 cls2
      (* monad *)
      | IO a1, IO a2 -> equal a1 a2
      | Return m1, Return m2 -> equal m1 m2
      | MLet (m1, bnd1), MLet (m2, bnd2) ->
        equal m1 m2 && eq_binder equal bnd1 bnd2
      (* magic *)
      | Magic _, _ -> true
      | _, Magic _ -> true
      (* other *)
      | _ -> false
  in
  if equal m1 m2 then
    true
  else if expand then
    false
  else
    eq_tm ~expand:true ctx m1 m2
