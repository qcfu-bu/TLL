open Bindlib
open Names
open Syntax1
open Context1e

let rec whnf ?(expand = true) (env : Env.t) = function
  (* inference *)
  | Ann (m, a) -> whnf ~expand env m
  (* core *)
  | Var x when expand -> (
    try whnf ~expand env (Env.find_var x env) with
    | _ -> Var x)
  | Const (x, ss) when expand -> (
    try
      let sch = Env.find_const x env in
      whnf ~expand env (msubst sch (Array.of_list ss))
    with
    | _ -> Const (x, ss))
  | App _ as m -> (
    let hd, ms = unApps m in
    let hd = whnf ~expand env hd in
    let ms = List.map (whnf ~expand env) ms in
    match hd with
    | Fun (guard, _, bnd) -> (
      let cls = subst bnd hd in
      match match_cls guard cls ms with
      | Some (Some rhs, rst) -> whnf ~expand env (mkApps rhs rst)
      | _ -> mkApps hd ms)
    | _ -> mkApps hd ms)
  | Let (_, m, bnd) ->
    let m = whnf ~expand env m in
    whnf ~expand env (subst bnd m)
  (* inductive *)
  | Match (guard, ms, a, cls) -> (
    let ms = List.map (whnf ~expand env) ms in
    match match_cls guard cls ms with
    | Some (Some rhs, []) -> whnf ~expand env rhs
    | _ -> Match (guard, ms, a, cls))
  (* monadic *)
  | MLet (m, bnd) -> (
    let m = whnf ~expand env m in
    match m with
    | Return m ->
      let m = whnf ~expand env m in
      whnf ~expand env (subst bnd m)
    | _ -> MLet (m, bnd))
  (* other *)
  | m -> m

and match_cls guard cls ms =
  let rec check_guard guard ms =
    match (guard, ms) with
    | true :: guard, (Constr _ as m) :: ms ->
      Option.map (fun (ms, ns) -> (m :: ms, ns)) (check_guard guard ms)
    | true :: guard, _ -> None
    | false :: guard, m :: ms ->
      Option.map (fun (ms, ns) -> (m :: ms, ns)) (check_guard guard ms)
    | false :: guard, [] -> None
    | [], ms -> Some ([], ms)
  in
  match check_guard guard ms with
  | Some (ms, ns) ->
    List.fold_left
      (fun acc_opt ((p0s, bnd) as cl) ->
        match acc_opt with
        | Some _ -> acc_opt
        | None -> (
          try Some (psubst cl ms, ns) with
          | _ -> None))
      None cls
  | None -> None

let rec aeq_tm m1 m2 =
  if m1 == m2 then
    true
  else
    match (m1, m2) with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) -> aeq_tm m1 m2 && aeq_tm a1 a2
    | IMeta (x1, _, _), IMeta (x2, _, _) -> IMeta.equal x1 x2
    | PMeta x1, PMeta x2 -> eq_vars x1 x2
    (* core *)
    | Type s1, Type s2 -> eq_sort s1 s2
    | Var x1, Var x2 -> eq_vars x1 x2
    | Const (x1, ss1), Const (x2, ss2) ->
      Const.equal x1 x2 && List.equal eq_sort ss1 ss2
    | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2) ->
      relv1 = relv2 && eq_sort s1 s2 && aeq_tm a1 a2
      && eq_binder aeq_tm bnd1 bnd2
    | Fun (_, a1, bnd1), Fun (_, a2, bnd2) ->
      aeq_tm a1 a2
      && eq_binder (List.equal (eq_pbinder (Option.equal aeq_tm))) bnd1 bnd2
    | App (m1, n1), App (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) ->
      relv1 = relv2 && aeq_tm m1 m2 && eq_binder aeq_tm bnd1 bnd2
    (* inductive *)
    | Ind (d1, ss1, ms1, ns1), Ind (d2, ss2, ms2, ns2) ->
      Ind.equal d1 d2 && List.equal eq_sort ss1 ss2 && List.equal aeq_tm ms1 ms2
      && List.equal aeq_tm ns1 ns2
    | Constr (c1, ss1, ms1, ns1), Constr (c2, ss2, ms2, ns2) ->
      Constr.equal c1 c2 && List.equal eq_sort ss1 ss2
      && List.equal aeq_tm ms1 ms2 && List.equal aeq_tm ns1 ns2
    | Match (_, ms1, a1, cls1), Match (_, ms2, a2, cls2) ->
      List.equal aeq_tm ms1 ms2 && aeq_tm a1 a2
      && List.equal (eq_pbinder (Option.equal aeq_tm)) cls1 cls2
    (* monad *)
    | IO a1, IO a2 -> aeq_tm a1 a2
    | Return m1, Return m2 -> aeq_tm m1 m2
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      aeq_tm m1 m2 && eq_binder aeq_tm bnd1 bnd2
    (* magic *)
    | Magic a1, Magic a2 -> aeq_tm a1 a2
    (* other *)
    | _ -> false

let rec eq_tm ?(expand = false) env m1 m2 =
  let rec equal m1 m2 =
    if aeq_tm m1 m2 then
      true
    else
      let m1 = whnf ~expand env m1 in
      let m2 = whnf ~expand env m2 in
      match (m1, m2) with
      (* inference *)
      | IMeta (x1, _, _), IMeta (x2, _, _) -> IMeta.equal x1 x2
      | PMeta x1, PMeta x2 -> eq_vars x1 x2
      (* core *)
      | Type s1, Type s2 -> eq_sort s1 s2
      | Var x1, Var x2 -> eq_vars x1 x2
      | Const (x1, ss1), Const (x2, ss2) ->
        Const.equal x1 x2 && List.equal eq_sort ss1 ss2
      | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2) ->
        relv1 = relv2 && eq_sort s1 s2 && equal a1 a2
        && eq_binder equal bnd1 bnd2
      | Fun (_, a1, bnd1), Fun (_, a2, bnd2) ->
        equal a1 a2
        && eq_binder (List.equal (eq_pbinder (Option.equal equal))) bnd1 bnd2
      | App (m1, n1), App (m2, n2) -> equal m1 m2 && equal n1 n2
      | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) ->
        relv1 = relv2 && equal m1 m2 && eq_binder equal bnd1 bnd2
      (* inductive *)
      | Ind (d1, ss1, ms1, ns1), Ind (d2, ss2, ms2, ns2) ->
        Ind.equal d1 d2 && List.equal eq_sort ss1 ss2
        && List.equal equal ms1 ms2 && List.equal equal ns1 ns2
      | Constr (c1, ss1, ms1, ns1), Constr (c2, ss2, ms2, ns2) ->
        Constr.equal c1 c2 && List.equal eq_sort ss1 ss2
        && List.equal equal ms1 ms2 && List.equal equal ns1 ns2
      | Match (_, ms1, a1, cls1), Match (_, ms2, a2, cls2) ->
        List.equal equal ms1 ms2 && equal a1 a2
        && List.equal (eq_pbinder (Option.equal equal)) cls1 cls2
      (* monad *)
      | IO a1, IO a2 -> equal a1 a2
      | Return m1, Return m2 -> equal m1 m2
      | MLet (m1, bnd1), MLet (m2, bnd2) ->
        equal m1 m2 && eq_binder equal bnd1 bnd2
      (* magic *)
      | Magic a1, Magic a2 -> equal a1 a2
      (* other *)
      | _ -> false
  in
  if equal m1 m2 then
    true
  else if expand then
    false
  else
    eq_tm ~expand:true env m1 m2
