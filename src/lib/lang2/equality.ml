open Bindlib
open Names
open Syntax
open Util
open Environment

let is_guarded i ms =
  let sz = Array.length ms in
  let rec loop j =
    if j <= i && j < sz then
      match unApps ms.(j) with
      | Constr _, _ -> true
      | _ -> loop (j + 1)
    else
      false
  in
  loop 0

let get_field x m =
  match m with
  | Struct (_, fields) -> (
    let opt = Array.find_opt (fun (_, y, _) -> Field.equal x y) fields in
    match opt with
    | Some (_, _, m) -> Some m
    | _ -> None)
  | _ -> None

(* weak head normal form *)
let rec whnf ?(expand = true) (env : Env.t) = function
  (* inference *)
  | Ann (m, a) -> whnf ~expand env m
  (* core *)
  | Var x -> (
    match Env.find_var x env with
    | Some m when expand -> whnf ~expand env m
    | _ -> Var x)
  | Const (x, ss) -> (
    match Env.find_const x env with
    | Some f when expand -> whnf ~expand env (f ss)
    | _ -> Const (x, ss))
  | App _ as m -> (
    let hd, ms = unApps m in
    let hd = whnf ~expand env hd in
    let ms = Array.map (whnf ~expand env) ms in
    match hd with
    | Lam (_, _, _, bnd) ->
      let m = ms.(0) in
      let ms = Array.(sub ms 1 (length ms - 1)) in
      whnf ~expand env (mkApps (subst bnd m) ms)
    | Fix (i, _, bnd) when is_guarded i ms ->
      whnf ~expand env (mkApps (subst bnd hd) ms)
    | _ -> mkApps hd ms)
  | Let (_, m, bnd) ->
    let m = whnf ~expand env m in
    whnf ~expand env (subst bnd m)
  (* inductive *)
  | Match (ms, a, cls) -> (
    let ms = Array.map (fun (m, r) -> (whnf ~expand env m, r)) ms in
    let ns = Array.map (fun (m, r) -> m) ms in
    let a = whnf ~expand env a in
    let rhs_opt =
      Array.fold_left
        (fun acc_opt cl ->
          match acc_opt with
          | Some _ -> acc_opt
          | None -> (
            try Some (psubst cl ns) with
            | _ -> acc_opt))
        None cls
    in
    match rhs_opt with
    | Some rhs -> whnf ~expand env rhs
    | _ -> Match (ms, a, cls))
  (* record *)
  | Proj (x, m) -> (
    let m = whnf ~expand env m in
    match get_field x m with
    | Some m -> whnf ~expand env m
    | _ -> Proj (x, m))
  (* other *)
  | m -> m

(* sort equality *)
let rec eq_sort s1 s2 =
  match (s1, s2) with
  | SVar x, SVar y -> eq_vars x y
  | SMeta (x1, _), SMeta (x2, _) -> SMeta.equal x1 x2
  | _ -> s1 = s2

(* alpha equivalence *)
let rec aeq_tm m1 m2 =
  if m1 == m2 then
    true
  else
    match (m1, m2) with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) -> aeq_tm m1 m2 && aeq_tm a1 a2
    | IMeta (x1, _, _), IMeta (x2, _, _) -> IMeta.equal x1 x2
    | PMeta x1, PMeta x2 -> PMeta.equal x1 x2
    (* core *)
    | Type s1, Type s2 -> eq_sort s1 s2
    | Var x1, Var x2 -> eq_vars x1 x2
    | Const (x1, ss1), Const (x2, ss2) ->
      Const.equal x1 x2 && Array.for_all2 eq_sort ss1 ss2
    | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2) ->
      relv1 = relv2 && eq_sort s1 s2 && aeq_tm a1 a2
      && eq_binder aeq_tm bnd1 bnd2
    | Lam (relv1, s1, a1, bnd1), Lam (relv2, s2, a2, bnd2) ->
      relv1 = relv2 && eq_sort s1 s2 && aeq_tm a1 a2
      && eq_binder aeq_tm bnd1 bnd2
    | Fix (i1, a1, bnd1), Fix (i2, a2, bnd2) ->
      i1 = i2 && aeq_tm a1 a2 && eq_binder aeq_tm bnd1 bnd2
    | App (m1, n1), App (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) ->
      relv1 = relv2 && aeq_tm m1 m2 && eq_binder aeq_tm bnd1 bnd2
    (* inductive *)
    | Ind (ind1, ss1), Ind (ind2, ss2) ->
      Ind.equal ind1 ind2 && Array.for_all2 eq_sort ss1 ss2
    | Constr (constr1, ss1), Constr (constr2, ss2) ->
      Constr.equal constr1 constr2 && Array.for_all2 eq_sort ss1 ss2
    | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
      Array.for_all2
        (fun (m1, relv1) (m2, relv2) -> aeq_tm m1 m2 && relv1 = relv2)
        ms1 ms2
      && aeq_tm a1 a2
      && Array.for_all2 (fun cl1 cl2 -> eq_pbinder aeq_tm cl1 cl2) cls1 cls2
    | Absurd, Absurd -> true
    (* record *)
    | Record (record1, ss1), Record (record2, ss2) ->
      Record.equal record1 record2 && Array.for_all2 eq_sort ss1 ss2
    | Struct (s1, fields1), Struct (s2, fields2) ->
      eq_sort s1 s2
      && Array.for_all2
           (fun (relv1, x1, m1) (relv2, x2, m2) ->
             relv1 = relv2 && Field.equal x1 x2 && aeq_tm m1 m2)
           fields1 fields2
    | Proj (x1, m1), Proj (x2, m2) -> Field.equal x1 x2 && aeq_tm m1 m2
    (* magic *)
    | Magic, _ -> true
    | _, Magic -> true
    (* other *)
    | _ -> false

(* beta/delta/iota equality *)
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
      | PMeta x1, PMeta x2 -> PMeta.equal x1 x2 (* core *)
      (* core *)
      | Type s1, Type s2 -> eq_sort s1 s2
      | Var x1, Var x2 -> eq_vars x1 x2
      | Const (x1, ss1), Const (x2, ss2) ->
        Const.equal x1 x2 && Array.for_all2 eq_sort ss1 ss2
      | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && eq_sort s1 s2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | Lam (rel1, s1, a1, bnd1), Lam (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && eq_sort s1 s2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | App (m1, n1), App (m2, n2) -> equal m1 m2 && equal n1 n2
      | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) ->
        rel1 = rel2 && equal m1 m2 && eq_binder equal bnd1 bnd2
      (* inductive *)
      | Ind (ind1, ss1), Ind (ind2, ss2) ->
        Ind.equal ind1 ind2 && Array.for_all2 eq_sort ss1 ss2
      | Constr (constr1, ss1), Constr (constr2, ss2) ->
        Constr.equal constr1 constr2 && Array.for_all2 eq_sort ss1 ss2
      | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
        Array.for_all2
          (fun (m1, rel1) (m2, rel2) -> equal m1 m2 && rel1 = rel2)
          ms1 ms2
        && equal a1 a2
        && Array.for_all2
             (fun (p0s1, bnd1) (p0s2, bnd2) ->
               eq_p0s p0s1 p0s2 && eq_mbinder equal bnd1 bnd2)
             cls1 cls2
      | Absurd, Absurd -> true (* record *)
      (* record *)
      | Record (record1, ss1), Record (record2, ss2) ->
        Record.equal record1 record2 && Array.for_all2 eq_sort ss1 ss2
      | Struct (s1, fields1), Struct (s2, fields2) ->
        eq_sort s1 s2
        && Array.for_all2
             (fun (relv1, x1, m1) (relv2, x2, m2) ->
               relv1 = relv2 && Field.equal x1 x2 && equal m1 m2)
             fields1 fields2
      | Proj (x1, m1), Proj (x2, m2) -> Field.equal x1 x2 && equal m1 m2
      (* magic *)
      | Magic, _ -> true
      | _, Magic -> true
      (* other *)
      | _ -> false
  in
  if equal m1 m2 then
    true
  else if expand then
    false
  else
    eq_tm ~expand:true env m1 m2
