open Fmt
open Bindlib
open Names
open Syntax1
open Context12
open Equality12
open Constraint12
open Pprint1

let map_pmeta f m =
  let rec aux m =
    match m with
    (* inference *)
    | Ann (m, a) -> Ann (aux m, aux a)
    | IMeta (x, ss, ms) -> IMeta (x, ss, List.map aux ms)
    | PMeta x -> f aux x
    (* core *)
    | Type s -> Type s
    | Var x -> Var x
    | Const (x, ss) -> Const (x, ss)
    | Pi (relv, s, a, bnd) ->
      let x, b = unbind bnd in
      let a = aux a in
      let b = lift_tm (aux b) in
      Pi (relv, s, a, unbox (bind_var x b))
    | Fun (guard, a, bnd) ->
      let x, cls = unbind bnd in
      let a = aux a in
      let cls =
        List.map
          (fun cl ->
            let ps, rhs_opt = unbind_ps cl in
            let rhs_opt = Option.map (fun rhs -> lift_tm (aux rhs)) rhs_opt in
            bind_ps ps (box_opt rhs_opt))
          cls
      in
      let cls = box_list cls in
      Fun (guard, a, unbox (bind_var x cls))
    | App (m, n) -> App (aux m, aux n)
    | Let (relv, m, bnd) ->
      let x, n = unbind bnd in
      let m = aux m in
      let n = lift_tm (aux n) in
      Let (relv, m, unbox (bind_var x n))
    (* inductive *)
    | Ind (d, ss, ms, ns) -> Ind (d, ss, List.map aux ms, List.map aux ns)
    | Constr (c, ss, ms, ns) -> Constr (c, ss, List.map aux ms, List.map aux ns)
    | Match (guard, ms, a, cls) ->
      let ms = List.map aux ms in
      let a = aux a in
      let cls =
        List.map
          (fun cl ->
            let ps, rhs_opt = unbind_ps cl in
            let rhs_opt = Option.map (fun rhs -> lift_tm (aux rhs)) rhs_opt in
            bind_ps ps (box_opt rhs_opt))
          cls
      in
      let cls = box_list cls in
      Match (guard, ms, a, unbox cls)
    (* monad *)
    | IO a -> IO (aux a)
    | Return m -> Return (aux m)
    | MLet (m, bnd) ->
      let x, n = unbind bnd in
      let m = aux m in
      let n = lift_tm (aux n) in
      MLet (m, unbox (bind_var x n))
    (* magic *)
    | Magic a -> Magic (aux a)
  in
  aux m

(* substitute pmeta variables *)
let subst_pmeta var_map m =
  map_pmeta
    (fun self x ->
      match Var.Map.find_opt x var_map with
      | Some m -> self m
      | None -> PMeta x)
    m

(* demote pmeta variables *)
let demote_pmeta m = map_pmeta (fun self x -> Var x) m

(* substitute and demote pmeta variables *)
let resolve_pmeta var_map m =
  map_pmeta
    (fun self x ->
      match Var.Map.find_opt x var_map with
      | Some m -> self m
      | None -> Var x)
    m

let rec simpl_pprbm ?(expand = false) eqn =
  match eqn with
  | EqualPat _ -> failwith "unifier1.simpl_pprbm(EqualPat)"
  | EqualTerm (env, m1, m2) -> (
    let m1 = whnf ~expand env m1 in
    let m2 = whnf ~expand env m2 in
    Debug.exec (fun () ->
        pr "@[simpl_pprbm ~expand:%b(@;<1 2>%a,@;<1 2>%a)@]@." expand pp_tm m1
          pp_tm m2);
    match (m1, m2) with
    (* inference *)
    | IMeta (x1, _, _), IMeta (x2, _, _) when IMeta.equal x2 x2 -> []
    | PMeta x, PMeta y when compare_vars x y < 0 -> [ EqualTerm (env, m1, m2) ]
    | PMeta x, PMeta y when compare_vars x y > 0 -> [ EqualTerm (env, m2, m1) ]
    | PMeta x, PMeta y when compare_vars x y = 0 -> []
    | _, PMeta _ -> [ EqualTerm (env, m1, m2) ]
    | PMeta _, _ -> [ EqualTerm (env, m2, m1) ]
    (* core *)
    | Type s1, Type s2 when eq_sort s1 s2 -> []
    | Var x1, Var x2 when eq_vars x1 x2 -> []
    | Const (x1, ss1), Const (x2, ss2)
      when Const.equal x1 x2 && List.equal eq_sort ss1 ss2 ->
      []
    | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2)
      when relv1 = relv2 && eq_sort s1 s2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm (EqualTerm (env, a1, a2)) in
      let eqns2 = simpl_pprbm (EqualTerm (env, b1, b2)) in
      eqns1 @ eqns2
    | Fun (_, a1, bnd1), Fun (_, a2, bnd2) ->
      let _, cls1, cls2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm (EqualTerm (env, a1, a2)) in
      let eqns2 =
        List.map2
          (fun cl1 cl2 ->
            let _, rhs_opt1, rhs_opt2 = unbind_ps2 cl1 cl2 in
            match (rhs_opt1, rhs_opt2) with
            | Some rhs1, Some rhs2 -> simpl_pprbm (EqualTerm (env, rhs1, rhs2))
            | None, None -> []
            | _ -> failwith "unifier.simpl_pprbm(Fun)")
          cls1 cls2
      in
      eqns1 @ List.concat eqns2
    | _, App _
    | App _, _ -> (
      try
        let hd1, sp1 = unApps m1 in
        let hd2, sp2 = unApps m2 in
        let eqns1 = simpl_pprbm (EqualTerm (env, hd1, hd2)) in
        let eqns2 =
          List.map2 (fun m n -> simpl_pprbm (EqualTerm (env, m, n))) sp1 sp2
        in
        eqns1 @ List.concat eqns2
      with
      | _ when expand -> failwith "unifier1.solve_pprbm(App)"
      | _ -> simpl_pprbm ~expand:true (EqualTerm (env, m1, m2)))
    | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) when relv1 = relv2 ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm (EqualTerm (env, m1, m2)) in
      let eqns2 = simpl_pprbm (EqualTerm (env, n1, n2)) in
      eqns1 @ eqns2
    (* inductive *)
    | Ind (d1, ss1, ms1, ns1), Ind (d2, ss2, ms2, ns2)
      when Ind.equal d1 d2 && List.equal eq_sort ss1 ss2 ->
      let eqns1 =
        List.map2 (fun m1 m2 -> simpl_pprbm (EqualTerm (env, m1, m2))) ms1 ms2
      in
      let eqns2 =
        List.map2 (fun n1 n2 -> simpl_pprbm (EqualTerm (env, n1, n2))) ns1 ns2
      in
      List.concat eqns1 @ List.concat eqns2
    | Constr (c1, ss1, ms1, ns1), Constr (c2, ss2, ms2, ns2)
      when Constr.equal c1 c2 && List.equal eq_sort ss1 ss2 ->
      let eqns1 =
        List.map2 (fun m1 m2 -> simpl_pprbm (EqualTerm (env, m1, m2))) ms1 ms2
      in
      let eqns2 =
        List.map2 (fun n1 n2 -> simpl_pprbm (EqualTerm (env, n1, n2))) ns1 ns2
      in
      List.concat eqns1 @ List.concat eqns2
    | Match (_, ms1, a1, cls1), Match (_, ms2, a2, cls2) ->
      let eqns1 =
        List.map2 (fun m1 m2 -> simpl_pprbm (EqualTerm (env, m1, m2))) ms1 ms2
      in
      let eqns2 = simpl_pprbm (EqualTerm (env, a1, a2)) in
      let eqns3 =
        List.map2
          (fun cl1 cl2 ->
            let _, rhs_opt1, rhs_opt2 = unbind_ps2 cl1 cl2 in
            match (rhs_opt1, rhs_opt2) with
            | Some rhs1, Some rhs2 -> simpl_pprbm (EqualTerm (env, rhs1, rhs2))
            | None, None -> []
            | _ -> failwith "unifier.simpl_pprbm(Match)")
          cls1 cls2
      in
      List.concat eqns1 @ eqns2 @ List.concat eqns3
    (* monad *)
    | IO a1, IO a2 -> simpl_pprbm (EqualTerm (env, a1, a2))
    | Return m1, Return m2 -> simpl_pprbm (EqualTerm (env, m1, m2))
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm (EqualTerm (env, m1, m2)) in
      let eqns2 = simpl_pprbm (EqualTerm (env, n1, n2)) in
      eqns1 @ eqns2
    (* magic *)
    | Magic a1, Magic a2 -> simpl_pprbm (EqualTerm (env, a1, a2))
    | _ when not expand -> simpl_pprbm ~expand:true (EqualTerm (env, m1, m2))
    | _ ->
      failwith "@[<v 0>unifier1.simpl_pprbm(@;<1 2>%a,@;<1 2>%a@;<1 0>)@]" pp_tm
        m1 pp_tm m2)

let solve_pprbm map eqn =
  match eqn with
  | EqualTerm (_, m, PMeta x) ->
    if occur x (lift_tm (demote_pmeta m)) then
      map
    else
      Var.Map.add x m map
  | _ -> failwith "unifier1.solve_pprbm(solve)"

let unify_pprbm local global =
  Debug.exec (fun () ->
      pr "@[unify_local(@;<1 2>@[%a@]@;<1 0>)@]@." pp_eqns local);
  Debug.exec (fun () ->
      pr "@[unify_global(@;<1 2>@[%a@]@;<1 0>)@]@." pp_eqns global);
  let rec aux_eqns var_map = function
    | [] -> var_map
    | EqualPat (_, env, m, PVar x, _) :: eqns -> (
      let m = subst_pmeta var_map m in
      let n = subst_pmeta var_map (PMeta x) in
      match simpl_pprbm (EqualTerm (env, m, n)) with
      | [] -> aux_eqns var_map eqns
      | eqn :: eqns0 ->
        let var_map = solve_pprbm var_map eqn in
        aux_eqns var_map (eqns0 @ eqns))
    | EqualPat _ :: eqns -> failwith "unifier12.unify_pprbm"
    | EqualTerm (env, m, n) :: eqns -> (
      let m = subst_pmeta var_map m in
      let n = subst_pmeta var_map n in
      match simpl_pprbm (EqualTerm (env, m, n)) with
      | [] -> aux_eqns var_map eqns
      | eqn :: eqns0 ->
        let var_map = solve_pprbm var_map eqn in
        aux_eqns var_map (eqns0 @ eqns))
  and flatten_eqn = function
    | EqualPat (relv, env, m, PVar x, _) -> EqualTerm (env, m, PMeta x)
    | EqualPat _ -> failwith "unifier12.solve_pprbm(unify)"
    | eqn -> eqn
  in
  let local = List.map flatten_eqn local in
  let local_map = aux_eqns Var.Map.empty local in
  let global = List.map flatten_eqn global in
  let global_map = aux_eqns local_map global in
  (local_map, global_map)

let succeed_pprbm global =
  try
    let _ = unify_pprbm [] global in
    true
  with
  | _ -> false
