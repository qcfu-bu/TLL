open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Constraint1
open Pprint1

let resolve_iprbm (eqns : IPrbm.eqns) (m : tm) : tm = m

let rec simpl_pprbm ?(expand = false) eqn =
  let open PPrbm in
  match eqn with
  | EqualPat _ -> failwith "unifier1.simpl_pprbm(EqualPat)"
  | EqualTerm (ctx, m1, m2) -> (
    let m1 = whnf ~expand ctx m1 in
    let m2 = whnf ~expand ctx m2 in
    match (m1, m2) with
    (* inference *)
    | IMeta (x1, _, _), IMeta (x2, _, _) when IMeta.equal x2 x2 -> []
    | PMeta x, PMeta y when compare_vars x y < 0 -> [ EqualTerm (ctx, m1, m2) ]
    | PMeta x, PMeta y when compare_vars x y > 0 -> [ EqualTerm (ctx, m2, m1) ]
    | PMeta x, PMeta y when compare_vars x y = 0 -> []
    | _, PMeta _ -> [ EqualTerm (ctx, m1, m2) ]
    | PMeta _, _ -> [ EqualTerm (ctx, m2, m1) ]
    (* core *)
    | Type s1, Type s2 when eq_sort s1 s2 -> []
    | Var x1, Var x2 when eq_vars x1 x2 -> []
    | Const (x1, ss1), Const (x2, ss2)
      when Const.equal x1 x2 && List.equal eq_sort ss1 ss2 ->
      []
    | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2)
      when relv1 = relv2 && eq_sort s1 s2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm ~expand (EqualTerm (ctx, a1, a2)) in
      let eqns2 = simpl_pprbm ~expand (EqualTerm (ctx, b1, b2)) in
      eqns1 @ eqns2
    | Fun (a1, bnd1), Fun (a2, bnd2) ->
      let _, cls1, cls2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm ~expand (EqualTerm (ctx, a1, a2)) in
      let eqns2 =
        List.map2
          (fun cl1 cl2 ->
            let _, rhs_opt1, rhs_opt2 = unbind_ps2 cl1 cl2 in
            match (rhs_opt1, rhs_opt2) with
            | Some rhs1, Some rhs2 ->
              simpl_pprbm ~expand (EqualTerm (ctx, rhs1, rhs2))
            | None, None -> []
            | _ -> failwith "unifier.simpl_pprbm(Fun)")
          cls1 cls2
      in
      eqns1 @ List.concat eqns2
    | _, App _
    | App _, _ -> (
      try
        let hd1, sp1 = unApps m1 in
        let hd2, sp2 = unApps m1 in
        let eqns1 = simpl_pprbm ~expand (EqualTerm (ctx, hd1, hd2)) in
        let eqns2 =
          List.map2
            (fun m n -> simpl_pprbm ~expand (EqualTerm (ctx, m, n)))
            sp1 sp2
        in
        eqns1 @ List.concat eqns2
      with
      | _ ->
        if expand then
          failwith "unifier1.solve_pprbm(App)"
        else
          simpl_pprbm ~expand:true (EqualTerm (ctx, m1, m2)))
    | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) when relv1 = relv2 ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm ~expand (EqualTerm (ctx, m1, m2)) in
      let eqns2 = simpl_pprbm ~expand (EqualTerm (ctx, n1, n2)) in
      eqns1 @ eqns2
    (* inductive *)
    | Ind (d1, ss1, ms1, ns1), Ind (d2, ss2, ms2, ns2)
      when Ind.equal d1 d2 && List.equal eq_sort ss1 ss2 ->
      let eqns1 =
        List.map2
          (fun m1 m2 -> simpl_pprbm ~expand (EqualTerm (ctx, m1, m2)))
          ms1 ms2
      in
      let eqns2 =
        List.map2
          (fun n1 n2 -> simpl_pprbm ~expand (EqualTerm (ctx, n1, n2)))
          ns1 ns2
      in
      List.concat eqns1 @ List.concat eqns2
    | Constr (c1, ss1, ms1, ns1), Constr (c2, ss2, ms2, ns2)
      when Constr.equal c1 c2 && List.equal eq_sort ss1 ss2 ->
      let eqns1 =
        List.map2
          (fun m1 m2 -> simpl_pprbm ~expand (EqualTerm (ctx, m1, m2)))
          ms1 ms2
      in
      let eqns2 =
        List.map2
          (fun n1 n2 -> simpl_pprbm ~expand (EqualTerm (ctx, n1, n2)))
          ns1 ns2
      in
      List.concat eqns1 @ List.concat eqns2
    | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
      let eqns1 =
        List.map2
          (fun m1 m2 -> simpl_pprbm ~expand (EqualTerm (ctx, m1, m2)))
          ms1 ms2
      in
      let eqns2 = simpl_pprbm ~expand (EqualTerm (ctx, a1, a2)) in
      let eqns3 =
        List.map2
          (fun cl1 cl2 ->
            let _, rhs_opt1, rhs_opt2 = unbind_ps2 cl1 cl2 in
            match (rhs_opt1, rhs_opt2) with
            | Some rhs1, Some rhs2 ->
              simpl_pprbm ~expand (EqualTerm (ctx, rhs1, rhs2))
            | None, None -> []
            | _ -> failwith "unifier.simpl_pprbm(Match)")
          cls1 cls2
      in
      List.concat eqns1 @ eqns2 @ List.concat eqns3
    (* monad *)
    | IO a1, IO a2 -> simpl_pprbm ~expand (EqualTerm (ctx, a1, a2))
    | Return m1, Return m2 -> simpl_pprbm ~expand (EqualTerm (ctx, m1, m2))
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl_pprbm ~expand (EqualTerm (ctx, m1, m2)) in
      let eqns2 = simpl_pprbm ~expand (EqualTerm (ctx, n1, n2)) in
      eqns1 @ eqns2
    (* magic *)
    | Magic _, _ -> []
    | _, Magic _ -> []
    | _ ->
      if expand then
        failwith "unifier1.simpl_pprm(%a, %a)" pp_tm m1 pp_tm m2
      else
        simpl_pprbm ~expand:true (EqualTerm (ctx, m1, m2)))

let solve_pprbm (eqns : PPrbm.eqns) : tm Var.Map.t =
  let open PPrbm in
  let solve map = function
    | EqualTerm (_, m, PMeta x) ->
      if occur x (lift_tm m) then
        failwith "unifier.solve_pprbm(occurs)"
      else
        Var.Map.add x m map
    | _ -> failwith "unifier1.solve_pprbm(solve)"
  in
  let eqns =
    List.map
      (fun eqn ->
        match eqn with
        | EqualPat (ctx, m, PVar x, _) -> EqualTerm (ctx, m, PMeta x)
        | EqualPat _ -> failwith "unifier1.solve_pprbm(unify)"
        | EqualTerm _ -> eqn)
      eqns
  in
  let eqns = List.concat_map simpl_pprbm eqns in
  List.fold_left solve Var.Map.empty eqns

let resolve_pprbm (eqns : PPrbm.eqns) (m : tm) : tm =
  let var_map = solve_pprbm eqns in
  subst_pmeta var_map m
