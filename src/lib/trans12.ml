open Fmt
open Bindlib
open Names
open Syntax1
open Context12
open Constraint12
open Equality12
open Unifier12
open Pprint1

module State : sig
  open Resolver

  val add_const : Const.t -> Const.t RMap.t -> unit
  val add_ind : Ind.t -> sorts -> Ind.t -> unit
  val add_constr : Constr.t -> sorts -> Constr.t -> unit
  val find_const : Const.t -> sorts -> Const.t
  val find_ind : Ind.t -> sorts -> Ind.t
  val find_constr : Constr.t -> sorts -> Constr.t
end = struct
  let state = ref Resolver.empty
  let add_const x0 rmap = state := Resolver.add_const x0 rmap !state
  let add_ind d0 ss d1 = state := Resolver.add_ind d0 ss d1 !state
  let add_constr c0 ss c1 = state := Resolver.add_constr c0 ss c1 !state
  let find_const x0 ss = Resolver.find_const x0 ss !state
  let find_ind d0 ss = Resolver.find_ind d0 ss !state
  let find_constr c0 ss = Resolver.find_constr c0 ss !state
end

module Logical = struct
  let assert_sort = function
    | U -> ()
    | L -> ()
    | _ -> failwith "trans12.Logical.assert_sort"

  let assert_equal env m n =
    if not (eq_tm env m n) then
      failwith "trans12.Logical.assert_equal(%a, %a)" pp_tm m pp_tm n

  let rec infer_sort ctx env a =
    let t = infer_tm ctx env a in
    match whnf env t with
    | Type U -> U
    | Type L -> L
    | _ -> failwith "trans12.Logical.assert_equal(%a : %a)" pp_tm a pp_tm t

  and infer_tm ctx env m =
    Debug.exec (fun () -> pr "@[Logical.infer_tm(%a)@]@." pp_tm m);
    match m with
    (* inference *)
    | Ann (m, a) ->
      let _ = infer_sort ctx env a in
      check_tm ctx env m a;
      a
    | IMeta _ -> failwith "trans12.Logical.infer_tm(IMeta)"
    | PMeta _ -> failwith "trans12.Logical.infer_tm(PMeta)"
    (* core *)
    | Type s ->
      assert_sort s;
      Type U
    | Var x -> fst (Ctx.find_var x ctx)
    | Const (x0, ss) ->
      let x1 = State.find_const x0 ss in
      fst (Ctx.find_const x1 ctx)
    | Pi (_, s, a, bnd) ->
      assert_sort s;
      let x, b = unbind bnd in
      let t = infer_sort ctx env a in
      let _ = infer_sort (Ctx.add_var x a t ctx) env b in
      Type s
    | Fun (a, bnd) ->
      let x, cls = unbind bnd in
      let s = infer_sort ctx env a in
      check_cls (Ctx.add_var x a s ctx) env cls a;
      a
    | App (m, n) -> (
      let t = infer_tm ctx env m in
      match whnf env t with
      | Pi (_, _, a, bnd) ->
        check_tm ctx env n a;
        subst bnd n
      | _ -> failwith "trans12.Logical.infer_tm(App)")
    | Let (_, m, bnd) ->
      let x, n = unbind bnd in
      let a = infer_tm ctx env m in
      let s = infer_sort ctx env a in
      infer_tm (Ctx.add_var x a s ctx) (Env.add_var x m env) n
    (* inductive *)
    | Ind (d0, ss, ms, ns) ->
      List.iter assert_sort ss;
      let d1 = State.find_ind d0 ss in
      let ptl, _ = Ctx.find_ind d1 ctx in
      infer_ptl ctx env ms ns ptl
    | Constr (c0, ss, ms, ns) ->
      List.iter assert_sort ss;
      let c1 = State.find_constr c0 ss in
      let ptl, _ = Ctx.find_constr c1 ctx in
      infer_ptl ctx env ms ns ptl
    | Match (ms, a, cls) ->
      let b = infer_motive ctx env ms a in
      check_cls ctx env cls a;
      b
    (* monad *)
    | IO a ->
      let _ = infer_sort ctx env a in
      Type L
    | Return m -> IO (infer_tm ctx env m)
    | MLet (m, bnd) -> (
      let t1 = infer_tm ctx env m in
      match whnf env t1 with
      | IO a -> (
        let s = infer_sort ctx env a in
        let x, n = unbind bnd in
        let t2 = infer_tm (Ctx.add_var x a s ctx) env n in
        match whnf env t2 with
        | IO b -> IO b
        | _ -> failwith "trans12.Logical.infer_tm(MLet)")
      | _ -> failwith "trans12.Logical.infer_tm(MLet)")
    (* magic *)
    | Magic a ->
      let _ = infer_sort ctx env a in
      a

  and infer_ptl ctx env ms ns ptl =
    let rec aux_param ms ptl =
      match (ms, ptl) with
      | [], PBase tl -> aux_tele ns tl
      | m :: ms, PBind (a, bnd) ->
        check_tm ctx env m a;
        aux_param ms (subst bnd m)
      | _ -> failwith "trans12.Logical.infer_ptl(param)"
    and aux_tele ns tl =
      match (ns, tl) with
      | [], TBase a -> a
      | n :: ns, TBind (_, a, bnd) ->
        check_tm ctx env n a;
        aux_tele ns (subst bnd n)
      | _ -> failwith "trans12.Logical.infer_ptl(tele)"
    in
    aux_param ms ptl

  and infer_motive ctx env ms a =
    match (ms, whnf env a) with
    | [], a -> a
    | m :: ms, Pi (_, _, a, bnd) ->
      check_tm ctx env m a;
      infer_motive ctx env ms (subst bnd m)
    | _ -> failwith "trans12.Logical.infer_motive"

  and check_tm ctx env m a =
    Debug.exec (fun () ->
        pr "@[Logical.check_tm(@;<1 2>@[%a@],@;<1 2>@[%a@]@;<1 0>)@]@." pp_tm m
          pp_tm a);
    match m with
    | Fun (b, bnd) ->
      let x, cls = unbind bnd in
      let s = infer_sort ctx env b in
      assert_equal env a b;
      check_cls (Ctx.add_var x a s ctx) env cls a
    | _ ->
      let b = infer_tm ctx env m in
      assert_equal env a b

  and check_cls ctx env cls a =
    let rec is_absurd eqns rhs =
      match (eqns, rhs) with
      | EqualPat (_, _, PMeta _, PAbsurd, _) :: _, None -> true
      | EqualPat (_, _, PMeta _, PAbsurd, _) :: _, Some _ ->
        failwith "trans12.Logical.is_absurd"
      | _ :: eqns, _ -> is_absurd eqns rhs
      | [], _ -> false
    in
    let rec get_absurd = function
      | EqualPat (_, _, PMeta _, PAbsurd, a) :: _ -> a
      | _ :: eqns -> get_absurd eqns
      | [] -> failwith "trans12.Logical.get_absurd"
    in
    let rec can_split = function
      | EqualPat (_, _, PMeta _, PConstr _, _) :: _ -> true
      | _ :: eqns -> can_split eqns
      | [] -> false
    in
    let rec first_split = function
      | EqualPat (_, _, PMeta x, PConstr _, a) :: _ -> (x, a)
      | _ :: eqns -> first_split eqns
      | [] -> failwith "trans12.Logical.first_split"
    in
    let fail_on_ind global ctx d1 ss ms a =
      let _, cs0 = Ctx.find_ind d1 ctx in
      List.iter
        (fun c0 ->
          let c1 = State.find_constr c0 ss in
          let param, _ = Ctx.find_constr c1 ctx in
          let tele = param_inst param ms in
          let _, t = unbind_tele tele in
          let global = EqualTerm (env, a, t) :: global in
          if succeed_pprbm global then
            failwith "trans12.Logical.fail_on_ind(%a)" Ind.pp d1)
        cs0
    in
    let rec aux_prbm ctx prbm a =
      match prbm.clause with
      (* empty *)
      | [] -> (
        Debug.exec (fun () -> pr "case_empty@.");
        if succeed_pprbm prbm.global then
          match whnf env a with
          | Pi (_, _, a, _) -> (
            match whnf env a with
            | Ind (d0, ss, ms, ns) ->
              let d1 = State.find_ind d0 ss in
              fail_on_ind prbm.global ctx d1 ss ms a
            | _ -> failwith "trans12.check_cls(Empty)")
          | _ -> failwith "trans12.check_cls(Empty)")
      (* case intro *)
      | (eqns, p :: ps, rhs) :: clause -> (
        match whnf env a with
        | Pi (relv, _, a, bnd) ->
          let x, b = unbind_pmeta bnd in
          let s =
            infer_sort (Ctx.map_var demote_pmeta ctx) env (demote_pmeta a)
          in
          let ctx = Ctx.add_var x a s ctx in
          let prbm = prbm_add env prbm x a relv in
          aux_prbm ctx prbm b
        | a ->
          failwith "trans12.Logical.check_cls(Intro(%a, %a))" pp_tm a
            (pp_ps " ") ps)
      (* case splitting *)
      | (eqns, [], rhs) :: _ when can_split eqns -> (
        let x, b = first_split eqns in
        match whnf env b with
        | Ind (d0, ss, ms, _) ->
          let d1 = State.find_ind d0 ss in
          let _, cs0 = Ctx.find_ind d1 ctx in
          List.iter
            (fun c0 ->
              let c1 = State.find_constr c0 ss in
              let param, _ = Ctx.find_constr c1 ctx in
              let tele = param_inst param ms in
              let args, t = unbind_tele tele in
              let ctx, ns =
                List.fold_left_map
                  (fun ctx (_, x, a) ->
                    let s = infer_sort ctx env a in
                    (Ctx.add_var x a s ctx, PMeta x))
                  ctx args
              in
              let m = Constr (c0, ss, ms, ns) in
              let var_map = Var.Map.singleton x m in
              let a = subst_pmeta var_map a in
              let ctx = Ctx.map_var (subst_pmeta var_map) ctx in
              let prbm = prbm_simpl ctx var_map prbm in
              let prbm =
                { prbm with global = EqualTerm (env, b, t) :: prbm.global }
              in
              aux_prbm ctx prbm a)
            cs0
        | _ -> failwith "trans12.Logical.check_cls(Split(%a))" pp_tm b)
      (* absurd pattern *)
      | (eqns, [], rhs) :: _ when is_absurd eqns rhs -> (
        Debug.exec (fun () -> pr "trans12.Logical.case_absurd@.");
        if succeed_pprbm prbm.global then
          let a = get_absurd eqns in
          match whnf env a with
          | Ind (d0, ss, ms, ns) ->
            let d1 = State.find_ind d0 ss in
            fail_on_ind prbm.global ctx d1 ss ms a
          | _ -> failwith "trans12.Logical.check_cls(Absurd)")
      (* case coverage *)
      | (eqns, [], rhs) :: _ -> (
        Debug.exec (fun () ->
            pr "@[<v 0>case_coverage{|@;<1 2>%a@;<1 0>|}@]@." pp_pprbm prbm);
        match rhs with
        | Some rhs ->
          let local_map, global_map = unify_pprbm eqns prbm.global in
          let a = resolve_pmeta global_map a in
          let ctx = Ctx.map_var (resolve_pmeta global_map) ctx in
          let env = Env.merge_var (Var.Map.map demote_pmeta global_map) env in
          let rhs = resolve_pmeta local_map rhs in
          Debug.exec (fun () ->
              pr "@[case_coverage_ok(@;<1 2>%a,@;<1 2>%a)@]@." pp_tm rhs pp_tm a);
          check_tm ctx env rhs a
        | None ->
          if succeed_pprbm prbm.global then
            failwith "trans12.Logical.check_cls(Cover)")
    in
    aux_prbm ctx (of_cls cls) a

  and prbm_add env prbm x a relv =
    match prbm.clause with
    | [] -> prbm
    | (eqns, p :: ps, rhs) :: clause ->
      let prbm = prbm_add env { prbm with clause } x a relv in
      let clause =
        (eqns @ [ EqualPat (relv, env, PMeta x, p, a) ], ps, rhs) :: prbm.clause
      in
      { prbm with clause }
    | _ -> failwith "trans12.Logical.prbm_add"

  and prbm_simpl ctx var_map prbm =
    let rec aux_global = function
      | [] -> []
      | EqualTerm (env, a, b) :: eqns ->
        let a = subst_pmeta var_map a in
        let b = subst_pmeta var_map b in
        let eqns = aux_global eqns in
        EqualTerm (env, a, b) :: eqns
      | EqualPat _ :: _ -> failwith "trans12.Logical.prbm_simpl(Global)"
    in
    let rec aux_clause = function
      | [] -> []
      | (eqns, ps, rhs) :: clause -> (
        let clause = aux_clause clause in
        let opt =
          List.fold_left
            (fun acc eqn ->
              match (acc, eqn) with
              | Some acc, EqualPat (relv, env, l, r, a) -> (
                let l = subst_pmeta var_map l in
                let a = subst_pmeta var_map a in
                match p_simpl relv ctx env l r a with
                | Some eqns -> Some (acc @ eqns)
                | None -> None)
              | _ -> None)
            (Some []) eqns
        in
        match opt with
        | Some eqns -> (eqns, ps, rhs) :: clause
        | None -> clause)
    in
    let global = aux_global prbm.global in
    let clause = aux_clause prbm.clause in
    { global; clause }

  and p_simpl relv ctx env m p a =
    let a = whnf env a in
    match (m, p, a) with
    | Constr (c0, _, _, ns), PConstr (c, ps), Ind (d0, ss, ms, _) ->
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0 then
        if Constr.equal c0 c then
          let c1 = State.find_constr c0 ss in
          let param, _ = Ctx.find_constr c1 ctx in
          let tele = param_inst param ms in
          ps_simpl relv ctx env ns ps tele
        else
          None
      else
        failwith "trans12.Logical.p_simpl"
    | Constr _, _, Ind _ -> Some [ EqualPat (relv, env, m, p, a) ]
    | _, PConstr (c, _), Ind (d0, ss, _, _) ->
      let d1 = State.find_ind d0 ss in
      let _, cs0 = Ctx.find_ind d1 ctx in
      if List.exists (fun c0 -> Constr.equal c0 c) cs0 then
        Some [ EqualPat (relv, env, m, p, a) ]
      else
        failwith "trans12.Logical.p_simpl"
    | m, p, a -> Some [ EqualPat (relv, env, m, p, a) ]

  and ps_simpl relv0 ctx env ms ps tele =
    match (relv0, ms, ps, tele) with
    | R, m :: ms, p :: ps, TBind (relv, a, bnd) -> (
      let opt1 = p_simpl relv ctx env m p a in
      let tele = subst bnd m in
      let opt2 = ps_simpl relv0 ctx env ms ps tele in
      match (opt1, opt2) with
      | Some eqns1, Some eqns2 -> Some (eqns1 @ eqns2)
      | _ -> None)
    (* sub-patterns inherit irrelevancy *)
    | N, m :: ms, p :: ps, TBind (_, a, bnd) -> (
      let opt1 = p_simpl N ctx env m p a in
      let tele = subst bnd m in
      let opt2 = ps_simpl N ctx env ms ps tele in
      match (opt1, opt2) with
      | Some eqns1, Some eqns2 -> Some (eqns1 @ eqns2)
      | _ -> None)
    | _, [], [], TBase _ -> Some []
    | _ -> None
end
