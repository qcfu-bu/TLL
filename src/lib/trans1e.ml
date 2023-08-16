open Fmt
open Bindlib
open Names
open Syntax1
open Context1e
open Constraint1e
open Equality1e
open Unifier1e
open Pprint1

module State : sig
  val add_eqn : IPrbm.eqn -> unit
  val add_imeta : Ctx.t -> Env.t -> IMeta.t -> sorts -> tms -> tm -> unit
  val find_imeta : IMeta.t -> tm option
  val resolve : tm -> tm
  val get_delayed : unit -> (Ctx.t * Env.t * tm * tm) list
  val solve_all : unit -> meta_map
  val dump : unit -> unit
end = struct
  type t =
    { mutable eqns : IPrbm.eqns
    ; mutable mctx : MCtx.t
    ; mutable meta_map : meta_map
    }

  let state : t =
    { eqns = []
    ; mctx = MCtx.empty
    ; meta_map = (SMeta.Map.empty, IMeta.Map.empty)
    }

  let add_eqn prbm = state.eqns <- prbm :: state.eqns

  let add_imeta ctx env x ss xs a =
    state.mctx <- MCtx.add_imeta ctx env x ss xs a state.mctx

  let find_imeta x = MCtx.find_imeta x state.mctx

  let resolve m =
    let meta_map, eqns = unify_iprbm state.meta_map state.eqns in
    state.meta_map <- meta_map;
    state.eqns <- eqns;
    resolve_tm meta_map m

  let get_delayed () =
    let mctx = state.mctx in
    state.mctx <- MCtx.empty;
    MCtx.entries mctx

  let solve_all () =
    let rec loop i =
      let meta_map, eqns = unify_iprbm state.meta_map state.eqns in
      match eqns with
      | [] ->
        state.meta_map <- meta_map;
        state.eqns <- eqns;
        meta_map
      | _ when 0 < i ->
        state.meta_map <- meta_map;
        state.eqns <- eqns;
        loop (i - 1)
      | _ -> failwith "trans1e.solve_all(Timeout)"
    in
    loop 10

  let dump () =
    pr "@[<v 0>begin_dump@;<1 2>%a@;<1 2>%a@;<1 2>@[%a@]@;<1 0>end_dump@]@."
      MCtx.pp state.mctx pp_meta state.meta_map IPrbm.pp_eqns state.eqns
end

let smeta_of_ctx (ctx : Ctx.t) =
  let x = SMeta.mk "" in
  let ss = Ctx.spine_svar ctx |> List.map svar in
  SMeta (x, ss)

let imeta_of_ctx (ctx : Ctx.t) =
  let x = IMeta.mk "" in
  let ss = Ctx.spine_svar ctx |> List.map svar in
  let xs = Ctx.spine_var ctx |> List.map var in
  IMeta (x, ss, xs)

let assert_equal0 s1 s2 =
  if not (eq_sort s1 s2) then State.add_eqn (EqualSort (s1, s2))

let assert_equal1 env m1 m2 =
  Debug.exec (fun () ->
      pr "@[assert_equal1(@;<1 2>%a,@;<1 2>%a)@]@." pp_tm m1 pp_tm m2);
  match eq_tm env m1 m2 with
  | true ->
    Debug.exec (fun () ->
        pr "@[assert_equal1_ok(@;<1 2>%a,@;<1 2>%a)@]@." pp_tm m1 pp_tm m2)
  | false ->
    Debug.exec (fun () ->
        pr "@[assert_equal1_extend(@;<1 2>%a,@;<1 2>%a)@]@." pp_tm m1 pp_tm m2);
    State.add_eqn (EqualTerm (env, m1, m2))

let rec assert_type ctx env a =
  let t = infer_tm ctx env a in
  let t = State.resolve t in
  match whnf env t with
  | Type _ -> ()
  | IMeta _ as m ->
    let s = smeta_of_ctx ctx in
    Debug.exec (fun () -> pr "delay_assert(%a, %a)@." pp_tm m pp_sort s);
    State.add_eqn (EqualTerm (env, m, Type s))
  | t -> failwith "trans1e.assert_type(%a : %a)" pp_tm a pp_tm t

and infer_tm ctx env m : tm =
  Debug.exec (fun () -> pr "infer_tm(%a)@." pp_tm m);
  match m with
  (* inference *)
  | Ann (m, a) ->
    assert_type ctx env a;
    check_tm ctx env m a;
    a
  | IMeta (x, ss, xs) -> (
    match State.find_imeta x with
    | Some a -> a
    | None ->
      let a = imeta_of_ctx ctx in
      State.add_imeta ctx env x ss xs a;
      a)
  | PMeta _ -> failwith "trans1e.infer_tm(PMeta)"
  (* core *)
  | Type _ -> Type U
  | Var x -> Ctx.find_var x ctx
  | Const (x, ss) -> msubst (Ctx.find_const x ctx) (Array.of_list ss)
  | Pi (rel, s, a, bnd) ->
    let x, b = unbind bnd in
    assert_type ctx env a;
    assert_type (Ctx.add_var x a ctx) env b;
    Type s
  | Fun (a, bnd) ->
    let x, cls = unbind bnd in
    assert_type ctx env a;
    check_cls (Ctx.add_var x a ctx) env cls a;
    a
  | App (m, n) -> (
    let t = infer_tm ctx env m in
    let t = State.resolve t in
    match whnf env t with
    | Pi (_, _, a, bnd) ->
      check_tm ctx env n a;
      subst bnd n
    | _ -> failwith "trans1e.App")
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let a = infer_tm ctx env m in
    infer_tm (Ctx.add_var x a ctx) (Env.add_var x m env) n
  (* inductive *)
  | Ind (d, ss, ms, ns) ->
    let sch, _ = Ctx.find_ind d ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_ptl ctx env ms ns ptl
  | Constr (c, ss, ms, ns) ->
    let sch = Ctx.find_constr c ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_ptl ctx env ms ns ptl
  | Match (ms, a, cls) ->
    let b = infer_motive ctx env ms a in
    check_cls ctx env cls a;
    b
  (* monad *)
  | IO a ->
    assert_type ctx env a;
    Type L
  | Return m -> IO (infer_tm ctx env m)
  | MLet (m, bnd) -> (
    let t1 = infer_tm ctx env m in
    let t1 = State.resolve t1 in
    match whnf env t1 with
    | IO a -> (
      let x, n = unbind bnd in
      let t2 = infer_tm (Ctx.add_var x a ctx) env n in
      let t2 = State.resolve t2 in
      match whnf env t2 with
      | IO b -> IO b
      | _ -> failwith "trans1e.MLet")
    | _ -> failwith "trans1e.MLet")
  (* magic *)
  | Magic a ->
    assert_type ctx env a;
    a

and infer_ptl ctx env ms ns ptl =
  let rec aux_param ms ptl =
    match (ms, ptl) with
    | [], PBase tl -> aux_tele ns tl
    | m :: ms, PBind (a, bnd) ->
      check_tm ctx env m a;
      aux_param ms (subst bnd m)
    | _ -> failwith "trans1e.infer_ptl(param)"
  and aux_tele ns tl =
    match (ns, tl) with
    | [], TBase a -> a
    | n :: ns, TBind (_, a, bnd) ->
      check_tm ctx env n a;
      aux_tele ns (subst bnd n)
    | _ -> failwith "trans1e.infer_ptl(tele)"
  in
  aux_param ms ptl

and infer_motive ctx1 env ms a =
  let rec aux_motive ctx0 ms a0 a1 =
    (* ctx0: motive context
       ctx1: discriminee context *)
    match (ms, a0, a1) with
    | [], a0, a1 ->
      assert_type ctx0 env a0;
      assert_type ctx1 env a1;
      a1
    | m :: ms, Pi (_, L, a0, bnd0), Pi (_, L, a1, bnd1) ->
      Debug.exec (fun () ->
          pr "infer_motive(%a : %a : %a)@." pp_tm m pp_tm a0 pp_tm a0);
      let x, b0 = unbind bnd0 in
      assert_type ctx0 env a0;
      assert_type ctx1 env a1;
      check_tm ctx1 env m a1;
      aux_motive (Ctx.add_var x a0 ctx0) ms b0 (subst bnd1 m)
    | _ -> failwith "trans1e.infer_motive"
  in
  aux_motive ctx1 ms a a

and check_tm ctx env m a : unit =
  Debug.exec (fun () ->
      pr "@[check_tm(@;<1 2>%a,@;<1 2>%a)@]@." pp_tm m pp_tm a);
  match m with
  (* inference *)
  | IMeta (x, ss, xs) -> State.add_imeta ctx env x ss xs a
  | Fun (b, bnd) ->
    let x, cls = unbind bnd in
    assert_type ctx env b;
    assert_equal1 env a b;
    check_cls (Ctx.add_var x a ctx) env cls a
  | _ ->
    let b = infer_tm ctx env m in
    assert_equal1 env a b

and check_cls ctx env cls a : unit =
  let rec is_absurd eqns rhs =
    match (eqns, rhs) with
    | PPrbm.EqualPat (_, PMeta _, PAbsurd, _) :: _, None -> true
    | PPrbm.EqualPat (_, PMeta _, PAbsurd, _) :: _, Some _ ->
      failwith "trans1e.is_absurd"
    | _ :: eqns, _ -> is_absurd eqns rhs
    | [], _ -> false
  in
  let rec get_absurd = function
    | PPrbm.EqualPat (_, PMeta _, PAbsurd, a) :: _ -> a
    | _ :: eqns -> get_absurd eqns
    | [] -> failwith "trans1e.get_absurd"
  in
  let rec can_split = function
    | PPrbm.EqualPat (_, PMeta _, PConstr _, _) :: _ -> true
    | _ :: eqns -> can_split eqns
    | [] -> false
  in
  let rec first_split = function
    | PPrbm.EqualPat (_, PMeta x, PConstr _, a) :: _ -> (x, a)
    | _ :: eqns -> first_split eqns
    | [] -> failwith "trans1e.first_split"
  in
  let fail_on_ind global ctx d ss ms a =
    let _, cs = Ctx.find_ind d ctx in
    List.iter
      (fun c ->
        let sch = Ctx.find_constr c ctx in
        let param = msubst sch (Array.of_list ss) in
        let tele = param_inst param ms in
        let _, t = unbind_tele tele in
        let global = PPrbm.EqualTerm (env, a, t) :: global in
        if succeed_pprbm global then failwith "trans1e.fail_on_ind(%a)" Ind.pp d)
      cs
  in
  let rec aux_prbm (ctx : Ctx.t) (prbm : PPrbm.t) a =
    match prbm.clause with
    (* empty *)
    | [] -> (
      Debug.exec (fun () -> pr "case_empty@.");
      if succeed_pprbm prbm.global then
        match whnf env a with
        | Pi (_, _, a, _) -> (
          match whnf env a with
          | Ind (d, ss, ms, ns) -> fail_on_ind prbm.global ctx d ss ms a
          | _ -> failwith "trans1e.check_cls(Empty)")
        | _ -> failwith "trans1e.check_cls(Empty)")
    (* case intro *)
    | (eqns, p :: ps, rhs) :: clause -> (
      Debug.exec (fun () -> pr "case_intro@.");
      match whnf env a with
      | Pi (_, _, a, bnd) ->
        let x, b = unbind_pmeta bnd in
        Debug.exec (fun () -> pr "case_introed(%a : %a)@." Var.pp x pp_tm a);
        let ctx = Ctx.add_var x a ctx in
        let prbm = prbm_add env prbm x a in
        aux_prbm ctx prbm b
      | a -> failwith "trans1e.check_cls(Intro(%a, %a))" pp_tm a (pp_ps " ") ps)
    (* case splitting *)
    | (eqns, [], rhs) :: _ when can_split eqns -> (
      Debug.exec (fun () -> pr "case_splitting@.");
      let x, b = first_split eqns in
      match whnf env b with
      | Ind (d, ss, ms, _) ->
        let _, cs = Ctx.find_ind d ctx in
        List.iter
          (fun c ->
            Debug.exec (fun () -> pr "splitting_on(%a)@." Constr.pp c);
            let sch = Ctx.find_constr c ctx in
            let param = msubst sch (Array.of_list ss) in
            let tele = param_inst param ms in
            let args, t = unbind_tele tele in
            let ctx =
              List.fold_left (fun ctx (_, x, a) -> Ctx.add_var x a ctx) ctx args
            in
            let m =
              Constr (c, ss, ms, List.map (fun (_, x, _) -> PMeta x) args)
            in
            let var_map = Var.Map.singleton x m in
            let a = subst_pmeta var_map a in
            let ctx = Ctx.map_var (subst_pmeta var_map) ctx in
            let prbm = prbm_simpl ctx var_map prbm in
            let prbm =
              PPrbm.{ prbm with global = EqualTerm (env, b, t) :: prbm.global }
            in
            aux_prbm ctx prbm a)
          cs
      | b -> failwith "trans1e.check_cls(Split(%a))" pp_tm b)
    (* absurd pattern *)
    | (eqns, [], rhs) :: _ when is_absurd eqns rhs -> (
      Debug.exec (fun () -> pr "case_absurd@.");
      if succeed_pprbm prbm.global then
        let a = get_absurd eqns in
        match whnf env a with
        | Ind (d, ss, ms, ns) -> fail_on_ind prbm.global ctx d ss ms a
        | _ -> failwith "trans1e.check_cls(Absurd)")
    (* case coverage *)
    | (eqns, [], rhs) :: _ -> (
      Debug.exec (fun () ->
          pr "@[<v 0>case_coverage{|@;<1 2>%a@;<1 0>|}@]@." PPrbm.pp prbm);
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
        if succeed_pprbm prbm.global then failwith "trans1e.check_cls(Cover)")
  in
  let prbm = PPrbm.of_cls cls in
  let a = State.resolve a in
  Debug.exec (fun () ->
      pr "@[<v 0>check_cls {|@;<1 2>%a@;<1 2>a := @[%a@]@;<1 0>|}@]@." PPrbm.pp
        prbm pp_tm a);
  aux_prbm ctx prbm a

and prbm_add env prbm x a =
  match prbm.clause with
  | [] -> prbm
  | (eqns, p :: ps, rhs) :: clause ->
    let prbm = prbm_add env { prbm with clause } x a in
    let clause =
      (eqns @ [ PPrbm.EqualPat (env, PMeta x, p, a) ], ps, rhs) :: prbm.clause
    in
    { prbm with clause }
  | _ -> failwith "trans1e.prbm_add"

and prbm_simpl ctx var_map prbm =
  let rec aux_global = function
    | [] -> []
    | PPrbm.EqualTerm (env, a, b) :: eqns ->
      let a = subst_pmeta var_map a in
      let b = subst_pmeta var_map b in
      let eqns = aux_global eqns in
      PPrbm.EqualTerm (env, a, b) :: eqns
    | PPrbm.EqualPat _ :: _ -> failwith "trans1e.prbm_simpl(Global)"
  in
  let rec aux_clause = function
    | [] -> []
    | (eqns, ps, rhs) :: clause -> (
      let clause = aux_clause clause in
      let opt =
        List.fold_left
          (fun acc eqn ->
            match (acc, eqn) with
            | Some acc, PPrbm.EqualPat (env, l, r, a) -> (
              let l = subst_pmeta var_map l in
              let a = subst_pmeta var_map a in
              match p_simpl ctx env l r a with
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

and p_simpl ctx env m p a =
  let a = whnf env a in
  match (m, p, a) with
  | Constr (c1, _, _, ns), PConstr (c2, ps), Ind (d, ss, ms, _) ->
    let _, cs = Ctx.find_ind d ctx in
    if List.exists (fun c -> Constr.equal c c2) cs then
      if Constr.equal c1 c2 then
        let sch = Ctx.find_constr c1 ctx in
        let param = msubst sch (Array.of_list ss) in
        let tele = param_inst param ms in
        ps_simpl ctx env ns ps tele
      else
        None
    else
      failwith "trans1e.p_simpl"
  | Constr _, _, Ind _ -> Some [ PPrbm.EqualPat (env, m, p, a) ]
  | _, PConstr (c2, _), Ind (d, _, _, _) ->
    let _, cs = Ctx.find_ind d ctx in
    if List.exists (fun c -> Constr.equal c c2) cs then
      Some [ PPrbm.EqualPat (env, m, p, a) ]
    else
      failwith "trans1e.p_simpl"
  | m, p, a -> Some [ PPrbm.EqualPat (env, m, p, a) ]

and ps_simpl ctx env ms ps tele =
  match (ms, ps, tele) with
  | m :: ms, p :: ps, TBind (_, a, bnd) -> (
    let opt1 = p_simpl ctx env m p a in
    let tele = subst bnd m in
    let opt2 = ps_simpl ctx env ms ps tele in
    match (opt1, opt2) with
    | Some eqns1, Some eqns2 -> Some (eqns1 @ eqns2)
    | _ -> None)
  | [], [], TBase _ -> Some []
  | _ -> None

let rec check_dcls ctx env dcls =
  let solve_delayed entries =
    Debug.exec (fun () -> State.dump ());
    let rec loop i entries =
      match entries with
      | [] -> State.solve_all ()
      | (ctx, env, m, a) :: entries when 0 < i ->
        let meta_map = State.solve_all () in
        let ctx = Ctx.map_var (resolve_tm meta_map) ctx in
        let env = Env.map_var (resolve_tm meta_map) env in
        let m = resolve_tm meta_map m in
        let a = resolve_tm meta_map a in
        assert_type ctx env a;
        check_tm ctx env m a;
        let entries0 = State.get_delayed () in
        loop (i - 1) (entries0 @ entries)
      | _ -> failwith "trans1e.solve_delayed(Timeout)"
    in
    loop (10 * List.length entries) entries
  in
  match dcls with
  | Definition { name = x; relv; scheme = sch } :: dcls ->
    Debug.exec (fun () -> pr "definition-------------------------@.");
    let ss, (m, a) = unmbind sch in
    let ctx0 = Array.fold_right Ctx.add_svar ss ctx in
    assert_type ctx0 env a;
    check_tm ctx0 env m a;
    let meta_map = solve_delayed (State.get_delayed ()) in
    let a_sch = bind_mvar ss (lift_tm (resolve_tm meta_map a)) in
    let m_sch = bind_mvar ss (lift_tm (resolve_tm meta_map m)) in
    let ctx = Ctx.add_const x (unbox a_sch) ctx in
    let env = Env.add_const x (unbox m_sch) env in
    Debug.exec (fun () -> pr "----------------------------------@.@.");
    check_dcls ctx env dcls
  | Inductive { name = ind; relv; arity; dconstrs } :: dcls ->
    Debug.exec (fun () -> pr "inductive-------------------------@.");
    check_arity ctx env arity;
    let ctx0 = Ctx.add_ind ind (arity, []) ctx in
    check_dconstrs ind ctx0 env dconstrs;
    let meta_map = solve_delayed (State.get_delayed ()) in
    let arity =
      resolve_scheme (lift_param lift_tele)
        (resolve_param lift_tele resolve_tele)
        meta_map arity
    in
    let dconstrs = resolve_dconstrs meta_map dconstrs in
    let cs, ctx =
      List.fold_right
        (fun (c, sch) (acc, ctx) -> (c :: acc, Ctx.add_constr c sch ctx))
        dconstrs ([], ctx)
    in
    let ctx = Ctx.add_ind ind (arity, cs) ctx in
    Debug.exec (fun () -> pr "----------------------------------@.@.");
    check_dcls ctx env dcls
  | [] -> State.solve_all ()

and check_arity ctx env arity =
  let rec aux_param ctx = function
    | PBase tele -> aux_tele ctx tele
    | PBind (a, bnd) ->
      let x, b = unbind bnd in
      assert_type ctx env a;
      aux_param (Ctx.add_var x a ctx) b
  and aux_tele ctx = function
    | TBase (Type s) -> ()
    | TBind (R, a, bnd) ->
      let x, b = unbind bnd in
      assert_type ctx env a;
      aux_tele ctx b
    | _ -> failwith "trans1e.check_arity(aux_tele)"
  in
  let ss, param = unmbind arity in
  let ctx = Array.fold_right Ctx.add_svar ss ctx in
  aux_param ctx param

and check_dconstrs ind ctx env dconstrs =
  let check_dconstr ind ctx dconstr =
    let rec aux_param sids args ctx = function
      | PBase tele -> aux_tele sids (List.rev args) ctx tele
      | PBind (a, bnd) ->
        let x, b = unbind bnd in
        assert_type ctx env a;
        aux_param sids (x :: args) (Ctx.add_var x a ctx) b
    and aux_tele sids xs ctx = function
      | TBase (Ind (x, ss, ms, ns) as a) ->
        List.iter2 (fun sid s -> assert_equal0 (SVar sid) s) sids ss;
        List.iter2 (fun x m -> assert_equal1 env (Var x) m) xs ms;
        assert_type ctx env a
      | TBind (_, a, bnd) ->
        let x, b = unbind bnd in
        assert_type ctx env a;
        aux_tele sids xs (Ctx.add_var x a ctx) b
      | _ -> failwith "trans1e.check_dconstr(aux_tele)"
    in
    let _, sch = dconstr in
    let sids, param = unmbind sch in
    aux_param (Array.to_list sids) [] ctx param
  in
  List.iter (check_dconstr ind ctx) dconstrs

let trans_dcls dcls =
  let meta_map = check_dcls Ctx.empty Env.empty dcls in
  Debug.exec (fun () -> pr "%a@." pp_meta meta_map);
  resolve_dcls meta_map dcls
