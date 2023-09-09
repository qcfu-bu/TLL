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

  val add_imeta :
    Ctx.t -> Env.t -> IMeta.t -> sorts box -> tms box -> tm -> unit

  val find_imeta : IMeta.t -> (sorts box * tms box * tm) option
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

let spine_of_ctx (ctx : Ctx.t) =
  let ss = Ctx.spine_svar ctx |> List.map _SVar |> box_list in
  let xs = Ctx.spine_var ctx |> List.map _Var |> box_list in
  (ss, xs)

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

let rec assert_type ctx env a : tm box =
  Debug.exec (fun () -> pr "assert_type(%a)@." pp_tm a);
  let t, a_elab = infer_tm ctx env a in
  Debug.exec (fun () -> pr "assert_type_ok(%a, %a)@." pp_tm a pp_tm t);
  let t = State.resolve t in
  match whnf env t with
  | Type _ -> a_elab
  | IMeta _ as m ->
    let s = smeta_of_ctx ctx in
    Debug.exec (fun () -> pr "delay_assert(%a, %a)@." pp_tm m pp_sort s);
    State.add_eqn (EqualTerm (env, m, Type s));
    a_elab
  | t -> failwith "trans1e.assert_type(%a : %a)" pp_tm a pp_tm t

and infer_tm ctx env m : tm * tm box =
  (* ctx ⊢ m => (T_elab, m_elab) *)
  Debug.exec (fun () -> pr "infer_tm(%a)@." pp_tm m);
  match m with
  (* inference *)
  | Ann (m, a) ->
    let a_elab = assert_type ctx env a in
    let a = unbox a_elab in
    let m_elab = check_tm ctx env m a in
    (a, _Ann m_elab a_elab)
  | IMeta (x, _, _) ->
    (match State.find_imeta x with
     | Some (ss, xs, a) -> (a, _IMeta x ss xs)
     | None ->
       let a = imeta_of_ctx ctx in
       let ss, xs = spine_of_ctx ctx in
       State.add_imeta ctx env x ss xs a;
       (a, _IMeta x ss xs))
  | PMeta _ -> failwith "trans1e.infer_tm(PMeta)"
  (* core *)
  | Type s -> (Type U, _Type (lift_sort s))
  | Var x -> (Ctx.find_var x ctx, _Var x)
  | Const (x, ss) ->
    let ss_elab = ss |> List.map lift_sort |> box_list in
    (msubst (Ctx.find_const x ctx) (Array.of_list ss), _Const x ss_elab)
  | Pi (relv, s, a, bnd) ->
    let x, b = unbind bnd in
    let a_elab = assert_type ctx env a in
    let a = unbox a_elab in
    let b_elab = assert_type (Ctx.add_var x a ctx) env b in
    (Type s, _Pi relv (lift_sort s) a_elab (bind_var x b_elab))
  | Fun (guard, a, bnd) ->
    let x, cls = unbind bnd in
    let a_elab = assert_type ctx env a in
    let a = unbox a_elab in
    let cls_elab = check_cls (Ctx.add_var x a ctx) env cls a in
    (a, _Fun guard a_elab (bind_var x cls_elab))
  | App (m, n) ->
    (let t, m_elab = infer_tm ctx env m in
     let t = State.resolve t in
     match whnf env t with
     | Pi (_, _, a, bnd) ->
       let n_elab = check_tm ctx env n a in
       let n = unbox n_elab in
       (subst bnd n, _App m_elab n_elab)
     | _ -> failwith "trans1e.App")
  | Let (relv, m, bnd) ->
    let x, n = unbind bnd in
    let a, m_elab = infer_tm ctx env m in
    let m = unbox m_elab in
    let b, n_elab = infer_tm (Ctx.add_var x a ctx) (Env.add_var x m env) n in
    (b, _Let relv m_elab (bind_var x n_elab))
  (* inductive *)
  | Ind (d, ss, ms, ns) ->
    let sch, _ = Ctx.find_ind d ctx in
    let ptl = msubst sch (Array.of_list ss) in
    let ss_elab = ss |> List.map lift_sort |> box_list in
    let a, ms_elab, ns_elab = infer_ptl ctx env ms ns ptl in
    (a, _Ind d ss_elab ms_elab ns_elab)
  | Constr (c, ss, ms, ns) ->
    let sch = Ctx.find_constr c ctx in
    let ptl = msubst sch (Array.of_list ss) in
    let ss_elab = ss |> List.map lift_sort |> box_list in
    let a, ms_elab, ns_elab = infer_ptl ctx env ms ns ptl in
    (a, _Constr c ss_elab ms_elab ns_elab)
  | Match (guard, ms, a, cls) ->
    let b, ms_elab, a_elab = infer_motive ctx env ms a in
    let a = unbox a_elab in
    let cls_elab = check_cls ctx env cls a in
    (b, _Match guard ms_elab a_elab cls_elab)
  (* monad *)
  | IO a ->
    let a_elab = assert_type ctx env a in
    (Type L, _IO a_elab)
  | Return m ->
    let a, m_elab = infer_tm ctx env m in
    (IO a, _Return m_elab)
  | MLet (m, bnd) ->
    (let t1, m_elab = infer_tm ctx env m in
     let t1 = State.resolve t1 in
     match whnf env t1 with
     | IO a ->
       (let x, n = unbind bnd in
        let t2, n_elab = infer_tm (Ctx.add_var x a ctx) env n in
        let t2 = State.resolve t2 in
        match whnf env t2 with
        | IO b -> (IO b, _MLet m_elab (bind_var x n_elab))
        | _ -> failwith "trans1e.MLet")
     | _ -> failwith "trans1e.MLet")
  (* magic *)
  | Magic a ->
    let a_elab = assert_type ctx env a in
    let a = unbox a_elab in
    (a, _Magic a_elab)

and infer_ptl ctx env ms ns ptl : tm * tms box * tms box =
  let rec aux_param ms ptl =
    match (ms, ptl) with
    | [], PBase tl ->
      let a, ns_elab = aux_tele ns tl in
      (a, [], ns_elab)
    | m :: ms, PBind (a, bnd) ->
      let m_elab = check_tm ctx env m a in
      let m = unbox m_elab in
      let a, ms_elab, ns_elab = aux_param ms (subst bnd m) in
      (a, m_elab :: ms_elab, ns_elab)
    | _ -> failwith "trans1e.infer_ptl(param)"
  and aux_tele ns tl =
    match (ns, tl) with
    | [], TBase a -> (a, [])
    | n :: ns, TBind (_, a, bnd) ->
      let n_elab = check_tm ctx env n a in
      let n = unbox n_elab in
      let a, ns_elab = aux_tele ns (subst bnd n) in
      (a, n_elab :: ns_elab)
    | _ -> failwith "trans1e.infer_ptl(tele)"
  in
  let a, ms_elab, ns_elab = aux_param ms ptl in
  (a, box_list ms_elab, box_list ns_elab)

and infer_motive ctx1 env ms a =
  (* a0: original motive
     a1 : instantiated motive *)
  let rec aux_motive ctx0 ms a0 a1 =
    match (ms, a0, a1) with
    | [], a0, a1 ->
      let a0_elab = assert_type ctx0 env a0 in
      let a1_elab = assert_type ctx1 env a1 in
      (unbox a1_elab, [], a0_elab)
    | m :: ms, Pi (relv, L, a0, bnd0), Pi (_, L, a1, bnd1) ->
      let x, b0 = unbind bnd0 in
      let a0_elab = assert_type ctx0 env a0 in
      let a1_elab = assert_type ctx1 env a1 in
      let a0 = unbox a0_elab in
      let a1 = unbox a1_elab in
      let m_elab = check_tm ctx1 env m a1 in
      let t, ms_elab, b0_elab =
        aux_motive (Ctx.add_var x a0 ctx0) ms b0 (subst bnd1 m)
      in
      (t, m_elab :: ms_elab, _Pi relv _L a0_elab (bind_var x b0_elab))
    | _ -> failwith "trans1e.infer_motive"
  in
  let b, ms_elab, a_elab = aux_motive ctx1 ms a a in
  (b, box_list ms_elab, a_elab)

and check_tm ctx env m a : tm box =
  (* ctx ⊢ m <= T_elab *)
  Debug.exec (fun () ->
      pr "@[check_tm(@;<1 2>%a,@;<1 2>%a)@]@." pp_tm m pp_tm a);
  match m with
  (* inference *)
  | IMeta (x, _, _) ->
    (match State.find_imeta x with
     | Some (ss, xs, b) ->
       assert_equal1 env a b;
       let m_elab = _IMeta x ss xs in
       m_elab
     | None ->
       let ss, xs = spine_of_ctx ctx in
       State.add_imeta ctx env x ss xs a;
       let m_elab = _IMeta x ss xs in
       m_elab)
  | Fun (guard, b, bnd) ->
    let x, cls = unbind bnd in
    let b_elab = assert_type ctx env b in
    let b = unbox b_elab in
    assert_equal1 env a b;
    let cls_elab = check_cls (Ctx.add_var x a ctx) env cls a in
    _Fun guard b_elab (bind_var x cls_elab)
  | _ ->
    let b, m_elab = infer_tm ctx env m in
    assert_equal1 env a b;
    m_elab

and check_cls ctx env cls a : cls box =
  let rec is_absurd eqns rhs =
    match (eqns, rhs) with
    | PPrbm.EqualPat (_, PMeta _, PAbsurd, _) :: _, None -> true
    | PPrbm.EqualPat (_, PMeta _, PAbsurd, _) :: _, Some _ ->
      failwith "trans1e.is_absurd"
    | _ :: eqns, _ -> is_absurd eqns rhs
    | [], _ -> false
  in
  let rec get_absurd = function
    | PPrbm.EqualPat (_, PMeta x, PAbsurd, a) :: _ -> (x, a)
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
    List.iter (fun c ->
        let sch = Ctx.find_constr c ctx in
        let param = msubst sch (Array.of_list ss) in
        let tele = param_inst param ms in
        let _, t = unbind_tele tele in
        let global = PPrbm.EqualTerm (env, a, t) :: global in
        if not (witness_distinct global) then
          failwith "trans1e.fail_on_ind(%a)" Ind.pp d)
      cs
  in
  let rec aux_prbm (ctx : Ctx.t) (prbm : PPrbm.t) a : cl box list =
    match prbm.clause with
    (* empty *)
    | [] ->
      Debug.exec (fun () -> pr "case_empty@.");
      if not (witness_distinct prbm.global) then
        match whnf env a with
        | Pi (_, _, a, _) ->
          (match whnf env a with
           | Ind (d, ss, ms, ns) ->
             fail_on_ind prbm.global ctx d ss ms a;
             []
           | _ -> failwith "trans1e.check_cls(Empty)")
        | _ -> failwith "trans1e.check_cls(Empty)"
      else []
    (* case intro *)
    | (eqns, p :: ps, rhs, _) :: clause ->
      (match whnf env a with
       | Pi (_, _, a, bnd) ->
         let x, b = unbind_pmeta bnd in
         Debug.exec (fun () -> pr "case_intro(%a : %a)@." Var.pp x pp_tm a);
         let ctx = Ctx.add_var x a ctx in
         let prbm = prbm_add env prbm x a in
         aux_prbm ctx prbm b
       | a -> failwith "trans1e.check_cls(Intro(%a, %a))" pp_tm a (pp_ps " ") ps)
    (* case splitting *)
    | (eqns, [], rhs, ps) :: _ when can_split eqns ->
      (let x, b = first_split eqns in
       match whnf env b with
       | Ind (d, ss, ms, _) ->
         let _, cs = Ctx.find_ind d ctx in
         List.concat_map (fun c ->
             Debug.exec (fun () -> pr "splitting_on(%a)@." Constr.pp c);
             let sch = Ctx.find_constr c ctx in
             let param = msubst sch (Array.of_list ss) in
             let tele = param_inst param ms in
             let args, t = unbind_tele tele in
             let ctx, args = List.fold_left_map (fun ctx (_, x, a) ->
                 (Ctx.add_var x a ctx, (PMeta x, PVar x)))
                 ctx args
             in
             let ns, ps = List.split args in
             let m = Constr (c, ss, ms, ns) in
             let p = PConstr (c, ps) in
             let var_map = Var.Map.singleton x m in
             let pvar_map = Var.Map.singleton x p in
             let a = subst_pmeta var_map a in
             let ctx = Ctx.map_var (subst_pmeta var_map) ctx in
             let prbm = prbm_simpl ctx var_map pvar_map prbm in
             let prbm = PPrbm.{ prbm with global = EqualTerm (env, b, t) :: prbm.global } in
             aux_prbm ctx prbm a)
           cs
       | b -> failwith "trans1e.check_cls(Split(%a : %a))" Var.pp x pp_tm b)
    (* absurd pattern *)
    | (eqns, [], rhs, ps) :: _ when is_absurd eqns rhs ->
      Debug.exec (fun () -> pr "case_absurd@.");
      let x, a = get_absurd eqns in
      let ps = expand_ps ps (Var.Map.singleton x PAbsurd) in
      if not (witness_distinct prbm.global) then
        match whnf env a with
        | Ind (d, ss, ms, ns) ->
          fail_on_ind prbm.global ctx d ss ms a;
          [ bind_ps ps _None ]
        | _ -> failwith "trans1e.check_cls(Absurd)"
      else [ bind_ps ps _None ]
    (* case coverage *)
    | (eqns, [], rhs, ps) :: _ ->
      (Debug.exec (fun () ->
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
         let rhs_elab = check_tm ctx env rhs a in
         [ bind_ps ps (_Some rhs_elab) ]
       | None ->
         if not (witness_distinct prbm.global) then
           failwith "trans1e.check_cls(Cover)"
         else [ bind_ps ps _None ])
  in
  let prbm = PPrbm.of_cls cls in
  let a = State.resolve a in
  Debug.exec (fun () ->
      pr "@[<v 0>check_cls {|@;<1 2>%a@;<1 2>a := @[%a@]@;<1 0>|}@]@." PPrbm.pp
        prbm pp_tm a);
  let cls_elab = aux_prbm ctx prbm a in
  box_list cls_elab

and prbm_add env prbm x a =
  match prbm.clause with
  | [] -> prbm
  | (eqns, p :: ps, rhs, ps0) :: clause ->
    let prbm = prbm_add env { prbm with clause } x a in
    let clause =
      (eqns @ [ PPrbm.EqualPat (env, PMeta x, p, a) ], ps, rhs, ps0 @ [ PVar x ])
      :: prbm.clause
    in { prbm with clause }
  | _ -> failwith "trans1e.prbm_add"

and prbm_simpl ctx var_map pvar_map prbm =
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
    | (eqns, [], rhs, ps) :: clause ->
      (let clause = aux_clause clause in
       let opt = List.fold_left (fun acc eqn ->
           match (acc, eqn) with
           | Some acc, PPrbm.EqualPat (env, l, r, a) ->
             (let l = subst_pmeta var_map l in
              let a = subst_pmeta var_map a in
              match p_simpl ctx env l r a with
              | Some eqns -> Some (acc @ eqns)
              | None -> None)
           | _ -> None)
           (Some []) eqns
       in
       match opt with
       | Some eqns -> (eqns, [], rhs, expand_ps ps pvar_map) :: clause
       | None -> clause)
    | _ -> failwith "trans1e.prbm_simpl(Clause)"
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
      else None
    else failwith "trans1e.p_simpl"
  | Constr _, _, Ind _ -> Some [ PPrbm.EqualPat (env, m, p, a) ]
  | _, PConstr (c2, _), Ind (d, _, _, _) ->
    let _, cs = Ctx.find_ind d ctx in
    if List.exists (fun c -> Constr.equal c c2) cs
    then Some [ PPrbm.EqualPat (env, m, p, a) ]
    else failwith "trans1e.p_simpl"
  | m, p, a -> Some [ PPrbm.EqualPat (env, m, p, a) ]

and ps_simpl ctx env ms ps tele =
  match (ms, ps, tele) with
  | m :: ms, p :: ps, TBind (_, a, bnd) ->
    (let opt1 = p_simpl ctx env m p a in
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
        Debug.exec (fun () -> pr "attempt_delay(%a : %a)@." pp_tm m pp_tm a);
        let ctx = Ctx.map_var (resolve_tm meta_map) ctx in
        Debug.exec (fun () -> pr "resolve_ctx_ok@.");
        let env = Env.map_var (resolve_tm meta_map) env in
        Debug.exec (fun () -> pr "resolve_env_ok@.");
        let m = resolve_tm meta_map m in
        let a = resolve_tm meta_map a in
        let _ = assert_type ctx env a in
        let _ = check_tm ctx env m a in
        let entries0 = State.get_delayed () in
        loop (i - 1) (entries0 @ entries)
      | _ -> failwith "trans1e.solve_delayed(Timeout)"
    in loop (10 * List.length entries) entries
  in
  match dcls with
  | Definition { name = x; relv; scheme = sch } :: dcls ->
    Debug.exec (fun () -> pr "definition-------------------------@.");
    let ss, (m, a) = unmbind sch in
    let ctx0 = Array.fold_right Ctx.add_svar ss ctx in
    let a_elab = assert_type ctx0 env a in
    let a = unbox a_elab in
    let m_elab = check_tm ctx0 env m a in
    let m = unbox m_elab in
    let meta_map = solve_delayed (State.get_delayed ()) in
    let a_box = lift_tm (resolve_tm meta_map a) in
    let m_box = lift_tm (resolve_tm meta_map m) in
    let a_sch = bind_mvar ss a_box in
    let m_sch = bind_mvar ss m_box in
    let sch = bind_mvar ss (box_pair m_box a_box) in
    let ctx = Ctx.add_const x (unbox a_sch) ctx in
    let env = Env.add_const x (unbox m_sch) env in
    Debug.exec (fun () -> pr "----------------------------------@.@.");
    let dcls = check_dcls ctx env dcls in
    Definition { name = x; relv; scheme = unbox sch } :: dcls
  | Inductive { name = ind; relv; arity; dconstrs } :: dcls ->
    Debug.exec (fun () -> pr "inductive-------------------------@.");
    let arity_elab = check_arity ctx env arity in
    let arity = unbox arity_elab in
    let ctx0 = Ctx.add_ind ind (arity, []) ctx in
    let dconstrs_elab = check_dconstrs ind ctx0 env dconstrs in
    let dconstrs = unbox dconstrs_elab in
    let meta_map = solve_delayed (State.get_delayed ()) in
    let arity =
      resolve_scheme (lift_param lift_tele)
        (resolve_param lift_tele resolve_tele)
        meta_map arity
    in
    let dconstrs = resolve_dconstrs meta_map dconstrs in
    let cs, ctx = List.fold_right (fun (c, sch) (acc, ctx) ->
        (c :: acc, Ctx.add_constr c sch ctx))
        dconstrs ([], ctx)
    in
    let ctx = Ctx.add_ind ind (arity, cs) ctx in
    Debug.exec (fun () -> pr "----------------------------------@.@.");
    let dcls = check_dcls ctx env dcls in
    Inductive { name = ind; relv; arity; dconstrs } :: dcls
  | Extern { name = x; relv; scheme = sch } :: dcls ->
    (Debug.exec (fun () -> pr "extern---------------------------------@.");
     let ss, (m_opt, a) = unmbind sch in
     match m_opt with
     | Some m ->
       let ctx0 = Array.fold_right Ctx.add_svar ss ctx in
       let a_elab = assert_type ctx0 env a in
       let a = unbox a_elab in
       let m_elab = check_tm ctx0 env m a in
       let m = unbox m_elab in
       let meta_map = solve_delayed (State.get_delayed ()) in
       let a_box = lift_tm (resolve_tm meta_map a) in
       let m_box = lift_tm (resolve_tm meta_map m) in
       let a_sch = bind_mvar ss a_box in
       let m_sch = bind_mvar ss m_box in
       let sch = bind_mvar ss (box_pair (box_opt (Some m_box)) a_box) in
       let ctx = Ctx.add_const x (unbox a_sch) ctx in
       let env = Env.add_const x (unbox m_sch) env in
       Debug.exec (fun () -> pr "----------------------------------@.@.");
       let dcls = check_dcls ctx env dcls in
       Extern { name = x; relv; scheme = unbox sch } :: dcls
     | None ->
       let ctx0 = Array.fold_right Ctx.add_svar ss ctx in
       let a_elab = assert_type ctx0 env a in
       let a = unbox a_elab in
       let meta_map = solve_delayed (State.get_delayed ()) in
       let a_box = lift_tm (resolve_tm meta_map a) in
       let m_box = box None in
       let a_sch = bind_mvar ss a_box in
       let sch = bind_mvar ss (box_pair m_box a_box) in
       let ctx = Ctx.add_const x (unbox a_sch) ctx in
       Debug.exec (fun () -> pr "----------------------------------@.@.");
       let dcls = check_dcls ctx env dcls in
       Extern { name = x; relv; scheme = unbox sch } :: dcls)
  | [] -> []

and check_arity ctx env arity =
  let rec aux_param ctx = function
    | PBase tele -> _PBase (aux_tele ctx tele)
    | PBind (a, bnd) ->
      let x, b = unbind bnd in
      let a_elab = assert_type ctx env a in
      let a = unbox a_elab in
      let b_elab = aux_param (Ctx.add_var x a ctx) b in
      _PBind a_elab (bind_var x b_elab)
  and aux_tele ctx = function
    | TBase (Type s) -> _TBase (_Type (lift_sort s))
    | TBind (R, a, bnd) ->
      let x, b = unbind bnd in
      let a_elab = assert_type ctx env a in
      let b_elab = aux_tele ctx b in
      _TBind R a_elab (bind_var x b_elab)
    | _ -> failwith "trans1e.check_arity(aux_tele)"
  in
  let ss, param = unmbind arity in
  let ctx = Array.fold_right Ctx.add_svar ss ctx in
  let param_elab = aux_param ctx param in
  bind_mvar ss param_elab

and check_dconstrs ind ctx env dconstrs =
  let check_dconstr ind ctx dconstr =
    let rec aux_param sids args ctx = function
      | PBase tele -> _PBase (aux_tele sids (List.rev args) ctx tele)
      | PBind (a, bnd) ->
        let x, b = unbind bnd in
        let a_elab = assert_type ctx env a in
        let a = unbox a_elab in
        let b_elab = aux_param sids (x :: args) (Ctx.add_var x a ctx) b in
        _PBind a_elab (bind_var x b_elab)
    and aux_tele sids xs ctx = function
      | TBase (Ind (x, ss, ms, ns) as a) -> (
          let a_elab = assert_type ctx env a in
          match unbox a_elab with
          | Ind (x, ss, ms, ns) ->
            List.iter2 (fun sid s -> assert_equal0 (SVar sid) s) sids ss;
            List.iter2 (fun x m -> assert_equal1 env (Var x) m) xs ms;
            _TBase a_elab
          | _ -> failwith "trans1e.check_dconstr(aux_tele)")
      | TBind (relv, a, bnd) ->
        let x, b = unbind bnd in
        let a_elab = assert_type ctx env a in
        let a = unbox a_elab in
        let b_elab = aux_tele sids xs (Ctx.add_var x a ctx) b in
        _TBind relv a_elab (bind_var x b_elab)
      | _ -> failwith "trans1e.check_dconstr(aux_tele)"
    in
    let c, sch = dconstr in
    let ss, param = unmbind sch in
    let ctx = Array.fold_right Ctx.add_svar ss ctx in
    let param_elab = aux_param (Array.to_list ss) [] ctx param in
    _DConstr c (bind_mvar ss param_elab)
  in
  box_list (List.map (check_dconstr ind ctx) dconstrs)

let trans_dcls dcls = check_dcls Ctx.empty Env.empty dcls
