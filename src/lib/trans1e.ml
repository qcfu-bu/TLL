open Fmt
open Bindlib
open Names
open Syntax1
open Context1
open Constraint1
open Equality1
open Unifier1
open Pprint1
open Debug

module State : sig
  type t

  val add_eqn : IPrbm.eqn -> unit
  val add_imeta : Ctx.t -> IMeta.t -> sorts -> tms -> tm -> unit
  val find_imeta : IMeta.t -> tm option
  val resolve : tm -> tm
  val get_delayed : unit -> (Ctx.t * tm * tm) list
  val solve_all : unit -> meta_map
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

  let add_imeta ctx x ss xs a =
    state.mctx <- MCtx.add_imeta ctx x ss xs a state.mctx

  let find_imeta x = MCtx.find_imeta x state.mctx

  let resolve m =
    let meta_map, eqns = unify_iprbm state.meta_map state.eqns in
    state.meta_map <- meta_map;
    state.eqns <- eqns;
    resolve_tm meta_map m

  let get_delayed () =
    let mctx = state.mctx in
    Debug.exec (fun () ->
        pr
          "@[<v 0>begin_delayed@;\
           <1 2>%a@;\
           <1 2>%a@;\
           <1 2>@[%a@]@;\
           <1 0>end_delayed@]@." MCtx.pp mctx pp_meta state.meta_map
          IPrbm.pp_eqns state.eqns);
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
    loop 1000
end

let has_failed f =
  try
    f ();
    false
  with
  | _ -> true

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

let assert_equal1 ctx m1 m2 =
  Debug.exec (fun () -> pr "assert_equal1(%a, %a)@." pp_tm m1 pp_tm m2);
  if not (eq_tm ctx m1 m2) then State.add_eqn (EqualTerm (ctx, m1, m2))

let rec assert_type ctx a =
  let t = infer_tm ctx a in
  let t = State.resolve t in
  match whnf ~expand:true ctx t with
  | Type _ -> ()
  | IMeta _ as m ->
    let s = smeta_of_ctx ctx in
    Debug.exec (fun () -> pr "delay_assert(%a, %a)@." pp_tm m pp_sort s);
    State.add_eqn (EqualTerm (ctx, m, Type s))
  | t -> failwith "trans1e.assert_type(%a : %a)" pp_tm a pp_tm t

and infer_tm ctx m : tm =
  Debug.exec (fun () -> pr "infer_tm(%a)@." pp_tm m);
  match m with
  (* inference *)
  | Ann (m, a) ->
    assert_type ctx a;
    check_tm ctx m a;
    a
  | IMeta (x, ss, xs) -> (
    match State.find_imeta x with
    | Some a -> a
    | None ->
      let a = imeta_of_ctx ctx in
      State.add_imeta ctx x ss xs a;
      a)
  | PMeta x -> Ctx.find_var0 x ctx
  (* core *)
  | Type _ -> Type U
  | Var x -> Ctx.find_var0 x ctx
  | Const (x, ss) ->
    let sch = Ctx.find_const x ctx in
    snd (msubst sch (Array.of_list ss))
  | Pi (rel, s, a, bnd) ->
    let x, b = unbind bnd in
    assert_type ctx a;
    assert_type (Ctx.add_var0 x a ctx) b;
    Type s
  | Fun (a, bnd) ->
    let x, cls = unbind bnd in
    assert_type ctx a;
    check_cls (Ctx.add_var0 x a ctx) cls a;
    a
  | App (m, n) -> (
    let t = infer_tm ctx m in
    let t = State.resolve t in
    match whnf ~expand:true ctx t with
    | Pi (_, _, a, bnd) ->
      check_tm ctx n a;
      subst bnd n
    | _ -> failwith "trans1e.App")
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let a = infer_tm ctx m in
    infer_tm (Ctx.add_var1 x m a ctx) n
  (* inductive *)
  | Ind (d, ss, ms, ns) ->
    let sch, _ = Ctx.find_ind d ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_ind ctx ms ns ptl
  | Constr (c, ss, ms, ns) ->
    let sch, _ = Ctx.find_constr c ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_constr ctx ms ns ptl
  | Match (ms, a, cls) ->
    assert_type ctx a;
    check_cls ctx cls a;
    infer_motive ctx ms a
  (* monad *)
  | IO a ->
    assert_type ctx a;
    Type L
  | Return m -> IO (infer_tm ctx m)
  | MLet (m, bnd) -> (
    let t1 = infer_tm ctx m in
    let t1 = State.resolve t1 in
    match whnf ~expand:true ctx t1 with
    | IO a -> (
      let x, n = unbind bnd in
      let t2 = infer_tm (Ctx.add_var0 x a ctx) n in
      let t2 = State.resolve t2 in
      match whnf ~expand:true ctx t2 with
      | IO b -> IO b
      | _ -> failwith "trans1e.MLet")
    | _ -> failwith "trans1e.MLet")
  (* magic *)
  | Magic a -> a

and infer_ind ctx ms ns ptl =
  let rec aux_param ms ptl =
    match (ms, ptl) with
    | [], PBase tl -> aux_tele ns tl
    | m :: ms, PBind (a, bnd) ->
      check_tm ctx m a;
      aux_param ms (subst bnd m)
    | _ -> failwith "trans1e.infer_ind(param)"
  and aux_tele ns tl =
    match (ns, tl) with
    | [], TBase a -> a
    | n :: ns, TBind (_, a, bnd) ->
      check_tm ctx n a;
      aux_tele ns (subst bnd n)
    | _ -> failwith "trans1e.infer_ind(tele)"
  in
  aux_param ms ptl

and infer_constr ctx ms ns ptl =
  let rec aux_param ms ptl =
    match (ms, ptl) with
    | [], PBase tl -> aux_tele ns tl
    | m :: ms, PBind (a, bnd) ->
      check_tm ctx m a;
      aux_param ms (subst bnd m)
    | _ -> failwith "trans1e.infer_constr(param)"
  and aux_tele ns tl =
    match (ns, tl) with
    | [], TBase a -> a
    | n :: ns, TBind (_, a, bnd) ->
      check_tm ctx n a;
      aux_tele ns (subst bnd n)
    | _ -> failwith "trans1e.infer_constr(tele)"
  in
  aux_param ms ptl

and infer_motive ctx ms a =
  match (ms, whnf ~expand:true ctx a) with
  | [], a -> a
  | m :: ms, Pi (_, _, a, bnd) ->
    check_tm ctx m a;
    infer_motive ctx ms (subst bnd m)
  | _ -> failwith "trans1e.infer_motive"

and check_tm ctx m a : unit =
  Debug.exec (fun () -> pr "check_tm(%a, %a)@." pp_tm m pp_tm a);
  match m with
  (* inference *)
  | IMeta (x, ss, xs) -> State.add_imeta ctx x ss xs a
  | _ ->
    let b = infer_tm ctx m in
    assert_equal1 ctx a b

and check_cls ctx cls a : unit =
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
    | PPrbm.EqualPat (_, PMeta _, PMul _, _) :: _ -> true
    | PPrbm.EqualPat (_, PMeta _, PAdd _, _) :: _ -> true
    | _ :: eqns -> can_split eqns
    | [] -> false
  in
  let rec first_split = function
    | PPrbm.EqualPat (_, PMeta x, PMul _, a) :: _ -> (x, a)
    | PPrbm.EqualPat (_, PMeta x, PAdd _, a) :: _ -> (x, a)
    | _ :: eqns -> first_split eqns
    | [] -> failwith "trans1e.first_split"
  in
  let fail_on_ind global ctx ind ss ms a =
    let _, cs = Ctx.find_ind ind ctx in
    List.iter
      (fun c ->
        let sch, _ = Ctx.find_constr c ctx in
        let param = msubst sch (Array.of_list ss) in
        let tele = param_inst param ms in
        let _, t = unbind_tele tele in
        let global = PPrbm.EqualTerm (ctx, a, t) :: global in
        if not (has_failed (fun () -> unify_pprbm global)) then
          failwith "trans1e.fail_on_ind")
      cs
  in
  let rec aux_prbm ctx (prbm : PPrbm.t) a =
    match prbm.clause with
    (* empty *)
    | [] -> (
      if not (has_failed (fun () -> unify_pprbm prbm.global)) then
        match whnf ~expand:true ctx a with
        | Pi (_, _, a, _) -> (
          match whnf ~expand:true ctx a with
          | Ind (d, ss, ms, ns) -> fail_on_ind prbm.global ctx d ss ms a
          | _ -> failwith "trans1e.check_cls(Empty)")
        | _ -> failwith "trans1e.check_cls(Empty)")
    (* case intro *)
    | (eqns, p :: ps, rhs) :: clause -> (
      match whnf ~expand:true ctx a with
      | Pi (_, _, a, bnd) ->
        let x, b = unbind_pmeta bnd in
        let ctx = Ctx.add_var0 x a ctx in
        let prbm = prbm_add ctx prbm x a in
        aux_prbm ctx prbm b
      | a -> failwith "trans1e.check_cls(Intro, %a, %a)" pp_tm a (pp_ps " ") ps)
    (* absurd pattern *)
    | (eqns, [], rhs) :: _ when is_absurd eqns rhs -> (
      if not (has_failed (fun () -> unify_pprbm prbm.global)) then
        let a = get_absurd eqns in
        match whnf ~expand:true ctx a with
        | Ind (d, ss, ms, ns) -> fail_on_ind prbm.global ctx d ss ms a
        | _ -> failwith "trans1e.check_cls(Absurd)")
    (* case splitting *)
    | (eqns, [], rhs) :: _ when can_split eqns -> (
      let x, b = first_split eqns in
      match whnf ~expand:true ctx b with
      | Ind (d, ss, ms, _) ->
        let _, cs = Ctx.find_ind d ctx in
        List.iter
          (fun c ->
            let sch, _ = Ctx.find_constr c ctx in
            let param = msubst sch (Array.of_list ss) in
            let tele = param_inst param ms in
            let args, t = unbind_tele tele in
            let ctx =
              List.fold_left
                (fun acc (_, x, a) -> Ctx.add_var0 x a acc)
                ctx args
            in
            let m =
              Constr (c, ss, ms, List.map (fun (_, x, _) -> PMeta x) args)
            in
            let var_map = Var.Map.singleton x m in
            let a = presolve_tm var_map a in
            let ctx = presolve_ctx var_map ctx in
            let prbm = prbm_simpl ctx var_map prbm in
            let prbm =
              PPrbm.{ prbm with global = EqualTerm (ctx, b, t) :: prbm.global }
            in
            aux_prbm ctx prbm a)
          cs
      | _ -> failwith "trans1e.check_cls(Split)")
    (* case coverage *)
    | (eqns, [], rhs) :: _ ->
      Debug.exec (fun () ->
          pr "@[<v 0>case_coverage{|@;<1 2>%a@;<1 0>|}@]@." PPrbm.pp prbm);
      let var_map = unify_pprbm (prbm.global @ eqns) in
      let a = presolve_tm var_map a in
      let ctx = presolve_ctx var_map ctx in
      let rhs =
        match rhs with
        | Some m -> presolve_tm var_map m
        | None -> failwith "trans1e.check_cls(Cover)"
      in
      Debug.exec (fun () -> pr "case_coverage_ok(%a, %a)@." pp_tm rhs pp_tm a);
      check_tm ctx rhs a
  in
  let prbm = PPrbm.of_cls cls in
  let a = State.resolve a in
  aux_prbm ctx prbm a

and prbm_add ctx prbm x a =
  match prbm.clause with
  | [] -> prbm
  | (eqns, p :: ps, rhs) :: clause ->
    let prbm = prbm_add ctx { prbm with clause } x a in
    let clause =
      (eqns @ [ PPrbm.EqualPat (ctx, PMeta x, p, a) ], ps, rhs) :: prbm.clause
    in
    { prbm with clause }
  | _ -> failwith "trans1e.prbm_add"

and prbm_simpl ctx var_map prbm =
  let rec aux_global = function
    | [] -> []
    | PPrbm.EqualTerm (ctx, a, b) :: eqns ->
      let a = presolve_tm var_map a in
      let b = presolve_tm var_map b in
      let eqns = aux_global eqns in
      PPrbm.EqualTerm (ctx, a, b) :: eqns
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
            | Some acc, PPrbm.EqualPat (ctx, l, r, a) -> (
              let l = presolve_tm var_map l in
              let a = presolve_tm var_map a in
              match p_simpl ctx l r a with
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

and p_simpl ctx m p a =
  let a = whnf ~expand:true ctx a in
  match (m, p, a) with
  | Constr (c1, _, _, ns1), PMul (c2, ps), Ind (d, ss, ms, ns2) ->
    let _, cs = Ctx.find_ind d ctx in
    if List.exists (fun c -> Constr.equal c c2) cs then
      if Constr.equal c1 c2 then
        let sch, _ = Ctx.find_constr c1 ctx in
        let param = msubst sch (Array.of_list ss) in
        let tele = param_inst param ms in
        ps_simpl ctx ns1 ps tele
      else
        None
    else
      failwith "trans1e.p_simpl"
  | Constr (c1, _, _, ns1), PAdd (c2, i, ps), Ind (d, ss, ms, ns2) ->
    let _, cs = Ctx.find_ind d ctx in
    if List.exists (fun c -> Constr.equal c c2) cs then
      if Constr.equal c1 c2 then
        let sch, _ = Ctx.find_constr c1 ctx in
        let param = msubst sch (Array.of_list ss) in
        let tele = param_inst param ms in
        ps_simpl ctx ns1 ps tele
      else
        None
    else
      failwith "trans1e.p_simpl"
  | Constr (c1, _, _, _), _, Ind (d, _, _, _) ->
    Some [ PPrbm.EqualPat (ctx, m, p, a) ]
  | _, PMul (c2, _), Ind (d, _, _, _) ->
    let _, cs = Ctx.find_ind d ctx in
    if List.exists (fun c -> Constr.equal c c2) cs then
      Some [ PPrbm.EqualPat (ctx, m, p, a) ]
    else
      failwith "trans1e.p_simpl"
  | _, PAdd (c2, _, _), Ind (d, _, _, _) ->
    let _, cs = Ctx.find_ind d ctx in
    if List.exists (fun c -> Constr.equal c c2) cs then
      Some [ PPrbm.EqualPat (ctx, m, p, a) ]
    else
      failwith "trans1e.p_simpl"
  | m, p, a -> Some [ PPrbm.EqualPat (ctx, m, p, a) ]

and ps_simpl ctx ms ps tele =
  match (ms, ps, tele) with
  | m :: ms, p :: ps, TBind (_, a, bnd) -> (
    let opt1 = p_simpl ctx m p a in
    let tele = subst bnd m in
    let opt2 = ps_simpl ctx ms ps tele in
    match (opt1, opt2) with
    | Some eqns1, Some eqns2 -> Some (eqns1 @ eqns2)
    | _ -> None)
  | [], [], TBase _ -> Some []
  | _ -> None

let rec check_dcls ctx dcls =
  let solve_delayed entries =
    let rec loop i entries =
      match entries with
      | [] -> State.solve_all ()
      | (ctx, m, a) :: entries when 0 < i ->
        let meta_map = State.solve_all () in
        let ctx = resolve_ctx meta_map ctx in
        let m = resolve_tm meta_map m in
        let a = resolve_tm meta_map a in
        Debug.exec (fun () -> pr "loop_check(%a %a)@." pp_tm m pp_tm a);
        assert_type ctx a;
        check_tm ctx m a;
        let entries0 = State.get_delayed () in
        loop (i - 1) (entries0 @ entries)
      | _ -> failwith "trans1e.solve_delayed(Timeout)"
    in
    loop 1000 entries
  in
  match dcls with
  | Definition { name = x; relv; scheme = sch } :: dcls ->
    Debug.exec (fun () -> pr "definition-------------------------@.");
    let ss, (m, a) = unmbind sch in
    let ctx0 = Array.fold_right Ctx.add_svar ss ctx in
    assert_type ctx0 a;
    check_tm ctx0 m a;
    let meta_map = solve_delayed (State.get_delayed ()) in
    let sch =
      resolve_scheme
        (fun (m, a) -> box_pair (lift_tm m) (lift_tm a))
        (fun meta_map (m, a) -> (resolve_tm meta_map m, resolve_tm meta_map a))
        meta_map sch
    in
    let ctx = Ctx.add_const x sch ctx in
    Debug.exec (fun () -> pr "----------------------------------@.@.");
    check_dcls ctx dcls
  | Inductive { name = ind; relv; arity; dconstrs } :: dcls ->
    Debug.exec (fun () -> pr "inductive-------------------------@.");
    check_arity ctx arity;
    let ctx0 = Ctx.add_ind ind (arity, []) ctx in
    check_dconstrs ind ctx0 dconstrs;
    let meta_map = solve_delayed (State.get_delayed ()) in
    let arity =
      resolve_scheme (lift_param lift_tele)
        (resolve_param lift_tele resolve_tele)
        meta_map arity
    in
    let dconstrs = resolve_dconstrs meta_map dconstrs in
    let cs, ctx =
      List.fold_right
        (fun (mode, c, sch) (acc, ctx) ->
          (c :: acc, Ctx.add_constr c (sch, mode) ctx))
        dconstrs ([], ctx)
    in
    let ctx = Ctx.add_ind ind (arity, cs) ctx in
    Debug.exec (fun () -> pr "----------------------------------@.@.");
    check_dcls ctx dcls
  | [] -> State.solve_all ()

and check_arity ctx arity =
  let rec aux_param ctx = function
    | PBase tele -> aux_tele ctx tele
    | PBind (a, bnd) ->
      let x, b = unbind bnd in
      assert_type ctx a;
      aux_param (Ctx.add_var0 x a ctx) b
  and aux_tele ctx = function
    | TBase (Type s) -> ()
    | TBind (R, a, bnd) ->
      let x, b = unbind bnd in
      assert_type ctx a;
      aux_tele ctx b
    | _ -> failwith "trans1e.check_arity(aux_tele)"
  in
  let ss, param = unmbind arity in
  let ctx = Array.fold_right Ctx.add_svar ss ctx in
  aux_param ctx param

and check_dconstrs ind ctx dconstrs =
  let check_dconstr ind ctx dconstr =
    let rec aux_param sids args ctx = function
      | PBase tele -> aux_tele sids (List.rev args) ctx tele
      | PBind (a, bnd) ->
        let x, b = unbind bnd in
        assert_type ctx a;
        aux_param sids (x :: args) (Ctx.add_var0 x a ctx) b
    and aux_tele sids xs ctx = function
      | TBase (Ind (x, ss, ms, ns) as a) ->
        List.iter2 (fun sid s -> assert_equal0 (SVar sid) s) sids ss;
        List.iter2 (fun x m -> assert_equal1 ctx (Var x) m) xs ms;
        assert_type ctx a
      | TBind (_, a, bnd) ->
        let x, b = unbind bnd in
        assert_type ctx a;
        aux_tele sids xs (Ctx.add_var0 x a ctx) b
      | _ -> failwith "trans1e.check_dconstr(aux_tele)"
    in
    let _, _, sch = dconstr in
    let sids, param = unmbind sch in
    aux_param (Array.to_list sids) [] ctx param
  in
  List.iter (check_dconstr ind ctx) dconstrs

let trans_dcls dcls =
  let meta_map = check_dcls Ctx.empty dcls in
  Debug.exec (fun () -> pr "%a@." pp_meta meta_map);
  resolve_dcls meta_map dcls
