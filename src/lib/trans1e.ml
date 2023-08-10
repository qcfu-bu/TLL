open Fmt
open Bindlib
open Names
open Syntax1
open Context1
open Constraint1
open Equality1
open Unifier1

module State : sig
  type t

  val add_eqn : IPrbm.eqn -> unit
  val add_imeta : Ctx.t -> IMeta.t -> tm -> unit
  val find_imeta : IMeta.t -> tm option
  val init : unit -> unit
  val export_eqns : unit -> IPrbm.eqns
  val export_mctx : unit -> MCtx.t
end = struct
  type t =
    { mutable eqns : IPrbm.eqns
    ; mutable mctx : MCtx.t
    }

  let state : t = { eqns = []; mctx = MCtx.empty }
  let add_eqn prbm = state.eqns <- prbm :: state.eqns
  let add_imeta ctx x a = state.mctx <- MCtx.add_imeta ctx x a state.mctx
  let find_imeta x = MCtx.find_imeta x state.mctx

  let init () =
    state.eqns <- [];
    state.mctx <- MCtx.empty

  let export_eqns () = state.eqns
  let export_mctx () = state.mctx
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
  if not (eq_tm ctx m1 m2) then State.add_eqn (EqualTerm (ctx, m1, m2))

let rec assert_type ctx a =
  let t = infer_tm ctx a in
  let t = resolve_tm (State.export_eqns ()) t in
  match whnf ~expand:true ctx t with
  | Type _ -> ()
  | _ -> failwith "trans1e.assert_type"

and infer_tm ctx m : tm =
  match m with
  (* inference *)
  | Ann (m, a) ->
    assert_type ctx a;
    check_tm ctx m a;
    a
  | IMeta (x, _, _) -> (
    match State.find_imeta x with
    | Some a -> a
    | None ->
      let a = imeta_of_ctx ctx in
      State.add_imeta ctx x a;
      a)
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
    let t = resolve_tm (State.export_eqns ()) t in
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
  | Ind (ind, ss, ms, ns) ->
    let sch, _ = Ctx.find_ind ind ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_ind ctx ms ns ptl
  | Constr (constr, ss, ms, ns) ->
    let sch, _ = Ctx.find_constr constr ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_constr ctx ms ns ptl
  | Match (ms, a, cls) ->
    assert_type ctx a;
    check_cls ctx cls a;
    infer_motive ctx ms a
  | Absurd -> failwith "trans1e.inter_tm(Absurd)"
  (* monad *)
  | IO a ->
    assert_type ctx a;
    Type L
  | Return m -> IO (infer_tm ctx m)
  | MLet (m, bnd) -> (
    let t1 = infer_tm ctx m in
    let t1 = resolve_tm (State.export_eqns ()) t1 in
    match whnf ~expand:true ctx t1 with
    | IO a -> (
      let x, n = unbind bnd in
      let t2 = infer_tm (Ctx.add_var0 x a ctx) n in
      let t2 = resolve_tm (State.export_eqns ()) t2 in
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
  match m with
  (* inference *)
  | IMeta (x, _, _) -> State.add_imeta ctx x a
  | _ ->
    let b = infer_tm ctx m in
    assert_equal1 ctx a b

and check_cls ctx cls a : unit =
  let rec is_absurd eqns rhs =
    match (eqns, rhs) with
    | PPrbm.EqualTerm (_, Var _, Absurd, _) :: _, None -> true
    | PPrbm.EqualTerm (_, Var _, Absurd, _) :: _, Some _ ->
      failwith "trans1e.is_absurd"
    | _ :: eqns, _ -> is_absurd eqns rhs
    | [], _ -> false
  in
  let rec get_absurd = function
    | PPrbm.EqualTerm (_, Var _, Absurd, a) :: _ -> a
    | _ :: eqns -> get_absurd eqns
    | [] -> failwith "trans1e.get_absurd"
  in
  let rec can_split = function
    | PPrbm.EqualTerm (_, Var _, Constr _, _) :: _ -> true
    | _ :: eqns -> can_split eqns
    | [] -> false
  in
  let rec first_split = function
    | PPrbm.EqualTerm (_, Var x, Constr _, a) :: _ -> (x, a)
    | _ :: eqns -> first_split eqns
    | [] -> failwith "trans1e.first_split"
  in
  let fail_on_ind global ctx ind ss ms a =
    let rec aux_constrs = function
      | [] -> ()
      | constr :: constrs ->
        let sch, _ = Ctx.find_constr constr ctx in
        let param = msubst sch (Array.of_list ss) in
        let tele = param_inst param ms in
        let t = unbind_tele tele in
        let global = PPrbm.EqualType (ctx, a, t) :: global in
        if has_failed (fun () -> resolve_pprbm global) then
          aux_constrs constrs
        else
          failwith "trans1e.fail_on_ind"
    in
    let _, constrs = Ctx.find_ind ind ctx in
    aux_constrs (Constr.Set.elements constrs)
  in
  let rec aux_prbm ctx (prbm : PPrbm.t) a =
    match prbm.clause with
    | [] -> (
      if not (has_failed (fun () -> resolve_pprbm prbm.global)) then
        let a = resolve_tm (State.export_eqns ()) a in
        match whnf ~expand:true ctx a with
        | Pi (_, _, a, _) -> (
          match whnf ~expand:true ctx a with
          | Ind (ind, ss, ms, ns) -> fail_on_ind prbm.global ctx ind ss ms a
          | _ -> failwith "trans1e.check_cls(Empty)")
        | _ -> failwith "trans1e.check_cls(Empty)")
    | (eqns, ps, rhs) :: _ when is_absurd eqns rhs -> (
      if not (has_failed (fun () -> resolve_pprbm prbm.global)) then
        let a = get_absurd eqns in
        let a = resolve_tm (State.export_eqns ()) a in
        match whnf ~expand:true ctx a with
        | Ind (d, ss, ms, ns) -> _
        | _ -> failwith "trans1e.check_cls(Absurd)")
    | (eqns, ps, rhs) :: _ when can_split es -> _
    | (eqns, ps, rhs) :: clause -> _
  in
  let prbm = PPrbm.of_cls cls in
  aux_prbm ctx prbm a

let rec check_dcls ctx = function
  | Definition { name = x; relv; scheme = sch } :: dcls ->
    let ss, (m, a) = unmbind sch in
    let ctx0 = Array.fold_right Ctx.add_svar ss ctx in
    State.init ();
    assert_type ctx0 a;
    check_tm ctx0 m a;
    let prbm = State.(export_eqns (), export_mctx ()) in
    let prbms =
      let ctx = Ctx.add_const x sch ctx in
      check_dcls ctx dcls
    in
    prbm :: prbms
  | Inductive { name = ind; relv; arity; dconstrs } :: dcls ->
    State.init ();
    check_arity ctx arity;
    let ctx0 = Ctx.add_ind ind (arity, Constr.Set.empty) ctx in
    check_dconstrs ind ctx0 dconstrs;
    let prbm = State.(export_eqns (), export_mctx ()) in
    let prbms =
      let constrs, ctx =
        List.fold_left
          (fun (acc, ctx) (mode, constr, sch) ->
            (Constr.Set.add constr acc, Ctx.add_constr constr (sch, mode) ctx))
          (Constr.Set.empty, ctx) dconstrs
      in
      let ctx = Ctx.add_ind ind (arity, constrs) ctx in
      check_dcls ctx dcls
    in
    prbm :: prbms
  | [] -> []

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
