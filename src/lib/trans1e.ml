open Bindlib
open Names
open Syntax1
open Equality1
open Context1
open Constraint1

module State : sig
  val add_prbm : IPrbm.prbm -> unit
  val add_imeta : IMeta.t -> tm -> unit
  val find_imeta : IMeta.t -> tm option
  val init : unit -> unit
  val export : unit -> IPrbm.t
end = struct
  type t =
    { mutable prbm : IPrbm.t
    ; mutable mctx : MCtx.t
    }

  let state : t = { prbm = []; mctx = MCtx.empty }
  let add_prbm prbm = state.prbm <- prbm :: state.prbm
  let add_imeta x a = state.mctx <- MCtx.add_imeta x a state.mctx
  let find_imeta x = MCtx.find_imeta x state.mctx

  let init () =
    state.prbm <- [];
    state.mctx <- MCtx.empty

  let export () = state.prbm
end

let smeta_of_ctx (ctx : Ctx.t) =
  let x = SMeta.mk "" in
  let ss = ctx.svar |> SVar.Set.elements |> List.map (fun x -> SVar x) in
  SMeta (x, ss)

let imeta_of_ctx (ctx : Ctx.t) =
  let x = IMeta.mk "" in
  let ss = ctx.svar |> SVar.Set.elements |> List.map (fun x -> SVar x) in
  let xs = ctx.var |> Var.Map.bindings |> List.map (fun x -> Var (fst x)) in
  IMeta (x, ss, xs)

let assert_equal0 s1 s2 =
  if not (eq_sort s1 s2) then State.add_prbm (EqSort (s1, s2))

let assert_equal1 env m1 m2 =
  if not (eq_tm env m1 m2) then State.add_prbm (EqTm (env, m1, m2))

let rec assert_type ctx env a =
  let t = infer_tm ctx env a in
  match whnf ~expand:true env t with
  | Type _ -> ()
  | _ -> State.add_prbm (AssertType (env, a))

and infer_tm ctx env m =
  match m with
  (* inference *)
  | Ann (m, a) ->
    assert_type ctx env a;
    check_tm ctx env m a;
    a
  | IMeta (x, _, _) -> (
    match State.find_imeta x with
    | Some a -> a
    | None ->
      let a = imeta_of_ctx ctx in
      State.add_imeta x a;
      State.add_prbm (Check (ctx, env, m, a));
      a)
  (* core *)
  | Type _ -> Type U
  | Var x -> Ctx.find_var x ctx
  | Const (x, ss) ->
    let sch = Ctx.find_const x ctx in
    let _, a = msubst sch (Array.of_list ss) in
    a
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
    match whnf ~expand:true env t with
    | Pi (_, _, a, bnd) ->
      check_tm ctx env n a;
      subst bnd n
    | _ ->
      let s = smeta_of_ctx ctx in
      let b = imeta_of_ctx ctx in
      State.add_prbm (Check (ctx, env, b, Type s));
      State.add_prbm (Check (ctx, env, App (m, n), b));
      b)
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let a = infer_tm ctx env m in
    infer_tm (Ctx.add_var x a ctx) (Env.add_var x m env) n
  (* inductive *)
  | Ind (ind, ss, ms, ns) ->
    let sch, _ = Ctx.find_ind ind ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_ind ctx env ms ns ptl
  | Constr (constr, ss, ms, ns) ->
    let _, sch = Ctx.find_constr constr ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_constr ctx env ms ns ptl
  | Match (ms, a, cls) ->
    assert_type ctx env a;
    check_cls ctx env cls a;
    infer_motive ctx env ms a
  (* monad *)
  | IO a ->
    assert_type ctx env a;
    Type L
  | Return m ->
    let a = infer_tm ctx env m in
    IO a
  | MLet (m, bnd) -> (
    let t1 = infer_tm ctx env m in
    match whnf ~expand:true env t1 with
    | IO a -> (
      let x, n = unbind bnd in
      let t2 = infer_tm (Ctx.add_var x a ctx) env n in
      match whnf ~expand:true env t2 with
      | IO b -> IO b
      | _ ->
        let s = smeta_of_ctx ctx in
        let b = imeta_of_ctx ctx in
        State.add_prbm (Check (ctx, env, b, Type s));
        assert_equal1 env t2 (IO b);
        IO b)
    | _ ->
      let s = smeta_of_ctx ctx in
      let b = imeta_of_ctx ctx in
      State.add_prbm (Check (ctx, env, b, Type s));
      State.add_prbm (Check (ctx, env, MLet (m, bnd), IO b));
      IO b)
  | Magic a -> a

and infer_ind ctx env ms ns ptl =
  let rec aux_param ms ptl =
    match (ms, ptl) with
    | [], PBase tl -> aux_tele ns tl
    | m :: ms, PBind (a, bnd) ->
      check_tm ctx env m a;
      aux_param ms (subst bnd m)
    | _ -> failwith "trans1e.infer_ind(param)"
  and aux_tele ns tl =
    match (ns, tl) with
    | [], TBase a -> a
    | n :: ns, TBind (_, a, bnd) ->
      check_tm ctx env n a;
      aux_tele ns (subst bnd n)
    | _ -> failwith "trans1e.infer_ind(tele)"
  in
  aux_param ms ptl

and infer_constr ctx env ms ns ptl =
  let rec aux_param ms ptl =
    match (ms, ptl) with
    | [], PBase tl -> aux_tele ns tl
    | m :: ms, PBind (a, bnd) ->
      check_tm ctx env m a;
      aux_param ms (subst bnd m)
    | _ -> failwith "trans1e.infer_constr(param)"
  and aux_tele ns tl =
    match (ns, tl) with
    | [], TBase a -> a
    | n :: ns, TBind (_, a, bnd) ->
      check_tm ctx env n a;
      aux_tele ns (subst bnd n)
    | _ -> failwith "trans1e.infer_constr(tele)"
  in
  aux_param ms ptl

and infer_motive ctx env ms a =
  match (ms, whnf ~expand:true env a) with
  | [], a -> a
  | m :: ms, Pi (_, _, a, bnd) ->
    check_tm ctx env m a;
    infer_motive ctx env ms (subst bnd m)
  | _ -> failwith "trans1e.infer_motive"

and check_tm ctx env m a =
  match m with
  (* inference *)
  | IMeta (x, _, _) ->
    State.add_imeta x a;
    State.add_prbm (Check (ctx, env, m, a))
  | _ ->
    let b = infer_tm ctx env m in
    assert_equal1 env a b

and check_cls ctx env cls a = ()

let rec check_dcls ctx env = function
  | Definition { name = x; relv; scheme = sch } :: dcls ->
    let ss, (m, a) = unmbind sch in
    let ctx0 = Array.fold_right Ctx.add_svar ss ctx in
    State.init ();
    assert_type ctx0 env a;
    check_tm ctx0 env m a;
    let prbm = State.export () in
    let prbms =
      let ctx = Ctx.add_const x sch ctx in
      let env = Env.add_const x sch env in
      check_dcls ctx env dcls
    in
    prbm :: prbms
  | Inductive { name = ind; relv; arity; dconstrs } :: dcls ->
    State.init ();
    check_arity ctx env arity;
    let ctx0 = Ctx.add_ind ind (arity, Constr.Set.empty) ctx in
    check_dconstrs ind ctx0 env dconstrs;
    let prbm = State.export () in
    let prbms =
      let constrs, ctx =
        List.fold_left
          (fun (acc, ctx) (mode, constr, sch) ->
            (Constr.Set.add constr acc, Ctx.add_constr constr (mode, sch) ctx))
          (Constr.Set.empty, ctx) dconstrs
      in
      let ctx = Ctx.add_ind ind (arity, constrs) ctx in
      check_dcls ctx env dcls
    in
    prbm :: prbms
  | [] -> []

and check_arity ctx env arity =
  let rec aux_param ctx env = function
    | PBase tele -> aux_tele ctx env tele
    | PBind (a, bnd) ->
      let x, b = unbind bnd in
      assert_type ctx env a;
      aux_param (Ctx.add_var x a ctx) env b
  and aux_tele ctx env = function
    | TBase (Type s) -> ()
    | TBind (R, a, bnd) ->
      let x, b = unbind bnd in
      assert_type ctx env a;
      aux_tele ctx env b
    | _ -> failwith "trans1e.check_arity(aux_tele)"
  in
  let ss, param = unmbind arity in
  let ctx = Array.fold_right Ctx.add_svar ss ctx in
  aux_param ctx env param

and check_dconstrs ind ctx env dconstrs =
  let check_dconstr ind ctx env dconstr =
    let rec aux_param sids args ctx env = function
      | PBase tele -> aux_tele sids (List.rev args) ctx env tele
      | PBind (a, bnd) ->
        let x, b = unbind bnd in
        assert_type ctx env a;
        aux_param sids (x :: args) (Ctx.add_var x a ctx) env b
    and aux_tele sids xs ctx env = function
      | TBase (Ind (x, ss, ms, ns) as a) ->
        List.iter2 (fun sid s -> assert_equal0 (SVar sid) s) sids ss;
        List.iter2 (fun x m -> assert_equal1 env (Var x) m) xs ms;
        assert_type ctx env a
      | TBind (_, a, bnd) ->
        let x, b = unbind bnd in
        assert_type ctx env a;
        aux_tele sids xs (Ctx.add_var x a ctx) env b
      | _ -> failwith "trans1e.check_dconstr(aux_tele)"
    in
    let _, _, sch = dconstr in
    let sids, param = unmbind sch in
    aux_param (Array.to_list sids) [] ctx env param
  in
  List.iter (check_dconstr ind ctx env) dconstrs
