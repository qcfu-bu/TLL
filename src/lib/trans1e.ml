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

let rec assert_type ctx env a =
  let s = smeta_of_ctx ctx in
  check_tm ctx env a (Type s)

and infer_tm ctx env m =
  match m with
  (* inference *)
  | Ann (m, a) ->
    let _ = assert_type ctx env a in
    let _ = check_tm ctx env m a in
    a
  | IMeta (x, _, _) -> (
    match State.find_imeta x with
    | Some a -> a
    | None ->
      let a = imeta_of_ctx ctx in
      let _ = State.add_imeta x a in
      let _ = State.add_prbm (Check (ctx, env, m, a)) in
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
    let _ = assert_type ctx env a in
    let _ = assert_type (Ctx.add_var x a ctx) env b in
    Type s
  | Fun (a, bnd) ->
    let x, cls = unbind bnd in
    let _ = assert_type ctx env a in
    let _ = check_cls (Ctx.add_var x a ctx) env cls a in
    a
  | App (m, n) -> (
    let t = infer_tm ctx env m in
    match whnf ~expand:true env t with
    | Pi (_, _, a, bnd) ->
      let _ = check_tm ctx env n a in
      subst bnd n
    | _ ->
      let s = smeta_of_ctx ctx in
      let b = imeta_of_ctx ctx in
      let _ = State.add_prbm (Check (ctx, env, b, Type s)) in
      let _ = State.add_prbm (Check (ctx, env, App (m, n), b)) in
      b)
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let a = infer_tm ctx env m in
    infer_tm (Ctx.add_var x a ctx) (Env.add_var x m env) n
  (* inductive *)
  | Ind (ind, ss, ms, ns) ->
    let sch = Ctx.find_ind ind ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_ind ctx env ms ns ptl
  | Constr (constr, ss, ms, ns) ->
    let sch = Ctx.find_constr constr ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_constr ctx env ms ns ptl
  | Match (ms, a, cls) ->
    let _ = assert_type ctx env a in
    let _ = check_cls ctx env cls a in
    infer_motive ctx env ms a
  (* monad *)
  | IO a ->
    let _ = assert_type ctx env a in
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
        let _ = State.add_prbm (Check (ctx, env, b, Type s)) in
        let _ = State.add_prbm (EqTm (env, t2, IO b)) in
        IO b)
    | _ ->
      let s = smeta_of_ctx ctx in
      let b = imeta_of_ctx ctx in
      let _ = State.add_prbm (Check (ctx, env, b, Type s)) in
      let _ = State.add_prbm (Check (ctx, env, MLet (m, bnd), IO b)) in
      IO b)
  | Magic a -> a

and infer_ind ctx env ms ns ptl =
  let rec aux_param ms ptl =
    match (ms, ptl) with
    | [], PBase (tl, _) -> aux_tele ns tl
    | m :: ms, PBind (a, bnd) ->
      let _ = check_tm ctx env m a in
      aux_param ms (subst bnd m)
    | _ -> failwith "trans1e.infer_ind(param)"
  and aux_tele ns tl =
    match (ns, tl) with
    | [], TBase a -> a
    | n :: ns, TBind (_, a, bnd) ->
      let _ = check_tm ctx env n a in
      aux_tele ns (subst bnd n)
    | _ -> failwith "trans1e.infer_ind(tele)"
  in
  aux_param ms ptl

and infer_constr ctx env ms ns ptl =
  let rec aux_param ms ptl =
    match (ms, ptl) with
    | [], PBase tl -> aux_tele ns tl
    | m :: ms, PBind (a, bnd) ->
      let _ = check_tm ctx env m a in
      aux_param ms (subst bnd m)
    | _ -> failwith "trans1e.infer_constr(param)"
  and aux_tele ns tl =
    match (ns, tl) with
    | [], TBase a -> a
    | n :: ns, TBind (_, a, bnd) ->
      let _ = check_tm ctx env n a in
      aux_tele ns (subst bnd n)
    | _ -> failwith "trans1e.infer_constr(tele)"
  in
  aux_param ms ptl

and infer_motive ctx env ms a =
  match (ms, whnf ~expand:true env a) with
  | [], a -> a
  | m :: ms, Pi (_, _, a, bnd) ->
    let _ = check_tm ctx env m a in
    infer_motive ctx env ms (subst bnd m)
  | _ -> failwith "trans1e.infer_motive"

and check_tm ctx env m a =
  match m with
  (* inference *)
  | IMeta (x, _, _) ->
    let _ = State.add_imeta x a in
    let _ = State.add_prbm (Check (ctx, env, m, a)) in
    ()
  | _ ->
    let b = infer_tm ctx env m in
    let _ = State.add_prbm (EqTm (env, a, b)) in
    ()

and check_cls ctx env cls a = ()

let rec check_dcls ctx env = function
  | Definition { name = x; relv; scheme = sch } :: dcls ->
    let ss, (m, a) = unmbind sch in
    let ctx0 = Array.fold_right Ctx.add_svar ss ctx in
    let _ = State.init () in
    let _ = assert_type ctx0 env a in
    let _ = check_tm ctx0 env m a in
    let prbm = State.export () in
    let prbms =
      let ctx = Ctx.add_const x sch ctx in
      let env = Env.add_const x sch env in
      check_dcls ctx env dcls
    in
    prbm :: prbms
  | Inductive { name = ind; relv; arity; dconstrs } :: dcls ->
    check_dcls ctx env dcls
    (* let ss, inddef = unmbind sch in *)
    (* let ctx0 = Array.fold_right Ctx.add_svar ss ctx in *)
    (* let _ = State.init () in *)
    (* let _ = check_inddef ctx0 env ind inddef in *)
    (* let prbm = State.export () in *)
    (* let prbms = *)
    (*   let ctx = Ctx.add_ind ind sch ctx in *)
    (*   let ctx = *)
    (*     List.fold_right *)
    (*       (fun (constr, sch) ctx -> Ctx.add_constr constr sch ctx) *)
    (*       dconstrs ctx *)
    (*   in *)
    (*   check_dcls ctx env dcls *)
    (* in *)
    (* prbm :: prbms *)
  | [] -> []

(* ; ind : (tele * dconstrs) param scheme Ind.Map.t *)
(* ; constr : tele param scheme Constr.Map.t *)
