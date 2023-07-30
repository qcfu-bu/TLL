open Bindlib
open Names
open Syntax
open Util
open Context
open Environment
open Equality
open Constraint

type 'a tc = Ctx.t * Env.t * MCtx.t -> 'a * MCtx.t * IConstraint.t

let return (a : 'a) : 'a tc = fun (_, _, mctx) -> (a, mctx, [])

let ( >>= ) (m : 'a tc) (f : 'a -> 'b tc) : 'b tc =
 fun (ctx, env, mctx) ->
  let a, mctx, eqns0 = m (ctx, env, mctx) in
  let b, mctx, eqns1 = f a (ctx, env, mctx) in
  (b, mctx, eqns0 @ eqns1)

let ( >> ) (m : 'a tc) (n : 'b tc) : 'b tc =
 fun (ctx, env, mctx) ->
  let _, mctx, eqns0 = m (ctx, env, mctx) in
  let b, mctx, eqns1 = n (ctx, env, mctx) in
  (b, mctx, eqns0 @ eqns1)

let ( let* ) = ( >>= )

let smeta_mk : sort tc =
 fun (ctx, env, mctx) ->
  let x = SMeta.mk "" in
  let ss = ctx.svar |> SVar.Set.elements |> List.map (fun x -> SVar x) in
  (SMeta (x, Array.of_list ss), mctx, [])

let imeta_mk : tm tc =
 fun (ctx, env, mctx) ->
  let x = IMeta.mk "" in
  let ss = ctx.svar |> SVar.Set.elements |> List.map (fun x -> SVar x) in
  let xs = ctx.var |> Var.Map.bindings |> List.map (fun x -> Var (fst x)) in
  Array.(IMeta (x, of_list ss, of_list xs), mctx, [])

let add_var x a (m : 'a tc) : 'a tc =
 fun (ctx, env, mctx) -> m (Ctx.add_var x a ctx, env, mctx)

let add_svar x (m : 'a tc) : 'a tc =
 fun (ctx, env, mctx) -> m (Ctx.add_svar x ctx, env, mctx)

let add_imeta x a : unit tc =
 fun (_, _, mctx) -> ((), MCtx.add_imeta x a mctx, [])

let add_tmeta x a : unit tc =
 fun (_, _, mctx) -> ((), MCtx.add_tmeta x a mctx, [])

let find_var x : tm tc = fun (ctx, env, mctx) -> (Ctx.find_var x ctx, mctx, [])

let find_const x : tm scheme tc =
 fun (ctx, env, mctx) -> (Ctx.find_const x ctx, mctx, [])

let find_ind x : (tm scheme * 'a) tc =
 fun (ctx, env, mctx) -> (Ctx.find_ind x ctx, mctx, [])

let find_constr x : tm scheme tc =
 fun (ctx, env, mctx) -> (Ctx.find_constr x ctx, mctx, [])

let find_record x : 'a tc =
 fun (ctx, env, mctx) -> (Ctx.find_record x ctx, mctx, [])

let find_imeta x m : tm tc =
 fun (ctx, env, mctx) ->
  match MCtx.find_imeta x mctx with
  | Some a -> (a, mctx, [])
  | _ ->
    let y = IMeta.mk "" in
    let ss = ctx.svar |> SVar.Set.elements |> List.map (fun x -> SVar x) in
    let xs = ctx.var |> Var.Map.bindings |> List.map (fun x -> Var (fst x)) in
    let a = Array.(IMeta (y, of_list ss, of_list xs)) in
    (a, MCtx.add_imeta x a mctx, [ Check (ctx, env, m, a) ])

let find_tmeta x m : tm tc =
 fun (ctx, env, mctx) ->
  match MCtx.find_tmeta x mctx with
  | Some a -> (a, mctx, [])
  | _ ->
    let y = IMeta.mk "" in
    let ss = ctx.svar |> SVar.Set.elements |> List.map (fun x -> SVar x) in
    let xs = ctx.var |> Var.Map.bindings |> List.map (fun x -> Var (fst x)) in
    let a = Array.(IMeta (y, of_list ss, of_list xs)) in
    (a, MCtx.add_tmeta x a mctx, [ Search (ctx, env, m, a) ])

let assert_equal0 s1 s2 : unit tc =
 fun (_, _, mctx) ->
  if eq_sort s1 s2 then
    ((), mctx, [])
  else
    ((), mctx, [ EqSort (s1, s2) ])

let assert_equal1 m n : unit tc =
 fun (ctx, env, mctx) ->
  if eq_tm env m n then
    ((), mctx, [])
  else
    ((), mctx, [ EqTm (env, m, n) ])

let assert_check m a : unit tc =
 fun (ctx, env, mctx) -> ((), mctx, [ Check (ctx, env, m, a) ])

let rec assert_type a : unit tc =
  let* s = smeta_mk in
  check_tm a (Type s)

and infer_tm m : tm tc =
  match m with
  (* inference *)
  | Ann (m, a) ->
    let* _ = assert_type a in
    let* _ = check_tm m a in
    return a
  | IMeta (x, _, _) -> find_imeta x m
  | TMeta (x, _, _) -> find_tmeta x m
  | PMeta x -> failwith "unimplemented"
  (* core *)
  | Type _ -> return (Type U)
  | Var x -> find_var x
  | Const (x, ss) ->
    let* sch = find_const x in
    return (msubst sch ss)
  | Pi (_, s, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = assert_type a in
    let* _ = add_var x a (assert_type b) in
    return (Type s)
  | Lam (rel, s, a, bnd) ->
    let x, m = unbind bnd in
    let* _ = assert_type a in
    let* b = add_var x a (infer_tm m) in
    let bnd = bind_var x (lift_tm b) in
    return (Pi (rel, s, a, unbox bnd))
  | Fix (_, a, bnd) ->
    let x, m = unbind bnd in
    let* _ = assert_type a in
    let* _ = add_var x a (check_tm m a) in
    return a
  | App (m, n) -> (
    let* ty_m1 = infer_tm m in
    match ty_m1 with
    | Pi (_, _, a, bnd) ->
      let* _ = check_tm n a in
      return (subst bnd n)
    | _ ->
      let* b = imeta_mk in
      let* _ = assert_check (App (m, n)) b in
      return b)
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let* a = infer_tm m in
    let* b = add_var x a (infer_tm n) in
    return b
  (* inductive *)
  | Ind (ind, ss) ->
    let* sch, _ = find_ind ind in
    let a = msubst sch ss in
    return a
  | Constr (constr, ss) ->
    let* sch = find_constr constr in
    let a = msubst sch ss in
    return a
  | Match (ms, a, cls) -> failwith "unimplemented"
  | Absurd -> return Absurd
  (* record *)
  | Record (record, ss) ->
    let* sch = find_record record in
    let a, _ = msubst sch ss in
    return a
  | Struct (s, fields) -> infer_struct s fields
  | Proj (field, m) -> infer_proj field m
  (* magic *)
  | Magic -> imeta_mk

and infer_struct s fields = failwith "unimplemented"
and infer_proj field m = failwith "unimplemented"

and check_tm m a : unit tc =
  match (m, a) with
  (* inference *)
  | IMeta (x, _, _), _ ->
    let* _ = add_imeta x a in
    let* _ = assert_check m a in
    return ()
  (* core *)
  | Lam (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) when rel1 = rel2 ->
    let x, m, b = unbind2 bnd1 bnd2 in
    let* _ = assert_type a1 in
    let* _ = assert_equal0 s1 s2 in
    let* _ = assert_equal1 a1 a2 in
    let* _ = add_var x a1 (check_tm m a) in
    return ()
  (* *)
  | _ ->
    let* ty_m = infer_tm m in
    let* _ = assert_equal1 ty_m a in
    return ()
