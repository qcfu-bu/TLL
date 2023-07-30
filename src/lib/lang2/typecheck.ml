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

let map_array (f : 'a -> 'b tc) (ms : 'a array) : 'b array tc =
 fun (ctx, env, mctx) ->
  let (mctx, eqns), ns =
    Array.fold_left_map
      (fun (mctx, eqns0) m ->
        let n, mctx, eqns1 = f m (ctx, env, mctx) in
        ((mctx, eqns0 @ eqns1), n))
      (mctx, []) ms
  in
  (ns, mctx, eqns)

let fold_array (f : 'a -> 'b -> 'a tc) (acc : 'a) (ms : 'b array) : 'a tc =
 fun (ctx, env, mctx) ->
  let mctx, eqns, acc =
    Array.fold_left
      (fun (mctx, eqns0, acc) m ->
        let acc, mctx, eqns1 = f acc m (ctx, env, mctx) in
        (mctx, eqns0 @ eqns1, acc))
      (mctx, [], acc) ms
  in
  (acc, mctx, eqns)

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

let whnf m : tm tc = fun (ctx, env, mctx) -> (whnf env m, mctx, [])

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

let assert_search m a : unit tc =
 fun (ctx, env, mctx) -> ((), mctx, [ Search (ctx, env, m, a) ])

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
  | Fun (a, bnd) ->
    let x, cls = unbind bnd in
    let* _ = assert_type a in
    let* _ = add_var x a (check_cls cls a) in
    return a
  | App (m, n) -> (
    let* ty_m1 = infer_tm m in
    let* ty_m1 = whnf ty_m1 in
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
  | Struct (a, fields) ->
    let* _ = assert_type a in
    let* _ = check_tm (Struct (a, fields)) a in
    return a
  | Proj (field, m) -> (
    let* ty_m = infer_tm m in
    let* ty_m = whnf ty_m in
    match unApps ty_m with
    | Record (record, ss), ms -> infer_proj record ss ms field m
    | _ ->
      let* b = imeta_mk in
      let* _ = assert_check (Proj (field, m)) b in
      return b)
  (* magic *)
  | Magic -> imeta_mk

and infer_proj record ss ms x m =
  let rec fdef_proj fdef =
    match fdef with
    | Empty -> failwith "infer_proj"
    | Field (y, _, a, bnd) when Field.equal x y -> return a
    | Field (y, _, a, bnd) -> fdef_proj (subst bnd (Proj (y, m)))
  in
  let* sch = find_record record in
  let _, bnd = msubst sch ss in
  let fdef = msubst bnd ms in
  fdef_proj fdef

and check_tm m a : unit tc =
  let* a = whnf a in
  match m with
  (* inference *)
  | IMeta (x, _, _) ->
    let* _ = add_imeta x a in
    let* _ = assert_check m a in
    return ()
  | TMeta (x, _, _) ->
    let* _ = add_tmeta x a in
    let* _ = assert_search m a in
    return ()
  (* record *)
  | Struct (b, fields) -> (
    let* _ = assert_equal1 a b in
    match unApps a with
    | Record (record, ss), ms ->
      let* sch = find_record record in
      let _, bnd = msubst sch ss in
      let fdef = msubst bnd ms in
      check_fields fields fdef
    | _ -> assert_check m a)
  (* other *)
  | _ ->
    let* ty_m = infer_tm m in
    let* _ = assert_equal1 ty_m a in
    return ()

and check_fields fields fdef =
  let* fdef =
    fold_array
      (fun fdef (x1, relv1, m) ->
        match fdef with
        | Field (x2, relv2, a, bnd) when Field.equal x1 x2 && relv1 = relv2 ->
          let* _ = check_tm m a in
          return (subst bnd m)
        | _ -> failwith "check_fields")
      fdef fields
  in
  match fdef with
  | Empty -> return ()
  | _ -> failwith "check_fields"

and check_cls cls a = failwith "unimplemented"
