open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Unify1
open Pprint1

type ctx =
  { vs : tm VMap.t
  ; ds : (tm param * C.t list) DMap.t
  ; cs : tele param CMap.t
  }

let add_v x a ctx = { ctx with vs = VMap.add x a ctx.vs }
let add_d d ptm cs ctx = { ctx with ds = DMap.add d (ptm, cs) ctx.ds }
let add_c c ptl ctx = { ctx with cs = CMap.add c ptl ctx.cs }

let find_v x ctx =
  match VMap.find_opt x ctx.vs with
  | Some a -> a
  | None -> failwith "find_v(%a)" V.pp x

let find_d d ctx =
  match DMap.find_opt d ctx.ds with
  | Some res -> res
  | None -> failwith "find_d(%a)" D.pp d

let find_c c ctx =
  match CMap.find_opt c ctx.cs with
  | Some ptl -> ptl
  | None -> failwith "find_c(%a)" C.pp c

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.vs |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, xs), x)

type 'a trans1e = eqns * map -> 'a * eqns * map

let return (a : 'a) : 'a trans1e = fun (eqns, map) -> (a, eqns, map)

let find_m x ctx : tm trans1e =
 fun (eqns, map) ->
  match MMap.find_opt x map with
  | Some (_, Some a) -> (a, eqns, map)
  | _ -> (fst (meta_mk ctx), eqns, map)

let ( >>= ) (m : 'a trans1e) (f : 'a -> 'b trans1e) : 'b trans1e =
 fun (eqns, map) ->
  let a, eqns', map' = m (eqns, map) in
  (f a) (eqns', map')

let ( let* ) = ( >>= )

let assert_equal env m n : unit trans1e =
 fun (eqns, map) ->
  if equal [| Beta; Delta; Zeta; Iota |] env m n then
    ((), eqns, map)
  else
    ((), (env, m, n) :: eqns, map)

let resolve_tm m : tm trans1e =
 fun (eqns, map) ->
  let m = resolve_tm map m in
  (m, eqns, map)

let unify : unit trans1e =
 fun (eqns, map) ->
  let map = unify map eqns in
  ((), eqns, map)

(* infer the type + sort of a term *)
let rec infer_sort ctx env a : (sort * tm) trans1e =
  let* srt, a' = infer_tm ctx env a in
  let* srt = resolve_tm srt in
  match whnf rd_all env srt with
  | Type s -> return (s, a')
  | _ -> failwith "infert_sort(%a)" pp_tm a

and infer_tm ctx env m : (tm * tm) trans1e =
  match m with
  (* inference *)
  | Ann (m, a) ->
    let* _ = infer_sort ctx env a in
    let* _ = check_tm ctx env m a in
    return (a, Ann (m, a))
  | Meta (x, ms) ->
    let* a = find_m x ctx in
    return (a, Meta (x, ms))
  (* core *)
  | Type srt -> return (Type U, Type srt)
  | Var x -> return (find_v x ctx, Var x)
  | Pi (res, srt, a, bnd) ->
    let x, b = unbind bnd in
    let* _, a' = infer_sort ctx env a in
    let* _, b' = infer_sort (add_v x a' ctx) env b in
    let bnd' = unbox (bind_var x (lift_tm b')) in
    return (Type srt, Pi (res, srt, a', bnd'))
  | Lam _ -> failwith "infer_tm(%a)" pp_tm m
  | App (m, n) -> (
    let* a, m' = infer_tm ctx env m in
    let* a = resolve_tm a in
    match whnf rd_all env a with
    | Pi (_, _, a, bnd) ->
      let* n' = check_tm ctx env n a in
      return (subst bnd n', App (m', n'))
    | _ -> failwith "infer_tm(%a)" pp_tm m)
  | Let (rel, m, bnd) ->
    let* a, m' = infer_tm ctx env m in
    let* _ = unify in
    let* m' = resolve_tm m' in
    let* a = resolve_tm a in
    let x, n = unbind bnd in
    let* b, n' = infer_tm (add_v x a ctx) (VMap.add x m' env) n in
    let bnd' = unbox (bind_var x (lift_tm n')) in
    return (b, Let (rel, m, bnd'))
  | Fix _ -> failwith "infer_tm(%a)" pp_tm m
  (* data *)
  | Sigma (rel, srt, a, bnd) ->
    let x, b = unbind bnd in
    let* _, a' = infer_sort ctx env a in
    let* _, b' = infer_sort (add_v x a' ctx) env b in
    let bnd' = unbox (bind_var x (lift_tm b')) in
    return (Type srt, Sigma (rel, srt, a', bnd'))
  | Pair (rel, srt, m, n) ->
    let* a, m' = infer_tm ctx env m in
    let* b, n' = infer_tm ctx env n in
    let x = mk "_" in
    let bnd = unbox (bind_var x (lift_tm b)) in
    return (Sigma (rel, srt, a, bnd), Pair (rel, srt, m', n'))
  | Data (d, ms) ->
    let ptm, _ = find_d d ctx in
    let* ms', b = infer_ptm ctx env ms ptm in
    return (b, Data (d, ms'))
  | Cons (c, ms) ->
    let ptl = find_c c ctx in
    let* ms', b = infer_ptl ctx env ms ptl in
    return (b, Ann (Cons (c, ms'), b))
  | Match (m, bnd, cls) -> (
    let a, m' = infer_tm ctx env m in
    let* _ = unify in
    let* a = resolve_tm a in
    match whnf rd_all env a with
    | Data (d, ms) ->
      let _, cs = find_d d ctx in
      _
    | _ -> failwith "infer_tm(%a)" pp_tm m)
  | _ -> _

and infer_ptm ctx env ms ptm =
  match (ms, ptm) with
  | [], PBase b ->
    let* _, b' = infer_sort ctx env b in
    return ([], b')
  | m :: ms, PBind (a, bnd) ->
    let* m' = check_tm ctx env m a in
    let* ms', b' = infer_ptm ctx env ms (subst bnd (Ann (m', a))) in
    return (m' :: ms', b')

and infer_ptl ctx env ms ptl =
  match ptl with
  | PBase tl -> infer_tele ctx env ms tl
  | PBind (a, bnd) ->
    let m, _ = meta_mk ctx in
    infer_ptl ctx env ms (subst bnd (Ann (m, a)))

and infer_tele ctx env ms tl =
  match (ms, tl) with
  | [], TBase a ->
    let* _ = infer_sort ctx env a in
    return a
  | m :: ms, TBind (_, a, bnd) ->
    let* _ = check_tm ctx env m a in
    infer_tele ctx env ms (subst bnd (Ann (m, a)))

and check_tm ctx env m a : tm trans1e =
  match m with
  | _ -> _
