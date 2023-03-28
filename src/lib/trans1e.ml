open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Unify1
open Pprint1

type ctx =
  { vs : tm VMap.t
  ; ds : (tm param * CSet.t) DMap.t
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
let rec infer_sort ctx env a : sort trans1e =
  let* srt, a' = infer_tm ctx env a in
  let* srt = resolve_tm srt in
  match whnf rd_all env srt with
  | Type s -> return (s, a')
  | _ -> failwith "infert_sort(%a)" pp_tm a

and infer_tm ctx env m0 : (tm * tm) trans1e =
  match m0 with
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
  | Pi (rel, srt, a, bnd) ->
    let x, b = unbind bnd in
    let* _, a' = infer_sort ctx env a in
    let* _, b' = infer_sort (add_v x a' ctx) env b in
    let bnd' = unbox (bind_var x (lift_tm b')) in
    return (Type srt, Pi (rel, srt, a', bnd'))
  | Lam (rel, srt, bnd) -> failwith "infer_tm(%a)" pp_tm m0
  | App (m, n) -> (
    let* a, m' = infer_tm ctx env m in
    let* a = resolve_tm a in
    match whnf rd_all env a with
    | Pi (_, _, a, bnd) ->
      let* n' = check_tm ctx env n a in
      return (subst bnd n', App (m', n'))
    | _ -> failwith "infer_tm(%a)" pp_tm m0)
  | Let (rel, m, bnd) ->
    let* a, m' = infer_tm ctx env m in
    let* _ = unify in
    let* m' = resolve_tm m' in
    let* a = resolve_tm a in
    let x, n = unbind bnd in
    let* b, n' = infer_tm (add_v x a ctx) (VMap.add x m' env) n in
    let bnd' = unbox (bind_var x (lift_tm n')) in
    return (b, Let (rel, m, bnd'))
  | Fix _ -> failwith "infer_tm(%a)" pp_tm m0
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
  | Cons (c, ms, ns) ->
    let ptl = find_c c ctx in
    let* ms', b = infer_ptl ctx env ms ptl in
    return (b, Ann (Cons (c, ms'), b))
  | Match (m, mot, cls) -> (
    let* a, m' = infer_tm ctx env m in
    let* _ = unify in
    let* a = resolve_tm a in
    match whnf rd_all env a with
    | Sigma (rel, srt, a, bnd) ->
      let* cls' = infer_pair ctx env rel srt a bnd mot cls in
      return (subst mot m', Match (m', mot, cls'))
    | Data (d, ms) ->
      let _, cs = find_d d ctx in
      let* cls' = infer_cls ctx env cs ms mot cls in
      return (subst mot m', Match (m', mot, cls'))
    | _ -> failwith "infer_tm(%a)" pp_tm m0)
  (* equality *)
  | Eq (m, n) ->
    let* a, m' = infer_tm ctx env m in
    let* n' = check_tm ctx env n a in
    return (Type U, Eq (m', n'))
  | Refl ->
    let m, _ = meta_mk ctx in
    let n, _ = meta_mk ctx in
    return (Eq (m, n), Ann (Refl, Eq (m, n)))
  | Rew (bnd, p, m) -> (
    let xs, mot = unmbind bnd in
    let* e, p' = infer_tm ctx env p in
    let* _ = unify in
    let* e = resolve_tm e in
    match (e, xs) with
    | Eq (m, n), [| x; y |] ->
      let* a, m' = infer_tm ctx env m in
      let ctx' = add_v x a ctx in
      let ctx' = add_v y (Eq (m', Var x)) ctx' in
      let* _, mot' = infer_sort ctx' env mot in
      let bnd' = unbox (bind_mvar xs (lift_tm mot')) in
      let tm = Ann (Refl, Eq (m, m)) in
      let* m' = check_tm ctx env m (msubst bnd' [| m; tm |]) in
      let ty = msubst bnd' [| n; p' |] in
      return (Rew (bnd', p', m'))
    | _ -> failwith "infer_rew")
  | _ -> _

and infer_pair ctx env rel srt a b mot cls =
  match cls with
  | [ PPair (rel0, srt0, bnd) ] when rel = rel0 && srt = srt0 -> (
    let xs, rhs = unmbind bnd in
    match xs with
    | [| x; y |] ->
      let ctx = add_v x a ctx in
      let ctx = add_v y (subst b (Var x)) ctx in
      let tm = Pair (rel, srt, Var x, Var y) in
      let ty = Sigma (rel, srt, a, b) in
      let mot = subst mot (Ann (tm, ty)) in
      let* _, mot' = infer_sort ctx env mot in
      let* rhs' = check_tm ctx env rhs mot' in
      let bnd' = bind_mvar xs (lift_tm rhs') in
      return [ PPair (rel, srt, unbox bnd') ]
    | _ -> failwith "infer_pair")
  | _ -> failwith "infer_pair"

and infer_cls ctx env cs ms mot cls =
  match cls with
  | [] ->
    if CSet.is_empty cs then
      return []
    else
      failwith "infer_cls(unmatched case)"
  | PCons (c, bnd) :: cls ->
    let* cl' = infer_cl ctx env ms mot c bnd in
    let* cls' = infer_cls ctx env (CSet.remove c cs) ms mot cls in
    return (cl' :: cls')
  | PPair _ :: _ -> failwith "infer_cls"

and infer_cl ctx env ms mot c bnd =
  let rec init_param ms ptl =
    match (ms, ptl) with
    | [], PBase tl -> tl
    | m :: ms, PBind (a, bnd) -> init_param ms (subst bnd (Ann (m, a)))
    | _ -> failwith "init_param"
  in
  let rec init_tele ctx xs tl =
    match (xs, tl) with
    | [], TBase b -> (ctx, b)
    | x :: xs, TBind (_, a, bnd) ->
      let ctx = add_v x a ctx in
      let tl = subst bnd (Var x) in
      init_tele ctx xs tl
    | _ -> failwith "init_tele"
  in
  let xs0, rhs = unmbind bnd in
  let xs = Array.to_list xs0 in
  let ptl = find_c c ctx in
  let tl = init_param ms ptl in
  let ctx, ty = init_tele ctx xs tl in
  let tm = Cons (c, List.map (fun x -> Var x) xs) in
  let mot = subst mot (Ann (tm, ty)) in
  let* _, mot' = infer_sort ctx env mot in
  let* rhs' = check_tm ctx env rhs mot' in
  let bnd' = bind_mvar xs0 (lift_tm rhs') in
  return (PCons (c, unbox bnd'))

and infer_ptm ctx env ms ptm =
  match (ms, ptm) with
  | [], PBase b ->
    let* _, b' = infer_sort ctx env b in
    return ([], b')
  | m :: ms, PBind (a, bnd) ->
    let* m' = check_tm ctx env m a in
    let* ms', b' = infer_ptm ctx env ms (subst bnd m') in
    return (m' :: ms', b')
  | _ -> failwith "infer_ptm(%a)" pp_ptm ptm

and infer_ptl ctx env ms ptl =
  match ptl with
  | PBase tl -> infer_tele ctx env ms tl
  | PBind (a, bnd) ->
    let m, _ = meta_mk ctx in
    infer_ptl ctx env ms (subst bnd (Ann (m, a)))

and infer_tele ctx env ms tl =
  match (ms, tl) with
  | [], TBase b ->
    let* _, b' = infer_sort ctx env b in
    return ([], b')
  | m :: ms, TBind (_, a, bnd) ->
    let* m' = check_tm ctx env m a in
    let* ms', b' = infer_tele ctx env ms (subst bnd m') in
    return (m' :: ms', b')
  | _ -> failwith "infer_tele(%a)" pp_tele tl

and check_tm ctx env m a : tm trans1e =
  match m with
  | _ -> _
