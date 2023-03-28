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

let ( >> ) (m : 'a trans1e) (n : 'b trans1e) : 'b trans1e =
 fun (eqns, map) ->
  let _, eqns', map' = m (eqns, map) in
  n (eqns', map')

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
  let* srt = infer_tm ctx env a in
  let* srt = resolve_tm srt in
  match whnf rd_all env srt with
  | Type s -> return s
  | _ -> failwith "infert_sort(%a)" pp_tm a

and infer_tm ctx env m0 : tm trans1e =
  match m0 with
  (* inference *)
  | Ann (m, a) ->
    let* _ = infer_sort ctx env a in
    let* _ = check_tm ctx env m a in
    return a
  | Meta (x, ms) -> find_m x ctx
  (* core *)
  | Type srt -> return (Type U)
  | Var x -> return (find_v x ctx)
  | Pi (rel, srt, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* _ = infer_sort (add_v x a ctx) env b in
    return (Type srt)
  | Lam (rel, srt, bnd) -> failwith "infer_tm(%a)" pp_tm m0
  | App (m, n) -> (
    let* ty = infer_tm ctx env m in
    let* ty = resolve_tm ty in
    match whnf rd_all env ty with
    | Pi (_, _, a, bnd) ->
      let* _ = check_tm ctx env n a in
      return (subst bnd n)
    | _ -> failwith "infer_tm(%a)" pp_tm m0)
  | Let (rel, m, bnd) ->
    let* a = infer_tm ctx env m in
    let* m = unify >> resolve_tm m in
    let* a = resolve_tm a in
    let x, n = unbind bnd in
    infer_tm (add_v x a ctx) (VMap.add x m env) n
  | Fix _ -> failwith "infer_tm(%a)" pp_tm m0
  (* data *)
  | Sigma (R, srt, a, bnd) ->
    let x, b = unbind bnd in
    let* s = infer_sort ctx env a in
    let* r = infer_sort (add_v x a ctx) env b in
    if s <= srt && r <= srt then
      return (Type srt)
    else
      failwith "infer_Sigma"
  | Sigma (N, srt, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* r = infer_sort (add_v x a ctx) env b in
    if r <= srt then
      return (Type srt)
    else
      failwith "infer_Sigma"
  | Pair (rel, srt, m, n) ->
    let* a = infer_tm ctx env m in
    let* b = infer_tm ctx env n in
    let x = mk "_" in
    let bnd = unbox (bind_var x (lift_tm b)) in
    let ty = Sigma (rel, srt, a, bnd) in
    infer_sort ctx env ty >> return ty
  | Data (d, ms) ->
    let ptm, _ = find_d d ctx in
    infer_ptm ctx env ms ptm
  | Cons (c, ms, ns) ->
    let ptl = find_c c ctx in
    infer_ptl ctx env ms ns ptl
  | Match (m, mot, cls) -> (
    let* ty = infer_tm ctx env m in
    let* ty = unify >> resolve_tm ty in
    match whnf rd_all env ty with
    | Sigma (rel, srt, a, bnd) ->
      let* _ = infer_pair ctx env rel srt a bnd mot cls in
      return (subst mot m)
    | Data (d, ms) ->
      let _, cs = find_d d ctx in
      let* _ = infer_cls ctx env cs ms mot cls in
      return (subst mot m)
    | _ -> failwith "infer_tm(%a)" pp_tm m0)
  (* equality *)
  | Eq (a, m, n) ->
    let* _ = check_tm ctx env m a in
    let* _ = check_tm ctx env n a in
    return (Type U)
  | Refl m ->
    let* a = infer_tm ctx env m in
    return (Eq (a, m, m))
  | Rew (bnd, p, m) -> (
    let xs, mot = unmbind bnd in
    let* ty = infer_tm ctx env p in
    let* ty = unify >> resolve_tm ty in
    match (ty, xs) with
    | Eq (a, m, n), [| x; y |] ->
      let ctx' = add_v x a ctx in
      let ctx' = add_v y (Eq (a, m, Var x)) ctx' in
      let* _ = infer_sort ctx' env mot in
      let* _ = check_tm ctx env m (msubst bnd [| m; Refl m |]) in
      return (msubst bnd [| n; p |])
    | _ -> failwith "infer_rew")
  (* monadic *)
  | IO a ->
    let* _ = infer_sort ctx env a in
    return (Type L)
  | Return m ->
    let* a = infer_tm ctx env m in
    return (IO a)
  | MLet (m, bnd) -> (
    let* ty_m = infer_tm ctx env m in
    let* m = unify >> resolve_tm m in
    let* ty_m = resolve_tm ty_m in
    let x, n = unbind bnd in
    match whnf rd_all env ty_m with
    | IO a -> (
      let* ty_n = infer_tm (add_v x a ctx) env n in
      let* ty_n = unify >> resolve_tm ty_n in
      match whnf rd_all env ty_n with
      | IO b -> return (IO b)
      | _ -> failwith "infer_MLet")
    | _ -> failwith "infer_MLet")
  (* session *)
  | Proto -> return (Type U)
  | End -> return Proto
  | Act (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* _ = check_tm (add_v x a ctx) env b Proto in
    return Proto
  | Ch (_, a) ->
    let* _ = check_tm ctx env a Proto in
    return (Type L)
  | Open Stdin -> return (IO (Ch (Pos, Var Prelude1.stdin_t_v)))
  | Open Stdout -> return (IO (Ch (Pos, Var Prelude1.stdout_t_v)))
  | Open Stderr -> return (IO (Ch (Pos, Var Prelude1.stderr_t_v)))
  | Fork (a0, bnd) -> (
    let x, m = unbind bnd in
    let* _ = infer_sort ctx env a0 in
    let* a0 = unify >> resolve_tm a0 in
    match whnf rd_all env a0 with
    | Ch (Pos, a) ->
      let ty = IO (Data (Prelude1.unit_d, [])) in
      let* _ = check_tm (add_v x a0 ctx) env m ty in
      return (IO (Ch (Neg, a)))
    | _ -> failwith "infer_Fork")
  | Recv m -> (
    let* ty = infer_tm ctx env m in
    let* ty = unify >> resolve_tm ty in
    match whnf rd_all env ty with
    | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = true ->
      let x, b = unbind bnd in
      let bnd = unbox (bind_var x (lift_tm (Ch (rol1, b)))) in
      return (IO (Sigma (rel, L, a, bnd)))
    | _ -> failwith "infer_Recv")
  | Send m -> (
    let* ty = infer_tm ctx env m in
    let* ty = unify >> resolve_tm ty in
    match whnf rd_all env ty with
    | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = false ->
      let x, b = unbind bnd in
      let bnd = unbox (bind_var x (lift_tm (IO (Ch (rol1, b))))) in
      return (Pi (rel, L, a, bnd))
    | _ -> failwith "infer_Send")
  | Close m -> (
    let* ty = infer_tm ctx env m in
    let* ty = unify >> resolve_tm ty in
    match whnf rd_all env ty with
    | Ch (_, End) -> return (IO (Data (Prelude1.unit_d, [])))
    | _ -> failwith "infer_Close")

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
      let* _ = infer_sort ctx env mot in
      check_tm ctx env rhs mot
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
  let xs, rhs = unmbind bnd in
  let xs = Array.to_list xs in
  let ptl = find_c c ctx in
  let tl = init_param ms ptl in
  let ctx, ty = init_tele ctx xs tl in
  let mot = subst mot (Cons (c, ms, List.map var xs)) in
  let* _ = infer_sort ctx env mot in
  let* _ = check_tm ctx env rhs mot in
  return ()

and infer_ptm ctx env ms ptm =
  match (ms, ptm) with
  | [], PBase b ->
    let* _ = infer_sort ctx env b in
    return b
  | m :: ms, PBind (a, bnd) ->
    let* _ = check_tm ctx env m a in
    infer_ptm ctx env ms (subst bnd m)
  | _ -> failwith "infer_ptm(%a)" pp_ptm ptm

and infer_ptl ctx env ms ns ptl =
  match (ms, ptl) with
  | [], PBase tl -> infer_tele ctx env ns tl
  | m :: ms, PBind (a, bnd) ->
    let* _ = check_tm ctx env m a in
    infer_ptl ctx env ms ns (subst bnd m)
  | _ -> failwith "infer_ptl(%a)" pp_ptl ptl

and infer_tele ctx env ns tl =
  match (ns, tl) with
  | [], TBase b ->
    let* _ = infer_sort ctx env b in
    return b
  | n :: ns, TBind (_, a, bnd) ->
    let* _ = check_tm ctx env n a in
    infer_tele ctx env ns (subst bnd n)
  | _ -> failwith "infer_tele(%a)" pp_tele tl

and check_tm ctx env m a : unit trans1e =
  match m with
  | _ -> _
