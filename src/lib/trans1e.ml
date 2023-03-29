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

let ( >>= ) (m : 'a trans1e) (f : 'a -> 'b trans1e) : 'b trans1e =
 fun (eqns, map) ->
  let a, eqns', map' = m (eqns, map) in
  (f a) (eqns', map')

let ( >> ) (m : 'a trans1e) (n : 'b trans1e) : 'b trans1e =
 fun (eqns, map) ->
  let _, eqns', map' = m (eqns, map) in
  n (eqns', map')

let ( let* ) = ( >>= )
let run_trans1e (m : 'a trans1e) : 'a * eqns * map = m ([], MMap.empty)

let find_m x ctx : tm trans1e =
 fun (eqns, map) ->
  match MMap.find_opt x map with
  | Some (_, Some a) -> (a, eqns, map)
  | _ -> (fst (meta_mk ctx), eqns, map)

let add_m x a : unit trans1e =
 fun (eqns, map) -> ((), eqns, MMap.add x (None, Some a) map)

let assert_equal env m n : unit trans1e =
  let _ =
    pr "@[assert_equal(@;<1 2>%a@;<1 0>::::::@;<1 2>%a)@]@.@." pp_tm m pp_tm n
  in
  fun (eqns, map) ->
    if equal [| Beta; Delta; Zeta; Iota |] env m n then
      ((), eqns, map)
    else
      ((), (env, m, n) :: eqns, map)

let unify : unit trans1e =
 fun (eqns, map) ->
  let map = unify map eqns in
  ((), eqns, map)

let resolve_ptm ptm : tm param trans1e =
 fun (eqns, map) ->
  let ptm = resolve_param lift_tm resolve_tm map ptm in
  (ptm, eqns, map)

let resolve_ptl ptl : tele param trans1e =
 fun (eqns, map) ->
  let ptl = resolve_param lift_tele resolve_tele map ptl in
  (ptl, eqns, map)

let resolve_tm m : tm trans1e =
 fun (eqns, map) ->
  let m = resolve_tm map m in
  (m, eqns, map)

(* infer the type + sort of a term *)
let rec infer_sort ctx env a : unit trans1e =
  let* srt = infer_tm ctx env a in
  let* srt = resolve_tm srt in
  match whnf rd_all env srt with
  | Meta _ -> return ()
  | Type s -> return ()
  | _ -> failwith "infert_sort(%a)" pp_tm a

and infer_tm ctx env m0 : tm trans1e =
  let _ = pr "@[infer_tm(@;<1 2>%a)@]@.@." pp_tm m0 in
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
  | Lam (rel, srt, bnd) -> failwith "infer_Lam"
  | App (m, n) -> (
    let* ty = infer_tm ctx env m in
    let* ty = unify >> resolve_tm ty in
    match whnf rd_all env ty with
    | Pi (_, _, a, bnd) ->
      let* _ = check_tm ctx env n a in
      return (subst bnd n)
    | _ -> failwith "infer_App")
  | Let (rel, m, bnd) ->
    let* a = infer_tm ctx env m in
    let x, n = unbind bnd in
    infer_tm (add_v x a ctx) (VMap.add x m env) n
  | Fix _ -> failwith "infer_Fix"
  (* data *)
  | Sigma (R, srt, a, bnd) ->
    let x, b = unbind bnd in
    let* s = infer_sort ctx env a in
    let* r = infer_sort (add_v x a ctx) env b in
    return (Type srt)
  | Sigma (N, srt, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* r = infer_sort (add_v x a ctx) env b in
    return (Type srt)
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
  | Rew (bnd, p, h) -> (
    let xs, mot = unmbind bnd in
    let* ty = infer_tm ctx env p in
    let* ty = unify >> resolve_tm ty in
    match (ty, xs) with
    | Eq (a, m, n), [| x; y |] ->
      let ctx' = add_v x a ctx in
      let ctx' = add_v y (Eq (a, m, Var x)) ctx' in
      let* _ = infer_sort ctx' env mot in
      let* _ = check_tm ctx env h (msubst bnd [| m; Refl m |]) in
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
    let* ty_m = unify >> resolve_tm ty_m in
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
    | ty -> failwith "infer_Send(%a)" pp_tm ty)
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
      return ()
    else
      failwith "infer_cls(unmatched case)"
  | PCons (c, bnd) :: cls ->
    let* _ = infer_cl ctx env ms mot c bnd in
    infer_cls ctx env (CSet.remove c cs) ms mot cls
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

and check_tm ctx env m ty : unit trans1e =
  let _ =
    pr "@[check_tm(@;<1 2>%a@;<1 0>::::::@;<1 2>%a)@]@.@." pp_tm m pp_tm ty
  in
  match m with
  (* inference *)
  | Meta (x, _) -> add_m x ty
  (* core *)
  | Lam (rel0, srt0, bnd0) -> (
    let* ty = unify >> resolve_tm ty in
    match whnf rd_all env ty with
    | Pi (rel, srt, a, bnd) when rel = rel0 && srt = srt0 ->
      let x, b, m = unbind2 bnd bnd0 in
      check_tm (add_v x a ctx) env m b
    | _ -> failwith "check_Lam")
  | Let (rel, m, bnd) ->
    let* a = infer_tm ctx env m in
    let* m = unify >> resolve_tm m in
    let* a = unify >> resolve_tm a in
    let x, n = unbind bnd in
    check_tm (add_v x a ctx) (VMap.add x m env) n ty
  | Fix (_, bnd) ->
    let x, m = unbind bnd in
    check_tm (add_v x ty ctx) env m ty
  (* data *)
  | Pair (rel0, srt0, m, n) -> (
    let* ty = unify >> resolve_tm ty in
    match whnf rd_all env ty with
    | Sigma (rel, srt, a, bnd) when rel = rel0 && srt = srt0 ->
      let* _ = check_tm ctx env m a in
      check_tm ctx env n (subst bnd m)
    | ty -> failwith "check_Pair(%a)" pp_tm ty)
  | Match (m, mot, cls) -> (
    let* ty_m = infer_tm ctx env m in
    let ty' = subst mot m in
    let* _ = infer_sort ctx env ty' in
    let* _ = assert_equal env ty ty' in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf rd_all env ty_m with
    | Sigma (rel, srt, a, bnd) -> infer_pair ctx env rel srt a bnd mot cls
    | Data (d, ms) ->
      let _, cs = find_d d ctx in
      infer_cls ctx env cs ms mot cls
    | _ -> failwith "check_Match")
  (* other *)
  | _ ->
    let* ty' = infer_tm ctx env m in
    assert_equal env ty ty'

let rec check_dcls ctx env dcls =
  match dcls with
  | [] -> return ()
  | DTm (_, x, a, m) :: dcls ->
    let* _ = infer_sort ctx env a in
    let* _ = check_tm ctx env m a in
    let* m = unify >> resolve_tm m in
    let* a = unify >> resolve_tm a in
    check_dcls (add_v x a ctx) (VMap.add x m env) dcls
  | DData (d, ptm, dconss) :: dcls ->
    let* _ = check_ptm ctx env ptm in
    let* _ = unify >> resolve_ptm ptm in
    let ctx = add_d d ptm CSet.empty ctx in
    let* ctx, cs = check_dconss ctx env d dconss in
    let* _ = unify in
    check_dcls (add_d d ptm cs ctx) env dcls

and check_dconss ctx env d dconss =
  match dconss with
  | [] -> return (ctx, CSet.empty)
  | DCons (c, ptl) :: dconss ->
    let* _ = check_ptl ctx env d ptl in
    let* ptl = resolve_ptl ptl in
    let* ctx, cs = check_dconss ctx env d dconss in
    return (add_c c ptl ctx, CSet.add c cs)

and check_ptl ctx env d ptl =
  match ptl with
  | PBase tl -> check_tl ctx env d tl
  | PBind (a, bnd) ->
    let x, ptl = unbind bnd in
    let* _ = infer_sort ctx env a in
    check_ptl (add_v x a ctx) env d ptl

and check_tl ctx env d0 tl =
  match tl with
  | TBase (Data (d, _) as a) when D.equal d d0 -> infer_sort ctx env a
  | TBind (_, a, bnd) ->
    let x, tl = unbind bnd in
    let* _ = infer_sort ctx env a in
    check_tl (add_v x a ctx) env d0 tl
  | _ -> failwith "check_tl"

and check_ptm ctx env ptm =
  match ptm with
  | PBase (Type s) -> return s
  | PBind (a, bnd) ->
    let x, ptm = unbind bnd in
    let* _ = infer_sort ctx env a in
    check_ptm (add_v x a ctx) env ptm
  | _ -> failwith "check_ptm"

let trans_dcls dcls =
  let ctx = { vs = VMap.empty; ds = DMap.empty; cs = CMap.empty } in
  let _, eqns, map = run_trans1e (check_dcls ctx VMap.empty dcls) in
  let map = Unify1.unify map eqns in
  let _ = pr "%a@.@." pp_map map in
  resolve_dcls map dcls
