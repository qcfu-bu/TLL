open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Unify1
open Pprint1

type ctx =
  { (* types for variables *)
    var : tm VMap.t
  ; (* type-schemes for constants *)
    const : tm scheme VMap.t
  ; (* type-schemes for data *)
    data : (tm param scheme * CSet.t) DMap.t
  ; (* type-schemes for constructors *)
    cons : tele param scheme CMap.t
  }

let add_var x a ctx = { ctx with var = VMap.add x a ctx.var }
let add_const x sch ctx = { ctx with const = VMap.add x sch ctx.const }
let add_data d sch cs ctx = { ctx with data = DMap.add d (sch, cs) ctx.data }
let add_cons c sch ctx = { ctx with cons = CMap.add c sch ctx.cons }

let find_var x ctx =
  match VMap.find_opt x ctx.var with
  | Some a -> a
  | None -> failwith "find_var(%a)" V.pp x

let find_const x ctx =
  match VMap.find_opt x ctx.const with
  | Some sch -> sch
  | None -> failwith "find_const(%a)" V.pp x

let find_data d ctx =
  match DMap.find_opt d ctx.data with
  | Some res -> res
  | None -> failwith "find_data(%a)" D.pp d

let find_cons c ctx =
  match CMap.find_opt c ctx.cons with
  | Some sch -> sch
  | None -> failwith "find_cons(%a)" C.pp c

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.var |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, xs), x)

(* monad for collecting unification constraints *)
type 'a trans1e = eqns * map0 * map1 -> 'a * eqns * map0 * map1

let return (a : 'a) : 'a trans1e =
 fun (eqns, map0, map1) -> (a, eqns, map0, map1)

let ( >>= ) (m : 'a trans1e) (f : 'a -> 'b trans1e) : 'b trans1e =
 fun (eqns, map0, map1) ->
  let a, eqns, map0, map1 = m (eqns, map0, map1) in
  (f a) (eqns, map0, map1)

let ( >> ) (m : 'a trans1e) (n : 'b trans1e) : 'b trans1e =
 fun (eqns, map0, map1) ->
  let _, eqns, map0, map1 = m (eqns, map0, map1) in
  n (eqns, map0, map1)

let ( let* ) = ( >>= )

let run_trans1e (m : 'a trans1e) : 'a * eqns * map0 * map1 =
  m ([], MMap.empty, MMap.empty)

let find_meta x ctx : tm trans1e =
 fun (eqns, map0, map1) ->
  match MMap.find_opt x map1 with
  | Some (_, Some a) -> (a, eqns, map0, map1)
  | _ ->
    let a, _ = meta_mk ctx in
    (a, eqns, map0, MMap.add x (None, Some a) map1)

let add_meta x a : unit trans1e =
 fun (eqns, map0, map1) -> ((), eqns, map0, MMap.add x (None, Some a) map1)

(* assert equality between two sorts *)
let assert_equal0 s1 s2 : unit trans1e =
 fun (eqns, map0, map1) -> ((), Eqn0 (s1, s2) :: eqns, map0, map1)

(* assert equality between two terms *)
let assert_equal env m n : unit trans1e =
  let _ =
    pr "@[assert_equal(@;<1 2>%a@;<1 0>::::::@;<1 2>%a)@]@.@." pp_tm m pp_tm n
  in
  fun (eqns, map0, map1) ->
    if eq_tm rd_all env m n then
      ((), eqns, map0, map1)
    else
      ((), Eqn1 (env, m, n) :: eqns, map0, map1)

let unify : unit trans1e =
 fun (eqns, map0, map1) ->
  let map0, map1 = unify (map0, map1) eqns in
  ((), eqns, map0, map1)

let resolve_ptm ptm : tm param trans1e =
 fun (eqns, map0, map1) ->
  let ptm = resolve_param lift_tm resolve_tm (map0, map1) ptm in
  (ptm, eqns, map0, map1)

let resolve_ptl ptl : tele param trans1e =
 fun (eqns, map0, map1) ->
  let ptl = resolve_param lift_tele resolve_tele (map0, map1) ptl in
  (ptl, eqns, map0, map1)

let resolve_tm m : tm trans1e =
 fun (eqns, map0, map1) ->
  let m = resolve_tm (map0, map1) m in
  (m, eqns, map0, map1)

(* assert the sort of a type *)
let rec assert_sort ctx env a : unit trans1e =
  let* srt = infer_tm ctx env a in
  let x = M.mk () in
  assert_equal env srt (Type (SMeta x))

and infer_tm ctx env m0 : tm trans1e =
  let _ = pr "@[infer_tm(@;<1 2>%a)@]@.@." pp_tm m0 in
  match m0 with
  (* inference *)
  | Ann (m, a) ->
    let* _ = assert_sort ctx env a in
    let* _ = check_tm ctx env m a in
    return a
  | Meta (x, _) -> find_meta x ctx
  (* core *)
  | Type _ -> return (Type U)
  | Var x -> return (find_var x ctx)
  | Const (x, ss) ->
    let sch = find_const x ctx in
    return (msubst sch (Array.of_list ss))
  | Pi (rel, s, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = assert_sort ctx env a in
    let* _ = assert_sort (add_var x a ctx) env b in
    return (Type s)
  | Lam (rel, s, bnd) ->
    let x, m = unbind bnd in
    let a, _ = meta_mk ctx in
    let* b = infer_tm (add_var x a ctx) env m in
    let bnd = bind_var x (lift_tm b) in
    return (Pi (rel, s, a, unbox bnd))
  | App (m, n) -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf rd_all env ty_m with
    | Pi (_, _, a, bnd) ->
      let* _ = check_tm ctx env n a in
      return (subst bnd n)
    | _ -> failwith "infer_App")
  | Let (rel, m, bnd) ->
    let* a = infer_tm ctx env m in
    infer_tm ctx env (subst bnd (Ann (m, a)))
  (* data *)
  | Sigma (rel, s, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = assert_sort ctx env a in
    let* _ = assert_sort (add_var x a ctx) env b in
    return (Type s)
  | Pair (rel, s, m, n) ->
    let* a = infer_tm ctx env m in
    let* b = infer_tm ctx env n in
    let x = V.mk "_" in
    let bnd = unbox (bind_var x (lift_tm b)) in
    let ty = Sigma (rel, s, a, bnd) in
    return ty
  | Data (d, ss, ms) ->
    let sch, _ = find_data d ctx in
    let ptm = msubst sch (Array.of_list ss) in
    infer_ptm ctx env ms ptm
  | Cons (c, ss, ms, ns) ->
    let sch = find_cons c ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_ptl ctx env ms ns ptl
  | Match (m, mot, cls) -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf rd_all env ty_m with
    | Sigma (rel, s, a, bnd) ->
      let* _ = infer_pair ctx env rel s a bnd mot cls in
      return (subst mot m)
    | Data (d, ss, ms) ->
      let _, cs = find_data d ctx in
      let* _ = infer_cls ctx env cs ss ms mot cls in
      return (subst mot m)
    | _ -> failwith "infer_Match(%a)" pp_tm m0)
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
    let* ty_p = infer_tm ctx env p in
    let* ty_p = unify >> resolve_tm ty_p in
    match (ty_p, xs) with
    | Eq (a, m, n), [| x; y |] ->
      let ctx' = add_var x a ctx in
      let ctx' = add_var y (Eq (a, m, Var x)) ctx' in
      let* _ = assert_sort ctx' env mot in
      let* _ = check_tm ctx env h (msubst bnd [| m; Refl m |]) in
      return (msubst bnd [| n; p |])
    | _ -> failwith "infer_Rew(%a)" pp_tm m0)
  (* monadic *)
  | IO a ->
    let* _ = assert_sort ctx env a in
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
      let* ty_n = infer_tm (add_var x a ctx) env n in
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
    let* _ = assert_sort ctx env a in
    let* _ = check_tm (add_var x a ctx) env b Proto in
    return Proto
  | Ch (_, a) ->
    let* _ = check_tm ctx env a Proto in
    return (Type L)
  | Open Stdin -> return (IO (Ch (Pos, Const (Prelude1.stdin_t_v, []))))
  | Open Stdout -> return (IO (Ch (Pos, Const (Prelude1.stdout_t_v, []))))
  | Open Stderr -> return (IO (Ch (Pos, Const (Prelude1.stderr_t_v, []))))
  | Fork (a0, bnd) -> (
    let x, m = unbind bnd in
    let* _ = assert_sort ctx env a0 in
    let* a0 = unify >> resolve_tm a0 in
    match whnf rd_all env a0 with
    | Ch (Pos, a) ->
      let ty = IO (Data (Prelude1.unit_d, [], [])) in
      let* _ = check_tm (add_var x a0 ctx) env m ty in
      return (IO (Ch (Neg, a)))
    | _ -> failwith "infer_Fork")
  | Recv m -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf rd_all env ty_m with
    | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = true ->
      let x, b = unbind bnd in
      let bnd = unbox (bind_var x (lift_tm (Ch (rol1, b)))) in
      return (IO (Sigma (rel, L, a, bnd)))
    | ty -> failwith "infer_Recv(%a)" pp_tm ty)
  | Send m -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf rd_all env ty_m with
    | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = false ->
      let x, b = unbind bnd in
      let bnd = unbox (bind_var x (lift_tm (IO (Ch (rol1, b))))) in
      return (Pi (rel, L, a, bnd))
    | ty -> failwith "infer_Send(%a)" pp_tm ty)
  | Close m -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf rd_all env ty_m with
    | Ch (_, End) -> return (IO (Data (Prelude1.unit_d, [], [])))
    | ty -> failwith "infer_Close(%a)" pp_tm ty)

and infer_pair ctx env rel s a b mot cls =
  match cls with
  | [ PPair (rel0, s0, bnd) ] when rel = rel0 -> (
    let* _ = assert_equal0 s s0 in
    let xs, rhs = unmbind bnd in
    match xs with
    | [| x; y |] ->
      let ctx = add_var x a ctx in
      let ctx = add_var y (subst b (Var x)) ctx in
      let tm = Pair (rel, s, Var x, Var y) in
      let ty = Sigma (rel, s, a, b) in
      let mot = subst mot (Ann (tm, ty)) in
      let* _ = assert_sort ctx env mot in
      check_tm ctx env rhs mot
    | _ -> failwith "infer_pair")
  | _ -> failwith "infer_pair"

and infer_cls ctx env cs ss ms mot cls =
  match cls with
  | [] -> return ()
  | PCons (c, bnd) :: cls -> (
    match CSet.find_opt c cs with
    | Some _ ->
      let* _ = infer_cl ctx env ss ms mot c bnd in
      infer_cls ctx env cs ss ms mot cls
    | _ -> failwith "infer_cls")
  | PPair _ :: _ -> failwith "infer_cls"

and infer_cl ctx env ss ms mot c bnd =
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
      let ctx = add_var x a ctx in
      let tl = subst bnd (Var x) in
      init_tele ctx xs tl
    | _ -> failwith "init_tele"
  in
  let xs, rhs = unmbind bnd in
  let xs = Array.to_list xs in
  let sch = find_cons c ctx in
  let ptl = msubst sch (Array.of_list ss) in
  let tl = init_param ms ptl in
  let ctx, ty = init_tele ctx xs tl in
  let mot = subst mot (Cons (c, ss, ms, List.map var xs)) in
  let* _ = assert_sort ctx env mot in
  let* _ = check_tm ctx env rhs mot in
  return ()

and infer_ptm ctx env ms ptm =
  match (ms, ptm) with
  | [], PBase b ->
    let* _ = assert_sort ctx env b in
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
    let* _ = assert_sort ctx env b in
    return b
  | n :: ns, TBind (_, a, bnd) ->
    let* _ = check_tm ctx env n a in
    infer_tele ctx env ns (subst bnd n)
  | _ -> failwith "infer_tele(%a)" pp_tele tl

and check_tm ctx env m0 a0 : unit trans1e =
  let _ =
    pr "@[check_tm(@;<1 2>%a@;<1 0>::::::@;<1 2>%a)@]@.@." pp_tm m0 pp_tm a0
  in
  match m0 with
  (* inference *)
  | Meta (x, _) -> add_meta x a0
  | Ann (m, a) ->
    let* _ = assert_sort ctx env a in
    let* _ = assert_equal env a a0 in
    let* a = unify >> resolve_tm a in
    check_tm ctx env m a
  (* core *)
  | Lam (rel0, s0, bnd0) -> (
    let* a0 = unify >> resolve_tm a0 in
    match whnf rd_all env a0 with
    | Pi (rel1, s1, a1, bnd1) when rel0 = rel1 ->
      let* _ = assert_equal0 s0 s1 in
      let x, m, b = unbind2 bnd0 bnd1 in
      check_tm (add_var x a1 ctx) env m b
    | _ -> failwith "check_Lam")
  | Let (rel, m, bnd) ->
    let* a = infer_tm ctx env m in
    check_tm ctx env (subst bnd (Ann (m, a))) a0
  (* data *)
  | Pair (rel0, s0, m, n) -> (
    let* a0 = unify >> resolve_tm a0 in
    match whnf rd_all env a0 with
    | Sigma (rel1, s1, a, bnd) when rel0 = rel1 ->
      let* _ = assert_equal0 s0 s1 in
      let* _ = check_tm ctx env m a in
      check_tm ctx env n (subst bnd m)
    | ty -> failwith "check_Pair(%a)" pp_tm ty)
  | Match (m, mot, cls) -> (
    let* ty_m = infer_tm ctx env m in
    let a1 = subst mot m in
    let* _ = assert_sort ctx env a1 in
    let* _ = assert_equal env a0 a1 in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf rd_all env ty_m with
    | Sigma (rel, srt, a, bnd) -> infer_pair ctx env rel srt a bnd mot cls
    | Data (d, ss, ms) ->
      let _, cs = find_data d ctx in
      infer_cls ctx env cs ss ms mot cls
    | _ -> failwith "check_Match")
  (* other *)
  | _ ->
    let* a1 = infer_tm ctx env m0 in
    assert_equal env a0 a1
