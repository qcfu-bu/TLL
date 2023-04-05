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
  ; (* sort variables in scope *)
    svar : SVSet.t
  ; (* type-schemes for constants *)
    const : tm scheme IMap.t
  ; (* type-schemes for data *)
    data : (tm param scheme * CSet.t) DMap.t
  ; (* type-schemes for constructors *)
    cons : tele param scheme CMap.t
  }

(* context of meta-variables *)
type mctx = tm MMap.t

let add_var x a ctx = { ctx with var = VMap.add x a ctx.var }

let add_svar xs ctx =
  let svar = SVSet.of_list (Array.to_list xs) in
  { ctx with svar = SVSet.union svar ctx.svar }

let add_const x sch ctx = { ctx with const = IMap.add x sch ctx.const }
let add_data d sch cs ctx = { ctx with data = DMap.add d (sch, cs) ctx.data }
let add_cons c sch ctx = { ctx with cons = CMap.add c sch ctx.cons }

let find_var x ctx =
  match VMap.find_opt x ctx.var with
  | Some a -> a
  | None -> failwith "find_var(%a)" V.pp x

let find_const x ctx =
  match IMap.find_opt x ctx.const with
  | Some sch -> sch
  | None -> failwith "find_const(%a)" I.pp x

let find_data d ctx =
  match DMap.find_opt d ctx.data with
  | Some res -> res
  | None -> failwith "find_data(%a)" D.pp d

let find_cons c ctx =
  match CMap.find_opt c ctx.cons with
  | Some sch -> sch
  | None -> failwith "find_cons(%a)" C.pp c

let smeta_mk ctx =
  let x = M.mk () in
  let ss = ctx.svar |> SVSet.elements |> List.map (fun x -> SVar x) in
  (SMeta (x, ss), x)

let meta_mk ctx =
  let x = M.mk () in
  let ss = ctx.svar |> SVSet.elements |> List.map (fun x -> SVar x) in
  let xs = ctx.var |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, ss, xs), x)

(* monad for collecting unification constraints *)
type 'a trans1e = mctx * eqns * map0 * map1 -> 'a * mctx * eqns * map0 * map1

let return (a : 'a) : 'a trans1e =
 fun (mctx, eqns, map0, map1) -> (a, mctx, eqns, map0, map1)

let ( >>= ) (m : 'a trans1e) (f : 'a -> 'b trans1e) : 'b trans1e =
 fun (mctx, eqns, map0, map1) ->
  let a, mctx, eqns, map0, map1 = m (mctx, eqns, map0, map1) in
  (f a) (mctx, eqns, map0, map1)

let ( >> ) (m : 'a trans1e) (n : 'b trans1e) : 'b trans1e =
 fun (mctx, eqns, map0, map1) ->
  let _, mctx, eqns, map0, map1 = m (mctx, eqns, map0, map1) in
  n (mctx, eqns, map0, map1)

let ( let* ) = ( >>= )

let run_trans1e (m : 'a trans1e) : 'a * mctx * eqns * map0 * map1 =
  m (MMap.empty, [], MMap.empty, MMap.empty)

let find_meta x ctx : tm trans1e =
 fun (mctx, eqns, map0, map1) ->
  match MMap.find_opt x mctx with
  | Some a -> (a, mctx, eqns, map0, map1)
  | None ->
    let a, _ = meta_mk ctx in
    (a, MMap.add x a mctx, eqns, map0, map1)

let add_meta env x a : unit trans1e =
 fun (mctx, eqns, map0, map1) ->
  match MMap.find_opt x mctx with
  | Some b -> ((), mctx, Eqn1 (env, a, b) :: eqns, map0, map1)
  | None -> ((), MMap.add x a mctx, eqns, map0, map1)

(* assert equality between two sorts *)
let assert_equal0 s1 s2 : unit trans1e =
 fun (mctx, eqns, map0, map1) ->
  if eq_sort s1 s2 then
    ((), mctx, eqns, map0, map1)
  else
    ((), mctx, Eqn0 (s1, s2) :: eqns, map0, map1)

(* assert equality between two terms *)
let assert_equal1 env m n : unit trans1e =
 fun (mctx, eqns, map0, map1) ->
  if eq_tm env m n then
    ((), mctx, eqns, map0, map1)
  else
    ((), mctx, Eqn1 (env, m, n) :: eqns, map0, map1)

(* assert equality between terms and their sorts *)
let assert_equal env (m, s1) (n, s2) : unit trans1e =
  let* _ = assert_equal0 s1 s2 in
  let* _ = assert_equal1 env m n in
  return ()

let unify : unit trans1e =
 fun (mctx, eqns, map0, map1) ->
  let map0, map1 = unify (map0, map1) eqns in
  ((), mctx, [], map0, map1)

let resolve_ptm ptm : tm param trans1e =
 fun (mctx, eqns, map0, map1) ->
  let ptm = resolve_param lift_tm resolve_tm (map0, map1) ptm in
  (ptm, mctx, eqns, map0, map1)

let resolve_ptl ptl : tele param trans1e =
 fun (mctx, eqns, map0, map1) ->
  let ptl = resolve_param lift_tele resolve_tele (map0, map1) ptl in
  (ptl, mctx, eqns, map0, map1)

let resolve_tm m : tm trans1e =
 fun (mctx, eqns, map0, map1) ->
  let m = resolve_tm (map0, map1) m in
  (m, mctx, eqns, map0, map1)

(* assert the sort of a type *)
let rec infer_sort ctx env a : sort trans1e =
  let* srt = infer_tm ctx env a in
  let* srt = resolve_tm srt in
  match whnf env srt with
  | Type s -> return s
  | _ ->
    let s, _ = smeta_mk ctx in
    let* _ = assert_equal1 env srt (Type s) in
    return s

and infer_tm ctx env m0 : tm trans1e =
  match m0 with
  (* inference *)
  | Ann (m, a) ->
    let* _ = infer_sort ctx env a in
    let* _ = check_tm ctx env m a in
    return a
  | Meta (x, _, _) -> find_meta x ctx
  (* core *)
  | Type _ -> return (Type U)
  | Var x -> return (find_var x ctx)
  | Const (x, ss) ->
    let sch = find_const x ctx in
    return (msubst sch (Array.of_list ss))
  | Pi (rel, s, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* _ = infer_sort (add_var x a ctx) env b in
    return (Type s)
  | Lam (rel, s, a, bnd) ->
    let x, m = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* b = infer_tm (add_var x a ctx) env m in
    let bnd = bind_var x (lift_tm b) in
    return (Pi (rel, s, a, unbox bnd))
  | App (m, n) -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Pi (_, _, a, bnd) ->
      let* _ = check_tm ctx env n a in
      return (subst bnd n)
    | _ -> failwith "infer_App")
  | Let (rel, m, bnd) ->
    let x, n = unbind bnd in
    let* a = infer_tm ctx env m in
    let* a = unify >> resolve_tm a in
    infer_tm (add_var x a ctx) (Env.add_var x m env) n
  (* data *)
  | Sigma (rel, s, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* _ = infer_sort (add_var x a ctx) env b in
    return (Type s)
  | Pair (rel, s, m, n) ->
    let* a = infer_tm ctx env m in
    let* b = infer_tm ctx env n in
    let x = V.mk "_" in
    let bnd = bind_var x (lift_tm b) in
    return (Sigma (rel, s, a, unbox bnd))
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
    match whnf env ty_m with
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
    let* _ = infer_sort ctx env a in
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
    match (whnf env ty_p, xs) with
    | Eq (a, m, n), [| x; y |] ->
      let ctx' = add_var x a ctx in
      let ctx' = add_var y (Eq (a, m, Var x)) ctx' in
      let* _ = infer_sort ctx' env mot in
      let* _ = check_tm ctx env h (msubst bnd [| m; Refl m |]) in
      return (msubst bnd [| n; p |])
    | _ -> failwith "infer_Rew(%a)" pp_tm m0)
  (* monadic *)
  | IO a ->
    let* _ = infer_sort ctx env a in
    return (Type L)
  | Return m ->
    let* a = infer_tm ctx env m in
    return (IO a)
  | MLet (m, bnd) -> (
    let x, n = unbind bnd in
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | IO a -> (
      let* ty_n = infer_tm (add_var x a ctx) env n in
      let* ty_n = unify >> resolve_tm ty_n in
      match whnf env ty_n with
      | IO b -> return (IO b)
      | _ -> failwith "infer_MLet")
    | _ -> failwith "infer_MLet")
  (* session *)
  | Proto -> return (Type U)
  | End -> return Proto
  | Act (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* _ = check_tm (add_var x a ctx) env b Proto in
    return Proto
  | Ch (_, a) ->
    let* _ = check_tm ctx env a Proto in
    return (Type L)
  | Open Stdin -> return (IO (Ch (Pos, Const (Prelude1.stdin_t_i, []))))
  | Open Stdout -> return (IO (Ch (Pos, Const (Prelude1.stdout_t_i, []))))
  | Open Stderr -> return (IO (Ch (Pos, Const (Prelude1.stderr_t_i, []))))
  | Fork (a0, bnd) -> (
    let x, m = unbind bnd in
    let* _ = infer_sort ctx env a0 in
    let* a0 = unify >> resolve_tm a0 in
    match whnf env a0 with
    | Ch (Pos, a) ->
      let ty = IO (Data (Prelude1.unit_d, [], [])) in
      let* _ = check_tm (add_var x a0 ctx) env m ty in
      return (IO (Ch (Neg, a)))
    | _ -> failwith "infer_Fork")
  | Recv m -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = true ->
      let x, b = unbind bnd in
      let bnd = unbox (bind_var x (lift_tm (Ch (rol1, b)))) in
      return (IO (Sigma (rel, L, a, bnd)))
    | ty -> failwith "infer_Recv(%a)" pp_tm ty)
  | Send m -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = false ->
      let x, b = unbind bnd in
      let bnd = unbox (bind_var x (lift_tm (IO (Ch (rol1, b))))) in
      return (Pi (rel, L, a, bnd))
    | ty -> failwith "infer_Send(%a)" pp_tm ty)
  | Close m -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
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
      let* _ = infer_sort ctx env mot in
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

and check_tm ctx env m0 a0 : unit trans1e =
  let* a0 = unify >> resolve_tm a0 in
  match (m0, whnf env a0) with
  (* inference *)
  | Meta (x, _, _), a0 -> add_meta env x a0
  | Ann (m, a1), a0 ->
    let* s0 = infer_sort ctx env a0 in
    let* s1 = infer_sort ctx env a1 in
    let* _ = assert_equal env (a0, s0) (a1, s1) in
    let* a1 = unify >> resolve_tm a1 in
    check_tm ctx env m a1
  (* core *)
  | Lam (rel0, s0, a0, bnd0), Pi (rel1, s1, a1, bnd1) when rel0 = rel1 ->
    let x, m, b = unbind2 bnd0 bnd1 in
    let* t0 = infer_sort ctx env a0 in
    let* t1 = infer_sort ctx env a1 in
    let* _ = assert_equal0 s0 s1 in
    let* _ = assert_equal env (a0, t0) (a1, t1) in
    check_tm (add_var x a1 ctx) env m b
  | Let (rel, m, bnd), a0 ->
    let x, n = unbind bnd in
    let* a = infer_tm ctx env m in
    let* a = unify >> resolve_tm a in
    let* m = unify >> resolve_tm m in
    check_tm (add_var x a ctx) (Env.add_var x m env) n a0
  (* data *)
  | Pair (rel0, s0, m, n), Sigma (rel1, s1, a, bnd) when rel0 = rel1 ->
    let* _ = assert_equal0 s0 s1 in
    let* _ = check_tm ctx env m a in
    check_tm ctx env n (subst bnd (Ann (m, a)))
  | Match (m, mot, cls), a0 -> (
    let* ty_m = infer_tm ctx env m in
    let a1 = subst mot m in
    let* s0 = infer_sort ctx env a0 in
    let* s1 = infer_sort ctx env a1 in
    let* _ = assert_equal env (a0, s0) (a1, s1) in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Sigma (rel, srt, a, bnd) -> infer_pair ctx env rel srt a bnd mot cls
    | Data (d, ss, ms) ->
      let _, cs = find_data d ctx in
      infer_cls ctx env cs ss ms mot cls
    | _ ->
      let* a1 = infer_tm ctx env m0 in
      let* s0 = infer_sort ctx env a0 in
      let* s1 = infer_sort ctx env a1 in
      let* _ = assert_equal env (a0, s0) (a1, s1) in
      return ())
  (* other *)
  | m0, a0 ->
    let* a1 = infer_tm ctx env m0 in
    let* s0 = infer_sort ctx env a0 in
    let* s1 = infer_sort ctx env a1 in
    let* _ = assert_equal env (a0, s0) (a1, s1) in
    return ()

let rec check_dcls ctx env dcls =
  match dcls with
  | [] -> return ()
  | DTm (_, x, guard, sch) :: dcls ->
    let xs, (a, m) = unmbind sch in
    let sch_a = unbox (bind_mvar xs (lift_tm a)) in
    let sch_m = unbox (bind_mvar xs (lift_tm m)) in
    let ctx' = add_svar xs ctx in
    let* _ = infer_sort ctx' env a in
    let* _ =
      if guard then
        check_tm (add_const x sch_a ctx') env m a
      else
        check_tm ctx' env m a
    in
    let ctx = add_const x sch_a ctx in
    let env =
      Env.add_const x
        { scheme = (fun ss -> msubst sch_m (Array.of_list ss))
        ; guarded = guard
        }
        env
    in
    check_dcls ctx env dcls
  | DData (d, sch, dconss) :: dcls ->
    let xs, ptm = unmbind sch in
    let ctx' = add_svar xs ctx in
    let* _ = check_ptm ctx' env ptm in
    let ctx' = add_data d sch CSet.empty ctx' in
    let* dconss = check_dconss ctx' env d dconss in
    let ctx, cs =
      List.fold_right
        (fun (c, sch) (ctx, cs) -> (add_cons c sch ctx, CSet.add c cs))
        dconss (ctx, CSet.empty)
    in
    check_dcls (add_data d sch cs ctx) env dcls

and check_ptm ctx env ptm =
  match ptm with
  | PBase (Type s) -> return s
  | PBind (a, bnd) ->
    let x, ptm = unbind bnd in
    let* _ = infer_sort ctx env a in
    check_ptm (add_var x a ctx) env ptm
  | _ -> failwith "check_ptm"

and check_dconss ctx env d dconss =
  match dconss with
  | [] -> return []
  | DCons (c, sch) :: dconss ->
    let _, ptl = unmbind sch in
    let* _ = check_ptl ctx env d ptl in
    let* dconss = check_dconss ctx env d dconss in
    return ((c, sch) :: dconss)

and check_ptl ctx env d ptl =
  match ptl with
  | PBase tl -> check_tl ctx env d tl
  | PBind (a, bnd) ->
    let x, ptl = unbind bnd in
    let* _ = infer_sort ctx env a in
    check_ptl (add_var x a ctx) env d ptl

and check_tl ctx env d0 tl =
  match tl with
  | TBase (Data (d, _, _) as a) when D.equal d d0 -> infer_sort ctx env a
  | TBind (_, a, bnd) ->
    let x, tl = unbind bnd in
    let* _ = infer_sort ctx env a in
    check_tl (add_var x a ctx) env d0 tl
  | _ -> failwith "check_tl"

let trans_dcls dcls =
  let ctx =
    { var = VMap.empty
    ; svar = SVSet.empty
    ; const = IMap.empty
    ; data = DMap.empty
    ; cons = CMap.empty
    }
  in
  let _, _, eqns, map0, map1 = run_trans1e (check_dcls ctx Env.empty dcls) in
  let map0, map1 = Unify1.unify (map0, map1) eqns in
  resolve_dcls (map0, map1) dcls
