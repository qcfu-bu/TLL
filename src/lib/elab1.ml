open Fmt
open Names
open Syntax1
open Equality1
open Pprint1
open Unify1

type ctx =
  { vs : tm VMap.t
  ; ds : (ptl * C.t list) DMap.t
  ; cs : ptl CMap.t
  }

let add_v x a ctx = { ctx with vs = VMap.add x a ctx.vs }
let add_d d ptl cs ctx = { ctx with ds = DMap.add d (ptl, cs) ctx.ds }
let add_c c ptl ctx = { ctx with cs = CMap.add c ptl ctx.cs }
let add_m x a map = MMap.add x (None, Some a) map

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

let find_m x map =
  match MMap.find_opt x map with
  | Some (_, Some a) -> a
  | _ -> failwith "find_m(%a)" M.pp x

let pp_vs fmt vs =
  let aux fmt vs =
    VMap.iter (fun x a -> pf fmt "@[%a :@;<1 2>%a@]@;<1 2>" V.pp x pp_tm a) vs
  in
  pf fmt "@[<v 0>vs={@;<1 2>%a}@]" aux vs

let pp_ds fmt ds =
  let aux fmt ds =
    DMap.iter
      (fun d (ptl, _) -> pf fmt "@[%a : %a@]@;<1 2>" D.pp d pp_ptl ptl)
      ds
  in
  pf fmt "@[<v 0>ds={@;<1 2>%a}@]" aux ds

let pp_cs fmt cs =
  let aux fmt cs =
    CMap.iter (fun c ptl -> pf fmt "@[%a : %a@]@;<1 2>" C.pp c pp_ptl ptl) cs
  in
  pf fmt "@[<v 0>cs={@;<1 2>%a}@]" aux cs

let pp_ctx fmt ctx = pf fmt "@[<v 0>ctx{@;<1 2>%a}@]" pp_vs ctx.vs

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.vs |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, xs), x)

let assert_equal env eqns map m n =
  if equal rd_all env m n then
    (eqns, map)
  else
    ((env, m, n) :: eqns, map)

let rec infer_sort ctx env eqns map a =
  let srt, eqns, map = infer_tm ctx env eqns map a in
  let srt = resolve_tm map srt in
  match whnf rd_all env srt with
  | Type s -> (s, eqns, map)
  | _ -> failwith "infer_sort(%a : %a)" pp_tm a pp_tm srt

and infer_tm ctx env eqns map m =
  let _ = pr "elab_infer(%a)@." pp_tm m in
  match m with
  | Ann (a, m) -> (
    match m with
    | Let (r, m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let eqns, map = check_tm ctx env eqns map (Let (r, m, abs)) a in
      (a, eqns, map)
    | _ ->
      let eqns, map = check_tm ctx env eqns map m a in
      (a, eqns, map))
  | Meta (x, _) -> (
    try (find_m x map, eqns, map) with
    | _ ->
      let meta, _ = meta_mk ctx in
      (meta, eqns, add_m x meta map))
  | Type _ -> (Type U, eqns, map)
  | Var x -> (find_v x ctx, eqns, map)
  | Pi (_, s, a, abs) ->
    let x, b = unbind_tm abs in
    let _, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    let _, eqns, map = infer_sort ctx env eqns map b in
    (Type s, eqns, map)
  | Lam _ ->
    let a, _ = meta_mk ctx in
    (a, eqns, map)
  | App (m, n) -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = resolve_tm map a in
    match whnf rd_all env a with
    | Pi (_, _, a, abs) ->
      let eqns, map = check_tm ctx env eqns map n a in
      (asubst_tm abs (Ann (a, n)), eqns, map)
    | _ -> (fst (meta_mk ctx), eqns, map))
  | Let (_, m, abs) ->
    let a, eqns, map = infer_tm ctx env eqns map m in
    let _, eqns, map = infer_sort ctx env eqns map a in
    let map = unify map eqns in
    let m = resolve_tm map m in
    let a = resolve_tm map a in
    let x, n = unbind_tm abs in
    let ctx = add_v x a ctx in
    let env = VMap.add x m env in
    infer_tm ctx env eqns map n
  | Data (d, ms) ->
    let ptl, _ = find_d d ctx in
    check_ptl ctx env eqns map ms ptl
  | Cons (c, ms) ->
    let ptl = find_c c ctx in
    check_ptl ctx env eqns map ms ptl
  | Match (m, mot, cls) -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let map = unify map eqns in
    let a = resolve_tm map a in
    let a = whnf rd_all env a in
    match a with
    | Data (d, ms) -> (
      let _, cs = find_d d ctx in
      let cover, eqns, map = coverage ctx env eqns map cls cs ms in
      match mot with
      | Mot0 -> (
        let ts, eqns, map = infer_cover cover env eqns map in
        match ts with
        | [] -> failwith "infer_Mot0"
        | t0 :: ts ->
          let eqns =
            List.fold_left (fun acc t -> (env, t0, t) :: acc) eqns ts
          in
          (t0, eqns, map))
      | Mot1 abs ->
        let b = asubst_tm abs m in
        let eqns, map = check_mot cover env eqns map mot in
        (b, eqns, map)
      | Mot2 abs ->
        let p, b = unbindp_tm abs in
        let b = substp_tm p b a in
        let eqns, map = check_mot cover env eqns map mot in
        (b, eqns, map)
      | Mot3 abs ->
        let x, abs = unbind_ptm abs in
        let p, b = unbindp_tm abs in
        let b = subst_tm x b m in
        let b = substp_tm p b a in
        (b, eqns, map))
    | _ -> failwith "infer_Match(%a)" pp_tm m)
  | Fix abs as m -> (
    let _, n = unbind_tm abs in
    match n with
    | Ann (a, _) ->
      let _, eqns, map = infer_sort ctx env eqns map a in
      let eqns, map = check_tm ctx env eqns map m a in
      (a, eqns, map)
    | _ ->
      let a, _ = meta_mk ctx in
      (a, eqns, map))

and check_ptl ctx env eqns map ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (a, abs) ->
    let _, eqns, map = infer_sort ctx env eqns map a in
    let eqns, map = check_tm ctx env eqns map m a in
    check_ptl ctx env eqns map ms (asubst_ptl abs (Ann (a, m)))
  | ms, PBase tl -> check_tl ctx env eqns map ms tl
  | _ -> failwith "check_ptl(%a, %a)" pp_tms ms pp_ptl ptl

and check_tl ctx env eqns map ms tl =
  match (ms, tl) with
  | m :: ms, TBind (_, a, abs) ->
    let _, eqns, map = infer_sort ctx env eqns map a in
    let eqns, map = check_tm ctx env eqns map m a in
    check_tl ctx env eqns map ms (asubst_tl abs (Ann (a, m)))
  | [], TBase a ->
    let _, eqns, map = infer_sort ctx env eqns map a in
    (a, eqns, map)
  | _ -> failwith "check_tl(%a, %a)" pp_tms ms pp_tl tl

and check_tm ctx env eqns map m a =
  let _ = pr "elab_check(%a :? %a)@." pp_tm m pp_tm a in
  match m with
  | Meta (x, _) -> (eqns, add_m x a map)
  | Lam (r1, s1, abs) -> (
    let x, m = unbind_tm abs in
    let a = resolve_tm map a in
    match whnf rd_all env a with
    | Pi (r2, s2, a, abs) when r1 = r2 && s1 = s2 ->
      let b = asubst_tm abs (Var x) in
      check_tm (add_v x a ctx) env eqns map m b
    | _ -> failwith "check_Lam(%a)" pp_tm m)
  | Let (r, m, abs) ->
    let x, n = unbind_tm abs in
    let abs = bind_tm x (Ann (a, n)) in
    let b, eqns, map = infer_tm ctx env eqns map (Let (r, m, abs)) in
    assert_equal env eqns map a b
  | Cons (c, ms) -> (
    let a = resolve_tm map a in
    match whnf rd_all env a with
    | Data (_, ns) ->
      let ptl = find_c c ctx in
      let ptl =
        List.fold_left
          (fun ptl n ->
            match ptl with
            | PBind (a, abs) -> asubst_ptl abs (Ann (a, n))
            | PBase _ -> ptl)
          ptl ns
      in
      let b, eqns, map = check_ptl ctx env eqns map ms ptl in
      assert_equal env eqns map a b
    | _ ->
      let b, eqns, map = infer_tm ctx env eqns map m in
      assert_equal env eqns map a b)
  | Match (m, mot, cls) -> (
    match mot with
    | Mot0 -> (
      let b, eqns, map = infer_tm ctx env eqns map m in
      let map = unify map eqns in
      let b = resolve_tm map b in
      match whnf rd_all env b with
      | Data (d, ms) ->
        let _, cs = find_d d ctx in
        let cover, eqns, map = coverage ctx env eqns map cls cs ms in
        check_cover cover env eqns map a
      | _ -> failwith "check_Match(%a)" pp_tm m)
    | _ ->
      let b, eqns, map = infer_tm ctx env eqns map (Match (m, mot, cls)) in
      assert_equal env eqns map a b)
  | Fix abs ->
    let x, m = unbind_tm abs in
    check_tm (add_v x a ctx) env eqns map m a
  | _ ->
    let b, eqns, map = infer_tm ctx env eqns map m in
    assert_equal env eqns map a b

and tl_of_ptl ptl ns =
  match (ptl, ns) with
  | PBind (a, abs), n :: ns ->
    let ptl = asubst_ptl abs (Ann (a, n)) in
    tl_of_ptl ptl ns
  | PBase tl, _ -> tl
  | _ -> failwith "tl_of_ptl"

and coverage ctx env eqns map cls cs ms =
  let rec tm_of_p = function
    | PVar x -> Var x
    | PData (d, xs) -> Data (d, List.map var xs)
    | PCons (c, xs) -> Cons (c, List.map var xs)
  and remove_c k ctx = function
    | c :: cs ->
      if C.equal k c then
        (find_c c ctx, cs)
      else
        let a, cs = remove_c k ctx cs in
        (a, c :: cs)
    | _ -> failwith "remove_c(%a)" C.pp k
  and ctx_ptl ctx eqns map a ms xs =
    match (a, ms) with
    | PBind (a, abs), m :: ms ->
      let b = asubst_ptl abs (Ann (a, m)) in
      ctx_ptl ctx eqns map b ms xs
    | PBase a, _ -> ctx_tl ctx eqns map a xs
    | _ -> failwith "ctx_ptl"
  and ctx_tl ctx eqns map a xs =
    match (a, xs) with
    | TBind (_, a, abs), x :: xs ->
      let _, eqns, map = infer_sort ctx env eqns map a in
      let ctx = add_v x a ctx in
      let b = asubst_tl abs (Var x) in
      let ctx, b, eqns, map = ctx_tl ctx eqns map b xs in
      (ctx, b, eqns, map)
    | TBase a, [] -> (ctx, a, eqns, map)
    | _ -> failwith "ctx_tl"
  in
  match cls with
  | cl :: cls -> (
    let p, rhs = unbindp_tm cl in
    match p with
    | PCons (c, xs) ->
      let cns = tm_of_p p in
      let ptl, cs = remove_c c ctx cs in
      let ctx, a, eqns, map = ctx_ptl ctx eqns map ptl ms xs in
      let rhs = resolve_tm map rhs in
      let cover, eqns, map = coverage ctx env eqns map cls cs ms in
      ((ctx, cns, a, rhs) :: cover, eqns, map)
    | _ -> failwith "coverage")
  | [] -> (
    match cs with
    | [] -> ([], eqns, map)
    | _ -> failwith "coverage")

and infer_cover cover env eqns map =
  match cover with
  | (ctx, _, _, rhs) :: cover ->
    let t, eqns, map = infer_tm ctx env eqns map rhs in
    let ts, eqns, map = infer_cover cover env eqns map in
    (t :: ts, eqns, map)
  | _ -> ([], eqns, map)

and check_cover cover env eqns map a =
  match cover with
  | (ctx, _, _, rhs) :: cover ->
    let eqns, map = check_tm ctx env eqns map rhs a in
    check_cover cover env eqns map a
  | _ -> (eqns, map)

and check_mot cover env eqns map mot =
  match (mot, cover) with
  | Mot0, _ -> failwith "check_Mot0"
  | Mot1 abs, (ctx, cns, _, rhs) :: cover ->
    let a = asubst_tm abs cns in
    let eqns, map = check_tm ctx env eqns map rhs a in
    check_mot cover env eqns map mot
  | Mot2 abs, (ctx, _, a, rhs) :: cover ->
    let p, b = unbindp_tm abs in
    let b = substp_tm p b a in
    let eqns, map = check_tm ctx env eqns map rhs b in
    check_mot cover env eqns map mot
  | Mot3 abs, (ctx, cns, a, rhs) :: cover ->
    let x, abs = unbind_ptm abs in
    let p, b = unbindp_tm abs in
    let b = subst_tm x b cns in
    let b = substp_tm p b a in
    let eqns, map = check_tm ctx env eqns map rhs b in
    check_mot cover env eqns map mot
  | _ -> (eqns, map)

let rec infer_dcl ctx env eqns map dcl =
  match dcl with
  | DTm (_, x, a_opt, m) -> (
    match a_opt with
    | Some a ->
      let _, eqns, map = infer_sort ctx env eqns map a in
      let eqns, map = check_tm ctx env eqns map m a in
      let map = unify map eqns in
      let m = resolve_tm map m in
      let a = resolve_tm map a in
      let ctx = add_v x a ctx in
      let env = VMap.add x m env in
      (ctx, env, eqns, map)
    | None ->
      let a, eqns, map = infer_tm ctx env eqns map m in
      let s, eqns, map = infer_sort ctx env eqns map a in
      let map = unify map eqns in
      let m = resolve_tm map m in
      let a = resolve_tm map a in
      let ctx = add_v x a ctx in
      if s = U then
        let env = VMap.add x m env in
        (ctx, env, eqns, map)
      else
        (ctx, env, eqns, map))
  | DData (d, ptl, dconss) ->
    let s, eqns, map = arity_ptl ctx env eqns map ptl in
    let map = unify map eqns in
    let ptl = resolve_ptl map ptl in
    let ctx = add_d d ptl [] ctx in
    let eqns, map, cs, ctx =
      List.fold_right
        (fun (DCons (c, ptl)) (eqns, map, acc, ctx) ->
          let eqns, map = param_ptl ctx env eqns map ptl d [] s in
          let ptl = resolve_ptl map ptl in
          let ctx = add_c c ptl ctx in
          (eqns, map, c :: acc, ctx))
        dconss (eqns, map, [], ctx)
    in
    let map = unify map eqns in
    let ctx = add_d d ptl cs ctx in
    (ctx, env, eqns, map)
  | DAtom (_, x, a) ->
    let _, eqns, map = infer_sort ctx env eqns map a in
    (add_v x a ctx, env, eqns, map)

and infer_dcls ctx env eqns map dcls =
  match dcls with
  | [] -> (eqns, map)
  | dcl :: dcls ->
    let ctx, env, eqns, map = infer_dcl ctx env eqns map dcl in
    infer_dcls ctx env eqns map dcls

and param_ptl ctx env eqns map ptl d xs s =
  match ptl with
  | PBase tl -> param_tl ctx env eqns map tl d (List.rev xs) s
  | PBind (a, abs) ->
    let x, ptl = unbind_ptl abs in
    let _, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    param_ptl ctx env eqns map ptl d (x :: xs) s

and param_tl ctx env eqns map tl d xs s =
  let rec param eqns map xs ms =
    match (xs, ms) with
    | [], _ -> (eqns, map)
    | x :: xs, Var y :: ms ->
      if V.equal x y then
        param eqns map xs ms
      else
        failwith "param(%a, %a)" V.pp x V.pp y
    | _ -> failwith "param"
  in
  match tl with
  | TBase a -> (
    let t, eqns, map = infer_sort ctx env eqns map a in
    match a with
    | Data (d', ms) when s = t ->
      if D.equal d d' then
        param eqns map xs ms
      else
        failwith "param_tl(%a, %a)" D.pp d D.pp d'
    | _ -> failwith "param_tl(%a : %a)" pp_tl tl pp_sort s)
  | TBind (N, a, abs) ->
    let x, tl = unbind_tl abs in
    let _ = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    param_tl ctx env eqns map tl d xs s
  | TBind (R, a, abs) ->
    let x, tl = unbind_tl abs in
    let t, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    if cmp_sort t s then
      param_tl ctx env eqns map tl d xs s
    else
      failwith "param_tl(%a : %a <= %a)" pp_tm a pp_sort t pp_sort s

and arity_ptl ctx env eqns map ptl =
  match ptl with
  | PBase tl -> arity_tl ctx env eqns map tl
  | PBind (a, abs) ->
    let x, ptl = unbind_ptl abs in
    let _, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    arity_ptl ctx env eqns map ptl

and arity_tl ctx env eqns map tl =
  match tl with
  | TBase (Type s) -> (s, eqns, map)
  | TBind (_, a, abs) ->
    let x, tl = unbind_tl abs in
    let _, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    arity_tl ctx env eqns map tl
  | _ -> failwith "arity_tl"

and cmp_sort s1 s2 =
  match (s1, s2) with
  | L, U -> false
  | _ -> true

let elab_dcls dcls =
  let ctx = { vs = VMap.empty; ds = DMap.empty; cs = CMap.empty } in
  let _, map = infer_dcls ctx VMap.empty [] MMap.empty dcls in
  resolve_dcls map dcls
