open Fmt
open Names
open Syntax1
open Equality1
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

let has_failed f =
  try
    let _ = f () in
    false
  with
  | _ -> true

let rec infer_sort ctx env eqns map a =
  let srt, eqns, map = infer_tm ctx env eqns map a in
  let srt = resolve_tm map srt in
  match whnf rd_all env srt with
  | Type s -> (s, eqns, map)
  | _ -> failwith "infer_sort(%a : %a)" pp_tm a pp_tm srt

and infer_tm ctx env eqns map = function
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
    let s, eqns, map = infer_sort ctx env eqns map a in
    let map = unify map eqns in
    let m = resolve_tm map m in
    let a = resolve_tm map a in
    let x, n = unbind_tm abs in
    let ctx = add_v x a ctx in
    let env =
      match s with
      | U -> VMap.add x m env
      | L -> env
    in
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
    match whnf rd_all env a with
    | Data (d, ms) -> (
      let _, cs = find_d d ctx in
      let cover, eqns, map = coverage ctx env eqns map cls cs ms in
      match mot with
      | Mot0 ->
        let ms, eqns, map = infer_cover cover ctx env eqns map in
        let eqns = List.fold_left (fun acc n -> (env, m, n) :: acc) eqns ms in
        (m, eqns, map)
      | Mot1 abs ->
        let a = asubst_tm abs m in
        let eqns, map = check_mot cover ctx env eqns map mot in
        (a, eqns, map)
      | Mot2 abs ->
        let p, a = unbindp_tm abs in
        let a = substp_tm p a m in
        let eqns, map = check_mot cover ctx env eqns map mot in
        (a, eqns, map)
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
  | m :: ms, PBind (_, a, abs) ->
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
  match m with
  | Meta (x, _) -> (eqns, add_m x a map)
  | Lam abs -> (
    let x, m = unbind_tm abs in
    let a = resolve_tm map a in
    match whnf rd_all env a with
    | Pi (_, _, a, abs) ->
      let b = asubst_tm abs (Var x) in
      let _, eqns, map = infer_sort ctx env eqns map a in
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
            | PBind (_, a, abs) -> asubst_ptl abs (Ann (a, n))
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
        check_cover cover ctx env eqns map a
      | _ -> failwith "check_Match(%a)" pp_tm m)
    | _ ->
      let b, eqns, map = infer_tm ctx env eqns map (Match (m, mot, cls)) in
      assert_equal env eqns map a b)
  | _ ->
    let b, eqns, map = infer_tm ctx env eqns map m in
    assert_equal env eqns map a b

and tl_of_ptl ptl ns =
  match (ptl, ns) with
  | PBind (_, a, abs), n :: ns ->
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
    | _ -> failwith "remove_c(%a)" C.pp c
  in
  __

let rec infer_dcl ctx env eqns map dcl =
  match dcl with
  | DTm (_, x, a_opt, m) -> (
    match a_opt with
    | Some a ->
      let s, eqns, map = infer_sort ctx env eqns map a in
      let eqns, map = check_tm ctx env eqns map m a in
      let map = UMeta.unify map eqns in
      let m = UMeta.resolve_tm map m in
      let a = UMeta.resolve_tm map a in
      let ctx = add_v x a ctx in
      if s = U then
        let env = VMap.add x m env in
        (ctx, env, eqns, map)
      else
        (ctx, env, eqns, map)
    | None ->
      let a, eqns, map = infer_tm ctx env eqns map m in
      let s, eqns, map = infer_sort ctx env eqns map a in
      let map = UMeta.unify map eqns in
      let m = UMeta.resolve_tm map m in
      let a = UMeta.resolve_tm map a in
      let ctx = add_v x a ctx in
      if s = U then
        let env = VMap.add x m env in
        (ctx, env, eqns, map)
      else
        (ctx, env, eqns, map))
  | DFun (_, x, a, abs) ->
    let s, eqns, map = infer_sort ctx env eqns map a in
    let y, cls = unbind_cls abs in
    if s = U then
      let local_ctx = add_v y a ctx in
      let prbm = UVar.prbm_of_cls cls in
      let eqns, map = check_prbm local_ctx env eqns map prbm a in
      let map = UMeta.unify map eqns in
      let abs = UMeta.resolve_cls_abs map abs in
      let a = UMeta.resolve_tm map a in
      let ctx = add_v x a ctx in
      let env = VMap.add x (Fun (Some a, abs)) env in
      (ctx, env, eqns, map)
    else
      let prbm = UVar.prbm_of_cls cls in
      let eqns, map = check_prbm ctx env eqns map prbm a in
      let map = UMeta.unify map eqns in
      let a = UMeta.resolve_tm map a in
      let ctx = add_v x a ctx in
      (ctx, env, eqns, map)
  | DData (d, ptl, dconss) ->
    let eqns, map = infer_ptl ctx env eqns map ptl U in
    let map = UMeta.unify map eqns in
    let ptl = UMeta.resolve_ptl map ptl in
    let ctx = add_d d ptl [] ctx in
    let eqns, map, cs, ctx =
      List.fold_right
        (fun (DCons (c, ptl)) (eqns, map, acc, ctx) ->
          let eqns, map = infer_ptl ctx env eqns map ptl U in
          let _ = param_ptl ptl d [] in
          let ptl = UMeta.resolve_ptl map ptl in
          let ctx = add_c c ptl ctx in
          (eqns, map, c :: acc, ctx))
        dconss (eqns, map, [], ctx)
    in
    let map = UMeta.unify map eqns in
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

and param_ptl ptl d xs =
  match ptl with
  | PBase a -> param_tl a d (List.rev xs)
  | PBind (_, _, abs) ->
    let x, ptl = unbind_ptl abs in
    param_ptl ptl d (x :: xs)

and param_tl tl d xs =
  let rec param xs ms =
    match (xs, ms) with
    | [], _ -> ()
    | x :: xs, Var y :: ms ->
      if V.equal x y then
        param xs ms
      else
        failwith "param(%a, %a)" V.pp x V.pp y
    | _ -> failwith "param"
  in
  match tl with
  | TBase b -> (
    match b with
    | Data (d', ms) ->
      if D.equal d d' then
        param xs ms
      else
        failwith "param_tl(%a, %a)" D.pp d D.pp d'
    | _ -> failwith "param_tl")
  | TBind (_, _, abs) ->
    let _, tl = unbind_tl abs in
    param_tl tl d xs

and infer_tl ctx env eqns map tl s =
  match tl with
  | TBase a ->
    let t, eqns, map = infer_sort ctx env eqns map a in
    if cmp_sort t s then
      (eqns, map)
    else
      failwith "infer_tl"
  | TBind (_, a, abs) ->
    let x, tl = unbind_tl abs in
    let t, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    infer_tl ctx env eqns map tl (min_sort s t)

and infer_ptl ctx env eqns map ptl s =
  match ptl with
  | PBase tl -> infer_tl ctx env eqns map tl s
  | PBind (_, a, abs) ->
    let x, ptl = unbind_ptl abs in
    let t, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    infer_ptl ctx env eqns map ptl (min_sort s t)

and min_sort s1 s2 =
  match s1 with
  | U -> s2
  | L -> s1

and cmp_sort s1 s2 =
  match (s1, s2) with
  | U, L -> false
  | _ -> true

let elab_dcls dcls =
  let ctx = { vs = VMap.empty; ds = DMap.empty; cs = CMap.empty } in
  let _, map = infer_dcls ctx VMap.empty [] MMap.empty dcls in
  UMeta.resolve_dcls map dcls
