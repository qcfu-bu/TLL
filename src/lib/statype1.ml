open Fmt
open Names
open Syntax1
open Context1
open Equality1
open Pprint1

let assert_equal env m n =
  if equal rd_all env m n then
    ()
  else
    failwith "@[assert_equal(@;<1 2>%a@;<1 2>!=@;<1 2>%a)@]" pp_tm m pp_tm n

let rec infer_sort ctx env a =
  let srt = infer_tm ctx env a in
  match whnf rd_all env srt with
  | Type s -> s
  | _ -> failwith "infer_sort(%a : %a)" pp_tm a pp_tm srt

and infer_tm ctx env m =
  match m with
  | Ann (a, m) -> (
    match m with
    | Let (r, m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let _ = check_tm ctx env (Let (r, m, abs)) a in
      a
    | _ ->
      let _ = check_tm ctx env m a in
      a)
  | Meta _ -> failwith "infer_tm_Meta(%a)" pp_tm m
  | Type _ -> Type U
  | Var x ->
    let _, a = find_v x ctx in
    a
  | Pi (_, s, a, abs) ->
    let x, b = unbind_tm abs in
    let t = infer_sort ctx env a in
    let ctx = add_v x t a ctx in
    let _ = infer_sort ctx env b in
    Type s
  | Lam _ -> failwith "infer_tm_Lam(%a)" pp_tm m
  | App (m, n) -> (
    let a = infer_tm ctx env m in
    match whnf rd_all env a with
    | Pi (_, _, a, abs) ->
      let _ = check_tm ctx env n a in
      asubst_tm abs (Ann (a, n))
    | _ -> failwith "infer_tm_App(%a)" pp_tm m)
  | Let (_, m, abs) ->
    let a = infer_tm ctx env m in
    let s = infer_sort ctx env a in
    let x, n = unbind_tm abs in
    let ctx = add_v x s a ctx in
    let env = VMap.add x m env in
    infer_tm ctx env n
  | Data (d, ms) ->
    let ptl, _ = find_d d ctx in
    check_ptl ctx env ms ptl
  | Cons (c, ms) ->
    let ptl = find_c c ctx in
    check_ptl ctx env ms ptl
  | Match (m, mot, cls) -> (
    let a = infer_tm ctx env m in
    match whnf rd_all env a with
    | Data (d, ms) -> (
      let _, cs = find_d d ctx in
      let cover = coverage ctx env cls cs ms in
      match mot with
      | Mot0 -> (
        let ts = infer_cover cover env in
        match ts with
        | [] -> failwith "infer_Mot0"
        | t0 :: ts ->
          List.fold_left
            (fun acc t ->
              if equal rd_all env t0 t then
                acc
              else
                failwith "infer_Mot0")
            t0 ts)
      | Mot1 abs ->
        let b = asubst_tm abs m in
        let _ = check_mot cover env mot in
        b
      | Mot2 abs ->
        let p, b = unbindp_tm abs in
        let b = substp_tm p b a in
        let _ = check_mot cover env mot in
        b
      | Mot3 abs ->
        let x, abs = unbind_ptm abs in
        let p, b = unbindp_tm abs in
        let b = subst_tm x b m in
        let b = substp_tm p b a in
        b)
    | _ -> failwith "infer_Match(%a)" pp_tm m)
  | Fix abs -> (
    let _, n = unbind_tm abs in
    match n with
    | Ann (a, _) ->
      let _ = infer_sort ctx env a in
      let _ = check_tm ctx env m a in
      a
    | _ -> failwith "infer_Fix(%a)" pp_tm m)

and check_ptl ctx env ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (a, abs) ->
    let _ = infer_sort ctx env a in
    let _ = check_tm ctx env m a in
    check_ptl ctx env ms (asubst_ptl abs (Ann (a, m)))
  | ms, PBase tl -> check_tl ctx env ms tl
  | _ -> failwith "check_Ptl(%a, %a)" pp_tms ms pp_ptl ptl

and check_tl ctx env ms tl =
  match (ms, tl) with
  | m :: ms, TBind (_, a, abs) ->
    let _ = infer_sort ctx env a in
    let _ = check_tm ctx env m a in
    check_tl ctx env ms (asubst_tl abs (Ann (a, m)))
  | [], TBase a ->
    let _ = infer_sort ctx env a in
    a
  | _ -> failwith "check_Tl(%a, %a)" pp_tms ms pp_tl tl

and check_tm ctx env m a =
  match m with
  | Meta (x, _) -> failwith "check_Meta(%a)" M.pp x
  | Lam (r1, s1, abs) -> (
    let x, m = unbind_tm abs in
    match whnf rd_all env a with
    | Pi (r2, s2, a, abs) when r1 = r2 && s1 = s2 ->
      let b = asubst_tm abs (Var x) in
      let t = infer_sort ctx env a in
      check_tm (add_v x t a ctx) env m b
    | _ -> failwith "check_Lam(%a)" pp_tm m)
  | Let (r, m, abs) ->
    let x, n = unbind_tm abs in
    let abs = bind_tm x (Ann (a, n)) in
    let b = infer_tm ctx env (Let (r, m, abs)) in
    assert_equal env a b
  | Cons (c, ms) -> (
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
      let b = check_ptl ctx env ms ptl in
      assert_equal env a b
    | _ ->
      let b = infer_tm ctx env m in
      assert_equal env a b)
  | Match (m, mot, cls) -> (
    match mot with
    | Mot0 -> (
      let b = infer_tm ctx env m in
      match whnf rd_all env b with
      | Data (d, ms) ->
        let _, cs = find_d d ctx in
        let cover = coverage ctx env cls cs ms in
        check_cover cover env a
      | _ -> failwith "check_Match(%a)" pp_tm m)
    | _ ->
      let b = infer_tm ctx env (Match (m, mot, cls)) in
      assert_equal env a b)
  | Fix abs ->
    let x, m = unbind_tm abs in
    let s = infer_sort ctx env a in
    check_tm (add_v x s a ctx) env m a
  | _ ->
    let b = infer_tm ctx env m in
    assert_equal env a b

and tl_of_ptl ptl ns =
  match (ptl, ns) with
  | PBind (a, abs), n :: ns ->
    let ptl = asubst_ptl abs (Ann (a, n)) in
    tl_of_ptl ptl ns
  | PBase tl, _ -> tl
  | _ -> failwith "tl_of_ptl"

and coverage ctx env cls cs ms =
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
  and ctx_ptl ctx a ms xs =
    match (a, ms) with
    | PBind (a, abs), m :: ms ->
      let b = asubst_ptl abs (Ann (a, m)) in
      ctx_ptl ctx b ms xs
    | PBase a, _ -> ctx_tl ctx a xs
    | _ -> failwith "ctx_ptl"
  and ctx_tl ctx a xs =
    match (a, xs) with
    | TBind (_, a, abs), x :: xs ->
      let s = infer_sort ctx env a in
      let ctx = add_v x s a ctx in
      let tl = asubst_tl abs (Var x) in
      let ctx, b = ctx_tl ctx tl xs in
      (ctx, b)
    | TBase a, [] -> (ctx, a)
    | _ -> failwith "ctx_tl"
  in
  match cls with
  | cl :: cls -> (
    let p, rhs = unbindp_tm cl in
    match p with
    | PCons (c, xs) ->
      let cns = tm_of_p p in
      let ptl, cs = remove_c c ctx cs in
      let ctx, a = ctx_ptl ctx ptl ms xs in
      let cover = coverage ctx env cls cs ms in
      (ctx, cns, a, rhs) :: cover
    | _ -> failwith "coverage")
  | [] -> (
    match cs with
    | [] -> []
    | _ -> failwith "coverage")

and infer_cover cover env =
  match cover with
  | (ctx, _, _, rhs) :: cover ->
    let t = infer_tm ctx env rhs in
    let ts = infer_cover cover env in
    t :: ts
  | _ -> []

and check_cover cover env a =
  match cover with
  | (ctx, _, _, rhs) :: cover ->
    let _ = check_tm ctx env rhs a in
    check_cover cover env a
  | _ -> ()

and check_mot cover env mot =
  match (mot, cover) with
  | Mot0, _ -> failwith "check_Mot0"
  | Mot1 abs, (ctx, cns, _, rhs) :: cover ->
    let b = asubst_tm abs cns in
    let _ = check_tm ctx env rhs b in
    check_mot cover env mot
  | Mot2 abs, (ctx, _, a, rhs) :: cover ->
    let p, b = unbindp_tm abs in
    let b = substp_tm p b a in
    let _ = check_tm ctx env rhs b in
    check_mot cover env mot
  | Mot3 abs, (ctx, cns, a, rhs) :: cover ->
    let x, abs = unbind_ptm abs in
    let p, b = unbindp_tm abs in
    let b = subst_tm x b cns in
    let b = substp_tm p b a in
    let _ = check_tm ctx env rhs b in
    check_mot cover env mot
  | _ -> ()

let rec param_ptl ctx env ptl d xs s =
  match ptl with
  | PBase tl -> param_tl ctx env tl d (List.rev xs) s
  | PBind (a, abs) ->
    let x, ptl = unbind_ptl abs in
    let t = infer_sort ctx env a in
    let ctx = add_v x t a ctx in
    param_ptl ctx env ptl d (x :: xs) s

and param_tl ctx env tl d xs s =
  let rec param xs ms sz =
    match (xs, ms) with
    | [], _ -> sz
    | x :: xs, Var y :: ms ->
      if V.equal x y then
        param xs ms sz
      else
        failwith "param(%a, %a)" V.pp x V.pp y
    | _ -> failwith "param"
  in
  match tl with
  | TBase a -> (
    let t = infer_sort ctx env a in
    match a with
    | Data (d', ms) when s = t ->
      if D.equal d d' then
        param xs ms 0
      else
        failwith "param_tl(%a, %a)" D.pp d D.pp d'
    | _ -> failwith "param_tl(%a : %a)" pp_tl tl pp_sort s)
  | TBind (N, a, abs) ->
    let x, tl = unbind_tl abs in
    let t = infer_sort ctx env a in
    let ctx = add_v x t a ctx in
    1 + param_tl ctx env tl d xs s
  | TBind (R, a, abs) ->
    let x, tl = unbind_tl abs in
    let t = infer_sort ctx env a in
    let ctx = add_v x t a ctx in
    if cmp_sort t s then
      1 + param_tl ctx env tl d xs s
    else
      failwith "param_tl(%a : %a <= %a)" pp_tl tl pp_sort t pp_sort s

and arity_ptl ctx env ptl =
  match ptl with
  | PBase tl -> arity_tl ctx env tl
  | PBind (a, abs) ->
    let x, ptl = unbind_ptl abs in
    let t = infer_sort ctx env a in
    let ctx = add_v x t a ctx in
    arity_ptl ctx env ptl

and arity_tl ctx env tl =
  match tl with
  | TBase (Type s) -> s
  | TBind (_, a, abs) ->
    let x, tl = unbind_tl abs in
    let t = infer_sort ctx env a in
    let ctx = add_v x t a ctx in
    arity_tl ctx env tl
  | _ -> failwith "arity_tl"

and cmp_sort s1 s2 =
  match (s1, s2) with
  | L, U -> false
  | _ -> true
