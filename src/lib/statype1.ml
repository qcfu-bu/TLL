open Fmt
open Names
open Syntax1
open Pprint1
open Equality1
open Unify1

type ctx =
  { vs : (rel * srt * tm) VMap.t
  ; ds : (ptl * C.t list) DMap.t
  ; cs : ptl CMap.t
  }

let add_v x r s a ctx = { ctx with vs = VMap.add x (r, s, a) ctx.vs }
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
    VMap.iter
      (fun x (r, s, a) ->
        pf fmt "@[%a :(%a;%a)@;<1 2>%a@]@;<1 2>" V.pp x pp_rel r pp_srt s pp_tm
          a)
      vs
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

let pp_ctx fmt ctx =
  pf fmt "@[<v 0>ctx{@;<1 2>%a@;<1 2>%a@;<1 2>%a}@]" pp_vs ctx.vs pp_ds ctx.ds
    pp_cs ctx.cs

let assert_equal env m n =
  if equal rd_all env m n then
    ()
  else
    failwith "@[assert_equal(@;<1 2>%a@;<1 2>!=@;<1 2>%a)@]" pp_tm m pp_tm n

let has_failed f =
  try
    let _ = f () in
    false
  with
  | _ -> true

let rec infer_sort ctx env a =
  let srt = infer_tm ctx env a in
  match whnf rd_all env srt with
  | Type s -> s
  | _ -> failwith "infer_sort(%a : %a)" pp_tm a pp_tm srt

and infer_tm ctx env = function
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
  | Meta _ as m -> failwith "infer_tm_Meta(%a)" pp_tm m
  | Type _ -> Type U
  | Var x ->
    let _, _, a = find_v x ctx in
    a
  | Pi (r, s, a, abs) ->
    let x, b = unbind_tm abs in
    let t = infer_sort ctx env a in
    let ctx = add_v x r t a ctx in
    let _ = infer_sort ctx env b in
    Type s
  | Lam _ as m -> failwith "infer_Lam(%a)" pp_tm m
  | App (m, n) -> (
    let a = infer_tm ctx env m in
    match whnf rd_all env a with
    | Pi (_, _, a, abs) ->
      let _ = check_tm ctx env n a in
      asubst_tm abs (Ann (a, n))
    | _ -> failwith "infer_App(%a)" pp_tm m)
  | Let (r, m, abs) ->
    let a = infer_tm ctx env m in
    let t = infer_sort ctx env a in
    let x, n = unbind_tm abs in
    let ctx = add_v x r t a ctx in
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
        let ms = infer_cover cover env in
        match ms with
        | [] -> failwith "infer_Mot0"
        | m :: ms ->
          List.fold_left
            (fun acc n ->
              if equal rd_all env m n then
                acc
              else
                failwith "infer_Mot0")
            m ms)
      | Mot1 abs ->
        let a = asubst_tm abs m in
        let _ = check_mot cover env mot in
        a
      | Mot2 abs ->
        let p, a = unbindp_tm abs in
        let a = substp_tm p a m in
        let _ = check_mot cover env mot in
        a
      | Mot3 abs ->
        let x, abs = unbind_ptm abs in
        let p, b = unbindp_tm abs in
        let b = subst_tm x b m in
        let b = substp_tm p b a in
        b)
    | _ -> failwith "infer_Match(%a)" pp_tm m)
  | Fix abs as m -> (
    let _, n = unbind_tm abs in
    match n with
    | Ann (a, _) ->
      let _ = infer_sort ctx env a in
      let _ = check_tm ctx env m a in
      a
    | _ -> failwith "infer_Fix(%a)" pp_tm m)

and check_ptl ctx env ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (_, a, abs) ->
    let _ = infer_sort ctx env a in
    let _ = check_tm ctx env m a in
    check_ptl ctx env ms (asubst_ptl abs (Ann (a, m)))
  | ms, PBase tl -> check_tl ctx env ms tl
  | _ -> failwith "check_ptl(%a, %a)" pp_tms ms pp_ptl ptl

and check_tl ctx env ms tl =
  match (ms, tl) with
  | m :: ms, TBind (_, a, abs) ->
    let _ = infer_sort ctx env a in
    let _ = check_tm ctx env m a in
    check_tl ctx env ms (asubst_tl abs (Ann (a, m)))
  | [], TBase a ->
    let _ = infer_sort ctx env a in
    a
  | _ -> failwith "check_tl(%a, %a)" pp_tms ms pp_tl tl

and check_tm ctx env m a =
  match m with
  | Lam abs -> (
    let x, m = unbind_tm abs in
    match whnf rd_all env a with
    | Pi (r, s, a, abs) ->
      let b = asubst_tm abs (Var x) in
      check_tm (add_v x r s a ctx) env m b
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
            | PBind (_, a, abs) -> asubst_ptl abs (Ann (a, n))
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
  | _ ->
    let b = infer_tm ctx env m in
    assert_equal env a b

and tl_of_ptl ptl ns =
  match (ptl, ns) with
  | PBind (_, a, abs), n :: ns ->
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
  in
  let rec arity_ptl ctx a ms xs =
    match (a, ms) with
    | PBind (_, a, abs), m :: ms ->
      let b = asubst_ptl abs (Ann (m, a)) in
      arity_ptl ctx b ms xs
    | PBase a, _ -> arity_tl ctx a xs
    | _ -> failwith "arity_ptl"
  and arity_tl ctx a xs =
    match (a, xs) with
    | TBind (r, a, abs), x :: xs ->
      let s = infer_sort ctx env a in
      let ctx = add_v x r s a ctx in
      let b = asubst_tl abs (Var x) in
      let ctx, b, ss = arity_tl ctx b xs in
      (ctx, b, (x, s) :: ss)
    | TBase a, [] -> (ctx, a, [])
    | _ -> failwith "arity_tl"
  in
  match cls with
  | cl :: cls -> (
    let p, m = unbindp_tm cl in
    match p with
    | PCons (c, xs) ->
      let cns = tm_of_p p in
      let ptl, cs = remove_c c ctx cs in
      let ctx, a, ss = arity_ptl ctx ptl ms xs in
      let cs = coverage ctx env cls cs ms in
      (ctx, cns, a, m, ss) :: cs
    | _ -> failwith "coverage")
  | [] -> (
    match cs with
    | [] -> []
    | _ -> failwith "coverage")
