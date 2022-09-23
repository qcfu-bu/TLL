open Fmt
open Names
open Syntax1
open Equality1

type ctx =
  { vs : (rel * srt * tm) VMap.t
  ; ds : (ptl * C.t list) DMap.t
  ; cs : ptl CMap.t
  }

let add_v x r s a ctx = { ctx with vs = VMap.add x (r, s, a) ctx.vs }
let add_d d ptl cs ctx = { ctx with ds = DMap.add d (ptl, cs) ctx.ds }
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

let pp_ctx fmt ctx = pf fmt "@[<v 0>ctx{@;<1 2>%a}@]" pp_vs ctx.vs

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
  | Lam _ as m -> failwith "infer_tm_Lam(%a)" pp_tm m
  | App (m, n) -> (
    let a = infer_tm ctx env m in
    match whnf rd_all env a with
    | Pi (_, _, a, abs) ->
      let _ = check_tm ctx env n a in
      asubst_tm abs (Ann (a, n))
    | _ -> failwith "infer_tm_App(%a)" pp_tm m)
  | Let (r, m, abs) ->
    let a = infer_tm ctx env m in
    let s = infer_sort ctx env a in
    let x, n = unbind_tm abs in
    let ctx = add_v x r s a ctx in
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
      | Mot0 -> failwith "TODO"
      | Mot1 abs -> failwith "TODO"
      | Mot2 abs -> failwith "TODO"
      | Mot3 abs -> failwith "TODO")
    | _ -> failwith "infer_Match(%a)" pp_tm m)
  | Fix abs as m -> (
    let _, n = unbind_tm abs in
    match n with
    | Ann (a, _) ->
      let _ = infer_sort ctx env a in
      let _ = check_tm ctx env m a in
      a
    | _ -> failwith "infer_Fix(%a)" pp_tm m)

and check_tm ctx env m a = failwith "TODO"
and check_ptl ctx env ms ptl = failwith "TODO"
