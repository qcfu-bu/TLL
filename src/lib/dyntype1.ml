open Fmt
open Names
open Syntax1
open Equality1
open Context1

let pp_usage fmt usage =
  let aux fmt usage =
    VMap.iter
      (fun x (s, b) -> pf fmt "%a ?(%a;%b)@;<1 2>" V.pp x pp_srt s b)
      usage
  in
  pf fmt "@[<v 0>{@;<1 2>%a}]" aux usage

let merge usage1 usage2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some (L, false), Some (_, false) -> failwith "merge"
      | Some (_, false), Some (L, false) -> failwith "merge"
      | Some (s1, b1), Some (s2, b2) ->
        if s1 = s2 then
          Some (s1, b1 && b2)
        else
          failwith "merge"
      | Some b, None -> Some b
      | None, Some b -> Some b
      | _ -> None)
    usage1 usage2

let refine_equal usage1 usage2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some (s1, b1), Some (s2, b2) when s1 = s2 -> Some (s1, b1 && b2)
      | Some (_, true), None -> None
      | None, Some (_, true) -> None
      | None, None -> None
      | _ -> failwith "refine_equal")
    usage1 usage2

let assert_empty usage =
  if VMap.for_all (fun _ (_, b) -> b) usage then
    ()
  else
    failwith "assert_empty"

let remove x usage r s =
  match (r, s) with
  | N, _ ->
    if VMap.exists (fun y _ -> V.equal x y) usage then
      failwith "remove(%a)" V.pp x
    else
      usage
  | R, U -> VMap.remove x usage
  | R, L ->
    if VMap.exists (fun y _ -> V.equal x y) usage then
      VMap.remove x usage
    else
      failwith "remove(%a)" V.pp x

let trans_sort = function
  | U -> Syntax2.U
  | L -> Syntax2.L

let rec infer_tm ctx env m =
  match m with
  | Ann (a, m) -> (
    let _ = Statype1.infer_sort ctx env a in
    match m with
    | Let (r, m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let m_elab, usage = check_tm ctx env (Let (r, m, abs)) a in
      (a, m_elab, usage)
    | _ ->
      let m_elab, usage = check_tm ctx env m a in
      (a, m_elab, usage))
  | Var x ->
    let s, a = find_v x ctx in
    Syntax2.(a, Var x, VMap.singleton x (s, false))
  | App (m, n) -> (
    let a, m_elab, usage1 = infer_tm ctx env m in
    match whnf rd_all env a with
    | Pi (N, s, a, abs) ->
      let _ = Statype1.check_tm ctx env n a in
      ( asubst_tm abs (Ann (a, n))
      , Syntax2.(App (trans_sort s, m_elab, Box))
      , usage1 )
    | Pi (R, s, a, abs) ->
      let n_elab, usage2 = check_tm ctx env n a in
      ( asubst_tm abs (Ann (a, n))
      , Syntax2.(App (trans_sort s, m_elab, n_elab))
      , merge usage1 usage2 )
    | _ -> failwith "infer_App(%a)" pp_tm m)
  | Let (N, m, abs) ->
    let a = Statype1.infer_tm ctx env m in
    let s = Statype1.infer_sort ctx env a in
    let x, n = unbind_tm abs in
    let ctx = add_v x s a ctx in
    let env = VMap.add x m env in
    let b, n_elab, usage = infer_tm ctx env n in
    let usage = remove x usage N s in
    (b, Syntax2.(Let (Box, bind_tm x n_elab)), usage)
  | Let (R, m, abs) ->
    let a, m_elab, usage1 = infer_tm ctx env m in
    let s = Statype1.infer_sort ctx env a in
    let x, n = unbind_tm abs in
    let ctx = add_v x s a ctx in
    let env = VMap.add x m env in
    let b, n_elab, usage2 = infer_tm ctx env n in
    let usage = merge usage1 (remove x usage2 R s) in
    (b, Syntax2.(Let (m_elab, bind_tm x n_elab)), usage)
  | Cons (c, ms) ->
    let ptl = find_c c ctx in
    let a, ms_elab, usage = check_ptl ctx env ms ptl in
    (a, Syntax2.(Cons (c, ms_elab)), usage)
  | _ -> failwith "TODO"

and check_tm ctx env m a = failwith "TODO"
and check_ptl ctx env ms ptl = failwith "TODO"
