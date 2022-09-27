open Fmt
open Names
open Syntax1
open Equality1
open Context1

let pp_usage fmt usage =
  let aux fmt usage =
    VMap.iter
      (fun x (s, b) -> pf fmt "%a ?(%a;%b)@;<1 2>" V.pp x pp_sort s b)
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
      | Some (U, false), None -> Some (U, false)
      | None, Some (U, false) -> Some (U, false)
      | Some (s1, b1), Some (s2, b2) when s1 = s2 -> Some (s1, b1 && b2)
      | Some (_, true), None -> None
      | None, Some (_, true) -> None
      | None, None -> None
      | _ -> failwith "refine_equal")
    usage1 usage2

let assert_pure usage =
  if VMap.for_all (fun _ (s, b) -> s = U || b) usage then
    ()
  else
    failwith "assert_pure"

let assert_empty usage =
  if VMap.for_all (fun _ (_, b) -> b) usage then
    ()
  else
    failwith "assert_empty"

let remove x usage r s =
  match (r, s) with
  | N, _ ->
    if VMap.exists (fun y (_, b) -> V.equal x y && not b) usage then
      failwith "remove(%a)" V.pp x
    else
      VMap.remove x usage
  | R, U -> VMap.remove x usage
  | R, L ->
    if VMap.exists (fun y _ -> V.equal x y) usage then
      VMap.remove x usage
    else
      failwith "remove(%a)" V.pp x

let usage_of_ctx ctx = VMap.map (fun (s, _) -> (s, true)) ctx.vs

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
  | Match (m, mot, cls) -> (
    let a, m_elab, usage1 = infer_tm ctx env m in
    let s = Statype1.infer_sort ctx env a in
    match whnf rd_all env a with
    | Data (d, ms) -> (
      let _, cs = find_d d ctx in
      let cover = coverage ctx env cls cs ms in
      match mot with
      | Mot0 -> (
        let cls_elab, usages = infer_cover cover env in
        match usages with
        | [] -> failwith "infer_Mot0"
        | (t0, usage0) :: usages ->
          let usage2 =
            List.fold_left
              (fun usage0 (t, usage) ->
                if equal rd_all env t0 t then
                  refine_equal usage0 usage
                else
                  failwith "infer_Mot0")
              usage0 usages
          in
          let usage = merge usage1 usage2 in
          (t0, Syntax2.(Match (trans_sort s, m_elab, cls_elab)), usage))
      | Mot1 abs -> (
        let b = asubst_tm abs m in
        let cls_elab, usages = check_mot cover env mot in
        match usages with
        | [] ->
          let usage2 = usage_of_ctx ctx in
          let usage = merge usage1 usage2 in
          (b, Syntax2.(Match (trans_sort s, m_elab, cls_elab)), usage)
        | usage0 :: usages ->
          let usage2 =
            List.fold_left
              (fun usage0 usage -> refine_equal usage0 usage)
              usage0 usages
          in
          let usage = merge usage1 usage2 in
          (b, Syntax2.(Match (trans_sort s, m_elab, cls_elab)), usage))
      | Mot2 abs -> (
        let p, b = unbindp_tm abs in
        let b = substp_tm p b a in
        let cls_elab, usages = check_mot cover env mot in
        match usages with
        | [] ->
          let usage2 = usage_of_ctx ctx in
          let usage = merge usage1 usage2 in
          (b, Syntax2.(Match (trans_sort s, m_elab, cls_elab)), usage)
        | usage0 :: usages ->
          let usage2 =
            List.fold_left
              (fun usage0 usage -> refine_equal usage0 usage)
              usage0 usages
          in
          let usage = merge usage1 usage2 in
          (b, Syntax2.(Match (trans_sort s, m_elab, cls_elab)), usage))
      | Mot3 abs -> (
        let x, abs = unbind_ptm abs in
        let p, b = unbindp_tm abs in
        let b = subst_tm x b m in
        let b = substp_tm p b a in
        let cls_elab, usages = check_mot cover env mot in
        match usages with
        | [] ->
          let usage2 = usage_of_ctx ctx in
          let usage = merge usage1 usage2 in
          (b, Syntax2.(Match (trans_sort s, m_elab, cls_elab)), usage)
        | usage0 :: usages ->
          let usage2 =
            List.fold_left
              (fun usage0 usage -> refine_equal usage0 usage)
              usage0 usages
          in
          let usage = merge usage1 usage2 in
          (b, Syntax2.(Match (trans_sort s, m_elab, cls_elab)), usage)))
    | _ -> failwith "infer_Match(%a)" pp_tm m)
  | Fix abs -> (
    let _, n = unbind_tm abs in
    match n with
    | Ann (a, _) ->
      let _ = Statype1.infer_sort ctx env a in
      let m_elab, usage = check_tm ctx env m a in
      (a, m_elab, usage)
    | _ -> failwith "infer_Fix(%a)" pp_tm m)
  | _ -> failwith "infer_tm(%a)" pp_tm m

and check_ptl ctx env ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (a, abs) ->
    let _ = Statype1.infer_sort ctx env a in
    let _ = Statype1.check_tm ctx env m a in
    let a, ms_elab, usage =
      check_ptl ctx env ms (asubst_ptl abs (Ann (a, m)))
    in
    (a, Syntax2.(Box :: ms_elab), usage)
  | ms, PBase tl -> check_tl ctx env ms tl
  | _ -> failwith "check_Ptl(%a, %a)" pp_tms ms pp_ptl ptl

and check_tl ctx env ms tl =
  match (ms, tl) with
  | m :: ms, TBind (N, a, abs) ->
    let _ = Statype1.infer_sort ctx env a in
    let _ = Statype1.check_tm ctx env m a in
    let a, ms_elab, usage = check_tl ctx env ms (asubst_tl abs (Ann (a, m))) in
    (a, Syntax2.(Box :: ms_elab), usage)
  | m :: ms, TBind (R, a, abs) ->
    let _ = Statype1.infer_sort ctx env a in
    let m_elab, usage1 = check_tm ctx env m a in
    let a, ms_elab, usage2 = check_tl ctx env ms (asubst_tl abs (Ann (a, m))) in
    (a, m_elab :: ms_elab, merge usage1 usage2)
  | [], TBase a ->
    let _ = Statype1.infer_sort ctx env a in
    (a, [], VMap.empty)
  | _ -> failwith "check_Tl(%a, %a)" pp_tms ms pp_tl tl

and check_tm ctx env m a =
  match m with
  | Lam (r1, s1, abs) -> (
    let x, m = unbind_tm abs in
    match whnf rd_all env a with
    | Pi (r2, s2, a, abs) when r1 = r2 && s1 = s2 -> (
      let b = asubst_tm abs (Var x) in
      let t = Statype1.infer_sort ctx env a in
      let m_elab, usage = check_tm (add_v x t a ctx) env m b in
      let usage = remove x usage r1 s1 in
      match s1 with
      | U ->
        let _ = assert_pure usage in
        (Syntax2.(Lam (trans_sort s1, bind_tm x m_elab)), usage)
      | L -> (Syntax2.(Lam (trans_sort s1, bind_tm x m_elab)), usage))
    | _ -> failwith "check_Lam(%a)" pp_tm m)
  | Let (r, m, abs) ->
    let x, n = unbind_tm abs in
    let abs = bind_tm x (Ann (a, n)) in
    let b, m_elab, usage = infer_tm ctx env (Let (r, m, abs)) in
    let _ = Statype1.assert_equal env a b in
    (m_elab, usage)
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
      let b, ms_elab, usage = check_ptl ctx env ms ptl in
      let _ = Statype1.assert_equal env a b in
      (Syntax2.(Cons (c, ms_elab)), usage)
    | _ ->
      let b, m_elab, usage = infer_tm ctx env m in
      let _ = Statype1.assert_equal env a b in
      (m_elab, usage))
  | Match (m, mot, cls) -> (
    match mot with
    | Mot0 -> (
      let b, m_elab, usage1 = infer_tm ctx env m in
      let s = Statype1.infer_sort ctx env b in
      match whnf rd_all env b with
      | Data (d, ms) -> (
        let _, cs = find_d d ctx in
        let cover = coverage ctx env cls cs ms in
        let cls_elab, usages = check_cover cover env a in
        match usages with
        | [] ->
          let usage2 = usage_of_ctx ctx in
          let usage = merge usage1 usage2 in
          (Syntax2.(Match (trans_sort s, m_elab, cls_elab)), usage)
        | usage0 :: usages ->
          let usage2 =
            List.fold_left
              (fun usage0 usage -> refine_equal usage0 usage)
              usage0 usages
          in
          let usage = merge usage1 usage2 in
          (Syntax2.(Match (trans_sort s, m_elab, cls_elab)), usage))
      | _ -> failwith "check_Match(%a)" pp_tm m)
    | _ ->
      let b, m_elab, usage = infer_tm ctx env (Match (m, mot, cls)) in
      let _ = Statype1.assert_equal env a b in
      (m_elab, usage))
  | Fix abs ->
    let x, m = unbind_tm abs in
    let s = Statype1.infer_sort ctx env a in
    let m_elab, usage = check_tm (add_v x s a ctx) env m a in
    let usage = remove x usage R s in
    let _ = assert_pure usage in
    Syntax2.(Fix (bind_tm x m_elab), usage)
  | _ ->
    let b, m_elab, usage = infer_tm ctx env m in
    let _ = Statype1.assert_equal env a b in
    (m_elab, usage)

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
  and arity_ptl ctx a ms xs =
    match (a, ms) with
    | PBind (a, abs), m :: ms ->
      let b = asubst_ptl abs (Ann (a, m)) in
      arity_ptl ctx b ms xs
    | PBase a, _ -> arity_tl ctx a xs
    | _ -> failwith "arity_ptl"
  and arity_tl ctx a xs =
    match (a, xs) with
    | TBind (r, a, abs), x :: xs ->
      let s = Statype1.infer_sort ctx env a in
      let ctx = add_v x s a ctx in
      let tl = asubst_tl abs (Var x) in
      let ctx, b, rsx = arity_tl ctx tl xs in
      (ctx, b, (r, s, x) :: rsx)
    | TBase a, [] -> (ctx, a, [])
    | _ -> failwith "arity_tl"
  in
  match cls with
  | cl :: cls -> (
    let p, rhs = unbindp_tm cl in
    match p with
    | PCons (c, xs) ->
      let cns = tm_of_p p in
      let ptl, cs = remove_c c ctx cs in
      let ctx, a, rsx = arity_ptl ctx ptl ms xs in
      let cover = coverage ctx env cls cs ms in
      (ctx, cns, a, c, rsx, rhs) :: cover
    | _ -> failwith "coverage")
  | [] -> (
    match cs with
    | [] -> []
    | _ -> failwith "coverage")

and infer_cover cover env =
  match cover with
  | (ctx, _, _, c, rsx, rhs) :: cover ->
    let a, rhs_elab, usage = infer_tm ctx env rhs in
    let usage =
      List.fold_left (fun usage (r, s, x) -> remove x usage r s) usage rsx
    in
    let cls_elab, usages = infer_cover cover env in
    let p = Syntax2.(PCons (c, List.map (fun (_, _, x) -> x) rsx)) in
    (Syntax2.(bindp_tm p rhs_elab :: cls_elab), (a, usage) :: usages)
  | _ -> ([], [])

and check_cover cover env a =
  match cover with
  | (ctx, _, _, c, rsx, rhs) :: cover ->
    let rhs_elab, usage = check_tm ctx env rhs a in
    let usage =
      List.fold_left (fun usage (r, s, x) -> remove x usage r s) usage rsx
    in
    let cls_elab, usages = check_cover cover env a in
    let p = Syntax2.(PCons (c, List.map (fun (_, _, x) -> x) rsx)) in
    (Syntax2.(bindp_tm p rhs_elab :: cls_elab), usage :: usages)
  | _ -> ([], [])

and check_mot cover env mot =
  match (mot, cover) with
  | Mot0, _ -> failwith "check_Mot0"
  | Mot1 abs, (ctx, cns, _, c, rsx, rhs) :: cover ->
    let b = asubst_tm abs cns in
    let rhs_elab, usage = check_tm ctx env rhs b in
    let usage =
      List.fold_left (fun usage (r, s, x) -> remove x usage r s) usage rsx
    in
    let cls_elab, usages = check_mot cover env mot in
    let p = Syntax2.(PCons (c, List.map (fun (_, _, x) -> x) rsx)) in
    (Syntax2.(bindp_tm p rhs_elab :: cls_elab), usage :: usages)
  | Mot2 abs, (ctx, _, a, c, rsx, rhs) :: cover ->
    let p, b = unbindp_tm abs in
    let b = substp_tm p b a in
    let rhs_elab, usage = check_tm ctx env rhs b in
    let usage =
      List.fold_left (fun usage (r, s, x) -> remove x usage r s) usage rsx
    in
    let cls_elab, usages = check_mot cover env mot in
    let p = Syntax2.(PCons (c, List.map (fun (_, _, x) -> x) rsx)) in
    (Syntax2.(bindp_tm p rhs_elab :: cls_elab), usage :: usages)
  | Mot3 abs, (ctx, cns, a, c, rsx, rhs) :: cover ->
    let x, abs = unbind_ptm abs in
    let p, b = unbindp_tm abs in
    let b = subst_tm x b cns in
    let b = substp_tm p b a in
    let rhs_elab, usage = check_tm ctx env rhs b in
    let usage =
      List.fold_left (fun usage (r, s, x) -> remove x usage r s) usage rsx
    in
    let cls_elab, usages = check_mot cover env mot in
    let p = Syntax2.(PCons (c, List.map (fun (_, _, x) -> x) rsx)) in
    (Syntax2.(bindp_tm p rhs_elab :: cls_elab), usage :: usages)
  | _ -> ([], [])

let rec infer_dcls ctx env dcls =
  match dcls with
  | DTm (N, x, a_opt, m) :: dcls -> (
    match a_opt with
    | Some a ->
      let s = Statype1.infer_sort ctx env a in
      let _ = Statype1.check_tm ctx env m a in
      let ctx = add_v x s a ctx in
      let env = VMap.add x m env in
      let dcls_elab, usage = infer_dcls ctx env dcls in
      let usage = remove x usage N s in
      (Syntax2.(DTm (x, Box) :: dcls_elab), usage)
    | None ->
      let a = Statype1.infer_tm ctx env m in
      let s = Statype1.infer_sort ctx env a in
      let ctx = add_v x s a ctx in
      let env = VMap.add x m env in
      let dcls_elab, usage = infer_dcls ctx env dcls in
      let usage = remove x usage N s in
      (Syntax2.(DTm (x, Box) :: dcls_elab), usage))
  | DTm (R, x, a_opt, m) :: dcls -> (
    match a_opt with
    | Some a ->
      let s = Statype1.infer_sort ctx env a in
      let m_elab, usage1 = check_tm ctx env m a in
      let ctx = add_v x s a ctx in
      let env = VMap.add x m env in
      let dcls_elab, usage2 = infer_dcls ctx env dcls in
      let usage2 = remove x usage2 R s in
      let usage = merge usage1 usage2 in
      (Syntax2.(DTm (x, m_elab) :: dcls_elab), usage)
    | None ->
      let a, m_elab, usage1 = infer_tm ctx env m in
      let s = Statype1.infer_sort ctx env a in
      let ctx = add_v x s a ctx in
      let env = VMap.add x m env in
      let dcls_elab, usage2 = infer_dcls ctx env dcls in
      let usage2 = remove x usage2 R s in
      let usage = merge usage1 usage2 in
      (Syntax2.(DTm (x, m_elab) :: dcls_elab), usage))
  | DData (d, ptl, dconss) :: dcls ->
    let s = Statype1.arity_ptl ctx env ptl in
    let ctx = add_d d ptl [] ctx in
    let dconss_elab, cs, ctx =
      List.fold_right
        (fun (DCons (c, ptl)) (dconss_elab, cs, ctx) ->
          let n = Statype1.param_ptl ctx env ptl d [] s in
          let ctx = add_c c ptl ctx in
          Syntax2.(DCons (c, n) :: dconss_elab, c :: cs, ctx))
        dconss ([], [], ctx)
    in
    let ctx = add_d d ptl cs ctx in
    let dcls_elab, usage = infer_dcls ctx env dcls in
    (Syntax2.(DData (d, dconss_elab) :: dcls_elab), usage)
  | DAtom (N, x, a) :: dcls ->
    let s = Statype1.infer_sort ctx env a in
    let ctx = add_v x s a ctx in
    let dcls_elab, usage = infer_dcls ctx env dcls in
    let usage = remove x usage N s in
    (dcls_elab, usage)
  | DAtom (R, x, a) :: dcls ->
    let s = Statype1.infer_sort ctx env a in
    let ctx = add_v x s a ctx in
    let dcls_elab, usage = infer_dcls ctx env dcls in
    let usage = remove x usage R s in
    (Syntax2.(DAtom x :: dcls_elab), usage)
  | [] -> ([], VMap.empty)

let check_dcls dcls =
  let dcls_elab, usage = infer_dcls empty VMap.empty dcls in
  let _ = assert_empty usage in
  dcls_elab
