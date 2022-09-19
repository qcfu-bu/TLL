open Fmt
open Names
open Syntax1
open Pprint1
open Equality1
open Unify1

let pp_usage fmt usage =
  let aux fmt usage =
    VMap.iter (fun x b -> pf fmt "%a ?%b@;<1 2>" V.pp x b) usage
  in
  pf fmt "@[<v 0>{@;<1 2>%a}]" aux usage

let merge usage1 usage2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some false, Some false -> failwith "merge"
      | Some b1, Some b2 -> Some (b1 && b2)
      | Some b, None -> Some b
      | None, Some b -> Some b
      | _ -> None)
    usage1 usage2

let refine_equal usage1 usage2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some b1, Some b2 -> Some (b1 && b2)
      | Some true, None -> None
      | None, Some true -> None
      | None, None -> None
      | _ -> failwith "refine_equal")
    usage1 usage2

let assert_empty usage =
  if VMap.for_all (fun _ b -> b) usage then
    ()
  else
    failwith "assert_empty"

let remove x usage s =
  match s with
  | U -> usage
  | L ->
    if VMap.exists (fun y _ -> V.equal x y) usage then
      VMap.remove x usage
    else
      failwith "remove(%a)" V.pp x

let usage_of_ctx ctx = VMap.map (fun _ -> true) Statype1.(ctx.vs)

let trans_sort s =
  match s with
  | U -> Syntax2.U
  | L -> Syntax2.L

let rec infer_tm ctx env = function
  | Ann (a, m) -> (
    let _ = Statype1.infer_sort ctx env a in
    match m with
    | Let (r, m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let m_elab, usage = check_tm ctx env (Let (r, m, abs)) a in
      (a, m_elab, usage)
    | _ ->
      let m_elab, ctx = check_tm ctx env m a in
      (a, m_elab, ctx))
  | Var x -> (
    let s, a = Statype1.find_v x ctx in
    match s with
    | U -> Syntax2.(a, Var x, VMap.empty)
    | L -> Syntax2.(a, Var x, VMap.singleton x false))
  | Fun (a_opt, abs) as m -> (
    match a_opt with
    | Some a ->
      let _ = Statype1.infer_sort ctx env a in
      let m_elab, usage = check_tm ctx env (Fun (a_opt, abs)) a in
      (a, m_elab, usage)
    | None -> failwith "infer_Fun(%a)" pp_tm m)
  | App (m, n) -> (
    let a, m_elab, usage1 = infer_tm ctx env m in
    match whnf rd_all env a with
    | Pi (N, s, a, abs) ->
      let _ = Statype1.infer_sort ctx env a in
      let _ = Statype1.check_tm ctx env n a in
      ( asubst_tm abs (Ann (a, n))
      , Syntax2.(App (trans_sort s, m_elab, Box))
      , usage1 )
    | Pi (R, s, a, abs) ->
      let _ = Statype1.infer_sort ctx env a in
      let n_elab, usage2 = check_tm ctx env n a in
      ( asubst_tm abs (Ann (a, n))
      , Syntax2.(App (trans_sort s, m_elab, n_elab))
      , merge usage1 usage2 )
    | _ -> failwith "infer_App(%a)" pp_tm m)
  | Let (N, m, abs) ->
    let a = Statype1.infer_tm ctx env m in
    let s = Statype1.infer_sort ctx env a in
    let x, n = unbind_tm abs in
    let b, n_elab, usage =
      infer_tm (Statype1.add_v x s a ctx) (VMap.add x m env) n
    in
    (b, Syntax2.(Let (Box, bind_tm x n_elab)), usage)
  | Let (R, m, abs) ->
    let a, m_elab, usage1 = infer_tm ctx env m in
    let s = Statype1.infer_sort ctx env a in
    let x, n = unbind_tm abs in
    let b, n_elab, usage2 =
      infer_tm (Statype1.add_v x s a ctx) (VMap.add x m env) n
    in
    let usage2 = remove x usage2 s in
    (b, Syntax2.(Let (m_elab, bind_tm x n_elab)), merge usage1 usage2)
  | Cons (c, ms) ->
    let ptl = Statype1.find_c c ctx in
    let a, ms_elab, usage = check_ptl ctx env ms ptl in
    (a, Syntax2.(Cons (c, ms_elab)), usage)
  | Match (ms, a, cls) ->
    let _ = Statype1.infer_sort ctx env a in
    let m_elab, usage = check_tm ctx env (Match (ms, a, cls)) a in
    (a, m_elab, usage)
  | m -> failwith "infer_Dyn(%a)" pp_tm m

and check_ptl ctx env ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (N, a, abs) ->
    let _ = Statype1.check_tm ctx env m a in
    let a, ms_elab, usage =
      check_ptl ctx env ms (asubst_ptl abs (Ann (a, m)))
    in
    (a, Box :: ms_elab, usage)
  | m :: ms, PBind (R, a, abs) ->
    let m_elab, usage1 = check_tm ctx env m a in
    let a, ms_elab, usage2 =
      check_ptl ctx env ms (asubst_ptl abs (Ann (a, m)))
    in
    (a, m_elab :: ms_elab, merge usage1 usage2)
  | ms, PBase tl -> check_tl ctx env ms tl
  | _ -> failwith "check_ptl(%a, %a)" pp_tms ms pp_ptl ptl

and check_tl ctx env ms tl =
  match (ms, tl) with
  | m :: ms, TBind (N, a, abs) ->
    let _ = Statype1.check_tm ctx env m a in
    let a, ms_elab, usage = check_tl ctx env ms (asubst_tl abs (Ann (a, m))) in
    (a, Box :: ms_elab, usage)
  | m :: ms, TBind (R, a, abs) ->
    let m_elab, usage1 = check_tm ctx env m a in
    let a, ms_elab, usage2 = check_tl ctx env ms (asubst_tl abs (Ann (a, m))) in
    (a, m_elab :: ms_elab, merge usage1 usage2)
  | [], TBase a ->
    let _ = Statype1.infer_sort ctx env a in
    (a, [], VMap.empty)
  | _ -> failwith "check_tl(%a, %a)" pp_tms ms pp_tl tl

and check_tm ctx env m a =
  match m with
  | Fun (b_opt, abs) ->
    let s =
      match b_opt with
      | Some b ->
        let s = Statype1.infer_sort ctx env b in
        let _ = Statype1.assert_equal env a b in
        s
      | None -> Statype1.infer_sort ctx env a
    in
    let x, cls = unbind_cls abs in
    let prbm = UVar.prbm_of_cls cls in
    let ctx, opt =
      match s with
      | U -> (Statype1.add_v x s a ctx, Some x)
      | L -> (ctx, None)
    in
    check_prbm ctx env prbm a opt
  | Let (r, m, abs) ->
    let x, n = unbind_tm abs in
    let abs = bind_tm x (Ann (a, n)) in
    let b, m_elab, usage = infer_tm ctx env (Let (r, m, abs)) in
    let _ = Statype1.assert_equal env a b in
    (m_elab, usage)
  | Cons (c, ms) -> (
    match whnf rd_all env a with
    | Data (_, ns) ->
      let ptl = Statype1.find_c c ctx in
      let ptl =
        List.fold_left
          (fun ptl n ->
            match ptl with
            | PBind (_, a, abs) -> asubst_ptl abs (Ann (a, n))
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
  | Match (ms, b, cls) ->
    let ms_ty, ms_elab, usage1 =
      List.fold_left
        (fun (ms_ty, ms_elab, acc) m ->
          let m_ty, m_elab, usage = infer_tm ctx env m in
          (m_ty :: ms_ty, m_elab :: ms_elab, merge usage acc))
        ([], [], VMap.empty) ms
    in
    let mot =
      List.fold_left
        (fun acc m_ty -> Pi (R, L, m_ty, bind_tm (V.blank ()) acc))
        b ms_ty
    in
    let _ = Statype1.infer_sort ctx env mot in
    let prbm = UVar.prbm_of_cls cls in
    let ct, usage2 = check_prbm ctx env prbm mot None in
    let _ = Statype1.assert_equal env a b in
    (Syntax2.(mkApps L ct (List.rev ms_elab)), merge usage1 usage2)
  | _ ->
    let b, m_elab, usage = infer_tm ctx env m in
    let _ = Statype1.assert_equal env a b in
    (m_elab, usage)

and tl_of_ptl ptl ns =
  match (ptl, ns) with
  | PBind (_, a, abs), n :: ns ->
    let ptl = asubst_ptl abs (Ann (a, n)) in
    tl_of_ptl ptl ns
  | PBase tl, _ -> tl
  | _ -> failwith "tl_of_ptl"

and check_prbm ctx env prbm a opt =
  let rec is_absurd es rhs =
    match (es, rhs) with
    | (_, Var _, Absurd, _) :: _, None -> true
    | (_, Var _, Absurd, _) :: _, Some _ -> failwith "is_absurd"
    | _ :: es, _ -> is_absurd es rhs
    | [], _ -> false
  in
  let rec get_absurd = function
    | (_, Var _, Absurd, a) :: _ -> a
    | _ :: es -> get_absurd es
    | [] -> failwith "get_absurd"
  in
  let rec can_split = function
    | (_, Var _, Cons (_, _), _) :: _ -> true
    | _ :: es -> can_split es
    | [] -> false
  in
  let rec first_split = function
    | (_, Var x, Cons (_, _), a) :: _ -> (x, a)
    | _ :: es -> first_split es
    | [] -> failwith "first_split"
  in
  let fail_on_d ctx d ns s a =
    let _, cs = Statype1.find_d d ctx in
    let ptls = List.map (fun c -> Statype1.find_c c ctx) cs in
    let rec loop = function
      | [] -> (Syntax2.Box, usage_of_ctx ctx)
      | ptl :: ptls ->
        let tl = tl_of_ptl ptl ns in
        let _, targ = fold_tl (fun () _ _ _ tl -> ((), tl)) () tl in
        let global = (env, a, targ, Type s) :: prbm.global in
        if Statype1.has_failed (fun () -> UVar.unify global) then
          loop ptls
        else
          failwith "fail_on_d(%a)" pp_tm (Data (d, ns))
    in
    loop ptls
  in
  match prbm.clause with
  | [] -> (
    if Statype1.has_failed (fun () -> UVar.unify prbm.global) then
      (Syntax2.Box, usage_of_ctx ctx)
    else
      match whnf rd_all env a with
      | Pi (_, _, a, _) -> (
        let s = Statype1.infer_sort ctx env a in
        match whnf rd_all env a with
        | Data (d, ns) -> fail_on_d ctx d ns s a
        | _ -> failwith "check_Empty")
      | _ -> failwith "check_Empty")
  | (es, _, rhs) :: _ when is_absurd es rhs -> (
    if Statype1.has_failed (fun () -> UVar.unify prbm.global) then
      (Syntax2.Box, usage_of_ctx ctx)
    else
      let a = get_absurd es in
      let s = Statype1.infer_sort ctx env a in
      match whnf rd_all env a with
      | Data (d, ns) -> fail_on_d ctx d ns s a
      | _ -> failwith "check_Absurd")
  | (es, _, _) :: _ when can_split es -> (
    let x, b = first_split es in
    let s = Statype1.infer_sort ctx env b in
    match whnf rd_all env b with
    | Data (d, ns) ->
      let _, cs = Statype1.find_d d ctx in
      let ptls = List.map (fun c -> Statype1.find_c c ctx) cs in
      let usage, cls =
        List.fold_left2
          (fun (acc, cls) ptl c ->
            let tl = tl_of_ptl ptl ns in
            let (ctx, xrs), targ =
              fold_tl
                (fun (ctx, acc) r a x tl ->
                  let s = Statype1.infer_sort ctx env a in
                  let ctx = Statype1.add_v x s a ctx in
                  ((ctx, (x, r, s) :: acc), tl))
                (ctx, []) tl
            in
            let xrs = List.rev xrs in
            let var_args = List.map (fun (x, _, _) -> Var x) xrs in
            let pvar_args = List.map (fun (x, _, _) -> Syntax2.PVar x) xrs in
            let cons = Ann (targ, Cons (c, var_args)) in
            let a = subst_tm x a cons in
            let ctx = Statype1.subst_ctx x ctx cons in
            let prbm = Statype1.prbm_subst ctx x prbm cons in
            let prbm =
              UVar.{ prbm with global = (env, b, targ, Type s) :: prbm.global }
            in
            let ct, usage = check_prbm ctx env prbm a opt in
            let usage =
              List.fold_left (fun acc (x, s) -> remove x acc s) usage xs
            in
            let usage =
              match s with
              | U -> usage
              | L -> VMap.add x false usage
            in
            let cl = Syntax2.(bindp_tm (PCons (c, pvar_args)) ct) in
            (refine_equal acc usage, cl :: cls))
          (usage_of_ctx ctx, [])
          ptls cs
      in
      (Syntax2.(Case (trans_sort s, Var x, List.rev cls)), usage)
    | _ -> failwith "check_Split(%a)" pp_tm b)
  | (es, [], rhs) :: _ ->
    let es = prbm.global @ es in
    let vmap = UVar.unify es in
    let a = UVar.msubst_tm vmap a in
    let ctx = msubst_ctx vmap ctx in
    let rhs =
      match rhs with
      | Some m -> UVar.msubst_tm vmap m
      | None -> failwith "check_Finish"
    in
    let _ = infer_sort ctx env a in
    check_tm ctx env rhs a
  | (es, ps, rhs) :: clause -> (
    let a = whnf rd_all env a in
    match (a, ps) with
    | Pi (s, a, abs), p :: ps -> (
      let x, b = unbind_tm abs in
      let t, _ = infer_sort ctx env a in
      let ctx = add_v x t a ctx in
      let prbm = prbm_add ctx env prbm x a in
      let ct, usage = check_prbm ctx env prbm b None in
      let usage = remove x usage t in
      match (s, opt) with
      | U, Some f ->
        let _ = assert_empty usage in
        (Syntax2.(Fix (bind_tm_abs f x ct)), VMap.empty)
      | U, None ->
        let _ = assert_empty usage in
        (Syntax2.(Lam (trans_sort s, bind_tm x ct)), VMap.empty)
      | L, _ -> (Syntax2.(Lam (trans_sort s, bind_tm x ct)), usage))
    | _ -> failwith "check_Intro")
