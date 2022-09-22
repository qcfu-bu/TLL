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
  | Fun (b_opt, abs) ->
    let s =
      match b_opt with
      | Some b ->
        let s = infer_sort ctx env b in
        let _ = assert_equal env a b in
        s
      | None -> infer_sort ctx env a
    in
    let x, cls = unbind_cls abs in
    let prbm = UVar.prbm_of_cls cls in
    check_prbm (add_v x s a ctx) env prbm a
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
  | Match (ms, b, cls) ->
    let _ = assert_equal env a b in
    let ms_ty = List.fold_left (fun acc m -> infer_tm ctx env m :: acc) [] ms in
    let a =
      List.fold_left
        (fun acc m_ty -> Pi (R, L, m_ty, bind_tm (V.blank ()) acc))
        a ms_ty
    in
    let prbm = UVar.prbm_of_cls cls in
    check_prbm ctx env prbm a
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

and check_prbm ctx env prbm a =
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
    let _, cs = find_d d ctx in
    let ptls = List.map (fun c -> find_c c ctx) cs in
    let rec loop = function
      | [] -> ()
      | ptl :: ptls ->
        let tl = tl_of_ptl ptl ns in
        let _, targ = fold_tl (fun () _ _ _ tl -> ((), tl)) () tl in
        let global = (env, a, targ, Type s) :: prbm.global in
        if has_failed (fun () -> UVar.unify global) then
          loop ptls
        else
          failwith "fail_on_d(%a)" pp_tm (Data (d, ns))
    in
    loop ptls
  in
  match prbm.clause with
  | [] -> (
    if has_failed (fun () -> UVar.unify prbm.global) then
      ()
    else
      match whnf rd_all env a with
      | Pi (_, _, a, _) -> (
        let s = infer_sort ctx env a in
        match whnf rd_all env a with
        | Data (d, ns) -> fail_on_d ctx d ns s a
        | _ -> failwith "check_Empty")
      | a -> failwith "check_Empty(%a)" pp_tm a)
  | (es, _, rhs) :: _ when is_absurd es rhs -> (
    if has_failed (fun () -> UVar.unify prbm.global) then
      ()
    else
      let a = get_absurd es in
      let s = infer_sort ctx env a in
      match whnf rd_all env a with
      | Data (d, ns) -> fail_on_d ctx d ns s a
      | _ -> failwith "check_Absurd")
  | (es, _, _) :: _ when can_split es -> (
    let x, b = first_split es in
    let s = infer_sort ctx env b in
    match whnf rd_all env b with
    | Data (d, ns) ->
      let _, cs = find_d d ctx in
      let ptls = List.map (fun c -> find_c c ctx) cs in
      List.iter2
        (fun ptl c ->
          let tl = tl_of_ptl ptl ns in
          let (ctx, args), targ =
            fold_tl
              (fun (ctx, acc) _ a x tl ->
                let s = infer_sort ctx env a in
                let ctx = add_v x s a ctx in
                ((ctx, Var x :: acc), tl))
              (ctx, []) tl
          in
          let c = Ann (targ, Cons (c, List.rev args)) in
          let a = subst_tm x a c in
          let ctx = subst_ctx x ctx c in
          let prbm = prbm_subst ctx x prbm c in
          let prbm =
            UVar.{ prbm with global = (env, b, targ, Type s) :: prbm.global }
          in
          check_prbm ctx env prbm a)
        ptls cs
    | b -> failwith "check_Split(%a)" pp_tm b)
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
    check_tm ctx env rhs a
  | (_, ps, _) :: _ -> (
    let a = whnf rd_all env a in
    match (a, ps) with
    | Pi (_, _, a, abs), _ :: _ ->
      let x, b = unbind_tm abs in
      let s = infer_sort ctx env a in
      let ctx = add_v x s a ctx in
      let prbm = prbm_add ctx env prbm x a in
      check_prbm ctx env prbm b
    | _ -> failwith "check_Intro")

and prbm_add ctx env prbm x a =
  let rec tm_of_p p =
    match p with
    | PVar x -> Var x
    | PCons (c, ps) ->
      let ptl = find_c c ctx in
      let ps = ps_of_ptl ps ptl in
      let ps = List.map tm_of_p ps in
      Cons (c, ps)
    | PAbsurd -> Absurd
  and ps_of_ptl ps ptl =
    match ptl with
    | PBase tl -> ps_of_tl ps tl
    | PBind (_, _, abs) ->
      let _, ptl = unbind_ptl abs in
      ps_of_ptl ps ptl
  and ps_of_tl ps tl =
    match tl with
    | TBase _ -> ps
    | TBind (_, _, abs) -> (
      let _, tl = unbind_tl abs in
      match ps with
      | p :: ps -> p :: ps_of_tl ps tl
      | _ -> failwith "ps_of_tl")
  in
  match prbm.clause with
  | [] -> prbm
  | (es, p :: ps, rhs) :: clause ->
    let prbm = prbm_add ctx env { prbm with clause } x a in
    let clause = ((env, Var x, tm_of_p p, a) :: es, ps, rhs) :: prbm.clause in
    { prbm with clause }
  | _ -> failwith "prbm_add"

and prbm_subst ctx x prbm m =
  match prbm.clause with
  | [] -> prbm
  | (es, ps, rhs) :: clause -> (
    let prbm = prbm_subst ctx x { prbm with clause } m in
    let opt =
      List.fold_left
        (fun acc (env, l, r, a) ->
          match acc with
          | Some acc -> (
            let l = subst_tm x l m in
            let a = subst_tm x a m in
            match p_simpl ctx env l r a with
            | Some es -> Some (acc @ es)
            | None -> None)
          | None -> None)
        (Some []) es
    in
    match opt with
    | Some es -> { prbm with clause = (es, ps, rhs) :: prbm.clause }
    | _ -> prbm)

and p_simpl ctx env m n a =
  let m = whnf rd_all env m in
  let n = whnf rd_all env n in
  let a = whnf rd_all env a in
  match (m, n, a) with
  | Cons (c1, xs), Cons (c2, ys), Data (d, ns) ->
    if C.equal c1 c2 then
      let _, cs = find_d d ctx in
      if List.exists (fun c -> c = c1) cs then
        let ptl = find_c c1 ctx in
        let tl = tl_of_ptl ptl ns in
        ps_simpl_tl ctx env xs ys tl
      else
        failwith "p_simpl(%a, %a, %a)" pp_tm m pp_tm n pp_tm a
    else
      None
  | Cons (c1, _), _, Data (d, _) ->
    let _, cs = find_d d ctx in
    if List.exists (fun c -> c = c1) cs then
      Some [ (env, m, n, a) ]
    else
      failwith "p_simpl(%a, %a, %a)" pp_tm m pp_tm n pp_tm a
  | _, Cons (c2, _), Data (d, _) ->
    let _, cs = find_d d ctx in
    if List.exists (fun c -> c = c2) cs then
      Some [ (env, m, n, a) ]
    else
      failwith "p_simpl(%a, %a, %a)" pp_tm m pp_tm n pp_tm a
  | _ -> Some [ (env, m, n, a) ]

and ps_simpl_tl ctx env ms ns tl =
  match (ms, ns, tl) with
  | m :: ms, n :: ns, TBind (_, a, abs) -> (
    let opt1 = p_simpl ctx env m n a in
    let tl = asubst_tl abs m in
    let opt2 = ps_simpl_tl ctx env ms ns tl in
    match (opt1, opt2) with
    | Some es1, Some es2 -> Some (es1 @ es2)
    | _ -> None)
  | [], [], TBase _ -> Some []
  | _ -> None
