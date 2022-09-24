open Fmt
open Names
open Syntax1
open Equality1
open Pprint1

let pp_map fmt map =
  let aux fmt map =
    VMap.iter (fun x m -> pf fmt "%a := %a@;<1 2>" V.pp x pp_tm m) map
  in
  pf fmt "@[<v 0>map{@;<1 2>%a}@]" aux map

type eqn = tm VMap.t * tm * tm
and eqns = eqn list

type map = (tm_opt * tm_opt) MMap.t

let pp_eqn fmt (_, m, n) = pf fmt "%a ?= %a" pp_tm m pp_tm n

let pp_eqns fmt eqns =
  let rec aux fmt eqns =
    match eqns with
    | [] -> ()
    | [ eqn ] -> pf fmt "@[%a@]" pp_eqn eqn
    | eqn :: eqns -> pf fmt "@[%a@]@;<1 2>%a" pp_eqn eqn aux eqns
  in
  pf fmt "@[<v 0>eqns{@;<1 2>%a}@]" aux eqns

let rec fv ctx = function
  | Ann (a, m) -> VSet.union (fv ctx a) (fv ctx m)
  | Meta (_, ms) ->
    List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  | Type _ -> VSet.empty
  | Var x -> (
    match VSet.find_opt x ctx with
    | Some _ -> VSet.empty
    | None -> VSet.singleton x)
  | Pi (_, _, a, abs) ->
    let x, b = unbind_tm abs in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Lam (_, _, abs) ->
    let x, m = unbind_tm abs in
    fv (VSet.add x ctx) m
  | App (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Let (_, m, abs) ->
    let x, n = unbind_tm abs in
    let fv1 = fv ctx m in
    let fv2 = fv (VSet.add x ctx) n in
    VSet.union fv1 fv2
  | Data (_, ms) ->
    List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  | Cons (_, ms) ->
    List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  | Match (m, mot, cls) ->
    let fv1 = fv ctx m in
    let fv2 = fv_mot ctx mot in
    let fv3 =
      List.fold_left
        (fun acc abs ->
          let p, m = unbindp_tm abs in
          let xs = xs_of_p p in
          let ctx = VSet.union (VSet.of_list xs) ctx in
          VSet.union acc (fv ctx m))
        VSet.empty cls
    in
    VSet.union (VSet.union fv1 fv2) fv3
  | Fix abs ->
    let x, m = unbind_tm abs in
    fv (VSet.add x ctx) m

and fv_mot ctx = function
  | Mot0 -> VSet.empty
  | Mot1 abs ->
    let x, m = unbind_tm abs in
    fv (VSet.add x ctx) m
  | Mot2 abs ->
    let p, m = unbindp_tm abs in
    let xs = xs_of_p p in
    let ctx = VSet.union (VSet.of_list xs) ctx in
    fv ctx m
  | Mot3 abs ->
    let x, abs = unbind_ptm abs in
    let p, m = unbindp_tm abs in
    let xs = xs_of_p p in
    let ctx = VSet.union (VSet.of_list (x :: xs)) ctx in
    fv ctx m

let rec occurs x = function
  | Ann (a, m) -> occurs x a || occurs x m
  | Meta (y, _) -> M.equal x y
  | Type _ -> false
  | Var _ -> false
  | Pi (_, _, a, abs) ->
    let _, b = unbind_tm abs in
    occurs x a || occurs x b
  | Lam (_, _, abs) ->
    let _, m = unbind_tm abs in
    occurs x m
  | App (m, n) -> occurs x m || occurs x n
  | Let (_, m, abs) ->
    let _, n = unbind_tm abs in
    occurs x m || occurs x n
  | Data (_, ms) -> List.exists (occurs x) ms
  | Cons (_, ms) -> List.exists (occurs x) ms
  | Match (m, mot, cls) ->
    let m_res = occurs x m in
    let mot_res = occurs_mot x mot in
    let cls_res =
      List.exists
        (fun abs ->
          let _, m = unbindp_tm abs in
          occurs x m)
        cls
    in
    m_res || mot_res || cls_res
  | Fix abs ->
    let _, m = unbind_tm abs in
    occurs x m

and occurs_mot x = function
  | Mot0 -> false
  | Mot1 abs ->
    let _, a = unbind_tm abs in
    occurs x a
  | Mot2 abs ->
    let _, a = unbindp_tm abs in
    occurs x a
  | Mot3 abs ->
    let _, abs = unbind_ptm abs in
    let _, a = unbindp_tm abs in
    occurs x a

let rec asimpl (env, m1, m2) =
  if equal rd_all env m1 m2 then
    []
  else
    let h1, sp1 = unApps m1 in
    let h2, sp2 = unApps m2 in
    let eqns_sp =
      List.fold_left2
        (fun acc m n ->
          let eqns = asimpl (env, m, n) in
          acc @ eqns)
        [] sp1 sp2
    in
    let eqns_h =
      match (h1, h2) with
      | Meta _, _ -> [ (env, m1, m2) ]
      | _, Meta _ -> [ (env, m2, m1) ]
      | Type s1, Type s2 ->
        if s1 = s2 then
          []
        else
          failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
      | Var x1, Var x2 ->
        if V.equal x1 x2 then
          []
        else
          failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
      | Var x, _ -> (
        match VMap.find_opt x env with
        | Some m1 -> asimpl (env, mkApps m1 sp1, m2)
        | None -> failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2)
      | _, Var y -> (
        match VMap.find_opt y env with
        | Some m2 -> asimpl (env, m1, mkApps m2 sp2)
        | None -> failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2)
      | Pi (r1, s1, a1, abs1), Pi (r2, s2, a2, abs2) ->
        if r1 = r2 && s1 = s2 then
          let _, b1, b2 = unbind2_tm abs1 abs2 in
          let eqns1 = asimpl (env, a1, a2) in
          let eqns2 = asimpl (env, b1, b2) in
          eqns1 @ eqns2
        else
          failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
      | Lam (r1, s1, abs1), Lam (r2, s2, abs2) ->
        if r1 = r2 && s1 = s2 then
          let _, m1, m2 = unbind2_tm abs1 abs2 in
          asimpl (env, m1, m2)
        else
          failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
      | Let (r1, e1, abs1), Let (r2, e2, abs2) ->
        if r1 = r2 then
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = asimpl (env, e1, e2) in
          let eqns2 = asimpl (env, n1, n2) in
          eqns1 @ eqns2
        else
          failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2
      | Data (d1, ms1), Data (d2, ms2) ->
        if D.equal d1 d2 then
          List.fold_left2
            (fun acc m1 m2 -> acc @ asimpl (env, m1, m2))
            [] ms1 ms2
        else
          failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
      | Cons (c1, ms1), Cons (c2, ms2) ->
        if C.equal c1 c2 then
          List.fold_left2
            (fun acc m1 m2 -> acc @ asimpl (env, m1, m2))
            [] ms1 ms2
        else
          failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
      | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
        let eqns1 = asimpl (env, m1, m2) in
        let eqns2 = asimpl_mot (env, mot1, mot2) in
        let eqns3 =
          List.fold_left2
            (fun acc abs1 abs2 ->
              let _, m, n = unbindp2_tm abs1 abs2 in
              acc @ asimpl (env, m, n))
            [] cls1 cls2
        in
        eqns1 @ eqns2 @ eqns3
      | Fix abs1, Fix abs2 ->
        let _, m1, m2 = unbind2_tm abs1 abs2 in
        asimpl (env, m1, m2)
      | _ -> failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2
    in
    eqns_h @ eqns_sp

and asimpl_mot (env, mot1, mot2) =
  match (mot1, mot2) with
  | Mot0, Mot0 -> []
  | Mot1 abs1, Mot1 abs2 ->
    let _, a1, a2 = unbind2_tm abs1 abs2 in
    asimpl (env, a1, a2)
  | Mot2 abs1, Mot2 abs2 ->
    let _, a1, a2 = unbindp2_tm abs1 abs2 in
    asimpl (env, a1, a2)
  | Mot3 abs1, Mot3 abs2 ->
    let _, abs1, abs2 = unbind2_ptm abs1 abs2 in
    let _, a1, a2 = unbindp2_tm abs1 abs2 in
    asimpl (env, a1, a2)
  | _ -> failwith "asimpl failure(%a, %a)" pp_mot mot1 pp_mot mot2

let rec simpl (env, m1, m2) =
  try asimpl (env, m1, m2) with
  | _ ->
    let m1 = whnf [ Beta; Iota; Zeta ] env m1 in
    let m2 = whnf [ Beta; Iota; Zeta ] env m2 in
    let h1, sp1 = unApps m1 in
    let h2, sp2 = unApps m2 in
    let eqns_sp =
      try
        List.fold_left2
          (fun acc m n ->
            let eqns = simpl (env, m, n) in
            acc @ eqns)
          [] sp1 sp2
      with
      | _ -> []
    in
    let eqns_h =
      match (h1, h2) with
      | Meta _, _ -> [ (env, m1, m2) ]
      | _, Meta _ -> [ (env, m2, m1) ]
      | Type s1, Type s2 ->
        if s1 = s2 then
          []
        else
          failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
      | Var x1, Var x2 ->
        if V.equal x1 x2 then
          []
        else
          failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
      | Var x, _ -> (
        match VMap.find_opt x env with
        | Some m1 -> simpl (env, mkApps m1 sp1, m2)
        | None -> failwith "umeta_simpl(%a, %a)" pp_tm m1 pp_tm m2)
      | _, Var y -> (
        match VMap.find_opt y env with
        | Some m2 -> simpl (env, m1, mkApps m2 sp2)
        | None -> failwith "umeta_simpl(%a, %a)" pp_tm m1 pp_tm m2)
      | Pi (r1, s1, a1, abs1), Pi (r2, s2, a2, abs2) ->
        if r1 = r2 && s1 = s2 then
          let _, b1, b2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (env, a1, a2) in
          let eqns2 = simpl (env, b1, b2) in
          eqns1 @ eqns2
        else
          failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
      | Lam (r1, s1, abs1), Lam (r2, s2, abs2) ->
        if r1 = r2 && s1 = s2 then
          let _, m1, m2 = unbind2_tm abs1 abs2 in
          simpl (env, m1, m2)
        else
          failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
      | Let (r1, e1, abs1), Let (r2, e2, abs2) ->
        if r1 = r2 then
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (env, e1, e2) in
          let eqns2 = simpl (env, n1, n2) in
          eqns1 @ eqns2
        else
          failwith "umeta_simpl(%a, %a)" pp_tm m1 pp_tm m2
      | Data (d1, ms1), Data (d2, ms2) ->
        if D.equal d1 d2 then
          List.fold_left2
            (fun acc m1 m2 -> acc @ simpl (env, m1, m2))
            [] ms1 ms2
        else
          failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
      | Cons (c1, ms1), Cons (c2, ms2) ->
        if C.equal c1 c2 then
          List.fold_left2
            (fun acc m1 m2 -> acc @ simpl (env, m1, m2))
            [] ms1 ms2
        else
          failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
      | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
        let eqns1 = simpl (env, m1, m2) in
        let eqns2 = simpl_mot (env, mot1, mot2) in
        let eqns3 =
          List.fold_left2
            (fun acc abs1 abs2 ->
              let _, m, n = unbindp2_tm abs1 abs2 in
              acc @ simpl (env, m, n))
            [] cls1 cls2
        in
        eqns1 @ eqns2 @ eqns3
      | Fix abs1, Fix abs2 ->
        let _, m1, m2 = unbind2_tm abs1 abs2 in
        simpl (env, m1, m2)
      | _ -> failwith "umeta_simpl(%a, %a)" pp_tm m1 pp_tm m2
    in
    eqns_h @ eqns_sp

and simpl_mot (env, mot1, mot2) =
  match (mot1, mot2) with
  | Mot0, Mot0 -> []
  | Mot1 abs1, Mot1 abs2 ->
    let _, a1, a2 = unbind2_tm abs1 abs2 in
    simpl (env, a1, a2)
  | Mot2 abs1, Mot2 abs2 ->
    let _, a1, a2 = unbindp2_tm abs1 abs2 in
    simpl (env, a1, a2)
  | Mot3 abs1, Mot3 abs2 ->
    let _, abs1, abs2 = unbind2_ptm abs1 abs2 in
    let _, a1, a2 = unbindp2_tm abs1 abs2 in
    simpl (env, a1, a2)
  | _ -> failwith "asimpl failure(%a, %a)" pp_mot mot1 pp_mot mot2

let meta_spine sp =
  List.map
    (fun m ->
      match m with
      | Var x -> x
      | _ -> V.blank ())
    sp

let solve map (env, m1, m2) =
  let m1 = whnf [ Beta; Iota; Zeta ] env m1 in
  let m2 = whnf [ Beta; Iota; Zeta ] env m2 in
  match (m1, m2) with
  | Meta _, Meta _ -> map
  | Meta (x, xs), _ ->
    if occurs x m2 then
      failwith "occurs(%a, %a)" M.pp x pp_tm m2
    else
      let xs = meta_spine xs in
      let ctx = fv VSet.empty m2 in
      if VSet.subset ctx (VSet.of_list xs) then
        let m = mLam R U xs m2 in
        MMap.add x (Some m, None) map
      else
        failwith "solve0(%a{%a} ?= %a)" pp_tm m1 V.pps xs pp_tm m2
  | _ -> failwith "solve1(%a ?= %a)" pp_tm m1 pp_tm m2

let rec resolve_tm map m =
  match m with
  | Meta (x, xs) -> (
    try
      match MMap.find x map with
      | Some h, _ ->
        let m = mkApps h xs in
        resolve_tm map (whnf [ Beta; Iota; Zeta ] VMap.empty m)
      | _ -> m
    with
    | _ -> m)
  | Ann (a, m) -> Ann (resolve_tm map a, resolve_tm map m)
  | Type _ -> m
  | Var _ -> m
  | Pi (r, s, a, abs) ->
    let x, b = unbind_tm abs in
    let a = resolve_tm map a in
    let b = resolve_tm map b in
    Pi (r, s, a, bind_tm x b)
  | Lam (r, s, abs) ->
    let x, m = unbind_tm abs in
    let m = resolve_tm map m in
    Lam (r, s, bind_tm x m)
  | App (m, n) ->
    let m = resolve_tm map m in
    let n = resolve_tm map n in
    App (m, n)
  | Let (r, m, abs) ->
    let x, n = unbind_tm abs in
    let m = resolve_tm map m in
    let n = resolve_tm map n in
    Let (r, m, bind_tm x n)
  | Data (d, ms) ->
    let ms = List.map (resolve_tm map) ms in
    Data (d, ms)
  | Cons (c, ms) ->
    let ms = List.map (resolve_tm map) ms in
    Cons (c, ms)
  | Match (m, mot, cls) ->
    let m = resolve_tm map m in
    let mot = resolve_mot map mot in
    let cls =
      List.map
        (fun abs ->
          let p, m = unbindp_tm abs in
          let m = resolve_tm map m in
          bindp_tm p m)
        cls
    in
    Match (m, mot, cls)
  | Fix abs ->
    let x, m = unbind_tm abs in
    let m = resolve_tm map m in
    Fix (bind_tm x m)

and resolve_mot map = function
  | Mot0 -> Mot0
  | Mot1 abs ->
    let x, a = unbind_tm abs in
    let a = resolve_tm map a in
    Mot1 (bind_tm x a)
  | Mot2 abs ->
    let p, a = unbindp_tm abs in
    let a = resolve_tm map a in
    Mot2 (bindp_tm p a)
  | Mot3 abs ->
    let x, abs = unbind_ptm abs in
    let p, m = unbindp_tm abs in
    let m = resolve_tm map m in
    Mot3 (bind_ptm x (bindp_tm p m))

let rec resolve_tl map tl =
  match tl with
  | TBase b -> TBase (resolve_tm map b)
  | TBind (r, a, abs) ->
    let x, tl = unbind_tl abs in
    let a = resolve_tm map a in
    let tl = resolve_tl map tl in
    TBind (r, a, bind_tl x tl)

let rec resolve_ptl map ptl =
  match ptl with
  | PBase tl -> PBase (resolve_tl map tl)
  | PBind (a, abs) ->
    let x, ptl = unbind_ptl abs in
    let a = resolve_tm map a in
    let ptl = resolve_ptl map ptl in
    PBind (a, bind_ptl x ptl)

let resolve_dcons map (DCons (c, ptl)) = DCons (c, resolve_ptl map ptl)

let resolve_dcl map dcl =
  match dcl with
  | DTm (r, x, a_opt, m) ->
    let a_opt = Option.map (resolve_tm map) a_opt in
    let m = resolve_tm map m in
    DTm (r, x, a_opt, m)
  | DData (d, ptl, dconss) ->
    let ptl = resolve_ptl map ptl in
    let dconss = List.map (resolve_dcons map) dconss in
    DData (d, ptl, dconss)
  | DAtom (r, x, a) -> DAtom (r, x, resolve_tm map a)

let resolve_dcls map dcls = List.map (resolve_dcl map) dcls

let rec unify map eqns =
  let eqns =
    List.map
      (fun (env, m1, m2) -> (env, resolve_tm map m1, resolve_tm map m2))
      eqns
  in
  match List.concat_map simpl eqns with
  | [] -> map
  | eqn :: eqns ->
    let map = solve map eqn in
    unify map eqns
