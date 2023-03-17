open Fmt
open Names
open Syntax1
open Equality1

type eqn = tm VMap.t * tm * tm
type eqns = eqn list

type map = (tm_opt * tm_opt) MMap.t

let rec fv ctx = function
  (* inference *)
  | Ann (m, a) -> VSet.union (fv ctx m) (fv ctx a)
  | Meta (_, ms) ->
    List.fold_left
      (fun acc m -> VSet.union acc (fv ctx m))
      VSet.empty ms
  (* core *)
  | Type _ -> VSet.empty
  | Var x ->
    (match VSet.find_opt x ctx with
     | Some _ -> VSet.empty
     | None -> VSet.singleton x)
  | Pi (_, _, a, abs) ->
    let x, b = unbind_tm abs in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Lam (_, _, abs) ->
    let (x, a_opt), m = unbind_ann abs in
    let fv1 =
      Option.fold
        ~none:VSet.empty
        ~some:(fv ctx)
        a_opt
    in
    let fv2 = fv (VSet.add x ctx) m in
    VSet.union fv1 fv2
  | App (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Let (_, m, abs) ->
    let (x, a_opt), n = unbind_ann abs in
    let fv1 =
      Option.fold
        ~none:VSet.empty
        ~some:(fv ctx)
        a_opt
    in
    let fv2 = fv (VSet.add x ctx) m in
    VSet.union fv1 fv2
  (* data *)
  | Sig (_, _, a, abs) ->
    let x, b = unbind_tm abs in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Pair (_, _, m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Data (_, ms) ->
    List.fold_left
      (fun acc m -> VSet.union acc (fv ctx m))
      VSet.empty ms
  | Cons (_, ms) ->
    List.fold_left
      (fun acc m -> VSet.union acc (fv ctx m))
      VSet.empty ms
  | Match (m, mot, cls) ->
    let fv1 = fv ctx m in
    let fv2 =
      Option.fold
        ~none:VSet.empty
        ~some:(fun abs ->
            let x, a = unbind_tm abs in
            fv (VSet.add x ctx) a)
        mot
    in
    let fv3 = 
      List.fold_left
        (fun acc pabs ->
           let p, m = unbindp_tm pabs in
           let xs = xs_of_p p in
           let ctx = VSet.union (VSet.of_list xs) ctx in
           VSet.union acc (fv ctx m))
        VSet.empty cls
    in
    VSet.union (VSet.union fv1 fv2) fv3
  (* equality *)
  | Eq (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Refl -> VSet.empty
  | Rew (abs, pf, m) ->
    let (x, y), a = unbind_tm2 abs in
    let fv1 = fv (VSet.add x (VSet.add y ctx)) a in
    let fv2 = fv ctx pf in
    let fv3 = fv ctx m in
    VSet.union (VSet.union fv1 fv2) fv3
  (* moandic *)
  | IO a -> fv ctx a
  | Return m -> fv ctx m
  | Do (m, abs) ->
    let (x, a_opt), n = unbind_ann abs in
    let fv1 = fv ctx m in
    let fv2 =
      Option.fold
        ~none:VSet.empty
        ~some:(fv ctx)
        a_opt
    in
    let fv3 = fv (VSet.add x ctx) n in
    VSet.union (VSet.union fv1 fv2) fv3
  (* session *)
  | Proto -> VSet.empty
  | End _ -> VSet.empty
  | Act (_, _, a, abs) ->
    let x, b = unbind_tm abs in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Ch (_, a) -> fv ctx a
  | Open _ -> VSet.empty
  | Fork (a, abs) ->
    let x, m = unbind_tm abs in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) m in
    VSet.union fv1 fv2
  | Recv (_, m) -> fv ctx m
  | Send (_, m) -> fv ctx m
  | Close m -> fv ctx m

let rec occurs x = function
  (* inference *)
  | Ann (m, a) -> occurs x m || occurs x a
  | Meta (y, _) -> M.equal x y
  (* core *)
  | Pi (_, _, a, abs) ->
    let _, b = unbind_tm abs in
    occurs x a || occurs x b
  | Lam (_, _, abs) ->
    let (_, a_opt), m = unbind_ann abs in
    let b1 =
      Option.fold
        ~none:false
        ~some:(occurs x)
        a_opt
    in
    let b2 = occurs x m in
    b1 || b2
  | App (m, n) -> occurs x m || occurs x n
  | Let (_, m, abs) -> 
    let (_, a_opt), n = unbind_ann abs in
    let b1 = occurs x m in
    let b2 = 
      Option.fold
        ~none:false
        ~some:(occurs x)
        a_opt
    in
    let b3 = occurs x n in
    b1 || b2 || b3
  (* data *)
  | Sig (_, _, a, abs) ->
    let _, b = unbind_tm abs in
    occurs x a || occurs x b
  | Pair (_, _, m, n) ->
    occurs x m || occurs x n
  | Data (_, ms) -> List.exists (occurs x) ms
  | Cons (_, ms) -> List.exists (occurs x) ms
  | Match (m, mot, cls) ->
    let b1 = occurs x m in
    let b2 = 
      Option.fold
        ~none:false
        ~some:(fun abs ->
            let _, a = unbind_tm abs in
            occurs x a)
        mot
    in
    let b3 =
      List.exists
        (fun abs ->
           let _, m = unbindp_tm abs in
           occurs x m)
        cls
    in
    b1 || b2 || b3
  (* equality *)
  | Eq (m, n) -> occurs x m || occurs x n
  | Rew (abs, pf, m) ->
    let _, a = unbind_tm2 abs in
    occurs x a || occurs x pf || occurs x m
  (* monadic *)
  | IO a -> occurs x a
  | Return m -> occurs x m
  | Do (m, abs) ->
    let (_, a_opt), n = unbind_ann abs in
    let b1 = occurs x m in
    let b2 =
      Option.fold
        ~none:false
        ~some:(occurs x)
        a_opt
    in
    let b3 = occurs x n in
    b1 || b2 || b3
  (* session *)
  | Act (_, _, a, abs) ->
    let _, b = unbind_tm abs in
    occurs x a || occurs x b
  | Ch (_, a) -> occurs x a
  | Fork (a, abs) ->
    let _, b = unbind_tm abs in
    occurs x a || occurs x b
  | Recv (_, m) -> occurs x m
  | Send (_, m) -> occurs x m
  | Close m -> occurs x m
  (* other *)
  | _ -> false

let rec asimpl (env, m1, m2) =
  if equal [Beta; Delta; Zeta; Iota] env m1 m2 then
    []
  else
    let h1, sp1 = unApps m1 in
    let h2, sp2 = unApps m2 in
    let eqns_sp =
      List.fold_left2
        (fun acc m n -> acc @ asimpl (env, m, n))
        [] sp1 sp2
    in
    let eqns_h =
      match h1, h2 with
      (* inference *)
      | Meta _, _ -> [(env, m1, m2)]
      | _, Meta _ -> [(env, m2, m1)]
      (* core *)
      | Type s1, Type s2 when s1 = s2 -> []
      | Var x1, Var x2 when V.equal x1 x2 -> []
      | Var x, _ ->
        (match VMap.find_opt x env with
         | Some m1 -> asimpl (env, mkApps m1 sp1, m2)
         | None -> failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2)
      | _, Var y ->
        (match VMap.find_opt y env with
         | Some m2 -> asimpl (env, m1, mkApps m2 sp2)
         | None -> failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2)
      | Pi (rel1, s1, a1, abs1), Pi (rel2, s2, a2, abs2)
        when rel1 = rel2 && s1 = s2 ->
        let _, b1, b2 = unbind2_tm abs1 abs2 in
        let eqns1 = asimpl (env, a1, a2) in
        let eqns2 = asimpl (env, b1, b2) in
        eqns1 @ eqns2
      | Lam (rel1, s1, abs1), Lam (rel2, s2, abs2)
        when rel1 = rel2 && s1 = s2 ->
        let (_, a1_opt, a2_opt), n1, n2 = unbind2_ann abs1 abs2 in
        let eqns1 =
          match a1_opt, a2_opt with
          | Some a1, Some a2 -> asimpl (env, a1, a2)
          | _ -> []
        in
        let eqns2 = asimpl (env, n1, n2) in
        eqns1 @ eqns2
      | Let (rel1, m1, abs1), Let (rel2, m2, abs2)
        when rel1 = rel2 ->
        let (_, a1_opt, a2_opt), n1, n2 = unbind2_ann abs1 abs2 in
        let eqns1 = asimpl (env, m1, m2) in
        let eqns2 =
          match a1_opt, a2_opt with
          | Some a1, Some a2 -> asimpl (env, a1, a2)
          | _ -> []
        in
        let eqns3 = asimpl (env, n1, n2) in
        eqns1 @ eqns2 @ eqns3
      (* data *)
      | Sig (rel1, s1, a1, abs1), Sig (rel2, s2, a2, abs2)
        when rel1 = rel2 && s1 = s2 ->
        let _, b1, b2 = unbind2_tm abs1 abs2 in
        let eqns1 = asimpl (env, a1, a2) in
        let eqns2 = asimpl (env, b1, b2) in
        eqns1 @ eqns2
      | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2)
        when rel1 = rel2 && s1 = s2 ->
        let eqns1 = asimpl (env, m1, m2) in
        let eqns2 = asimpl (env, n1, n2) in
        eqns1 @ eqns2
      | Data (d1, ms1), Data (d2, ms2) when D.equal d1 d2 ->
        List.fold_left2
          (fun acc m1 m2 -> acc @ asimpl (env, m1, m2))
          [] ms1 ms2
      | Cons (c1, ms1), Cons (c2, ms2) when C.equal c1 c2 ->
        List.fold_left2
          (fun acc m1 m2 -> acc @ asimpl (env, m1, m2))
          [] ms1 ms2
      | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
        let eqns1 = asimpl (env, m1, m2) in
        let eqns2 =
          match mot1, mot2 with
          | Some abs1, Some abs2 ->
            let _, a1, a2 = unbind2_tm abs1 abs2 in
            asimpl (env, a1, a2)
          | _ -> []
        in
        let eqns3 =
          List.fold_left2
            (fun acc pabs1 pabs2 ->
               let _, n1, n2 = unbindp2_tm pabs1 pabs2 in
               acc @ asimpl (env, n1, n2))
            [] cls1 cls2
        in
        eqns1 @ eqns2 @ eqns3
      (* equality *)
      | Eq (m1, n1), Eq (m2, n2) ->
        let eqns1 = asimpl (env, m1, m2) in
        let eqns2 = asimpl (env, n1, n2) in
        eqns1 @ eqns2
      | Refl, Refl -> []
      | Rew (abs1, pf1, m1), Rew (abs2, pf2, m2) ->
        let (_, _), a1, a2 = unbind2_tm2 abs1 abs2 in
        let eqns1 = asimpl (env, a1, a2) in
        let eqns2 = asimpl (env, pf1, pf2) in
        let eqns3 = asimpl (env, m1, m2) in
        eqns1 @ eqns2 @ eqns3
      (* monadic *)
      | IO a1, IO a2 -> asimpl (env, a1, a2)
      | Return m1, Return m2 -> asimpl (env, m1, m2)
      | Do (m1, abs1), Do (m2, abs2) ->
        let (_, a1_opt, a2_opt), n1, n2 = unbind2_ann abs1 abs2 in
        let eqns1 = asimpl (env, m1, m2) in
        let eqns2 =
          match a1_opt, a2_opt with
          | Some a1, Some a2 -> asimpl (env, a1, a2)
          | _ -> []
        in
        let eqns3 = asimpl (env, n1, n2) in
        eqns1 @ eqns2 @ eqns3
      (* session *)
      | Proto, Proto -> []
      | End rol1, End rol2 when rol1 = rol2 -> []
      | Act (rel1, rol1, a1, abs1), Act (rel2, rol2, a2, abs2)
        when rel1 = rel2 && rol1 = rol2 ->
        let _, b1, b2 = unbind2_tm abs1 abs2 in
        let eqns1 = asimpl (env, a1, a2) in
        let eqns2 = asimpl (env, b1, b2) in
        eqns1 @ eqns2
      | Ch (rol1, a1), Ch (rol2, a2)
        when rol1 = rol2 -> asimpl (env, a1, a2)
      | Open prim1, Open prim2 when prim1 = prim2 ->  []
      | Fork (a1, abs1), Fork (a2, abs2) ->
        let _, m1, m2 = unbind2_tm abs1 abs2 in
        let eqns1 = asimpl (env, a1, a2) in
        let eqns2 = asimpl (env, m1, m2) in
        eqns1 @ eqns2
      | Recv (rel1, m1), Recv (rel2, m2)
        when rel1 = rel2 -> asimpl (env, m1, m2)
      | Send (rel1, m1), Send (rel2, m2)
        when rel1 = rel2 -> asimpl (env, m1, m2)
      | Close m1, Close m2 -> asimpl (env, m1, m2)
      | _ -> failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2
    in
    eqns_h @ eqns_sp

let rec simpl (env, m1, m2) =
  try asimpl (env, m1, m2) with
  | _ ->
    let m1 = whnf [Beta; Iota; Zeta] env m1 in
    let m2 = whnf [Beta; Iota; Zeta] env m2 in
    let h1, sp1 = unApps m1 in
    let h2, sp2 = unApps m2 in
    let eqns_sp =
      try
        List.fold_left2
          (fun acc m n -> acc @ simpl (env, m, n))
          [] sp1 sp2
      with _ -> []
    in
    let eqns_h =
      match h1, h2 with
      (* inference *)
      | Meta _, _ -> [(env, m1, m2)]
      | _, Meta _ -> [(env, m2, m1)]
      (* core *)
      | Type _, Type _ -> []
      | Var _, Var _ -> []
      | Var x, _ ->
        (match VMap.find_opt x env with
         | Some m1 -> simpl (env, mkApps m1 sp1, m2)
         | None -> [])
      | _, Var y ->
        (match VMap.find_opt y env with
         | Some m2 -> simpl (env, m1, mkApps m2 sp2)
         | None -> [])
      | Pi (rel1, s1, a1, abs1), Pi (rel2, s2, a2, abs2)
        when rel1 = rel2 && s1 = s2 ->
        let _, b1, b2 = unbind2_tm abs1 abs2 in
        let eqns1 = simpl (env, a1, a2) in
        let eqns2 = simpl (env, b1, b2) in
        eqns1 @ eqns2
      | Lam (rel1, s1, abs1), Lam (rel2, s2, abs2)
        when rel1 = rel2 && s1 = s2 ->
        let (_, a1_opt, a2_opt), m1, m2 = unbind2_ann abs1 abs2 in
        let eqns1 =
          match a1_opt, a2_opt with
          | Some a1, Some a2 -> simpl (env, a1, a2)
          | _ -> []
        in
        let eqns2 = simpl (env, m1, m2) in
        eqns1 @ eqns2
      | App (m1, n1), App (m2, n2) ->
        let eqns1 = simpl (env, m1, m2) in
        let eqns2 = simpl (env, n1, n2) in
        eqns1 @ eqns2
      | Let (rel1, m1, abs1), Let (rel2, m2, abs2)
        when rel1 = rel2->
        let (_, a1_opt, a2_opt), n1, n2 = unbind2_ann abs1 abs2 in
        let eqns1 = simpl (env, m1, m2) in
        let eqns2 =
          match a1_opt, a2_opt with
          | Some a1, Some a2 -> simpl (env, a1, a2)
          | _ -> []
        in
        let eqns3 = simpl (env, n1, n2) in
        eqns1 @ eqns2 @ eqns3
      (* data *)
      | Sig (rel1, s1, a1, abs1), Sig (rel2, s2, a2, abs2)
        when rel1 = rel2 && s1 = s2->
        let _, b1, b2 = unbind2_tm abs1 abs2 in
        let eqns1 = simpl (env, a1, a2) in
        let eqns2 = simpl (env, b1, b2) in
        eqns1 @ eqns2
      | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2)
        when rel1 = rel2 && s1 = s2->
        let eqns1 = simpl (env, m1, m2) in
        let eqns2 = simpl (env, n1, n2) in
        eqns1 @ eqns2
      | Data (d1, ms1), Data (d2, ms2) when D.equal d1 d2 ->
        List.fold_left2
          (fun acc m1 m2 -> acc @ simpl (env, m1, m2))
          [] ms1 ms2
      | Cons (c1, ms1), Cons (c2, ms2) when C.equal c1 c2 ->
        List.fold_left2
          (fun acc m1 m2 -> acc @ simpl (env, m1, m2))
          [] ms1 ms2
      | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
        let eqns1 = simpl (env, m1, m2) in
        let eqns2 = 
          match mot1, mot2 with
          | Some abs1, Some abs2 ->
            let _, a1, a2 = unbind2_tm abs1 abs2 in
            simpl (env, a1, a2)
          | _ -> []
        in
        let eqns3 =
          List.fold_left2
            (fun acc pabs1 pabs2 ->
               let _, n1, n2 = unbindp2_tm pabs1 pabs2 in
               acc @ simpl (env, n1, n2))
            [] cls1 cls2
        in
        eqns1 @ eqns2 @ eqns3
      (* equality *)
      | Eq (m1, n1), Eq (m2, n2) ->
        let eqns1 = simpl (env, m1, m2) in
        let eqns2 = simpl (env, n1, n2) in
        eqns1 @ eqns2
      | Refl, Refl -> []
      | Rew (abs1, pf1, m1), Rew (abs2, pf2, m2) ->
        let (_, _), a1, a2 = unbind2_tm2 abs1 abs2 in
        let eqns1 = simpl (env, a1, a2) in
        let eqns2 = simpl (env, pf1, pf2) in
        let eqns3 = simpl (env, m1, m2) in
        eqns1 @ eqns2 @ eqns3
      (* monadic *)
      | IO a1, IO a2 -> simpl (env, a1, a2)
      | Return m1, Return m2 -> simpl (env, m1, m2)
      | Do (m1, abs1), Do (m2, abs2) ->
        let (_, a1_opt, a2_opt), n1, n2 = unbind2_ann abs1 abs2 in
        let eqns1 = simpl (env, m1, m2) in
        let eqns2 =
          match a1_opt, a2_opt with
          | Some a1, Some a2 -> simpl (env, a1, a2)
          | _ -> []
        in
        let eqns3 = simpl (env, n1, n2) in
        eqns1 @ eqns2 @ eqns3
      (* session *)
      | Proto, Proto -> []
      | End rol1, End rol2 when rol1 = rol2 -> []
      | Act (rel1, rol1, a1, abs1), Act (rel2, rol2, a2, abs2)
        when rel1 = rel2 && rol1 = rol2 -> 
        let _, b1, b2 = unbind2_tm abs1 abs2 in
        let eqns1 = simpl (env, a1, a2) in
        let eqns2 = simpl (env, b1, b2) in
        eqns1 @ eqns2
      | Ch (rol1, a1), Ch (rol2, a2)
        when rol1 = rol2 -> simpl (env, a1, a2)
      | Open prim1, Open prim2 when prim1 = prim2 -> []
      | Fork (a1, abs1), Fork (a2, abs2) ->
        let _, m1, m2 = unbind2_tm abs1 abs2 in
        let eqns1 = simpl (env, a1, a2) in
        let eqns2 = simpl (env, m1, m2) in
        eqns1 @ eqns2
      | Recv (rel1, m1), Recv (rel2, m2)
        when rel1 = rel2 -> simpl (env, m1, m2)
      | Send (rel1, m1), Send (rel2, m2)
        when rel1 = rel2 -> simpl (env, m1, m2)
      | Close m1, Close m2 -> simpl (env, m1, m2)
      | _ -> []
    in
    eqns_h @ eqns_sp


let solve map (env, m1, m2) =
  let meta_spine sp =
    List.map 
      (function
        | Var x-> x
        | _ -> V.blank ())
      sp
  in
  let m1 = whnf [Beta; Iota; Zeta] env m1 in
  let m2 = whnf [Beta; Iota; Zeta] env m2 in
  match m1, m2 with
  | Meta _, Meta _ -> map
  | Meta (x, xs), _ ->
    if occurs x m2 then
      map
    else
      let xs = meta_spine xs in
      if VSet.subset (fv VSet.empty m2) (VSet.of_list xs) then
        let args = List.map (fun x -> (x, None)) xs in
        let m = mLam R U args m2 in
        MMap.add x (Some m, None) map
      else
        map
  | _ -> map
