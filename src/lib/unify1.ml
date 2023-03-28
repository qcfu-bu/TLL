open Fmt
open Bindlib
open Names
open Syntax1
open Equality1

type eqn = tm VMap.t * tm * tm
type eqns = eqn list
type map = ((tm, tm) mbinder option * tm option) MMap.t

let rec fv ctx = function
  (* inference *)
  | Ann (m, a) -> VSet.union (fv ctx m) (fv ctx a)
  | Meta (_, ms) ->
    List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  (* core *)
  | Type _ -> VSet.empty
  | Var x -> (
    match VSet.find_opt x ctx with
    | Some _ -> VSet.empty
    | None -> VSet.singleton x)
  | Pi (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Lam (_, _, bnd) ->
    let x, m = unbind bnd in
    fv (VSet.add x ctx) m
  | App (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let fv1 = fv ctx m in
    let fv2 = fv (VSet.add x ctx) n in
    VSet.union fv1 fv2
  | Fix (_, bnd) ->
    let r, m = unbind bnd in
    fv (VSet.add r ctx) m
  (* data *)
  | Sigma (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Pair (_, _, m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Data (_, ms) ->
    List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
  | Cons (_, ms, ns) ->
    List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty (ms @ ns)
  | Match (m, bnd, cls) ->
    let x, mot = unbind bnd in
    let fv1 = fv ctx m in
    let fv2 = fv (VSet.add x ctx) mot in
    let fv3 =
      List.fold_left
        (fun acc cl ->
          match cl with
          | PPair (_, _, bnd) ->
            let xs, m = unmbind bnd in
            fv (Array.fold_right VSet.add xs ctx) m
          | PCons (_, bnd) ->
            let xs, m = unmbind bnd in
            fv (Array.fold_right VSet.add xs ctx) m)
        VSet.empty cls
    in
    VSet.union (VSet.union fv1 fv2) fv3
  (* equality *)
  | Eq (a, m, n) -> VSet.union (VSet.union (fv ctx a) (fv ctx m)) (fv ctx n)
  | Refl m -> fv ctx m
  | Rew (bnd, pf, m) ->
    let xs, a = unmbind bnd in
    let fv1 = fv (Array.fold_right VSet.add xs ctx) a in
    let fv2 = fv ctx pf in
    let fv3 = fv ctx m in
    VSet.union (VSet.union fv1 fv2) fv3
  (* monadic *)
  | IO a -> fv ctx a
  | Return m -> fv ctx m
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let fv1 = fv ctx m in
    let fv2 = fv (VSet.add x ctx) n in
    VSet.union fv1 fv2
  (* session *)
  | Proto -> VSet.empty
  | End -> VSet.empty
  | Act (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) b in
    VSet.union fv1 fv2
  | Ch (_, a) -> fv ctx a
  | Open _ -> VSet.empty
  | Fork (a, bnd) ->
    let x, m = unbind bnd in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) m in
    VSet.union fv1 fv2
  | Recv m -> fv ctx m
  | Send m -> fv ctx m
  | Close m -> fv ctx m

let rec occurs x = function
  (* inference *)
  | Ann (m, a) -> occurs x m || occurs x a
  | Meta (y, _) -> M.equal x y
  (* core *)
  | Pi (_, _, a, bnd) ->
    let _, b = unbind bnd in
    occurs x a || occurs x b
  | Lam (_, _, bnd) ->
    let _, m = unbind bnd in
    occurs x m
  | App (m, n) -> occurs x m || occurs x n
  | Let (_, m, bnd) ->
    let _, n = unbind bnd in
    occurs x m || occurs x n
  | Fix (_, bnd) ->
    let _, m = unbind bnd in
    occurs x m
  (* data *)
  | Sigma (_, _, a, bnd) ->
    let _, b = unbind bnd in
    occurs x a || occurs x b
  | Pair (_, _, m, n) -> occurs x m || occurs x n
  | Data (_, ms) -> List.exists (occurs x) ms
  | Cons (_, ms, ns) -> List.exists (occurs x) (ms @ ns)
  | Match (m, bnd, cls) ->
    let _, a = unbind bnd in
    occurs x m || occurs x a
    || List.exists
         (function
           | PPair (_, _, bnd) ->
             let _, m = unmbind bnd in
             occurs x m
           | PCons (_, bnd) ->
             let _, m = unmbind bnd in
             occurs x m)
         cls
  (* equality *)
  | Eq (a, m, n) -> occurs x a || occurs x m || occurs x n
  | Refl m -> occurs x m
  | Rew (bnd, pf, m) ->
    let _, a = unmbind bnd in
    occurs x a || occurs x pf || occurs x m
  (* monadic *)
  | IO a -> occurs x a
  | Return m -> occurs x m
  | MLet (m, bnd) ->
    let _, n = unbind bnd in
    occurs x m || occurs x n
  (* session *)
  | Act (_, _, a, bnd) ->
    let _, b = unbind bnd in
    occurs x a || occurs x b
  | Ch (_, a) -> occurs x a
  | Fork (a, bnd) ->
    let _, m = unbind bnd in
    occurs x a || occurs x m
  | Recv m -> occurs x m
  | Send m -> occurs x m
  | Close m -> occurs x m
  (* other *)
  | _ -> false

let rec asimpl (env, m1, m2) =
  if equal [| Beta; Zeta; Iota |] env m1 m2 then
    []
  else
    match (m1, m2) with
    (* inference *)
    | Meta _, _ -> [ (env, m1, m2) ]
    | _, Meta _ -> [ (env, m2, m1) ]
    (* core *)
    | Type s1, Type s2 when s1 = s2 -> []
    | Var x1, Var x2 when eq_vars x1 x2 -> []
    | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2)
      when rel1 = rel2 && s1 = s2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = asimpl (env, a1, a2) in
      let eqns2 = asimpl (env, b1, b2) in
      eqns1 @ eqns2
    | Lam (rel1, s1, bnd1), Lam (rel2, s2, bnd2) when rel1 = rel2 && s1 = s2 ->
      let _, m1, m2 = unbind2 bnd1 bnd2 in
      asimpl (env, m1, m2)
    | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) when rel1 = rel2 ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = asimpl (env, m1, m2) in
      let eqns2 = asimpl (env, n1, n2) in
      eqns1 @ eqns2
    | App _, App _ ->
      let hd1, sp1 = unApps m1 in
      let hd2, sp2 = unApps m2 in
      let eqns1 = asimpl (env, hd1, hd2) in
      let eqns2 =
        List.fold_right2 (fun m n acc -> asimpl (env, m, n) @ acc) sp1 sp2 []
      in
      eqns1 @ eqns2
    | Fix (_, bnd1), Fix (_, bnd2) ->
      let _, m1, m2 = unbind2 bnd1 bnd2 in
      asimpl (env, m1, m2)
    (* data *)
    | Sigma (rel1, s1, a1, bnd1), Sigma (rel2, s2, a2, bnd2)
      when rel1 = rel2 && s1 = s2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = asimpl (env, a1, a2) in
      let eqns2 = asimpl (env, b1, b2) in
      eqns1 @ eqns2
    | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2)
      when rel1 = rel2 && s1 = s2 ->
      let eqns1 = asimpl (env, m1, m2) in
      let eqns2 = asimpl (env, n1, n2) in
      eqns1 @ eqns2
    | Data (d1, ms1), Data (d2, ms2) when D.equal d1 d2 ->
      List.fold_right2 (fun m1 m2 acc -> asimpl (env, m1, m2) @ acc) ms1 ms2 []
    | Cons (c1, ms1, ns1), Cons (c2, ms2, ns2) when C.equal c1 c2 ->
      List.fold_right2
        (fun m1 m2 acc -> asimpl (env, m1, m2) @ acc)
        (ms1 @ ns1) (ms2 @ ns2) []
    | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
      let _, mot1, mot2 = unbind2 bnd1 bnd2 in
      let eqns1 = asimpl (env, m1, m2) in
      let eqns2 = asimpl (env, mot1, mot2) in
      let eqns3 =
        List.fold_right2
          (fun cl1 cl2 acc ->
            match (cl1, cl2) with
            | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2)
              when rel1 = rel2 && s1 = s2 ->
              let _, m1, m2 = unmbind2 bnd1 bnd2 in
              asimpl (env, m1, m2) @ acc
            | PCons (c1, bnd1), PCons (c2, bnd2) when C.equal c1 c2 ->
              let _, m1, m2 = unmbind2 bnd1 bnd2 in
              asimpl (env, m1, m2) @ acc
            | _ -> failwith "asimpl")
          cls1 cls2 []
      in
      eqns1 @ eqns2 @ eqns3
    (* equality *)
    | Eq (a1, m1, n1), Eq (a2, m2, n2) ->
      let eqns1 = asimpl (env, a1, a2) in
      let eqns2 = asimpl (env, m1, m2) in
      let eqns3 = asimpl (env, n1, n2) in
      eqns1 @ eqns2 @ eqns3
    | Refl m1, Refl m2 -> asimpl (env, m1, m2)
    | Rew (bnd1, pf1, m1), Rew (bnd2, pf2, m2) ->
      let _, a1, a2 = unmbind2 bnd1 bnd2 in
      let eqns1 = asimpl (env, a1, a2) in
      let eqns2 = asimpl (env, pf1, pf2) in
      let eqns3 = asimpl (env, m1, m2) in
      eqns1 @ eqns2 @ eqns3
    (* monadic *)
    | IO a1, IO a2 -> asimpl (env, a1, a2)
    | Return m1, Return m2 -> asimpl (env, m1, m2)
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = asimpl (env, m1, m2) in
      let eqns2 = asimpl (env, n1, n2) in
      eqns1 @ eqns2
    (* session *)
    | Proto, Proto -> []
    | End, End -> []
    | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2)
      when rel1 = rel2 && rol1 = rol2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = asimpl (env, a1, a2) in
      let eqns2 = asimpl (env, b1, b2) in
      eqns1 @ eqns2
    | Ch (rol1, a1), Ch (rol2, a2) when rol1 = rol2 -> asimpl (env, a1, a2)
    | Open prim1, Open prim2 when prim1 = prim2 -> []
    | Fork (a1, bnd1), Fork (a2, bnd2) ->
      let _, m1, m2 = unbind2 bnd1 bnd2 in
      let eqns1 = asimpl (env, a1, a2) in
      let eqns2 = asimpl (env, m1, m2) in
      eqns1 @ eqns2
    | Recv m1, Recv m2 -> asimpl (env, m1, m2)
    | Send m1, Send m2 -> asimpl (env, m1, m2)
    | Close m1, Close m2 -> asimpl (env, m1, m2)
    (* other *)
    | _ -> failwith "asimpl"

let rec simpl (env, m1, m2) =
  try asimpl (env, m1, m2) with
  | _ -> (
    let m1 = whnf [| Beta; Iota; Zeta |] env m1 in
    let m2 = whnf [| Beta; Iota; Zeta |] env m2 in
    match (m1, m2) with
    (* inference *)
    | Meta _, _ -> [ (env, m1, m2) ]
    | _, Meta _ -> [ (env, m2, m1) ]
    (* core *)
    | Type s1, Type s2 when s1 = s2 -> []
    | Var x1, Var x2 when eq_vars x1 x2 -> []
    | Var x, _ -> (
      match VMap.find_opt x env with
      | Some m1 -> simpl (env, m1, m2)
      | None -> [])
    | _, Var y -> (
      match VMap.find_opt y env with
      | Some m2 -> simpl (env, m1, m2)
      | None -> [])
    | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2)
      when rel1 = rel2 && s1 = s2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (env, a1, a2) in
      let eqns2 = simpl (env, b1, b2) in
      eqns1 @ eqns2
    | Lam (rel1, s1, bnd1), Lam (rel2, s2, bnd2) when rel1 = rel2 && s1 = s2 ->
      let _, m1, m2 = unbind2 bnd1 bnd2 in
      simpl (env, m1, m2)
    | App _, App _ ->
      let hd1, sp1 = unApps m1 in
      let hd2, sp2 = unApps m2 in
      let eqns1 = simpl (env, hd1, hd2) in
      let eqns2 =
        List.fold_right2 (fun m n acc -> simpl (env, m, n) @ acc) sp1 sp2 []
      in
      eqns1 @ eqns2
    | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) when rel1 = rel2 ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (env, m1, m2) in
      let eqns2 = simpl (env, n1, n2) in
      eqns1 @ eqns2
    | Fix (_, bnd1), Fix (_, bnd2) ->
      let _, m1, m2 = unbind2 bnd1 bnd2 in
      simpl (env, m1, m2)
    (* data *)
    | Sigma (rel1, s1, a1, bnd1), Sigma (rel2, s2, a2, bnd2)
      when rel1 = rel2 && s1 = s2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (env, a1, a2) in
      let eqns2 = simpl (env, b1, b2) in
      eqns1 @ eqns2
    | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2)
      when rel1 = rel2 && s1 = s2 ->
      let eqns1 = simpl (env, m1, m2) in
      let eqns2 = simpl (env, n1, n2) in
      eqns1 @ eqns2
    | Data (d1, ms1), Data (d2, ms2) when D.equal d1 d2 ->
      List.fold_right2 (fun m1 m2 acc -> simpl (env, m1, m2) @ acc) ms1 ms2 []
    | Cons (c1, ms1, ns1), Cons (c2, ms2, ns2) when C.equal c1 c2 ->
      List.fold_right2
        (fun m1 m2 acc -> simpl (env, m1, m2) @ acc)
        (ms1 @ ns1) (ms2 @ ns2) []
    | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
      let _, mot1, mot2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (env, m1, m2) in
      let eqns2 = simpl (env, mot1, mot2) in
      let eqns3 =
        List.fold_right2
          (fun cl1 cl2 acc ->
            match (cl1, cl2) with
            | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2)
              when rel1 = rel2 && s1 = s2 ->
              let _, m1, m2 = unmbind2 bnd1 bnd2 in
              simpl (env, m1, m2) @ acc
            | PCons (c1, bnd1), PCons (c2, bnd2) when C.equal c1 c2 ->
              let _, m1, m2 = unmbind2 bnd1 bnd2 in
              simpl (env, m1, m2) @ acc
            | _ -> acc)
          cls1 cls2 []
      in
      eqns1 @ eqns2 @ eqns3
    (* equality *)
    | Eq (a1, m1, n1), Eq (a2, m2, n2) ->
      let eqns1 = simpl (env, a1, a2) in
      let eqns2 = simpl (env, m1, m2) in
      let eqns3 = simpl (env, n1, n2) in
      eqns1 @ eqns2 @ eqns3
    | Refl m1, Refl m2 -> simpl (env, m1, m2)
    | Rew (bnd1, pf1, m1), Rew (bnd2, pf2, m2) ->
      let _, a1, a2 = unmbind2 bnd1 bnd2 in
      let eqns1 = simpl (env, a1, a2) in
      let eqns2 = simpl (env, pf1, pf2) in
      let eqns3 = simpl (env, m1, m2) in
      eqns1 @ eqns2 @ eqns3
    (* monadic *)
    | IO a1, IO a2 -> simpl (env, a1, a2)
    | Return m1, Return m2 -> simpl (env, m1, m2)
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (env, m1, m2) in
      let eqns2 = simpl (env, n1, n2) in
      eqns1 @ eqns2
    (* session *)
    | Proto, Proto -> []
    | End, End -> []
    | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2)
      when rel1 = rel2 && rol2 = rol2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (env, a1, a2) in
      let eqns2 = simpl (env, b1, b2) in
      eqns1 @ eqns2
    | Ch (rol1, a1), Ch (rol2, a2) when rol1 = rol2 -> simpl (env, a1, a2)
    | Open prim1, Open prim2 when prim1 = prim2 -> []
    | Fork (a1, bnd1), Fork (a2, bnd2) ->
      let _, m1, m2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (env, a1, a2) in
      let eqns2 = simpl (env, m1, m2) in
      eqns1 @ eqns2
    | Recv m1, Recv m2 -> simpl (env, m1, m2)
    | Send m1, Send m2 -> simpl (env, m1, m2)
    | Close m1, Close m2 -> simpl (env, m1, m2)
    | _ -> [])

let solve (map : map) (env, m1, m2) =
  let meta_spine sp =
    List.map
      (function
        | Var x -> x
        | _ -> mk "_")
      sp
  in
  let m1 = whnf [| Beta; Iota; Zeta |] env m1 in
  let m2 = whnf [| Beta; Iota; Zeta |] env m2 in
  match (m1, m2) with
  | Meta _, Meta _ -> map
  | Meta (x, xs), _ ->
    if occurs x m2 then
      map
    else
      let xs = meta_spine xs in
      if VSet.subset (fv VSet.empty m2) (VSet.of_list xs) then
        let m = bind_mvar (Array.of_list xs) (lift_tm m2) in
        MMap.add x (Some (unbox m), None) map
      else
        map
  | _ -> map

let rec resolve_tm (map : map) m =
  match m with
  (* inference *)
  | Meta (x, ms) -> (
    match MMap.find_opt x map with
    | Some (Some bnd, _) ->
      let m = msubst bnd (Array.of_list ms) in
      resolve_tm map m
    | _ -> m)
  | Ann (m, a) -> Ann (resolve_tm map m, resolve_tm map a)
  (* core *)
  | Pi (rel, s, a, bnd) ->
    let x, b = unbind bnd in
    let a = resolve_tm map a in
    let b = lift_tm (resolve_tm map b) in
    Pi (rel, s, a, unbox (bind_var x b))
  | Lam (rel, s, bnd) ->
    let x, m = unbind bnd in
    let m = lift_tm (resolve_tm map m) in
    Lam (rel, s, unbox (bind_var x m))
  | App (m, n) -> Ann (resolve_tm map m, resolve_tm map n)
  | Let (rel, m, bnd) ->
    let x, n = unbind bnd in
    let m = resolve_tm map m in
    let n = lift_tm (resolve_tm map n) in
    Let (rel, m, unbox (bind_var x n))
  | Fix (r, bnd) ->
    let x, m = unbind bnd in
    let m = lift_tm (resolve_tm map m) in
    Fix (r, unbox (bind_var x m))
  (* data *)
  | Sigma (rel, s, a, bnd) ->
    let x, b = unbind bnd in
    let a = resolve_tm map a in
    let b = lift_tm (resolve_tm map b) in
    Sigma (rel, s, a, unbox (bind_var x b))
  | Pair (rel, s, m, n) -> Pair (rel, s, resolve_tm map m, resolve_tm map n)
  | Data (d, ms) ->
    let ms = List.map (resolve_tm map) ms in
    Data (d, ms)
  | Cons (c, ns, ms) ->
    let ns = List.map (resolve_tm map) ns in
    let ms = List.map (resolve_tm map) ms in
    Cons (c, ns, ms)
  | Match (m, bnd, cls) ->
    let x, a = unbind bnd in
    let m = resolve_tm map m in
    let a = lift_tm (resolve_tm map a) in
    let cls =
      List.map
        (function
          | PPair (rel, s, bnd) ->
            let xs, n = unmbind bnd in
            let n = lift_tm (resolve_tm map n) in
            PPair (rel, s, unbox (bind_mvar xs n))
          | PCons (c, bnd) ->
            let xs, n = unmbind bnd in
            let n = lift_tm (resolve_tm map n) in
            PCons (c, unbox (bind_mvar xs n)))
        cls
    in
    Match (m, unbox (bind_var x a), cls)
  (* equality *)
  | Eq (a, m, n) -> Eq (resolve_tm map a, resolve_tm map m, resolve_tm map n)
  | Refl m -> Refl (resolve_tm map m)
  | Rew (bnd, pf, m) ->
    let xs, a = unmbind bnd in
    let a = lift_tm (resolve_tm map a) in
    let pf = resolve_tm map pf in
    let m = resolve_tm map m in
    Rew (unbox (bind_mvar xs a), pf, m)
  (* monadic *)
  | IO a -> IO (resolve_tm map a)
  | Return m -> Return (resolve_tm map m)
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let m = resolve_tm map m in
    let n = lift_tm (resolve_tm map n) in
    MLet (m, unbox (bind_var x n))
  (* session *)
  | Act (rel, rol, a, bnd) ->
    let x, b = unbind bnd in
    let a = resolve_tm map a in
    let b = lift_tm (resolve_tm map b) in
    Act (rel, rol, a, unbox (bind_var x b))
  | Ch (rol, a) -> Ch (rol, resolve_tm map a)
  | Fork (a, bnd) ->
    let x, m = unbind bnd in
    let a = resolve_tm map a in
    let m = lift_tm (resolve_tm map m) in
    Fork (a, unbox (bind_var x m))
  | Recv m -> Recv (resolve_tm map m)
  | Send m -> Send (resolve_tm map m)
  | Close m -> Close (resolve_tm map m)
  (* other *)
  | _ -> m

let rec resolve_param lift resolve map = function
  | PBase a -> PBase (resolve map a)
  | PBind (a, bnd) ->
    let x, b = unbind bnd in
    let a = resolve_tm map a in
    let b = lift_param lift (resolve_param lift resolve map b) in
    PBind (a, unbox (bind_var x b))

let rec resolve_tele map = function
  | TBase a -> TBase (resolve_tm map a)
  | TBind (rel, a, bnd) ->
    let x, b = unbind bnd in
    let a = resolve_tm map a in
    let b = lift_tele (resolve_tele map b) in
    TBind (rel, a, unbox (bind_var x b))

let resolve_dcons map (DCons (c, ptl)) =
  DCons (c, resolve_param lift_tele resolve_tele map ptl)

let resolve_dcl map dcl =
  match dcl with
  | DTm (rel, x, a, m) ->
    let a = resolve_tm map a in
    let m = resolve_tm map m in
    DTm (rel, x, a, m)
  | DData (d, ptm, dconss) ->
    let ptm = resolve_param lift_tm resolve_tm map ptm in
    let dconss = List.map (resolve_dcons map) dconss in
    DData (d, ptm, dconss)

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
