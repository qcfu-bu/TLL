open Fmt
open Bindlib
open Names
open Syntax1
open Equality1

type eqn = tm VMap.t * tm * tm
type eqns = eqn list
type map = (tm option * tm option) MMap.t

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
  | Cons (_, ms) ->
      List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
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
  | Eq (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Refl -> VSet.empty
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
  | End _ -> VSet.empty
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
  | Recv (_, m) -> fv ctx m
  | Send (_, m) -> fv ctx m
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
  | Cons (_, ms) -> List.exists (occurs x) ms
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
  | Eq (m, n) -> occurs x m || occurs x n
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
  | Recv (_, m) -> occurs x m
  | Send (_, m) -> occurs x m
  | Close m -> occurs x m
  (* other *)
  | _ -> false

let rec asimpl (env, m1, m2) =
  if equal [| Beta; Zeta; Iota |] env m1 m2 then []
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
        List.fold_right2
          (fun m1 m2 acc -> asimpl (env, m1, m2) @ acc)
          ms1 ms2 []
    | Cons (c1, ms1), Cons (c2, ms2) when C.equal c1 c2 ->
        List.fold_right2
          (fun m1 m2 acc -> asimpl (env, m1, m2) @ acc)
          ms1 ms2 []
    | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
        let _, mot1, mot2 = unbind2 bnd1 bnd2 in
        let eqns1 = asimpl (env, m1, m2) in
        let eqns2 = asimpl (env, mot1, mot2) in
        let eqns3 =
          List.fold_left2
            (fun acc cl1 cl2 ->
              match (cl1, cl2) with
              | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2)
                when rel1 = rel2 && s1 = s2 ->
                  let _, m1, m2 = unmbind2 bnd1 bnd2 in
                  asimpl (env, m1, m2)
              | PCons (c1, bnd1), PCons (c2, bnd2) when C.equal c1 c2 ->
                  let _, m1, m2 = unmbind2 bnd1 bnd2 in
                  asimpl (env, m1, m2)
              | _ -> failwith "asimpl")
            [] cls1 cls2
        in
        eqns1 @ eqns2 @ eqns3
    (* equality *)
    (* monadic *)
    (* session *)
    | _ -> failwith "asimpl"
