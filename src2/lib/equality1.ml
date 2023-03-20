open Bindlib
open Names
open Syntax1

type rd = Beta | Delta | Zeta | Iota

let enabled mode rd = Array.exists (( = ) rd) mode

let rec whnf mode env = function
  (* inference *)
  | Ann (m, a) -> whnf mode env m
  (* core *)
  | Var x ->
      if enabled mode Delta then
        match VMap.find_opt x env with
        | Some m -> whnf mode env m
        | None -> Var x
      else Var x
  | App (m, n) ->
      let m = whnf mode env m in
      let n = whnf mode env n in
      if enabled mode Beta then
        match (m, n) with
        | Lam (_, _, bnd), _ -> whnf mode env (subst bnd n)
        | Fix (r, bnd), Cons _ -> whnf mode env (App (subst bnd (Var r), n))
        | _ -> App (m, n)
      else App (m, n)
  | Let (r, m, bnd) ->
      if enabled mode Zeta then
        let m = whnf mode env m in
        let x, n = unbind bnd in
        whnf mode (VMap.add x m env) n
      else Let (r, m, bnd)
  (* data *)
  | Match (m, mot, cls) ->
      let m = whnf mode env m in
      if enabled mode Iota then
        match match_cls cls m with
        | Some m -> whnf mode env m
        | _ -> Match (m, mot, cls)
      else Match (m, mot, cls)
  (* equality *)
  | Rew (bnd, pf, m) -> (
      let pf = whnf mode env pf in
      match pf with Refl -> whnf mode env m | _ -> Rew (bnd, pf, m))
  (* monadic *)
  | MLet (m, bnd) ->
      if enabled mode Zeta then
        let m = whnf mode env m in
        match m with
        | Return m ->
            let x, n = unbind bnd in
            whnf mode (VMap.add x m env) n
        | _ -> MLet (m, bnd)
      else MLet (m, bnd)
  (* other *)
  | m -> m

and match_cls cls m =
  Array.fold_left
    (fun acc cl ->
      Option.fold
        ~some:(fun _ -> acc)
        ~none:
          (match (cl, m) with
          | PPair (rel1, s1, bnd), Pair (rel2, s2, m1, m2)
            when rel1 = rel2 && s1 = s2 ->
              Some (msubst bnd [| m1; m2 |])
          | PCons (c1, bnd), Cons (c2, ms) when C.equal c1 c2 ->
              Some (msubst bnd ms)
          | _ -> acc)
        acc)
    None cls

let rec aeq m1 m2 =
  if m1 == m2 then true
  else
    match (m1, m2) with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) -> aeq m1 m2 && aeq a1 a2
    | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
    (* core *)
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> eq_vars x1 x2
    | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && s1 = s2 && aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Lam (rel1, s1, bnd1), Lam (rel2, s2, bnd2) ->
        rel1 = rel2 && s1 = s2 && eq_binder aeq bnd1 bnd2
    | App (m1, n1), App (m2, n2) -> aeq m1 m2 && aeq n1 n2
    | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) ->
        rel1 = rel2 && aeq m1 m2 && eq_binder aeq bnd1 bnd2
    | Fix (_, bnd1), Fix (_, bnd2) -> eq_binder aeq bnd1 bnd2
    (* data *)
    | Sigma (rel1, s1, a1, bnd1), Sigma (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && s1 = s2 && aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2) ->
        rel1 = rel2 && s1 = s2 && aeq m1 m2 && aeq n1 n2
    | Data (d1, ms1), Data (d2, ms2) ->
        D.equal d1 d2 && Array.for_all2 aeq ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) ->
        C.equal c1 c2 && Array.for_all2 aeq ms1 ms2
    | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
        aeq m1 m2 && eq_binder aeq bnd1 bnd2
        && Array.for_all2
             (fun cl1 cl2 ->
               match (cl1, cl2) with
               | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2) ->
                   rel1 = rel2 && s1 = s2 && eq_mbinder aeq bnd1 bnd2
               | PCons (c1, bnd1), PCons (c2, bnd2) ->
                   C.equal c1 c2 && eq_mbinder aeq bnd1 bnd2
               | _ -> false)
             cls1 cls2
    (* equality *)
    | Eq (m1, n1), Eq (m2, n2) -> aeq m1 m2 && aeq n1 n2
    | Refl, Refl -> true
    | Rew (bnd1, pf1, m1), Rew (bnd2, pf2, m2) ->
        eq_mbinder aeq bnd1 bnd2 && aeq pf1 pf2
    (* monadic *)
    | IO a1, IO a2 -> aeq a1 a2
    | Return m1, Return m2 -> aeq m1 m2
    | MLet (m1, bnd1), MLet (m2, bnd2) -> aeq m1 m2 && eq_binder aeq bnd1 bnd2
    (* session *)
    | Proto, Proto -> true
    | End rol1, End rol2 -> rol1 = rol2
    | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2) ->
        rel1 = rel2 && rol1 = rol2 && aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Ch (rol1, a1), Ch (rol2, a2) -> rol1 = rol2 && aeq a1 a2
    | Open prim1, Open prim2 -> prim1 = prim2
    | Fork (a1, bnd1), Fork (a2, bnd2) -> aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Recv (rol1, m1), Recv (rol2, m2) -> rol1 = rol2 && aeq m1 m2
    | Send (rol1, m1), Send (rol2, m2) -> rol1 = rol2 && aeq m1 m2
    | Close m1, Close m2 -> aeq m1 m2
    (* other *)
    | _ -> false

let rec equal mode env m1 m2 =
  if aeq m1 m2 then true
  else
    let m1 = whnf mode env m1 in
    let m2 = whnf mode env m2 in
    match (m1, m2) with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) -> equal mode env m1 m2 && equal mode env a1 a2
    | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
    (* core *)
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> eq_vars x1 x2
    | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && s1 = s2 && equal mode env a1 a2
        && eq_binder (equal mode env) bnd1 bnd2
    | Lam (rel1, s1, bnd1), Lam (rel2, s2, bnd2) ->
        rel1 = rel2 && s1 = s2 && eq_binder (equal mode env) bnd1 bnd2
    | App (m1, n1), App (m2, n2) -> equal mode env m1 m2 && equal mode env n1 n2
    | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) ->
        rel1 = rel2 && equal mode env m1 m2
        && eq_binder (equal mode env) bnd1 bnd2
    | Fix (_, bnd1), Fix (_, bnd2) -> eq_binder (equal mode env) bnd1 bnd2
    (* data *)
    | Sigma (rel1, s1, a1, bnd1), Sigma (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && s1 = s2 && equal mode env a1 a2
        && eq_binder (equal mode env) bnd1 bnd2
    | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2) ->
        rel1 = rel2 && s1 = s2 && equal mode env m1 m2 && equal mode env n1 n2
    | Data (d1, ms1), Data (d2, ms2) ->
        D.equal d1 d2 && Array.for_all2 (equal mode env) ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) ->
        C.equal c1 c2 && Array.for_all2 (equal mode env) ms1 ms2
    | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
        equal mode env m1 m2
        && eq_binder (equal mode env) bnd1 bnd2
        && Array.for_all2
             (fun cl1 cl2 ->
               match (cl1, cl2) with
               | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2) ->
                   rel1 = rel2 && s1 = s2
                   && eq_mbinder (equal mode env) bnd1 bnd2
               | PCons (c1, bnd1), PCons (c2, bnd2) ->
                   C.equal c1 c2 && eq_mbinder (equal mode env) bnd1 bnd2
               | _ -> false)
             cls1 cls2
    (* equality *)
    | Eq (m1, n1), Eq (m2, n2) -> equal mode env m1 m2 && equal mode env n1 n2
    | Refl, Refl -> true
    | Rew (bnd1, pf1, m1), Rew (bnd2, pf2, m2) ->
        eq_mbinder (equal mode env) bnd1 bnd2
        && equal mode env pf1 pf2 && equal mode env m1 m2
    (* monadic *)
    | IO a1, IO a2 -> equal mode env a1 a2
    | Return m1, Return m2 -> equal mode env m1 m2
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
        equal mode env m1 m2 && eq_binder (equal mode env) bnd1 bnd2
    (* session *)
    | Proto, Proto -> true
    | End rol1, End rol2 -> rol1 = rol2
    | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2) ->
        rel1 = rel2 && rol1 = rol2 && equal mode env a1 a2
        && eq_binder (equal mode env) bnd1 bnd2
    | Ch (rol1, a1), Ch (rol2, a2) -> rol1 = rol2 && equal mode env a1 a2
    | Open prim1, Open prim2 -> prim1 = prim2
    | Fork (a1, bnd1), Fork (a2, bnd2) ->
        equal mode env a1 a2 && eq_binder (equal mode env) bnd1 bnd2
    | Recv (rel1, m1), Recv (rel2, m2) -> rel1 = rel2 && equal mode env m1 m2
    | Send (rel1, m1), Send (rel2, m2) -> rel1 = rel2 && equal mode env m1 m2
    | Close m1, Close m2 -> equal mode env m1 m2
    (* other *)
    | _ -> false
