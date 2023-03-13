open Names
open Syntax1

type rd =
  | Beta
  | Delta
  | Zeta
  | Iota

let rec is_mode mode rd =
  List.exists ((=) rd) mode

let rec whnf mode env = function
  (* inference *)
  | Ann (m, a) ->
    (let m = whnf mode env m in
     match m with
     | Let (r, m, abs) ->
       let (x, ann), n = unbind_ann abs in
       let abs = bind_ann x ann (Ann (n, a)) in
       whnf mode env (Let (r, m, abs))
     | Match (n, mot, cls) -> 
       (match mot with
        | Some _ -> m
        | None ->
          let cls = 
            List.map
              (fun abs ->
                 let p, m = unbindp_tm abs in
                 bindp_tm p (Ann (m, a)))
              cls
          in
          whnf mode env (Match (m, mot, cls)))
     | _ -> m)
  (* core *)
  | Var x ->
    if is_mode mode Delta then
      match VMap.find_opt x env with
      | Some m -> whnf mode env m
      | None -> Var x
    else
      Var x
  | App (m, n) ->
    let m = whnf mode env m in
    let n = whnf mode env n in
    if is_mode mode Beta then
      match m with
      | Lam (_, _, abs) -> whnf mode env (asubst_ann abs n)
      | _ -> App (m, n)
    else
      App (m, n)
  | Let (r, m, abs) ->
    if is_mode mode Zeta then
      let m = whnf mode env m in
      let (x, _), n  = unbind_ann abs in
      whnf mode (VMap.add x m env) n
    else
      Let (r, m, abs)
  (* data *)
  | Match (m, mot, cls) ->
    let m = whnf mode env m in
    if is_mode mode Iota then
      match match_cls cls m with
      | Some m -> whnf mode env m
      | _ -> Match (m, mot, cls)
    else
      Match (m, mot, cls)
  (* equality *)
  | Rew (abs, pf, m) ->
    (let pf = whnf mode env pf in
     match pf with
     | Refl -> whnf mode env m
     | _ -> Rew (abs, pf, m))
  (* monadic *)
  | Do (m, abs) ->
    if is_mode mode Zeta then
      let m = whnf mode env m in
      let (x, _), n = unbind_ann abs in
      match m with
      | Return m -> whnf mode (VMap.add x m env) n
      | _ -> Do (m, abs)
    else
      Do (m, abs)
  (* other *)
  | m -> m

and match_cls cls m =
  List.fold_left
    (fun acc pabs ->
       match acc with
       | Some _ -> acc
       | None ->
         (let p, rhs = unbindp_tm pabs in
          try Some (substp_tm p rhs m) with
          | _ -> None))
    None cls

let rec aeq m1 m2 =
  if m1 == m2 then
    true
  else
    match m1, m2 with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) -> aeq m1 m2 && aeq a1 a2
    | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
    (* core *)
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> V.equal x1 x2
    | Pi (rel1, s1, a1, abs1), Pi (rel2, s2, a2, abs2) ->
      rel1 = rel2 && s1 = s2 && aeq a1 a2 && equal_abs aeq abs1 abs2
    | Lam (rel1, s1, abs1), Lam (rel2, s2, abs2) ->
      rel1 = rel2 && s1 = s2 && equal_ann aeq abs1 abs2
    | App (m1, n1), App (m2, n2) ->
      aeq m1 m2 && aeq n1 n2
    | Let (rel1, m1, abs1), Let (rel2, m2, abs2) ->
      rel1 = rel2 && aeq m1 m2 && equal_ann aeq abs1 abs2
    (* data *)
    | Sig (rel1, s1, a1, abs1), Sig (rel2, s2, a2, abs2) ->
      rel1 = rel2 && s1 = s2 && aeq a2 a2 && equal_abs aeq abs1 abs2
    | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2) ->
      rel1 = rel2 && s2 = s2 && aeq m1 m2 && aeq n1 n2
    | Data (d1, ms1), Data (d2, ms2) ->
      D.equal d1 d2 && List.equal aeq ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) ->
      C.equal c1 c2 && List.equal aeq ms1 ms2
    | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
      aeq m1 m2 && Option.equal (equal_abs aeq) mot1 mot2 &&
      List.equal (equal_pabs aeq) cls1 cls2
    (* equality *)
    | Eq (m1, n1), Eq (m2, n2) ->
      aeq m1 m2 && aeq n1 n2
    | Refl, Refl -> true
    | Rew (abs1, pf1, m1), Rew (abs2, pf2, m2) ->
      equal_abs aeq abs1 abs2 && aeq pf1 pf2 && aeq m1 m2
    (* monadic *)
    | IO a1, IO a2 -> aeq a1 a2
    | Return m1, Return m2 -> aeq m1 m2
    | Do (m1, abs1), Do (m2, abs2) ->
      aeq m1 m2 && equal_ann aeq abs1 abs2
    (* session *)
    | Proto, Proto -> true
    | End rol1, End rol2 -> rol1 = rol2
    | Act (rel1, rol1, a1, abs1), Act (rel2, rol2, a2, abs2) ->
      rel1 = rel2 && rol1 = rol2 && aeq a1 a2 && equal_abs aeq abs1 abs2
    | Ch (rol1, a1), Ch (rol2, a2) ->
      rol1 = rol2 && aeq a1 a2
    | Open prim1, Open prim2 -> prim1 = prim2
    | Fork (a1, abs1), Fork (a2, abs2) ->
      aeq a1 a2 && equal_abs aeq abs1 abs2
    | Recv (rol1, m1), Recv (rol2, m2) ->
      rol1 = rol2 && aeq m1 m2
    | Send (rol1, m1), Send (rol2, m2) ->
      rol2 = rol2 && aeq m1 m2
    | Close m1, Close m2 -> aeq m1 m2
    (* other *)
    | _ -> false

let rec equal mode env m1 m2 =
  if aeq m1 m2 then
    true
  else
    let m1 = whnf mode env m1 in
    let m2 = whnf mode env m2 in
    match m1, m2 with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) ->
      equal mode env m1 m2 && equal mode env a1 a2
    | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
    (* core *)
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> V.equal x1 x2
    | Pi (rel1, s1, a1, abs1), Pi (rel2, s2, a2, abs2) ->
      rel1 = rel2 && s1 = s2 && equal mode env a1 a2 &&
      equal_abs (equal mode env) abs1 abs2
    | Lam (rel1, s1, abs1), Lam (rel2, s2, abs2) ->
      rel1 = rel2 && s1 = s2 &&
      equal_ann (equal mode env) abs1 abs2
    | App (m1, n1), App (m2, n2) ->
      equal mode env m1 m2 && equal mode env n1 n2
    | Let (rel1, m1, abs1), Let (rel2, m2, abs2) ->
      rel1 = rel2 && equal mode env m1 m2 &&
      equal_ann (equal mode env) abs1 abs2
    (* data *)
    | Sig (rel1, s1, a1, abs1), Sig (rel2, s2, a2, abs2) ->
      rel1 = rel2 && equal mode env m1 m2 &&
      equal_abs (equal mode env) abs1 abs2
    | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2) ->
      rel1 = rel2 && s1 = s2 &&
      equal mode env m1 m2 && equal mode env n1 n2
    | Data (d1, ms1), Data (d2, ms2) ->
      D.equal d1 d2 && List.equal (equal mode env) ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) ->
      C.equal c1 c2 && List.equal (equal mode env) ms1 ms2
    | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
      equal mode env m1 m2 &&
      Option.equal (equal_abs (equal mode env)) mot1 mot2 &&
      List.equal (equal_pabs (equal mode env)) cls1 cls2
    (* equality *)
    | Eq (m1, n1), Eq (m2, n2) ->
      equal mode env m1 m2 && equal mode env n1 n2
    | Refl, Refl -> true
    | Rew (abs1, pf1, m1), Rew (abs2, pf2, m2) ->
      equal_abs (equal mode env) abs1 abs2 &&
      equal mode env pf1 pf2 && equal mode env m1 m2
    (* monadic *)
    | IO a1, IO a2 -> equal mode env a1 a2
    | Return m1, Return m2 -> equal mode env m1 m2
    | Do (m1, abs1), Do (m2, abs2) ->
      equal mode env m1 m2 && equal_ann (equal mode env) abs1 abs2
    (* session *)
    | Proto, Proto -> true
    | End rol1, End rol2 -> rol1 = rol2
    | Act (rel1, rol1, a1, abs1), Act (rel2, rol2, a2, abs2) ->
      rel1 = rel2 && rol1 = rol2 &&
      equal mode env a1 a2 && equal_abs (equal mode env) abs1 abs2
    | Ch (rol1, a1), Ch (rol2, a2) ->
      rol1 = rol2 && equal mode env a1 a2
    | Open prim1, Open prim2 -> prim1 = prim2
    | Fork (a1, abs1), Fork (a2, abs2) ->
      equal mode env a1 a2 && equal_abs (equal mode env) abs1 abs2
    | Recv (rol1, m1), Recv (rol2, m2) ->
      rol1 = rol2 && equal mode env m1 m2
    | Send (rol1, m1), Send (rol2, m2) ->
      rol1 = rol2 && equal mode env m1 m2
    | Close m1, Close m2 -> equal mode env m1 m2
    (* other *)
    | _ -> false
