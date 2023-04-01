open Bindlib
open Names
open Syntax1

type env_entry =
  { scheme : sorts -> tm
  ; guarded : bool
  }

type env = env_entry VMap.t

type rd =
  | Beta
  | Delta
  | Iota

let rd_all = [| Beta; Delta; Iota |]
let enabled mode rd = Array.exists (( = ) rd) mode

let is_guarded sp =
  List.exists
    (function
      | Cons _ -> true
      | _ -> false)
    sp

let rec whnf mode (env : env) = function
  (* inference *)
  | Ann (m, a) -> whnf mode env m
  (* core *)
  | Const (x, ss) when enabled mode Delta -> (
    match VMap.find_opt x env with
    | Some entry when not entry.guarded -> whnf mode env (entry.scheme ss)
    | _ -> Const (x, ss))
  | App _ as m when enabled mode Beta -> (
    let hd, sp = unApps m in
    let hd = whnf mode env hd in
    let sp = List.map (whnf mode env) sp in
    match (hd, sp) with
    | Lam (_, _, bnd), n :: sp -> whnf mode env (mkApps (subst bnd n) sp)
    | Const (x, ss), _ when is_guarded sp && enabled mode Delta -> (
      match VMap.find_opt x env with
      | Some entry -> whnf mode env (mkApps (entry.scheme ss) sp)
      | None -> mkApps hd sp)
    | _ -> mkApps hd sp)
  | Let (r, m, bnd) ->
    let m = whnf mode env m in
    whnf mode env (subst bnd m)
  (* data *)
  | Match (m, mot, cls) when enabled mode Iota -> (
    let m = whnf mode env m in
    match match_cls cls m with
    | Some m -> whnf mode env m
    | _ -> Match (m, mot, cls))
  (* equality *)
  | Rew (bnd, pf, m) -> (
    let pf = whnf mode env pf in
    match pf with
    | Refl _ -> whnf mode env m
    | _ -> Rew (bnd, pf, m))
  (* monadic *)
  | MLet (m, bnd) -> (
    let m = whnf mode env m in
    match m with
    | Return m -> whnf mode env (subst bnd m)
    | _ -> MLet (m, bnd))
  (* session *)
  | Ch (rol, a) -> Ch (rol, whnf mode env a)
  (* other *)
  | m -> m

and match_cls cls m =
  List.fold_left
    (fun acc cl ->
      Option.fold
        ~some:(fun _ -> acc)
        ~none:
          (match (cl, m) with
          | PPair (rel1, s1, bnd), Pair (rel2, s2, m1, m2)
            when rel1 = rel2 && s1 = s2 ->
            Some (msubst bnd [| m1; m2 |])
          | PCons (c1, bnd), Cons (c2, _, _, ms) when C.equal c1 c2 ->
            Some (msubst bnd (Array.of_list ms))
          | _ -> acc)
        acc)
    None cls

(* alpha equivalence *)
let rec aeq tm1 tm2 =
  if tm1 == tm2 then
    true
  else
    match (tm1, tm2) with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) -> aeq m1 m2 && aeq a1 a2
    | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
    (* core *)
    | Type s1, Type s2 -> eq_sort s1 s2
    | Var x1, Var x2 -> eq_vars x1 x2
    | Const (x1, ss1), Const (x2, ss2) ->
      eq_vars x1 x2 && List.equal eq_sort ss1 ss2
    | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) ->
      rel1 = rel2 && eq_sort s1 s2 && aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Lam (rel1, s1, bnd1), Lam (rel2, s2, bnd2) ->
      rel1 = rel2 && eq_sort s1 s2 && eq_binder aeq bnd1 bnd2
    | App (m1, n1), App (m2, n2) -> aeq m1 m2 && aeq n1 n2
    | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) ->
      rel1 = rel2 && aeq m1 m2 && eq_binder aeq bnd1 bnd2
    (* data *)
    | Sigma (rel1, s1, a1, bnd1), Sigma (rel2, s2, a2, bnd2) ->
      rel1 = rel2 && eq_sort s1 s2 && aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2) ->
      rel1 = rel2 && s1 = s2 && aeq m1 m2 && aeq n1 n2
    | Data (d1, ss1, ms1), Data (d2, ss2, ms2) ->
      D.equal d1 d2 && List.equal eq_sort ss1 ss2 && List.equal aeq ms1 ms2
    | Cons (c1, ss1, ms1, ns1), Cons (c2, ss2, ms2, ns2) ->
      C.equal c1 c2 && List.equal eq_sort ss1 ss2 && List.equal aeq ms1 ms2
      && List.equal aeq ns1 ns2
    | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
      aeq m1 m2 && eq_binder aeq bnd1 bnd2
      && List.equal
           (fun cl1 cl2 ->
             match (cl1, cl2) with
             | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2) ->
               rel1 = rel2 && eq_sort s1 s2 && eq_mbinder aeq bnd1 bnd2
             | PCons (c1, bnd1), PCons (c2, bnd2) ->
               C.equal c1 c2 && eq_mbinder aeq bnd1 bnd2
             | _ -> false)
           cls1 cls2
    (* equality *)
    | Eq (a1, m1, n1), Eq (a2, m2, n2) -> aeq a1 a2 && aeq m1 m2 && aeq n1 n2
    | Refl m1, Refl m2 -> aeq m1 m2
    | Rew (bnd1, p1, m1), Rew (bnd2, p2, m2) ->
      eq_mbinder aeq bnd1 bnd2 && aeq p1 p2 && aeq m1 m2
    (* monadic *)
    | IO a1, IO a2 -> aeq a1 a2
    | Return m1, Return m2 -> aeq m1 m2
    | MLet (m1, bnd1), MLet (m2, bnd2) -> aeq m1 m2 && eq_binder aeq bnd1 bnd2
    (* session *)
    | Proto, Proto -> true
    | End, End -> true
    | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2) ->
      rel1 = rel2 && rol1 = rol2 && aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Ch (rol1, a1), Ch (rol2, a2) -> rol1 = rol2 && aeq a1 a2
    | Open prim1, Open prim2 -> prim1 = prim2
    | Fork (a1, bnd1), Fork (a2, bnd2) -> aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Recv m1, Recv m2 -> aeq m1 m2
    | Send m1, Send m2 -> aeq m1 m2
    | Close m1, Close m2 -> aeq m1 m2
    (* other *)
    | _ -> false

(* Beta/Delta/Iota equaltiy *)
let eq_tm mode env m1 m2 =
  let rec equal m1 m2 =
    if aeq m1 m2 then
      true
    else
      let m1 = whnf mode env m1 in
      let m2 = whnf mode env m2 in
      match (m1, m2) with
      (* inference *)
      | Ann (m1, a1), Ann (m2, a2) -> equal m1 m2 && equal a1 a2
      | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
      (* core *)
      | Type s1, Type s2 -> eq_sort s1 s2
      | Var x1, Var x2 -> eq_vars x1 x2
      | Const (x1, ss1), Const (x2, ss2) ->
        eq_vars x1 x2 && List.equal eq_sort ss1 ss2
      | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && eq_sort s1 s2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | Lam (rel1, s1, bnd1), Lam (rel2, s2, bnd2) ->
        rel1 = rel2 && eq_sort s1 s2 && eq_binder equal bnd1 bnd2
      | App (m1, n1), App (m2, n2) -> equal m1 m2 && equal n1 n2
      | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) ->
        rel1 = rel2 && equal m1 m2 && eq_binder equal bnd1 bnd2
      (* data *)
      | Sigma (rel1, s1, a1, bnd1), Sigma (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && eq_sort s1 s2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2) ->
        rel1 = rel2 && eq_sort s1 s2 && equal m1 m2 && equal n1 n2
      | Data (d1, ss1, ms1), Data (d2, ss2, ms2) ->
        D.equal d1 d2 && List.equal eq_sort ss1 ss2 && List.equal equal ms1 ms2
      | Cons (c1, ss1, ms1, ns1), Cons (c2, ss2, ms2, ns2) ->
        C.equal c1 c2 && List.equal eq_sort ss1 ss2 && List.equal equal ms1 ms2
        && List.equal equal ns1 ns2
      | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
        equal m1 m2 && eq_binder equal bnd1 bnd2
        && List.equal
             (fun cl1 cl2 ->
               match (cl1, cl2) with
               | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2) ->
                 rel1 = rel2 && eq_sort s1 s2 && eq_mbinder equal bnd1 bnd2
               | PCons (c1, bnd1), PCons (c2, bnd2) ->
                 C.equal c1 c2 && eq_mbinder equal bnd1 bnd2
               | _ -> false)
             cls1 cls2
      (* equality *)
      | Eq (a1, m1, n1), Eq (a2, m2, n2) ->
        equal a1 a2 && equal m1 m2 && equal n1 n2
      | Refl m1, Refl m2 -> equal m1 m2
      | Rew (bnd1, p1, m1), Rew (bnd2, p2, m2) ->
        eq_mbinder equal bnd1 bnd2 && equal p1 p2 && equal m1 m2
      (* monadic *)
      | IO a1, IO a2 -> equal a1 a2
      | Return m1, Return m2 -> equal m1 m2
      | MLet (m1, bnd1), MLet (m2, bnd2) ->
        equal m1 m2 && eq_binder equal bnd1 bnd2
      (* session *)
      | Proto, Proto -> true
      | End, End -> true
      | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2) ->
        rel1 = rel2 && rol1 = rol2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | Ch (rol1, a1), Ch (rol2, a2) -> rol1 = rol2 && equal a1 a2
      | Open prim1, Open prim2 -> prim1 = prim2
      | Fork (a1, bnd1), Fork (a2, bnd2) ->
        equal a1 a2 && eq_binder equal bnd1 bnd2
      | Recv m1, Recv m2 -> equal m1 m2
      | Send m1, Send m2 -> equal m1 m2
      | Close m1, Close m2 -> equal m1 m2
      (* other *)
      | _ -> false
  in
  equal m1 m2
