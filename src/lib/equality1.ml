open Names
open Syntax1

type rd =
  | Beta
  | Delta
  | Zeta
  | Iota

let rd_all = [ Beta; Delta; Zeta; Iota ]

let rec whnf rds env = function
  | Ann (a, m) -> (
    let m = whnf rds env m in
    match m with
    | Let (r, m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      whnf rds env (Let (r, m, abs))
    | Match (m, mot, cls) ->
      let cls =
        List.map
          (fun abs ->
            let p, m = unbindp_tm abs in
            let m = Ann (a, m) in
            bindp_tm p m)
          cls
      in
      whnf rds env (Match (m, mot, cls))
    | _ -> m)
  | Var x ->
    if List.exists (( = ) Delta) rds then
      match VMap.find_opt x env with
      | Some m -> whnf rds env m
      | None -> Var x
    else
      Var x
  | App (m, n) ->
    let m = whnf rds env m in
    let n = whnf rds env n in
    if List.exists (( = ) Beta) rds then
      match m with
      | Lam abs -> whnf rds env (asubst_tm abs n)
      | Fix abs -> whnf rds env (App (asubst_tm abs m, n))
      | _ -> App (m, n)
    else
      App (m, n)
  | Let (r, m, abs) ->
    if List.exists (( = ) Zeta) rds then
      let m = whnf rds env m in
      let x, n = unbind_tm abs in
      whnf rds (VMap.add x m env) n
    else
      Let (r, m, abs)
  | Match (m, mot, cls) ->
    let m = whnf rds env m in
    if List.exists (( = ) Iota) rds then
      match match_cls cls m with
      | Some m -> whnf rds env m
      | _ -> Match (m, mot, cls)
    else
      Match (m, mot, cls)
  | m -> m

and match_cls cls m =
  List.fold_left
    (fun acc abs ->
      match acc with
      | Some _ -> acc
      | None -> (
        let p, rhs = unbindp_tm abs in
        try Some (substp_tm p rhs m) with
        | _ -> None))
    None cls

let equal_mot eq mot1 mot2 =
  match (mot1, mot2) with
  | Mot0, Mot0 -> true
  | Mot1 abs1, Mot1 abs2 -> equal_abs eq abs1 abs2
  | Mot2 abs1, Mot2 abs2 -> equal_pabs eq abs1 abs2
  | Mot3 abs1, Mot3 abs2 -> equal_abs (equal_pabs eq) abs1 abs2
  | _ -> false

let rec aeq m1 m2 =
  if m1 == m2 then
    true
  else
    match (m1, m2) with
    | Ann (a1, m1), Ann (a2, m2) -> aeq a1 a2 && aeq m1 m2
    | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> V.equal x1 x2
    | Pi (r1, s1, a1, abs1), Pi (r2, s2, a2, abs2) ->
      r1 = r2 && s1 = s2 && aeq a1 a2 && equal_abs aeq abs1 abs2
    | Lam abs1, Lam abs2 -> equal_abs aeq abs1 abs2
    | App (m1, n1), App (m2, n2) -> aeq m1 m2 && aeq n1 n2
    | Let (r1, m1, abs1), Let (r2, m2, abs2) ->
      r1 = r2 && aeq m1 m2 && equal_abs aeq abs1 abs2
    | Data (d1, ms1), Data (d2, ms2) -> D.equal d1 d2 && List.equal aeq ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) -> C.equal c1 c2 && List.equal aeq ms1 ms2
    | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
      aeq m1 m2 && equal_mot aeq mot1 mot2
      && List.equal (equal_pabs aeq) cls1 cls2
    | Fix abs1, Fix abs2 -> equal_abs aeq abs1 abs2
    | _ -> false

let rec equal rds env m1 m2 =
  if aeq m1 m2 then
    true
  else
    let m1 = whnf rds env m1 in
    let m2 = whnf rds env m2 in
    match (m1, m2) with
    | Ann (a1, m1), Ann (a2, m2) -> equal rds env a1 a2 && equal rds env m1 m2
    | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> V.equal x1 x2
    | Pi (r1, s1, a1, abs1), Pi (r2, s2, a2, abs2) ->
      r1 = r2 && s1 = s2 && equal rds env a1 a2
      && equal_abs (equal rds env) abs1 abs2
    | Lam abs1, Lam abs2 -> equal_abs (equal rds env) abs1 abs2
    | App (m1, n1), App (m2, n2) -> equal rds env m1 m2 && equal rds env n1 n2
    | Let (r1, m1, abs1), Let (r2, m2, abs2) ->
      r1 = r2 && equal rds env m1 m2 && equal_abs (equal rds env) abs1 abs2
    | Data (d1, ms1), Data (d2, ms2) ->
      D.equal d1 d2 && List.equal (equal rds env) ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) ->
      C.equal c1 c2 && List.equal (equal rds env) ms1 ms2
    | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
      equal rds env m1 m2
      && equal_mot (equal rds env) mot1 mot2
      && List.equal (equal_pabs (equal rds env)) cls1 cls2
    | _ -> false
