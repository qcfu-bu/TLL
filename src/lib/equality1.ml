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
    | Match (ms, b, cls) ->
      let cls =
        List.map
          (fun pabs ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let m_opt = Option.map (fun m -> Ann (a, m)) m_opt in
            bindp_tm_opt ps m_opt)
          cls
      in
      whnf rds env (Match (ms, b, cls))
    | _ -> m)
  | Var x ->
    if List.exists (( = ) Delta) rds then
      match VMap.find_opt x env with
      | Some m -> whnf rds env m
      | None -> Var x
    else
      Var x
  | App _ as m -> (
    let m, sp = unApps m in
    let m = whnf rds env m in
    let sp = List.map (whnf rds env) sp in
    match (m, sp) with
    | Fun (_, abs), _ :: _ ->
      if List.exists (( = ) Beta) rds then
        let cls = asubst_cls abs m in
        match match_cls cls sp with
        | Some (Some n) -> whnf rds env n
        | _ -> mkApps m sp
      else
        mkApps m sp
    | _ -> mkApps m sp)
  | Let (r, m, abs) ->
    if List.exists (( = ) Zeta) rds then
      let m = whnf rds env m in
      let x, n = unbind_tm abs in
      whnf rds (VMap.add x m env) n
    else
      Let (r, m, abs)
  | Match (ms, a, cls) ->
    let ms = List.map (whnf rds env) ms in
    let a = whnf rds env a in
    if List.exists (( = ) Iota) rds then
      match match_cls cls ms with
      | Some (Some m) -> whnf rds env m
      | _ -> Match (ms, a, cls)
    else
      Match (ms, a, cls)
  | m -> m

and match_cls cls ms =
  List.fold_left
    (fun acc pabs ->
      match acc with
      | Some _ -> acc
      | None -> (
        let ps, rhs = unbindp_tm_opt pabs in
        try Some (substp_tm_opt ps rhs ms) with
        | _ -> None))
    None cls

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
    | Fun (a1_opt, abs1), Fun (a2_opt, abs2) ->
      Option.equal aeq a1_opt a2_opt
      && equal_abs (List.equal (equal_pabs (Option.equal aeq))) abs1 abs2
    | App (m1, n1), App (m2, n2) -> aeq m1 m2 && aeq n1 n2
    | Let (r1, m1, abs1), Let (r2, m2, abs2) ->
      r1 = r2 && aeq m1 m2 && equal_abs aeq abs1 abs2
    | Data (d1, ms1), Data (d2, ms2) -> D.equal d1 d2 && List.equal aeq ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) -> C.equal c1 c2 && List.equal aeq ms1 ms2
    | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
      List.equal aeq ms1 ms2 && aeq a1 a2
      && List.equal (equal_pabs (Option.equal aeq)) cls1 cls2
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
    | Fun (_, abs1), Fun (_, abs2) ->
      equal_abs
        (List.equal (equal_pabs (Option.equal (equal rds env))))
        abs1 abs2
    | App (m1, n1), App (m2, n2) -> equal rds env m1 m2 && equal rds env n1 n2
    | Let (r1, m1, abs1), Let (r2, m2, abs2) ->
      r1 = r2 && equal rds env m1 m2 && equal_abs (equal rds env) abs1 abs2
    | Data (d1, ms1), Data (d2, ms2) ->
      D.equal d1 d2 && List.equal (equal rds env) ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) ->
      C.equal c1 c2 && List.equal (equal rds env) ms1 ms2
    | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
      List.equal (equal rds env) ms1 ms2
      && equal rds env a1 a2
      && List.equal (equal_pabs (Option.equal (equal rds env))) cls1 cls2
    | _ -> false
