open Fmt
open Bindlib
open Names
open Syntax3

let rec simpl_arg = function
  | Var _ -> true
  | Const _ -> true
  | Int _ -> true
  | NULL -> true
  | _ -> false

let simpl_bnd bnd =
  let rec occurs_tm x = function
    (* core *)
    | Var y when eq_vars x y -> 1
    | Lam (_, bnd) ->
      let _, m = unbind bnd in
      occurs_tm x m
    | Call (_, ms) -> List.fold_left (fun acc m -> acc + occurs_tm x m) 0 ms
    | App (_, m, n) -> occurs_tm x m + occurs_tm x n
    | Let (m, bnd) ->
      let _, n = unbind bnd in
      occurs_tm x m + occurs_tm x n
    (* native *)
    | Add (_, m) -> occurs_tm x m
    | Ifte (m, n1, n2) -> occurs_tm x m + occurs_tm x n1 + occurs_tm x n2
    (* data *)
    | Pair (m, n) -> occurs_tm x m + occurs_tm x n
    | Cons (_, ms) -> List.fold_left (fun acc m -> acc + occurs_tm x m) 0 ms
    | Match (_, m, cls) ->
      List.fold_left
        (fun acc -> function
          | PPair bnd ->
            let _, rhs = unmbind bnd in
            acc + occurs_tm x rhs
          | PCons (_, bnd) ->
            let _, rhs = unmbind bnd in
            acc + occurs_tm x rhs)
        (occurs_tm x m) cls
      (* effect *)
    | Fork bnd ->
      let _, m = unbind bnd in
      occurs_tm x m
    | Recv m -> occurs_tm x m
    | Send (m, n) -> occurs_tm x m + occurs_tm x n
    | Close m -> occurs_tm x m
    | Sleep m -> occurs_tm x m
    | _ -> 0
  in
  let x, m = unbind bnd in
  occurs_tm x m = 1

let rec trans_tm m0 =
  match m0 with
  (* core *)
  | Lam (s, bnd) ->
    let x, m = unbind bnd in
    let m = trans_tm m in
    _Lam s (bind_var x m)
  | Call (x, ms) ->
    let ms = List.map trans_tm ms in
    _Call x (box_list ms)
  | App (s, m, n) -> (
    let m = unbox (trans_tm m) in
    let n = unbox (trans_tm n) in
    match m with
    | Lam (_, bnd) when simpl_arg n || simpl_bnd bnd -> lift_tm (subst bnd n)
    | Match (s, m, cls) ->
      let cls =
        List.map
          (function
            | PPair bnd ->
              let xs, rhs = unmbind bnd in
              let rhs = _App s (lift_tm rhs) (lift_tm n) in
              _PPair (bind_mvar xs (trans_tm (unbox rhs)))
            | PCons (c, bnd) ->
              let xs, rhs = unmbind bnd in
              let rhs = _App s (lift_tm rhs) (lift_tm n) in
              _PCons c (bind_mvar xs (trans_tm (unbox rhs))))
          cls
      in
      _Match s (lift_tm m) (box_list cls)
    | Let (m, bnd) ->
      let x, rhs = unbind bnd in
      let rhs = _App s (lift_tm rhs) (lift_tm n) in
      _Let (lift_tm m) (bind_var x (trans_tm (unbox rhs)))
    | _ -> _App s (lift_tm m) (lift_tm n))
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let m = unbox (trans_tm m) in
    let bnd = unbox (bind_var x (trans_tm n)) in
    if simpl_arg m || simpl_bnd bnd then
      lift_tm (subst bnd m)
    else
      _Let (lift_tm m) (box_binder lift_tm bnd)
  (* native *)
  | Add _ as m -> trans_int m
  | Ifte (m, n1, n2) ->
    let m = trans_tm m in
    let n1 = trans_tm n1 in
    let n2 = trans_tm n2 in
    _Ifte m n1 n2
  (* data *)
  | Pair (m, n) ->
    let m = trans_tm m in
    let n = trans_tm n in
    _Pair m n
  | Cons (c, ms) ->
    let ms = List.map trans_tm ms in
    _Cons c (box_list ms)
  | Match (s, m, cls) ->
    let m = trans_tm m in
    let cls =
      List.map
        (function
          | PPair bnd ->
            let xs, rhs = unmbind bnd in
            let rhs = trans_tm rhs in
            _PPair (bind_mvar xs rhs)
          | PCons (c, bnd) ->
            let xs, rhs = unmbind bnd in
            let rhs = trans_tm rhs in
            _PCons c (bind_mvar xs rhs))
        cls
    in
    _Match s m (box_list cls)
  (* effect *)
  | Fork bnd ->
    let x, m = unbind bnd in
    let m = trans_tm m in
    _Fork (bind_var x m)
  | Recv m -> _Recv (trans_tm m)
  | Send (m, n) -> _Send (trans_tm m) (trans_tm n)
  | Close m -> _Close (trans_tm m)
  | Sleep m -> _Sleep (trans_tm m)
  | _ -> lift_tm m0

and trans_int = function
  | Int i -> _Int i
  | Add (0, m) -> trans_int m
  | Add (i, m) -> (
    match unbox (trans_tm m) with
    | Int j -> _Int (i + j)
    | Add (j, m) when i + j = 0 -> lift_tm m
    | Add (j, m) -> _Add (i + j) (lift_tm m)
    | m -> _Add i (lift_tm m))
  | m -> lift_tm m

let trans_dcls dcls =
  let rec aux = function
    | DFun (x, bnd) ->
      let xs, m = unmbind bnd in
      _DFun x (bind_mvar xs (trans_tm m))
    | DVal (x, m) -> _DVal x (trans_tm m)
    | DMain m -> _DMain (trans_tm m)
  in
  let dcls = List.map aux dcls in
  unbox (box_list dcls)
