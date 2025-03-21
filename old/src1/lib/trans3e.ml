open Fmt
open Bindlib
open Names
open Syntax3

let simpl_arg = function
  | Var _ -> true
  | Const _ -> true
  | Pair _ -> true
  | Cons _ -> true
  | NULL -> true
  | _ -> false

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
    | Lam (_, bnd) when simpl_arg n -> lift_tm (subst bnd n)
    | Match (s, m, cls) when simpl_arg n ->
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
    | Let (m, bnd) when simpl_arg n ->
      let x, rhs = unbind bnd in
      let rhs = _App s (lift_tm rhs) (lift_tm n) in
      _Let (lift_tm m) (bind_var x (trans_tm (unbox rhs)))
    | _ -> _App s (lift_tm m) (lift_tm n))
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let m = trans_tm m in
    let n = trans_tm n in
    _Let m (bind_var x n)
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
  | _ -> lift_tm m0

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
