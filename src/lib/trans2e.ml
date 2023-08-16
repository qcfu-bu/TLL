open Fmt
open Bindlib
open Names
open Syntax2
open Equality2e
open Pprint2

let rec trans_tm = function
  (* core *)
  | Var x -> _Var x
  | Const x -> _Const x
  | Fun bnd ->
    let x, bnd = unbind bnd in
    let xs, m = unmbind bnd in
    let m_elab = trans_tm m in
    _Fun (bind_var x (bind_mvar xs m_elab))
  | App (s, m, n) ->
    let m_elab = trans_tm m in
    let n_elab = trans_tm n in
    _App s m_elab n_elab
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let m_elab = trans_tm m in
    let n_elab = trans_tm n in
    _Let m_elab (bind_var x n_elab)
  (* inductive *)
  | Constr (c, ms) ->
    let ms = List.map trans_tm ms in
    _Constr c (box_list ms)
  | Match (R, s, m, cls) -> (
    let m_elab = trans_tm m in
    let cls_prune =
      List.filter_map
        (fun (c, bnd) ->
          let xs, rhs = unmbind bnd in
          let rhs_elab = trans_tm rhs in
          match unbox rhs_elab with
          | Absurd -> None
          | _ -> Some (_PConstr c (bind_mvar xs rhs_elab)))
        cls
    in
    match cls_prune with
    | [] -> _Absurd
    | _ -> _Match R s m_elab (box_list cls_prune))
  | Match (N, _, _, cls) as m0 -> (
    let rhs_merge =
      List.fold_left
        (fun acc_opt (c, bnd) ->
          let xs, rhs = unmbind bnd in
          let rhs_elab = trans_tm rhs in
          match (unbox rhs_elab, acc_opt) with
          | Absurd, _ -> acc_opt
          | rhs, None -> Some rhs
          | rhs, Some acc ->
            if eq_tm rhs acc then
              Some rhs
            else
              failwith "trans2e.irrelevant_split(%a)" pp_tm m0)
        None cls
    in
    match rhs_merge with
    | None -> _Absurd
    | Some rhs -> lift_tm rhs)
  | Absurd -> _Absurd
  (* monad *)
  | Return m -> _Return (trans_tm m)
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let m_elab = trans_tm m in
    let n_elab = trans_tm n in
    _MLet m_elab (bind_var x n_elab)
  (* erasure *)
  | NULL -> _NULL
  (* magic *)
  | Magic -> _Magic

let rec trans_dcls = function
  | [] -> []
  | Definition { name; body } :: dcls ->
    let body_elab = trans_tm body in
    let dcls_elab = trans_dcls dcls in
    Definition { name; body = unbox body_elab } :: dcls_elab
  | Inductive { name; body } :: dcls ->
    Inductive { name; body } :: trans_dcls dcls
