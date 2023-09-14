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
  | Fun (relvs, bnd) ->
    let x, bnd = unbind bnd in
    let xs, m = unmbind bnd in
    let m_elab = trans_tm m in
    _Fun relvs (bind_var x (bind_mvar xs m_elab))
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
  | Match (R, s, m, cls) -> 
    let m_elab = trans_tm m in
    let cls_prune = List.filter_map (fun (c, bnd) ->
        let xs, rhs = unmbind bnd in
        let rhs_elab = trans_tm rhs in
        match unbox rhs_elab with
        | Absurd -> None
        | _ -> Some (_PConstr c (bind_mvar xs rhs_elab)))
        cls
    in
    (match cls_prune with
     | [] -> _Absurd
     | _ -> _Match R s m_elab (box_list cls_prune))
  | Match (N, _, _, cls) as m0 -> 
    let rhs_merge = List.fold_left (fun acc_opt (c, bnd) ->
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
    (match rhs_merge with
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
  (* primitive terms *)
  | Int i -> _Int i
  | Char c -> _Char c
  | String s -> _String s
  (* primitive operators *)
  | Neg m -> _Neg (trans_tm m)
  | Add (m, n) -> _Add (trans_tm m) (trans_tm n)
  | Sub (m, n) -> _Sub (trans_tm m) (trans_tm n)
  | Mul (m, n) -> _Mul (trans_tm m) (trans_tm n)
  | Div (m, n) -> _Div (trans_tm m) (trans_tm n)
  | Mod (m, n) -> _Mod (trans_tm m) (trans_tm n)
  | Lte (m, n) -> _Lte (trans_tm m) (trans_tm n)
  | Gte (m, n) -> _Gte (trans_tm m) (trans_tm n)
  | Lt (m, n) -> _Lt (trans_tm m) (trans_tm n)
  | Gt (m, n) -> _Gt (trans_tm m) (trans_tm n)
  | Eq (m, n) -> _Eq (trans_tm m) (trans_tm n)
  | Chr m -> _Chr (trans_tm m)
  | Ord m -> _Ord (trans_tm m)
  | Push (m, n) -> _Push (trans_tm m) (trans_tm n)
  | Cat (m, n) -> _Cat (trans_tm m) (trans_tm n)
  | Size m -> _Size (trans_tm m)
  | Indx (m, n) -> _Indx (trans_tm m) (trans_tm n)
  (* primitive effects *)
  | Print m -> _Print (trans_tm m)
  | Prerr m -> _Prerr (trans_tm m)
  | ReadLn m -> _ReadLn (trans_tm m)
  | Fork m -> _Fork (trans_tm m)
  | Send (relv, s, m) -> _Send relv s (trans_tm m)
  | Recv (relv, s, m) -> _Recv relv s (trans_tm m)
  | Close (role, m) -> _Close role (trans_tm m)
  (* erasure *)
  | NULL -> _NULL
  (* magic *)
  | Magic -> _Magic

let trans_dcls dcls = 
  let rec aux = function
    | [] -> []
    | Main { body } :: [] -> Main { body = unbox (trans_tm body) } :: []
    | Main _ :: _ -> failwith "trans12.trans_dcls(Main)"
    | Definition { name; relv; body } :: dcls ->
      let body_elab = trans_tm body in
      let dcls_elab = aux dcls in
      Definition { name; relv; body = unbox body_elab } :: dcls_elab
    | Inductive { name; relv; body } :: dcls ->
      Inductive { name; relv; body } :: aux dcls
    | Extern { name; relv } :: dcls -> Extern { name; relv } :: aux dcls
  in
  let dcls = aux dcls in
  pf Debug.fmt "%a" Pprint2.pp_dcls dcls;
  pf Debug.fmt "@.@.[trans2e success]";
  pf Debug.fmt "@.@.-----------------------------------------@.@.";
  dcls

