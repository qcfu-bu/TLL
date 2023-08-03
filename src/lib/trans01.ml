open Fmt
open Bindlib
open Names
open Syntax0

type nspc_entry =
  | EVar of Syntax1.tm var
  | ESVar of Syntax1.sort var
  | EConst of Const.t * int
  | EInd of Ind.t * int
  | EConstr of Constr.t * int * int

type nspc = (string * nspc_entry) list

let find_var s nspc =
  let opt =
    List.find_opt
      (function
        | k, EVar _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EVar x) -> Some x
  | _ -> None

let find_svar s nspc =
  let opt =
    List.find_opt
      (function
        | k, ESVar _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, ESVar x) -> Some x
  | _ -> None

let find_const s nspc =
  let opt =
    List.find_opt
      (function
        | k, EConst _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EConst (x, _)) -> Some x
  | _ -> None

let find_ind s nspc =
  let opt =
    List.find_opt
      (function
        | k, EInd _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EInd (d, i)) -> Some (d, i)
  | _ -> None

let find_constr s nspc =
  let opt =
    List.find_opt
      (function
        | k, EConstr _ when s = k -> true
        | _ -> false)
      nspc
  in
  match opt with
  | Some (_, EConstr (c, i, j)) -> Some (c, i, j)
  | _ -> None

let trans_relv = function
  | R -> Syntax1.R
  | N -> Syntax1.N

let sspine_of_nspc nspc =
  List.fold_right
    (fun (_, entry) acc ->
      match entry with
      | ESVar x -> Binding1._SVar x :: acc
      | _ -> acc)
    nspc []

let vspine_of_nspc nspc =
  List.fold_right
    (fun (_, entry) acc ->
      match entry with
      | EVar x -> Binding1._Var x :: acc
      | _ -> acc)
    nspc []

let trans_sort nspc = function
  | U -> Binding1._U
  | L -> Binding1._L
  | SId "_" -> Binding1.(_SMeta (SMeta.mk "") (box_list (sspine_of_nspc nspc)))
  | SId id -> (
    match find_svar id nspc with
    | Some x -> Binding1.(_SVar x)
    | None -> failwith "trans01.trans_sort")

let mk_smeta nspc =
  Binding1.(_SMeta (SMeta.mk "") (box_list (sspine_of_nspc nspc)))

let mk_meta nspc =
  Binding1.(
    _IMeta (IMeta.mk "")
      (box_list (sspine_of_nspc nspc))
      (box_list (vspine_of_nspc nspc)))

let mk_inst nspc i =
  let ss = List.init i (fun _ -> mk_smeta nspc) in
  box_list ss

let mk_param nspc i =
  let ms = List.init i (fun _ -> mk_meta nspc) in
  box_list ms
