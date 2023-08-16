open Fmt
open Bindlib
open Names
open Syntax2

let pipe fmt _ = pf fmt " | "
let break fmt _ = pf fmt "@.@."

let pp_sort fmt = function
  | U -> pf fmt "U"
  | L -> pf fmt "L"

let rec pp_sorts fmt = function
  | [] -> ()
  | [ s ] -> pp_sort fmt s
  | s :: ss -> pf fmt "%a,%a" pp_sort s pp_sorts ss

let pp_modifier fmt = function
  | R -> pf fmt "program"
  | N -> pf fmt "logical"

let rec pp_rxs fmt = function
  | [] -> ()
  | [ (r, x, a) ] -> (
    match r with
    | N -> pf fmt "{%a : %a}" Var.pp x pp_tm a
    | R -> pf fmt "(%a : %a)" Var.pp x pp_tm a)
  | (r, x, a) :: rxs -> (
    match r with
    | R -> pf fmt "(%a : %a)@;<1 0>%a" Var.pp x pp_tm a pp_rxs rxs
    | N -> pf fmt "{%a : %a}@;<1 0>%a" Var.pp x pp_tm a pp_rxs rxs)

and pp_tm fmt = function
  (* core *)
  | Var x -> Var.pp fmt x
  | Const x -> pf fmt "%a" Const.pp x
  | Fun bnd ->
    let x, bnd = unbind bnd in
    let xs, m = unmbind bnd in
    pf fmt "@[<v 0>@[fun %a (%a) =>@;<1 2>@[%a@]@]" Var.pp x
      (array ~sep:comma Var.pp) xs pp_tm m
  | App _ as m ->
    let hd, ms = unApps m in
    let ms = List.map fst ms in
    pf fmt "@[((%a)@;<1 2>@[%a@])@]" pp_tm hd (list ~sep:sp pp_tm) ms
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" Var.pp x pp_tm m pp_tm
      n
  (* inductive *)
  | Constr (c, []) -> pf fmt "%a" Constr.pp c
  | Constr (c, ms) ->
    pf fmt "@[(%a@;<1 2>@[%a@])@]" Constr.pp c (list ~sep:sp pp_tm) ms
  | Match (R, _, m, cls) ->
    pf fmt "@[<v 0>@[match %a with@]@;<1 0>@[%a@]@;<1 0>end@]" pp_tm m pp_cls
      cls
  | Match (N, _, m, cls) ->
    pf fmt "@[<v 0>@[match {%a} with@]@;<1 0>@[%a@]@;<1 0>end@]" pp_tm m pp_cls
      cls
  | Absurd -> pf fmt "!!"
  (* monad *)
  | Return m -> pf fmt "return %a" pp_tm m
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let* %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" Var.pp x pp_tm m
      pp_tm n
  (* erasure *)
  | NULL -> pf fmt "NULL"
  (* magic *)
  | Magic -> pf fmt "#magic"

and pp_cl fmt (c, bnd) =
  let xs, rhs = unmbind bnd in
  pf fmt "| @[%a %a =>@;<1 0>%a@]" Constr.pp c (array ~sep:sp Var.pp) xs pp_tm
    rhs

and pp_cls fmt = function
  | [] -> ()
  | [ cl ] -> pp_cl fmt cl
  | cl :: cls -> pf fmt "%a@;<1 0>%a" pp_cl cl pp_cls cls

let rec pp_dconstr fmt (c, i) = pf fmt "| @[%a of size(%d)@]" Constr.pp c i

let rec pp_dconstrs fmt = function
  | [] -> ()
  | [ dconstr ] -> pp_dconstr fmt dconstr
  | dconstr :: dconstrs ->
    pf fmt "%a@;<1 0>%a" pp_dconstr dconstr pp_dconstrs dconstrs

let rec pp_dcl fmt = function
  | Definition { name; body } ->
    pf fmt "@[def %a :=@;<1 2>%a@]" Const.pp name pp_tm body
  | Inductive { name; body } ->
    pf fmt "@[<v 0>@[inductive %a where@]@;<1 0>@[%a@]@]" Ind.pp name
      pp_dconstrs body

let pp_dcls fmt dcls = pf fmt "%a" (list ~sep:break pp_dcl) dcls
