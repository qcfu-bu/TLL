open Fmt
open Bindlib
open Names
open Syntax3

let pipe fmt _ = pf fmt " | "
let break fmt _ = pf fmt "@.@."

let rec gather_lam = function
  | Lam0 (s, m) ->
    let xs, m = gather_lam m in
    ((s, None) :: xs, m)
  | Lam1 (s, bnd) ->
    let x, m = unbind bnd in
    let xs, m = gather_lam m in
    ((s, Some x) :: xs, m)
  | m -> ([], m)

let pp_sort fmt = function
  | U -> pf fmt "U"
  | L -> pf fmt "L"

let rec pp_sorts fmt = function
  | [] -> ()
  | [ s ] -> pp_sort fmt s
  | s :: ss -> pf fmt "%a,%a" pp_sort s pp_sorts ss

let rec pp_rxs fmt = function
  | [] -> ()
  | [ (s, opt) ] -> (
    match (s, opt) with
    | U, None -> pf fmt "() ->"
    | L, None -> pf fmt "() -o"
    | U, Some x -> pf fmt "(%a) ->" Var.pp x
    | L, Some x -> pf fmt "(%a) -o" Var.pp x)
  | (s, opt) :: rxs -> (
    match (s, opt) with
    | U, None -> pf fmt "() ->@;<1 0>%a" pp_rxs rxs
    | L, None -> pf fmt "() -o@;<1 0>%a" pp_rxs rxs
    | U, Some x -> pf fmt "(%a) ->@;<1 0>%a" Var.pp x pp_rxs rxs
    | L, Some x -> pf fmt "(%a) -o@;<1 0>%a" Var.pp x pp_rxs rxs)

and pp_tm fmt = function
  (* core *)
  | Var x -> Var.pp fmt x
  | Const x -> pf fmt "%a" Const.pp x
  | Fun bnd ->
    let x, m = unbind bnd in
    let rxs, m = gather_lam m in
    pf fmt "@[<v 0>@[fun %a %a@;<1 2>@[%a@]@]" Var.pp x pp_rxs rxs pp_tm m
  | Lam0 _ as m ->
    let rxs, m = gather_lam m in
    pf fmt "@[lam %a@;<1 2>@[%a@]@]" pp_rxs rxs pp_tm m
  | Lam1 _ as m ->
    let rxs, m = gather_lam m in
    pf fmt "@[lam %a@;<1 2>@[%a@]@]" pp_rxs rxs pp_tm m
  | App0 _ as m ->
    let hd, ms = unApps m in
    pf fmt "@[((%a)@;<1 2>@[%a@])@]" pp_tm hd pp_spine ms
  | App1 _ as m ->
    let hd, ms = unApps m in
    pf fmt "@[((%a)@;<1 2>@[%a@])@]" pp_tm hd pp_spine ms
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" Var.pp x pp_tm m pp_tm
      n
  (* inductive *)
  | Constr0 c -> pf fmt "%a" Constr.pp c
  | Constr1 (c, ms) ->
    pf fmt "@[(%a@;<1 2>@[%a@])@]" Constr.pp c (list ~sep:sp pp_tm) ms
  | Match0 (m, cls) ->
    pf fmt "@[<v 0>@[match %a with@]@;<1 0>@[%a@]@;<1 0>end@]" pp_tm m pp_cl0s
      cls
  | Match1 (_, m, cls) ->
    pf fmt "@[<v 0>@[match %a with@]@;<1 0>@[%a@]@;<1 0>end@]" pp_tm m pp_cl1s
      cls
  | Absurd -> pf fmt "!!"
  (* magic *)
  | Magic -> pf fmt "#magic"

and pp_spine fmt = function
  | [] -> ()
  | None :: [] -> pf fmt "()"
  | None :: spine -> pf fmt "()@;<1 2>%a" pp_spine spine
  | Some (n, _) :: [] -> pf fmt "%a" pp_tm n
  | Some (n, _) :: spine -> pf fmt "%a@;<1 2>%a" pp_tm n pp_spine spine

and pp_cl0 fmt (c, rhs) = pf fmt "| @[%a =>@;<1 0>%a@]" Constr.pp c pp_tm rhs

and pp_cl0s fmt = function
  | [] -> ()
  | [ cl ] -> pp_cl0 fmt cl
  | cl :: cls -> pf fmt "%a@;<1 0>%a" pp_cl0 cl pp_cl0s cls

and pp_cl1 fmt (c, bnd) =
  let xs, rhs = unmbind bnd in
  pf fmt "| @[%a %a =>@;<1 0>%a@]" Constr.pp c (array ~sep:sp Var.pp) xs pp_tm
    rhs

and pp_cl1s fmt = function
  | [] -> ()
  | [ cl ] -> pp_cl1 fmt cl
  | cl :: cls -> pf fmt "%a@;<1 0>%a" pp_cl1 cl pp_cl1s cls

let rec pp_dcl fmt = function
  | Main { body } -> pf fmt "@[def main :=@;<1 2>@[%a@]@]" pp_tm body
  | Definition { name; body } ->
    pf fmt "@[def %a :=@;<1 2>@[%a@]@]" Const.pp name pp_tm body

let pp_dcls fmt dcls = pf fmt "%a" (list ~sep:break pp_dcl) dcls
