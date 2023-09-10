open Fmt
open Bindlib
open Names
open Syntax3

let pipe fmt _ = pf fmt " | "
let break fmt _ = pf fmt "@.@."

let rec gather_lam = function
  | Lam (relv, s, bnd) ->
    let x, m = unbind bnd in
    let xs, m = gather_lam m in
    ((relv, s, x) :: xs, m)
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
  | [ (R, U, x) ] -> pf fmt "(%a) ->" Var.pp x
  | [ (R, L, x) ] -> pf fmt "(%a) -o" Var.pp x
  | [ (N, U, x) ] -> pf fmt "{%a} ->" Var.pp x
  | [ (N, L, x) ] -> pf fmt "{%a} -o" Var.pp x
  | (R, U, x) :: rxs -> pf fmt "(%a) ->@;<1 0>%a" Var.pp x pp_rxs rxs
  | (R, L, x) :: rxs -> pf fmt "(%a) -o@;<1 0>%a" Var.pp x pp_rxs rxs
  | (N, U, x) :: rxs -> pf fmt "{%a} ->@;<1 0>%a" Var.pp x pp_rxs rxs
  | (N, L, x) :: rxs -> pf fmt "{%a} -o@;<1 0>%a" Var.pp x pp_rxs rxs

and pp_tm fmt = function
  (* core *)
  | Var x -> Var.pp fmt x
  | Const x -> pf fmt "%a" Const.pp x
  | Fun bnd ->
    let x, m = unbind bnd in
    let rxs, m = gather_lam m in
    pf fmt "@[<v 0>@[fun %a %a@;<1 2>@[%a@]@]" Var.pp x pp_rxs rxs pp_tm m
  | Lam _ as m ->
    let rxs, m = gather_lam m in
    pf fmt "@[lam %a@;<1 2>@[%a@]@]" pp_rxs rxs pp_tm m
  | App _ as m ->
    let hd, ms = unApps m in
    pf fmt "@[((%a)@;<1 2>@[%a@])@]" pp_tm hd pp_spine ms
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a :=@;<1 2>%a@]@;<1 0>in@;<1 0>%a@]" Var.pp x pp_tm m pp_tm n
  (* inductive *)
  | Constr0 c -> pf fmt "%a" Constr.pp c
  | Constr1 (c, ms) ->
    pf fmt "@[(%a@;<1 2>@[%a@])@]" Constr.pp c (list ~sep:sp pp_tm) ms
  | Match0 (m, cls) ->
    pf fmt "@[<v 0>@[match %a with@]@;<1 0>@[%a@]@;<1 0>end@]" pp_tm m pp_cl0s cls
  | Match1 (_, m, cls) ->
    pf fmt "@[<v 0>@[match %a with@]@;<1 0>@[%a@]@;<1 0>end@]" pp_tm m pp_cl1s cls
  | Absurd -> pf fmt "!!"
  (* lazy *)
  | Lazy m -> pf fmt "@[lazy(@[%a@])@]" pp_tm m
  | Force m -> pf fmt "@[force(@[%a@])@]" pp_tm m
  (* primitive terms *)
  | Int i -> pf fmt "%d" i
  | Char c -> pf fmt "%c" c
  | String s -> pf fmt "%s" s
  (* primitive operators *)
  | Neg m -> pf fmt "@[(__neg__@;<1 2>@[%a@])@]" pp_tm m
  | Add (m, n) -> pf fmt "@[(__add__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Sub (m, n) -> pf fmt "@[(__sub__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Mul (m, n) -> pf fmt "@[(__mul__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Div (m, n) -> pf fmt "@[(__div__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Mod (m, n) -> pf fmt "@[(__mod__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Lte (m, n) -> pf fmt "@[(__lte__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Gte (m, n) -> pf fmt "@[(__gte__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Lt (m, n) -> pf fmt "@[(__lt__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Gt (m, n) -> pf fmt "@[(__gt__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Eq (m, n) -> pf fmt "@[(__eq__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Chr m -> pf fmt "@[(__chr__@;<1 2>@[%a@])@]" pp_tm m
  | Ord m -> pf fmt "@[(__ord__@;<1 2>@[%a@])@]" pp_tm m
  | Push (m, n) -> pf fmt "@[(__push__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Cat (m, n) -> pf fmt "@[(__cat__@;<1 2>@[%a@]@;<1 2>@[%a@])@]" pp_tm m pp_tm n
  | Size m -> pf fmt "@[(__size__@;<1 2>@[%a@])@]" pp_tm m
  | Indx (m, n) -> pf fmt "@[%a.[%a]@]" pp_tm m pp_tm n
  (* primitive effects *)
  | Print m -> pf fmt "@[print@;<1 2>%a@]" pp_tm m
  | Prerr m -> pf fmt "@[prerr@;<1 2>%a@]" pp_tm m
  | ReadLn m -> pf fmt "@[readln@;<1 2>%a@]" pp_tm m
  | Fork m -> pf fmt "@[fork@;<1 2>@[%a@]@]" pp_tm m
  | Send (m, n) -> pf fmt "@[send(%a, %a)@]" pp_tm m pp_tm n
  | Recv (s, m) -> pf fmt "@[recv[%a](%a)@]" pp_sort s pp_tm m
  | Close (role, m) -> pf fmt "@[close[%b]@;<1 2>%a@]" role pp_tm m
  (* erasure *)
  | NULL -> pf fmt "NULL"
  (* magic *)
  | Magic -> pf fmt "#magic"

and pp_spine fmt = function
  | [] -> ()
  | (n, _) :: [] -> pf fmt "%a" pp_tm n
  | (n, _) :: spine -> pf fmt "%a@;<1 2>%a" pp_tm n pp_spine spine

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
