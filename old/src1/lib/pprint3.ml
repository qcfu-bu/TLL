open Util
open Fmt
open Bindlib
open Names
open Syntax3
open Prelude1

let rec nat_of m =
  match m with
  | Cons (c, []) when C.equal c o_c -> Some 0
  | Cons (c, [ m ]) when C.equal c s_c -> Option.map succ (nat_of m)
  | _ -> None

let bin_of ms =
  List.fold_right
    (fun m opt ->
      Option.bind opt (fun acc ->
          match m with
          | Cons (c, []) when C.equal c true_c -> Some (true :: acc)
          | Cons (c, []) when C.equal c false_c -> Some (false :: acc)
          | _ -> None))
    ms (Some [])

let char_of m =
  match m with
  | Cons (c, ms) when C.equal c ascii_c -> Option.map char_of_bits (bin_of ms)
  | _ -> None

let rec string_of = function
  | Cons (c, []) when C.equal c emptyString_c -> Some ""
  | Cons (c, [ m; n ]) when C.equal c string_c -> (
    match (char_of m, string_of n) with
    | Some c, Some s -> Some (str "%c%s" c s)
    | _ -> None)
  | _ -> None

let pipe fmt _ = pf fmt " | "
let break fmt _ = pf fmt "@.@."

let rec pp_sort fmt = function
  | U -> pf fmt "U"
  | L -> pf fmt "L"

let pp_prim fmt = function
  | Stdin -> pf fmt "stdin"
  | Stdout -> pf fmt "stdout"
  | Stderr -> pf fmt "stderr"

let rec gather_lam s m =
  match m with
  | Lam (t, bnd) ->
    if s = t then
      let x, m = unbind bnd in
      let xs, m = gather_lam s m in
      (x :: xs, m)
    else
      ([], m)
  | _ -> ([], m)

and pp_tm fmt = function
  (* core *)
  | Var x -> V.pp fmt x
  | Const x -> pf fmt "%a" I.pp x
  | Lam (s, bnd) -> (
    let x, m = unbind bnd in
    let xs, m = gather_lam s m in
    let xs = x :: xs in
    match s with
    | U -> pf fmt "@[fn @[%a@] ⇒@;<1 2>@[%a@]@]" (list ~sep:sp V.pp) xs pp_tm m
    | L -> pf fmt "@[ln @[%a@] ⇒@;<1 2>@[%a@]@]" (list ~sep:sp V.pp) xs pp_tm m)
  | Call (x, ms) -> pf fmt "@[%a(@[%a@])@]" I.pp x (list ~sep:comma pp_tm) ms
  | App (_, m, n) -> pf fmt "@[(%a)@;<1 2>@[%a@]@]" pp_tm m pp_tm n
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a =@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm n
  (* data *)
  | Pair (m, n) -> pf fmt "(%a, %a)" pp_tm m pp_tm n
  | Cons (c, []) -> pf fmt "%a" C.pp c
  | Cons (c, ms) as m ->
    if C.equal c o_c || C.equal c s_c then
      match nat_of m with
      | Some n -> pf fmt "%d" n
      | None -> pf fmt "@[(%a@;<1 2>@[%a@])@]" C.pp c (list ~sep:sp pp_tm) ms
    else if C.equal c ascii_c then
      match char_of m with
      | Some c -> pf fmt "%C" c
      | None -> pf fmt "@[(%a@;<1 2>@[%a@])@]" C.pp c (list ~sep:sp pp_tm) ms
    else if C.equal c string_c then
      match string_of m with
      | Some s -> pf fmt "%S" s
      | None -> pf fmt "@[(%a@;<1 2>@[%a@])@]" C.pp c (list ~sep:sp pp_tm) ms
    else
      pf fmt "@[(%a@;<1 2>@[%a@])@]" C.pp c (list ~sep:sp pp_tm) ms
  | Match (_, m, cls) ->
    pf fmt "@[<v 0>@[match %a with@]@;<1 0>@[%a@]@;<1 0>end@]" pp_tm m pp_cls
      cls
  (* effect *)
  | Open prim -> pf fmt "open %a" pp_prim prim
  | Fork bnd ->
    let x, m = unbind bnd in
    pf fmt "@[@[fork %a in@]@;<1 2>%a@]" V.pp x pp_tm m
  | Recv m -> pf fmt "recv(%a)" pp_tm m
  | Send (m, n) -> pf fmt "send(%a, %a)" pp_tm m pp_tm n
  | Close m -> pf fmt "close(%a)" pp_tm m
  | NULL -> pf fmt "NULL"

and pp_cl fmt = function
  | PPair bnd ->
    let xs, m = unmbind bnd in
    pf fmt "| @[(%a, %a) ⇒@;<1 0>%a@]" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PCons (c, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "| @[%a %a ⇒@;<1 0>%a@]" C.pp c (array ~sep:sp V.pp) xs pp_tm m

and pp_cls fmt = function
  | [] -> ()
  | [ cl ] -> pp_cl fmt cl
  | cl :: cls -> pf fmt "%a@;<1 0>%a" pp_cl cl pp_cls cls

let rec pp_dcl fmt = function
  | DFun (x, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "@[fun %a(%a) =@;<1 2>%a@]" I.pp x (array ~sep:comma V.pp) xs pp_tm m
  | DVal (x, m) -> pf fmt "@[val %a =@;<1 2>%a@]" I.pp x pp_tm m
  | DMain m -> pf fmt "@[main =@;<1 2>%a@]" pp_tm m

let pp_dcls fmt dcls = pf fmt "%a" (list ~sep:break pp_dcl) dcls
