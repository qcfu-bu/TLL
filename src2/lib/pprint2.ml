open Util
open Fmt
open Bindlib
open Names
open Syntax2
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

let pp_role fmt = function
  | Pos -> pf fmt "⇑"
  | Neg -> pf fmt "⇓"

let pp_prim fmt = function
  | Stdin -> pf fmt "stdin"
  | Stdout -> pf fmt "stdout"
  | Stderr -> pf fmt "stderr"

let rec lam_gather m =
  match m with
  | Lam bnd ->
    let x, m = unbind bnd in
    let xs, m = lam_gather m in
    (x :: xs, m)
  | m -> ([], m)

and pp_tm fmt = function
  (* core *)
  | Var x -> V.pp fmt x
  | Const x -> pf fmt "%a" I.pp x
  | Lam _ as m ->
    let xs, m = lam_gather m in
    pf fmt "@[fn @[%a@] ⇒@;<1 2>@[%a@]@]" (list ~sep:sp V.pp) xs pp_tm m
  | App (_, m, n) -> pf fmt "@[(%a@;<1 2>@[%a@])@]" pp_tm m pp_tm n
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
  (* monadic *)
  | Return m -> pf fmt "return %a" pp_tm m
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a ⇐@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm n
  (* session *)
  | Open prim -> pf fmt "open %a" pp_prim prim
  | Fork bnd ->
    let x, m = unbind bnd in
    pf fmt "@[@[fork %a in@]@;<1 2>%a@]" V.pp x pp_tm m
  | Recv (R, m) -> pf fmt "recv %a" pp_tm m
  | Send (R, m) -> pf fmt "send %a" pp_tm m
  | Recv (N, m) -> pf fmt "{recv} %a" pp_tm m
  | Send (N, m) -> pf fmt "{send} %a" pp_tm m
  | Close (rol, m) -> pf fmt "close%a %a" pp_role rol pp_tm m
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

let rec pp_dcons fmt (DCons (c, i)) = pf fmt "| @[%a of size(%d)@]" C.pp c i

let rec pp_dconss fmt = function
  | [] -> ()
  | [ dcons ] -> pp_dcons fmt dcons
  | dcons :: dconss -> pf fmt "%a@;<1 0>%a" pp_dcons dcons pp_dconss dconss

let rec pp_dcl fmt = function
  | DTm (x, m) -> pf fmt "@[def %a =@;<1 2>%a@]" I.pp x pp_tm m
  | DData (d, dconss) ->
    pf fmt "@[<v 0>@[data %a =@]@;<1 0>@[%a@]@]" D.pp d pp_dconss dconss
  | DMain m -> pf fmt "@[main =@;<1 2>%a@]" pp_tm m

let pp_dcls fmt dcls = pf fmt "%a" (list ~sep:break pp_dcl) dcls
