open Util
open Fmt
open Bindlib
open Names
open Syntax1
open Prelude1

let rec nat_of m =
  match m with
  | Cons (c, [], [], []) when C.equal c o_c -> Some 0
  | Cons (c, [], [], [ m ]) when C.equal c s_c -> Option.map succ (nat_of m)
  | _ -> None

let bin_of ms =
  List.fold_right
    (fun m opt ->
      Option.bind opt (fun acc ->
          match m with
          | Cons (c, [], [], []) when C.equal c true_c -> Some (true :: acc)
          | Cons (c, [], [], []) when C.equal c false_c -> Some (false :: acc)
          | _ -> None))
    ms (Some [])

let char_of m =
  match m with
  | Cons (c, [], [], ms) when C.equal c ascii_c ->
    Option.map char_of_bits (bin_of ms)
  | _ -> None

let rec string_of = function
  | Cons (c, [], [], []) when C.equal c emptyString_c -> Some ""
  | Cons (c, [], [], [ m; n ]) when C.equal c string_c -> (
    match (char_of m, string_of n) with
    | Some c, Some s -> Some (str "%c%s" c s)
    | _ -> None)
  | _ -> None

let pipe fmt _ = pf fmt " | "
let break fmt _ = pf fmt "@.@."

let pp_sort fmt = function
  | U -> pf fmt "U"
  | L -> pf fmt "L"
  | SVar x -> SV.pp fmt x
  | SMeta x -> pf fmt "?%a" M.pp x

let pp_role fmt = function
  | Pos -> pf fmt "!"
  | Neg -> pf fmt "?"

let pp_prim fmt = function
  | Stdin -> pf fmt "stdin"
  | Stdout -> pf fmt "stdout"
  | Stderr -> pf fmt "stderr"

let rec pp_xs fmt = function
  | [] -> ()
  | [ x ] -> pf fmt "%a" V.pp x
  | x :: xs -> pf fmt "%a %a" V.pp x pp_xs xs

let rec rel_gather r rxs =
  match rxs with
  | [] -> ([], [])
  | (r', x) :: rxs' ->
    if r' = r then
      let xs, rxs = rel_gather r rxs' in
      (x :: xs, rxs)
    else
      ([], rxs)

let rec pp_rxs fmt = function
  | [] -> ()
  | [ (r, x) ] -> (
    match r with
    | N -> pf fmt "{%a}" V.pp x
    | R -> pf fmt "%a" V.pp x)
  | (r, x) :: rxs -> (
    let xs, rxs = rel_gather r rxs in
    let xs = x :: xs in
    match (r, rxs) with
    | R, [] -> pf fmt "%a" pp_xs xs
    | R, _ -> pf fmt "%a %a" pp_xs xs pp_rxs rxs
    | N, [] -> pf fmt "{%a}" pp_xs xs
    | N, _ -> pf fmt "{%a} %a" pp_xs xs pp_rxs rxs)

let rec lam_gather s m =
  match m with
  | Lam (r, t, bnd) ->
    if eq_sort s t then
      let x, m = unbind bnd in
      let rxs, m = lam_gather s m in
      ((r, x) :: rxs, m)
    else
      ([], m)
  | m -> ([], m)

let rec pp_tm fmt = function
  (* inference *)
  | Ann (m, a) -> pf fmt "@[(%a@;<1 2>: %a)@]" pp_tm m pp_tm a
  | Meta (x, _) -> pf fmt "%a" M.pp x
  (* core *)
  | Type U -> pf fmt "U"
  | Type L -> pf fmt "L"
  | Type s -> pf fmt "Type‹%a›" pp_sort s
  | Var x -> V.pp fmt x
  | Const (x, []) -> V.pp fmt x
  | Const (x, ss) -> pf fmt "%a‹%a›" V.pp x (list ~sep:comma pp_sort) ss
  | Pi (R, U, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∀ (%a :@;<1 2>%a) →@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    else
      pf fmt "@[%a →@;<1 2>%a@]" pp_tm a pp_tm b
  | Pi (N, U, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∀ {%a :@;<1 2>%a} →@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    else
      pf fmt "@[{%a} →@;<1 2>%a@]" pp_tm a pp_tm b
  | Pi (R, L, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∀ (%a :@;<1 2>%a) ⊸@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    else
      pf fmt "@[%a ⊸@;<1 2>%a@]" pp_tm a pp_tm b
  | Pi (N, L, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∀ {%a :@;<1 2>%a} ⊸@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    else
      pf fmt "@[{%a} ⊸@;<1 2>%a@]" pp_tm a pp_tm b
  | Pi (R, s, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[forall‹%a›(%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_sort s V.pp x pp_tm
      a pp_tm b
  | Pi (N, s, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[forall‹%a›{%a :@;<1 2>%a},@]@;<1 2>%a@]" pp_sort s V.pp x pp_tm
      a pp_tm b
  | Lam (rel, U, bnd) ->
    let x, m = unbind bnd in
    let rxs, m = lam_gather U m in
    let rxs = (rel, x) :: rxs in
    pf fmt "@[fn %a ⇒@;<1 2>%a@]" pp_rxs rxs pp_tm m
  | Lam (rel, L, bnd) ->
    let x, m = unbind bnd in
    let rxs, m = lam_gather U m in
    let rxs = (rel, x) :: rxs in
    pf fmt "@[ln %a ⇒@;<1 2>%a@]" pp_rxs rxs pp_tm m
  | Lam (rel, s, bnd) ->
    let x, m = unbind bnd in
    let rxs, m = lam_gather s m in
    let rxs = (rel, x) :: rxs in
    pf fmt "@[function‹%a›%a,@;<1 2>%a@]" pp_sort s pp_rxs rxs pp_tm m
  | App _ as m ->
    let m, ms = unApps m in
    pf fmt "@[(%a@;<1 2>@[%a@])@]" pp_tm m (list ~sep:sp pp_tm) ms
  | Let (R, m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a =@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm n
  | Let (N, m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let {%a} =@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm
      n
  (* data *)
  | Sigma (R, U, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∃ (%a :@;<1 2>%a) ×@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    else
      pf fmt "@[%a ×@;<1 2>%a@]" pp_tm a pp_tm b
  | Sigma (N, U, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∃ {%a :@;<1 2>%a} ×@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    else
      pf fmt "@[{%a} ×@;<1 2>%a@]" pp_tm a pp_tm b
  | Sigma (R, L, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∃ (%a :@;<1 2>%a) ⊗@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    else
      pf fmt "@[%a ⊗@;<1 2>%a@]" pp_tm a pp_tm b
  | Sigma (N, L, a, bnd) ->
    let x, b = unbind bnd in
    if binder_occur bnd then
      pf fmt "@[@[∃ {%a :@;<1 2>%a} ⊗@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    else
      pf fmt "@[{%a} ⊗@;<1 2>%a@]" pp_tm a pp_tm b
  | Sigma (R, s, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[exists‹%a›(%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_sort s V.pp x pp_tm
      a pp_tm b
  | Sigma (N, s, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[exists‹%a›{%a :@;<1 2>%a},@]@;<1 2>%a@]" pp_sort s V.pp x pp_tm
      a pp_tm b
  | Pair (R, U, m, n) -> pf fmt "(%a, %a)" pp_tm m pp_tm n
  | Pair (N, U, m, n) -> pf fmt "({%a}, %a)" pp_tm m pp_tm n
  | Pair (R, L, m, n) -> pf fmt "⟨%a, %a⟩" pp_tm m pp_tm n
  | Pair (N, L, m, n) -> pf fmt "⟨{%a}, %a⟩" pp_tm m pp_tm n
  | Pair (R, s, m, n) -> pf fmt "tup‹%a›(%a, %a)" pp_sort s pp_tm m pp_tm n
  | Pair (N, s, m, n) -> pf fmt "tup‹%a›({%a}, %a)" pp_sort s pp_tm m pp_tm n
  | Data (d, ss, []) -> pf fmt "%a‹%a›" D.pp d (list ~sep:comma pp_sort) ss
  | Data (d, ss, ms) ->
    pf fmt "@[(%a‹%a›@;<1 2>@[%a@])@]" D.pp d (list ~sep:comma pp_sort) ss
      (list ~sep:sp pp_tm) ms
  | Cons (c, _, _, []) -> C.pp fmt c
  | Cons (c, _, _, ms) as m ->
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
  | Match (m, bnd, cls) ->
    let x, a = unbind bnd in
    pf fmt "@[<v 0>@[match %a as %a in@;<1 2>%a with@]@;<1 0>@[%a@]@;<1 0>end@]"
      pp_tm m V.pp x pp_tm a pp_cls cls
  (* equality *)
  | Eq (_, m, n) -> pf fmt "@[%a ≡@;<1 2>%a@]" pp_tm m pp_tm n
  | Refl m -> pf fmt "refl %a" pp_tm m
  | Rew (bnd, p, m) ->
    let xs, a = unmbind bnd in
    pf fmt "@[@[rew [%a, %a ⇒@;<1 2>%a]@;<1 2>%a in@]@;<1 0>%a@]" V.pp xs.(0)
      V.pp xs.(1) pp_tm a pp_tm p pp_tm m
  (* monadic *)
  | IO a -> pf fmt "IO %a" pp_tm a
  | Return m -> pf fmt "return %a" pp_tm m
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a ⇐@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm n
  (* session *)
  | Proto -> pf fmt "proto"
  | End -> pf fmt "end"
  | Act (R, rol, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[%a(%a :@;<1 2>%a) ⇒@]@;<1 2>%a@]" pp_role rol V.pp x pp_tm a
      pp_tm b
  | Act (N, rol, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "@[@[%a{%a :@;<1 2>%a} ⇒@]@;<1 2>%a@]" pp_role rol V.pp x pp_tm a
      pp_tm b
  | Ch (Pos, m) -> pf fmt "ch⟨%a⟩" pp_tm m
  | Ch (Neg, m) -> pf fmt "hc⟨%a⟩" pp_tm m
  | Open prim -> pf fmt "open %a" pp_prim prim
  | Fork (a, bnd) ->
    let x, m = unbind bnd in
    pf fmt "@[@[fork (%a :@;<1 2>%a)@;<1 0>in@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm
      m
  | Recv m -> pf fmt "recv %a" pp_tm m
  | Send m -> pf fmt "send %a" pp_tm m
  | Close m -> pf fmt "close %a" pp_tm m

and pp_cl fmt = function
  | PPair (R, U, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "| @[(%a, %a) ⇒@;<1 0>%a@]" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PPair (N, U, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "| @[({%a}, %a) ⇒@;<1 0>%a@]" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PPair (R, L, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "| @[⟨%a, %a⟩ ⇒@;<1 0>%a@]" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PPair (N, L, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "| @[⟨{%a}, %a⟩ ⇒@;<1 0>%a@]" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PPair (R, s, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "| @[tup‹%a›(%a, %a) ⇒@;<1 0>%a@]" pp_sort s V.pp xs.(0) V.pp xs.(1)
      pp_tm m
  | PPair (N, s, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "| @[tup‹%a›({%a}, %a) ⇒@;<1 0>%a@]" pp_sort s V.pp xs.(0) V.pp
      xs.(1) pp_tm m
  | PCons (c, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "| @[%a %a ⇒@;<1 0>%a@]" C.pp c (array ~sep:sp V.pp) xs pp_tm m

and pp_cls fmt = function
  | [] -> ()
  | [ cl ] -> pp_cl fmt cl
  | cl :: cls -> pf fmt "%a@;<1 0>%a" pp_cl cl pp_cls cls

let pp_scheme pp fmt sch =
  let rec loop = function
    | SBase m -> ([], m)
    | SBind bnd ->
      let x, sch = unbind bnd in
      let xs, m = loop sch in
      (x :: xs, m)
  in
  let xs, m = loop sch in
  match xs with
  | [] -> pf fmt "%a" pp m
  | _ -> pf fmt "@[‹%a›@]@;<1 2>%a" (list ~sep:comma SV.pp) xs pp m

let rec pp_ptm fmt = function
  | PBase b -> pf fmt ": %a" pp_tm b
  | PBind (a, bnd) ->
    let x, ptm = unbind bnd in
    pf fmt "(%a : %a) %a" V.pp x pp_tm a pp_ptm ptm

let rec pp_tele fmt = function
  | TBase b -> pf fmt ": %a" pp_tm b
  | TBind (R, a, bnd) ->
    let x, tl = unbind bnd in
    pf fmt "(%a : %a)@;<1 0>%a" V.pp x pp_tm a pp_tele tl
  | TBind (N, a, bnd) ->
    let x, tl = unbind bnd in
    pf fmt "{%a : %a}@;<1 0>%a" V.pp x pp_tm a pp_tele tl

let rec pp_ptl fmt = function
  | PBase tl -> pp_tele fmt tl
  | PBind (a, bnd) ->
    let x, ptl = unbind bnd in
    pf fmt "(%a : %a)@;<1 0>%a" V.pp x pp_tm a pp_ptl ptl

let rec pp_dcons fmt (DCons (c, sch)) =
  pf fmt "| @[%a of@;<1 2>@[%a@]@]" C.pp c (pp_scheme pp_ptl) sch

let rec pp_dconss fmt = function
  | [] -> ()
  | [ dcons ] -> pp_dcons fmt dcons
  | dcons :: dconss -> pf fmt "%a@;<1 0>%a" pp_dcons dcons pp_dconss dconss

let rec pp_dcl fmt = function
  | DTm (R, x, sch) ->
    pf fmt "@[program %a%a@]" V.pp x
      (pp_scheme (fun fmt (a, m) ->
           pf fmt " :@;<1 2>%a@;<1 0>=@;<1 2>%a" pp_tm a pp_tm m))
      sch
  | DTm (N, x, sch) ->
    pf fmt "@[logical %a%a@]" V.pp x
      (pp_scheme (fun fmt (a, m) ->
           pf fmt " :@;<1 2>%a@;<1 0>=@;<1 2>%a" pp_tm a pp_tm m))
      sch
  | DData (d, sch, dconss) ->
    pf fmt "@[<v 0>@[inductive %a@;<1 2>%a@;<1 0>=@]@;<1 0>@[%a@]@]" D.pp d
      (pp_scheme pp_ptm) sch pp_dconss dconss

let pp_dcls fmt dcls = pf fmt "%a" (list ~sep:break pp_dcl) dcls
