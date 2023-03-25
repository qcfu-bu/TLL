open Fmt
open Bindlib
open Names
open Syntax1

let pipe fmt _ = pf fmt " | "
let break fmt _ = pf fmt "@.@."

let pp_sort fmt = function
  | U -> pf fmt "U"
  | L -> pf fmt "L"

let pp_role fmt = function
  | Pos -> pf fmt "!"
  | Neg -> pf fmt "?"

let pp_prim fmt = function
  | Stdin -> pf fmt "stdin"
  | Stdout -> pf fmt "stdout"
  | Stderr -> pf fmt "stderr"

let rec pp_tm fmt = function
  (* inference *)
  | Ann (m, a) -> pf fmt "(%a : %a)" pp_tm m pp_tm a
  | Meta (x, ms) -> pf fmt "%a[%a]" M.pp x (list ~sep:semi pp_tm) ms
  (* core *)
  | Type s -> pp_sort fmt s
  | Var x -> V.pp fmt x
  | Pi (R, U, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "(∀ (%a : %a) → %a)" V.pp x pp_tm a pp_tm b
  | Pi (N, U, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "(∀ {%a : %a} → %a)" V.pp x pp_tm a pp_tm b
  | Pi (R, L, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "(∀ (%a : %a) ⊸ %a)" V.pp x pp_tm a pp_tm b
  | Pi (N, L, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "(∀ {%a : %a} ⊸ %a)" V.pp x pp_tm a pp_tm b
  | Lam (R, U, bnd) ->
    let x, m = unbind bnd in
    pf fmt "(fn %a ⇒ %a)" V.pp x pp_tm m
  | Lam (N, U, bnd) ->
    let x, m = unbind bnd in
    pf fmt "(fn {%a} ⇒ %a)" V.pp x pp_tm m
  | Lam (R, L, bnd) ->
    let x, m = unbind bnd in
    pf fmt "(ln %a ⇒ %a)" V.pp x pp_tm m
  | Lam (N, L, bnd) ->
    let x, m = unbind bnd in
    pf fmt "(ln {%a} ⇒ %a)" V.pp x pp_tm m
  | App _ as m ->
    let m, ms = unApps m in
    pf fmt "(%a %a)" pp_tm m (list ~sep:sp pp_tm) ms
  | Let (R, m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "let %a = %a in %a" V.pp x pp_tm m pp_tm n
  | Let (N, m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "let {%a} = %a in %a" V.pp x pp_tm m pp_tm n
  | Fix (x, bnd) ->
    let r, m = unbind bnd in
    pf fmt "fix (%a := %a) ⇒ %a" V.pp x V.pp r pp_tm m
  (* data *)
  | Sigma (R, U, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "(∃ (%a : %a) × %a)" V.pp x pp_tm a pp_tm b
  | Sigma (N, U, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "(∃ {%a : %a} × %a)" V.pp x pp_tm a pp_tm b
  | Sigma (R, L, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "(∃ (%a : %a) ⊗ %a)" V.pp x pp_tm a pp_tm b
  | Sigma (N, L, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "(∃ {%a : %a} ⊗ %a)" V.pp x pp_tm a pp_tm b
  | Pair (R, U, m, n) -> pf fmt "(%a, %a)" pp_tm m pp_tm n
  | Pair (N, U, m, n) -> pf fmt "({%a}, %a)" pp_tm m pp_tm n
  | Pair (R, L, m, n) -> pf fmt "⟨%a, %a⟩" pp_tm m pp_tm n
  | Pair (N, L, m, n) -> pf fmt "⟨{%a}, %a⟩" pp_tm m pp_tm n
  | Data (d, []) -> D.pp fmt d
  | Data (d, ms) -> pf fmt "(%a %a)" D.pp d (list ~sep:sp pp_tm) ms
  | Cons (c, []) -> C.pp fmt c
  | Cons (c, ms) -> pf fmt "(%a %a)" C.pp c (list ~sep:sp pp_tm) ms
  | Match (m, bnd, cls) ->
    let x, a = unbind bnd in
    pf fmt "match %a [ %a ⇒ %a ] with %a" pp_tm m V.pp x pp_tm a pp_cls cls
  (* equality *)
  | Eq (m, n) -> pf fmt "%a ≡ %a" pp_tm m pp_tm n
  | Refl -> pf fmt "refl"
  | Rew (bnd, p, m) ->
    let xs, a = unmbind bnd in
    pf fmt "rew [ %a, %a ⇒ %a ] %a in %a" V.pp xs.(0) V.pp xs.(1) pp_tm a pp_tm
      p pp_tm m
  (* monadic *)
  | IO a -> pf fmt "IO %a" pp_tm a
  | Return m -> pf fmt "return %a" pp_tm m
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "let %a ⇐ %a in %a" V.pp x pp_tm m pp_tm n
  (* session *)
  | Proto -> pf fmt "proto"
  | End -> pf fmt "end"
  | Act (R, rol, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "%a(%a : %a) ⇒ %a" pp_role rol V.pp x pp_tm a pp_tm b
  | Act (N, rol, a, bnd) ->
    let x, b = unbind bnd in
    pf fmt "%a{%a : %a} ⇒ %a" pp_role rol V.pp x pp_tm a pp_tm b
  | Ch (Pos, m) -> pf fmt "ch‹%a›" pp_tm m
  | Ch (Neg, m) -> pf fmt "hc‹%a›" pp_tm m
  | Open prim -> pf fmt "open %a" pp_prim prim
  | Fork (a, bnd) ->
    let x, m = unbind bnd in
    pf fmt "fork (%a : %a) in %a" V.pp x pp_tm a pp_tm m
  | Recv m -> pf fmt "recv %a" pp_tm m
  | Send m -> pf fmt "send %a" pp_tm m
  | Close m -> pf fmt "close %a" pp_tm m

and pp_cl fmt = function
  | PPair (R, U, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "(%a, %a) ⇒ %a" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PPair (N, U, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "({%a}, %a) ⇒ %a" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PPair (R, L, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "⟨%a, %a⟩ ⇒ %a" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PPair (N, L, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "⟨{%a}, %a⟩ ⇒ %a" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PCons (c, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "%a %a ⇒ %a" C.pp c (array ~sep:sp V.pp) xs pp_tm m

and pp_cls fmt cls = list ~sep:pipe pp_cl fmt cls

let rec pp_ptm fmt = function
  | PBase b -> pf fmt ": %a" pp_tm b
  | PBind (a, bnd) ->
    let x, ptm = unbind bnd in
    pf fmt "(%a : %a) %a" V.pp x pp_tm a pp_ptm ptm

let rec pp_tele fmt = function
  | TBase b -> pf fmt ": %a" pp_tm b
  | TBind (R, a, bnd) ->
    let x, tl = unbind bnd in
    pf fmt "(%a : %a) %a" V.pp x pp_tm a pp_tele tl
  | TBind (N, a, bnd) ->
    let x, tl = unbind bnd in
    pf fmt "{%a : %a} %a" V.pp x pp_tm a pp_tele tl

let rec pp_ptl fmt = function
  | PBase tl -> pp_tele fmt tl
  | PBind (a, bnd) ->
    let x, ptl = unbind bnd in
    pf fmt "(%a : %a) %a" V.pp x pp_tm a pp_ptl ptl

let rec pp_dcons fmt (DCons (c, ptl)) = pf fmt "%a of %a" C.pp c pp_ptl ptl

let rec pp_dcl fmt = function
  | DTm (R, x, a, m) -> pf fmt "definition %a : %a = %a" V.pp x pp_tm a pp_tm m
  | DTm (N, x, a, m) -> pf fmt "theorem %a : %a = %a" V.pp x pp_tm a pp_tm m
  | DData (d, ptm, dconss) ->
    pf fmt "inductive %a %a = %a" D.pp d pp_ptm ptm (list ~sep:pipe pp_dcons)
      dconss

let pp_dcls fmt dcls = pf fmt "%a" (list ~sep:break pp_dcl) dcls
