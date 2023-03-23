open Fmt
open Bindlib
open Names
open Syntax1

let pipe fmt _ = pf fmt "|"
let break fmt _ = pf fmt "@.@."
let pp_sort fmt = function U -> pf fmt "U" | L -> pf fmt "L"
let pp_role fmt = function Pos -> pf fmt "!" | Neg -> pf fmt "?"

let pp_prim fmt = function
  | Stdin -> pf fmt "stdin"
  | Stdout -> pf fmt "stdout"
  | Stderr -> pf fmt "stderr"

let rec pp0_tm ctx0 fmt = function
  (* inference *)
  | Ann (m, a) -> pf fmt "(%a : %a)" (pp0_tm ctx0) m (pp0_tm ctx0) a
  | Meta (x, _) -> M.pp fmt x
  (* core *)
  | Type s -> pp_sort fmt s
  | Var x -> V.pp fmt x
  | Pi (R, U, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "(∀ (%a : %a) → %a)" V.pp x (pp0_tm ctx0) a (pp0_tm ctx) b
  | Pi (N, U, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "(∀ {%a : %a} → %a)" V.pp x (pp0_tm ctx0) a (pp0_tm ctx) b
  | Pi (R, L, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "(∀ (%a : %a) ⊸ %a)" V.pp x (pp0_tm ctx0) a (pp0_tm ctx) b
  | Pi (N, L, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "(∀ {%a : %a} ⊸ %a)" V.pp x (pp0_tm ctx0) a (pp0_tm ctx) b
  | Lam (R, U, bnd) ->
      let x, m, ctx = unbind_in ctx0 bnd in
      pf fmt "(fn %a ⇒ %a)" V.pp x (pp0_tm ctx) m
  | Lam (N, U, bnd) ->
      let x, m, ctx = unbind_in ctx0 bnd in
      pf fmt "(fn {%a} ⇒ %a)" V.pp x (pp0_tm ctx) m
  | Lam (R, L, bnd) ->
      let x, m, ctx = unbind_in ctx0 bnd in
      pf fmt "(ln %a ⇒ %a)" V.pp x (pp0_tm ctx) m
  | Lam (N, L, bnd) ->
      let x, m, ctx = unbind_in ctx0 bnd in
      pf fmt "(ln {%a} ⇒ %a)" V.pp x (pp0_tm ctx) m
  | App (m, n) -> pf fmt "(%a) %a" (pp0_tm ctx0) m (pp0_tm ctx0) n
  | Let (R, m, bnd) ->
      let x, n, ctx = unbind_in ctx0 bnd in
      pf fmt "let %a = %a in %a" V.pp x (pp0_tm ctx0) m (pp0_tm ctx) n
  | Let (N, m, bnd) ->
      let x, n, ctx = unbind_in ctx0 bnd in
      pf fmt "let {%a} = %a in %a" V.pp x (pp0_tm ctx0) m (pp0_tm ctx) n
  | Fix (x, bnd) ->
      let r, m, ctx = unbind_in ctx0 bnd in
      pf fmt "fix (%a := %a) ⇒ %a" V.pp x V.pp r (pp0_tm ctx) m
  (* data *)
  | Sigma (R, U, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "(∃ (%a : %a) × %a)" V.pp x (pp0_tm ctx0) a (pp0_tm ctx) b
  | Sigma (N, U, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "(∃ {%a : %a} × %a)" V.pp x (pp0_tm ctx0) a (pp0_tm ctx) b
  | Sigma (R, L, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "(∃ (%a : %a) ⊗ %a)" V.pp x (pp0_tm ctx0) a (pp0_tm ctx) b
  | Sigma (N, L, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "(∃ {%a : %a} ⊗ %a)" V.pp x (pp0_tm ctx0) a (pp0_tm ctx) b
  | Pair (R, U, m, n) -> pf fmt "(%a, %a)" (pp0_tm ctx0) m (pp0_tm ctx0) n
  | Pair (N, U, m, n) -> pf fmt "({%a}, %a)" (pp0_tm ctx0) m (pp0_tm ctx0) n
  | Pair (R, L, m, n) -> pf fmt "⟨%a, %a⟩" (pp0_tm ctx0) m (pp0_tm ctx0) n
  | Pair (N, L, m, n) -> pf fmt "⟨{%a}, %a⟩" (pp0_tm ctx0) m (pp0_tm ctx0) n
  | Data (d, ms) -> pf fmt "(%a %a)" D.pp d (list ~sep:sp (pp0_tm ctx0)) ms
  | Cons (c, ms) -> pf fmt "(%a %a)" C.pp c (list ~sep:sp (pp0_tm ctx0)) ms
  | Match (m, bnd, cls) ->
      let x, a, ctx = unbind_in ctx0 bnd in
      pf fmt "match %a [ %a ⇒ %a ] with %a" (pp0_tm ctx0) m V.pp x (pp0_tm ctx)
        a (pp0_cls ctx0) cls
  (* equality *)
  | Eq (m, n) -> pf fmt "%a ≡ %a" (pp0_tm ctx0) m (pp0_tm ctx0) n
  | Refl -> pf fmt "refl"
  | Rew (bnd, p, m) ->
      let xs, a, ctx = unmbind_in ctx0 bnd in
      pf fmt "rew [ %a, %a ⇒ %a ] %a in %a" V.pp xs.(0) V.pp xs.(1) (pp0_tm ctx)
        a (pp0_tm ctx0) p (pp0_tm ctx0) m
  (* monadic *)
  | IO a -> pf fmt "IO %a" (pp0_tm ctx0) a
  | Return m -> pf fmt "return %a" (pp0_tm ctx0) m
  | MLet (m, bnd) ->
      let x, n, ctx = unbind_in ctx0 bnd in
      pf fmt "let %a ⇐ %a in %a" V.pp x (pp0_tm ctx0) m (pp0_tm ctx) n
  (* session *)
  | Proto -> pf fmt "proto"
  | End -> pf fmt "end"
  | Act (R, rol, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "%a(%a : %a) ⇒ %a" pp_role rol V.pp x (pp0_tm ctx0) a (pp0_tm ctx)
        b
  | Act (N, rol, a, bnd) ->
      let x, b, ctx = unbind_in ctx0 bnd in
      pf fmt "%a{%a : %a} ⇒ %a" pp_role rol V.pp x (pp0_tm ctx0) a (pp0_tm ctx)
        b
  | Ch (Pos, m) -> pf fmt "ch‹%a›" (pp0_tm ctx0) m
  | Ch (Neg, m) -> pf fmt "hc‹%a›" (pp0_tm ctx0) m
  | Open prim -> pf fmt "open %a" pp_prim prim
  | Fork (a, bnd) ->
      let x, m, ctx = unbind_in ctx0 bnd in
      pf fmt "fork (%a : %a) in %a" V.pp x (pp0_tm ctx0) a (pp0_tm ctx0) m
  | Recv m -> pf fmt "recv %a" (pp0_tm ctx0) m
  | Send m -> pf fmt "send %a" (pp0_tm ctx0) m
  | Close m -> pf fmt "close %a" (pp0_tm ctx0) m

and pp0_cl ctx0 fmt = function
  | PPair (R, U, bnd) ->
      let xs, m, ctx = unmbind_in ctx0 bnd in
      pf fmt "(%a, %a) ⇒ %a" V.pp xs.(0) V.pp xs.(1) (pp0_tm ctx) m
  | PPair (N, U, bnd) ->
      let xs, m, ctx = unmbind_in ctx0 bnd in
      pf fmt "({%a}, %a) ⇒ %a" V.pp xs.(0) V.pp xs.(1) (pp0_tm ctx) m
  | PPair (R, L, bnd) ->
      let xs, m, ctx = unmbind_in ctx0 bnd in
      pf fmt "⟨%a, %a⟩ ⇒ %a" V.pp xs.(0) V.pp xs.(1) (pp0_tm ctx) m
  | PPair (N, L, bnd) ->
      let xs, m, ctx = unmbind_in ctx0 bnd in
      pf fmt "⟨{%a}, %a⟩ ⇒ %a" V.pp xs.(0) V.pp xs.(1) (pp0_tm ctx) m
  | PCons (c, bnd) ->
      let xs, m, ctx = unmbind_in ctx0 bnd in
      pf fmt "%a %a ⇒ %a" C.pp c (array ~sep:sp V.pp) xs (pp0_tm ctx) m

and pp0_cls ctx0 fmt cls = list ~sep:pipe (pp0_cl ctx0) fmt cls

let rec pp0_ptm ctx0 fmt = function
  | PBase b -> pf fmt ": %a" (pp0_tm ctx0) b
  | PBind (a, bnd) ->
      let x, ptm, ctx = unbind_in ctx0 bnd in
      pf fmt "(%a : %a) %a" V.pp x (pp0_tm ctx0) a (pp0_ptm ctx) ptm

let rec pp0_tele ctx0 fmt = function
  | TBase b -> pf fmt ": %a" (pp0_tm ctx0) b
  | TBind (R, a, bnd) ->
      let x, tl, ctx = unbind_in ctx0 bnd in
      pf fmt "(%a : %a) %a" V.pp x (pp0_tm ctx0) a (pp0_tele ctx) tl
  | TBind (N, a, bnd) ->
      let x, tl, ctx = unbind_in ctx0 bnd in
      pf fmt "{%a : %a} %a" V.pp x (pp0_tm ctx0) a (pp0_tele ctx) tl

let rec pp0_ptl ctx0 fmt = function
  | PBase tl -> (pp0_tele ctx0) fmt tl
  | PBind (a, bnd) ->
      let x, ptl, ctx = unbind_in ctx0 bnd in
      pf fmt "(%a : %a) %a" V.pp x (pp0_tm ctx0) a (pp0_ptl ctx) ptl

let rec pp0_dcons ctx0 fmt (DCons (c, ptl)) =
  pf fmt "%a of %a" C.pp c (pp0_ptl ctx0) ptl

let rec pp0_dcl ctx0 fmt = function
  | DTm (R, x, a, m) ->
      pf fmt "definition %a : %a = %a" V.pp x (pp0_tm ctx0) a (pp0_tm ctx0) m
  | DTm (N, x, a, m) ->
      pf fmt "theorem %a : %a = %a" V.pp x (pp0_tm ctx0) a (pp0_tm ctx0) m
  | DData (d, ptm, dconss) ->
      pf fmt "inductive %a %a = %a" D.pp d (pp0_ptm ctx0) ptm
        (list ~sep:pipe (pp0_dcons ctx0))
        dconss

let pp0_dcls ctx0 fmt dcls = pf fmt "%a" (list ~sep:break (pp0_dcl ctx0)) dcls
let pp_tm fmt m = pp0_tm (free_vars (lift_tm m)) fmt m
let pp_dcls fmt dcls = pp0_dcls (free_vars (lift_dcls dcls)) fmt dcls
