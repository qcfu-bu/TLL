open Fmt
open Syntax0

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
  (* core *)
  | Type s -> pp_sort fmt s
  | Id id -> pf fmt "%s" id
  | Pi (R, U, a, Binder (id, b)) ->
    pf fmt "(∀ (%s : %a) → %a)" id pp_tm a pp_tm b
  | Pi (N, U, a, Binder (id, b)) ->
    pf fmt "(∀ {%s : %a} → %a)" id pp_tm a pp_tm b
  | Pi (R, L, a, Binder (id, b)) ->
    pf fmt "(∀ (%s : %a) ⊸ %a)" id pp_tm a pp_tm b
  | Pi (N, L, a, Binder (id, b)) ->
    pf fmt "(∀ {%s : %a} ⊸ %a)" id pp_tm a pp_tm b
  | Lam (R, U, Binder (id, m)) -> pf fmt "(fn %s ⇒ %a)" id pp_tm m
  | Lam (N, U, Binder (id, m)) -> pf fmt "(fn {%s} ⇒ %a)" id pp_tm m
  | Lam (R, L, Binder (id, m)) -> pf fmt "(ln %s ⇒ %a)" id pp_tm m
  | Lam (N, L, Binder (id, m)) -> pf fmt "(ln {%s} ⇒ %a)" id pp_tm m
  | App ms -> pf fmt "(%a)" (list ~sep:sp (parens pp_tm)) ms
  | Let (R, m, Binder (id, n)) -> pf fmt "let %s = %a in %a" id pp_tm m pp_tm n
  | Let (N, m, Binder (id, n)) ->
    pf fmt "let {%s} = %a in %a" id pp_tm m pp_tm n
  | Fix (x, Binder (r, m)) -> pf fmt "fix (%s := %s) ⇒ %a" x r pp_tm m
  (* data *)
  | Sigma (R, U, a, Binder (id, b)) ->
    pf fmt "(∃ (%s : %a) × %a)" id pp_tm a pp_tm b
  | Sigma (N, U, a, Binder (id, b)) ->
    pf fmt "(∃ {%s : %a} × %a)" id pp_tm a pp_tm b
  | Sigma (R, L, a, Binder (id, b)) ->
    pf fmt "(∃ (%s : %a) ⊗ %a)" id pp_tm a pp_tm b
  | Sigma (N, L, a, Binder (id, b)) ->
    pf fmt "(∃ {%s : %a} ⊗ %a)" id pp_tm a pp_tm b
  | Pair (R, U, m, n) -> pf fmt "(%a, %a)" pp_tm m pp_tm n
  | Pair (N, U, m, n) -> pf fmt "({%a}, %a)" pp_tm m pp_tm n
  | Pair (R, L, m, n) -> pf fmt "⟨%a, %a⟩" pp_tm m pp_tm n
  | Pair (N, L, m, n) -> pf fmt "⟨{%a}, %a⟩" pp_tm m pp_tm n
  | Match (m, Binder (id, a), cls) ->
    pf fmt "match %a {%s ⇒ %a} with %a" pp_tm m id pp_tm a pp_cls cls
  (* equality *)
  | Eq (m, n) -> pf fmt "%a ≡ %a" pp_tm m pp_tm n
  | Refl -> pf fmt "refl"
  | Rew (MBinder (ids, a), p, m) ->
    pf fmt "rew {%a ⇒ %a} %a in %a" (list ~sep:comma string) ids pp_tm a pp_tm p
      pp_tm m
  (* monadic *)
  | IO a -> pf fmt "IO %a" pp_tm a
  | Return m -> pf fmt "return %a" pp_tm m
  | MLet (m, Binder (id, n)) -> pf fmt "let %s ⇐ %a in %a" id pp_tm m pp_tm n
  (* session *)
  | Proto -> pf fmt "proto"
  | End -> pf fmt "end"
  | Act (R, rol, a, Binder (id, b)) ->
    pf fmt "%a(%s : %a) → %a" pp_role rol id pp_tm a pp_tm b
  | Act (N, rol, a, Binder (id, b)) ->
    pf fmt "%a{%s : %a} → %a" pp_role rol id pp_tm a pp_tm b
  | Ch (Pos, a) -> pf fmt "ch⟨%a⟩" pp_tm a
  | Ch (Neg, a) -> pf fmt "hc⟨%a⟩" pp_tm a
  | Open prim -> pf fmt "open %a" pp_prim prim
  | Fork (a, Binder (id, m)) -> pf fmt "fork (%s : %a) in %a" id pp_tm a pp_tm m
  | Recv m -> pf fmt "recv %a" pp_tm m
  | Send m -> pf fmt "send %a" pp_tm m
  | Close m -> pf fmt "close %a" pp_tm m

and pp_cl fmt = function
  | PPair (R, U, MBinder ([ id1; id2 ], m)) ->
    pf fmt "(%s, %s) ⇒ %a" id1 id2 pp_tm m
  | PPair (N, U, MBinder ([ id1; id2 ], m)) ->
    pf fmt "({%s}, %s) ⇒ %a" id1 id2 pp_tm m
  | PPair (R, L, MBinder ([ id1; id2 ], m)) ->
    pf fmt "⟨%s, %s⟩ ⇒ %a" id1 id2 pp_tm m
  | PPair (N, L, MBinder ([ id1; id2 ], m)) ->
    pf fmt "⟨{%s}, %s⟩ ⇒ %a" id1 id2 pp_tm m
  | PCons (id, MBinder (ids, m)) ->
    pf fmt "%s %a ⇒ %a" id (list ~sep:sp string) ids pp_tm m
  | _ -> failwith "pp_cl"

and pp_cls fmt cls = list ~sep:pipe pp_cl fmt cls

let rec pp_ptm fmt = function
  | PBase b -> pf fmt ": %a" pp_tm b
  | PBind (a, Binder (id, ptm)) -> pf fmt "(%s : %a) %a" id pp_tm a pp_ptm ptm

let rec pp_tele fmt = function
  | TBase b -> pf fmt "→ %a" pp_tm b
  | TBind (R, a, Binder (id, tl)) -> pf fmt "(%s : %a) %a" id pp_tm a pp_tele tl
  | TBind (N, a, Binder (id, tl)) -> pf fmt "{%s : %a} %a" id pp_tm a pp_tele tl

let rec pp_ptl fmt = function
  | PBase b -> pp_tele fmt b
  | PBind (a, Binder (id, ptl)) -> pf fmt "{%s : %a} %a" id pp_tm a pp_ptl ptl

let rec pp_args fmt = function
  | ABase (m, a) -> pf fmt ": %a = %a" pp_tm a pp_tm m
  | ABind (R, a, Binder (id, args)) ->
    pf fmt "(%s : %a) %a" id pp_tm a pp_args args
  | ABind (N, a, Binder (id, args)) ->
    pf fmt "{%s : %a} %a" id pp_tm a pp_args args

let pp_dcons fmt (DCons (id, ptl)) = pf fmt "%s of %a" id pp_ptl ptl

let pp_dcl fmt = function
  | DTm (R, id, args) -> pf fmt "program %s %a" id pp_args args
  | DTm (N, id, args) -> pf fmt "logical %s %a" id pp_args args
  | DData (id, ptm, dconss) ->
    pf fmt "inductive %s %a = %a" id pp_ptm ptm (list ~sep:pipe pp_dcons) dconss

let pp_dcls fmt dcls = pf fmt "%a" (list ~sep:break pp_dcl) dcls
