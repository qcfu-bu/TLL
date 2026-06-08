import TLLC.Dynamic.Step
import TLLC.Process.Typing

/-!
# Process reduction (self-dual single-channel encoding)

Port of `coq_session/proc_step.v`: structural congruence `≡` (Coq `proc_congr0` + its `conv` closure)
and process reduction `⇛` (Coq `proc_step`), adapted to the self-dual single-channel encoding (see
[[tllc-process-channel-encoding]]).

Because each `res` binds ONE self-dual channel (both communicating threads reference `CVar 0`, with
polarity supplied by typing), the Coq's symmetric rule pairs collapse: `proc_step_com0`/`com0i`,
`com1`/`com1i`, and `end`/`endi` each become ONE rule, the `exch` congruence swaps just channels
`0 ↔ 1`, and the channel shifts are `±1` (Coq used `±2`).
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- The channel `CVar 0` as a term. -/
abbrev cvar (n : Nat) : Term := .chan (Chan.var_Chan n)

/-- Channel exchange substitution swapping the two innermost channels `0 ↔ 1` (Coq `exch`, here over
one channel per `res` instead of two endpoints). -/
def exch : Nat → Chan :=
  Chan.var_Chan 1 .: Chan.var_Chan 0 .: (fun x => Chan.var_Chan (x + 2))

/-- One-step structural congruence (Coq `proc_congr0`). -/
inductive Congr : Proc → Proc → Prop where
  | par_sym {p q} :
    Congr (.par p q) (.par q p)
  | assoc {o p q} :
    Congr (.par o (.par p q)) (.par (.par o p) q)
  | scope {p q} :
    Congr (.par (.res p) q) (.res (.par p (q⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)))
  | exch {p} :
    Congr (.res (.res p)) (.res (.res (p[exch; Term.var_Term])))
  | par {p p' q q'} :
    Congr p p' →
    Congr q q' →
    Congr (.par p q) (.par p' q')
  | nu {p p'} :
    Congr p p' →
    Congr (.res p) (.res p')
  | «end» {p} :
    Congr (.par p (.tm (.pure .one))) p

/-- Structural congruence (the conversion closure of `Congr`, Coq `≡`). -/
abbrev Cong : Proc → Proc → Prop := ARS.Conv Congr

@[inherit_doc] scoped infix:50 " ≡ₚ " => Cong

/-- Process reduction (Coq `proc_step`, `p ⇛ q`). -/
inductive Step : Proc → Proc → Prop where
  -- monadic
  | exp {m m'} :
    m ~>> m' →
    Step (.tm m) (.tm m')
  -- session
  | fork {A m m' n n'} :
    m' = m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ →
    n' = n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ →
    Step (.tm (.mlet (.fork A m) n))
      (.res (.par (.tm (n'[Chan.var_Chan; (cvar 0)..])) (.tm (m'[Chan.var_Chan; (cvar 0)..]))))
  | com {m n1 n2} :
    Step (.res (.par (.tm (.mlet (.app (.send (cvar 0) .im) m .im) n1)) (.tm (.mlet (.recv (cvar 0) .im) n2))))
      (.res (.par (.tm (.mlet (.pure (cvar 0)) n1)) (.tm (.mlet (.pure (.pair m (cvar 0) .im .L)) n2))))
  | comEx {v n1 n2} :
    Val v →
    Step (.res (.par (.tm (.mlet (.app (.send (cvar 0) .ex) v .ex) n1)) (.tm (.mlet (.recv (cvar 0) .ex) n2))))
      (.res (.par (.tm (.mlet (.pure (cvar 0)) n1)) (.tm (.mlet (.pure (.pair v (cvar 0) .ex .L)) n2))))
  | «end» {m m' n n'} :
    m' = m⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩ →
    n' = n⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩ →
    Step (.res (.par (.tm (.mlet (.close true (cvar 0)) m)) (.tm (.mlet (.close false (cvar 0)) n))))
      (.par (.tm (.mlet (.pure .one) m')) (.tm (.mlet (.pure .one) n')))
  -- congruence
  | par {o p q} :
    Step p q →
    Step (.par o p) (.par o q)
  | nu {p q} :
    Step p q →
    Step (.res p) (.res q)
  | congr {p p' q q'} :
    p ≡ₚ p' →
    Step p' q' →
    q' ≡ₚ q →
    Step p q

@[inherit_doc] scoped infix:50 " ⇛ " => Step

/-- Multi-step process reduction. -/
abbrev Red : Proc → Proc → Prop := ARS.Star Process.Step

@[inherit_doc] scoped infix:50 " ⇛* " => Red

end TLLC.Process
