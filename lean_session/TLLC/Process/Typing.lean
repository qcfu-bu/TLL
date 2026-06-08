import TLLC.Dynamic.SR
import TLLC.Dynamic.ProcWf

/-!
# Process typing (self-dual single-channel encoding)

Port of `coq_session/proc_type.v` (process typing `Θ ⊢ p`, here `Typed Θ p`, notation `Θ ⊩ p`),
adapted to the Lean **self-dual single-channel** scope restriction (`Proc.res : bind Chan in Proc`,
one bound channel) rather than the Coq `Nu`'s two endpoints / the report's two-channel `vcd.P`.
See [[tllc-process-channel-encoding]].

## The self-dual design
A session channel has two dual endpoints. The Coq introduces both as two `:L` slots and routes each
to its thread with the ordinary merge. Here `res p` introduces ONE channel, tracked by a **trinary
slot** `Slot` recording how many of its two endpoints are still present:

* `Slot.both A` — both dual endpoints of protocol `A` (fresh from `res`),
* `Slot.one r A` — a single endpoint of polarity `r`,
* `Slot.none` — consumed/absent.

The process-context merge `PMerge` is **count-conserving**: its `split` rule divides a `both` (count 2)
into `one r` + `one (¬r)` (the two dual endpoints, 1 + 1). Crucially `split` PRODUCES a `both`, which
can never re-enter as a `one`, so a single endpoint cannot be split-merged against several duals (the
unsoundness of a naive `ch r`-shaped result). A single endpoint reaches exactly one leaf via the
ordinary `one`/`none` routing. Leaf (thread) typing converts a `both`-free process context to a
`Dynamic` channel context via `Realize` (`one r A ↦ ch r A :L`), so a `both` channel must be `split`
by a `par` before any thread can use it.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- A channel slot tracking how many of a channel's two dual endpoints are present. -/
inductive Slot where
  | none
  | one (r : Bool) (A : Term)
  | both (A : Term)

/-- Process channel context: a list of trinary channel slots. -/
abbrev PCtx := List Slot

/-- Count-conserving process-context merge with channel dual-`split`. -/
inductive PMerge : PCtx → PCtx → PCtx → Prop where
  | nil :
    PMerge [] [] []
  | none {Δ1 Δ2 Δ} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.none :: Δ1) (.none :: Δ2) (.none :: Δ)
  | oneL {Δ1 Δ2 Δ r A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.one r A :: Δ1) (.none :: Δ2) (.one r A :: Δ)
  | oneR {Δ1 Δ2 Δ r A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.none :: Δ1) (.one r A :: Δ2) (.one r A :: Δ)
  | bothL {Δ1 Δ2 Δ A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.both A :: Δ1) (.none :: Δ2) (.both A :: Δ)
  | bothR {Δ1 Δ2 Δ A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.none :: Δ1) (.both A :: Δ2) (.both A :: Δ)
  | split {Δ1 Δ2 Δ r A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.one r A :: Δ1) (.one (!r) A :: Δ2) (.both A :: Δ)

/-- Lower a `both`-free process context to a dynamic channel context for leaf (thread) typing. -/
inductive Realize : PCtx → Ctx → Prop where
  | nil :
    Realize [] []
  | none {Θ Θ'} :
    Realize Θ Θ' →
    Realize (.none :: Θ) (Option.none :: Θ')
  | one {Θ Θ' r A} :
    Realize Θ Θ' →
    Realize (.one r A :: Θ) (.ch r A :L Θ')

/-- Process typing (Coq `proc_type`, report `Θ ⊩ P`). -/
inductive Typed : PCtx → Proc → Prop where
  | exp {Θ Θ' m} :
    Realize Θ Θ' →
    Θ' ⨾ [] ⨾ [] ⊢ m : .M .unit →
    Typed Θ (.tm m)
  | par {Θ1 Θ2 Θ p q} :
    PMerge Θ1 Θ2 Θ →
    Typed Θ1 p →
    Typed Θ2 q →
    Typed Θ (.par p q)
  | scope {Θ p A} :
    [] ⊢ A : .proto →
    Typed (.both A :: Θ) p →
    Typed Θ (.res p)

@[inherit_doc] scoped notation:50 Θ:50 " ⊩ " p:51 => Typed Θ p

end TLLC.Process
