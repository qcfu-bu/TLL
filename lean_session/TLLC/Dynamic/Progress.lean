import TLLC.Dynamic.Inversion
import TLLC.Dynamic.Step

/-!
# Monadic canonical forms (global-progress seed)

Port of `coq_session/dyn_prog.v` (excluded from the Coq `_CoqProject` — unfinished scaffolding toward
global progress). `Typed.monad_canonical` (Coq `dyn_monad_canonical`) is the canonical-forms lemma
for closed values of monadic type: a value `v` of a type convertible to `IO A` is either a returned
value `.pure u` (with `u` a value) or a suspended `Thunk` (a bind/fork/recv/send-application/close).

This is one of the two seeds (with `EvalCtx.lean`) for the Lean-only deadlock-freedom contribution.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static
open TLLC.Static.Tactic

/-- Canonical forms for closed values of monadic type (Coq `dyn_monad_canonical`). -/
lemma Typed.monad_canonical {Θ A v T} (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : T)
    (vl : Val v) (eq : .M A ≃ T) :
    (∃ u, Val u ∧ v = .pure u) ∨ Thunk v := by
  generalize eΓ : ([] : Static.Ctx) = Γ at ty
  generalize eΔ : ([] : Ctx) = Δ at ty
  induction ty generalizing A with
  | var _ _ _ dhs => subst eΔ; cases dhs
  | lamIm => false_conv
  | lamEx => false_conv
  | pairIm => false_conv
  | pairEx => false_conv
  | one => false_conv
  | tt => false_conv
  | ff => false_conv
  | chan => false_conv
  | send => false_conv
  | pure _ _ => cases vl with
    | pure vu => exact .inl ⟨_, vu, rfl⟩
    | thunk th => cases th
  | mlet _ _ _ _ _ _ _ => cases vl with | thunk th => exact .inr th
  | fork _ _ => cases vl with | thunk th => exact .inr th
  | recv _ _ _ => cases vl with | thunk th => exact .inr th
  | close _ _ => cases vl with | thunk th => exact .inr th
  | appIm _ _ _ => cases vl with | thunk th => exact .inr th
  | appEx _ _ _ _ _ _ => cases vl with | thunk th => exact .inr th
  | projIm _ _ _ _ _ _ _ => cases vl with | thunk th => cases th
  | projEx _ _ _ _ _ _ _ => cases vl with | thunk th => cases th
  | ite _ _ _ _ _ _ _ _ _ => cases vl with | thunk th => cases th
  | conv eq1 _ _ ihm => exact ihm vl (ARS.conv_trans eq (ARS.conv_sym eq1)) eΓ eΔ

end TLLC.Dynamic
