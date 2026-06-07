import TLLC.Dynamic.Typing
import TLLC.Static.Validity

/-!
# Dynamic validity

Port of `coq_session/dyn_valid.v`: the erasure of a dynamic typing to its static counterpart
(`dyn_sta_type`, here `Typed.toStatic`) and the validity theorem (`dyn_valid`, here
`Typed.validity`): every dynamically typed term has a well-sorted type.

Because `Wf` is standalone (see `Typing.lean`), `Typed.toStatic` is a plain structural induction on
the dynamic derivation, mapping each linear rule to the corresponding static rule (the merge/key
premises are simply dropped).
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- A dynamic typing erases to a static typing (Coq `dyn_sta_type`). -/
lemma Typed.toStatic {Θ Γ Δ m A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m : A) : Γ ⊢ m : A := by
  induction h with
  | var _ wf shs _ => exact .var wf.toStatic shs
  | lamIm _ _ _ ihm => exact .lam ihm
  | lamEx _ _ _ ihm => exact .lam ihm
  | appIm _ tyn ihm => exact .app ihm tyn
  | appEx _ _ _ _ ihm ihn => exact .app ihm ihn
  | pairIm tyS tym _ ihn => exact .pair tyS tym ihn
  | pairEx _ _ tyS _ _ ihm ihn => exact .pair tyS ihm ihn
  | projIm _ _ tyC _ _ ihm ihn => exact .proj tyC ihm ihn
  | projEx _ _ tyC _ _ ihm ihn => exact .proj tyC ihm ihn
  | one _ wf _ => exact .one wf.toStatic
  | tt _ wf _ => exact .tt wf.toStatic
  | ff _ wf _ => exact .ff wf.toStatic
  | ite _ _ tyA _ _ _ ihm ihn1 ihn2 => exact .ite tyA ihm ihn1 ihn2
  | pure _ ihm => exact .pure ihm
  | mlet _ _ tyB _ _ ihm ihn => exact .mlet tyB ihm ihn
  | chan _ wf _ tyA => exact .chan wf.toStatic tyA
  | fork _ ihm => exact .fork ihm
  | recv hxor _ ihm => exact .recv hxor ihm
  | send hxor _ ihm => exact .send hxor ihm
  | close _ ihm => exact .close ihm
  | conv hconv _ tyB ihm => exact .conv hconv ihm tyB

/-- Validity: every dynamically typed term has a well-sorted type (Coq `dyn_valid`). -/
theorem Typed.validity {Θ Γ Δ m A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m : A) : ∃ s, Γ ⊢ A : .srt s :=
  Static.Typed.validity h.toStatic

end TLLC.Dynamic
