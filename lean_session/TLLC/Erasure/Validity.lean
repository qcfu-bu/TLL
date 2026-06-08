import TLLC.Erasure.Typing
import TLLC.Dynamic.Validity

/-!
# Erasure validity

Port of `coq_session/era_valid.v`: the bridges from the erasure relation back to the dynamic and
static typing judgments — `era_dyn_type` (here `Erased.toDyn`: the source term is dynamically typed),
`era_sta_type` (`Erased.toStatic`), `era_type_wf` (`Erased.wf`), and the validity theorem `era_valid`
(`Erased.validity`). All but `toDyn` reduce immediately to their dynamic counterparts.
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Erasure implies dynamic typing of the source term (Coq `era_dyn_type`). -/
lemma Erased.toDyn {Θ Γ Δ m m' A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) : Θ ⨾ Γ ⨾ Δ ⊢ m : A := by
  induction h with
  | var emp wf shs dhs => exact .var emp wf shs dhs
  | lamIm kΘ kΔ _ ih => exact .lamIm kΘ kΔ ih
  | lamEx kΘ kΔ _ ih => exact .lamEx kΘ kΔ ih
  | appIm _ tyn ihm => exact .appIm ihm tyn
  | appEx mrgΘ mrgΔ _ _ ihm ihn => exact .appEx mrgΘ mrgΔ ihm ihn
  | pairIm tyS tym _ ihn => exact .pairIm tyS tym ihn
  | pairEx mrgΘ mrgΔ tyS _ _ ihm ihn => exact .pairEx mrgΘ mrgΔ tyS ihm ihn
  | projIm mrgΘ mrgΔ tyC _ _ ihm ihn => exact .projIm mrgΘ mrgΔ tyC ihm ihn
  | projEx mrgΘ mrgΔ tyC _ _ ihm ihn => exact .projEx mrgΘ mrgΔ tyC ihm ihn
  | one emp wf k => exact .one emp wf k
  | tt emp wf k => exact .tt emp wf k
  | ff emp wf k => exact .ff emp wf k
  | ite mrgΘ mrgΔ tyA _ _ _ ihm ihn1 ihn2 => exact .ite mrgΘ mrgΔ tyA ihm ihn1 ihn2
  | pure _ ihm => exact .pure ihm
  | mlet mrgΘ mrgΔ tyB _ _ ihm ihn => exact .mlet mrgΘ mrgΔ tyB ihm ihn
  | chan js wf k tyA => exact .chan js wf k tyA
  | fork _ ihm => exact .fork ihm
  | recv hxor _ ihm => exact .recv hxor ihm
  | send hxor _ ihm => exact .send hxor ihm
  | close _ ihm => exact .close ihm
  | conv c _ tyB ihm => exact .conv c ihm tyB

/-- Erasure implies static typing of the source term (Coq `era_sta_type`). -/
lemma Erased.toStatic {Θ Γ Δ m m' A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) : Γ ⊢ m : A :=
  h.toDyn.toStatic

/-- Erasure implies dynamic well-formedness (Coq `era_type_wf`). -/
lemma Erased.wf {Θ Γ Δ m m' A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) : Wf Γ Δ :=
  h.toDyn.wf

/-- Validity: every erasure-typed term has a well-sorted type (Coq `era_valid`). -/
theorem Erased.validity {Θ Γ Δ m m' A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) : ∃ s, Γ ⊢ A : .srt s :=
  h.toDyn.validity

end TLLC.Erasure
