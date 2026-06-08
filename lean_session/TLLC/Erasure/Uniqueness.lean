import TLLC.Erasure.Validity

/-!
# Erasure uniqueness

Port of `coq_session/era_uniq.v`: the erasure relation `era_type` determines a *function* on terms.
Concretely:

* `dyn_era_type` (here `Dynamic.Typed.toErased`): every dynamically-typed term has an erasure.
* `erase` (here `erase`): the structural erasure function `term → term`, replacing irrelevant
  subterms (implicit annotations/arguments/components, `LetIn`/`Ifte`/`Fork` motives, `IO` types)
  with `Box` (`.box`).
* `era_type_erase` (here `Erased.eq_erase`): the erasure relation agrees with `erase`.
* `era_unicity` (here `Erased.unicity`): the erased term is unique.
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Every dynamically-typed term has an erasure (Coq `dyn_era_type`). -/
lemma Dynamic.Typed.toErased {Θ Γ Δ m A} (ty : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    ∃ m', Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A := by
  induction ty with
  | var emp wf shs dhs => exact ⟨_, .var emp wf shs dhs⟩
  | lamIm kΘ kΔ _ ih => obtain ⟨m', erm⟩ := ih; exact ⟨_, .lamIm kΘ kΔ erm⟩
  | lamEx kΘ kΔ _ ih => obtain ⟨m', erm⟩ := ih; exact ⟨_, .lamEx kΘ kΔ erm⟩
  | appIm _ tyn ihm => obtain ⟨m', erm⟩ := ihm; exact ⟨_, .appIm erm tyn⟩
  | appEx mrgΘ mrgΔ _ _ ihm ihn =>
    obtain ⟨m', erm⟩ := ihm; obtain ⟨n', ern⟩ := ihn
    exact ⟨_, .appEx mrgΘ mrgΔ erm ern⟩
  | pairIm tyS tym _ ihn => obtain ⟨n', ern⟩ := ihn; exact ⟨_, .pairIm tyS tym ern⟩
  | pairEx mrgΘ mrgΔ tyS _ _ ihm ihn =>
    obtain ⟨m', erm⟩ := ihm; obtain ⟨n', ern⟩ := ihn
    exact ⟨_, .pairEx mrgΘ mrgΔ tyS erm ern⟩
  | projIm mrgΘ mrgΔ tyC _ _ ihm ihn =>
    obtain ⟨m', erm⟩ := ihm; obtain ⟨n', ern⟩ := ihn
    exact ⟨_, .projIm mrgΘ mrgΔ tyC erm ern⟩
  | projEx mrgΘ mrgΔ tyC _ _ ihm ihn =>
    obtain ⟨m', erm⟩ := ihm; obtain ⟨n', ern⟩ := ihn
    exact ⟨_, .projEx mrgΘ mrgΔ tyC erm ern⟩
  | one emp wf k => exact ⟨_, .one emp wf k⟩
  | tt emp wf k => exact ⟨_, .tt emp wf k⟩
  | ff emp wf k => exact ⟨_, .ff emp wf k⟩
  | ite mrgΘ mrgΔ tyA _ _ _ ihm ihn1 ihn2 =>
    obtain ⟨m', erm⟩ := ihm; obtain ⟨n1', ern1⟩ := ihn1; obtain ⟨n2', ern2⟩ := ihn2
    exact ⟨_, .ite mrgΘ mrgΔ tyA erm ern1 ern2⟩
  | pure _ ihm => obtain ⟨m', erm⟩ := ihm; exact ⟨_, .pure erm⟩
  | mlet mrgΘ mrgΔ tyB _ _ ihm ihn =>
    obtain ⟨m', erm⟩ := ihm; obtain ⟨n', ern⟩ := ihn
    exact ⟨_, .mlet mrgΘ mrgΔ tyB erm ern⟩
  | chan js wf k tyA => exact ⟨_, .chan js wf k tyA⟩
  | fork _ ihm => obtain ⟨m', erm⟩ := ihm; exact ⟨_, .fork erm⟩
  | recv hxor _ ihm => obtain ⟨m', erm⟩ := ihm; exact ⟨_, .recv hxor erm⟩
  | send hxor _ ihm => obtain ⟨m', erm⟩ := ihm; exact ⟨_, .send hxor erm⟩
  | close _ ihm => obtain ⟨m', erm⟩ := ihm; exact ⟨_, .close erm⟩
  | conv c _ tyB ihm => obtain ⟨m', erm⟩ := ihm; exact ⟨_, .conv c erm tyB⟩

/-- The structural erasure function (Coq `erase`). -/
def erase : Term → Term
  | .var_Term x => .var_Term x
  | .lam _ m i s => .lam .box (erase m) i s
  | .app m _ .im => .app (erase m) .box .im
  | .app m n .ex => .app (erase m) (erase n) .ex
  | .pair _ n .im s => .pair .box (erase n) .im s
  | .pair m n .ex s => .pair (erase m) (erase n) .ex s
  | .proj _ m n => .proj .box (erase m) (erase n)
  | .fix _ m => .fix .box (erase m)
  | .one => .one
  | .tt => .tt
  | .ff => .ff
  | .ite _ m n1 n2 => .ite .box (erase m) (erase n1) (erase n2)
  | .M _ => .box
  | .pure m => .pure (erase m)
  | .mlet m n => .mlet (erase m) (erase n)
  | .chan c => .chan c
  | .fork _ m => .fork .box (erase m)
  | .recv m i => .recv (erase m) i
  | .send m i => .send (erase m) i
  | .close b m => .close b (erase m)
  | _ => .box

/-- The erasure relation agrees with the `erase` function (Coq `era_type_erase`). -/
lemma Erased.eq_erase {Θ Γ Δ m m' A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) : m' = erase m := by
  induction h with
  | var => rfl
  | lamIm _ _ _ ih => simp only [erase, ih]
  | lamEx _ _ _ ih => simp only [erase, ih]
  | appIm _ _ ihm => simp only [erase, ihm]
  | appEx _ _ _ _ ihm ihn => simp only [erase, ihm, ihn]
  | pairIm _ _ _ ihn => simp only [erase, ihn]
  | pairEx _ _ _ _ _ ihm ihn => simp only [erase, ihm, ihn]
  | projIm _ _ _ _ _ ihm ihn => simp only [erase, ihm, ihn]
  | projEx _ _ _ _ _ ihm ihn => simp only [erase, ihm, ihn]
  | one => rfl
  | tt => rfl
  | ff => rfl
  | ite _ _ _ _ _ _ ihm ihn1 ihn2 => simp only [erase, ihm, ihn1, ihn2]
  | pure _ ihm => simp only [erase, ihm]
  | mlet _ _ _ _ _ ihm ihn => simp only [erase, ihm, ihn]
  | chan => rfl
  | fork _ ihm => simp only [erase, ihm]
  | recv _ _ ihm => simp only [erase, ihm]
  | send _ _ ihm => simp only [erase, ihm]
  | close _ ihm => simp only [erase, ihm]
  | conv _ _ _ ihm => exact ihm

/-- Uniqueness of erasure (Coq `era_unicity`). -/
lemma Erased.unicity {Θ Γ Δ m m1 m2 A}
    (h1 : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m1 : A) (h2 : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m2 : A) : m1 = m2 :=
  h1.eq_erase.trans h2.eq_erase.symm

end TLLC.Erasure
