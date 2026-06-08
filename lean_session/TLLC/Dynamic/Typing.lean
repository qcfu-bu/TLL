import TLLC.Dynamic.Context
import TLLC.Static.Typing

/-!
# Dynamic typing

Port of `coq_session/dyn_type.v`: the linear typing judgment `dyn_type` over three contexts
(`Θ ; Γ ; Δ ⊢ m : A`, here `Typed Θ Γ Δ m A`) and the dynamic well-formedness `dyn_wf`
(here `Wf`). `Θ`/`Δ` are dynamic (linear) contexts and `Γ` is the static context.

A structural note: although Coq declares `dyn_type` and `dyn_wf` in one `with` block, `dyn_wf`'s
premises are *static* typings (`Γ ⊢ A : Sort s`), so it never mentions `dyn_type`. Hence the two are
not genuinely mutual; here `Wf` is a standalone inductive defined first, then `Typed`.

As in the static layer, Coq's implicit/explicit constructor pairs merge via the `Rlv`/`Bool` tag
*only when identical modulo the tag*. The CBV/linearity asymmetries keep several split (suffixed
`Im`/`Ex`): `lamIm`/`lamEx` (the explicit binder is linearly available, the implicit one is null),
`appIm`/`appEx` (the implicit argument is typed statically, the explicit one with a context split),
`pairIm`/`pairEx`, `projIm`/`projEx` (`LetIn0`/`LetIn1`). The merged ones are `ite`, `mlet` (`Bind`),
`recv`/`send`, `close` (`Close`/`Wait`).

Coq → Lean lemma name map: `dyn_wf_merge`→`Wf.merge`, `dyn_type_wf`→`Typed.wf`,
`dyn_sta_wf`→`Wf.toStatic`, `dyn_wf_inv`→`Wf.split`.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-! ## Dynamic well-formedness (Coq `dyn_wf`). -/

/-- Dynamic well-formedness of a static/linear context pair (Coq `dyn_wf`). -/
inductive Wf : Static.Ctx → Ctx → Prop where
  | nil :
    Wf [] []
  | cons {Γ Δ A s} :
    Wf Γ Δ →
    Γ ⊢ A : .srt s →
    Wf (A :: Γ) (A :⟨s⟩ Δ)
  | null {Γ Δ A s} :
    Wf Γ Δ →
    Γ ⊢ A : .srt s →
    Wf (A :: Γ) (none :: Δ)

/-! ## Dynamic typing (Coq `dyn_type`). -/

/-- Linear typing judgment over `Θ` (process), `Γ` (static), `Δ` (linear) (Coq `dyn_type`). -/
inductive Typed : Ctx → Static.Ctx → Ctx → Term → Term → Prop where
  -- core
  | var {Θ Γ Δ x s A} :
    Empty Θ →
    Wf Γ Δ →
    Static.Has Γ x A →
    Has Δ x s A →
    Typed Θ Γ Δ (.var_Term x) A
  | lamIm {Θ Γ Δ A B m s} :
    Θ ▷ s →
    Δ ▷ s →
    Typed Θ (A :: Γ) (none :: Δ) m B →
    Typed Θ Γ Δ (.lam A m .im s) (.pi A B .im s)
  | lamEx {Θ Γ Δ A B m s t} :
    Θ ▷ s →
    Δ ▷ s →
    Typed Θ (A :: Γ) (A :⟨t⟩ Δ) m B →
    Typed Θ Γ Δ (.lam A m .ex s) (.pi A B .ex s)
  | appIm {Θ Γ Δ A B m n s} :
    Typed Θ Γ Δ m (.pi A B .im s) →
    Γ ⊢ n : A →
    Typed Θ Γ Δ (.app m n .im) (B[Chan.var_Chan; n..])
  | appEx {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    Typed Θ1 Γ Δ1 m (.pi A B .ex s) →
    Typed Θ2 Γ Δ2 n A →
    Typed Θ Γ Δ (.app m n .ex) (B[Chan.var_Chan; n..])
  | pairIm {Θ Γ Δ A B m n t} :
    Γ ⊢ .sig A B .im t : .srt t →
    Γ ⊢ m : A →
    Typed Θ Γ Δ n (B[Chan.var_Chan; m..]) →
    Typed Θ Γ Δ (.pair m n .im t) (.sig A B .im t)
  | pairEx {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    Γ ⊢ .sig A B .ex t : .srt t →
    Typed Θ1 Γ Δ1 m A →
    Typed Θ2 Γ Δ2 n (B[Chan.var_Chan; m..]) →
    Typed Θ Γ Δ (.pair m n .ex t) (.sig A B .ex t)
  | projIm {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    .sig A B .im t :: Γ ⊢ C : .srt s →
    Typed Θ1 Γ Δ1 m (.sig A B .im t) →
    Typed Θ2 (B :: A :: Γ) (B :⟨r⟩ none :: Δ2) n
      (C[Chan.var_Chan; (Term.pair (.var_Term 1) (.var_Term 0) .im t) .: funcomp Term.var_Term (· + 2)]) →
    Typed Θ Γ Δ (.proj C m n) (C[Chan.var_Chan; m..])
  | projEx {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    .sig A B .ex t :: Γ ⊢ C : .srt s →
    Typed Θ1 Γ Δ1 m (.sig A B .ex t) →
    Typed Θ2 (B :: A :: Γ) (B :⟨r2⟩ A :⟨r1⟩ Δ2) n
      (C[Chan.var_Chan; (Term.pair (.var_Term 1) (.var_Term 0) .ex t) .: funcomp Term.var_Term (· + 2)]) →
    Typed Θ Γ Δ (.proj C m n) (C[Chan.var_Chan; m..])
  -- data
  | one {Θ Γ Δ} :
    Empty Θ →
    Wf Γ Δ →
    Δ ▷ Srt.U →
    Typed Θ Γ Δ .one .unit
  | tt {Θ Γ Δ} :
    Empty Θ →
    Wf Γ Δ →
    Δ ▷ Srt.U →
    Typed Θ Γ Δ .tt .bool
  | ff {Θ Γ Δ} :
    Empty Θ →
    Wf Γ Δ →
    Δ ▷ Srt.U →
    Typed Θ Γ Δ .ff .bool
  | ite {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    .bool :: Γ ⊢ A : .srt s →
    Typed Θ1 Γ Δ1 m .bool →
    Typed Θ2 Γ Δ2 n1 (A[Chan.var_Chan; Term.tt..]) →
    Typed Θ2 Γ Δ2 n2 (A[Chan.var_Chan; Term.ff..]) →
    Typed Θ Γ Δ (.ite A m n1 n2) (A[Chan.var_Chan; m..])
  -- monadic
  | pure {Θ Γ Δ m A} :
    Typed Θ Γ Δ m A →
    Typed Θ Γ Δ (.pure m) (.M A)
  | mlet {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    Γ ⊢ B : .srt t →
    Typed Θ1 Γ Δ1 m (.M A) →
    Typed Θ2 (A :: Γ) (A :⟨s⟩ Δ2) n (.M (B⟨(id : Nat → Nat); ↑⟩)) →
    Typed Θ Γ Δ (.mlet m n) (.M B)
  -- session
  | chan {Θ Γ Δ r x A} :
    Just Θ x (.ch r A) →
    Wf Γ Δ →
    Δ ▷ Srt.U →
    [] ⊢ A : .proto →
    Typed Θ Γ Δ (.chan (Chan.var_Chan x)) (.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩))
  | fork {Θ Γ Δ A m} :
    Typed Θ (.ch true A :: Γ) (.ch true A :L Δ) m (.M .unit) →
    Typed Θ Γ Δ (.fork A m) (.M (.ch false A))
  | recv {Θ Γ Δ r1 r2 A B m i} :
    xor r1 r2 = false →
    Typed Θ Γ Δ m (.ch r1 (.act r2 A B i)) →
    Typed Θ Γ Δ (.recv m i) (.M (.sig A (.ch r1 B) i .L))
  | send {Θ Γ Δ r1 r2 A B m i} :
    xor r1 r2 = true →
    Typed Θ Γ Δ m (.ch r1 (.act r2 A B i)) →
    Typed Θ Γ Δ (.send m i) (.pi A (.M (.ch r1 B)) i .L)
  | close {Θ Γ Δ b m} :
    Typed Θ Γ Δ m (.ch b .stop) →
    Typed Θ Γ Δ (.close b m) (.M .unit)
  -- conversion
  | conv {Θ Γ Δ A B m s} :
    A ≃ B →
    Typed Θ Γ Δ m A →
    Γ ⊢ B : .srt s →
    Typed Θ Γ Δ m B

@[inherit_doc]
scoped notation:50 Θ:50 " ⨾ " Γ:51 " ⨾ " Δ:51 " ⊢ " m:51 " : " A:51 => Typed Θ Γ Δ m A

/-! ## Basic metatheory -/

/-- Merging two well-formed linear contexts is well-formed (Coq `dyn_wf_merge`). -/
lemma Wf.merge {Γ Δ1} (wf1 : Wf Γ Δ1) : ∀ {Δ Δ2}, Merge Δ1 Δ2 Δ → Wf Γ Δ2 → Wf Γ Δ := by
  induction wf1 with
  | nil => intro _ _ mrg wf2; cases mrg; exact wf2
  | cons _ tyA ih => intro _ _ mrg wf2; cases mrg with
    | left _ mrg' => cases wf2 with | cons wf2' _ => exact .cons (ih mrg' wf2') tyA
    | right1 _ mrg' => cases wf2 with | null wf2' _ => exact .cons (ih mrg' wf2') tyA
  | null _ tyA ih => intro _ _ mrg wf2; cases mrg with
    | right2 _ mrg' => cases wf2 with | cons wf2' tyA2 => exact .cons (ih mrg' wf2') tyA2
    | null mrg' => cases wf2 with | null wf2' _ => exact .null (ih mrg' wf2') tyA

/-- Dynamic typing implies dynamic well-formedness (Coq `dyn_type_wf`). -/
lemma Typed.wf {Θ Γ Δ m A} (h : Typed Θ Γ Δ m A) : Wf Γ Δ := by
  induction h with
  | var _ wf _ _ => exact wf
  | lamIm _ _ _ ih => cases ih with | null w _ => exact w
  | lamEx _ _ _ ih => cases ih with | cons w _ => exact w
  | appIm _ _ ihm => exact ihm
  | appEx _ mrgΔ _ _ ihm ihn => exact ihm.merge mrgΔ ihn
  | pairIm _ _ _ ihn => exact ihn
  | pairEx _ mrgΔ _ _ _ ihm ihn => exact ihm.merge mrgΔ ihn
  | projIm _ mrgΔ _ _ _ ihm ihn =>
    cases ihn with | cons w1 _ => cases w1 with | null w2 _ => exact ihm.merge mrgΔ w2
  | projEx _ mrgΔ _ _ _ ihm ihn =>
    cases ihn with | cons w1 _ => cases w1 with | cons w2 _ => exact ihm.merge mrgΔ w2
  | one _ wf _ => exact wf
  | tt _ wf _ => exact wf
  | ff _ wf _ => exact wf
  | ite _ mrgΔ _ _ _ _ ihm ihn1 _ => exact ihm.merge mrgΔ ihn1
  | pure _ ihm => exact ihm
  | mlet _ mrgΔ _ _ _ ihm ihn => cases ihn with | cons w _ => exact ihm.merge mrgΔ w
  | chan _ wf _ _ => exact wf
  | fork _ ihm => cases ihm with | cons w _ => exact w
  | recv _ _ ihm => exact ihm
  | send _ _ ihm => exact ihm
  | close _ ihm => exact ihm
  | conv _ _ _ ihm => exact ihm

/-- Dynamic well-formedness implies static well-formedness (Coq `dyn_sta_wf`). -/
lemma Wf.toStatic {Γ Δ} (wf : Wf Γ Δ) : Static.Wf Γ := by
  induction wf with
  | nil => exact .nil
  | cons _ tyA ih => exact .cons ih tyA
  | null _ tyA ih => exact .cons ih tyA

/-- A merge splits a well-formed linear context into well-formed components (Coq `dyn_wf_inv`). -/
lemma Wf.split {Γ Δ} (wf : Wf Γ Δ) : ∀ {Δ1 Δ2}, Merge Δ1 Δ2 Δ → Wf Γ Δ1 ∧ Wf Γ Δ2 := by
  induction wf with
  | nil => intro _ _ mrg; cases mrg; exact ⟨.nil, .nil⟩
  | cons _ tyA ih => intro _ _ mrg; cases mrg with
    | left _ mrg' => obtain ⟨w1, w2⟩ := ih mrg'; exact ⟨.cons w1 tyA, .cons w2 tyA⟩
    | right1 _ mrg' => obtain ⟨w1, w2⟩ := ih mrg'; exact ⟨.cons w1 tyA, .null w2 tyA⟩
    | right2 _ mrg' => obtain ⟨w1, w2⟩ := ih mrg'; exact ⟨.null w1 tyA, .cons w2 tyA⟩
  | null _ tyA ih => intro _ _ mrg; cases mrg with
    | null mrg' => obtain ⟨w1, w2⟩ := ih mrg'; exact ⟨.null w1 tyA, .null w2 tyA⟩

end TLLC.Dynamic
