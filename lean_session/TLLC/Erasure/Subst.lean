import TLLC.Erasure.Rename
import TLLC.Dynamic.Subst

/-!
# Erasure substitution

Port of `coq_session/era_subst.v`: the erasure substitution-agreement relation `AgreeSubst`
(Coq `era_agree_subst`, notation `Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2`), which threads a process
context `Θ1`, a static context pair `(Γ1, Γ2)`, a dynamic (linear) context pair `(Δ1, Δ2)` and a
PAIR of substitutions `σ1` (acting on the source term/type) and `σ2` (acting on the erased term);
its structural lemmas; the substitution-preservation metatheorem `Erased.substitution`
(Coq `era_substitution`); and the corollaries `Erased.subst0`/`subst1`/`esubst0`/`esubst1` and
`Erased.ctx_conv0`/`ctx_conv1`.

This file mirrors `Dynamic/Subst.lean` (`coq_session/dyn_subst.v`) almost line-for-line, threading a
SECOND substitution `σ2` and a second (erased) term `m'`/`n'` alongside the source. The projections
`AgreeSubst.toStatic`/`toDyn` recover the static (Coq `era_sta_agree_subst`) and dynamic
(Coq `era_dyn_agree_subst`) agreements, both acting on `σ1`. The well-formedness preservation reuses
the dynamic `Wf.substitution` via `toDyn`.

Notation: the Coq `;`-token judgment notation poisons the tactic `;`, so we use `⨾`:
`Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δ2 := AgreeSubst Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2`.
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Erasure substitution agreement (Coq `era_agree_subst`), threading a pair `(σ1, σ2)`. -/
inductive AgreeSubst :
    Ctx → Static.Ctx → Ctx → (Nat → Term) → (Nat → Term) → Static.Ctx → Ctx → Prop where
  | nil {Θ1} :
    Empty Θ1 →
    AgreeSubst Θ1 ([] : Static.Ctx) ([] : Ctx) Term.var_Term Term.var_Term
      ([] : Static.Ctx) ([] : Ctx)
  | ty {Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s} :
    AgreeSubst Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 →
    Γ2 ⊢ A : .srt s →
    AgreeSubst Θ1 (A[Chan.var_Chan; σ1] :: Γ1) (A[Chan.var_Chan; σ1] :⟨s⟩ Δ1)
      (up_Term_Term σ1) (up_Term_Term σ2) (A :: Γ2) (A :⟨s⟩ Δ2)
  | n {Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s} :
    AgreeSubst Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 →
    Γ2 ⊢ A : .srt s →
    AgreeSubst Θ1 (A[Chan.var_Chan; σ1] :: Γ1) (none :: Δ1)
      (up_Term_Term σ1) (up_Term_Term σ2) (A :: Γ2) (none :: Δ2)
  | wk0 {Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A} :
    AgreeSubst Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 →
    Γ1 ⊢ n : A[Chan.var_Chan; σ1] →
    AgreeSubst Θ1 Γ1 Δ1 (n .: σ1) (n' .: σ2) (A :: Γ2) (none :: Δ2)
  | wk1 {Θa Θb Θ1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s} :
    Θb ▷ s →
    Δb ▷ s →
    Merge Θa Θb Θ1 →
    Merge Δa Δb Δ1 →
    AgreeSubst Θa Γ1 Δa σ1 σ2 Γ2 Δ2 →
    Erased Θb Γ1 Δb n n' (A[Chan.var_Chan; σ1]) →
    AgreeSubst Θ1 Γ1 Δ1 (n .: σ1) (n' .: σ2) (A :: Γ2) (A :⟨s⟩ Δ2)
  | conv0 {Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s} :
    A ≃ B →
    Γ1 ⊢ (B⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; σ1] : .srt s →
    Γ2 ⊢ B : .srt s →
    AgreeSubst Θ1 Γ1 Δ1 σ1 σ2 (A :: Γ2) (none :: Δ2) →
    AgreeSubst Θ1 Γ1 Δ1 σ1 σ2 (B :: Γ2) (none :: Δ2)
  | conv1 {Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s} :
    A ≃ B →
    Γ1 ⊢ (B⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; σ1] : .srt s →
    Γ2 ⊢ B : .srt s →
    AgreeSubst Θ1 Γ1 Δ1 σ1 σ2 (A :: Γ2) (A :⟨s⟩ Δ2) →
    AgreeSubst Θ1 Γ1 Δ1 σ1 σ2 (B :: Γ2) (B :⟨s⟩ Δ2)

@[inherit_doc]
scoped notation:50 Θ1:50 " ⨾ " Γ1:51 " ⨾ " Δ1:51 " ⊢ " σ1:51 " ~ " σ2:51 " ⊣ " Γ2:51 " ⨾ " Δ2:51 =>
  AgreeSubst Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2

/-- Substitution agreement transports keys (Coq `era_agree_subst_key`). -/
lemma AgreeSubst.key {Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2 s}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δ2) (k : Δ2 ▷ s) : Θ1 ▷ s ∧ Δ1 ▷ s := by
  induction agr generalizing s with
  | nil emp => exact ⟨emp.key, .nil⟩
  | @ty Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s' agr tyA ih =>
    cases k with
    | U _ k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨k1, .U _ k2⟩
    | L _ k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨Key.impure, .L _ k2⟩
  | @n Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s' agr tyA ih =>
    cases k with
    | null k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨k1, .null k2⟩
  | @wk0 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr tyn ih =>
    cases k with
    | null k' => exact ih k'
  | @wk1 Θa Θb Θ1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s' kb kΔb mrgΘ mrgΔ agr tyn ih =>
    cases k with
    | U _ k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨mrgΘ.key_image k1 kb, mrgΔ.key_image k2 kΔb⟩
    | L _ k' => exact ⟨Key.impure, Key.impure⟩
  | @conv0 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s' eq tyB1 tyB2 agr ih =>
    cases k with
    | null k' => exact ih (.null k')
  | @conv1 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s' eq tyB1 tyB2 agr ih =>
    cases k with
    | U _ k' => exact ih (.U _ k')
    | L _ k' => exact ih (.L _ k')

/-- The static projection of an erasure substitution agreement (Coq `era_sta_agree_subst`). -/
lemma AgreeSubst.toStatic {Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δ2) : Γ1 ⊢ σ1 ⊣ Γ2 := by
  induction agr with
  | nil _ => exact .nil
  | ty _ tyA ih => exact .ty ih tyA
  | n _ tyA ih => exact .ty ih tyA
  | wk0 _ tyn ih => exact .wk1 ih tyn
  | wk1 _ _ _ _ _ ern ih => exact .wk1 ih ern.toStatic
  | conv0 eq tyB1 tyB2 _ ih => exact .conv eq tyB1 tyB2 ih
  | conv1 eq tyB1 tyB2 _ ih => exact .conv eq tyB1 tyB2 ih

/-- The dynamic projection of an erasure substitution agreement (Coq `era_dyn_agree_subst`). -/
lemma AgreeSubst.toDyn {Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δ2) : Dynamic.AgreeSubst Θ1 Γ1 Δ1 σ1 Γ2 Δ2 := by
  induction agr with
  | nil emp => exact .nil emp
  | ty _ tyA ih => exact .ty ih tyA
  | n _ tyA ih => exact .n ih tyA
  | wk0 _ tyn ih => exact .wk0 ih tyn
  | wk1 kb kΔb mrgΘ mrgΔ _ ern ih => exact .wk1 kb kΔb mrgΘ mrgΔ ih ern.toDyn
  | conv0 eq tyB1 tyB2 _ ih => exact .conv0 eq tyB1 tyB2 ih
  | conv1 eq tyB1 tyB2 _ ih => exact .conv1 eq tyB1 tyB2 ih

/-- The identity substitution agrees a well-formed pair with itself (Coq `era_agree_subst_refl`). -/
lemma AgreeSubst.refl :
    ∀ {Θ Γ Δ}, Empty Θ → Wf Γ Δ → Θ ⨾ Γ ⨾ Δ ⊢ Term.var_Term ~ Term.var_Term ⊣ Γ ⨾ Δ
  | _, _, _, emp, .nil => .nil emp
  | _, _, _, emp, @Wf.cons Γ Δ A s wf tyA => by
    have ih := AgreeSubst.refl emp wf
    have h := AgreeSubst.ty ih tyA
    rw [show A[Chan.var_Chan; Term.var_Term] = A from by asimp,
        show up_Term_Term Term.var_Term = Term.var_Term from by asimp] at h
    exact h
  | _, _, _, emp, @Wf.null Γ Δ A s wf tyA => by
    have ih := AgreeSubst.refl emp wf
    have h := AgreeSubst.n ih tyA
    rw [show A[Chan.var_Chan; Term.var_Term] = A from by asimp,
        show up_Term_Term Term.var_Term = Term.var_Term from by asimp] at h
    exact h

/-- An erasure typing yields an empty splitter (Coq `era_type_empty`). -/
lemma Erased.empty {Θ1 Γ Δ m m' A} (erm : Θ1 ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) :
    ∃ Θ, Empty Θ ∧ Merge Θ Θ1 Θ1 :=
  erm.toDyn.empty

/-- Substitution agreement transports linear lookups (Coq `era_agree_subst_has`). -/
lemma AgreeSubst.has {Θ1 Θ2 Θ Γ1 Γ2 σ1 σ2 Δ1 Δ2 x s A}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δ2) (emp2 : Empty Θ2) (mrg : Merge Θ1 Θ2 Θ)
    (wf : Wf Γ1 Δ1) (hs : Has Δ2 x s A) :
    Θ ⨾ Γ1 ⨾ Δ1 ⊢ σ1 x ~ σ2 x : A[Chan.var_Chan; σ1] := by
  induction agr generalizing x Θ2 Θ s A with
  | nil emp1 => cases hs
  | @ty Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr tyA ih =>
    cases wf with
    | @cons _ _ _ _ wf' tyA' =>
      cases hs with
      | @zero _ A' _ k =>
        obtain ⟨k1, k2⟩ := agr.key k
        have e := mrg.pureL k1; subst e
        rw [show (A⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; up_Term_Term σ1]
              = (A[Chan.var_Chan; σ1])⟨(id : Nat → Nat); ↑⟩ from by asimp]
        exact .var emp2 (.cons wf' tyA') Static.Has.zero (Has.zero k2)
      | @succ _ A' _ y _ hs =>
        rw [show (A'⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; up_Term_Term σ1]
              = (A'[Chan.var_Chan; σ1])⟨(id : Nat → Nat); ↑⟩ from by asimp,
            show (up_Term_Term σ1) (y + 1) = (σ1 y)⟨(id : Nat → Nat); ↑⟩ from by asimp,
            show (up_Term_Term σ2) (y + 1) = (σ2 y)⟨(id : Nat → Nat); ↑⟩ from by asimp]
        exact Erased.eweakenU rfl rfl rfl tyA' (ih emp2 mrg wf' hs)
  | @n Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr tyA ih =>
    cases wf with
    | @null _ _ _ _ wf' tyA' =>
      cases hs with
      | @null _ A' y _ hs =>
        rw [show (A'⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; up_Term_Term σ1]
              = (A'[Chan.var_Chan; σ1])⟨(id : Nat → Nat); ↑⟩ from by asimp,
            show (up_Term_Term σ1) (y + 1) = (σ1 y)⟨(id : Nat → Nat); ↑⟩ from by asimp,
            show (up_Term_Term σ2) (y + 1) = (σ2 y)⟨(id : Nat → Nat); ↑⟩ from by asimp]
        exact Erased.eweakenN rfl rfl rfl tyA' (ih emp2 mrg wf' hs)
  | @wk0 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr tyn ih =>
    cases hs with
    | @null _ A' _ _ hs =>
      asimp
      exact ih emp2 mrg wf hs
  | @wk1 Θa Θb Θ1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s kb kΔb mrgΘ mrgΔ agr ern ih =>
    cases hs with
    | @zero _ A' _ k =>
      asimp
      obtain ⟨k3, k4⟩ := agr.key k
      have e := mrgΘ.pureL k3; subst e
      have e := mrgΔ.pureL k4; subst e
      have e := mrg.emptyR emp2; subst e
      exact ern
    | @succ _ A' _ _ _ hs =>
      asimp
      have e := mrgΘ.pureR kb; subst e
      have e := mrgΔ.pureR kΔb; subst e
      exact ih emp2 mrg wf hs
  | @conv0 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih =>
    cases hs with
    | @null _ A' _ _ hs =>
      exact ih emp2 mrg wf (.null hs)
  | @conv1 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih =>
    cases hs with
    | @zero _ A' _ k =>
      apply Erased.conv
      · exact Static.conv_subst σ1 (Static.conv_ren Nat.succ eq)
      · exact ih emp2 mrg wf (.zero k)
      · exact tyB1
    | @succ _ A' _ _ _ hs =>
      exact ih emp2 mrg wf (.succ hs)

/-- Substitution agreement is compatible with merge (Coq `era_agree_subst_merge`). -/
lemma AgreeSubst.merge {Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δ2) :
    ∀ {Δa Δb}, Merge Δa Δb Δ2 →
    ∃ Θa' Θb' Δa' Δb',
      Merge Θa' Θb' Θ1 ∧
      Merge Δa' Δb' Δ1 ∧
      (Θa' ⨾ Γ1 ⨾ Δa' ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δa) ∧
      (Θb' ⨾ Γ1 ⨾ Δb' ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δb) := by
  induction agr with
  | @nil Θ1 emp =>
    intro _ _ mrg; cases mrg
    exact ⟨Θ1, Θ1, [], [], emp.merge_self, .nil, .nil emp, .nil emp⟩
  | @ty Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr tyA ih =>
    intro _ _ mrg
    cases mrg with
    | left _ mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, A[Chan.var_Chan; σ1] :U Δa, A[Chan.var_Chan; σ1] :U Δb,
        mrg1, .left _ mrg2, .ty agra tyA, .ty agrb tyA⟩
    | right1 _ mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, A[Chan.var_Chan; σ1] :L Δa, none :: Δb,
        mrg1, .right1 _ mrg2, .ty agra tyA, .n agrb tyA⟩
    | right2 _ mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, none :: Δa, A[Chan.var_Chan; σ1] :L Δb,
        mrg1, .right2 _ mrg2, .n agra tyA, .ty agrb tyA⟩
  | @n Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr tyA ih =>
    intro _ _ mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, none :: Δa, none :: Δb, mrg1, .null mrg2, .n agra tyA, .n agrb tyA⟩
  | @wk0 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr tyn ih =>
    intro _ _ mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, .wk0 agra tyn, .wk0 agrb tyn⟩
  | @wk1 Θa Θb Θ1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s kb kΔb mrgΘ mrgΔ agr ern ih =>
    intro Δa' Δb' mrg'
    cases mrg' with
    | left _ mrg'' =>
      obtain ⟨Θa', Θb', Δa'', Δb'', mrg1', mrg2', agra, agrb⟩ := ih mrg''
      obtain ⟨Θc, mrg1a, mrg1b⟩ := mrgΘ.splitL mrg1'
      obtain ⟨Δc, mrg2a, mrg2b⟩ := mrgΔ.splitL mrg2'
      refine ⟨Θc, Θb', Δc, Δb'', mrg1b, mrg2b, ?_, ?_⟩
      · exact .wk1 kb kΔb mrg1a mrg2a agra ern
      · obtain ⟨Θd, mrg3, _⟩ := mrgΘ.splitR mrg1'
        obtain ⟨Δd, mrg4, _⟩ := mrgΔ.splitR mrg2'
        have e := mrg3.pureR kb; subst e
        have e := mrg4.pureR kΔb; subst e
        exact .wk1 kb kΔb mrg3 mrg4 agrb ern
    | right1 _ mrg'' =>
      obtain ⟨Θa', Θb', Δa'', Δb'', mrg1', mrg2', agra, agrb⟩ := ih mrg''
      obtain ⟨Θc, mrg1a, mrg1b⟩ := mrgΘ.splitL mrg1'
      obtain ⟨Δc, mrg2a, mrg2b⟩ := mrgΔ.splitL mrg2'
      exact ⟨Θc, Θb', Δc, Δb'', mrg1b, mrg2b,
        .wk1 kb kΔb mrg1a mrg2a agra ern, .wk0 agrb ern.toStatic⟩
    | right2 _ mrg'' =>
      obtain ⟨Θa', Θb', Δa'', Δb'', mrg1', mrg2', agra, agrb⟩ := ih mrg''
      obtain ⟨Θc, mrg1a, mrg1b⟩ := mrgΘ.splitR mrg1'
      obtain ⟨Δc, mrg2a, mrg2b⟩ := mrgΔ.splitR mrg2'
      exact ⟨Θa', Θc, Δa'', Δc, mrg1b.sym, mrg2b.sym,
        .wk0 agra ern.toStatic, .wk1 kb kΔb mrg1a mrg2a agrb ern⟩
  | @conv0 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih =>
    intro _ _ mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θa', Θb', Δa', Δb', mrg1', mrg2', agra, agrb⟩ := ih (.null mrg')
      exact ⟨Θa', Θb', Δa', Δb', mrg1', mrg2',
        .conv0 eq tyB1 tyB2 agra, .conv0 eq tyB1 tyB2 agrb⟩
  | @conv1 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih =>
    intro _ _ mrg
    cases mrg with
    | left _ mrg' =>
      obtain ⟨Θa', Θb', Δa', Δb', mrg1', mrg2', agra, agrb⟩ := ih (.left _ mrg')
      exact ⟨Θa', Θb', Δa', Δb', mrg1', mrg2',
        .conv1 eq tyB1 tyB2 agra, .conv1 eq tyB1 tyB2 agrb⟩
    | right1 _ mrg' =>
      obtain ⟨Θa', Θb', Δa', Δb', mrg1', mrg2', agra, agrb⟩ := ih (.right1 _ mrg')
      exact ⟨Θa', Θb', Δa', Δb', mrg1', mrg2',
        .conv1 eq tyB1 tyB2 agra, .conv0 eq tyB1 tyB2 agrb⟩
    | right2 _ mrg' =>
      obtain ⟨Θa', Θb', Δa', Δb', mrg1', mrg2', agra, agrb⟩ := ih (.right2 _ mrg')
      exact ⟨Θa', Θb', Δa', Δb', mrg1', mrg2',
        .conv0 eq tyB1 tyB2 agra, .conv1 eq tyB1 tyB2 agrb⟩

/-- Substitution preserves dynamic well-formedness (Coq `era_substitution_wf`). -/
lemma Wf.substitution {Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2}
    (wf : Wf Γ2 Δ2) (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δ2) : Wf Γ1 Δ1 :=
  wf.substitution agr.toDyn

/-- Substitution preserves the erasure relation (Coq `era_substitution`). -/
lemma Erased.substitution {Θ2 Γ2 Δ2 m m' A} (erm : Θ2 ⨾ Γ2 ⨾ Δ2 ⊢ m ~ m' : A) :
    ∀ {Θ1 Θ Γ1 Δ1 σ1 σ2}, Merge Θ1 Θ2 Θ → (Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ⨾ Δ2) →
      Θ ⨾ Γ1 ⨾ Δ1 ⊢ m[Chan.var_Chan; σ1] ~ m'[Chan.var_Chan; σ2] : A[Chan.var_Chan; σ1] := by
  induction erm with
  | @var Θ2 Γ Δ x s A emp wf shs dhs =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    asimp
    exact AgreeSubst.has agr emp mrg (wf.substitution agr.toDyn) dhs
  | @lamIm Θ2 Γ Δ A B m m' s kΘ kΔ erm ihm =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    asimp
    cases erm.wf with
    | @null _ _ _ s' _ tyA =>
      obtain ⟨ka, kb⟩ := agr.key kΔ
      exact .lamIm (mrg.key_image ka kΘ) kb (ihm mrg (.n agr tyA))
  | @lamEx Θ2 Γ Δ A B m m' s t kΘ kΔ erm ihm =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    asimp
    cases erm.wf with
    | @cons _ _ _ s' _ tyA =>
      obtain ⟨ka, kb⟩ := agr.key kΔ
      exact .lamEx (mrg.key_image ka kΘ) kb (ihm mrg (.ty agr tyA))
  | @appIm Θ2 Γ Δ A B m m' n s erm tyn ihm =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    rw [show (B[Chan.var_Chan; n..])[Chan.var_Chan; σ1]
          = (B[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan; (n[Chan.var_Chan; σ1])..]
          from by asimp]
    have ihm' := ihm mrg agr
    asimp at ihm'
    exact .appIm ihm' (Static.Typed.substitution tyn agr.toStatic)
  | @appEx Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A B m m' n n' s mrgΘ2 mrgΔ erm ern ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    rw [show (B[Chan.var_Chan; n..])[Chan.var_Chan; σ1]
          = (B[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan; (n[Chan.var_Chan; σ1])..]
          from by asimp]
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    have ihm' := ihm mrg4 agra
    asimp at ihm'
    exact .appEx mrg3 mrgy ihm' (ihn mrg5 agrb)
  | @pairIm Θ2 Γ Δ A B m n n' t tyS tym ern ihn =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    have tyS' := Static.Typed.substitution tyS agr.toStatic
    have tym' := Static.Typed.substitution tym agr.toStatic
    have ihn' := ihn mrg agr
    asimp at tyS' ⊢
    rw [show (B[Chan.var_Chan; m..])[Chan.var_Chan; σ1]
          = (B[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan; (m[Chan.var_Chan; σ1])..]
          from by asimp] at ihn'
    exact .pairIm tyS' tym' ihn'
  | @pairEx Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A B m m' n n' t mrgΘ2 mrgΔ tyS erm ern ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    have tyS' := Static.Typed.substitution tyS agr.toStatic
    have ihm' := ihm mrg4 agra
    have ihn' := ihn mrg5 agrb
    asimp at tyS' ⊢
    rw [show (B[Chan.var_Chan; m..])[Chan.var_Chan; σ1]
          = (B[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan; (m[Chan.var_Chan; σ1])..]
          from by asimp] at ihn'
    exact .pairEx mrg3 mrgy tyS' ihm' ihn'
  | @projIm Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A B C m m' n n' s r t mrgΘ2 mrgΔ tyC erm ern ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    rw [show (C[Chan.var_Chan; m..])[Chan.var_Chan; σ1]
          = (C[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan; (m[Chan.var_Chan; σ1])..]
          from by asimp]
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    cases tyC.wf with
    | @cons _ _ s' _ tyAB =>
      cases ern.wf with
      | @cons _ _ _ s'' wfA tyB =>
        cases wfA with
        | @null _ _ _ s''' _ tyA =>
          have ihC := Static.Typed.substitution tyC (.ty agr.toStatic tyAB)
          have ihm' := ihm mrg4 agra
          have ihn' := ihn mrg5 (.ty (.n agrb tyA) tyB)
          asimp at ihC ihm'
          rw [show (C[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                  up_Term_Term (up_Term_Term σ1)]
                = (C[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)]
                from by
                  asimp; congr 1; funext x
                  rcases x with _ | _ | x
                  · rfl
                  · asimp; substify
                  · asimp; substify] at ihn'
          exact .projIm mrg3 mrgy ihC ihm' ihn'
  | @projEx Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A B C m m' n n' s r1 r2 t mrgΘ2 mrgΔ tyC erm ern ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    rw [show (C[Chan.var_Chan; m..])[Chan.var_Chan; σ1]
          = (C[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan; (m[Chan.var_Chan; σ1])..]
          from by asimp]
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    cases tyC.wf with
    | @cons _ _ s' _ tyAB =>
      cases ern.wf with
      | @cons _ _ _ s'' wfA tyB =>
        cases wfA with
        | @cons _ _ _ s''' _ tyA =>
          have ihC := Static.Typed.substitution tyC (.ty agr.toStatic tyAB)
          have ihm' := ihm mrg4 agra
          have ihn' := ihn mrg5 (.ty (.ty agrb tyA) tyB)
          asimp at ihC ihm'
          rw [show (C[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                  up_Term_Term (up_Term_Term σ1)]
                = (C[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)]
                from by
                  asimp; congr 1; funext x
                  rcases x with _ | _ | x
                  · rfl
                  · asimp; substify
                  · asimp; substify] at ihn'
          exact .projEx mrg3 mrgy ihC ihm' ihn'
  | @one Θ2 Γ Δ emp wf k =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    asimp
    obtain ⟨ka, kb⟩ := agr.key k
    have e := mrg.pureL ka; subst e
    exact .one emp (wf.substitution agr.toDyn) kb
  | @tt Θ2 Γ Δ emp wf k =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    asimp
    obtain ⟨ka, kb⟩ := agr.key k
    have e := mrg.pureL ka; subst e
    exact .tt emp (wf.substitution agr.toDyn) kb
  | @ff Θ2 Γ Δ emp wf k =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    asimp
    obtain ⟨ka, kb⟩ := agr.key k
    have e := mrg.pureL ka; subst e
    exact .ff emp (wf.substitution agr.toDyn) kb
  | @ite Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A m m' n1 n1' n2 n2' s mrgΘ2 mrgΔ tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    rw [show (A[Chan.var_Chan; m..])[Chan.var_Chan; σ1]
          = (A[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan; (m[Chan.var_Chan; σ1])..]
          from by asimp]
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    have tyBool : Γ ⊢ Term.bool : Term.srt .U := .bool erm.toStatic.wf
    have tyA' := Static.Typed.substitution tyA (.ty agr.toStatic tyBool)
    have ihm' := ihm mrg4 agra
    have ihn1' := ihn1 mrg5 agrb
    have ihn2' := ihn2 mrg5 agrb
    asimp at tyA'
    rw [show (A[Chan.var_Chan; Term.tt..])[Chan.var_Chan; σ1]
          = (A[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan; Term.tt..] from by asimp] at ihn1'
    rw [show (A[Chan.var_Chan; Term.ff..])[Chan.var_Chan; σ1]
          = (A[Chan.var_Chan; up_Term_Term σ1])[Chan.var_Chan; Term.ff..] from by asimp] at ihn2'
    exact .ite mrg3 mrgy tyA' ihm' ihn1' ihn2'
  | @pure Θ2 Γ Δ m m' A erm ihm =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    asimp
    exact .pure (ihm mrg agr)
  | @mlet Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ m m' n n' A B s t mrgΘ2 mrgΔ tyB erm ern ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    asimp
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    cases ern.wf with
    | @cons _ _ _ s' _ tyA =>
      have tyB' := Static.Typed.substitution tyB agr.toStatic
      have ihm' := ihm mrg4 agra
      have ihn' := ihn mrg5 (.ty agrb tyA)
      asimp at tyB' ⊢
      rw [show (Term.M (B⟨(id : Nat → Nat); ↑⟩))[Chan.var_Chan; up_Term_Term σ1]
            = Term.M ((B[Chan.var_Chan; σ1])⟨(id : Nat → Nat); ↑⟩) from by
            show Term.M _ = Term.M _; congr 1; asimp] at ihn'
      exact .mlet mrg3 mrgy tyB' ihm' ihn'
  | @chan Θ2 Γ Δ r x A js wf k tyA =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    obtain ⟨k1, k2⟩ := agr.key k
    have e := mrg.pureL k1; subst e
    rw [show (Term.chan (Chan.var_Chan x))[Chan.var_Chan; σ1]
          = Term.chan (Chan.var_Chan x) from rfl,
        show (Term.chan (Chan.var_Chan x))[Chan.var_Chan; σ2]
          = Term.chan (Chan.var_Chan x) from rfl,
        show (Term.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩))[Chan.var_Chan; σ1]
          = Term.ch r (A[Chan.var_Chan; funcomp σ1 (· + Γ.length)]) from by
          show Term.ch r _ = Term.ch r _
          congr 1
          asimp
          try substify,
        agr.toStatic.size,
        show A[Chan.var_Chan; funcomp Term.var_Term (· + Γ1.length)]
          = A⟨(id : Nat → Nat); (· + Γ1.length)⟩ from
          (rinst_inst_Term id (· + Γ1.length) Chan.var_Chan
            (funcomp Term.var_Term (· + Γ1.length)) (congrFun rfl) (congrFun rfl) A).symm]
    exact .chan js (wf.substitution agr.toDyn) k2 tyA
  | @fork Θ2 Γ Δ A m m' erm ihm =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    asimp
    cases erm.wf with
    | @cons _ _ _ s' _ tyCh =>
      have ihm' := ihm mrg (.ty agr tyCh)
      asimp at ihm'
      exact .fork ihm'
  | @recv Θ2 Γ Δ r1 r2 A B m m' i hxor erm ihm =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr; asimp; exact .recv hxor (ihm mrg agr)
  | @send Θ2 Γ Δ r1 r2 A B m m' i hxor erm ihm =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr; asimp; exact .send hxor (ihm mrg agr)
  | @close Θ2 Γ Δ b m m' erm ihm =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr; asimp; exact .close (ihm mrg agr)
  | @conv Θ2 Γ Δ A B m m' s eq erm tyB ihm =>
    intro Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr
    have h := Static.Typed.substitution tyB agr.toStatic
    asimp at h
    exact .conv (Static.conv_subst σ1 eq) (ihm mrg agr) h

/-- Substitution of a static argument into a null slot (Coq `era_subst0`). -/
lemma Erased.subst0 {Θ Γ Δ m m' n A B}
    (erm : Θ ⨾ (A :: Γ) ⨾ (none :: Δ) ⊢ m ~ m' : B) (tyn : Γ ⊢ n : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m[Chan.var_Chan; n..] ~ m'[Chan.var_Chan; (Term.box)..] : B[Chan.var_Chan; n..] := by
  cases erm.wf with
  | @null _ _ _ s wf' tyA =>
    obtain ⟨Θ0, emp, mrg⟩ := erm.empty
    have agr := AgreeSubst.wk0 (AgreeSubst.refl emp wf') (n := n) (n' := Term.box) (A := A)
      (by asimp; exact tyn)
    have h := erm.substitution mrg agr
    asimp at h
    exact h

/-- Linear substitution of an argument (Coq `era_subst1`). -/
lemma Erased.subst1 {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s}
    (k1 : Θ2 ▷ s) (mrg1 : Merge Θ1 Θ2 Θ) (k2 : Δ2 ▷ s) (mrg2 : Merge Δ1 Δ2 Δ)
    (erm : Θ1 ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ1) ⊢ m ~ m' : B) (ern : Θ2 ⨾ Γ ⨾ Δ2 ⊢ n ~ n' : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m[Chan.var_Chan; n..] ~ m'[Chan.var_Chan; n'..] : B[Chan.var_Chan; n..] := by
  cases erm.wf with
  | @cons _ _ _ s' wf' tyA =>
    obtain ⟨Θ0, emp, mrg⟩ := ern.empty
    have agr : AgreeSubst Θ2 Γ Δ (n .: Term.var_Term) (n' .: Term.var_Term) (A :: Γ) (A :⟨s⟩ Δ1) :=
      AgreeSubst.wk1 k1 k2 mrg mrg2 (AgreeSubst.refl emp wf')
        (by asimp; exact ern)
    have h := erm.substitution mrg1.sym agr
    asimp at h
    exact h

/-- Null-slot substitution up to equality (Coq `era_esubst0`). -/
lemma Erased.esubst0 {Θ Γ Δ m m' n n' v A B B'}
    (em : m' = m[Chan.var_Chan; v..])
    (en : n' = n[Chan.var_Chan; (Term.box)..])
    (eB : B' = B[Chan.var_Chan; v..])
    (erm : Θ ⨾ (A :: Γ) ⨾ (none :: Δ) ⊢ m ~ n : B) (tyv : Γ ⊢ v : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m' ~ n' : B' := by
  subst em; subst en; subst eB; exact erm.subst0 tyv

/-- Linear substitution up to equality (Coq `era_esubst1`). -/
lemma Erased.esubst1 {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' v v' A B B' s}
    (em : m' = m[Chan.var_Chan; v..])
    (en : n' = n[Chan.var_Chan; v'..])
    (eB : B' = B[Chan.var_Chan; v..])
    (k1 : Θ2 ▷ s) (mrg1 : Merge Θ1 Θ2 Θ) (k2 : Δ2 ▷ s) (mrg2 : Merge Δ1 Δ2 Δ)
    (erm : Θ1 ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ1) ⊢ m ~ n : B) (tyv : Θ2 ⨾ Γ ⨾ Δ2 ⊢ v ~ v' : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m' ~ n' : B' := by
  subst em; subst en; subst eB
  exact Erased.subst1 k1 mrg1 k2 mrg2 erm tyv

/-- Context conversion of the topmost hypothesis, null slot (Coq `era_ctx_conv0`). -/
lemma Erased.ctx_conv0 {Θ Γ Δ m m' A B C s}
    (eq : B ≃ A) (tyB : Γ ⊢ B : .srt s) (erm : Θ ⨾ (A :: Γ) ⨾ (none :: Δ) ⊢ m ~ m' : C) :
    Θ ⨾ (B :: Γ) ⨾ (none :: Δ) ⊢ m ~ m' : C := by
  cases erm.wf with
  | @null _ _ _ s' wf' tyA =>
    obtain ⟨Θ0, emp, mrg⟩ := erm.empty
    have agr : AgreeSubst Θ0 (B :: Γ) (none :: Δ) Term.var_Term Term.var_Term (A :: Γ) (none :: Δ) :=
      AgreeSubst.conv0 eq
        (Static.Typed.eweaken (congrFun instId_Term (A⟨(id : Nat → Nat); ↑⟩)) rfl tyA tyB)
        tyA (AgreeSubst.refl emp (.null wf' tyB))
    have h := erm.substitution mrg agr
    asimp at h
    exact h

/-- Context conversion of the topmost hypothesis, real slot (Coq `era_ctx_conv1`). -/
lemma Erased.ctx_conv1 {Θ Γ Δ m m' A B C s}
    (eq : B ≃ A) (tyB : Γ ⊢ B : .srt s) (erm : Θ ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ) ⊢ m ~ m' : C) :
    Θ ⨾ (B :: Γ) ⨾ (B :⟨s⟩ Δ) ⊢ m ~ m' : C := by
  cases erm.wf with
  | @cons _ _ _ s' wf' tyA =>
    obtain ⟨Θ0, emp, mrg⟩ := erm.empty
    have agr : AgreeSubst Θ0 (B :: Γ) (B :⟨s⟩ Δ) Term.var_Term Term.var_Term (A :: Γ) (A :⟨s⟩ Δ) :=
      AgreeSubst.conv1 eq
        (Static.Typed.eweaken (congrFun instId_Term (A⟨(id : Nat → Nat); ↑⟩)) rfl tyA tyB)
        tyA (AgreeSubst.refl emp (.cons wf' tyB))
    have h := erm.substitution mrg agr
    asimp at h
    exact h

end TLLC.Erasure
