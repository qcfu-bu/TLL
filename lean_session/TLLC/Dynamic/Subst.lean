import TLLC.Dynamic.Rename

/-!
# Dynamic substitution

Port of `coq_session/dyn_subst.v`: the dynamic substitution-agreement relation `AgreeSubst`
(Coq `dyn_agree_subst`, notation `Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2`), which threads a process context
`Θ1`, a static context pair `(Γ1, Γ2)`, a dynamic (linear) context pair `(Δ1, Δ2)` and a
substitution `σ`; its structural lemmas; the substitution-preservation metatheorem
`Typed.substitution` (Coq `dyn_substitution`); and the corollaries `Typed.subst0`/`subst1`/`esubst0`/
`esubst1` and `Typed.ctx_conv0`/`ctx_conv1`.

Coq proves `dyn_substitution` through the mutual recursor `dyn_type_mut` with a motive for `dyn_wf`.
Because here `Wf` is standalone (see `Typing.lean`), the well-formedness preservation
(Coq `dyn_substitution_wf`) is a separate lemma `Wf.substitution`, proved first; `Typed.substitution`
is then a plain induction over the `Typed` cases.

Notation: the Coq `;`-token judgment notation poisons the tactic `;`, so we use `⨾`:
`Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ Γ2 ⨾ Δ2 := AgreeSubst Θ1 Γ1 Δ1 σ Γ2 Δ2`.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- Dynamic substitution agreement (Coq `dyn_agree_subst`). -/
inductive AgreeSubst :
    Ctx → Static.Ctx → Ctx → (Nat → Term) → Static.Ctx → Ctx → Prop where
  | nil {Θ1} :
    Empty Θ1 →
    AgreeSubst Θ1 ([] : Static.Ctx) ([] : Ctx) Term.var_Term ([] : Static.Ctx) ([] : Ctx)
  | ty {Θ1 Γ1 Δ1 σ Γ2 Δ2 A s} :
    AgreeSubst Θ1 Γ1 Δ1 σ Γ2 Δ2 →
    Γ2 ⊢ A : .srt s →
    AgreeSubst Θ1 (A[Chan.var_Chan; σ] :: Γ1) (A[Chan.var_Chan; σ] :⟨s⟩ Δ1)
      (up_Term_Term σ) (A :: Γ2) (A :⟨s⟩ Δ2)
  | n {Θ1 Γ1 Δ1 σ Γ2 Δ2 A s} :
    AgreeSubst Θ1 Γ1 Δ1 σ Γ2 Δ2 →
    Γ2 ⊢ A : .srt s →
    AgreeSubst Θ1 (A[Chan.var_Chan; σ] :: Γ1) (□: Δ1)
      (up_Term_Term σ) (A :: Γ2) (□: Δ2)
  | wk0 {Θ1 Γ1 Δ1 σ Γ2 Δ2 n A} :
    AgreeSubst Θ1 Γ1 Δ1 σ Γ2 Δ2 →
    Γ1 ⊢ n : A[Chan.var_Chan; σ] →
    AgreeSubst Θ1 Γ1 Δ1 (n .: σ) (A :: Γ2) (□: Δ2)
  | wk1 {Θa Θb Θ1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s} :
    Θb ▷ s →
    Δb ▷ s →
    Merge Θa Θb Θ1 →
    Merge Δa Δb Δ1 →
    AgreeSubst Θa Γ1 Δa σ Γ2 Δ2 →
    Typed Θb Γ1 Δb n (A[Chan.var_Chan; σ]) →
    AgreeSubst Θ1 Γ1 Δ1 (n .: σ) (A :: Γ2) (A :⟨s⟩ Δ2)
  | conv0 {Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s} :
    A ≃ B →
    Γ1 ⊢ (B⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; σ] : .srt s →
    Γ2 ⊢ B : .srt s →
    AgreeSubst Θ1 Γ1 Δ1 σ (A :: Γ2) (□: Δ2) →
    AgreeSubst Θ1 Γ1 Δ1 σ (B :: Γ2) (□: Δ2)
  | conv1 {Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s} :
    A ≃ B →
    Γ1 ⊢ (B⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; σ] : .srt s →
    Γ2 ⊢ B : .srt s →
    AgreeSubst Θ1 Γ1 Δ1 σ (A :: Γ2) (A :⟨s⟩ Δ2) →
    AgreeSubst Θ1 Γ1 Δ1 σ (B :: Γ2) (B :⟨s⟩ Δ2)

@[inherit_doc]
scoped notation:50 Θ1:50 " ⨾ " Γ1:51 " ⨾ " Δ1:51 " ⊢ " σ:51 " ⊣ " Γ2:51 " ⨾ " Δ2:51 =>
  AgreeSubst Θ1 Γ1 Δ1 σ Γ2 Δ2

/-- Substitution agreement transports keys (Coq `dyn_agree_subst_key`). -/
lemma AgreeSubst.key {Θ1 Γ1 Γ2 Δ1 Δ2 σ s}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ Γ2 ⨾ Δ2) (k : Δ2 ▷ s) : Θ1 ▷ s ∧ Δ1 ▷ s := by
  induction agr generalizing s with
  | nil emp => exact ⟨emp.key, .nil⟩
  | @ty Θ1 Γ1 Δ1 σ Γ2 Δ2 A s' agr tyA ih =>
    cases k with
    | U _ k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨k1, .U _ k2⟩
    | L _ k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨Key.impure, .L _ k2⟩
  | @n Θ1 Γ1 Δ1 σ Γ2 Δ2 A s' agr tyA ih =>
    cases k with
    | null k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨k1, .null k2⟩
  | @wk0 Θ1 Γ1 Δ1 σ Γ2 Δ2 n A agr tyn ih =>
    cases k with
    | null k' => exact ih k'
  | @wk1 Θa Θb Θ1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s' kb kΔb mrgΘ mrgΔ agr tyn ih =>
    cases k with
    | U _ k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨mrgΘ.key_image k1 kb, mrgΔ.key_image k2 kΔb⟩
    | L _ k' => exact ⟨Key.impure, Key.impure⟩
  | @conv0 Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s' eq tyB1 tyB2 agr ih =>
    cases k with
    | null k' => exact ih (.null k')
  | @conv1 Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s' eq tyB1 tyB2 agr ih =>
    cases k with
    | U _ k' => exact ih (.U _ k')
    | L _ k' => exact ih (.L _ k')

/-- The static projection of a dynamic substitution agreement (Coq `dyn_sta_agree_subst`). -/
lemma AgreeSubst.toStatic {Θ1 Γ1 Γ2 Δ1 Δ2 σ}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ Γ2 ⨾ Δ2) : Γ1 ⊢ σ ⊣ Γ2 := by
  induction agr with
  | nil _ => exact .nil
  | ty _ tyA ih => exact .ty ih tyA
  | n _ tyA ih => exact .ty ih tyA
  | wk0 _ tyn ih => exact .wk1 ih tyn
  | wk1 _ _ _ _ _ tyn ih => exact .wk1 ih tyn.toStatic
  | conv0 eq tyB1 tyB2 _ ih => exact .conv eq tyB1 tyB2 ih
  | conv1 eq tyB1 tyB2 _ ih => exact .conv eq tyB1 tyB2 ih

/-- The identity substitution agrees a well-formed pair with itself (Coq `dyn_agree_subst_refl`). -/
lemma AgreeSubst.refl : ∀ {Θ Γ Δ}, Empty Θ → Wf Γ Δ → Θ ⨾ Γ ⨾ Δ ⊢ Term.var_Term ⊣ Γ ⨾ Δ
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

/-- A typing in a process context yields an empty splitter (Coq `dyn_type_empty`). -/
lemma Typed.empty {Θ1 Γ Δ m A} (ty : Θ1 ⨾ Γ ⨾ Δ ⊢ m : A) :
    ∃ Θ, Empty Θ ∧ Merge Θ Θ1 Θ1 := by
  induction ty with
  | @var Θ Γ Δ x s A emp wf shs dhs => exact ⟨Θ, emp, emp.merge_self⟩
  | @lamIm Θ Γ Δ A B m s k1 k2 tym ih => exact ih
  | @lamEx Θ Γ Δ A B m s t k1 k2 tym ih => exact ih
  | @appIm Θ Γ Δ A B m n s tym tyn ihm => exact ihm
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym tyn ihm ihn =>
    obtain ⟨Θm, empm, mrgm⟩ := ihm
    obtain ⟨Θn, empn, mrgn⟩ := ihn
    obtain ⟨Θx, Θy, mrgx, mrgy, mrgz⟩ := mrg1.distr mrgm mrgn
    have e := mrg1.inj mrgz; subst e
    exact ⟨Θx, mrgy.empty_image empm empn, mrgx⟩
  | @pairIm Θ Γ Δ A B m n t tyS tym tyn ihn => exact ihn
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym tyn ihm ihn =>
    obtain ⟨Θm, empm, mrgm⟩ := ihm
    obtain ⟨Θn, empn, mrgn⟩ := ihn
    obtain ⟨Θx, Θy, mrgx, mrgy, mrgz⟩ := mrg1.distr mrgm mrgn
    have e := mrg1.inj mrgz; subst e
    exact ⟨Θx, mrgy.empty_image empm empn, mrgx⟩
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym tyn ihm ihn =>
    obtain ⟨Θm, empm, mrgm⟩ := ihm
    obtain ⟨Θn, empn, mrgn⟩ := ihn
    obtain ⟨Θx, Θy, mrgx, mrgy, mrgz⟩ := mrg1.distr mrgm mrgn
    have e := mrg1.inj mrgz; subst e
    exact ⟨Θx, mrgy.empty_image empm empn, mrgx⟩
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym tyn ihm ihn =>
    obtain ⟨Θm, empm, mrgm⟩ := ihm
    obtain ⟨Θn, empn, mrgn⟩ := ihn
    obtain ⟨Θx, Θy, mrgx, mrgy, mrgz⟩ := mrg1.distr mrgm mrgn
    have e := mrg1.inj mrgz; subst e
    exact ⟨Θx, mrgy.empty_image empm empn, mrgx⟩
  | @one Θ Γ Δ emp wf k => exact ⟨Θ, emp, emp.merge_self⟩
  | @tt Θ Γ Δ emp wf k => exact ⟨Θ, emp, emp.merge_self⟩
  | @ff Θ Γ Δ emp wf k => exact ⟨Θ, emp, emp.merge_self⟩
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    obtain ⟨Θm, empm, mrgm⟩ := ihm
    obtain ⟨Θn, empn, mrgn⟩ := ihn1
    obtain ⟨Θx, Θy, mrgx, mrgy, mrgz⟩ := mrg1.distr mrgm mrgn
    have e := mrg1.inj mrgz; subst e
    exact ⟨Θx, mrgy.empty_image empm empn, mrgx⟩
  | @pure Θ Γ Δ m A tym ih => exact ih
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym tyn ihm ihn =>
    obtain ⟨Θm, empm, mrgm⟩ := ihm
    obtain ⟨Θn, empn, mrgn⟩ := ihn
    obtain ⟨Θx, Θy, mrgx, mrgy, mrgz⟩ := mrg1.distr mrgm mrgn
    have e := mrg1.inj mrgz; subst e
    exact ⟨Θx, mrgy.empty_image empm empn, mrgx⟩
  | @chan Θ Γ Δ r x A js wf k tyA => exact js.empty
  | @fork Θ Γ Δ A m tym ih => exact ih
  | @recv Θ Γ Δ r1 r2 A B m i e tym ih => exact ih
  | @send Θ Γ Δ r1 r2 A B m i e tym ih => exact ih
  | @close Θ Γ Δ b m tym ih => exact ih
  | @conv Θ Γ Δ A B m s eq tym tyB ih => exact ih

/-- Substitution agreement transports linear lookups (Coq `dyn_agree_subst_has`). -/
lemma AgreeSubst.has {Θ1 Θ2 Θ Γ1 Γ2 σ Δ1 Δ2 x s A}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ Γ2 ⨾ Δ2) (emp2 : Empty Θ2) (mrg : Merge Θ1 Θ2 Θ)
    (wf : Wf Γ1 Δ1) (hs : Has Δ2 x s A) :
    Θ ⨾ Γ1 ⨾ Δ1 ⊢ σ x : A[Chan.var_Chan; σ] := by
  induction agr generalizing x Θ2 Θ s A with
  | nil emp1 => cases hs
  | @ty Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr tyA ih =>
    cases wf with
    | @cons _ _ _ _ wf' tyA' =>
      cases hs with
      | @zero _ A' _ k =>
        obtain ⟨k1, k2⟩ := agr.key k
        have e := mrg.pureL k1; subst e
        rw [show (A⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; up_Term_Term σ]
              = (A[Chan.var_Chan; σ])⟨(id : Nat → Nat); ↑⟩ from by asimp]
        exact .var emp2 (.cons wf' tyA') Static.Has.zero (Has.zero k2)
      | @succ _ A' _ y _ hs =>
        rw [show (A'⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; up_Term_Term σ]
              = (A'[Chan.var_Chan; σ])⟨(id : Nat → Nat); ↑⟩ from by asimp,
            show (up_Term_Term σ) (y + 1) = (σ y)⟨(id : Nat → Nat); ↑⟩ from by asimp]
        exact Typed.eweakenU rfl rfl tyA' (ih emp2 mrg wf' hs)
  | @n Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr tyA ih =>
    cases wf with
    | @null _ _ _ _ wf' tyA' =>
      cases hs with
      | @null _ A' y _ hs =>
        rw [show (A'⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; up_Term_Term σ]
              = (A'[Chan.var_Chan; σ])⟨(id : Nat → Nat); ↑⟩ from by asimp,
            show (up_Term_Term σ) (y + 1) = (σ y)⟨(id : Nat → Nat); ↑⟩ from by asimp]
        exact Typed.eweakenN rfl rfl tyA' (ih emp2 mrg wf' hs)
  | @wk0 Θ1 Γ1 Δ1 σ Γ2 Δ2 n A agr tyn ih =>
    cases hs with
    | @null _ A' _ _ hs =>
      asimp
      exact ih emp2 mrg wf hs
  | @wk1 Θa Θb Θ1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s kb kΔb mrgΘ mrgΔ agr tyn ih =>
    cases hs with
    | @zero _ A' _ k =>
      asimp
      obtain ⟨k3, k4⟩ := agr.key k
      have e := mrgΘ.pureL k3; subst e
      have e := mrgΔ.pureL k4; subst e
      have e := mrg.emptyR emp2; subst e
      exact tyn
    | @succ _ A' _ _ _ hs =>
      asimp
      have e := mrgΘ.pureR kb; subst e
      have e := mrgΔ.pureR kΔb; subst e
      exact ih emp2 mrg wf hs
  | @conv0 Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih =>
    cases hs with
    | @null _ A' _ _ hs =>
      exact ih emp2 mrg wf (.null hs)
  | @conv1 Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih =>
    cases hs with
    | @zero _ A' _ k =>
      apply Typed.conv
      · exact Static.conv_subst σ (Static.conv_ren Nat.succ eq)
      · exact ih emp2 mrg wf (.zero k)
      · exact tyB1
    | @succ _ A' _ _ _ hs =>
      exact ih emp2 mrg wf (.succ hs)

/-- Substitution agreement is compatible with merge (Coq `dyn_agree_subst_merge`). -/
lemma AgreeSubst.merge {Θ1 Γ1 Γ2 Δ1 Δ2 σ}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ Γ2 ⨾ Δ2) :
    ∀ {Δa Δb}, Merge Δa Δb Δ2 →
    ∃ Θa' Θb' Δa' Δb',
      Merge Θa' Θb' Θ1 ∧
      Merge Δa' Δb' Δ1 ∧
      (Θa' ⨾ Γ1 ⨾ Δa' ⊢ σ ⊣ Γ2 ⨾ Δa) ∧
      (Θb' ⨾ Γ1 ⨾ Δb' ⊢ σ ⊣ Γ2 ⨾ Δb) := by
  induction agr with
  | @nil Θ1 emp =>
    intro _ _ mrg; cases mrg
    exact ⟨Θ1, Θ1, [], [], emp.merge_self, .nil, .nil emp, .nil emp⟩
  | @ty Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr tyA ih =>
    intro _ _ mrg
    cases mrg with
    | left _ mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, A[Chan.var_Chan; σ] :U Δa, A[Chan.var_Chan; σ] :U Δb,
        mrg1, .left _ mrg2, .ty agra tyA, .ty agrb tyA⟩
    | right1 _ mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, A[Chan.var_Chan; σ] :L Δa, □: Δb,
        mrg1, .right1 _ mrg2, .ty agra tyA, .n agrb tyA⟩
    | right2 _ mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, □: Δa, A[Chan.var_Chan; σ] :L Δb,
        mrg1, .right2 _ mrg2, .n agra tyA, .ty agrb tyA⟩
  | @n Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr tyA ih =>
    intro _ _ mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, □: Δa, □: Δb, mrg1, .null mrg2, .n agra tyA, .n agrb tyA⟩
  | @wk0 Θ1 Γ1 Δ1 σ Γ2 Δ2 n A agr tyn ih =>
    intro _ _ mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, agra, agrb⟩ := ih mrg'
      exact ⟨Θa, Θb, Δa, Δb, mrg1, mrg2, .wk0 agra tyn, .wk0 agrb tyn⟩
  | @wk1 Θa Θb Θ1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s kb kΔb mrgΘ mrgΔ agr tyn ih =>
    intro Δa' Δb' mrg'
    cases mrg' with
    | left _ mrg'' =>
      obtain ⟨Θa', Θb', Δa'', Δb'', mrg1', mrg2', agra, agrb⟩ := ih mrg''
      obtain ⟨Θc, mrg1a, mrg1b⟩ := mrgΘ.splitL mrg1'
      obtain ⟨Δc, mrg2a, mrg2b⟩ := mrgΔ.splitL mrg2'
      refine ⟨Θc, Θb', Δc, Δb'', mrg1b, mrg2b, ?_, ?_⟩
      · exact .wk1 kb kΔb mrg1a mrg2a agra tyn
      · obtain ⟨Θd, mrg3, _⟩ := mrgΘ.splitR mrg1'
        obtain ⟨Δd, mrg4, _⟩ := mrgΔ.splitR mrg2'
        have e := mrg3.pureR kb; subst e
        have e := mrg4.pureR kΔb; subst e
        exact .wk1 kb kΔb mrg3 mrg4 agrb tyn
    | right1 _ mrg'' =>
      obtain ⟨Θa', Θb', Δa'', Δb'', mrg1', mrg2', agra, agrb⟩ := ih mrg''
      obtain ⟨Θc, mrg1a, mrg1b⟩ := mrgΘ.splitL mrg1'
      obtain ⟨Δc, mrg2a, mrg2b⟩ := mrgΔ.splitL mrg2'
      exact ⟨Θc, Θb', Δc, Δb'', mrg1b, mrg2b,
        .wk1 kb kΔb mrg1a mrg2a agra tyn, .wk0 agrb tyn.toStatic⟩
    | right2 _ mrg'' =>
      obtain ⟨Θa', Θb', Δa'', Δb'', mrg1', mrg2', agra, agrb⟩ := ih mrg''
      obtain ⟨Θc, mrg1a, mrg1b⟩ := mrgΘ.splitR mrg1'
      obtain ⟨Δc, mrg2a, mrg2b⟩ := mrgΔ.splitR mrg2'
      exact ⟨Θa', Θc, Δa'', Δc, mrg1b.sym, mrg2b.sym,
        .wk0 agra tyn.toStatic, .wk1 kb kΔb mrg1a mrg2a agrb tyn⟩
  | @conv0 Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih =>
    intro _ _ mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θa', Θb', Δa', Δb', mrg1', mrg2', agra, agrb⟩ := ih (.null mrg')
      exact ⟨Θa', Θb', Δa', Δb', mrg1', mrg2',
        .conv0 eq tyB1 tyB2 agra, .conv0 eq tyB1 tyB2 agrb⟩
  | @conv1 Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih =>
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

/-- An agreement into the empty pair produces a well-formed source (Coq `dyn_agree_subst_wf_nil`). -/
lemma AgreeSubst.wf_nil {Θ1 Γ1 Δ1 σ}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ ([] : Static.Ctx) ⨾ ([] : Ctx)) : Wf Γ1 Δ1 := by
  generalize e1 : ([] : Static.Ctx) = Γ2 at agr
  generalize e2 : ([] : Ctx) = Δ2 at agr
  induction agr with
  | nil _ => exact .nil
  | ty _ _ _ => cases e1
  | n _ _ _ => cases e1
  | wk0 _ _ _ => cases e1
  | wk1 _ _ _ _ _ _ _ => cases e1
  | conv0 _ _ _ _ _ => cases e1
  | conv1 _ _ _ _ _ => cases e1

/-- Extending the target by a real slot keeps the source well-formed (Coq `dyn_agree_subst_wf_ty`). -/
lemma AgreeSubst.wf_ty {Θ1 Γ1 Γ2 Δ1 Δ2 A s σ}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ (A :: Γ2) ⨾ (A :⟨s⟩ Δ2)) (_wf : Wf Γ2 Δ2)
    (ih0 : ∀ {Θ1 Γ1 Δ1 σ}, (Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ Γ2 ⨾ Δ2) → Wf Γ1 Δ1) :
    Wf Γ1 Δ1 := by
  generalize e1 : (A :: Γ2) = Γ0 at agr
  generalize e2 : (A :⟨s⟩ Δ2) = Δ0 at agr
  induction agr generalizing A Γ2 Δ2 s with
  | nil _ => cases e1
  | @ty Θ1 Γ1 Δ1 σ Γ2' Δ2' A' s' agr tyA' _ =>
    cases e1; cases e2
    refine .cons (ih0 agr) ?_
    have h := Static.Typed.substitution tyA' agr.toStatic
    asimp at h
    exact h
  | @n Θ1 Γ1 Δ1 σ Γ2' Δ2' A' s' agr tyA' _ => cases e2
  | @wk0 Θ1 Γ1 Δ1 σ Γ2' Δ2' n A' agr tyn _ => cases e2
  | @wk1 Θa Θb Θ1 Γ1 Γ2' σ Δ1 Δ2' Δa Δb n A' s' kb kΔb mrgΘ mrgΔ agr tyn _ =>
    cases e1; cases e2
    exact (ih0 agr).merge mrgΔ tyn.wf
  | @conv0 Θ1 Γ1 Δ1 σ Γ2' Δ2' A' B' s' eq tyB1 tyB2 agr _ => cases e2
  | @conv1 Θ1 Γ1 Δ1 σ Γ2' Δ2' A' B' s' eq tyB1 tyB2 agr ih =>
    cases e1; cases e2
    exact ih _wf ih0 rfl rfl

/-- Extending the target by a null slot keeps the source well-formed (Coq `dyn_agree_subst_wf_n`). -/
lemma AgreeSubst.wf_n {Θ1 Γ1 Γ2 Δ1 Δ2 A σ}
    (agr : Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ (A :: Γ2) ⨾ (□: Δ2)) (_wf : Wf Γ2 Δ2)
    (ih0 : ∀ {Θ1 Γ1 Δ1 σ}, (Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ Γ2 ⨾ Δ2) → Wf Γ1 Δ1) :
    Wf Γ1 Δ1 := by
  generalize e1 : (A :: Γ2) = Γ0 at agr
  generalize e2 : (□: Δ2) = Δ0 at agr
  induction agr generalizing A Γ2 Δ2 with
  | nil _ => cases e1
  | @ty Θ1 Γ1 Δ1 σ Γ2' Δ2' A' s' agr tyA' _ => cases e2
  | @n Θ1 Γ1 Δ1 σ Γ2' Δ2' A' s' agr tyA' _ =>
    cases e1; cases e2
    have h := Static.Typed.substitution tyA' agr.toStatic
    asimp at h
    exact .null (ih0 agr) h
  | @wk0 Θ1 Γ1 Δ1 σ Γ2' Δ2' n A' agr tyn ih =>
    cases e1; cases e2
    exact ih0 agr
  | @wk1 Θa Θb Θ1 Γ1 Γ2' σ Δ1 Δ2' Δa Δb n A' s' kb kΔb mrgΘ mrgΔ agr tyn _ => cases e2
  | @conv0 Θ1 Γ1 Δ1 σ Γ2' Δ2' A' B' s' eq tyB1 tyB2 agr ih =>
    cases e1; cases e2
    exact ih _wf ih0 rfl rfl
  | @conv1 Θ1 Γ1 Δ1 σ Γ2' Δ2' A' B' s' eq tyB1 tyB2 agr _ => cases e2

/-- Substitution preserves dynamic well-formedness (Coq `dyn_substitution_wf`). -/
lemma Wf.substitution {Γ2 Δ2} (wf : Wf Γ2 Δ2) :
    ∀ {Θ1 Γ1 Δ1 σ}, (Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ Γ2 ⨾ Δ2) → Wf Γ1 Δ1 := by
  induction wf with
  | nil => intro _ _ _ _ agr; exact agr.wf_nil
  | @cons Γ Δ A s wf tyA ih => intro _ _ _ _ agr; exact agr.wf_ty wf (fun a => ih a)
  | @null Γ Δ A s wf tyA ih => intro _ _ _ _ agr; exact agr.wf_n wf (fun a => ih a)

/-- Substitution preserves dynamic typing (Coq `dyn_substitution`). -/
lemma Typed.substitution {Θ2 Γ2 Δ2 m A} (tym : Θ2 ⨾ Γ2 ⨾ Δ2 ⊢ m : A) :
    ∀ {Θ1 Θ Γ1 Δ1 σ}, Merge Θ1 Θ2 Θ → (Θ1 ⨾ Γ1 ⨾ Δ1 ⊢ σ ⊣ Γ2 ⨾ Δ2) →
      Θ ⨾ Γ1 ⨾ Δ1 ⊢ m[Chan.var_Chan; σ] : A[Chan.var_Chan; σ] := by
  induction tym with
  | @var Θ2 Γ Δ x s A emp wf shs dhs =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    asimp
    exact AgreeSubst.has agr emp mrg (wf.substitution agr) dhs
  | @lamIm Θ2 Γ Δ A B m s k1 k2 tym ihm =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    asimp
    cases tym.wf with
    | @null _ _ _ s' _ tyA =>
      obtain ⟨ka, kb⟩ := agr.key k2
      exact .lamIm (mrg.key_image ka k1) kb (ihm mrg (.n agr tyA))
  | @lamEx Θ2 Γ Δ A B m s t k1 k2 tym ihm =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    asimp
    cases tym.wf with
    | @cons _ _ _ s' _ tyA =>
      obtain ⟨ka, kb⟩ := agr.key k2
      exact .lamEx (mrg.key_image ka k1) kb (ihm mrg (.ty agr tyA))
  | @appIm Θ2 Γ Δ A B m n s tym tyn ihm =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    rw [show (B[Chan.var_Chan; n..])[Chan.var_Chan; σ]
          = (B[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (n[Chan.var_Chan; σ])..]
          from by asimp]
    have ihm' := ihm mrg agr
    asimp at ihm'
    exact .appIm ihm' (Static.Typed.substitution tyn agr.toStatic)
  | @appEx Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A B m n s mrgΘ2 mrgΔ tym tyn ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    rw [show (B[Chan.var_Chan; n..])[Chan.var_Chan; σ]
          = (B[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (n[Chan.var_Chan; σ])..]
          from by asimp]
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    have ihm' := ihm mrg4 agra
    asimp at ihm'
    exact .appEx mrg3 mrgy ihm' (ihn mrg5 agrb)
  | @pairIm Θ2 Γ Δ A B m n t tyS tym tyn ihn =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    have tyS' := Static.Typed.substitution tyS agr.toStatic
    have tym' := Static.Typed.substitution tym agr.toStatic
    have ihn' := ihn mrg agr
    asimp at tyS' ⊢
    rw [show (B[Chan.var_Chan; m..])[Chan.var_Chan; σ]
          = (B[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m[Chan.var_Chan; σ])..]
          from by asimp] at ihn'
    exact .pairIm tyS' tym' ihn'
  | @pairEx Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A B m n t mrgΘ2 mrgΔ tyS tym tyn ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    have tyS' := Static.Typed.substitution tyS agr.toStatic
    have ihm' := ihm mrg4 agra
    have ihn' := ihn mrg5 agrb
    asimp at tyS' ⊢
    rw [show (B[Chan.var_Chan; m..])[Chan.var_Chan; σ]
          = (B[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m[Chan.var_Chan; σ])..]
          from by asimp] at ihn'
    exact .pairEx mrg3 mrgy tyS' ihm' ihn'
  | @projIm Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A B C m n s r t mrgΘ2 mrgΔ tyC tym tyn ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    rw [show (C[Chan.var_Chan; m..])[Chan.var_Chan; σ]
          = (C[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m[Chan.var_Chan; σ])..]
          from by asimp]
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    cases tyC.wf with
    | @cons _ _ s' _ tyAB =>
      cases tyn.wf with
      | @cons _ _ _ s'' wfA tyB =>
        cases wfA with
        | @null _ _ _ s''' _ tyA =>
          have ihC := Static.Typed.substitution tyC (.ty agr.toStatic tyAB)
          have ihm' := ihm mrg4 agra
          have ihn' := ihn mrg5 (.ty (.n agrb tyA) tyB)
          asimp at ihC ihm'
          rw [show (C[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                  up_Term_Term (up_Term_Term σ)]
                = (C[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)]
                from by
                  asimp; congr 1; funext x
                  rcases x with _ | _ | x
                  · rfl
                  · asimp; substify
                  · asimp; substify] at ihn'
          exact .projIm mrg3 mrgy ihC ihm' ihn'
  | @projEx Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A B C m n s r1 r2 t mrgΘ2 mrgΔ tyC tym tyn ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    rw [show (C[Chan.var_Chan; m..])[Chan.var_Chan; σ]
          = (C[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m[Chan.var_Chan; σ])..]
          from by asimp]
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    cases tyC.wf with
    | @cons _ _ s' _ tyAB =>
      cases tyn.wf with
      | @cons _ _ _ s'' wfA tyB =>
        cases wfA with
        | @cons _ _ _ s''' _ tyA =>
          have ihC := Static.Typed.substitution tyC (.ty agr.toStatic tyAB)
          have ihm' := ihm mrg4 agra
          have ihn' := ihn mrg5 (.ty (.ty agrb tyA) tyB)
          asimp at ihC ihm'
          rw [show (C[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                  up_Term_Term (up_Term_Term σ)]
                = (C[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)]
                from by
                  asimp; congr 1; funext x
                  rcases x with _ | _ | x
                  · rfl
                  · asimp; substify
                  · asimp; substify] at ihn'
          exact .projEx mrg3 mrgy ihC ihm' ihn'
  | @one Θ2 Γ Δ emp wf k =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    asimp
    obtain ⟨ka, kb⟩ := agr.key k
    have e := mrg.pureL ka; subst e
    exact .one emp (wf.substitution agr) kb
  | @tt Θ2 Γ Δ emp wf k =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    asimp
    obtain ⟨ka, kb⟩ := agr.key k
    have e := mrg.pureL ka; subst e
    exact .tt emp (wf.substitution agr) kb
  | @ff Θ2 Γ Δ emp wf k =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    asimp
    obtain ⟨ka, kb⟩ := agr.key k
    have e := mrg.pureL ka; subst e
    exact .ff emp (wf.substitution agr) kb
  | @ite Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ A m n1 n2 s mrgΘ2 mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    rw [show (A[Chan.var_Chan; m..])[Chan.var_Chan; σ]
          = (A[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m[Chan.var_Chan; σ])..]
          from by asimp]
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    have tyBool : Γ ⊢ Term.bool : Term.srt .U := .bool tym.wf.toStatic
    have tyA' := Static.Typed.substitution tyA (.ty agr.toStatic tyBool)
    have ihm' := ihm mrg4 agra
    have ihn1' := ihn1 mrg5 agrb
    have ihn2' := ihn2 mrg5 agrb
    asimp at tyA'
    rw [show (A[Chan.var_Chan; Term.tt..])[Chan.var_Chan; σ]
          = (A[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; Term.tt..] from by asimp] at ihn1'
    rw [show (A[Chan.var_Chan; Term.ff..])[Chan.var_Chan; σ]
          = (A[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; Term.ff..] from by asimp] at ihn2'
    exact .ite mrg3 mrgy tyA' ihm' ihn1' ihn2'
  | @pure Θ2 Γ Δ m A tym ihm =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    asimp
    exact .pure (ihm mrg agr)
  | @mlet Θ2a Θ2b Θ2 Γ Δ1' Δ2' Δ m n A B s t mrgΘ2 mrgΔ tyB tym tyn ihm ihn =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    asimp
    obtain ⟨Θa, Θb, Δa, Δb, mrgx, mrgy, agra, agrb⟩ := agr.merge mrgΔ
    obtain ⟨Θx, Θy, mrg3, mrg4, mrg5⟩ := mrg.distr mrgx mrgΘ2
    cases tyn.wf with
    | @cons _ _ _ s' _ tyA =>
      have tyB' := Static.Typed.substitution tyB agr.toStatic
      have ihm' := ihm mrg4 agra
      have ihn' := ihn mrg5 (.ty agrb tyA)
      asimp at tyB' ⊢
      rw [show (Term.M (B⟨(id : Nat → Nat); ↑⟩))[Chan.var_Chan; up_Term_Term σ]
            = Term.M ((B[Chan.var_Chan; σ])⟨(id : Nat → Nat); ↑⟩) from by
            show Term.M _ = Term.M _; congr 1; asimp] at ihn'
      exact .mlet mrg3 mrgy tyB' ihm' ihn'
  | @chan Θ2 Γ Δ r x A js wf k tyA =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    obtain ⟨k1, k2⟩ := agr.key k
    have e := mrg.pureL k1; subst e
    rw [show (Term.chan (Chan.var_Chan x))[Chan.var_Chan; σ]
          = Term.chan (Chan.var_Chan x) from rfl,
        show (Term.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩))[Chan.var_Chan; σ]
          = Term.ch r (A[Chan.var_Chan; funcomp σ (· + Γ.length)]) from by
          show Term.ch r _ = Term.ch r _
          congr 1
          asimp
          try substify,
        agr.toStatic.size,
        show A[Chan.var_Chan; funcomp Term.var_Term (· + Γ1.length)]
          = A⟨(id : Nat → Nat); (· + Γ1.length)⟩ from
          (rinst_inst_Term id (· + Γ1.length) Chan.var_Chan
            (funcomp Term.var_Term (· + Γ1.length)) (congrFun rfl) (congrFun rfl) A).symm]
    exact .chan js (wf.substitution agr) k2 tyA
  | @fork Θ2 Γ Δ A m tym ihm =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    asimp
    cases tym.wf with
    | @cons _ _ _ s' _ tyCh =>
      have ihm' := ihm mrg (.ty agr tyCh)
      asimp at ihm'
      exact .fork ihm'
  | @recv Θ2 Γ Δ r1 r2 A B m i e tym ihm =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr; asimp; exact .recv e (ihm mrg agr)
  | @send Θ2 Γ Δ r1 r2 A B m i e tym ihm =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr; asimp; exact .send e (ihm mrg agr)
  | @close Θ2 Γ Δ b m tym ihm =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr; asimp; exact .close (ihm mrg agr)
  | @conv Θ2 Γ Δ A B m s eq tym tyB ihm =>
    intro Θ1 Θ Γ1 Δ1 σ mrg agr
    have h := Static.Typed.substitution tyB agr.toStatic
    asimp at h
    exact .conv (Static.conv_subst σ eq) (ihm mrg agr) h

/-- Substitution of a static argument into a null slot (Coq `dyn_subst0`). -/
lemma Typed.subst0 {Θ Γ Δ m n A B}
    (tym : Θ ⨾ (A :: Γ) ⨾ (□: Δ) ⊢ m : B) (tyn : Γ ⊢ n : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m[Chan.var_Chan; n..] : B[Chan.var_Chan; n..] := by
  cases tym.wf with
  | @null _ _ _ s wf' tyA =>
    obtain ⟨Θ0, emp, mrg⟩ := tym.empty
    have agr := AgreeSubst.wk0 (AgreeSubst.refl emp wf') (n := n) (A := A) (by asimp; exact tyn)
    have h := tym.substitution mrg agr
    asimp at h
    exact h

/-- Linear substitution of an argument (Coq `dyn_subst1`). -/
lemma Typed.subst1 {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s}
    (k1 : Θ2 ▷ s) (mrg1 : Merge Θ1 Θ2 Θ) (k2 : Δ2 ▷ s) (mrg2 : Merge Δ1 Δ2 Δ)
    (tym : Θ1 ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ1) ⊢ m : B) (tyn : Θ2 ⨾ Γ ⨾ Δ2 ⊢ n : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m[Chan.var_Chan; n..] : B[Chan.var_Chan; n..] := by
  cases tym.wf with
  | @cons _ _ _ s' wf' tyA =>
    obtain ⟨Θ0, emp, mrg⟩ := tyn.empty
    have agr : AgreeSubst Θ2 Γ Δ (n .: Term.var_Term) (A :: Γ) (A :⟨s⟩ Δ1) :=
      AgreeSubst.wk1 k1 k2 mrg mrg2 (AgreeSubst.refl emp wf')
        (by asimp; exact tyn)
    have h := tym.substitution mrg1.sym agr
    asimp at h
    exact h

/-- Null-slot substitution up to equality (Coq `dyn_esubst0`). -/
lemma Typed.esubst0 {Θ Γ Δ m m' n A B B'}
    (em : m' = m[Chan.var_Chan; n..])
    (eB : B' = B[Chan.var_Chan; n..])
    (tym : Θ ⨾ (A :: Γ) ⨾ (□: Δ) ⊢ m : B) (tyn : Γ ⊢ n : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m' : B' := by
  subst em; subst eB; exact tym.subst0 tyn

/-- Linear substitution up to equality (Coq `dyn_esubst1`). -/
lemma Typed.esubst1 {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n A B B' s}
    (em : m' = m[Chan.var_Chan; n..])
    (eB : B' = B[Chan.var_Chan; n..])
    (k1 : Θ2 ▷ s) (mrg1 : Merge Θ1 Θ2 Θ) (k2 : Δ2 ▷ s) (mrg2 : Merge Δ1 Δ2 Δ)
    (tym : Θ1 ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ1) ⊢ m : B) (tyn : Θ2 ⨾ Γ ⨾ Δ2 ⊢ n : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m' : B' := by
  subst em; subst eB
  exact Typed.subst1 k1 mrg1 k2 mrg2 tym tyn

/-- Context conversion of the topmost hypothesis, null slot (Coq `dyn_ctx_conv0`). -/
lemma Typed.ctx_conv0 {Θ Γ Δ m A B C s}
    (eq : B ≃ A) (tyB : Γ ⊢ B : .srt s) (tym : Θ ⨾ (A :: Γ) ⨾ (□: Δ) ⊢ m : C) :
    Θ ⨾ (B :: Γ) ⨾ (□: Δ) ⊢ m : C := by
  cases tym.wf with
  | @null _ _ _ s' wf' tyA =>
    obtain ⟨Θ0, emp, mrg⟩ := tym.empty
    have agr : AgreeSubst Θ0 (B :: Γ) (□: Δ) Term.var_Term (A :: Γ) (□: Δ) :=
      AgreeSubst.conv0 eq
        (Static.Typed.eweaken (congrFun instId_Term (A⟨(id : Nat → Nat); ↑⟩)) rfl tyA tyB)
        tyA (AgreeSubst.refl emp (.null wf' tyB))
    have h := tym.substitution mrg agr
    asimp at h
    exact h

/-- Context conversion of the topmost hypothesis, real slot (Coq `dyn_ctx_conv1`). -/
lemma Typed.ctx_conv1 {Θ Γ Δ m A B C s}
    (eq : B ≃ A) (tyB : Γ ⊢ B : .srt s) (tym : Θ ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ) ⊢ m : C) :
    Θ ⨾ (B :: Γ) ⨾ (B :⟨s⟩ Δ) ⊢ m : C := by
  cases tym.wf with
  | @cons _ _ _ s' wf' tyA =>
    obtain ⟨Θ0, emp, mrg⟩ := tym.empty
    have agr : AgreeSubst Θ0 (B :: Γ) (B :⟨s⟩ Δ) Term.var_Term (A :: Γ) (A :⟨s⟩ Δ) :=
      AgreeSubst.conv1 eq
        (Static.Typed.eweaken (congrFun instId_Term (A⟨(id : Nat → Nat); ↑⟩)) rfl tyA tyB)
        tyA (AgreeSubst.refl emp (.cons wf' tyB))
    have h := tym.substitution mrg agr
    asimp at h
    exact h

end TLLC.Dynamic
