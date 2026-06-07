import TLLC.Static.Rename

/-!
# Static substitution

Port of `coq_session/sta_subst.v`: the substitution-agreement relation `AgreeSubst` (Coq
`sta_agree_subst`, notation `Γ1 ⊢ σ ⊣ Γ2`), its structural lemmas, the substitution-preservation
metatheorem `substitution` (Coq `sta_substitution`, a mutual induction over `Typed`/`Wf`), and the
corollaries `Typed.subst`/`Typed.esubst` (Coq `sta_subst`/`sta_esubst`) and `Typed.ctx_conv`
(context conversion, Coq `sta_ctx_conv`).
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Substitution agreement between two contexts (Coq `sta_agree_subst`). -/
inductive AgreeSubst : Ctx → (Nat → Term) → Ctx → Prop where
  | nil :
    AgreeSubst ([] : Ctx) Term.var_Term ([] : Ctx)
  | ty {Γ1 σ Γ2 A s} :
    AgreeSubst Γ1 σ Γ2 →
    Γ2 ⊢ A : .srt s →
    AgreeSubst (A[Chan.var_Chan; σ] :: Γ1) (up_Term_Term σ) (A :: Γ2)
  | wk1 {Γ1 σ Γ2 n A} :
    AgreeSubst Γ1 σ Γ2 →
    Γ1 ⊢ n : A[Chan.var_Chan; σ] →
    AgreeSubst Γ1 (n .: σ) (A :: Γ2)
  | wk2 {Γ1 σ Γ2 A s} :
    AgreeSubst Γ1 σ Γ2 →
    Γ1 ⊢ A : .srt s →
    AgreeSubst (A :: Γ1) (fun x => (σ x)⟨(id : Nat → Nat); ↑⟩) Γ2
  | conv {Γ1 σ Γ2 A B s} :
    A ≃ B →
    Γ1 ⊢ (B⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; σ] : .srt s →
    Γ2 ⊢ B : .srt s →
    AgreeSubst Γ1 σ (A :: Γ2) →
    AgreeSubst Γ1 σ (B :: Γ2)

@[inherit_doc] scoped notation:50 Γ1:50 " ⊢ " σ:51 " ⊣ " Γ2:51 => AgreeSubst Γ1 σ Γ2

/-- The identity substitution agrees a well-formed context with itself (Coq `sta_agree_subst_refl`). -/
lemma AgreeSubst.refl : ∀ {Γ}, Wf Γ → Γ ⊢ Term.var_Term ⊣ Γ
  | _, .nil => .nil
  | _, @Wf.cons Γ A s wf tyA => by
    have ih := AgreeSubst.refl wf
    have h := AgreeSubst.ty ih tyA
    rw [show A[Chan.var_Chan; Term.var_Term] = A from by asimp,
        show up_Term_Term Term.var_Term = Term.var_Term from by asimp] at h
    exact h

/-- Substitution agreement transports context lookups (Coq `sta_agree_subst_has`). -/
lemma AgreeSubst.has {Γ1 σ Γ2 x A}
    (agr : Γ1 ⊢ σ ⊣ Γ2) (wf : Wf Γ1) (hs : Has Γ2 x A) :
    Γ1 ⊢ σ x : A[Chan.var_Chan; σ] := by
  induction agr generalizing x A with
  | nil => cases hs
  | @ty Γ1 σ Γ2 A s agr tyA ih =>
    cases hs with
    | zero =>
      rw [show (A⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; up_Term_Term σ]
            = (A[Chan.var_Chan; σ])⟨(id : Nat → Nat); ↑⟩ from by asimp]
      exact .var wf Has.zero
    | @succ Γ A0 B x hs =>
      rw [show (A0⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; up_Term_Term σ]
            = (A0[Chan.var_Chan; σ])⟨(id : Nat → Nat); ↑⟩ from by asimp]
      cases wf with
      | @cons Γ A1 s1 wf1 tyA1 =>
        exact Typed.eweaken (by asimp) rfl (ih wf1 hs) tyA1
  | @wk1 Γ1 σ Γ2 n A agr tyn ih =>
    cases hs with
    | zero =>
      asimp
      exact tyn
    | @succ Γ A0 B x hs =>
      asimp
      exact ih wf hs
  | @wk2 Γ1 σ Γ2 A s agr tyA ih =>
    cases wf with
    | @cons Γ A1 s1 wf1 tyA1 =>
      have ty := ih wf1 hs
      have h := ty.weaken tyA1
      asimp at h ⊢
      exact h
  | @conv Γ1 σ Γ2 A B s eq tyB1 tyB2 agr ih =>
    cases hs with
    | zero =>
      apply Typed.conv
      · exact conv_subst σ (conv_ren Nat.succ eq)
      · exact ih wf Has.zero
      · exact tyB1
    | @succ Γ A0 B0 x hs =>
      exact ih wf (Has.succ hs)

/-- An agreement into the empty context produces a well-formed source (Coq `sta_agree_subst_wf_nil`). -/
lemma AgreeSubst.wf_nil {Γ1 σ} (agr : Γ1 ⊢ σ ⊣ []) : Wf Γ1 := by
  generalize e : ([] : Ctx) = Γ2 at agr
  induction agr with
  | nil => exact .nil
  | ty _ _ _ => cases e
  | @wk1 Γ1 σ Γ2 n A agr tyn ih => cases e
  | @wk2 Γ1 σ Γ2 A s agr tyA ih => exact .cons (ih e) tyA
  | conv _ _ _ _ _ => cases e

/-- Extending the target of an agreement keeps the source well-formed (Coq `sta_agree_subst_wf_cons`). -/
lemma AgreeSubst.wf_cons {Γ1 Γ2 A s σ}
    (agr : Γ1 ⊢ σ ⊣ (A :: Γ2)) (_wf : Wf Γ2)
    (h1 : ∀ {Γ1 σ}, Γ1 ⊢ σ ⊣ Γ2 → Wf Γ1)
    (h2 : ∀ {Γ1 σ}, Γ1 ⊢ σ ⊣ Γ2 → Γ1 ⊢ A[Chan.var_Chan; σ] : .srt s) :
    Wf Γ1 := by
  generalize e : (A :: Γ2) = Γ0 at agr
  induction agr generalizing A s with
  | nil => cases e
  | @ty Γ1' σ' Γ2' A0 s0 agr tyA0 _ =>
    cases e
    exact .cons (h1 agr) (h2 agr)
  | @wk1 Γ1' σ' Γ2' n A0 agr tyn _ =>
    exact tyn.wf
  | @wk2 Γ1' σ' Γ2' A0 s0 agr tyA0 ih =>
    exact .cons (ih h2 e) tyA0
  | @conv Γ1' σ' Γ2' A0 B0 s0 eq tyB1 tyB2 agr _ =>
    exact tyB1.wf

/-- The size shift relating the two contexts (Coq `sta_agree_subst_size`). -/
lemma AgreeSubst.size {Γ Γ' σ} (agr : Γ' ⊢ σ ⊣ Γ) :
    funcomp σ (· + Γ.length) = funcomp Term.var_Term (· + Γ'.length) := by
  induction agr with
  | nil => rfl
  | @ty Γ1 σ Γ2 A s agr tyA ih =>
    funext x
    have h := congrFun ih x
    simp only [funcomp, List.length_cons] at h ⊢
    rw [show x + (Γ2.length + 1) = (x + Γ2.length) + 1 from by omega,
        show (up_Term_Term σ) ((x + Γ2.length) + 1) = (σ (x + Γ2.length))⟨(id : Nat → Nat); ↑⟩
          from by asimp, h]
    asimp
    congr 1
  | @wk1 Γ1 σ Γ2 n A agr tyn ih =>
    funext x
    have h := congrFun ih x
    simp only [funcomp, List.length_cons] at h ⊢
    rw [show x + (Γ2.length + 1) = (x + Γ2.length) + 1 from by omega,
        show (n .: σ) ((x + Γ2.length) + 1) = σ (x + Γ2.length) from rfl, h]
  | @wk2 Γ1 σ Γ2 A s agr tyA ih =>
    funext x
    have h := congrFun ih x
    simp only [funcomp, List.length_cons] at h ⊢
    rw [h]
    asimp
    congr 1
  | @conv Γ1 σ Γ2 A B s eq tyB1 tyB2 agr ih => exact ih

/-- Protocol arity is preserved by substitution (Coq `sta_subst_arity_proto`). -/
lemma subst_arity_proto {A : Term} (σ : Nat → Term) (ar : ArityProto A) :
    ArityProto (A[Chan.var_Chan; σ]) := by
  induction A generalizing σ with
  | proto => exact ar
  | pi A B i s ihA ihB =>
    asimp
    exact ihB (up_Term_Term σ) ar
  | _ => exact ar.elim

/-- A variable outside the range of `ξ` stays outside the range of `upRen ξ` (shifted by one). -/
lemma not_range_up {i : Nat} {ξ : Nat → Nat} (h : ∀ x, i ≠ ξ x) :
    ∀ x, (i + 1) ≠ upRen_Term_Term ξ x
  | 0 => fun e => absurd e (Nat.succ_ne_zero i)
  | x + 1 => fun e => h x (Nat.succ.inj e)

/-- Guardedness holds for any variable outside the range of a renaming (Coq `sta_ren_guarded0`). -/
lemma ren_guarded0 {i : Nat} (m : Term) {ξ : Nat → Nat}
    (h : ∀ x, i ≠ ξ x) : Guarded i (m⟨(id : Nat → Nat); ξ⟩) := by
  induction m generalizing i ξ with
  | var_Term x => exact fun e => (h x e).elim
  | pi A B s r ihA ihB =>
    refine ⟨ihA h, ?_⟩
    have := ihB (i := i + 1) (ξ := upRen_Term_Term ξ) (not_range_up h)
    asimp at this ⊢
    exact this
  | lam A m s r ihA ihm =>
    refine ⟨ihA h, ?_⟩
    have := ihm (i := i + 1) (ξ := upRen_Term_Term ξ) (not_range_up h)
    asimp at this ⊢
    exact this
  | app m n r ihm ihn => exact ⟨ihm h, ihn h⟩
  | sig A B s r ihA ihB =>
    refine ⟨ihA h, ?_⟩
    have := ihB (i := i + 1) (ξ := upRen_Term_Term ξ) (not_range_up h)
    asimp at this ⊢
    exact this
  | pair m n s r ihm ihn => exact ⟨ihm h, ihn h⟩
  | proj A m n ihA ihm ihn =>
    refine ⟨?_, ihm h, ?_⟩
    · have := ihA (i := i + 1) (ξ := upRen_Term_Term ξ) (not_range_up h)
      asimp at this ⊢
      exact this
    · have := ihn (i := i + 2) (ξ := upRen_Term_Term (upRen_Term_Term ξ))
        (not_range_up (not_range_up h))
      asimp at this ⊢
      exact this
  | fix A m ihA ihm =>
    refine ⟨ihA h, ?_⟩
    have := ihm (i := i + 1) (ξ := upRen_Term_Term ξ) (not_range_up h)
    asimp at this ⊢
    exact this
  | ite A m n1 n2 ihA ihm ihn1 ihn2 =>
    refine ⟨?_, ihm h, ihn1 h, ihn2 h⟩
    have := ihA (i := i + 1) (ξ := upRen_Term_Term ξ) (not_range_up h)
    asimp at this ⊢
    exact this
  | M A ihA => exact ihA h
  | pure m ihm => exact ihm h
  | mlet m n ihm ihn =>
    refine ⟨ihm h, ?_⟩
    have := ihn (i := i + 1) (ξ := upRen_Term_Term ξ) (not_range_up h)
    asimp at this ⊢
    exact this
  | act b A B r ihA ihB => exact ihA h
  | ch b A ihA => exact ihA h
  | fork A m ihA ihm =>
    refine ⟨ihA h, ?_⟩
    have := ihm (i := i + 1) (ξ := upRen_Term_Term ξ) (not_range_up h)
    asimp at this ⊢
    exact this
  | recv m r ihm => exact ihm h
  | send m r ihm => exact ihm h
  | close b m ihm => exact ihm h
  | srt => trivial
  | unit => trivial
  | one => trivial
  | bool => trivial
  | tt => trivial
  | ff => trivial
  | proto => trivial
  | stop => trivial
  | chan c => trivial
  | box => trivial

/-- A substitution that guards `j` away from the image of `i` lifts under one binder. -/
lemma up_guarded {i j : Nat} {σ : Nat → Term} (h : ∀ x, i ≠ x → Guarded j (σ x)) :
    ∀ x, (i + 1) ≠ x → Guarded (j + 1) (up_Term_Term σ x)
  | 0, _ => Nat.succ_ne_zero j
  | x + 1, neq =>
    ren_guarded (fun _ _ e => Nat.succ.inj e) (h x (fun e => neq (congrArg Nat.succ e)))

/-- Guardedness is preserved by substitution (Coq `sta_subst_guarded`). -/
lemma subst_guarded {i j : Nat} {m : Term} {σ : Nat → Term}
    (h : ∀ x, i ≠ x → Guarded j (σ x)) (gr : Guarded i m) :
    Guarded j (m[Chan.var_Chan; σ]) := by
  induction m generalizing i j σ with
  | var_Term x => exact h x gr
  | pi A B s r ihA ihB =>
    obtain ⟨gA, gB⟩ := gr
    exact ⟨ihA h gA, ihB (i := i + 1) (j := j + 1) (up_guarded h) gB⟩
  | lam A m s r ihA ihm =>
    obtain ⟨gA, gm⟩ := gr
    exact ⟨ihA h gA, ihm (i := i + 1) (j := j + 1) (up_guarded h) gm⟩
  | app m n r ihm ihn =>
    obtain ⟨gm, gn⟩ := gr
    exact ⟨ihm h gm, ihn h gn⟩
  | sig A B s r ihA ihB =>
    obtain ⟨gA, gB⟩ := gr
    exact ⟨ihA h gA, ihB (i := i + 1) (j := j + 1) (up_guarded h) gB⟩
  | pair m n s r ihm ihn =>
    obtain ⟨gm, gn⟩ := gr
    exact ⟨ihm h gm, ihn h gn⟩
  | proj A m n ihA ihm ihn =>
    obtain ⟨gA, gm, gn⟩ := gr
    exact ⟨ihA (i := i + 1) (j := j + 1) (up_guarded h) gA, ihm h gm,
      ihn (i := i + 2) (j := j + 2) (up_guarded (up_guarded h)) gn⟩
  | fix A m ihA ihm =>
    obtain ⟨gA, gm⟩ := gr
    exact ⟨ihA h gA, ihm (i := i + 1) (j := j + 1) (up_guarded h) gm⟩
  | ite A m n1 n2 ihA ihm ihn1 ihn2 =>
    obtain ⟨gA, gm, gn1, gn2⟩ := gr
    exact ⟨ihA (i := i + 1) (j := j + 1) (up_guarded h) gA, ihm h gm, ihn1 h gn1, ihn2 h gn2⟩
  | M A ihA => exact ihA h gr
  | pure m ihm => exact ihm h gr
  | mlet m n ihm ihn =>
    obtain ⟨gm, gn⟩ := gr
    exact ⟨ihm h gm, ihn (i := i + 1) (j := j + 1) (up_guarded h) gn⟩
  | act b A B r ihA ihB => exact ihA h gr
  | ch b A ihA => exact ihA h gr
  | fork A m ihA ihm =>
    obtain ⟨gA, gm⟩ := gr
    exact ⟨ihA h gA, ihm (i := i + 1) (j := j + 1) (up_guarded h) gm⟩
  | recv m r ihm => exact ihm h gr
  | send m r ihm => exact ihm h gr
  | close b m ihm => exact ihm h gr
  | srt => trivial
  | unit => trivial
  | one => trivial
  | bool => trivial
  | tt => trivial
  | ff => trivial
  | proto => trivial
  | stop => trivial
  | chan c => trivial
  | box => trivial

/-- Substitution preserves typing (Coq `sta_substitution`). -/
lemma Typed.substitution {Γ2 m A} (tym : Γ2 ⊢ m : A) :
    ∀ {Γ1 σ}, Γ1 ⊢ σ ⊣ Γ2 → Γ1 ⊢ m[Chan.var_Chan; σ] : A[Chan.var_Chan; σ] := by
  induction tym using Typed.rec
    (motive_2 := fun Γ2 _ => ∀ {Γ1 σ}, Γ1 ⊢ σ ⊣ Γ2 → Wf Γ1) with
  | srt _ ih =>
    intro Γ1 σ agr; asimp; exact .srt (ih agr)
  | var wf hs ih =>
    intro Γ1 σ agr
    asimp
    exact AgreeSubst.has agr (ih agr) hs
  | @pi Γ A B i s r t tyA tyB ihA ihB =>
    intro Γ1 σ agr
    asimp
    exact .pi (ihA agr) (ihB (.ty agr tyA))
  | @lam Γ A B m i s tym ihm =>
    intro Γ1 σ agr
    asimp
    cases tym.wf with
    | @cons _ _ s' _ tyA => exact .lam (ihm (.ty agr tyA))
  | @app Γ A B m n i s tym tyn ihm ihn =>
    intro Γ1 σ agr
    rw [show (B[Chan.var_Chan; n..])[Chan.var_Chan; σ]
          = (B[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (n[Chan.var_Chan; σ])..]
          from by asimp]
    exact .app (ihm agr) (ihn agr)
  | @sig Γ A B i s r t ord1 ord2 tyA tyB ihA ihB =>
    intro Γ1 σ agr
    asimp
    exact .sig ord1 ord2 (ihA agr) (ihB (.ty agr tyA))
  | @pair Γ A B m n i t tyS tym tyn ihS ihm ihn =>
    intro Γ1 σ agr
    have ihn' := ihn agr
    rw [show (B[Chan.var_Chan; m..])[Chan.var_Chan; σ]
          = (B[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m[Chan.var_Chan; σ])..]
          from by asimp] at ihn'
    exact .pair (ihS agr) (ihm agr) ihn'
  | @proj Γ A B C m n i s t tyC tym tyn ihC ihm ihn =>
    intro Γ1 σ agr
    rw [show (C[Chan.var_Chan; m..])[Chan.var_Chan; σ]
          = (C[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m[Chan.var_Chan; σ])..]
          from by asimp]
    cases tyC.wf with
    | @cons _ _ s' _ tyS =>
      cases tyn.wf with
      | @cons _ _ s'' wfA tyB =>
        cases wfA with
        | @cons _ _ s''' _ tyA =>
          have ihn' := ihn (.ty (.ty agr tyA) tyB)
          rw [show (C[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                  up_Term_Term (up_Term_Term σ)]
                = (C[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)]
                from by
                  asimp; congr 1; funext x
                  rcases x with _ | _ | x
                  · rfl
                  · asimp; substify
                  · asimp; substify] at ihn'
          exact .proj (ihC (.ty agr tyS)) (ihm agr) ihn'
  | @fix Γ A m ar gr tym ihm =>
    intro Γ1 σ agr
    cases tym.wf with
    | @cons _ _ s' _ tyA =>
      have ihm' := ihm (.ty agr tyA)
      rw [show (A⟨(id : Nat → Nat); ↑⟩)[Chan.var_Chan; up_Term_Term σ]
            = (A[Chan.var_Chan; σ])⟨(id : Nat → Nat); ↑⟩ from by asimp] at ihm'
      refine .fix (subst_arity_proto σ ar) ?_ ihm'
      apply subst_guarded (i := 0) (j := 0) _ gr
      rintro (_ | x) neq
      · exact absurd rfl neq
      · exact ren_guarded0 _ (fun y e => Nat.succ_ne_zero y e.symm)
  | @ite Γ A m n1 n2 s tyA tym tyn1 tyn2 ihA ihm ihn1 ihn2 =>
    intro Γ1 σ agr
    have tyBool : Γ ⊢ Term.bool : Term.srt .U := .bool tym.wf
    have ihn1' := ihn1 agr
    have ihn2' := ihn2 agr
    rw [show (A[Chan.var_Chan; Term.tt..])[Chan.var_Chan; σ]
          = (A[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; Term.tt..] from by asimp; rfl] at ihn1'
    rw [show (A[Chan.var_Chan; Term.ff..])[Chan.var_Chan; σ]
          = (A[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; Term.ff..] from by asimp; rfl] at ihn2'
    rw [show (A[Chan.var_Chan; m..])[Chan.var_Chan; σ]
          = (A[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m[Chan.var_Chan; σ])..]
          from by asimp]
    exact .ite (ihA (.ty agr tyBool)) (ihm agr) ihn1' ihn2'
  | unit _ ih =>
    intro Γ1 σ agr; asimp; exact .unit (ih agr)
  | one _ ih =>
    intro Γ1 σ agr; asimp; exact .one (ih agr)
  | bool _ ih =>
    intro Γ1 σ agr; asimp; exact .bool (ih agr)
  | tt _ ih =>
    intro Γ1 σ agr; asimp; exact .tt (ih agr)
  | ff _ ih =>
    intro Γ1 σ agr; asimp; exact .ff (ih agr)
  | @M Γ A s tyA ihA =>
    intro Γ1 σ agr; asimp; exact .M (ihA agr)
  | @pure Γ m A tym ihm =>
    intro Γ1 σ agr; asimp; exact .pure (ihm agr)
  | @mlet Γ m n A B s tyB tym tyn ihB ihm ihn =>
    intro Γ1 σ agr
    cases tyn.wf with
    | @cons _ _ s' _ tyA =>
      have ihn' := ihn (.ty agr tyA)
      rw [show (Term.M (B⟨(id : Nat → Nat); ↑⟩))[Chan.var_Chan; up_Term_Term σ]
            = Term.M ((B[Chan.var_Chan; σ])⟨(id : Nat → Nat); ↑⟩) from by
            show Term.M _ = Term.M _; congr 1; asimp] at ihn'
      exact .mlet (ihB agr) (ihm agr) ihn'
  | @act Γ b A B i tyB ihB =>
    intro Γ1 σ agr
    asimp
    cases tyB.wf with
    | @cons _ _ s' _ tyA => exact .act (ihB (.ty agr tyA))
  | proto _ ih =>
    intro Γ1 σ agr; asimp; exact .proto (ih agr)
  | stop _ ih =>
    intro Γ1 σ agr; asimp; exact .stop (ih agr)
  | @ch Γ b A tyA ihA =>
    intro Γ1 σ agr; asimp; exact .ch (ihA agr)
  | @chan Γ b x A wf tyA ih ihA =>
    intro Γ1 σ agr
    rw [show (Term.ch b (A⟨(id : Nat → Nat); (· + Γ.length)⟩))[Chan.var_Chan; σ]
          = Term.ch b (A[Chan.var_Chan; funcomp σ (· + Γ.length)]) from by
          show Term.ch b _ = Term.ch b _
          congr 1
          asimp
          try substify,
        agr.size,
        show A[Chan.var_Chan; funcomp Term.var_Term (· + Γ1.length)]
          = A⟨(id : Nat → Nat); (· + Γ1.length)⟩ from
          (rinst_inst_Term id (· + Γ1.length) Chan.var_Chan
            (funcomp Term.var_Term (· + Γ1.length)) (congrFun rfl) (congrFun rfl) A).symm]
    exact .chan (ih agr) tyA
  | @fork Γ m A tym ihm =>
    intro Γ1 σ agr
    asimp
    cases tym.wf with
    | @cons _ _ s' _ tyCh => exact .fork (ihm (.ty agr tyCh))
  | @recv Γ r1 r2 A B m i e tym ihm =>
    intro Γ1 σ agr; asimp; exact .recv e (ihm agr)
  | @send Γ r1 r2 A B m i e tym ihm =>
    intro Γ1 σ agr; asimp; exact .send e (ihm agr)
  | @close Γ b m tym ihm =>
    intro Γ1 σ agr; asimp; exact .close (ihm agr)
  | @conv Γ A B m s eq tym tyB ihm ihB =>
    intro Γ1 σ agr
    exact .conv (conv_subst σ eq) (ihm agr) (ihB agr)
  | nil =>
    rename_i agr; exact agr.wf_nil
  | @cons Γ A s wf tyA ih ihA =>
    rename_i agr
    exact AgreeSubst.wf_cons agr wf (fun a => ih a) (fun a => ihA a)

/-- Single-point substitution preserves typing (Coq `sta_subst`). -/
lemma Typed.subst {Γ m n A B}
    (tym : (A :: Γ) ⊢ m : B) (tyn : Γ ⊢ n : A) :
    Γ ⊢ m[Chan.var_Chan; n..] : B[Chan.var_Chan; n..] := by
  apply tym.substitution
  apply AgreeSubst.wk1 (AgreeSubst.refl tyn.wf)
  asimp
  exact tyn

/-- Single-point substitution up to equality (Coq `sta_esubst`). -/
lemma Typed.esubst {Γ m m' n A B B'}
    (em : m' = m[Chan.var_Chan; n..])
    (eB : B' = B[Chan.var_Chan; n..])
    (tym : (A :: Γ) ⊢ m : B) (tyn : Γ ⊢ n : A) :
    Γ ⊢ m' : B' := by
  subst em; subst eB
  exact tym.subst tyn

/-- Context conversion of the topmost hypothesis (Coq `sta_ctx_conv`). -/
lemma Typed.ctx_conv {Γ m A B C s}
    (eq : B ≃ A) (tyB : Γ ⊢ B : .srt s) (tym : (A :: Γ) ⊢ m : C) :
    (B :: Γ) ⊢ m : C := by
  have wf := tym.wf
  cases wf with
  | @cons _ _ s' wf tyA =>
    have h : (B :: Γ) ⊢ m[Chan.var_Chan; Term.var_Term] : C[Chan.var_Chan; Term.var_Term] := by
      apply tym.substitution
      apply AgreeSubst.conv eq ?_ tyA (AgreeSubst.refl (.cons wf tyB))
      exact Typed.eweaken (congrFun instId_Term (A⟨(id : Nat → Nat); ↑⟩)) rfl tyA tyB
    asimp at h
    exact h

end TLLC.Static
