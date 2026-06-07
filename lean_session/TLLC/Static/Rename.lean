import TLLC.Static.Typing

/-!
# Static renaming

Port of `coq_session/sta_weak.v`: the renaming-agreement relation `AgreeRen` (Coq
`sta_agree_ren`), its structural lemmas, the renaming-preservation metatheorem `rename` (Coq
`sta_rename`, a mutual induction over `Typed`/`Wf`), and the weakening corollaries `weaken`/`eweaken`
(Coq `sta_weaken`/`sta_eweaken`).
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Renaming agreement between two contexts (Coq `sta_agree_ren`). -/
inductive AgreeRen : (Nat → Nat) → Ctx → Ctx → Prop where
  | nil :
    AgreeRen (id : Nat → Nat) ([] : Ctx) ([] : Ctx)
  | cons {Γ Γ' ξ m s} :
    Γ ⊢ m : .srt s →
    AgreeRen ξ Γ Γ' →
    AgreeRen (upRen_Term_Term ξ) (m :: Γ) (m⟨(id : Nat → Nat); ξ⟩ :: Γ')
  | wk {Γ Γ' ξ m s} :
    Γ' ⊢ m : .srt s →
    AgreeRen ξ Γ Γ' →
    AgreeRen (funcomp Nat.succ ξ) Γ (m :: Γ')

/-- A renaming witnessed by an agreement is injective (Coq `sta_agree_ren_injective`). -/
lemma AgreeRen.injective {Γ Γ' x y ξ} (agr : AgreeRen ξ Γ Γ') (e : ξ x = ξ y) : x = y := by
  induction agr generalizing x y with
  | nil => exact e
  | cons _ _ ih =>
    cases x <;> cases y <;> asimp at e <;>
      (try simp only [funcomp, var_zero, shift] at e)
    · rfl
    · exact (Nat.succ_ne_zero _ e.symm).elim
    · exact (Nat.succ_ne_zero _ e).elim
    · rw [ih (Nat.succ.inj e)]
  | wk _ _ ih =>
    apply ih
    exact Nat.succ.inj e

/-- The identity renaming agrees a well-formed context with itself (Coq `sta_agree_ren_refl`). -/
lemma AgreeRen.refl : ∀ {Γ}, Wf Γ → AgreeRen (id : Nat → Nat) Γ Γ
  | _, .nil => .nil
  | _, @Wf.cons Γ A s wf tyA => by
    have ih := AgreeRen.refl wf
    have h := AgreeRen.cons tyA ih
    rw [show A⟨(id : Nat → Nat); (id : Nat → Nat)⟩ = A from by asimp,
        show upRen_Term_Term (id : Nat → Nat) = (id : Nat → Nat) from by asimp] at h
    exact h

/-- Renaming agreement transports context lookups (Coq `sta_agree_ren_has`). -/
lemma AgreeRen.has {Γ Γ' ξ x A} (agr : AgreeRen ξ Γ Γ') (hs : Has Γ x A) :
    Has Γ' (ξ x) (A⟨(id : Nat → Nat); ξ⟩) := by
  induction agr generalizing x A with
  | nil => cases hs
  | @cons Γ Γ' ξ m s tym agr ih =>
    cases hs with
    | zero =>
      rw [show (m⟨(id : Nat → Nat); ↑⟩)⟨(id : Nat → Nat); upRen_Term_Term ξ⟩
            = (m⟨(id : Nat → Nat); ξ⟩)⟨(id : Nat → Nat); ↑⟩ from by asimp]
      exact Has.zero
    | @succ Γ A B x hs =>
      rw [show (A⟨(id : Nat → Nat); ↑⟩)⟨(id : Nat → Nat); upRen_Term_Term ξ⟩
            = (A⟨(id : Nat → Nat); ξ⟩)⟨(id : Nat → Nat); ↑⟩ from by asimp]
      exact Has.succ (ih hs)
  | @wk Γ Γ' ξ m s tym agr ih =>
    have hs' := ih hs
    rw [show A⟨(id : Nat → Nat); funcomp Nat.succ ξ⟩
          = (A⟨(id : Nat → Nat); ξ⟩)⟨(id : Nat → Nat); ↑⟩ from by asimp]
    exact Has.succ hs'

/-- An agreement from the empty context produces a well-formed target (Coq `sta_agree_weak_nil_wf`). -/
lemma AgreeRen.weak_nil_wf {Γ' ξ} (agr : AgreeRen ξ ([] : Ctx) Γ') : Wf Γ' := by
  generalize e : ([] : Ctx) = Γ at agr
  induction agr with
  | nil => exact .nil
  | cons _ _ _ => cases e
  | @wk Γ Γ' ξ m s tym agr ih => exact .cons (ih e) tym

/-- A well-formed context agrees with the empty context (Coq `sta_agree_weak_wf_nil`). -/
lemma AgreeRen.weak_wf_nil : ∀ {Γ'}, Wf Γ' → AgreeRen (· + Γ'.length) ([] : Ctx) Γ'
  | _, .nil => .nil
  | _, @Wf.cons Γ A s wf tyA => by
    have ih := AgreeRen.weak_wf_nil wf
    have h := AgreeRen.wk tyA ih
    rw [show funcomp Nat.succ (· + Γ.length) = (fun x => x + (A :: Γ).length) from by
          funext x; simp only [funcomp, List.length_cons]; omega] at h
    exact h

/-- Extending the source of an agreement keeps the target well-formed (Coq `sta_agree_weak_wf_cons`). -/
lemma AgreeRen.weak_wf_cons {Γ Γ' A s ξ}
    (agr : AgreeRen ξ (A :: Γ) Γ') (_wf : Wf Γ)
    (h1 : ∀ {Γ' ξ}, AgreeRen ξ Γ Γ' → Wf Γ')
    (h2 : ∀ {Γ' ξ}, AgreeRen ξ Γ Γ' → Γ' ⊢ A⟨(id : Nat → Nat); ξ⟩ : .srt s) :
    Wf Γ' := by
  generalize e : (A :: Γ) = Γ0 at agr
  induction agr generalizing A with
  | nil => cases e
  | @cons Γ1 Γ' ξ m s tym agr _ =>
    cases e
    exact .cons (h1 agr) (h2 agr)
  | @wk Γ1 Γ' ξ m s tym agr ih =>
    exact .cons (ih h2 e) tym

/-- The size shift relating the two contexts (Coq `sta_agree_ren_size`). -/
lemma AgreeRen.size {ξ Γ Γ'} (agr : AgreeRen ξ Γ Γ') :
    funcomp ξ (· + Γ.length) = (· + Γ'.length) := by
  induction agr with
  | nil => rfl
  | @cons Γ Γ' ξ m s tym agr ih =>
    funext x
    have h := congrFun ih x
    simp only [funcomp, List.length_cons] at h ⊢
    have e : upRen_Term_Term ξ (x + (Γ.length + 1)) = ξ (x + Γ.length) + 1 := by
      rw [show x + (Γ.length + 1) = (x + Γ.length) + 1 from by omega]; rfl
    rw [e, h]; omega
  | @wk Γ Γ' ξ m s tym agr ih =>
    funext x
    have h := congrFun ih x
    simp only [funcomp, List.length_cons] at h ⊢
    omega

/-- A well-formed context agrees with the empty context via its size (Coq `sta_wf_agree_ren`). -/
lemma Wf.agreeRen {Γ} (wf : Wf Γ) : AgreeRen (· + Γ.length) ([] : Ctx) Γ :=
  AgreeRen.weak_wf_nil wf

/-- Protocol arity is preserved by renaming (Coq `sta_ren_arity_proto`). -/
lemma ren_arity_proto {A : Term} (ξ : Nat → Nat) (ar : ArityProto A) :
    ArityProto (A⟨(id : Nat → Nat); ξ⟩) := by
  induction A generalizing ξ with
  | proto => exact ar
  | pi A B i s ihA ihB =>
    asimp
    exact ihB (upRen_Term_Term ξ) ar
  | _ => exact ar.elim

/-- Lifting an injective renaming stays injective (Coq `ren_upren_injective`). -/
lemma ren_upren_injective {ξ : Nat → Nat}
    (h : ∀ x y, ξ x = ξ y → x = y) :
    ∀ x y, (upRen_Term_Term ξ) x = (upRen_Term_Term ξ) y → x = y := by
  intro x y e
  cases x <;> cases y <;> asimp at e <;>
    (try simp only [funcomp, var_zero, shift] at e)
  · rfl
  · exact (Nat.succ_ne_zero _ e.symm).elim
  · exact (Nat.succ_ne_zero _ e).elim
  · rw [h _ _ (Nat.succ.inj e)]

/-- Guardedness is preserved by injective renaming (Coq `sta_ren_guarded`). -/
lemma ren_guarded {i : Nat} {m : Term} {ξ : Nat → Nat}
    (h : ∀ x y, ξ x = ξ y → x = y) (gr : Guarded i m) :
    Guarded (ξ i) (m⟨(id : Nat → Nat); ξ⟩) := by
  induction m generalizing i ξ with
  | var_Term x =>
    intro e
    exact gr (h _ _ e)
  | pi A B s r ihA ihB =>
    obtain ⟨gA, gB⟩ := gr
    refine ⟨ihA h gA, ?_⟩
    have := ihB (ξ := upRen_Term_Term ξ) (ren_upren_injective h) gB
    asimp at this ⊢
    exact this
  | lam A m s r ihA ihm =>
    obtain ⟨gA, gm⟩ := gr
    refine ⟨ihA h gA, ?_⟩
    have := ihm (ξ := upRen_Term_Term ξ) (ren_upren_injective h) gm
    asimp at this ⊢
    exact this
  | app m n r ihm ihn =>
    obtain ⟨gm, gn⟩ := gr
    exact ⟨ihm h gm, ihn h gn⟩
  | sig A B s r ihA ihB =>
    obtain ⟨gA, gB⟩ := gr
    refine ⟨ihA h gA, ?_⟩
    have := ihB (ξ := upRen_Term_Term ξ) (ren_upren_injective h) gB
    asimp at this ⊢
    exact this
  | pair m n s r ihm ihn =>
    obtain ⟨gm, gn⟩ := gr
    exact ⟨ihm h gm, ihn h gn⟩
  | proj A m n ihA ihm ihn =>
    obtain ⟨gA, gm, gn⟩ := gr
    refine ⟨?_, ihm h gm, ?_⟩
    · have := ihA (ξ := upRen_Term_Term ξ) (ren_upren_injective h) gA
      asimp at this ⊢
      exact this
    · have := ihn (ξ := upRen_Term_Term (upRen_Term_Term ξ))
        (ren_upren_injective (ren_upren_injective h)) gn
      asimp at this ⊢
      exact this
  | fix A m ihA ihm =>
    obtain ⟨gA, gm⟩ := gr
    refine ⟨ihA h gA, ?_⟩
    have := ihm (ξ := upRen_Term_Term ξ) (ren_upren_injective h) gm
    asimp at this ⊢
    exact this
  | ite A m n1 n2 ihA ihm ihn1 ihn2 =>
    obtain ⟨gA, gm, gn1, gn2⟩ := gr
    refine ⟨?_, ihm h gm, ihn1 h gn1, ihn2 h gn2⟩
    have := ihA (ξ := upRen_Term_Term ξ) (ren_upren_injective h) gA
    asimp at this ⊢
    exact this
  | M A ihA => exact ihA h gr
  | pure m ihm => exact ihm h gr
  | mlet m n ihm ihn =>
    obtain ⟨gm, gn⟩ := gr
    refine ⟨ihm h gm, ?_⟩
    have := ihn (ξ := upRen_Term_Term ξ) (ren_upren_injective h) gn
    asimp at this ⊢
    exact this
  | act b A B r ihA ihB => exact ihA h gr
  | ch b A ihA => exact ihA h gr
  | fork A m ihA ihm =>
    obtain ⟨gA, gm⟩ := gr
    refine ⟨ihA h gA, ?_⟩
    have := ihm (ξ := upRen_Term_Term ξ) (ren_upren_injective h) gm
    asimp at this ⊢
    exact this
  | recv m r ihm => exact ihm h gr
  | send m r ihm => exact ihm h gr
  | close b m ihm => exact ihm h gr
  | srt => exact gr
  | unit => exact gr
  | one => exact gr
  | bool => exact gr
  | tt => exact gr
  | ff => exact gr
  | proto => exact gr
  | stop => exact gr
  | chan c => exact gr
  | box => exact gr

/-- Conversion is closed under renaming (the renaming specialization of Coq `sta_conv_subst`). -/
lemma conv_ren {A B : Term} (ξ : Nat → Nat) (eq : A ≃ B) :
    (A⟨(id : Nat → Nat); ξ⟩) ≃ (B⟨(id : Nat → Nat); ξ⟩) := by
  have h := conv_subst (funcomp Term.var_Term ξ) eq
  have e : ∀ X : Term, X[Chan.var_Chan; funcomp Term.var_Term ξ] = X⟨(id : Nat → Nat); ξ⟩ :=
    fun X => (rinst_inst_Term id ξ Chan.var_Chan (funcomp Term.var_Term ξ)
      (congrFun rfl) (congrFun rfl) X).symm
  rw [e, e] at h
  exact h

/-- Renaming preserves typing (Coq `sta_rename`). -/
lemma Typed.rename {Γ m A} (tym : Γ ⊢ m : A) :
    ∀ {Γ' ξ}, AgreeRen ξ Γ Γ' → Γ' ⊢ m⟨(id : Nat → Nat); ξ⟩ : A⟨(id : Nat → Nat); ξ⟩ := by
  induction tym using Typed.rec
    (motive_2 := fun Γ _ => ∀ {Γ' ξ}, AgreeRen ξ Γ Γ' → Wf Γ') with
  | srt _ ih =>
    intro Γ' ξ agr; exact .srt (ih agr)
  | var _ hs ih =>
    intro Γ' ξ agr; exact .var (ih agr) (agr.has hs)
  | @pi Γ A B i s r t tyA tyB ihA ihB =>
    intro Γ' ξ agr
    exact .pi (ihA agr) (ihB (.cons tyA agr))
  | @lam Γ A B m i s tym ihm =>
    intro Γ' ξ agr
    cases tym.wf with
    | @cons _ _ s' _ tyA => exact .lam (ihm (.cons tyA agr))
  | @app Γ A B m n i s tym tyn ihm ihn =>
    intro Γ' ξ agr
    rw [show (B[Chan.var_Chan; n..])⟨(id : Nat → Nat); ξ⟩
          = (B⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (n⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp]
    exact .app (ihm agr) (ihn agr)
  | @sig Γ A B i s r t ord1 ord2 tyA tyB ihA ihB =>
    intro Γ' ξ agr
    exact .sig ord1 ord2 (ihA agr) (ihB (.cons tyA agr))
  | @pair Γ A B m n i t tyS tym tyn ihS ihm ihn =>
    intro Γ' ξ agr
    have ihn' := ihn agr
    rw [show (B[Chan.var_Chan; m..])⟨(id : Nat → Nat); ξ⟩
          = (B⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (m⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp] at ihn'
    exact .pair (ihS agr) (ihm agr) ihn'
  | @proj Γ A B C m n i s t tyC tym tyn ihC ihm ihn =>
    intro Γ' ξ agr
    cases tyC.wf with
    | @cons _ _ s' _ tyAB =>
      cases tyn.wf with
      | @cons _ _ s'' wfA tyB =>
        cases wfA with
        | @cons _ _ s''' _ tyA =>
          have ihn' := ihn (AgreeRen.cons tyB (AgreeRen.cons tyA agr))
          rw [show (C[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)])⟨(id :
                  Nat → Nat); upRen_Term_Term (upRen_Term_Term ξ)⟩
                = (C⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)]
                from by asimp; congr 1] at ihn'
          rw [show (C[Chan.var_Chan; m..])⟨(id : Nat → Nat); ξ⟩
                = (C⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (m⟨(id : Nat → Nat);
                  ξ⟩)..] from by asimp]
          exact .proj (ihC (.cons tyAB agr)) (ihm agr) ihn'
  | @fix Γ A m ar gr tym ihm =>
    intro Γ' ξ agr
    cases tym.wf with
    | @cons _ _ s' _ tyA =>
      have ihm' := ihm (.cons tyA agr)
      rw [show A⟨(id : Nat → Nat); ↑⟩⟨(id : Nat → Nat); upRen_Term_Term ξ⟩
            = A⟨(id : Nat → Nat); ξ⟩⟨(id : Nat → Nat); ↑⟩ from by asimp] at ihm'
      refine .fix (ren_arity_proto ξ ar) ?_ ihm'
      have h1 := ren_guarded (i := 0) (ren_upren_injective (fun _ _ e => agr.injective e)) gr
      asimp at h1
      exact h1
  | @ite Γ A m n1 n2 s tyA tym tyn1 tyn2 ihA ihm ihn1 ihn2 =>
    intro Γ' ξ agr
    have tyBool : Γ ⊢ Term.bool : Term.srt .U := .bool tym.wf
    have ihn1' := ihn1 agr
    have ihn2' := ihn2 agr
    rw [show (A[Chan.var_Chan; Term.tt..])⟨(id : Nat → Nat); ξ⟩
          = (A⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; Term.tt..]
          from by asimp; congr 1] at ihn1'
    rw [show (A[Chan.var_Chan; Term.ff..])⟨(id : Nat → Nat); ξ⟩
          = (A⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; Term.ff..]
          from by asimp; congr 1] at ihn2'
    rw [show (A[Chan.var_Chan; m..])⟨(id : Nat → Nat); ξ⟩
          = (A⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (m⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp]
    exact .ite (ihA (.cons tyBool agr)) (ihm agr) ihn1' ihn2'
  | unit _ ih =>
    intro Γ' ξ agr; exact .unit (ih agr)
  | one _ ih =>
    intro Γ' ξ agr; exact .one (ih agr)
  | bool _ ih =>
    intro Γ' ξ agr; exact .bool (ih agr)
  | tt _ ih =>
    intro Γ' ξ agr; exact .tt (ih agr)
  | ff _ ih =>
    intro Γ' ξ agr; exact .ff (ih agr)
  | @M Γ A s tyA ihA =>
    intro Γ' ξ agr; exact .M (ihA agr)
  | @pure Γ m A tym ihm =>
    intro Γ' ξ agr; exact .pure (ihm agr)
  | @mlet Γ m n A B s tyB tym tyn ihB ihm ihn =>
    intro Γ' ξ agr
    cases tyn.wf with
    | @cons _ _ s' _ tyA =>
      have ihn' := ihn (.cons tyA agr)
      rw [show (Term.M (B⟨(id : Nat → Nat); ↑⟩))⟨(id : Nat → Nat); upRen_Term_Term ξ⟩
            = Term.M (B⟨(id : Nat → Nat); ξ⟩⟨(id : Nat → Nat); ↑⟩) from by
            show Term.M _ = Term.M _; congr 1; asimp] at ihn'
      exact .mlet (ihB agr) (ihm agr) ihn'
  | @act Γ b A B i tyB ihB =>
    intro Γ' ξ agr
    cases tyB.wf with
    | @cons _ _ s' _ tyA => exact .act (ihB (.cons tyA agr))
  | proto _ ih =>
    intro Γ' ξ agr; exact .proto (ih agr)
  | stop _ ih =>
    intro Γ' ξ agr; exact .stop (ih agr)
  | @ch Γ b A tyA ihA =>
    intro Γ' ξ agr; exact .ch (ihA agr)
  | @chan Γ b x A wf tyA ih ihA =>
    intro Γ' ξ agr
    rw [show (Term.ch b (A⟨(id : Nat → Nat); (· + Γ.length)⟩))⟨(id : Nat → Nat); ξ⟩
          = Term.ch b (A⟨(id : Nat → Nat); funcomp ξ (· + Γ.length)⟩) from by
          show Term.ch b _ = Term.ch b _; congr 1; asimp,
        agr.size]
    exact .chan (ih agr) tyA
  | @fork Γ m A tym ihm =>
    intro Γ' ξ agr
    cases tym.wf with
    | @cons _ _ s' _ tyCh => exact .fork (ihm (.cons tyCh agr))
  | @recv Γ r1 r2 A B m i e tym ihm =>
    intro Γ' ξ agr; exact .recv e (ihm agr)
  | @send Γ r1 r2 A B m i e tym ihm =>
    intro Γ' ξ agr; exact .send e (ihm agr)
  | @close Γ b m tym ihm =>
    intro Γ' ξ agr; exact .close (ihm agr)
  | @conv Γ A B m s eq tym tyB ihm ihB =>
    intro Γ' ξ agr
    exact .conv (conv_ren ξ eq) (ihm agr) (ihB agr)
  | nil =>
    rename_i agr; exact agr.weak_nil_wf
  | @cons Γ A s wf tyA ih ihA =>
    rename_i agr
    exact AgreeRen.weak_wf_cons agr wf (fun a => ih a) (fun a => ihA a)

/-- A typed variable has a well-sorted type (Coq `sta_wf_ok`). -/
lemma Wf.ok : ∀ {Γ x A}, Wf Γ → Has Γ x A → ∃ s, Γ ⊢ A : .srt s
  | _, _, _, .nil, hs => by cases hs
  | _, _, _, @Wf.cons Γ A s wf tyA, hs => by
    cases hs with
    | zero =>
      refine ⟨s, ?_⟩
      rw [show Term.srt s = (Term.srt s)⟨(id : Nat → Nat); ↑⟩ from rfl]
      exact tyA.rename (.wk tyA (.refl wf))
    | @succ Γ A B x hs =>
      obtain ⟨t, tyA0⟩ := Wf.ok wf hs
      refine ⟨t, ?_⟩
      rw [show Term.srt t = (Term.srt t)⟨(id : Nat → Nat); ↑⟩ from rfl]
      exact tyA0.rename (.wk tyA (.refl wf))

/-- Weakening: typing is preserved under a fresh hypothesis (Coq `sta_weaken`). -/
lemma Typed.weaken {Γ m A B s} (tym : Γ ⊢ m : A) (tyB : Γ ⊢ B : .srt s) :
    (B :: Γ) ⊢ m⟨(id : Nat → Nat); ↑⟩ : A⟨(id : Nat → Nat); ↑⟩ :=
  tym.rename (.wk tyB (.refl tym.wf))

/-- Weakening up to equality of the weakened term/type (Coq `sta_eweaken`). -/
lemma Typed.eweaken {Γ m m' A A' B s}
    (em : m' = m⟨(id : Nat → Nat); ↑⟩) (eA : A' = A⟨(id : Nat → Nat); ↑⟩)
    (tym : Γ ⊢ m : A) (tyB : Γ ⊢ B : .srt s) :
    (B :: Γ) ⊢ m' : A' := by
  subst em; subst eA
  exact tym.weaken tyB

end TLLC.Static
