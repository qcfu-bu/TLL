import TLLC.Dynamic.Validity

/-!
# Dynamic renaming

Port of `coq_session/dyn_weak.v`: the dynamic renaming-agreement relation `AgreeRen`
(Coq `dyn_agree_ren`), which threads BOTH a static context pair `(Γ, Γ')` and a dynamic
(linear) context pair `(Δ, Δ')`; its structural lemmas; the renaming-preservation metatheorem
`Typed.rename` (Coq `dyn_rename`); and the weakening corollaries `weakenU`/`weakenN`/`eweakenU`/
`eweakenN` (Coq `dyn_weakenU`/`dyn_weakenN`/`dyn_eweakenU`/`dyn_eweakenN`).

Coq proves `dyn_rename` through the mutual recursor `dyn_type_mut` with a motive for `dyn_wf`.
Because here `Wf` is standalone (see `Typing.lean`), the well-formedness preservation
(Coq `dyn_rename_wf`) is a separate lemma `Wf.rename`, proved first; `Typed.rename` is then a plain
induction over the `Typed` cases.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- Dynamic renaming agreement between two static/linear context pairs (Coq `dyn_agree_ren`). -/
inductive AgreeRen : (Nat → Nat) → Static.Ctx → Ctx → Static.Ctx → Ctx → Prop where
  | nil :
    AgreeRen (id : Nat → Nat) ([] : Static.Ctx) ([] : Ctx) ([] : Static.Ctx) ([] : Ctx)
  | cons {Γ Γ' Δ Δ' ξ m s} :
    Γ ⊢ m : .srt s →
    AgreeRen ξ Γ Δ Γ' Δ' →
    AgreeRen (upRen_Term_Term ξ)
      (m :: Γ) (m :⟨s⟩ Δ) (m⟨(id : Nat → Nat); ξ⟩ :: Γ') (m⟨(id : Nat → Nat); ξ⟩ :⟨s⟩ Δ')
  | null {Γ Γ' Δ Δ' ξ m s} :
    Γ ⊢ m : .srt s →
    AgreeRen ξ Γ Δ Γ' Δ' →
    AgreeRen (upRen_Term_Term ξ)
      (m :: Γ) (none :: Δ) (m⟨(id : Nat → Nat); ξ⟩ :: Γ') (none :: Δ')
  | wkU {Γ Γ' Δ Δ' ξ m} :
    Γ' ⊢ m : .srt Srt.U →
    AgreeRen ξ Γ Δ Γ' Δ' →
    AgreeRen (funcomp Nat.succ ξ) Γ Δ (m :: Γ') (m :U Δ')
  | wkN {Γ Γ' Δ Δ' ξ m s} :
    Γ' ⊢ m : .srt s →
    AgreeRen ξ Γ Δ Γ' Δ' →
    AgreeRen (funcomp Nat.succ ξ) Γ Δ (m :: Γ') (none :: Δ')

/-- The static projection of a dynamic agreement (Coq `dyn_sta_agree_ren`). -/
lemma AgreeRen.toStatic {Γ Γ' Δ Δ' ξ} (agr : AgreeRen ξ Γ Δ Γ' Δ') :
    Static.AgreeRen ξ Γ Γ' := by
  induction agr with
  | nil => exact .nil
  | cons tym _ ih => exact .cons tym ih
  | null tym _ ih => exact .cons tym ih
  | wkU tym _ ih => exact .wk tym ih
  | wkN tym _ ih => exact .wk tym ih

/-- A well-formed pure context agrees with the empty pair via its size (Coq `dyn_wf_agree_ren`). -/
lemma Wf.agreeRen {Γ Δ} (wf : Wf Γ Δ) (k : Δ ▷ Srt.U) :
    AgreeRen (· + Γ.length) ([] : Static.Ctx) ([] : Ctx) Γ Δ := by
  induction wf with
  | nil => exact .nil
  | @cons Γ Δ A s wf tyA ih =>
    cases k with
    | U _ k' =>
      have h := AgreeRen.wkU tyA (ih k')
      rw [show funcomp Nat.succ (· + Γ.length) = (fun x => x + (A :: Γ).length) from by
            funext x; simp only [funcomp, List.length_cons]; omega] at h
      exact h
  | @null Γ Δ A s wf tyA ih =>
    cases k with
    | null k' =>
      have h := AgreeRen.wkN tyA (ih k')
      rw [show funcomp Nat.succ (· + Γ.length) = (fun x => x + (A :: Γ).length) from by
            funext x; simp only [funcomp, List.length_cons]; omega] at h
      exact h

/-- The identity renaming agrees a well-formed pair with itself (Coq `dyn_agree_ren_refl`). -/
lemma AgreeRen.refl : ∀ {Γ Δ}, Wf Γ Δ → AgreeRen (id : Nat → Nat) Γ Δ Γ Δ
  | _, _, .nil => .nil
  | _, _, @Wf.cons Γ Δ A s wf tyA => by
    have ih := AgreeRen.refl wf
    have h := AgreeRen.cons tyA ih
    rw [show A⟨(id : Nat → Nat); (id : Nat → Nat)⟩ = A from by asimp,
        show upRen_Term_Term (id : Nat → Nat) = (id : Nat → Nat) from by asimp] at h
    exact h
  | _, _, @Wf.null Γ Δ A s wf tyA => by
    have ih := AgreeRen.refl wf
    have h := AgreeRen.null tyA ih
    rw [show A⟨(id : Nat → Nat); (id : Nat → Nat)⟩ = A from by asimp,
        show upRen_Term_Term (id : Nat → Nat) = (id : Nat → Nat) from by asimp] at h
    exact h

/-- Renaming agreement transports keys (Coq `dyn_agree_ren_key`). -/
lemma AgreeRen.key {Γ Γ' Δ Δ' ξ s} (agr : AgreeRen ξ Γ Δ Γ' Δ') (k : Δ ▷ s) : Δ' ▷ s := by
  induction agr generalizing s with
  | nil => exact k
  | @cons Γ Γ' Δ Δ' ξ m s tym agr ih =>
    cases k with
    | U _ k' => exact .U _ (ih k')
    | L _ k' => exact .L _ (ih k')
  | @null Γ Γ' Δ Δ' ξ m s tym agr ih =>
    cases k with
    | null k' => exact .null (ih k')
  | @wkU Γ Γ' Δ Δ' ξ m tym agr ih =>
    cases s with
    | U => exact .U _ (ih k)
    | L => exact .L _ (ih k)
  | @wkN Γ Γ' Δ Δ' ξ m s tym agr ih => exact .null (ih k)

/-- Renaming agreement transports linear lookups (Coq `dyn_agree_ren_has`). -/
lemma AgreeRen.has {Γ Γ' Δ Δ' ξ x s A} (agr : AgreeRen ξ Γ Δ Γ' Δ') (hs : Has Δ x s A) :
    Has Δ' (ξ x) s (A⟨(id : Nat → Nat); ξ⟩) := by
  induction agr generalizing x s A with
  | nil => cases hs
  | @cons Γ Γ' Δ Δ' ξ m s tym agr ih =>
    cases hs with
    | @zero _ _ _ k =>
      rw [show (m⟨(id : Nat → Nat); ↑⟩)⟨(id : Nat → Nat); upRen_Term_Term ξ⟩
            = (m⟨(id : Nat → Nat); ξ⟩)⟨(id : Nat → Nat); ↑⟩ from by asimp]
      exact Has.zero (agr.key k)
    | @succ _ A _ _ _ hs =>
      rw [show (A⟨(id : Nat → Nat); ↑⟩)⟨(id : Nat → Nat); upRen_Term_Term ξ⟩
            = (A⟨(id : Nat → Nat); ξ⟩)⟨(id : Nat → Nat); ↑⟩ from by asimp]
      exact Has.succ (ih hs)
  | @null Γ Γ' Δ Δ' ξ m s tym agr ih =>
    cases hs with
    | @null _ A _ _ hs =>
      rw [show (A⟨(id : Nat → Nat); ↑⟩)⟨(id : Nat → Nat); upRen_Term_Term ξ⟩
            = (A⟨(id : Nat → Nat); ξ⟩)⟨(id : Nat → Nat); ↑⟩ from by asimp]
      exact Has.null (ih hs)
  | @wkU Γ Γ' Δ Δ' ξ m tym agr ih =>
    have hs' := ih hs
    rw [show A⟨(id : Nat → Nat); funcomp Nat.succ ξ⟩
          = (A⟨(id : Nat → Nat); ξ⟩)⟨(id : Nat → Nat); ↑⟩ from by asimp]
    exact Has.succ hs'
  | @wkN Γ Γ' Δ Δ' ξ m s tym agr ih =>
    have hs' := ih hs
    rw [show A⟨(id : Nat → Nat); funcomp Nat.succ ξ⟩
          = (A⟨(id : Nat → Nat); ξ⟩)⟨(id : Nat → Nat); ↑⟩ from by asimp]
    exact Has.null hs'

/-- Renaming agreement is compatible with merge (Coq `dyn_agree_ren_merge`). -/
lemma AgreeRen.merge {Γ Γ' Δ Δ' ξ} (agr : AgreeRen ξ Γ Δ Γ' Δ') :
    ∀ {Δ1 Δ2}, Merge Δ1 Δ2 Δ →
    ∃ Δ1' Δ2', Merge Δ1' Δ2' Δ' ∧ AgreeRen ξ Γ Δ1 Γ' Δ1' ∧ AgreeRen ξ Γ Δ2 Γ' Δ2' := by
  induction agr with
  | nil =>
    intro _ _ mrg; cases mrg
    exact ⟨[], [], .nil, .nil, .nil⟩
  | @cons Γ Γ' Δ Δ' ξ m s tym agr ih =>
    intro _ _ mrg
    cases mrg with
    | left _ mrg' =>
      obtain ⟨Δ1', Δ2', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨m⟨(id : Nat → Nat); ξ⟩ :U Δ1', m⟨(id : Nat → Nat); ξ⟩ :U Δ2',
        .left _ mrg', .cons tym agr1, .cons tym agr2⟩
    | right1 _ mrg' =>
      obtain ⟨Δ1', Δ2', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨m⟨(id : Nat → Nat); ξ⟩ :L Δ1', none :: Δ2',
        .right1 _ mrg', .cons tym agr1, .null tym agr2⟩
    | right2 _ mrg' =>
      obtain ⟨Δ1', Δ2', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨none :: Δ1', m⟨(id : Nat → Nat); ξ⟩ :L Δ2',
        .right2 _ mrg', .null tym agr1, .cons tym agr2⟩
  | @null Γ Γ' Δ Δ' ξ m s tym agr ih =>
    intro _ _ mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Δ1', Δ2', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨none :: Δ1', none :: Δ2', .null mrg', .null tym agr1, .null tym agr2⟩
  | @wkU Γ Γ' Δ Δ' ξ m tym agr ih =>
    intro _ _ mrg
    obtain ⟨Δ1', Δ2', mrg', agr1, agr2⟩ := ih mrg
    exact ⟨m :U Δ1', m :U Δ2', .left _ mrg', .wkU tym agr1, .wkU tym agr2⟩
  | @wkN Γ Γ' Δ Δ' ξ m s tym agr ih =>
    intro _ _ mrg
    obtain ⟨Δ1', Δ2', mrg', agr1, agr2⟩ := ih mrg
    exact ⟨none :: Δ1', none :: Δ2', .null mrg', .wkN tym agr1, .wkN tym agr2⟩

/-- An agreement from the empty pair produces a well-formed target (Coq `dyn_agree_weak_wf_nil`). -/
lemma AgreeRen.weak_wf_nil {Γ' Δ' ξ} (agr : AgreeRen ξ ([] : Static.Ctx) ([] : Ctx) Γ' Δ') :
    Wf Γ' Δ' := by
  generalize e1 : ([] : Static.Ctx) = Γ at agr
  generalize e2 : ([] : Ctx) = Δ at agr
  induction agr with
  | nil => exact .nil
  | cons _ _ _ => cases e1
  | null _ _ _ => cases e1
  | @wkU Γ Γ' Δ Δ' ξ m tym agr ih => exact .cons (ih e1 e2) tym
  | @wkN Γ Γ' Δ Δ' ξ m s tym agr ih => exact .null (ih e1 e2) tym

/-- Extending the source by a real slot keeps the target well-formed (Coq `dyn_agree_weak_wf_ty`). -/
lemma AgreeRen.weak_wf_ty {Γ Γ' Δ Δ' A s ξ}
    (agr : AgreeRen ξ (A :: Γ) (A :⟨s⟩ Δ) Γ' Δ') (_wf : Wf Γ Δ)
    (ih0 : ∀ {Γ' Δ' ξ}, AgreeRen ξ Γ Δ Γ' Δ' → Wf Γ' Δ') :
    Wf Γ' Δ' := by
  generalize e1 : (A :: Γ) = Γ0 at agr
  generalize e2 : (A :⟨s⟩ Δ) = Δ0 at agr
  induction agr with
  | nil => cases e1
  | @cons Γ1 Γ' Δ1 Δ' ξ m s' tym agr _ =>
    cases e1; cases e2
    refine .cons (ih0 agr) ?_
    have h := Static.Typed.rename tym agr.toStatic
    exact h
  | @null Γ1 Γ' Δ1 Δ' ξ m s' tym agr _ => cases e2
  | @wkU Γ1 Γ' Δ1 Δ' ξ m tym agr ih =>
    exact .cons (ih e1 e2) tym
  | @wkN Γ1 Γ' Δ1 Δ' ξ m s' tym agr ih =>
    exact .null (ih e1 e2) tym

/-- Extending the source by a null slot keeps the target well-formed (Coq `dyn_agree_weak_wf_n`). -/
lemma AgreeRen.weak_wf_n {Γ Γ' Δ Δ' A ξ}
    (agr : AgreeRen ξ (A :: Γ) (none :: Δ) Γ' Δ') (_wf : Wf Γ Δ)
    (ih0 : ∀ {Γ' Δ' ξ}, AgreeRen ξ Γ Δ Γ' Δ' → Wf Γ' Δ') :
    Wf Γ' Δ' := by
  generalize e1 : (A :: Γ) = Γ0 at agr
  generalize e2 : (none :: Δ) = Δ0 at agr
  induction agr with
  | nil => cases e1
  | @cons Γ1 Γ' Δ1 Δ' ξ m s' tym agr _ => cases e2
  | @null Γ1 Γ' Δ1 Δ' ξ m s' tym agr _ =>
    cases e1; cases e2
    have h := Static.Typed.rename tym agr.toStatic
    asimp at h
    exact .null (ih0 agr) h
  | @wkU Γ1 Γ' Δ1 Δ' ξ m tym agr ih =>
    exact .cons (ih e1 e2) tym
  | @wkN Γ1 Γ' Δ1 Δ' ξ m s' tym agr ih =>
    exact .null (ih e1 e2) tym

/-- The size shift relating the two static contexts (Coq `dyn_agree_ren_size`). -/
lemma AgreeRen.size {ξ Γ Γ' Δ Δ'} (agr : AgreeRen ξ Γ Δ Γ' Δ') :
    funcomp ξ (· + Γ.length) = (· + Γ'.length) := by
  induction agr with
  | nil => rfl
  | @cons Γ Γ' Δ Δ' ξ m s tym agr ih =>
    funext x
    have h := congrFun ih x
    simp only [funcomp, List.length_cons] at h ⊢
    have e : upRen_Term_Term ξ (x + (Γ.length + 1)) = ξ (x + Γ.length) + 1 := by
      rw [show x + (Γ.length + 1) = (x + Γ.length) + 1 from by omega]; rfl
    rw [e, h]; omega
  | @null Γ Γ' Δ Δ' ξ m s tym agr ih =>
    funext x
    have h := congrFun ih x
    simp only [funcomp, List.length_cons] at h ⊢
    have e : upRen_Term_Term ξ (x + (Γ.length + 1)) = ξ (x + Γ.length) + 1 := by
      rw [show x + (Γ.length + 1) = (x + Γ.length) + 1 from by omega]; rfl
    rw [e, h]; omega
  | @wkU Γ Γ' Δ Δ' ξ m tym agr ih =>
    funext x
    have h := congrFun ih x
    simp only [funcomp, List.length_cons] at h ⊢
    omega
  | @wkN Γ Γ' Δ Δ' ξ m s tym agr ih =>
    funext x
    have h := congrFun ih x
    simp only [funcomp, List.length_cons] at h ⊢
    omega

/-- Renaming preserves dynamic well-formedness (Coq `dyn_rename_wf`). -/
lemma Wf.rename {Γ Δ} (wf : Wf Γ Δ) :
    ∀ {Γ' Δ' ξ}, AgreeRen ξ Γ Δ Γ' Δ' → Wf Γ' Δ' := by
  induction wf with
  | nil => intro _ _ _ agr; exact agr.weak_wf_nil
  | @cons Γ Δ A s wf tyA ih => intro _ _ _ agr; exact agr.weak_wf_ty wf (fun a => ih a)
  | @null Γ Δ A s wf tyA ih => intro _ _ _ agr; exact agr.weak_wf_n wf (fun a => ih a)

/-- Renaming preserves dynamic typing (Coq `dyn_rename`). -/
lemma Typed.rename {Θ Γ Δ m A} (tym : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    ∀ {Γ' Δ' ξ}, AgreeRen ξ Γ Δ Γ' Δ' →
      Θ ⨾ Γ' ⨾ Δ' ⊢ m⟨(id : Nat → Nat); ξ⟩ : A⟨(id : Nat → Nat); ξ⟩ := by
  induction tym with
  | @var Θ Γ Δ x s A emp wf shs dhs =>
    intro Γ' Δ' ξ agr
    asimp
    exact .var emp (wf.rename agr) (agr.toStatic.has shs) (agr.has dhs)
  | @lamIm Θ Γ Δ A B m s k1 k2 tym ihm =>
    intro Γ' Δ' ξ agr
    asimp
    cases tym.wf with
    | @null _ _ _ s' _ tyA =>
      exact .lamIm k1 (agr.key k2) (ihm (.null tyA agr))
  | @lamEx Θ Γ Δ A B m s t k1 k2 tym ihm =>
    intro Γ' Δ' ξ agr
    asimp
    cases tym.wf with
    | @cons _ _ _ s' _ tyA =>
      exact .lamEx k1 (agr.key k2) (ihm (.cons tyA agr))
  | @appIm Θ Γ Δ A B m n s tym tyn ihm =>
    intro Γ' Δ' ξ agr
    rw [show (B[Chan.var_Chan; n..])⟨(id : Nat → Nat); ξ⟩
          = (B⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (n⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp]
    have ihm' := ihm agr
    asimp at ihm'
    exact .appIm ihm' (Static.Typed.rename tyn agr.toStatic)
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrgΘ mrgΔ tym tyn ihm ihn =>
    intro Γ' Δ' ξ agr
    rw [show (B[Chan.var_Chan; n..])⟨(id : Nat → Nat); ξ⟩
          = (B⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (n⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp]
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    have ihm' := ihm agr1
    asimp at ihm'
    exact .appEx mrgΘ mrgΔ' ihm' (ihn agr2)
  | @pairIm Θ Γ Δ A B m n t tyS tym tyn ihn =>
    intro Γ' Δ' ξ agr
    have tym' := Static.Typed.rename tym agr.toStatic
    have ihn' := ihn agr
    have tyS' := Static.Typed.rename tyS agr.toStatic
    asimp at tyS' ⊢
    rw [show (B[Chan.var_Chan; m..])⟨(id : Nat → Nat); ξ⟩
          = (B⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (m⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp] at ihn'
    exact .pairIm tyS' tym' ihn'
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrgΘ mrgΔ tyS tym tyn ihm ihn =>
    intro Γ' Δ' ξ agr
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    have ihm' := ihm agr1
    have ihn' := ihn agr2
    have tyS' := Static.Typed.rename tyS agr.toStatic
    asimp at tyS' ⊢
    rw [show (B[Chan.var_Chan; m..])⟨(id : Nat → Nat); ξ⟩
          = (B⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (m⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp] at ihn'
    exact .pairEx mrgΘ mrgΔ' tyS' ihm' ihn'
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    intro Γ' Δ' ξ agr
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    cases tyC.wf with
    | @cons _ _ s' _ tyAB =>
      cases tyn.wf with
      | @cons _ _ _ s'' wfA tyB =>
        cases wfA with
        | @null _ _ _ s''' _ tyA =>
          have ihC := Static.Typed.rename tyC (Static.AgreeRen.cons tyAB agr.toStatic)
          have ihm' := ihm agr1
          have ihn' := ihn (AgreeRen.cons tyB (AgreeRen.null tyA agr2))
          asimp at ihC ihm'
          rw [show (C[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)])⟨(id :
                  Nat → Nat); upRen_Term_Term (upRen_Term_Term ξ)⟩
                = (C⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)]
                from by asimp; congr 1] at ihn'
          rw [show (C[Chan.var_Chan; m..])⟨(id : Nat → Nat); ξ⟩
                = (C⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (m⟨(id : Nat → Nat);
                  ξ⟩)..] from by asimp]
          exact .projIm mrgΘ mrgΔ' ihC ihm' ihn'
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    intro Γ' Δ' ξ agr
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    cases tyC.wf with
    | @cons _ _ s' _ tyAB =>
      cases tyn.wf with
      | @cons _ _ _ s'' wfA tyB =>
        cases wfA with
        | @cons _ _ _ s''' _ tyA =>
          have ihC := Static.Typed.rename tyC (Static.AgreeRen.cons tyAB agr.toStatic)
          have ihm' := ihm agr1
          have ihn' := ihn (AgreeRen.cons tyB (AgreeRen.cons tyA agr2))
          asimp at ihC ihm'
          rw [show (C[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)])⟨(id :
                  Nat → Nat); upRen_Term_Term (upRen_Term_Term ξ)⟩
                = (C⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)]
                from by asimp; congr 1] at ihn'
          rw [show (C[Chan.var_Chan; m..])⟨(id : Nat → Nat); ξ⟩
                = (C⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (m⟨(id : Nat → Nat);
                  ξ⟩)..] from by asimp]
          exact .projEx mrgΘ mrgΔ' ihC ihm' ihn'
  | @one Θ Γ Δ emp wf k =>
    intro Γ' Δ' ξ agr; asimp; exact .one emp (wf.rename agr) (agr.key k)
  | @tt Θ Γ Δ emp wf k =>
    intro Γ' Δ' ξ agr; asimp; exact .tt emp (wf.rename agr) (agr.key k)
  | @ff Θ Γ Δ emp wf k =>
    intro Γ' Δ' ξ agr; asimp; exact .ff emp (wf.rename agr) (agr.key k)
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrgΘ mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    intro Γ' Δ' ξ agr
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    have tyBool : Γ ⊢ Term.bool : Term.srt .U := .bool tym.wf.toStatic
    have ihm' := ihm agr1
    have ihn1' := ihn1 agr2
    have ihn2' := ihn2 agr2
    have tyA' := Static.Typed.rename tyA (Static.AgreeRen.cons tyBool agr.toStatic)
    asimp at tyA'
    rw [show (A[Chan.var_Chan; Term.tt..])⟨(id : Nat → Nat); ξ⟩
          = (A⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; Term.tt..]
          from by asimp] at ihn1'
    rw [show (A[Chan.var_Chan; Term.ff..])⟨(id : Nat → Nat); ξ⟩
          = (A⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; Term.ff..]
          from by asimp] at ihn2'
    rw [show (A[Chan.var_Chan; m..])⟨(id : Nat → Nat); ξ⟩
          = (A⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (m⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp]
    exact .ite mrgΘ mrgΔ' tyA' ihm' ihn1' ihn2'
  | @pure Θ Γ Δ m A tym ihm =>
    intro Γ' Δ' ξ agr; asimp; exact .pure (ihm agr)
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrgΘ mrgΔ tyB tym tyn ihm ihn =>
    intro Γ' Δ' ξ agr
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    cases tyn.wf with
    | @cons _ _ _ s' _ tyA =>
      have tyB' := Static.Typed.rename tyB agr.toStatic
      have ihn' := ihn (.cons tyA agr2)
      asimp at tyB' ⊢
      rw [show (Term.M (B⟨(id : Nat → Nat); ↑⟩))⟨(id : Nat → Nat); upRen_Term_Term ξ⟩
            = Term.M (B⟨(id : Nat → Nat); ξ⟩⟨(id : Nat → Nat); ↑⟩) from by
            show Term.M _ = Term.M _; congr 1; asimp] at ihn'
      exact .mlet mrgΘ mrgΔ' tyB' (ihm agr1) ihn'
  | @chan Θ Γ Δ r x A js wf k tyA =>
    intro Γ' Δ' ξ agr
    rw [show ((Term.chan (Chan.var_Chan x)))⟨(id : Nat → Nat); ξ⟩
          = Term.chan (Chan.var_Chan x) from rfl,
        show (Term.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩))⟨(id : Nat → Nat); ξ⟩
          = Term.ch r (A⟨(id : Nat → Nat); funcomp ξ (· + Γ.length)⟩) from by
          show Term.ch r _ = Term.ch r _; congr 1; asimp,
        agr.size]
    exact .chan js (wf.rename agr) (agr.key k) tyA
  | @fork Θ Γ Δ A m tym ihm =>
    intro Γ' Δ' ξ agr
    asimp
    cases tym.wf with
    | @cons _ _ _ s' _ tyCh =>
      have ihm' := ihm (.cons tyCh agr)
      asimp at ihm'
      exact .fork ihm'
  | @recv Θ Γ Δ r1 r2 A B m i e tym ihm =>
    intro Γ' Δ' ξ agr; asimp; exact .recv e (ihm agr)
  | @send Θ Γ Δ r1 r2 A B m i e tym ihm =>
    intro Γ' Δ' ξ agr; asimp; exact .send e (ihm agr)
  | @close Θ Γ Δ b m tym ihm =>
    intro Γ' Δ' ξ agr; asimp; exact .close (ihm agr)
  | @conv Θ Γ Δ A B m s eq tym tyB ihm =>
    intro Γ' Δ' ξ agr
    exact .conv (Static.conv_ren ξ eq) (ihm agr) (Static.Typed.rename tyB agr.toStatic)

/-- Unrestricted weakening (Coq `dyn_weakenU`). -/
lemma Typed.weakenU {Θ Γ Δ m A B} (tyB : Γ ⊢ B : .srt Srt.U) (tym : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    Θ ⨾ (B :: Γ) ⨾ (B :U Δ) ⊢ m⟨(id : Nat → Nat); ↑⟩ : A⟨(id : Nat → Nat); ↑⟩ :=
  tym.rename (.wkU tyB (.refl tym.wf))

/-- Null weakening (Coq `dyn_weakenN`). -/
lemma Typed.weakenN {Θ Γ Δ m A B s} (tyB : Γ ⊢ B : .srt s) (tym : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    Θ ⨾ (B :: Γ) ⨾ (none :: Δ) ⊢ m⟨(id : Nat → Nat); ↑⟩ : A⟨(id : Nat → Nat); ↑⟩ :=
  tym.rename (.wkN tyB (.refl tym.wf))

/-- Unrestricted weakening up to equality (Coq `dyn_eweakenU`). -/
lemma Typed.eweakenU {Θ Γ Δ m m' A A' B}
    (em : m' = m⟨(id : Nat → Nat); ↑⟩) (eA : A' = A⟨(id : Nat → Nat); ↑⟩)
    (tyB : Γ ⊢ B : .srt Srt.U) (tym : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    Θ ⨾ (B :: Γ) ⨾ (B :U Δ) ⊢ m' : A' := by
  subst em; subst eA; exact tym.weakenU tyB

/-- Null weakening up to equality (Coq `dyn_eweakenN`). -/
lemma Typed.eweakenN {Θ Γ Δ m m' A A' B s}
    (em : m' = m⟨(id : Nat → Nat); ↑⟩) (eA : A' = A⟨(id : Nat → Nat); ↑⟩)
    (tyB : Γ ⊢ B : .srt s) (tym : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    Θ ⨾ (B :: Γ) ⨾ (none :: Δ) ⊢ m' : A' := by
  subst em; subst eA; exact tym.weakenN tyB

end TLLC.Dynamic
