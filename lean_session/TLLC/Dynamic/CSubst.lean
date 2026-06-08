import TLLC.Dynamic.Inversion
import TLLC.Dynamic.ProcWf
import TLLC.Static.CSubst

/-!
# Dynamic channel substitution

Port of `coq_session/dyn_csubst.v`: the dynamic channel-*substitution* agreement relation
`AgreeCSubst` (Coq `dyn_agree_csubst`, notation `Θ1 ⊩ σ ⫣ Θ2`), which threads a channel
substitution `σ` transforming the *process* context `Θ2` into `Θ1`; its structural lemmas
(`AgreeCSubst.empty`/`key`/`merge`/`procWf`/`just`, Coq `dyn_agree_csubst_empty`/`_key`/`_merge`/
`_wf`/`_just`), the process-context merge inversion `ProcWf.merge_inv` (Coq `proc_wf_merge_inv`,
proved here over `ProcWf`), and the headline preservation metatheorem `Typed.csubstitution`
(Coq `dyn_csubstitution`).

## Encoding (`σ : Nat → Chan`).

In the Lean AST `Chan` is a *variable-only* sort (its only constructor is `Chan.var_Chan`), so a
channel substitution is `σ : Nat → Chan` and `csubst σ m = m[σ; Term.var_Term]` (the channel
autosubst slot substituted, the term slot fixed at `Term.var_Term`). The Coq side condition
`sta_agree_csubst σ` (`∀ x, ∃ c, σ x = CVar c`) is therefore *automatic* here and is dropped
throughout — every `Chan` already *is* a variable. Consequently `Static.csubst_cren m σ :
m⟨Static.csubst_ren σ; id⟩ = m[σ; Term.var_Term]` is *unconditional*, and bridges channel
substitution to a channel renaming; combined with `Static.cren_conv0` (`cren ξ m ≃ m`) it gives the
workhorse `csubst_conv` (`csubst σ m ≃ m`) used to adapt every result type back to its un-substituted
form (the Coq `sta_csubst_cren`/`sta_cren_conv0` threading).

The Coq combinators map as: `cids = Chan.var_Chan` (identity channel subst), `cup σ = up_Term_Chan σ`
(lift under a Term binder), `cren ξ = ·⟨ξ; (id : Nat → Nat)⟩`, `σ >>> cren (+1)` is the channel-shift
of `σ` (its autosubst form is derived by `asimp`). The `wk1` constructor carries a dynamic channel
typing `Typed Θb [] [] (.chan (Chan.var_Chan x)) (.ch r A)`. As in `CRename.lean`, the Coq
`(-1)`/`term_cren_comp`/`term_cren_id` channel-predecessor arithmetic in `dyn_agree_csubst_just`
becomes truncated-`Nat` reasoning discharged by `Nat.add_sub_cancel`/`omega`/`asimp`.

The induction in `Typed.csubstitution` is ported directly (it does *not* reduce to `Typed.crename`):
the agreement `AgreeCSubst` transforms `Θ` with real substitution semantics (the `wk1` constructor
genuinely splits `Θ`), so the `chan` case routes through `AgreeCSubst.just`, the merge cases through
`AgreeCSubst.merge`, and the empties through `AgreeCSubst.empty`.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- Channel-substitution agreement on the process context `Θ` (Coq `dyn_agree_csubst`).
    `σ : Nat → Chan` is the channel substitution mapping the target `Θ2` to the source `Θ1`. -/
inductive AgreeCSubst : Ctx → (Nat → Chan) → Ctx → Prop where
  | nil {Θ} :
    ProcWf Θ →
    AgreeCSubst Θ Chan.var_Chan Θ
  | pad {Θ1 σ Θ2} :
    AgreeCSubst Θ1 σ Θ2 →
    AgreeCSubst (none :: Θ1) (funcomp (ren_Chan Nat.succ) σ) Θ2
  | ty {Θ1 σ Θ2 r A} :
    AgreeCSubst Θ1 σ Θ2 →
    [] ⊢ A : .proto →
    AgreeCSubst (.ch r A :L Θ1) (up_Chan_Chan σ) (.ch r A :L Θ2)
  | n {Θ1 σ Θ2} :
    AgreeCSubst Θ1 σ Θ2 →
    AgreeCSubst (none :: Θ1) (up_Chan_Chan σ) (none :: Θ2)
  | wk0 {Θ1 σ Θ2 x} :
    AgreeCSubst Θ1 σ Θ2 →
    AgreeCSubst Θ1 (Chan.var_Chan x .: σ) (none :: Θ2)
  | wk1 {Θa Θb Θ1 σ Θ2 x r A} :
    Merge Θa Θb Θ1 →
    AgreeCSubst Θa σ Θ2 →
    Θb ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ .chan (Chan.var_Chan x) : .ch r A →
    AgreeCSubst Θ1 (Chan.var_Chan x .: σ) (.ch r A :L Θ2)
  | conv {Θ1 σ Θ2 A B r} :
    A ≃ B →
    [] ⊢ B : .proto →
    AgreeCSubst Θ1 σ (.ch r A :L Θ2) →
    AgreeCSubst Θ1 σ (.ch r B :L Θ2)

@[inherit_doc] scoped notation:50 Θ1:50 " ⊩ " σ:51 " ⫣ " Θ2:51 => AgreeCSubst Θ1 σ Θ2

/-! ## Channel substitution as a channel renaming.

The Coq side condition `sta_agree_csubst σ` is automatic (`σ : Nat → Chan`), so the bridge lemmas
`dyn_sta_agree_csubst`/`dyn_csubst_cren` collapse to direct uses of `Static.csubst_cren`. -/

/-- A channel substitution leaves a term invariant up to conversion (the workhorse threading the Coq
    `sta_csubst_cren` + `sta_cren_conv0` chain): `csubst σ m ≃ m`. Unconditional here because
    `Static.csubst_cren` is unconditional. -/
lemma csubst_conv (σ : Nat → Chan) (m : Term) : m[σ; Term.var_Term] ≃ m := by
  rw [← Static.csubst_cren]
  exact Static.cren_conv0 .refl (Static.csubst_ren σ)

/-- Channel substitution coincides with channel renaming by its extracted indices (Coq
    `dyn_csubst_cren`). A direct instance of `Static.csubst_cren`. -/
lemma AgreeCSubst.csubst_cren {Θ1 Θ2 σ} (_agr : Θ1 ⊩ σ ⫣ Θ2) (m : Term) :
    m⟨Static.csubst_ren σ; (id : Nat → Nat)⟩ = m[σ; Term.var_Term] :=
  Static.csubst_cren m σ

/-! ## Structural lemmas. -/

/-- Channel substitution preserves emptiness of the process context (Coq `dyn_agree_csubst_empty`). -/
lemma AgreeCSubst.empty {Θ1 Θ2 σ} (agr : Θ1 ⊩ σ ⫣ Θ2) (emp : Empty Θ2) : Empty Θ1 := by
  induction agr with
  | nil _ => exact emp
  | pad _ ih => exact .null (ih emp)
  | ty _ _ => cases emp
  | n _ ih => cases emp with | null e => exact .null (ih e)
  | wk0 _ ih => cases emp with | null e => exact ih e
  | wk1 _ _ _ => cases emp
  | conv _ _ _ => cases emp

/-- Channel substitution transports keys (Coq `dyn_agree_csubst_key`). -/
lemma AgreeCSubst.key {Θ1 Θ2 σ s} (agr : Θ1 ⊩ σ ⫣ Θ2) (k : Θ2 ▷ s) : Θ1 ▷ s := by
  induction agr generalizing s with
  | nil _ => exact k
  | pad _ ih => exact .null (ih k)
  | ty _ _ ih => cases k with | L _ k' => exact .L _ (ih k')
  | n _ ih => cases k with | null k' => exact .null (ih k')
  | wk0 _ ih => cases k with | null k' => exact ih k'
  | @wk1 Θa Θb Θ1 σ Θ2 x r A mrg agr tyx ih =>
    cases k with | L _ k' => exact mrg.key_image (ih k') Key.impure
  | conv _ _ _ ih => cases k with | L _ k' => exact ih (.L _ k')

/-- Merge inversion for well-formed process contexts (Coq `proc_wf_merge_inv`). -/
lemma ProcWf.merge_inv {Θ1 Θ2 Θ} (mrg : Merge Θ1 Θ2 Θ) (wf : ProcWf Θ) :
    ProcWf Θ1 ∧ ProcWf Θ2 := by
  induction mrg with
  | nil => exact ⟨.nil, .nil⟩
  | left _ _ => cases wf
  | right1 _ mrg' ih => cases wf with
    | ty wf' tyA => obtain ⟨w1, w2⟩ := ih wf'; exact ⟨.ty w1 tyA, .null w2⟩
  | right2 _ mrg' ih => cases wf with
    | ty wf' tyA => obtain ⟨w1, w2⟩ := ih wf'; exact ⟨.null w1, .ty w2 tyA⟩
  | null _ ih => cases wf with
    | null wf' => obtain ⟨w1, w2⟩ := ih wf'; exact ⟨.null w1, .null w2⟩

/-- Channel substitution is compatible with merge (Coq `dyn_agree_csubst_merge`). -/
lemma AgreeCSubst.merge {Θ1 Θ2 σ} (agr : Θ1 ⊩ σ ⫣ Θ2) :
    ∀ {Θa Θb}, Merge Θa Θb Θ2 →
    ∃ Θa' Θb', Merge Θa' Θb' Θ1 ∧ (Θa' ⊩ σ ⫣ Θa) ∧ (Θb' ⊩ σ ⫣ Θb) := by
  induction agr with
  | @nil Θ wf =>
    intro Θa Θb mrg
    obtain ⟨wf1, wf2⟩ := ProcWf.merge_inv mrg wf
    exact ⟨Θa, Θb, mrg, .nil wf1, .nil wf2⟩
  | @pad Θ1 σ Θ2 agr ih =>
    intro Θa Θb mrg
    obtain ⟨Θa', Θb', mrg', agr1, agr2⟩ := ih mrg
    exact ⟨none :: Θa', none :: Θb', .null mrg', .pad agr1, .pad agr2⟩
  | @ty Θ1 σ Θ2 r A agr tyA ih =>
    intro Θa Θb mrg
    cases mrg with
    | right1 _ mrg' =>
      obtain ⟨Θa', Θb', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨.ch r A :L Θa', none :: Θb', .right1 _ mrg', .ty agr1 tyA, .n agr2⟩
    | right2 _ mrg' =>
      obtain ⟨Θa', Θb', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨none :: Θa', .ch r A :L Θb', .right2 _ mrg', .n agr1, .ty agr2 tyA⟩
  | @n Θ1 σ Θ2 agr ih =>
    intro Θa Θb mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θa', Θb', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨none :: Θa', none :: Θb', .null mrg', .n agr1, .n agr2⟩
  | @wk0 Θ1 σ Θ2 x agr ih =>
    intro Θa Θb mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θa', Θb', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨Θa', Θb', mrg', .wk0 agr1, .wk0 agr2⟩
  | @wk1 Θa0 Θb0 Θ1 σ Θ2 x r A mrgΘ agr tyx ih =>
    intro Θa Θb mrg
    cases mrg with
    | right1 _ mrg' =>
      obtain ⟨Θa', Θb', mrg', agr1, agr2⟩ := ih mrg'
      obtain ⟨Θc, mrg1, mrg2⟩ := mrgΘ.splitL mrg'
      exact ⟨Θc, Θb', mrg2, .wk1 mrg1 agr1 tyx, .wk0 agr2⟩
    | right2 _ mrg' =>
      obtain ⟨Θa', Θb', mrg', agr1, agr2⟩ := ih mrg'
      obtain ⟨Θc, mrg1, mrg2⟩ := mrgΘ.splitR mrg'
      exact ⟨Θa', Θc, mrg2.sym, .wk0 agr1, .wk1 mrg1 agr2 tyx⟩
  | @conv Θ1 σ Θ2 A B r eq tyB agr ih =>
    intro Θa Θb mrg
    cases mrg with
    | right1 _ mrg' =>
      obtain ⟨Θa', Θb', mrg', agr1, agr2⟩ := ih (.right1 (Term.ch r A) mrg')
      exact ⟨Θa', Θb', mrg', .conv eq tyB agr1, agr2⟩
    | right2 _ mrg' =>
      obtain ⟨Θa', Θb', mrg', agr1, agr2⟩ := ih (.right2 (Term.ch r A) mrg')
      exact ⟨Θa', Θb', mrg', agr1, .conv eq tyB agr2⟩

/-- The source of a channel substitution agreement is well-formed (Coq `dyn_agree_csubst_wf`). -/
lemma AgreeCSubst.procWf {Θ1 Θ2 σ} (agr : Θ1 ⊩ σ ⫣ Θ2) : ProcWf Θ2 := by
  induction agr with
  | nil wf => exact wf
  | pad _ ih => exact ih
  | ty _ tyA ih => exact .ty ih tyA
  | n _ ih => exact .null ih
  | wk0 _ ih => exact .null ih
  | @wk1 Θa Θb Θ1 σ Θ2 x r A mrg agr tyx ih =>
    obtain ⟨s, tyC⟩ := tyx.validity
    obtain ⟨tyA, _⟩ := Static.ch_inv tyC
    exact .ty ih tyA
  | conv eq tyB _ ih => cases ih with | ty wf' _ => exact .ty wf' tyB

/-! ## Channel-variable typing under a substitution. -/

/-- Peeling a null-slot `Just` lookup at a channel type: the de Bruijn shift on the stored type is
    `⟨(·+1); id⟩`, which on a `.ch` head reduces to a shift of the protocol; the channel-predecessor
    renaming `(· - 1)` undoes it (Coq's `inv js; destruct A0; inv H0; apply (sta_crename (-1))`). -/
lemma just_ch_pred {Θ x r A} (js : Just (none :: Θ) x (.ch r A)) :
    ∃ z A0, x = z + 1 ∧ A = A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ ∧ Just Θ z (.ch r A0) := by
  generalize hC : Term.ch r A = C at js
  cases js with
  | @null _ A1 z js' =>
    -- `A1⟨(·+1);id⟩ = .ch r A`; so `A1 = .ch r A0` with `A = A0⟨(·+1);id⟩`.
    cases A1
    case ch r' A0 =>
      rw [show (Term.ch r' A0)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            = Term.ch r' (A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) from by asimp] at hC
      cases hC
      exact ⟨z, A0, rfl, rfl, js'⟩
    all_goals (asimp at hC; exact absurd hC (by simp))

/-- Peeling a real-slot `Just` lookup at a channel type (the `Just.zero` case): the index is `0`,
    the slots after are empty, and the stored type is the front protocol shifted by `(·+1)`. -/
lemma just_ch_zero {Θ x r A r0 A0} (js : Just (.ch r A :L Θ) x (.ch r0 A0)) :
    x = 0 ∧ r0 = r ∧ A0 = A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ ∧ Empty Θ := by
  generalize hC : Term.ch r0 A0 = C at js
  cases js with
  | zero emp =>
    rw [show (Term.ch r A)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
          = Term.ch r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) from by asimp] at hC
    cases hC
    exact ⟨rfl, rfl, rfl, emp⟩

/-- A channel renaming by the predecessor `(· - 1)` undoes the `(·+1)` shift on a closed protocol,
    keeping it well-typed (the `sta_crename (-1)` + `term_cren_comp`/`term_cren_id` chain). -/
lemma proto_pred {A0 : Term} (tyA : [] ⊢ A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ : .proto) :
    [] ⊢ A0 : .proto := by
  have h := Static.Typed.crename tyA (funcomp (id : Nat → Nat) (· - 1))
  have hmap : funcomp ((· - 1) : Nat → Nat) ((· + 1) : Nat → Nat) = (id : Nat → Nat) := by
    funext y; simp only [funcomp, id]; omega
  rw [show (A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨funcomp (id : Nat → Nat) (· - 1);
        (id : Nat → Nat)⟩ = A0 from by asimp; rw [hmap]; asimp] at h
  exact h

/-- Channel substitution types the substituted channel variable (Coq `dyn_agree_csubst_just`). The
    `Just` lookup type carries a `⟨(·+1); id⟩` channel shift (the de Bruijn lift), which the hard
    cases peel via a channel-predecessor renaming `(· - 1)` (Coq `sta_crename (-1)` with
    `term_cren_comp`/`term_cren_id`; here truncated-`Nat` arithmetic). -/
lemma AgreeCSubst.just {Θ1 Θ2 σ x r A} (agr : Θ1 ⊩ σ ⫣ Θ2)
    (tyA : [] ⊢ A : .proto) (js : Just Θ2 x (.ch r A)) :
    Θ1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ .chan (σ x) : .ch r A := by
  induction agr generalizing x r A with
  | @nil Θ wf =>
    -- σ = Chan.var_Chan; the `chan` rule's `A⟨id; (·+0)⟩` collapses to `A`.
    have h := Typed.chan js Wf.nil Key.nil tyA
    rw [show A⟨(id : Nat → Nat); (· + ([] : Static.Ctx).length)⟩ = A from by
          simp only [List.length_nil, Nat.add_zero]
          rw [show ((fun x => x) : Nat → Nat) = (id : Nat → Nat) from rfl]
          asimp] at h
    exact h
  | @pad Θ1 σ Θ2 agr ih =>
    -- σ' = funcomp (ren_Chan +1) σ; cweaken the IH.
    have h := (ih tyA js).cweaken
    cases hc : σ x with
    | var_Chan k =>
      rw [show (Term.chan (σ x))⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            = Term.chan (funcomp (ren_Chan Nat.succ) σ x) from by
            rw [hc]; show Term.chan (Chan.var_Chan (k + 1)) = _
            rw [show funcomp (ren_Chan Nat.succ) σ x = ren_Chan Nat.succ (σ x) from rfl, hc]
            rfl] at h
      exact h
  | @ty Θ1 σ Θ2 r0 A0 agr tyA0 ih =>
    obtain ⟨hx, hr, hA, emp2⟩ := just_ch_zero js
    subst hx; subst hr; subst hA
    have emp1 := agr.empty emp2
    -- `up_Chan_Chan σ 0 = Chan.var_Chan 0`; the front-channel typing matches the shifted goal type.
    rw [show up_Chan_Chan σ 0 = Chan.var_Chan 0 from rfl]
    have js0 : Just (.ch r A0 :L Θ1) 0 (.ch r (A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)) := by
      have h0 := Just.zero (Δ := Θ1) (A := Term.ch r A0) emp1
      rwa [show (Term.ch r A0)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            = Term.ch r (A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) from by asimp] at h0
    have h := Typed.chan (Γ := []) (Δ := []) js0 Wf.nil Key.nil tyA
    rw [show (A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨(id : Nat → Nat);
          (· + ([] : Static.Ctx).length)⟩ = A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ from by
          simp only [List.length_nil, Nat.add_zero]
          rw [show ((fun x => x) : Nat → Nat) = (id : Nat → Nat) from rfl]; asimp] at h
    exact h
  | @n Θ1 σ Θ2 agr ih =>
    obtain ⟨z, A0, hx, hA, js'⟩ := just_ch_pred js
    subst hx; subst hA
    have tyA0 := proto_pred tyA
    have h := (ih tyA0 js').cweaken
    cases hc : σ z with
    | var_Chan k =>
      rw [show (Term.chan (σ z))⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            = Term.chan (up_Chan_Chan σ (z + 1)) from by
            rw [hc]; show Term.chan (Chan.var_Chan (k + 1)) = _
            rw [show up_Chan_Chan σ (z + 1) = ren_Chan Nat.succ (σ z) from rfl, hc]; rfl] at h
      apply Typed.conv ?_ h (.ch tyA)
      exact Static.conv_ch (ARS.conv_sym (Static.cren_conv0 .refl ((· + 1) : Nat → Nat)))
  | @wk0 Θ1 σ Θ2 y agr ih =>
    obtain ⟨z, A0, hx, hA, js'⟩ := just_ch_pred js
    subst hx; subst hA
    have tyA0 := proto_pred tyA
    have h := ih tyA0 js'
    -- result type `.ch r A0`; goal wants `.ch r (A0⟨+1;id⟩)`; adapt via `cren_conv0`.
    rw [show (Chan.var_Chan y .: σ) (z + 1) = σ z from rfl]
    apply Typed.conv ?_ h (.ch tyA)
    apply Static.conv_ch
    exact ARS.conv_sym (Static.cren_conv0 .refl ((· + 1) : Nat → Nat))
  | @wk1 Θa Θb Θ1 σ Θ2 y r0 A0 mrg agr tyx ih =>
    obtain ⟨hx, hr, hA, emp2⟩ := just_ch_zero js
    subst hx; subst hr; subst hA
    -- `Empty Θa` (via `agr.empty`), so the merge `Θa ∘ Θb => Θ1` makes `Θb = Θ1`.
    have emp_a := agr.empty emp2
    have e := mrg.emptyL emp_a; subst e
    -- `(Chan.var_Chan y .: σ) 0 = Chan.var_Chan y`; `tyx : Θ1 ⊢ chan y : .ch r0 A0`.
    rw [show (Chan.var_Chan y .: σ) 0 = Chan.var_Chan y from rfl]
    apply Typed.conv ?_ tyx (.ch tyA)
    exact Static.conv_ch (ARS.conv_sym (Static.cren_conv0 .refl ((· + 1) : Nat → Nat)))
  | @conv Θ1 σ Θ2 A1 B r0 eq tyB agr ih =>
    -- target is `.ch r0 B :L Θ2`; peel the lookup, then run `ih` over the pre-conv `.ch r0 A1 :L Θ2`.
    obtain ⟨hx, hr, hA, emp2⟩ := just_ch_zero js
    subst hx; subst hr; subst hA
    -- recover `[] ⊢ A1 : proto` from the pre-conv agreement's well-formedness.
    have wfA1 : [] ⊢ A1 : .proto := by cases agr.procWf with | ty _ tyA1 => exact tyA1
    have tyA1s := Static.Typed.crename wfA1 ((· + 1) : Nat → Nat)
    have js0 : Just (.ch r A1 :L Θ2) 0 (.ch r (A1⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)) := by
      have h0 := Just.zero (Δ := Θ2) (A := Term.ch r A1) emp2
      rwa [show (Term.ch r A1)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            = Term.ch r (A1⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) from by asimp] at h0
    have h := ih tyA1s js0
    -- adapt `.ch r (A1⟨+1;id⟩)` to the goal `.ch r (B⟨+1;id⟩)` via `A1 ≃ B`.
    apply Typed.conv ?_ h (.ch tyA)
    apply Static.conv_ch
    exact ARS.conv_trans (Static.cren_conv0 .refl ((· + 1) : Nat → Nat))
      (ARS.conv_trans eq (ARS.conv_sym (Static.cren_conv0 .refl ((· + 1) : Nat → Nat))))

/-- Well-sortedness of the `proj` branch motive `C[⟨1,0⟩ .: (+2)]` under the pattern context
    `B :: A :: Γ` (the static `Σ`-elim pair-injection substitution; same construction as the
    `projMotive_wellSorted` helper of `CRename.lean`, re-stated here since that one is `private`). -/
private lemma projMotive_wellSorted {Γ A B C i t s}
    (ihC : (Term.sig A B i t :: Γ) ⊢ C : .srt s)
    (wf : Static.Wf (Term.sig A B i t :: Γ)) :
    (B :: A :: Γ) ⊢
      C[Chan.var_Chan; Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)]
      : .srt s := by
  cases wf with
  | @cons _ _ s0 wfΓ tySig =>
    obtain ⟨s1, r, ord1, ord2, tyA, tyB, _⟩ := Static.sig_inv tySig
    have wf2 : Static.Wf (B :: A :: Γ) := .cons (.cons wfΓ tyA) tyB
    have agr0 : (B :: A :: Γ) ⊢ funcomp Term.var_Term (· + 2) ⊣ Γ := by
      have h := ((Static.AgreeSubst.refl wfΓ).wk2 (s := s1) tyA).wk2 (s := r) tyB
      rwa [show (fun x => ((Term.var_Term x)⟨(id : Nat → Nat); ↑⟩)⟨(id : Nat → Nat); ↑⟩)
            = funcomp Term.var_Term (· + 2) from by funext x; asimp] at h
    have tySig' := (Static.Typed.sig ord1 ord2 tyA tyB).substitution agr0
    asimp at tySig'
    have tyv1 : (B :: A :: Γ) ⊢ Term.var_Term 1
        : A[Chan.var_Chan; funcomp Term.var_Term (· + 2)] := by
      have h := Static.Typed.var wf2 (Static.Has.succ Static.Has.zero)
      rwa [show A⟨(id : Nat → Nat); ↑⟩⟨(id : Nat → Nat); ↑⟩
            = A[Chan.var_Chan; funcomp Term.var_Term (· + 2)] from by asimp; substify] at h
    have tyv0 : (B :: A :: Γ) ⊢ Term.var_Term 0
        : (B[Chan.var_Chan; up_Term_Term (funcomp Term.var_Term (· + 2))])[Chan.var_Chan;
            (Term.var_Term 1)..] := by
      have h := Static.Typed.var wf2 (Static.Has.zero (A := B))
      rwa [show B⟨(id : Nat → Nat); ↑⟩
            = (B[Chan.var_Chan; up_Term_Term (funcomp Term.var_Term (· + 2))])[Chan.var_Chan;
              (Term.var_Term 1)..] from by
              asimp; substify; congr 1; funext x; rcases x with _ | x <;> rfl] at h
    have agr : (B :: A :: Γ)
        ⊢ Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)
        ⊣ (Term.sig A B i t :: Γ) :=
      agr0.wk1 (A := Term.sig A B i t) (Static.Typed.pair tySig' tyv1 tyv0)
    exact ihC.substitution agr

/-! ## Channel substitution preserves typing. -/

/-- Channel substitution preserves dynamic typing (Coq `dyn_csubstitution`). Only the term is
    channel-substituted (`m[σ; Term.var_Term]`); the type `A` is left fixed (channel types are
    context-stable, so `csubst σ A ≃ A`). Ported by direct induction (the agreement genuinely splits
    `Θ` at the `wk1` constructor), threading `csubst_conv` to adapt each result type. -/
theorem Typed.csubstitution {Θ2 Γ Δ m A} (tym : Θ2 ⨾ Γ ⨾ Δ ⊢ m : A) :
    ∀ {Θ1 σ}, (Θ1 ⊩ σ ⫣ Θ2) → Θ1 ⨾ Γ ⨾ Δ ⊢ m[σ; Term.var_Term] : A := by
  induction tym with
  | @var Θ Γ Δ x s A emp wf shs dhs =>
    intro Θ1 σ agr
    asimp
    exact .var (agr.empty emp) wf shs dhs
  | @one Θ Γ Δ emp wf k =>
    intro Θ1 σ agr; asimp; exact .one (agr.empty emp) wf k
  | @tt Θ Γ Δ emp wf k =>
    intro Θ1 σ agr; asimp; exact .tt (agr.empty emp) wf k
  | @ff Θ Γ Δ emp wf k =>
    intro Θ1 σ agr; asimp; exact .ff (agr.empty emp) wf k
  | @pure Θ Γ Δ m A tym ihm =>
    intro Θ1 σ agr; asimp; exact .pure (ihm agr)
  | @recv Θ Γ Δ r1 r2 A B m i e tym ihm =>
    intro Θ1 σ agr; asimp; exact .recv e (ihm agr)
  | @send Θ Γ Δ r1 r2 A B m i e tym ihm =>
    intro Θ1 σ agr; asimp; exact .send e (ihm agr)
  | @close Θ Γ Δ b m tym ihm =>
    intro Θ1 σ agr; asimp; exact .close (ihm agr)
  | @conv Θ Γ Δ A B m s eq tym tyB ihm =>
    intro Θ1 σ agr; asimp; exact .conv eq (ihm agr) tyB
  | @lamIm Θ Γ Δ A B m s k1 k2 tym ihm =>
    intro Θ1 σ agr
    asimp
    cases tym.wf with
    | @null _ _ _ s' _ tyA =>
      obtain ⟨t, tyB⟩ := tym.validity
      -- retype the body under the substituted binder `A[σ]` and convert the `pi` head back.
      have tyAσ := Static.Typed.csubstitution tyA σ
      have hm := Typed.ctx_conv0 (csubst_conv σ A) tyAσ (ihm agr)
      exact .conv (Static.conv_pi (csubst_conv σ A) .refl)
        (.lamIm (agr.key k1) k2 hm) (.pi tyA tyB)
  | @lamEx Θ Γ Δ A B m s t k1 k2 tym ihm =>
    intro Θ1 σ agr
    asimp
    cases tym.wf with
    | @cons _ _ _ s' _ tyA =>
      obtain ⟨r, tyB⟩ := tym.validity
      have tyAσ := Static.Typed.csubstitution tyA σ
      have hm := Typed.ctx_conv1 (csubst_conv σ A) tyAσ (ihm agr)
      exact .conv (Static.conv_pi (csubst_conv σ A) .refl)
        (.lamEx (agr.key k1) k2 hm) (.pi tyA tyB)
  | @appIm Θ Γ Δ A B m n s tym tyn ihm =>
    intro Θ1 σ agr
    obtain ⟨t, tyP⟩ := tym.validity
    obtain ⟨r, tyB, _⟩ := Static.pi_inv tyP
    have tyBn := tyB.subst tyn
    asimp at tyBn
    asimp
    have tyn' := Static.Typed.csubstitution tyn σ
    exact .conv (Static.conv_beta (csubst_conv σ n)) (.appIm (ihm agr) tyn') tyBn
  | @appEx Θ1' Θ2' Θ' Γ Δ1 Δ2 Δ A B m n s mrgΘ mrgΔ tym tyn ihm ihn =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    obtain ⟨t, tyP⟩ := tym.validity
    obtain ⟨r, tyB, _⟩ := Static.pi_inv tyP
    have tyBn := tyB.subst tyn.toStatic
    asimp at tyBn
    asimp
    exact .conv (Static.conv_beta (csubst_conv σ n)) (.appEx mrgΘ' mrgΔ (ihm agr1) (ihn agr2)) tyBn
  | @pairIm Θ Γ Δ A B m n t tyS tym tyn ihn =>
    intro Θ1 σ agr
    asimp
    obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
    have tym' := Static.Typed.csubstitution tym σ
    have tyBm := tyB.subst tym'
    asimp at tyBm
    -- the `n` component: convert `B[m..]` to `B[(m[σ])..]`.
    have ihn' : Θ1 ⨾ Γ ⨾ Δ ⊢ n[σ; Term.var_Term] : B[Chan.var_Chan; (m[σ; Term.var_Term])..] :=
      Typed.conv (ARS.conv_sym (Static.conv_beta (csubst_conv σ m))) (ihn agr) tyBm
    exact .pairIm tyS tym' ihn'
  | @pairEx Θ1' Θ2' Θ' Γ Δ1 Δ2 Δ A B m n t mrgΘ mrgΔ tyS tym tyn ihm ihn =>
    intro Θ1 σ agr
    asimp
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
    have tym' := Static.Typed.csubstitution tym.toStatic σ
    have tyBm := tyB.subst tym'
    asimp at tyBm
    have ihn' : Θb ⨾ Γ ⨾ Δ2 ⊢ n[σ; Term.var_Term] : B[Chan.var_Chan; (m[σ; Term.var_Term])..] :=
      Typed.conv (ARS.conv_sym (Static.conv_beta (csubst_conv σ m))) (ihn agr2) tyBm
    exact .pairEx mrgΘ' mrgΔ tyS (ihm agr1) ihn'
  | @projIm Θ1' Θ2' Θ' Γ Δ1 Δ2 Δ A B C m n s r t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have tyC' := Static.Typed.csubstitution tyC σ
    -- the branch: convert the un-substituted motive in `ihn`'s type to the substituted one.
    have eqn : (C[σ; Term.var_Term])[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)]
        ≃ C[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)] :=
      Static.conv_subst _ (csubst_conv σ C)
    have tyn'' := Typed.conv (ARS.conv_sym eqn) (ihn agr2)
      (projMotive_wellSorted (i := .im) tyC' tyC.wf)
    -- the result type.
    have eqC : (C[σ; Term.var_Term])[Chan.var_Chan; (m[σ; Term.var_Term])..]
        ≃ C[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (csubst_conv σ m))
        (Static.conv_subst (m..) (csubst_conv σ C))
    asimp
    exact .conv eqC (.projIm mrgΘ' mrgΔ tyC' (ihm agr1) tyn'') (tyC.subst tym.toStatic)
  | @projEx Θ1' Θ2' Θ' Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have tyC' := Static.Typed.csubstitution tyC σ
    have eqn : (C[σ; Term.var_Term])[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)]
        ≃ C[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)] :=
      Static.conv_subst _ (csubst_conv σ C)
    have tyn'' := Typed.conv (ARS.conv_sym eqn) (ihn agr2)
      (projMotive_wellSorted (i := .ex) tyC' tyC.wf)
    have eqC : (C[σ; Term.var_Term])[Chan.var_Chan; (m[σ; Term.var_Term])..]
        ≃ C[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (csubst_conv σ m))
        (Static.conv_subst (m..) (csubst_conv σ C))
    asimp
    exact .conv eqC (.projEx mrgΘ' mrgΔ tyC' (ihm agr1) tyn'') (tyC.subst tym.toStatic)
  | @ite Θ1' Θ2' Θ' Γ Δ1 Δ2 Δ A m n1 n2 s mrgΘ mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have tyA' := Static.Typed.csubstitution tyA σ
    have h1 := tyA'.subst (Static.Typed.tt tym.wf.toStatic)
    have h2 := tyA'.subst (Static.Typed.ff tym.wf.toStatic)
    have tyn1' : Θb ⨾ Γ ⨾ Δ2 ⊢ n1[σ; Term.var_Term]
        : (A[σ; Term.var_Term])[Chan.var_Chan; Term.tt..] :=
      Typed.conv (ARS.conv_sym (Static.conv_subst (Term.tt..) (csubst_conv σ A))) (ihn1 agr2) h1
    have tyn2' : Θb ⨾ Γ ⨾ Δ2 ⊢ n2[σ; Term.var_Term]
        : (A[σ; Term.var_Term])[Chan.var_Chan; Term.ff..] :=
      Typed.conv (ARS.conv_sym (Static.conv_subst (Term.ff..) (csubst_conv σ A))) (ihn2 agr2) h2
    have eq : (A[σ; Term.var_Term])[Chan.var_Chan; (m[σ; Term.var_Term])..]
        ≃ A[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (csubst_conv σ m))
        (Static.conv_subst (m..) (csubst_conv σ A))
    asimp
    exact .conv eq (.ite mrgΘ' mrgΔ tyA' (ihm agr1) tyn1' tyn2') (tyA.subst tym.toStatic)
  | @mlet Θ1' Θ2' Θ' Γ Δ1 Δ2 Δ m n A B s t mrgΘ mrgΔ tyB tym tyn ihm ihn =>
    intro Θ1 σ agr
    asimp
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    exact .mlet mrgΘ' mrgΔ tyB (ihm agr1) (ihn agr2)
  | @chan Θ Γ Δ r x A js wf k tyA =>
    intro Θ1 σ agr
    -- `agr.just` types the substituted channel variable in the empty context.
    have tyx := agr.just tyA js
    -- lift it to `Γ`/`Δ` by the `+Γ.length` term renaming (which fixes channel variables).
    have h := tyx.rename (wf.agreeRen k)
    asimp at h ⊢
    -- the term renaming fixes the channel variable; the type is `.ch r (A⟨id; +Γ.length⟩)`.
    cases hc : σ x with
    | var_Chan c =>
      rw [hc] at h; asimp at h
      simpa using h
  | @fork Θ Γ Δ A m tym ihm =>
    intro Θ1 σ agr
    asimp
    cases tym.wf with
    | @cons _ _ _ s' _ tyCh =>
      obtain ⟨tyA, _⟩ := Static.ch_inv tyCh
      have tyAσ := Static.Typed.csubstitution tyA σ
      -- retype the body under the substituted channel binder `ch true (A[σ])`.
      have hm := Typed.ctx_conv1 (Static.conv_ch (csubst_conv σ A)) (.ch tyAσ) (ihm agr)
      apply Typed.conv (Static.conv_M (Static.conv_ch (csubst_conv σ A))) _
        (Static.Typed.M (Static.Typed.ch tyA))
      exact .fork hm

end TLLC.Dynamic