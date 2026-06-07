import TLLC.Static.Subst

/-!
# Static inversion

Port of `coq_session/sta_inv.v`: the typing-inversion lemmas, which extract the premises of a
typing derivation whose subject has a known head constructor (threading conversions through the
`conv` rule via the injectivity lemmas of `Confluence`), together with the "impossible-typing"
`*_false` lemmas, which refute cross-relevance typings.

As elsewhere, Coq's implicit/explicit constructor pairs are merged via the `Rlv` tag. The two
inversion lemmas `sta_pi0_inv`/`sta_pi1_inv` (identical save for the level) collapse into one
`pi_inv` carrying the `Rlv`; likewise `sta_act0_inv`/`sta_act1_inv` into `act_inv`. The pair
`sta_sig0_inv`/`sta_sig1_inv` genuinely differ (the `1` form carries an extra `s ⊑ t`); they merge
into `sig_inv` whose `i = .ex → s ⊑ t` premise is vacuous for `.im` and yields `s ⊑ t` for `.ex`,
exactly matching the merged `sig` typing rule.

The `*_false` lemmas merge analogously: `sta_lam0_pi1_false`/`sta_lam1_pi0_false` become a single
`lam_pi_false` and `sta_pair0_sig1_false`/`sta_pair1_sig0_false` a single `pair_sig_false`, each
gated by a relevance-mismatch hypothesis `i ≠ i'`. Because the merge turns Coq's head mismatch
(`Pi0` vs `Pi1`) into a mere `Rlv` mismatch under a shared `Term.pi` head, these lemmas refute the
conversion with `pi_inj`/`sig_inj` (extracting `i = i'`) rather than with `false_conv`; Coq's
`solve_conv` is replaced by `false_conv` only where the head constructors genuinely differ.

The proofs follow the standard generalize-then-induct idiom: the subject is generalized to a fresh
variable, induction runs over the typing derivation (`Typed.rec` with a trivial `Wf` motive, since
`Typed`/`Wf` are mutually inductive), all head-mismatch cases are discharged by `trivial`, the
matching constructor case reads off the premises, and the `conv` case threads the conversion.
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Inversion for `pi` (Coq `sta_pi0_inv` / `sta_pi1_inv`, merged). -/
lemma pi_inv {Γ A B C i s} (ty : Γ ⊢ .pi A B i s : C) :
    ∃ t, A :: Γ ⊢ B : .srt t ∧ (C ≃ .srt s) := by
  generalize e : Term.pi A B i s = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B i s
  all_goals try trivial
  case pi t _ tyB _ _ =>
    cases e; exact ⟨t, tyB, .refl⟩
  case conv eq1 _ _ ih _ =>
    obtain ⟨t, tyB, eq2⟩ := ih e
    exact ⟨t, tyB, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩

/-- Inversion for `sig` (Coq `sta_sig0_inv` / `sta_sig1_inv`, merged). -/
lemma sig_inv {Γ A B C i t} (ty : Γ ⊢ .sig A B i t : C) :
    ∃ s r,
      (i = .ex → s ⊑ t) ∧ (r ⊑ t) ∧
      Γ ⊢ A : .srt s ∧ A :: Γ ⊢ B : .srt r ∧ (C ≃ .srt t) := by
  generalize e : Term.sig A B i t = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B i t
  all_goals try trivial
  case sig =>
    cases e; exact ⟨_, _, ‹_›, ‹_›, ‹_›, ‹_›, .refl⟩
  case conv eq1 _ _ ih _ =>
    obtain ⟨s, r, ord1, ord2, tyA, tyB, eq2⟩ := ih e
    exact ⟨s, r, ord1, ord2, tyA, tyB, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩

/-- Inversion for `ite` (Coq `sta_ifte_inv`). -/
lemma ite_inv {Γ A m n1 n2 C} (ty : Γ ⊢ .ite A m n1 n2 : C) :
    (A[Chan.var_Chan; m..] ≃ C) ∧
    Γ ⊢ m : .bool ∧
    Γ ⊢ n1 : A[Chan.var_Chan; Term.tt..] ∧
    Γ ⊢ n2 : A[Chan.var_Chan; Term.ff..] := by
  generalize e : Term.ite A m n1 n2 = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A m n1 n2
  all_goals try trivial
  case ite _ tym tyn1 tyn2 _ _ _ _ =>
    cases e; exact ⟨.refl, tym, tyn1, tyn2⟩
  case conv eq1 _ _ ih _ =>
    obtain ⟨eqA, tym, tyn1, tyn2⟩ := ih e
    exact ⟨ARS.conv_trans eqA eq1, tym, tyn1, tyn2⟩

/-- Inversion for `M` (Coq `sta_io_inv`). -/
lemma M_inv {Γ A B} (ty : Γ ⊢ .M A : B) :
    ∃ s, Γ ⊢ A : .srt s ∧ (B ≃ .srt .L) := by
  generalize e : Term.M A = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A
  all_goals try trivial
  case M s tyA _ =>
    cases e; exact ⟨s, tyA, .refl⟩
  case conv eq1 _ _ ih _ =>
    obtain ⟨s, tyA, eq2⟩ := ih e
    exact ⟨s, tyA, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩

/-- Inversion for `pure` (Coq `sta_return_inv`). -/
lemma pure_inv {Γ m B} (ty : Γ ⊢ .pure m : B) :
    ∃ A, Γ ⊢ m : A ∧ (B ≃ .M A) := by
  generalize e : Term.pure m = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing m
  all_goals try trivial
  case pure A tym _ =>
    cases e; exact ⟨A, tym, .refl⟩
  case conv eq1 _ _ ih _ =>
    obtain ⟨A, tym, eq2⟩ := ih e
    exact ⟨A, tym, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩

/-- Inversion for `act` (Coq `sta_act0_inv` / `sta_act1_inv`, merged). -/
lemma act_inv {Γ b A B i C} (ty : Γ ⊢ .act b A B i : C) :
    A :: Γ ⊢ B : .proto := by
  generalize e : Term.act b A B i = n
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing b A B i
  all_goals try trivial
  case act tyB _ =>
    cases e; exact tyB
  case conv _ _ ih _ =>
    exact ih e

/-- Inversion for `ch` (Coq `sta_ch_inv`). -/
lemma ch_inv {Γ b A B} (ty : Γ ⊢ .ch b A : B) :
    Γ ⊢ A : .proto ∧ (B ≃ .srt .L) := by
  generalize e : Term.ch b A = n
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing b A
  all_goals try trivial
  case ch tyA _ =>
    cases e; exact ⟨tyA, .refl⟩
  case conv eq1 _ _ ih _ =>
    obtain ⟨tyA, eq2⟩ := ih e
    exact ⟨tyA, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩

/-- A `lam` of one relevance cannot have a `pi` type of the other
    (Coq `sta_lam0_pi1_false` / `sta_lam1_pi0_false`, merged). -/
lemma lam_pi_false {Γ A1 A2 B C m i i' s1 s2}
    (ty : Γ ⊢ .lam A1 m i s1 : C) (c : C ≃ .pi A2 B i' s2) (hi : i ≠ i') : False := by
  generalize e : Term.lam A1 m i s1 = n
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A1 A2 B m i i' s1 s2
  all_goals try trivial
  case lam _ _ =>
    cases e
    obtain ⟨_, _, ei, _⟩ := pi_inj c
    exact hi ei
  case conv eq1 _ _ ih _ =>
    exact ih (ARS.conv_trans eq1 c) hi e

/-- A `pair` of one relevance cannot have a `sig` type of the other
    (Coq `sta_pair0_sig1_false` / `sta_pair1_sig0_false`, merged). -/
lemma pair_sig_false {Γ A B C m1 m2 i i' s1 s2}
    (ty : Γ ⊢ .pair m1 m2 i s1 : C) (c : C ≃ .sig A B i' s2) (hi : i ≠ i') : False := by
  generalize e : Term.pair m1 m2 i s1 = n
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B m1 m2 i i' s1 s2
  all_goals try trivial
  case pair _ _ _ _ _ _ =>
    cases e
    obtain ⟨_, _, ei, _⟩ := sig_inj c
    exact hi ei
  case conv eq1 _ _ ih _ =>
    exact ih (ARS.conv_trans eq1 c) hi e

end TLLC.Static
