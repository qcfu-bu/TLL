import TLLC.Static.Inversion

/-!
# Static validity

Port of `coq_session/sta_valid.v`: the validity theorem `Typed.validity` (Coq `sta_valid` — every
typed term has a well-sorted type), together with the inversion lemmas for `lam`/`pair` subjects
(`lam_invX`/`lam_inv`/`pair_invX`/`pair_inv`, Coq `sta_lam0_invX`/`sta_lam1_invX`/… ).

As elsewhere, Coq's implicit/explicit constructor pairs are merged via the `Rlv` tag. The Coq
`0`/`1` lam-inversion pair `sta_lam0_invX`/`sta_lam1_invX` collapses into one `lam_invX` carrying the
`Rlv`, and likewise `sta_lam0_inv`/`sta_lam1_inv` into `lam_inv`, `sta_pair0_invX`/`sta_pair1_invX`
into `pair_invX`, and `sta_pair0_inv`/`sta_pair1_inv` into `pair_inv`. Because `lam`/`pi` (resp.
`pair`/`sig`) already share a head constructor under the merge, the conversion-head injection uses the
merged `pi_inj`/`sig_inj` of `Confluence`.

`validity` is the standard big induction over the typing derivation: each head constructor reads its
type off via the matching inversion lemma of `Inversion` (`pi_inv`, `act_inv`, `ch_inv`) and the
substitution/weakening lemmas of `Subst`/`Rename` (`Typed.esubst`, `Typed.subst`, `Typed.rename`,
`Wf.ok`), exactly as the Coq proof does; where the Coq proof leans on `eauto using sta_type` for the
trivially-well-sorted types we spell out the constructor application. The merge means the single
Lean `lam`/`app`/`proj`/`recv`/`send` cases each subsume both Coq `0`/`1` blocks; for the merged
`recv`/`send`/`sig`-building cases the relevance-gated premise `i = .ex → s ⊑ t` is discharged by
`sort_leq_Lgt` (here the codomain sort is always `L`).
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Every typed term has a well-sorted type (Coq `sta_valid`). -/
theorem Typed.validity {Γ m A} (ty : Γ ⊢ m : A) : ∃ s, Γ ⊢ A : .srt s := by
  induction ty using Typed.rec (motive_2 := fun _ _ => True) with
  | srt wf _ => exact ⟨.U, .srt wf⟩
  | var wf hs _ => exact wf.ok hs
  | @pi Γ A B i s r t tyA _ _ _ => exact ⟨.U, .srt tyA.wf⟩
  | @lam Γ A B m i s tym ihm =>
    obtain ⟨t, tyB⟩ := ihm
    cases tyB.wf with
    | @cons _ _ r wf tyA => exact ⟨s, .pi tyA tyB⟩
  | @app Γ A B m n i s tym tyn ihm _ =>
    obtain ⟨_, tyPi⟩ := ihm
    obtain ⟨t, tyB, _⟩ := pi_inv tyPi
    have h := tyB.subst tyn
    asimp at h
    exact ⟨t, h⟩
  | @sig Γ A B i s r t _ _ tyA _ _ _ => exact ⟨.U, .srt tyA.wf⟩
  | @pair Γ A B m n i t tyS tym tyn _ _ _ => exact ⟨t, tyS⟩
  | @proj Γ A B C m n i s t tyC tym tyn _ _ _ =>
    exact ⟨s, tyC.subst tym⟩
  | @fix Γ A m _ _ tym _ =>
    cases tym.wf with
    | @cons _ _ s wf tyA => exact ⟨s, tyA⟩
  | unit wf _ => exact ⟨.U, .srt wf⟩
  | one wf _ => exact ⟨.U, .unit wf⟩
  | bool wf _ => exact ⟨.U, .srt wf⟩
  | tt wf _ => exact ⟨.U, .bool wf⟩
  | ff wf _ => exact ⟨.U, .bool wf⟩
  | @ite Γ A m n1 n2 s tyA tym _ _ _ _ _ _ =>
    have h := tyA.subst tym
    asimp at h
    exact ⟨s, h⟩
  | M _ ih => obtain ⟨_, tyA⟩ := ih; exact ⟨.U, .srt tyA.wf⟩
  | @pure Γ m A tym ihm =>
    obtain ⟨s, tyA⟩ := ihm
    exact ⟨.L, .M tyA⟩
  | @mlet Γ m n A B s tyB tym tyn _ _ _ => exact ⟨.L, .M tyB⟩
  | proto wf _ => exact ⟨.U, .srt wf⟩
  | stop wf _ => exact ⟨.U, .proto wf⟩
  | @act Γ b A B i tyB _ =>
    cases tyB.wf with
    | @cons _ _ s wf _ => exact ⟨.U, .proto wf⟩
  | @ch Γ b A tyA _ => exact ⟨.U, .srt tyA.wf⟩
  | @chan Γ b x A wf tyA _ _ =>
    refine ⟨.L, ?_⟩
    have tyCh : [] ⊢ Term.ch b A : Term.srt .L := .ch tyA
    have h := tyCh.rename wf.agreeRen
    asimp at h
    exact h
  | @fork Γ m A tym ihm =>
    obtain ⟨s, tyIO⟩ := ihm
    cases tyIO.wf with
    | @cons _ _ r wf tyCh =>
      obtain ⟨tyA, _⟩ := ch_inv tyCh
      exact ⟨.L, .M (.ch tyA)⟩
  | @recv Γ r1 r2 A B m i _ tym ihm =>
    obtain ⟨s, tyCh⟩ := ihm
    obtain ⟨tyAct, _⟩ := ch_inv tyCh
    have tyB := act_inv tyAct
    cases tyB.wf with
    | @cons _ _ r wf tyA =>
      exact ⟨.L, .M (.sig (fun _ => sort_leq_Lgt) sort_leq_Lgt tyA (.ch tyB))⟩
  | @send Γ r1 r2 A B m i _ tym ihm =>
    obtain ⟨s, tyCh⟩ := ihm
    obtain ⟨tyAct, _⟩ := ch_inv tyCh
    have tyB := act_inv tyAct
    cases tyB.wf with
    | @cons _ _ r wf tyA =>
      exact ⟨.L, .pi tyA (.M (.ch tyB))⟩
  | @close Γ b m tym _ => exact ⟨.L, .M (.unit tym.wf)⟩
  | @conv Γ A B m s eq tym tyB _ _ => exact ⟨s, tyB⟩
  | nil => trivial
  | cons _ _ _ _ => trivial

/-- Inversion for a `lam` subject against a converted `pi` type (Coq `sta_lam0_invX` /
    `sta_lam1_invX`, merged). -/
lemma lam_invX {Γ A1 A2 B C m i s1 s2 t}
    (tyL : Γ ⊢ .lam A1 m i s1 : C)
    (eq : C ≃ .pi A2 B i s2)
    (tyB : A2 :: Γ ⊢ B : .srt t) :
    A2 :: Γ ⊢ m : B := by
  generalize e : Term.lam A1 m i s1 = n
  rw [e] at tyL
  induction tyL using Typed.rec (motive_2 := fun _ _ => True)
    generalizing A1 A2 B m i s1 s2 t
  all_goals try trivial
  case lam Γ A B0 m0 i0 s0 tym _ =>
    cases e
    obtain ⟨eqA, eqB, _, _⟩ := pi_inj eq
    have wf := tym.wf
    cases wf with
    | @cons _ _ sA wfΓ tyA =>
      have wf := tyB.wf
      cases wf with
      | @cons _ _ sA2 _ tyA2 =>
        apply Typed.ctx_conv (ARS.conv_sym eqA) tyA2
        apply Typed.conv eqB tym
        exact Typed.ctx_conv eqA tyA tyB
  case conv Γ A0 B0 m0 s0 eq1 tym tyB0 ihm _ =>
    exact ihm (ARS.conv_trans eq1 eq) tyB e

/-- Inversion for a `lam` typed at a `pi` type (Coq `sta_lam0_inv` / `sta_lam1_inv`, merged). -/
lemma lam_inv {Γ m A1 A2 B i s1 s2}
    (ty : Γ ⊢ .lam A2 m i s2 : .pi A1 B i s1) :
    A1 :: Γ ⊢ m : B := by
  obtain ⟨_, tyPi⟩ := ty.validity
  obtain ⟨_, tyB, _⟩ := pi_inv tyPi
  exact lam_invX ty .refl tyB

/-- Inversion for a `pair` subject against a converted `sig` type (Coq `sta_pair0_invX` /
    `sta_pair1_invX`, merged). -/
lemma pair_invX {Γ m n i s C} (ty : Γ ⊢ .pair m n i s : C) :
    ∀ {A B r t},
      C ≃ .sig A B i r →
      Γ ⊢ .sig A B i r : .srt t →
      s = r ∧ Γ ⊢ m : A ∧ Γ ⊢ n : B[Chan.var_Chan; m..] := by
  generalize e : Term.pair m n i s = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing m n i s
  all_goals try trivial
  case pair Γ A B m0 n0 i0 t0 tyS tym tyn _ _ _ =>
    cases e
    intro A0 B0 r t1 eq tyS0
    obtain ⟨eA, eB, _, esort⟩ := sig_inj eq
    obtain ⟨s0, r0, _, _, tyA0, tyB0, _⟩ := sig_inv tyS0
    have tym0 : Γ ⊢ m0 : A0 := Typed.conv eA tym tyA0
    refine ⟨esort, tym0, ?_⟩
    have tyB0m := tyB0.subst tym0
    asimp at tyB0m
    exact Typed.conv (conv_subst (m0..) eB) tyn tyB0m
  case conv Γ A0 B0 m0 s0 eq1 tym tyB0 ihm _ =>
    intro A B r t eq tyS
    exact ihm e (ARS.conv_trans eq1 eq) tyS

/-- Inversion for a `pair` typed at a `sig` type (Coq `sta_pair0_inv` / `sta_pair1_inv`, merged). -/
lemma pair_inv {Γ A B m n i s r} (ty : Γ ⊢ .pair m n i s : .sig A B i r) :
    s = r ∧ Γ ⊢ m : A ∧ Γ ⊢ n : B[Chan.var_Chan; m..] := by
  obtain ⟨_, tyS⟩ := ty.validity
  exact pair_invX ty .refl tyS

end TLLC.Static
