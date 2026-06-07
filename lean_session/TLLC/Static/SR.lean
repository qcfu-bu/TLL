import TLLC.Static.Unique
import TLLC.Static.Validity

/-!
# Static subject reduction

Port of `coq_session/sta_sr.v`: subject reduction. The helper lemmas `arity_proto_psr` /
`guarded_psr` (Coq `sta_arity_proto_psr` / `sta_guarded_psr`) show the proof-irrelevant
arity/guardedness predicates are preserved by parallel reduction; `Typed.psr`
(Coq `sta_psr`, parallel subject reduction) is the core big induction over the typing
derivation. `Typed.prd` / `Typed.sr` / `Typed.rd` (Coq `sta_prd` / `sta_sr` / `sta_rd`)
lift it over multi-step parallel reduction, single-step reduction, and multi-step reduction
respectively.

As elsewhere, Coq's implicit/explicit constructor pairs are merged via the `Rlv` tag. Following
the Coq proof, `Typed.psr` runs over the *level-0* typing judgment `Typed0` (whose `lam`/`pair`
rules carry the domain typing), bridging to the main judgment via `Typed.toTyped0` / `Typed0.toTyped`
exactly as Coq does with `sta_sta0_type` / `sta0_sta_type`.
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Protocol arity is preserved by parallel reduction (Coq `sta_arity_proto_psr`). -/
lemma arity_proto_psr {A A'} (st : A ≈> A') (ar : ArityProto A) : ArityProto A' := by
  induction st with
  | proto => exact ar
  | @pi A A' B B' r s _ _ _ ihB => exact ihB ar
  | _ => exact ar.elim

/-- Guardedness is preserved by parallel reduction (Coq `sta_guarded_psr`). -/
lemma guarded_psr {m m'} (st : m ≈> m') : ∀ i, Guarded i m → Guarded i m' := by
  induction st with
  | var => exact fun _ gr => gr
  | srt => exact fun _ gr => gr
  | unit => exact fun _ gr => gr
  | one => exact fun _ gr => gr
  | bool => exact fun _ gr => gr
  | tt => exact fun _ gr => gr
  | ff => exact fun _ gr => gr
  | proto => exact fun _ gr => gr
  | stop => exact fun _ gr => gr
  | box => exact fun _ gr => gr
  | chan => exact fun _ gr => gr
  | pi _ _ ihA ihB => exact fun i gr => ⟨ihA i gr.1, ihB (i + 1) gr.2⟩
  | lam _ _ ihA ihm => exact fun i gr => ⟨ihA i gr.1, ihm (i + 1) gr.2⟩
  | app _ _ ihm ihn => exact fun i gr => ⟨ihm i gr.1, ihn i gr.2⟩
  | sig _ _ ihA ihB => exact fun i gr => ⟨ihA i gr.1, ihB (i + 1) gr.2⟩
  | pair _ _ ihm ihn => exact fun i gr => ⟨ihm i gr.1, ihn i gr.2⟩
  | proj _ _ _ ihA ihm ihn =>
    exact fun i gr => ⟨ihA (i + 1) gr.1, ihm i gr.2.1, ihn (i + 2) gr.2.2⟩
  | fix _ _ ihA ihm => exact fun i gr => ⟨ihA i gr.1, ihm (i + 1) gr.2⟩
  | ite _ _ _ _ ihA ihm ihn1 ihn2 =>
    exact fun i gr => ⟨ihA (i + 1) gr.1, ihm i gr.2.1, ihn1 i gr.2.2.1, ihn2 i gr.2.2.2⟩
  | M _ ihA => exact fun i gr => ihA i gr
  | pure _ ihm => exact fun i gr => ihm i gr
  | mlet _ _ ihm ihn => exact fun i gr => ⟨ihm i gr.1, ihn (i + 1) gr.2⟩
  | act _ _ ihA _ => exact fun i gr => ihA i gr
  | ch _ ihA => exact fun i gr => ihA i gr
  | fork _ _ ihA ihm => exact fun i gr => ⟨ihA i gr.1, ihm (i + 1) gr.2⟩
  | recv _ ihm => exact fun i gr => ihm i gr
  | send _ ihm => exact fun i gr => ihm i gr
  | close _ ihm => exact fun i gr => ihm i gr
  | @beta A m m' n n' r s _ _ ihm ihn =>
    intro i gr
    obtain ⟨⟨_, gm⟩, gn⟩ := gr
    apply subst_guarded (i := i + 1) (j := i) _ (ihm (i + 1) gm)
    rintro (_ | x) neq
    · exact ihn i gn
    · intro e; exact neq (by omega)
  | @projE A m1 m1' m2 m2' n n' r s _ _ _ ihm1 ihm2 ihn =>
    intro i gr
    obtain ⟨_, ⟨gm1, gm2⟩, gn⟩ := gr
    apply subst_guarded (i := i + 2) (j := i) _ (ihn (i + 2) gn)
    rintro (_ | _ | x) neq
    · exact ihm2 i gm2
    · exact ihm1 i gm1
    · intro e; exact neq (by omega)
  | @fixE A A' m m' _ _ ihA ihm =>
    intro i gr
    obtain ⟨gA, gm⟩ := gr
    apply subst_guarded (i := i + 1) (j := i) _ (ihm (i + 1) gm)
    rintro (_ | x) neq
    · exact ⟨ihA i gA, ihm (i + 1) gm⟩
    · intro e; exact neq (by omega)
  | @mletE m m' n n' _ _ ihm ihn =>
    intro i gr
    obtain ⟨gm, gn⟩ := gr
    apply subst_guarded (i := i + 1) (j := i) _ (ihn (i + 1) gn)
    rintro (_ | x) neq
    · exact ihm i gm
    · intro e; exact neq (by omega)
  | iteT _ ih => exact fun i gr => ih i gr.2.2.1
  | iteF _ ih => exact fun i gr => ih i gr.2.2.2

/-- Parallel subject reduction (Coq `sta_psr`). -/
theorem Typed.psr {Γ m n A} (ty : Γ ⊢ m : A) (st : m ≈> n) : Γ ⊢ n : A := by
  have ty0 := ty.toTyped0
  clear ty
  suffices h : Typed0 Γ n A from h.toTyped
  induction ty0 using Typed0.rec (motive_2 := fun _ _ => True) generalizing n with
  | srt wf _ => cases st; exact .srt wf
  | var wf hs _ => cases st; exact .var wf hs
  | @pi Γ A B i s r t tyA tyB ihA ihB =>
    cases st with
    | @pi _ A2 _ B2 _ _ pA pB =>
      have tyA' := ihA pA
      have tyB' := ihB pB
      have tyB'' : A2 :: Γ ⊢ B2 : Term.srt t :=
        Typed.ctx_conv (ARS.conv1i pA) tyA'.toTyped tyB'.toTyped
      exact .pi tyA' tyB''.toTyped0
  | @lam Γ A B m i s r tyA tym ihA ihm =>
    cases st with
    | @lam _ A2 _ m2 _ _ pA pm =>
      have tyA' := ihA pA
      have tym' := ihm pm
      -- `tym'` is the body typing `A :: Γ ⊢ m2 : B`; validity gives the codomain sort
      obtain ⟨t, tyB⟩ := tym'.toTyped.validity
      apply Typed0.conv (B := .pi A B i s)
      · exact ARS.conv_sym (conv_pi (ARS.conv1 pA) ARS.Conv.refl)
      · refine .lam tyA' ?_
        apply Typed.toTyped0
        exact Typed.ctx_conv (ARS.conv1i pA) tyA'.toTyped tym'.toTyped
      · exact Typed0.pi tyA tyB.toTyped0
  | @app Γ A B m n i s tym tyn ihm ihn =>
    cases st with
    | app pm pn =>
      have tym' := ihm pm
      have tyn' := ihn pn
      obtain ⟨_, tyPi⟩ := tym.toTyped.validity
      obtain ⟨r, tyB, _⟩ := pi_inv tyPi
      have tyBn : Γ ⊢ B[Chan.var_Chan; n..] : Term.srt r :=
        Typed.esubst rfl rfl tyB tyn.toTyped
      exact Typed0.conv (conv_beta (ARS.conv1i pn)) (.app tym' tyn') tyBn.toTyped0
    | @beta A0 m0 m' n0 n' _ _ pm pn =>
      -- redex: app (lam A0 m0) n0 ≈> m'[n'..]
      have tym' := ihm (PStep.lam (pstep_refl A0) pm)
      have tyn' := ihn pn
      obtain ⟨_, tyP⟩ := tym'.toTyped.validity
      obtain ⟨_, tyB, _⟩ := pi_inv tyP
      have tym0 := lam_inv tym'.toTyped
      have tyBn := tyB.subst tyn.toTyped
      asimp at tyBn
      apply Typed.toTyped0
      refine Typed.conv (A := B[Chan.var_Chan; n'..]) (conv_beta (ARS.conv1i pn)) ?_ tyBn
      exact Typed.esubst rfl rfl tym0 tyn'.toTyped
  | @sig Γ A B i s r t ord1 ord2 tyA tyB ihA ihB =>
    cases st with
    | sig pA pB =>
      have tyA' := ihA pA
      have tyB' := ihB pB
      refine .sig ord1 ord2 tyA' ?_
      apply Typed.toTyped0
      exact Typed.ctx_conv (ARS.conv1i pA) tyA'.toTyped tyB'.toTyped
  | @pair Γ A B m n i t tyS tym tyn ihS ihm ihn =>
    cases st with
    | @pair _ m2 _ _ _ _ pm pn =>
      have tym' := ihm pm
      have tyn' := ihn pn
      obtain ⟨s, r, _, _, tyA, tyB, _⟩ := sig_inv tyS.toTyped
      have tyBm2 : Γ ⊢ B[Chan.var_Chan; m2..] : Term.srt r :=
        Typed.esubst rfl rfl tyB (tym'.toTyped)
      refine .pair tyS tym' ?_
      exact Typed0.conv (conv_beta (ARS.conv1 pm)) tyn' tyBm2.toTyped0
  | @proj Γ A B C m n i s t tyC tym tyn ihC ihm ihn =>
    cases st with
    | @proj _ C2 _ m2 _ n2 pC pm pn =>
      -- congruence: proj C m n ≈> proj C2 m2 n2
      have tyC' := ihC pC
      have tym' := ihm pm
      have tyn' := ihn pn
      cases tyC.toTyped.wf with
      | @cons _ _ s0 wfΓ tySig =>
        obtain ⟨s1, r, ord1, ord2, tyA, tyB, _⟩ := sig_inv tySig
        have wf2 : Wf (B :: A :: Γ) := .cons (.cons wfΓ tyA) tyB
        have agr0 : (B :: A :: Γ) ⊢ funcomp Term.var_Term (· + 2) ⊣ Γ := by
          have h := ((AgreeSubst.refl wfΓ).wk2 (s := s1) tyA).wk2 (s := r) tyB
          rwa [show (fun x => ((Term.var_Term x)⟨(id : Nat → Nat); ↑⟩)⟨(id : Nat → Nat); ↑⟩)
                = funcomp Term.var_Term (· + 2) from by funext x; asimp] at h
        have tySig' := (Typed.sig ord1 ord2 tyA tyB).substitution agr0
        asimp at tySig'
        have tyv1 : (B :: A :: Γ) ⊢ Term.var_Term 1
            : A[Chan.var_Chan; funcomp Term.var_Term (· + 2)] := by
          have h := Typed.var wf2 (Has.succ Has.zero)
          rwa [show A⟨(id : Nat → Nat); ↑⟩⟨(id : Nat → Nat); ↑⟩
                = A[Chan.var_Chan; funcomp Term.var_Term (· + 2)] from by asimp; substify] at h
        have tyv0 : (B :: A :: Γ) ⊢ Term.var_Term 0
            : (B[Chan.var_Chan; up_Term_Term (funcomp Term.var_Term (· + 2))])[Chan.var_Chan;
                (Term.var_Term 1)..] := by
          have h := Typed.var wf2 (Has.zero (A := B))
          rwa [show B⟨(id : Nat → Nat); ↑⟩
                = (B[Chan.var_Chan; up_Term_Term (funcomp Term.var_Term (· + 2))])[Chan.var_Chan;
                  (Term.var_Term 1)..] from by
                  asimp; substify; congr 1; funext x; rcases x with _ | x <;> rfl] at h
        have agr : (B :: A :: Γ)
            ⊢ Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)
            ⊣ (Term.sig A B i t :: Γ) :=
          agr0.wk1 (A := Term.sig A B i t) (Typed.pair tySig' tyv1 tyv0)
        -- well-sortedness of the reduced-motive substitution
        have hwit := (tyC'.toTyped).substitution agr
        -- retype the branch under the reduced motive
        have eqn : C[Chan.var_Chan;
              Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)]
            ≃ C2[Chan.var_Chan;
              Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)] :=
          conv_subst _ (ARS.conv1 pC)
        have tyn'' := Typed.conv eqn tyn'.toTyped hwit
        -- convert the projection's result type back to `C[m/]`
        have eqC : C2[Chan.var_Chan; m2..] ≃ C[Chan.var_Chan; m..] :=
          ARS.conv_trans (conv_beta (ARS.conv1i pm)) (conv_subst (m..) (ARS.conv1i pC))
        apply Typed.toTyped0
        exact .conv eqC (.proj tyC'.toTyped tym'.toTyped tyn'') (tyC.toTyped.subst tym.toTyped)
    | @projE A0 m1 m1' m2 m2' n0 n' r s pm1 pm2 pn =>
      -- redex: proj C (pair m1 m2 r s) n ≈> n'[m2' .: m1' .: var]
      -- the scrutinee `pair m1 m2 r s` is typed at `sig A B i t`, forcing r = i.
      have hri : r = i := by
        cases r <;> cases i
        · rfl
        · exact (pair_sig_false tym.toTyped ARS.Conv.refl nofun).elim
        · exact (pair_sig_false tym.toTyped ARS.Conv.refl nofun).elim
        · rfl
      subst hri
      have tym' := ihm (PStep.pair pm1 pm2)
      have tyn' := ihn pn
      obtain ⟨hst, tym1, tym2⟩ := pair_inv tym'.toTyped
      subst hst
      have tyC' := tyC.toTyped.subst tym.toTyped
      asimp at tyC'
      apply Typed.toTyped0
      apply Typed.conv (A := C[Chan.var_Chan; (Term.pair m1' m2' r s)..])
      · exact conv_beta (ARS.conv1i (PStep.pair pm1 pm2))
      · rw [show C[Chan.var_Chan; (Term.pair m1' m2' r s)..]
              = (C[Chan.var_Chan;
                  Term.pair (.var_Term 1) (.var_Term 0) r s .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                  m2' .: m1' .: Term.var_Term]
              from by asimp; congr 1]
        apply Typed.substitution tyn'.toTyped
        apply AgreeSubst.wk1
        · apply AgreeSubst.wk1 (AgreeSubst.refl tym1.wf)
          asimp; exact tym1
        · asimp; exact tym2
      · exact tyC'
  | @fix Γ A m s ar gr tyA tym ihA ihm =>
    -- shared: reduced fix is well typed (Coq's transformed `tym'`)
    have mkFix : ∀ {A2 m2}, A ≈> A2 → m ≈> m2 →
        Typed0 Γ A2 (.srt s) → Typed0 (A :: Γ) m2 (A⟨(id : Nat → Nat); ↑⟩) →
        Γ ⊢ Term.fix A2 m2 : A2 := by
      intro A2 m2 pA pm tyA' tym'
      have tymt'' : A2 :: Γ ⊢ m2 : A2⟨(id : Nat → Nat); ↑⟩ := by
        apply Typed.conv (A := A⟨(id : Nat → Nat); ↑⟩)
        · exact conv_ren Nat.succ (ARS.conv1 pA)
        · exact Typed.ctx_conv (ARS.conv1i pA) tyA'.toTyped tym'.toTyped
        · exact (tyA'.toTyped).weaken tyA'.toTyped
      exact Typed.fix (arity_proto_psr pA ar) (guarded_psr pm 0 gr) tymt''
    cases st with
    | @fix _ A2 _ m2 pA pm =>
      -- congruence
      apply Typed0.conv (B := A)
      · exact ARS.conv1i pA
      · exact (mkFix pA pm (ihA pA) (ihm pm)).toTyped0
      · exact tyA
    | @fixE _ A2 _ m2 pA pm =>
      -- redex: fix A m ≈> m2[(fix A2 m2)..]
      have tyA' := ihA pA
      have tym' := ihm pm
      have tyFix := mkFix pA pm tyA' tym'
      have tymt'' : A2 :: Γ ⊢ m2 : A2⟨(id : Nat → Nat); ↑⟩ := by
        apply Typed.conv (A := A⟨(id : Nat → Nat); ↑⟩)
        · exact conv_ren Nat.succ (ARS.conv1 pA)
        · exact Typed.ctx_conv (ARS.conv1i pA) tyA'.toTyped tym'.toTyped
        · exact (tyA'.toTyped).weaken tyA'.toTyped
      apply Typed.toTyped0
      apply Typed.conv (A := A2)
      · exact ARS.conv1i pA
      · have h := tymt''.subst tyFix
        asimp at h
        exact h
      · exact tyA.toTyped
  | unit wf _ => cases st; exact .unit wf
  | one wf _ => cases st; exact .one wf
  | bool wf _ => cases st; exact .bool wf
  | tt wf _ => cases st; exact .tt wf
  | ff wf _ => cases st; exact .ff wf
  | @ite Γ A m n1 n2 s tyA tym tyn1 tyn2 ihA ihm ihn1 ihn2 =>
    cases st with
    | @ite _ A2 _ m2 _ _ _ _ pA pm pn1 pn2 =>
      have tyA' := ihA pA
      have tym' := ihm pm
      have tyn1' := ihn1 pn1
      have tyn2' := ihn2 pn2
      have wf := tym.toTyped.wf
      have tyA'TT := tyA'.toTyped.subst (Typed.tt wf)
      have tyA'FF := tyA'.toTyped.subst (Typed.ff wf)
      asimp at tyA'TT tyA'FF
      have tyAm : Γ ⊢ A[Chan.var_Chan; m..] : Term.srt s :=
        Typed.esubst rfl rfl tyA.toTyped tym.toTyped
      apply Typed0.conv (A := A2[Chan.var_Chan; m2..]) (B := A[Chan.var_Chan; m..])
      · exact ARS.conv_trans (conv_beta (ARS.conv1i pm)) (conv_subst _ (ARS.conv1i pA))
      · refine .ite tyA' tym' ?_ ?_
        · apply Typed0.conv (B := A2[Chan.var_Chan; Term.tt..])
          · exact conv_subst _ (ARS.conv1 pA)
          · exact tyn1'
          · exact tyA'TT.toTyped0
        · apply Typed0.conv (B := A2[Chan.var_Chan; Term.ff..])
          · exact conv_subst _ (ARS.conv1 pA)
          · exact tyn2'
          · exact tyA'FF.toTyped0
      · exact tyAm.toTyped0
    | iteT pn1 =>
      -- redex: ite A tt n1 n2 ≈> n1' (type A[tt/] matches the branch IH directly)
      exact ihn1 pn1
    | iteF pn2 =>
      -- redex: ite A ff n1 n2 ≈> n2'
      exact ihn2 pn2
  | @M Γ A s tyA ihA => cases st with | M pA => exact .M (ihA pA)
  | @pure Γ m A tym ihm => cases st with | pure pm => exact .pure (ihm pm)
  | @mlet Γ m n A B s tyB tym tyn ihB ihm ihn =>
    cases st with
    | mlet pm pn =>
      exact .mlet tyB (ihm pm) (ihn pn)
    | @mletE m0 m' n0 n' pm pn =>
      -- redex: mlet (pure m0) n0 ≈> n'[m'..]
      have ihm' := ihm (PStep.pure pm)
      have ihn' := ihn pn
      obtain ⟨A0, tym', eq⟩ := pure_inv ihm'.toTyped
      have wf := ihn'.toTyped.wf
      cases wf with
      | @cons _ _ s' _ tyA0 =>
        have tym'' := Typed.conv (ARS.conv_sym (M_inj eq)) tym' tyA0
        have tynm := ihn'.toTyped.subst tym''
        rw [show (Term.M (B⟨(id : Nat → Nat); ↑⟩))[Chan.var_Chan; m'..] = Term.M B
              from by show Term.M _ = Term.M _; congr 1; asimp] at tynm
        exact tynm.toTyped0
  | proto wf _ => cases st; exact .proto wf
  | stop wf _ => cases st; exact .stop wf
  | @act Γ b A B i s tyA tyB ihA ihB =>
    cases st with
    | act pA pB =>
      have tyA' := ihA pA
      have tyB' := ihB pB
      refine .act tyA' ?_
      apply Typed.toTyped0
      exact Typed.ctx_conv (ARS.conv1i pA) tyA'.toTyped tyB'.toTyped
  | @ch Γ b A tyA ihA => cases st with | ch pA => exact .ch (ihA pA)
  | @chan Γ b x A wf tyA ih ihA => cases st; exact .chan wf tyA
  | @fork Γ A m s tyCh tym ihCh ihm =>
    cases st with
    | fork pA pm =>
      obtain ⟨tyA, _⟩ := ch_inv tyCh.toTyped
      have tyCh' := ihCh (PStep.ch (b := true) pA)
      have tym' := ihm pm
      apply Typed0.conv (B := Term.M (.ch false A))
      · exact conv_M (conv_ch (ARS.conv1i pA))
      · refine .fork tyCh' ?_
        apply Typed.toTyped0
        apply Typed.ctx_conv (conv_ch (ARS.conv1i pA)) tyCh'.toTyped tym'.toTyped
      · exact .M (.ch tyA.toTyped0)
  | @recv Γ r1 r2 A B m i e tym ihm =>
    cases st with | recv pm => exact .recv e (ihm pm)
  | @send Γ r1 r2 A B m i e tym ihm =>
    cases st with | send pm => exact .send e (ihm pm)
  | @close Γ b m tym ihm =>
    cases st with | close pm => exact .close (ihm pm)
  | conv c tym tyB ihm ihB =>
    exact .conv c (ihm st) tyB
  | nil => trivial
  | cons _ _ _ _ => trivial

/-- Parallel multi-step subject reduction (Coq `sta_prd`). -/
theorem Typed.prd {Γ m n A} (ty : Γ ⊢ m : A) (rd : m ≈>* n) : Γ ⊢ n : A := by
  induction rd with
  | refl => exact ty
  | tail _ st ih => exact ih.psr st

/-- Single-step subject reduction (Coq `sta_sr`). -/
theorem Typed.sr {Γ m n A} (ty : Γ ⊢ m : A) (st : m ~> n) : Γ ⊢ n : A :=
  ty.psr (step_pstep st)

/-- Multi-step subject reduction (Coq `sta_rd`). -/
theorem Typed.rd {Γ m n A} (ty : Γ ⊢ m : A) (rd : m ~>* n) : Γ ⊢ n : A :=
  ty.prd (red_pred rd)

end TLLC.Static
