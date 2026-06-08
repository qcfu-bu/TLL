import TLLC.Dynamic.Inversion
import TLLC.Dynamic.Step

/-!
# Dynamic subject reduction

Port of `coq_session/dyn_sr.v`: subject reduction for the dynamic (call-by-value, linear) reduction
relation `m ~>> n`. The helper `Step.toStatic` (Coq `dyn_sta_step`) lifts a dynamic step to a static
multi-step reduction; `Has.typed`/`Has.key` (Coq `dyn_has_type`/`dyn_has_key`) are the linear-lookup
bridges; `Typed.val_stability` (Coq `dyn_val_stability`) shows a value's context keys match its type
sort; `Typed.pure_empty` (Coq `dyn_pure_empty`) shows a pure process context is empty. The core
theorem `Typed.sr` (Coq `dyn_sr`) is subject reduction over a closed term (`Θ ⨾ [] ⨾ [] ⊢ m : A`),
lifted to multi-step by `Typed.rd` (Coq `dyn_rd`).

As elsewhere the unified AST collapses Coq's implicit/explicit constructor pairs via the `Rlv`/`Bool`
tag, and the inversion lemmas of `Inversion.lean` plus the substitution lemmas of `Subst.lean`
(`Typed.subst0`/`subst1`/`substitution`) drive the redex cases, mirroring `Static/SR.lean`.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- A dynamic step is a static multi-step reduction (Coq `dyn_sta_step`). -/
lemma Step.toStatic {m n : Term} (st : m ~>> n) : Static.Red m n := by
  induction st with
  | appL _ ih => exact ARS.star_hom (Term.app · _ _) _ (fun _ _ => .appL) _ _ ih
  | appR _ ih => exact ARS.star_hom (Term.app _ · _) _ (fun _ _ => .appR) _ _ ih
  | betaIm => exact ARS.star1 .beta
  | betaEx _ => exact ARS.star1 .beta
  | pairL _ ih => exact ARS.star_hom (Term.pair · _ _ _) _ (fun _ _ => .pairL) _ _ ih
  | pairR _ ih => exact ARS.star_hom (Term.pair _ · _ _) _ (fun _ _ => .pairR) _ _ ih
  | projM _ ih => exact ARS.star_hom (Term.proj _ · _) _ (fun _ _ => .projM) _ _ ih
  | projE _ => exact ARS.star1 .projE
  | fixE => exact ARS.star1 .fixE
  | iteM _ ih => exact ARS.star_hom (Term.ite _ · _ _) _ (fun _ _ => .iteM) _ _ ih
  | iteT => exact ARS.star1 .iteT
  | iteF => exact ARS.star1 .iteF
  | pure _ ih => exact ARS.star_hom Term.pure _ (fun _ _ => .pure) _ _ ih
  | mletL _ ih => exact ARS.star_hom (Term.mlet · _) _ (fun _ _ => .mletL) _ _ ih
  | mletE _ => exact ARS.star1 .mletE
  | recv _ ih => exact ARS.star_hom (Term.recv · _) _ (fun _ _ => .recv) _ _ ih
  | send _ ih => exact ARS.star_hom (Term.send · _) _ (fun _ _ => .send) _ _ ih
  | close _ ih => exact ARS.star_hom (Term.close _ ·) _ (fun _ _ => .close) _ _ ih

/-- A dynamic step yields a static conversion of the endpoints (Coq `dyn_sta_step` + `star_conv`). -/
lemma Step.toConv {m n : Term} (st : m ~>> n) : m ≃ n :=
  ARS.star_conv (Static.red_pred st.toStatic)

/-- The type of a linear lookup is well-sorted (Coq `dyn_has_type`). -/
lemma Has.typed {Γ Δ x s A} (hs : Has Δ x s A) (wf : Wf Γ Δ) : Γ ⊢ A : .srt s := by
  induction hs generalizing Γ with
  | @zero Δ A s k =>
    cases wf with
    | cons _ tyA =>
      exact Static.Typed.eweaken rfl (by asimp) tyA tyA
  | @succ Δ A B x s hs ih =>
    cases wf with
    | cons wf' tyB =>
      have tyA := ih wf'
      exact Static.Typed.eweaken rfl (by asimp) tyA tyB
  | @null Δ A x s hs ih =>
    cases wf with
    | null wf' tyB =>
      have tyA := ih wf'
      exact Static.Typed.eweaken rfl (by asimp) tyA tyB

/-- A linear lookup at sort `s` makes the context have key `s` (Coq `dyn_has_key`). -/
lemma Has.key {Δ x s A} (hs : Has Δ x s A) : Δ ▷ s := by
  induction hs with
  | @zero Δ A s k =>
    cases s with
    | U => exact .U _ k
    | L => exact Key.impure
  | @succ Δ A B x s hs ih =>
    cases s with
    | U => exact .U _ ih
    | L => exact Key.impure
  | @null Δ A x s hs ih =>
    cases s with
    | U => exact .null ih
    | L => exact Key.impure

/-- A value's context keys match its type's sort (Coq `dyn_val_stability`). -/
lemma Typed.val_stability {Θ Γ Δ m A s}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ m : A) (tyA : Γ ⊢ A : .srt s) (vl : Val m) : Θ ▷ₚ s ∧ Δ ▷ s := by
  cases s with
  | L => exact ⟨PKey.impure, Key.impure⟩
  | U =>
    induction ty with
    | @var Θ Γ Δ x s A emp wf shs dhs =>
      have tyAs := dhs.typed wf
      have e := Static.Typed.unicity tyA tyAs
      subst e
      exact ⟨emp.key, dhs.key⟩
    | @lamIm Θ Γ Δ A B m s k1 k2 tym ihm =>
      obtain ⟨_, _, e⟩ := Static.pi_inv tyA
      have e := Static.sort_inj e; subst e
      exact ⟨k1, k2⟩
    | @lamEx Θ Γ Δ A B m s t k1 k2 tym ihm =>
      obtain ⟨_, _, e⟩ := Static.pi_inv tyA
      have e := Static.sort_inj e; subst e
      exact ⟨k1, k2⟩
    | @appIm Θ Γ Δ A B m n s tym tyn ihm =>
      cases vl with
      | thunk h =>
        cases h with
        | appSendIm =>
          obtain ⟨r1, r2, A0, B0, _, eqP, tyv⟩ := sendIm_inv tym
          obtain ⟨eqA, eqB, _, _⟩ := Static.pi_inj eqP
          obtain ⟨_, tyCh⟩ := tyv.validity
          obtain ⟨tyAct, _⟩ := Static.ch_inv tyCh
          have tyB0 := Static.act_inv tyAct
          obtain ⟨_, tyA0⟩ := tyn.validity
          have tyB0 := Static.Typed.ctx_conv eqA tyA0 tyB0
          have tyIO := Static.Typed.M (Static.Typed.ch (b := r1) (Static.Typed.subst tyB0 tyn))
          obtain ⟨x, rd1, rd2⟩ := Static.church_rosser _ _
            (show B[Chan.var_Chan; n..] ≃ (Term.M (.ch r1 B0))[Chan.var_Chan; n..] from
              Static.conv_subst _ eqB)
          exact absurd (Static.Typed.unicity
            (Static.Typed.prd tyA rd1) (by asimp at tyIO ⊢; exact Static.Typed.prd tyIO rd2))
            (by simp)
    | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym tyn ihm ihn =>
      cases vl with
      | thunk h =>
        cases h with
        | appSendEx hv2 =>
          obtain ⟨r1, r2, A0, B0, _, eqP, tyv⟩ := sendEx_inv tym
          obtain ⟨eqA, eqB, _, _⟩ := Static.pi_inj eqP
          obtain ⟨_, tyCh⟩ := tyv.validity
          obtain ⟨tyAct, _⟩ := Static.ch_inv tyCh
          have tyB0 := Static.act_inv tyAct
          obtain ⟨_, tyA0⟩ := tyn.validity
          have tyB0 := Static.Typed.ctx_conv eqA tyA0 tyB0
          have tyIO := Static.Typed.M (Static.Typed.ch (b := r1) (Static.Typed.subst tyB0 tyn.toStatic))
          obtain ⟨x, rd1, rd2⟩ := Static.church_rosser _ _
            (show B[Chan.var_Chan; n..] ≃ (Term.M (.ch r1 B0))[Chan.var_Chan; n..] from
              Static.conv_subst _ eqB)
          exact absurd (Static.Typed.unicity
            (Static.Typed.prd tyA rd1) (by asimp at tyIO ⊢; exact Static.Typed.prd tyIO rd2))
            (by simp)
    | @pairIm Θ Γ Δ A B m n t tyS tym tyn ihn =>
      obtain ⟨s, r, _, ord, tyA0, tyB, e⟩ := Static.sig_inv tyA
      have e := Static.sort_inj e; subst e
      cases vl with
      | pairIm hv2 =>
        apply ihn hv2
        cases ord with | U =>
        apply Static.Typed.esubst rfl _ tyB tym
        asimp
      | thunk h => cases h
    | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym tyn ihm ihn =>
      obtain ⟨s, r, ord1, ord2, tyA0, tyB, e⟩ := Static.sig_inv tyA
      have e := Static.sort_inj e; subst e
      cases vl with
      | pairEx hv1 hv2 =>
        cases ord1 rfl with | U =>
        cases ord2 with | U =>
        obtain ⟨k1, k2⟩ := ihm hv1 tyA0
        obtain ⟨k3, k4⟩ := ihn hv2 (Static.Typed.subst tyB tym.toStatic)
        exact ⟨mrg1.key_image k1 k3, mrg2.key_image k2 k4⟩
      | thunk h => cases h
    | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym tyn ihm ihn =>
      cases vl with | thunk h => cases h
    | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym tyn ihm ihn =>
      cases vl with | thunk h => cases h
    | @one Θ Γ Δ emp wf k => exact ⟨emp.key, k⟩
    | @tt Θ Γ Δ emp wf k => exact ⟨emp.key, k⟩
    | @ff Θ Γ Δ emp wf k => exact ⟨emp.key, k⟩
    | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA' tym tyn1 tyn2 ihm ihn1 ihn2 =>
      cases vl with | thunk h => cases h
    | @pure Θ Γ Δ m A tym ihm =>
      obtain ⟨_, _, e⟩ := Static.M_inv tyA
      exact absurd (Static.sort_inj e) (by simp)
    | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym tyn ihm ihn =>
      cases vl with
      | thunk h =>
        obtain ⟨_, _, e⟩ := Static.M_inv tyA
        exact absurd (Static.sort_inj e) (by simp)
    | @chan Θ Γ Δ r x A js wf k tyA' =>
      obtain ⟨_, e⟩ := Static.ch_inv tyA
      exact absurd (Static.sort_inj e) (by simp)
    | @fork Θ Γ Δ A m tym ihm =>
      cases vl with
      | thunk h =>
        obtain ⟨_, _, e⟩ := Static.M_inv tyA
        exact absurd (Static.sort_inj e) (by simp)
    | @recv Θ Γ Δ r1 r2 A B m i e tym ihm =>
      cases vl with
      | thunk h =>
        obtain ⟨_, _, e⟩ := Static.M_inv tyA
        exact absurd (Static.sort_inj e) (by simp)
    | @send Θ Γ Δ r1 r2 A B m i e tym ihm =>
      obtain ⟨_, _, e⟩ := Static.pi_inv tyA
      exact absurd (Static.sort_inj e) (by simp)
    | @close Θ Γ Δ b m tym ihm =>
      cases vl with
      | thunk h =>
        obtain ⟨_, _, e⟩ := Static.M_inv tyA
        exact absurd (Static.sort_inj e) (by simp)
    | @conv Θ Γ Δ A B m s eq tym tyB ihm =>
      obtain ⟨r, tyA0⟩ := tym.validity
      obtain ⟨C, rd1, rd2⟩ := Static.church_rosser _ _ eq
      have tyCr := Static.Typed.prd tyA0 rd1
      have tyCU := Static.Typed.prd tyA rd2
      have e := Static.Typed.unicity tyCr tyCU
      subst e
      exact ihm vl tyA0

/-- A pure process context is empty (Coq `dyn_pure_empty`). -/
lemma Typed.pure_empty {Θ Γ Δ m A}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ m : A) (k : Θ ▷ₚ Srt.U) : PEmpty Θ := by
  induction ty with
  | var emp _ _ _ => exact emp
  | lamIm _ _ _ ih => exact ih k
  | lamEx _ _ _ ih => exact ih k
  | appIm _ _ ihm => exact ihm k
  | appEx mrg1 _ _ _ ihm ihn =>
    obtain ⟨k1, k2⟩ := mrg1.pure_split k
    exact mrg1.empty_image (ihm k1) (ihn k2)
  | pairIm _ _ _ ihn => exact ihn k
  | pairEx mrg1 _ _ _ _ ihm ihn =>
    obtain ⟨k1, k2⟩ := mrg1.pure_split k
    exact mrg1.empty_image (ihm k1) (ihn k2)
  | projIm mrg1 _ _ _ _ ihm ihn =>
    obtain ⟨k1, k2⟩ := mrg1.pure_split k
    exact mrg1.empty_image (ihm k1) (ihn k2)
  | projEx mrg1 _ _ _ _ ihm ihn =>
    obtain ⟨k1, k2⟩ := mrg1.pure_split k
    exact mrg1.empty_image (ihm k1) (ihn k2)
  | one emp _ _ => exact emp
  | tt emp _ _ => exact emp
  | ff emp _ _ => exact emp
  | ite mrg1 _ _ _ _ _ ihm ihn1 _ =>
    obtain ⟨k1, k2⟩ := mrg1.pure_split k
    exact mrg1.empty_image (ihm k1) (ihn1 k2)
  | pure _ ihm => exact ihm k
  | mlet mrg1 _ _ _ _ ihm ihn =>
    obtain ⟨k1, k2⟩ := mrg1.pure_split k
    exact mrg1.empty_image (ihm k1) (ihn k2)
  | chan js _ k1 _ => exact absurd k (js.not_pure)
  | fork _ ihm => exact ihm k
  | recv _ _ ihm => exact ihm k
  | send _ _ ihm => exact ihm k
  | close _ ihm => exact ihm k
  | conv _ _ _ ihm => exact ihm k

/-- Dynamic subject reduction over a closed term (Coq `dyn_sr`). -/
theorem Typed.sr {Θ m n A}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) (st : m ~>> n) :
    Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ n : A := by
  generalize e1 : ([] : Static.Ctx) = Γ at ty
  generalize e2 : ([] : Ctx) = Δ at ty
  induction ty generalizing n with
  | @var Θ Γ Δ x s A emp wf shs dhs => cases st
  | @lamIm Θ Γ Δ A B m s k1 k2 tym ihm => cases st
  | @lamEx Θ Γ Δ A B m s t k1 k2 tym ihm => cases st
  | @appIm Θ Γ Δ A B m n s tym tyn ihm =>
    subst e1; subst e2
    cases st with
    | appL stm =>
      exact .appIm (ihm stm rfl rfl) tyn
    | betaIm =>
      have tym0 := lamIm_inv tym
      exact tym0.subst0 tyn
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym tyn ihm ihn =>
    subst e1; subst e2
    cases mrg2
    cases st with
    | appL stm =>
      exact .appEx mrg1 .nil (ihm stm rfl rfl) tyn
    | appR stn =>
      have tyn' := ihn stn rfl rfl
      obtain ⟨_, tyP⟩ := tym.validity
      obtain ⟨r, tyB, _⟩ := Static.pi_inv tyP
      apply Typed.conv
      · exact Static.conv_beta (ARS.conv_sym (Step.toConv stn))
      · exact .appEx mrg1 .nil tym tyn'
      · have h := Static.Typed.subst tyB tyn.toStatic
        asimp at h ⊢
        exact h
    | betaEx hv =>
      obtain ⟨r, tym0⟩ := lamEx_inv tym
      have wf := tym0.wf
      cases wf with
      | @cons _ _ _ _ _ tyA =>
        obtain ⟨k1, k2⟩ := tyn.val_stability tyA hv
        exact Typed.subst1 k1 mrg1 k2 .nil tym0 tyn
  | @pairIm Θ Γ Δ A B m n t tyS tym tyn ihn =>
    subst e1; subst e2
    cases st with
    | pairR stn =>
      obtain ⟨s, r, _, ord, tyA, tyB, _⟩ := Static.sig_inv tyS
      exact .pairIm tyS tym (ihn stn rfl rfl)
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym tyn ihm ihn =>
    subst e1; subst e2
    cases mrg2
    cases st with
    | pairL stm =>
      obtain ⟨s, r, ord1, ord2, tyA, tyB, _⟩ := Static.sig_inv tyS
      have tym' := ihm stm rfl rfl
      refine .pairEx mrg1 .nil tyS tym' ?_
      apply Typed.conv (Static.conv_beta (Step.toConv stm)) tyn
      exact Static.Typed.esubst rfl rfl tyB tym'.toStatic
    | pairR stn =>
      exact .pairEx mrg1 .nil tyS tym (ihn stn rfl rfl)
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym tyn ihm ihn =>
    subst e1; subst e2
    cases mrg2
    cases st with
    | projM stm =>
      apply Typed.conv
      · exact Static.conv_beta (ARS.conv_sym (Step.toConv stm))
      · exact .projIm mrg1 .nil tyC (ihm stm rfl rfl) tyn
      · have h := Static.Typed.subst tyC tym.toStatic
        asimp at h
        exact h
    | @projE _ m1 m2 _ i sp hv =>
      cases i with
      | ex => exact (Static.pair_sig_false tym.toStatic ARS.Conv.refl nofun).elim
      | im =>
        obtain ⟨e, tym1, tym2⟩ := pairIm_inv tym
        cases e
        have wf := tyn.wf
        cases wf with
        | @cons _ _ _ _ wfA tyB =>
          cases wfA with
          | @null _ _ _ _ _ tyA =>
            cases hv with
            | pairIm hv2 =>
              obtain ⟨k1, k2⟩ := tym2.val_stability (Static.Typed.subst tyB tym1) hv2
              obtain ⟨Θ0, emp, mrg0⟩ := tym2.empty
              have eC : C[Chan.var_Chan; (Term.pair m1 m2 .im t)..]
                  = (C[Chan.var_Chan;
                      Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                      m2 .: m1 .: Term.var_Term] := by
                asimp; congr 1
              rw [eC]
              apply Typed.substitution tyn mrg1
              apply AgreeSubst.wk1 k1 k2 mrg0 .nil
              · apply AgreeSubst.wk0
                · exact AgreeSubst.refl emp tym2.wf
                · asimp; exact tym1
              · exact tym2
            | thunk h => cases h
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym tyn ihm ihn =>
    subst e1; subst e2
    cases mrg2
    cases st with
    | projM stm =>
      apply Typed.conv
      · exact Static.conv_beta (ARS.conv_sym (Step.toConv stm))
      · exact .projEx mrg1 .nil tyC (ihm stm rfl rfl) tyn
      · have h := Static.Typed.subst tyC tym.toStatic
        asimp at h
        exact h
    | @projE _ m1 m2 _ i sp hv =>
      cases i with
      | im => exact (Static.pair_sig_false tym.toStatic ARS.Conv.refl nofun).elim
      | ex =>
        obtain ⟨Θ1', Θ2', Δ1', Δ2', e, mrg1', mrg2', tym1, tym2⟩ := pairEx_inv tym
        cases e
        cases mrg2'
        have wf := tyn.wf
        cases wf with
        | @cons _ _ _ _ wfA tyB =>
          cases wfA with
          | @cons _ _ _ _ _ tyA =>
            cases hv with
            | pairEx hv1 hv2 =>
              obtain ⟨Θ0, emp, mrg0⟩ := tym1.empty
              obtain ⟨k1, k2⟩ := tym1.val_stability tyA hv1
              obtain ⟨k3, k4⟩ := tym2.val_stability (Static.Typed.subst tyB tym1.toStatic) hv2
              have eC : C[Chan.var_Chan; (Term.pair m1 m2 .ex t)..]
                  = (C[Chan.var_Chan;
                      Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                      m2 .: m1 .: Term.var_Term] := by
                asimp; congr 1
              rw [eC]
              apply Typed.substitution tyn mrg1
              apply AgreeSubst.wk1 k3 k4 mrg1' .nil
              apply AgreeSubst.wk1 k1 k2 mrg0 .nil
              · exact AgreeSubst.refl emp tym1.wf
              · asimp; exact tym1
              · exact tym2
            | thunk h => cases h
  | @one Θ Γ Δ emp wf k => cases st
  | @tt Θ Γ Δ emp wf k => cases st
  | @ff Θ Γ Δ emp wf k => cases st
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    subst e1; subst e2
    cases mrg2
    cases st with
    | iteM stm =>
      have tym' := ihm stm rfl rfl
      apply Typed.conv
      · exact Static.conv_beta (ARS.conv_sym (Step.toConv stm))
      · exact .ite mrg1 .nil tyA tym' tyn1 tyn2
      · exact Static.Typed.esubst rfl rfl tyA tym.toStatic
    | iteT =>
      have emp := tt_inv tym
      have e := mrg1.emptyL emp; subst e
      exact tyn1
    | iteF =>
      have emp := ff_inv tym
      have e := mrg1.emptyL emp; subst e
      exact tyn2
  | @pure Θ Γ Δ m A tym ihm =>
    subst e1; subst e2
    cases st with
    | pure stm => exact .pure (ihm stm rfl rfl)
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym tyn ihm ihn =>
    subst e1; subst e2
    cases mrg2
    cases st with
    | mletL stm => exact .mlet mrg1 .nil tyB (ihm stm rfl rfl) tyn
    | mletE hv =>
      have tyv := pure_inv tym
      have wf := tyn.wf
      cases wf with
      | @cons _ _ _ _ _ tyA =>
        obtain ⟨k1, _⟩ := tyv.val_stability tyA hv
        have h := Typed.subst1 k1 mrg1.sym (Key.nil) .nil tyn tyv
        asimp at h
        exact h
  | @chan Θ Γ Δ r x A js wf k tyA => cases st
  | @fork Θ Γ Δ A m tym ihm => subst e1; subst e2; cases st
  | @recv Θ Γ Δ r1 r2 A B m i e tym ihm =>
    subst e1; subst e2
    cases st with
    | recv stm => exact .recv e (ihm stm rfl rfl)
  | @send Θ Γ Δ r1 r2 A B m i e tym ihm =>
    subst e1; subst e2
    cases st with
    | send stm => exact .send e (ihm stm rfl rfl)
  | @close Θ Γ Δ b m tym ihm =>
    subst e1; subst e2
    cases st with
    | close stm => exact .close (ihm stm rfl rfl)
  | @conv Θ Γ Δ A B m s eq tym tyB ihm =>
    subst e1; subst e2
    exact .conv eq (ihm st rfl rfl) tyB

/-- Dynamic multi-step subject reduction (Coq `dyn_rd`). -/
theorem Typed.rd {Θ m n A}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) (rd : m ~>>* n) :
    Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ n : A := by
  induction rd with
  | refl => exact ty
  | tail _ st ih => exact ih.sr st

end TLLC.Dynamic
