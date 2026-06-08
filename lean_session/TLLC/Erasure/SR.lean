import TLLC.Erasure.Inversion
import TLLC.Dynamic.Step

/-!
# Erasure subject reduction

Port of `coq_session/era_sr.v`: subject reduction for the erasure relation. The source term `m` (of an
erasure `Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A`) steps in the dynamic reduction `m ~>> n`, and we show the *erased*
term `m'` steps to a matching erasure `m' ~>> n'` with `Θ ⨾ Γ ⨾ Δ ⊢ n ~ n' : A` (in the empty
context). The proof mirrors `Dynamic/SR.lean` (`Dynamic.Typed.sr`) case-by-case, additionally
producing the matching erased step.

Helpers ported first:
* `Erased.thunk_val` (Coq `era_dyn_thunk_val`): erasure preserves thunk-hood and value-hood.
* `Erased.val` (Coq `era_dyn_val`): the value half.
* `Erased.val_stability` (Coq `era_val_stability`): a value's context keys match its type sort,
  deferring to `Dynamic.Typed.val_stability` via `Erased.toDyn`.
* `Erased.pure_empty` (Coq `era_pure_empty`): a pure process context is empty.

The headline `Erased.sr` (Coq `era_sr`, a `Theorem`) and the multi-step corollary `Erased.rd`
(Coq `era_rd`) close the file. The redex cases reuse the erasure substitution lemmas
`Erased.subst0`/`subst1`/`substitution` and the `era_*_inv` form/inversion lemmas of `Inversion.lean`.
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Erasure preserves thunk-hood and value-hood (Coq `era_dyn_thunk_val`). -/
lemma Erased.thunk_val {Θ Γ Δ m m' A} (er : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) :
    (Thunk m → Thunk m') ∧ (Val m → Val m') := by
  induction er with
  | var => exact ⟨fun h => h, fun h => h⟩
  | lamIm _ _ _ _ => exact ⟨nofun, fun _ => .lam⟩
  | lamEx _ _ _ _ => exact ⟨nofun, fun _ => .lam⟩
  | @appIm Θ Γ Δ A B m m' n s erm tyn ihm =>
    refine ⟨?_, ?_⟩
    · intro h
      cases h with
      | appSendIm hv =>
        obtain ⟨m0, e⟩ := sendIm_form erm; subst e
        have hv' := ihm.2 (.send hv)
        cases hv' with
        | send hv0 => exact .appSendIm hv0
        | thunk h => cases h
    · intro h
      cases h with
      | thunk h =>
        cases h with
        | appSendIm hv =>
          obtain ⟨m0, e⟩ := sendIm_form erm; subst e
          have hv' := ihm.2 (.send hv)
          cases hv' with
          | send hv0 => exact .thunk (.appSendIm hv0)
          | thunk h => cases h
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrgΘ mrgΔ erm ern ihm ihn =>
    refine ⟨?_, ?_⟩
    · intro h
      cases h with
      | appSendEx hv1 hv2 =>
        obtain ⟨m0, e⟩ := sendEx_form erm; subst e
        have hv' := ihm.2 (.send hv1)
        cases hv' with
        | send hv0 => exact .appSendEx hv0 (ihn.2 hv2)
        | thunk h => cases h
    · intro h
      cases h with
      | thunk h =>
        cases h with
        | appSendEx hv1 hv2 =>
          obtain ⟨m0, e⟩ := sendEx_form erm; subst e
          have hv' := ihm.2 (.send hv1)
          cases hv' with
          | send hv0 => exact .thunk (.appSendEx hv0 (ihn.2 hv2))
          | thunk h => cases h
  | pairIm _ _ _ ihn =>
    refine ⟨nofun, fun h => ?_⟩
    cases h with
    | pairIm hv2 => exact .pairIm (ihn.2 hv2)
    | thunk h => cases h
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrgΘ mrgΔ tyS erm ern ihm ihn =>
    refine ⟨nofun, fun h => ?_⟩
    cases h with
    | pairEx hv1 hv2 => exact .pairEx (ihm.2 hv1) (ihn.2 hv2)
    | thunk h => cases h
  | projIm _ _ _ _ _ => exact ⟨nofun, fun h => by cases h with | thunk h => cases h⟩
  | projEx _ _ _ _ _ => exact ⟨nofun, fun h => by cases h with | thunk h => cases h⟩
  | one => exact ⟨nofun, fun _ => .one⟩
  | tt => exact ⟨nofun, fun _ => .tt⟩
  | ff => exact ⟨nofun, fun _ => .ff⟩
  | ite _ _ _ _ _ _ => exact ⟨nofun, fun h => by cases h with | thunk h => cases h⟩
  | pure _ ihm =>
    refine ⟨nofun, fun h => ?_⟩
    cases h with
    | pure hv => exact .pure (ihm.2 hv)
    | thunk h => cases h
  | mlet _ _ _ _ _ ihm ihn =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with | mlet hm => exact .mlet (ihm.1 hm)
    · cases h with | thunk h => cases h with | mlet hm => exact .thunk (.mlet (ihm.1 hm))
  | chan => exact ⟨nofun, fun _ => .chan⟩
  | fork _ _ => exact ⟨fun _ => .fork, fun h => by cases h with | thunk h => exact .thunk .fork⟩
  | recv _ _ ihm =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with | recv hv => exact .recv (ihm.2 hv)
    · cases h with | thunk h => cases h with | recv hv => exact .thunk (.recv (ihm.2 hv))
  | send _ _ ihm =>
    refine ⟨nofun, fun h => ?_⟩
    cases h with
    | send hv => exact .send (ihm.2 hv)
    | thunk h => cases h
  | close _ ihm =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with | close hv => exact .close (ihm.2 hv)
    · cases h with | thunk h => cases h with | close hv => exact .thunk (.close (ihm.2 hv))
  | conv _ _ _ ihm => exact ihm

/-- Erasure preserves value-hood (Coq `era_dyn_val`). -/
lemma Erased.val {Θ Γ Δ m m' A} (er : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) (vl : Val m) : Val m' :=
  er.thunk_val.2 vl

/-- A value's context keys match its type sort (Coq `era_val_stability`). -/
lemma Erased.val_stability {Θ Γ Δ m m' A s}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) (tyA : Γ ⊢ A : .srt s) (vl : Val m) : Θ ▷ s ∧ Δ ▷ s :=
  er.toDyn.val_stability tyA vl

/-- A pure process context is empty (Coq `era_pure_empty`). -/
lemma Erased.pure_empty {Θ Γ Δ m m' A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) (k : Θ ▷ Srt.U) : Empty Θ :=
  er.toDyn.pure_empty k

/-- Erasure subject reduction over a closed term (Coq `era_sr`). -/
theorem Erased.sr {Θ m m' n A}
    (er : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m ~ m' : A) (st : m ~>> n) :
    ∃ n', (Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ n ~ n' : A) ∧ m' ~>> n' := by
  generalize e1 : ([] : Static.Ctx) = Γ at er
  generalize e2 : ([] : Ctx) = Δ at er
  induction er generalizing n with
  | var => cases st
  | lamIm _ _ _ _ => cases st
  | lamEx _ _ _ _ => cases st
  | @appIm Θ Γ Δ A B m m' n s erm tyn ihm =>
    subst e1; subst e2
    cases st with
    | appL stm =>
      obtain ⟨m'1, erm', st'⟩ := ihm stm rfl rfl
      exact ⟨.app m'1 .box .im, .appIm erm' tyn, .appL st'⟩
    | betaIm =>
      obtain ⟨m1, e⟩ := lamIm_form erm; subst e
      have erm0 := lamIm_inv erm
      exact ⟨m1[Chan.var_Chan; (Term.box)..], erm0.subst0 tyn, .betaIm⟩
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrgΘ mrgΔ erm ern ihm ihn =>
    subst e1; subst e2
    cases mrgΔ
    cases st with
    | appL stm =>
      obtain ⟨m0, erm0, st'⟩ := ihm stm rfl rfl
      exact ⟨.app m0 n' .ex, .appEx mrgΘ .nil erm0 ern, .appL st'⟩
    | appR stn =>
      obtain ⟨n0, ern0, st'⟩ := ihn stn rfl rfl
      obtain ⟨x, tyP⟩ := erm.validity
      obtain ⟨r, tyB, _⟩ := Static.pi_inv tyP
      refine ⟨.app m' n0 .ex, ?_, .appR st'⟩
      apply Erased.conv
      · exact Static.conv_beta (ARS.conv_sym (Step.toConv stn))
      · exact .appEx mrgΘ .nil erm ern0
      · have h := Static.Typed.subst tyB ern.toStatic
        asimp at h ⊢
        exact h
    | betaEx hv =>
      obtain ⟨m0', e⟩ := lamEx_form erm; subst e
      obtain ⟨x, tyP⟩ := erm.validity
      obtain ⟨r, tyB, _⟩ := Static.pi_inv tyP
      obtain ⟨t, erm0⟩ := lamEx_inv erm
      have wf := erm0.wf
      cases wf with
      | @cons _ _ _ _ _ tyA =>
        obtain ⟨k1, k2⟩ := ern.val_stability tyA hv
        have vl := ern.val hv
        refine ⟨m0'[Chan.var_Chan; n'..], ?_, .betaEx vl⟩
        exact Erased.subst1 k1 mrgΘ k2 .nil erm0 ern
  | @pairIm Θ Γ Δ A B m n n' t tyS tym ern ihn =>
    subst e1; subst e2
    cases st with
    | pairR stn =>
      obtain ⟨n'1, ern', st'⟩ := ihn stn rfl rfl
      exact ⟨.pair .box n'1 .im t, .pairIm tyS tym ern', .pairR st'⟩
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrgΘ mrgΔ tyS erm ern ihm ihn =>
    subst e1; subst e2
    cases mrgΔ
    cases st with
    | pairL stm =>
      obtain ⟨s, r, ord1, ord2, tyA, tyB, _⟩ := Static.sig_inv tyS
      obtain ⟨m'1, erm0, st'⟩ := ihm stm rfl rfl
      refine ⟨.pair m'1 n' .ex t, ?_, .pairL st'⟩
      apply Erased.pairEx mrgΘ .nil tyS erm0
      apply Erased.conv
      · exact Static.conv_beta (Step.toConv stm)
      · exact ern
      · exact Static.Typed.esubst rfl rfl tyB erm0.toStatic
    | pairR stn =>
      obtain ⟨n'1, ern0, st'⟩ := ihn stn rfl rfl
      exact ⟨.pair m' n'1 .ex t, .pairEx mrgΘ .nil tyS erm ern0, .pairR st'⟩
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    subst e1; subst e2
    cases mrgΔ
    cases st with
    | projM stm =>
      obtain ⟨m'1, erm0, st'⟩ := ihm stm rfl rfl
      refine ⟨.proj .box m'1 n', ?_, .projM st'⟩
      apply Erased.conv
      · exact Static.conv_beta (ARS.conv_sym (Step.toConv stm))
      · exact .projIm mrgΘ .nil tyC erm0 ern
      · have h := Static.Typed.subst tyC erm.toStatic
        asimp at h
        exact h
    | @projE _ m1 m2 _ i sp hv =>
      cases i with
      | ex => exact (Static.pair_sig_false erm.toStatic ARS.Conv.refl nofun).elim
      | im =>
        obtain ⟨p1, e⟩ := pairIm_form erm; subst e
        obtain ⟨e, em2, tym1, erm2⟩ := pairIm_inv erm
        subst e
        have wf := ern.wf
        cases wf with
        | @cons _ _ _ _ wfA tyB =>
          cases wfA with
          | @null _ _ _ _ _ tyA =>
            cases hv with
            | thunk h => cases h
            | pairIm hv2 =>
              obtain ⟨k1, k2⟩ := erm2.val_stability (Static.Typed.subst tyB tym1) hv2
              obtain ⟨Θ0, emp, mrg0⟩ := erm2.empty
              have vl := erm2.val hv2
              have eC : C[Chan.var_Chan; (Term.pair m1 m2 .im sp)..]
                  = (C[Chan.var_Chan;
                      Term.pair (.var_Term 1) (.var_Term 0) .im sp .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                      m2 .: m1 .: Term.var_Term] := by
                asimp; congr 1
              rw [eC]
              refine ⟨n'[Chan.var_Chan; p1 .: Term.box .: Term.var_Term], ?_, .projE (.pairIm vl)⟩
              apply Erased.substitution ern mrgΘ
              apply AgreeSubst.wk1 k1 k2 mrg0 .nil
              · apply AgreeSubst.wk0
                · exact AgreeSubst.refl emp erm2.wf
                · asimp; exact tym1
              · asimp; exact erm2
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    subst e1; subst e2
    cases mrgΔ
    cases st with
    | projM stm =>
      obtain ⟨m'1, erm0, st'⟩ := ihm stm rfl rfl
      refine ⟨.proj .box m'1 n', ?_, .projM st'⟩
      apply Erased.conv
      · exact Static.conv_beta (ARS.conv_sym (Step.toConv stm))
      · exact .projEx mrgΘ .nil tyC erm0 ern
      · have h := Static.Typed.subst tyC erm.toStatic
        asimp at h
        exact h
    | @projE _ m1 m2 _ i sp hv =>
      cases i with
      | im => exact (Static.pair_sig_false erm.toStatic ARS.Conv.refl nofun).elim
      | ex =>
        obtain ⟨p1, p2, e⟩ := pairEx_form erm; subst e
        obtain ⟨Θ1', Θ2', Δ1', Δ2', e, mrg1', mrg2', erm1, erm2⟩ := pairEx_inv erm
        subst e
        cases mrg2'
        have wf := ern.wf
        cases wf with
        | @cons _ _ _ _ wfA tyB =>
          cases wfA with
          | @cons _ _ _ _ _ tyA =>
            cases hv with
            | thunk h => cases h
            | pairEx hv1 hv2 =>
              obtain ⟨Θ0, emp, mrg0⟩ := erm1.empty
              obtain ⟨k1, k2⟩ := erm1.val_stability tyA hv1
              obtain ⟨k3, k4⟩ := erm2.val_stability (Static.Typed.subst tyB erm1.toStatic) hv2
              have vl1 := erm1.val hv1
              have vl2 := erm2.val hv2
              have eC : C[Chan.var_Chan; (Term.pair m1 m2 .ex sp)..]
                  = (C[Chan.var_Chan;
                      Term.pair (.var_Term 1) (.var_Term 0) .ex sp .: funcomp Term.var_Term (· + 2)])[Chan.var_Chan;
                      m2 .: m1 .: Term.var_Term] := by
                asimp; congr 1
              rw [eC]
              refine ⟨_, ?_, .projE (.pairEx vl1 vl2)⟩
              apply Erased.substitution ern mrgΘ
              apply AgreeSubst.wk1 k3 k4 mrg1' .nil
              apply AgreeSubst.wk1 k1 k2 mrg0 .nil
              · exact AgreeSubst.refl emp erm1.wf
              · asimp; exact erm1
              · asimp; exact erm2
  | one => cases st
  | tt => cases st
  | ff => cases st
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrgΘ mrgΔ tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    subst e1; subst e2
    cases mrgΔ
    cases st with
    | iteM stm =>
      obtain ⟨m'1, erm0, st'⟩ := ihm stm rfl rfl
      refine ⟨.ite .box m'1 n1' n2', ?_, .iteM st'⟩
      apply Erased.conv
      · exact Static.conv_beta (ARS.conv_sym (Step.toConv stm))
      · exact .ite mrgΘ .nil tyA erm0 ern1 ern2
      · exact Static.Typed.esubst rfl rfl tyA erm.toStatic
    | iteT =>
      have e := tt_form erm; subst e
      have emp := tt_inv erm
      have e := mrgΘ.emptyL emp; subst e
      exact ⟨n1', ern1, .iteT⟩
    | iteF =>
      have e := ff_form erm; subst e
      have emp := ff_inv erm
      have e := mrgΘ.emptyL emp; subst e
      exact ⟨n2', ern2, .iteF⟩
  | @pure Θ Γ Δ m m' A erm ihm =>
    subst e1; subst e2
    cases st with
    | pure stm =>
      obtain ⟨m'1, erm0, st'⟩ := ihm stm rfl rfl
      exact ⟨.pure m'1, .pure erm0, .pure st'⟩
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrgΘ mrgΔ tyB erm ern ihm ihn =>
    subst e1; subst e2
    cases mrgΔ
    cases st with
    | mletL stm =>
      obtain ⟨m'1, erm0, st'⟩ := ihm stm rfl rfl
      exact ⟨.mlet m'1 n', .mlet mrgΘ .nil tyB erm0 ern, .mletL st'⟩
    | mletE hv =>
      obtain ⟨v', e⟩ := pure_form erm; subst e
      have erv := pure_inv erm
      have vl := erv.val hv
      have wf := ern.wf
      cases wf with
      | @cons _ _ _ _ _ tyA =>
        obtain ⟨k1, _⟩ := erv.val_stability tyA hv
        refine ⟨n'[Chan.var_Chan; v'..], ?_, .mletE vl⟩
        have h := Erased.subst1 k1 mrgΘ.sym (Key.nil) .nil ern erv
        asimp at h
        exact h
  | chan => cases st
  | fork _ _ => subst e1; subst e2; cases st
  | @recv Θ Γ Δ r1 r2 A B m m' i hxor erm ihm =>
    subst e1; subst e2
    cases st with
    | recv stm =>
      obtain ⟨m'1, erm0, st'⟩ := ihm stm rfl rfl
      exact ⟨.recv m'1 i, .recv hxor erm0, .recv st'⟩
  | @send Θ Γ Δ r1 r2 A B m m' i hxor erm ihm =>
    subst e1; subst e2
    cases st with
    | send stm =>
      obtain ⟨m'1, erm0, st'⟩ := ihm stm rfl rfl
      exact ⟨.send m'1 i, .send hxor erm0, .send st'⟩
  | @close Θ Γ Δ b m m' erm ihm =>
    subst e1; subst e2
    cases st with
    | close stm =>
      obtain ⟨m'1, erm0, st'⟩ := ihm stm rfl rfl
      exact ⟨.close b m'1, .close erm0, .close st'⟩
  | @conv Θ Γ Δ A B m m' s eq erm tyB ihm =>
    subst e1; subst e2
    obtain ⟨n', ern, st'⟩ := ihm st rfl rfl
    exact ⟨n', .conv eq ern tyB, st'⟩

/-- Erasure multi-step subject reduction (Coq `era_rd`). -/
theorem Erased.rd {Θ m m' n A}
    (er : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m ~ m' : A) (rd : m ~>>* n) :
    ∃ n', (Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ n ~ n' : A) ∧ m' ~>>* n' := by
  induction rd generalizing m' with
  | refl => exact ⟨m', er, .refl⟩
  | @tail y z _ st ih =>
    obtain ⟨n', ern, rd'⟩ := ih er
    obtain ⟨z', erz, st'⟩ := ern.sr st
    exact ⟨z', erz, rd'.tail st'⟩

end TLLC.Erasure
