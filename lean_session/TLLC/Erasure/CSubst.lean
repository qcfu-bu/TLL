import TLLC.Erasure.CRename
import TLLC.Dynamic.CSubst

/-!
# Erasure channel substitution

Port of `coq_session/era_csubst.v`: the channel-*substitution* preservation metatheorem for the
erasure relation. A channel substitution `σ : Nat → Chan` transforms the *process* context `Θ2`
into `Θ1` (via the dynamic agreement `Dynamic.AgreeCSubst`, notation `Θ1 ⊩ σ ⫣ Θ2`) and,
simultaneously, channel-substitutes BOTH the source term `m` and the erased runtime term `m'` with
the SAME `σ` (`csubst σ m = m[σ; Term.var_Term]`); the type `A` is left fixed (channels are
context-stable).

The single lemma `Erased.csubstitution` (Coq `era_csubstitution`) is proved by direct induction over
the erasure relation, structurally identical to the dynamic `Dynamic.Typed.csubstitution`
(Coq `dyn_csubstitution`), threading the second substituted term `m'`. It reuses the dynamic
channel-substitution agreement `Dynamic.AgreeCSubst` directly (Coq `era_csubst` uses
`dyn_agree_csubst`, no fresh relation). The erased constructors carry `.box` in the boxed slots, and
`.box[σ; Term.var_Term] = .box`, so the erased subjects reshape under `asimp` exactly as the source
subjects do.

The workhorse `Dynamic.csubst_conv` (`csubst σ m ≃ m`, Coq's `sta_csubst_cren` + `sta_cren_conv0`
chain) adapts each result type back to its un-substituted form; the `chan` case routes through
`Dynamic.AgreeCSubst.just`, the merge cases through `Dynamic.AgreeCSubst.merge`, and the empties
through `Dynamic.AgreeCSubst.empty`.
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

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

/-! ## Channel substitution preserves erasure. -/

/-- Channel substitution preserves erasure typing (Coq `era_csubstitution`). The channel
    substitution `σ : Nat → Chan` is applied to BOTH the source term `m` and the erased term `m'`;
    the static context `Γ`/`Δ` and the type `A` are left fixed (channels are context-stable). -/
theorem Erased.csubstitution {Θ2 Γ Δ m m' A} (h : Θ2 ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) :
    ∀ {Θ1 σ}, (Θ1 ⊩ σ ⫣ Θ2) →
      Θ1 ⨾ Γ ⨾ Δ ⊢ m[σ; Term.var_Term] ~ m'[σ; Term.var_Term] : A := by
  induction h with
  | @var Θ Γ Δ x s A emp wf shs dhs =>
    intro Θ1 σ agr
    asimp
    exact .var (agr.empty emp) wf shs dhs
  | @lamIm Θ Γ Δ A B m m' s k1 k2 erm ihm =>
    intro Θ1 σ agr
    cases erm.wf with
    | @null _ _ _ s' _ tyA =>
      obtain ⟨r, tyB⟩ := erm.validity
      have tyAσ := Static.Typed.csubstitution tyA σ
      have ihm' := ihm agr
      have hm := Erased.ctx_conv0 (csubst_conv σ A) tyAσ ihm'
      asimp
      exact .conv (Static.conv_pi (csubst_conv σ A) .refl)
        (.lamIm (agr.key k1) k2 hm) (.pi tyA tyB)
  | @lamEx Θ Γ Δ A B m m' s t k1 k2 erm ihm =>
    intro Θ1 σ agr
    cases erm.wf with
    | @cons _ _ _ s' _ tyA =>
      obtain ⟨r, tyB⟩ := erm.validity
      have tyAσ := Static.Typed.csubstitution tyA σ
      have ihm' := ihm agr
      have hm := Erased.ctx_conv1 (csubst_conv σ A) tyAσ ihm'
      asimp
      exact .conv (Static.conv_pi (csubst_conv σ A) .refl)
        (.lamEx (agr.key k1) k2 hm) (.pi tyA tyB)
  | @appIm Θ Γ Δ A B m m' n s erm tyn ihm =>
    intro Θ1 σ agr
    obtain ⟨r, tyP⟩ := erm.validity
    obtain ⟨t, tyB, _⟩ := Static.pi_inv tyP
    have tyBn := tyB.subst tyn
    asimp at tyBn
    have ihm' := ihm agr
    asimp at ihm'
    have eq : B[Chan.var_Chan; (n[σ; Term.var_Term])..] ≃ B[Chan.var_Chan; n..] :=
      Static.conv_beta (csubst_conv σ n)
    exact .conv eq (.appIm ihm' (Static.Typed.csubstitution tyn σ)) tyBn
  | @appEx Θ1' Θ2' Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrgΘ mrgΔ erm ern ihm ihn =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    obtain ⟨r, tyP⟩ := erm.validity
    obtain ⟨t, tyB, _⟩ := Static.pi_inv tyP
    have tyBn := tyB.subst ern.toStatic
    asimp at tyBn
    have ihm' := ihm agr1
    asimp at ihm'
    apply Erased.conv (Static.conv_beta (csubst_conv σ n)) _ tyBn
    exact .appEx mrgΘ' mrgΔ ihm' (ihn agr2)
  | @pairIm Θ Γ Δ A B m n n' t tyS tym ern ihn =>
    intro Θ1 σ agr
    obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
    have tym' := Static.Typed.csubstitution tym σ
    have tyBm := tyB.subst tym'
    asimp at tyBm
    have ihn' := ihn agr
    asimp at ihn' ⊢
    have ihn'' : Θ1 ⨾ Γ ⨾ Δ ⊢ n[σ; Term.var_Term] ~ n'[σ; Term.var_Term]
        : B[Chan.var_Chan; (m[σ; Term.var_Term])..] :=
      Erased.conv (ARS.conv_sym (Static.conv_beta (csubst_conv σ m))) ihn' tyBm
    exact .pairIm tyS tym' ihn''
  | @pairEx Θ1' Θ2' Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrgΘ mrgΔ tyS erm ern ihm ihn =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
    have tym' := Static.Typed.csubstitution erm.toStatic σ
    have tyBm := tyB.subst tym'
    asimp at tyBm
    have ihn' := ihn agr2
    asimp at ihn' ⊢
    have ihn'' : Θb ⨾ Γ ⨾ Δ2 ⊢ n[σ; Term.var_Term] ~ n'[σ; Term.var_Term]
        : B[Chan.var_Chan; (m[σ; Term.var_Term])..] :=
      Erased.conv (ARS.conv_sym (Static.conv_beta (csubst_conv σ m))) ihn' tyBm
    exact .pairEx mrgΘ' mrgΔ tyS (ihm agr1) ihn''
  | @projIm Θ1' Θ2' Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have ihm' := ihm agr1
    have ihn' := ihn agr2
    have tyC' := Static.Typed.csubstitution tyC σ
    have hwit := projMotive_wellSorted (i := .im) tyC' tyC.wf
    have eqn : (C[σ; Term.var_Term])[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)]
        ≃ C[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)] :=
      Static.conv_subst _ (csubst_conv σ C)
    have ern'' := Erased.conv (ARS.conv_sym eqn) ihn' hwit
    have eqC : (C[σ; Term.var_Term])[Chan.var_Chan; (m[σ; Term.var_Term])..]
        ≃ C[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (csubst_conv σ m))
        (Static.conv_subst (m..) (csubst_conv σ C))
    asimp
    exact .conv eqC (.projIm mrgΘ' mrgΔ tyC' ihm' ern'') (tyC.subst erm.toStatic)
  | @projEx Θ1' Θ2' Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have ihm' := ihm agr1
    have ihn' := ihn agr2
    have tyC' := Static.Typed.csubstitution tyC σ
    have hwit := projMotive_wellSorted (i := .ex) tyC' tyC.wf
    have eqn : (C[σ; Term.var_Term])[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)]
        ≃ C[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)] :=
      Static.conv_subst _ (csubst_conv σ C)
    have ern'' := Erased.conv (ARS.conv_sym eqn) ihn' hwit
    have eqC : (C[σ; Term.var_Term])[Chan.var_Chan; (m[σ; Term.var_Term])..]
        ≃ C[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (csubst_conv σ m))
        (Static.conv_subst (m..) (csubst_conv σ C))
    asimp
    exact .conv eqC (.projEx mrgΘ' mrgΔ tyC' ihm' ern'') (tyC.subst erm.toStatic)
  | @one Θ Γ Δ emp wf k =>
    intro Θ1 σ agr; asimp; exact .one (agr.empty emp) wf k
  | @tt Θ Γ Δ emp wf k =>
    intro Θ1 σ agr; asimp; exact .tt (agr.empty emp) wf k
  | @ff Θ Γ Δ emp wf k =>
    intro Θ1 σ agr; asimp; exact .ff (agr.empty emp) wf k
  | @ite Θ1' Θ2' Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrgΘ mrgΔ tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have wf := erm.wf
    have tyA' := Static.Typed.csubstitution tyA σ
    have h1 := tyA'.subst (Static.Typed.tt wf.toStatic)
    have h2 := tyA'.subst (Static.Typed.ff wf.toStatic)
    have ihm' := ihm agr1
    have ihn1' := ihn1 agr2
    have ihn2' := ihn2 agr2
    have ern1' : Θb ⨾ Γ ⨾ Δ2 ⊢ n1[σ; Term.var_Term] ~ n1'[σ; Term.var_Term]
        : (A[σ; Term.var_Term])[Chan.var_Chan; Term.tt..] :=
      Erased.conv (ARS.conv_sym (Static.conv_subst (Term.tt..) (csubst_conv σ A))) ihn1' h1
    have ern2' : Θb ⨾ Γ ⨾ Δ2 ⊢ n2[σ; Term.var_Term] ~ n2'[σ; Term.var_Term]
        : (A[σ; Term.var_Term])[Chan.var_Chan; Term.ff..] :=
      Erased.conv (ARS.conv_sym (Static.conv_subst (Term.ff..) (csubst_conv σ A))) ihn2' h2
    have eq : (A[σ; Term.var_Term])[Chan.var_Chan; (m[σ; Term.var_Term])..]
        ≃ A[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (csubst_conv σ m))
        (Static.conv_subst (m..) (csubst_conv σ A))
    asimp
    apply Erased.conv eq _ (tyA.subst erm.toStatic)
    exact .ite mrgΘ' mrgΔ tyA' ihm' ern1' ern2'
  | @pure Θ Γ Δ m m' A erm ihm =>
    intro Θ1 σ agr; asimp; exact .pure (ihm agr)
  | @mlet Θ1' Θ2' Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrgΘ mrgΔ tyB erm ern ihm ihn =>
    intro Θ1 σ agr
    obtain ⟨Θa, Θb, mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have ihn' := ihn agr2
    asimp
    exact .mlet mrgΘ' mrgΔ tyB (ihm agr1) ihn'
  | @chan Θ Γ Δ r x A js wf k tyA =>
    intro Θ1 σ agr
    asimp
    -- `agr.just` types the substituted channel variable in the empty context.
    have tyx := agr.just tyA js
    -- `σ x` is a channel variable; recover the underlying `Just` via channel inversion.
    cases hc : σ x with
    | var_Chan c =>
      rw [hc] at tyx
      obtain ⟨r0, A0, js0, tyA0, eq0⟩ := chan_inv tyx
      -- at the empty context the shift `(·+0)` collapses, so `eq0 : ch r A ≃ ch r0 A0`.
      rw [show A0⟨(id : Nat → Nat); (· + ([] : Static.Ctx).length)⟩ = A0 from by
            simp only [List.length_nil, Nat.add_zero]
            rw [show ((fun x => x) : Nat → Nat) = (id : Nat → Nat) from rfl]; asimp] at eq0
      obtain ⟨er, eA⟩ := Static.ch_inj eq0
      subst er
      -- the closed erasure of the channel variable, then lift to `Γ`/`Δ`.
      have erch : Θ1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx)
          ⊢ .chan (Chan.var_Chan c) ~ .chan (Chan.var_Chan c)
          : .ch r (A0⟨(id : Nat → Nat); (· + ([] : Static.Ctx).length)⟩) :=
        Erased.chan js0 .nil .nil tyA0
      have h := erch.rename (wf.agreeRen k)
      asimp at h
      -- result type `.ch r (A0⟨id; +Γ.length⟩)`; convert to the goal `.ch r (A⟨id; +Γ.length⟩)`.
      have tych : Γ ⊢ Term.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩) : .srt .L := by
        apply Static.Typed.ch
        have hr := Static.Typed.rename tyA (Static.Wf.agreeRen wf.toStatic)
        asimp at hr
        exact hr
      have eqty : Term.ch r (A0⟨(id : Nat → Nat); (· + Γ.length)⟩)
          ≃ Term.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩) :=
        Static.conv_ch (Static.conv_ren (· + Γ.length) (ARS.conv_sym eA))
      exact (Erased.conv eqty h tych)
  | @fork Θ Γ Δ A m m' erm ihm =>
    intro Θ1 σ agr
    have wf := erm.wf
    cases wf with
    | @cons _ _ _ s' _ tyCh =>
      obtain ⟨tyA, _⟩ := Static.ch_inv tyCh
      have tyAσ := Static.Typed.csubstitution tyA σ
      have ihm' := ihm agr
      have hm := Erased.ctx_conv1 (Static.conv_ch (csubst_conv σ A))
        (Static.Typed.ch tyAσ) ihm'
      asimp
      apply Erased.conv (Static.conv_M (Static.conv_ch (csubst_conv σ A))) _
        (Static.Typed.M (Static.Typed.ch tyA))
      exact .fork hm
  | @recv Θ Γ Δ r1 r2 A B m m' i e erm ihm =>
    intro Θ1 σ agr; asimp; exact .recv e (ihm agr)
  | @send Θ Γ Δ r1 r2 A B m m' i e erm ihm =>
    intro Θ1 σ agr; asimp; exact .send e (ihm agr)
  | @close Θ Γ Δ b m m' erm ihm =>
    intro Θ1 σ agr; asimp; exact .close (ihm agr)
  | @conv Θ Γ Δ A B m m' s eq erm tyB ihm =>
    intro Θ1 σ agr
    exact .conv eq (ihm agr) tyB

end TLLC.Erasure
