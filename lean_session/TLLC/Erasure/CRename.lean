import TLLC.Erasure.Subst
import TLLC.Dynamic.CRename

/-!
# Erasure channel renaming

Port of `coq_session/era_cren.v`: the channel-renaming preservation metatheorem for the erasure
relation. Channel renaming `cren ξ m = m⟨ξ; (id : Nat → Nat)⟩` renames the *process* context `Θ`
(its live slots hold channel typings `ch r A :L`) and, simultaneously, BOTH the source term `m` and
the erased runtime term `m'`; the type `A` is left fixed (channels are context-stable).

The proof is structurally identical to the dynamic `Dynamic.Typed.crename` (Coq `dyn_crename`),
threading the second renamed term `m'`. It reuses the dynamic channel-renaming agreement
`Dynamic.CtxCRen` directly (Coq `era_cren` uses `dyn_ctx_cren`, no fresh relation). The erased
constructors carry `.box` in the boxed slots, and `.box⟨ξ; (id : Nat → Nat)⟩ = .box`, so the erased
subjects reshape under `asimp` exactly as the source subjects do.

`Erased.cstrengthen`/`Erased.cweaken` (Coq `era_cstrengthen`/`era_cweaken`) are the
strengthening/weakening corollaries (the `(+1) >>> (-1) = id` channel arithmetic via `omega`/`asimp`,
mirroring `Dynamic.Typed.cstrengthen`/`cweaken`). `Erased.cren_inv` (Coq `era_cren_inv`) shows that
the runtime side `x` of an erasure of a renamed source `cren ξ m` is itself a renaming `cren ξ m'`.
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Well-sortedness of the `proj` branch motive `C[⟨1,0⟩ .: (+2)]` under the pattern context
    `B :: A :: Γ` (the static `Σ`-elim pair-injection substitution, factored out of the proj case so
    both `projIm`/`projEx` can reuse it; mirrors `projMotive_wellSorted`). -/
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

/-! ## Channel renaming preserves erasure. -/

/-- Channel renaming preserves erasure typing (Coq `era_crename`). Only the process context `Θ`,
    the source term `m`, and the erased term `m'` are renamed; `Γ`/`Δ` and the type `A` are left
    fixed (channels are context-stable). -/
theorem Erased.crename {Θ Γ Δ m m' A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) :
    ∀ {Θ' ξ}, Dynamic.CtxCRen ξ Θ Θ' →
      Θ' ⨾ Γ ⨾ Δ ⊢ m⟨ξ; (id : Nat → Nat)⟩ ~ m'⟨ξ; (id : Nat → Nat)⟩ : A := by
  induction h with
  | @var Θ Γ Δ x s A emp wf shs dhs =>
    intro Θ' ξ agr
    exact .var (agr.empty emp) wf shs dhs
  | @lamIm Θ Γ Δ A B m m' s k1 k2 erm ihm =>
    intro Θ' ξ agr
    cases erm.wf with
    | @null _ _ _ s' _ tyA =>
      obtain ⟨r, tyB⟩ := erm.validity
      have tyAr := Static.Typed.crename tyA ξ
      have ihm' := ihm agr
      have hm := Erased.ctx_conv0 (Static.cren_conv0 .refl ξ) tyAr ihm'
      asimp
      exact .conv (Static.conv_pi (Static.cren_conv0 .refl ξ) .refl)
        (.lamIm (agr.key k1) k2 hm) (.pi tyA tyB)
  | @lamEx Θ Γ Δ A B m m' s t k1 k2 erm ihm =>
    intro Θ' ξ agr
    cases erm.wf with
    | @cons _ _ _ s' _ tyA =>
      obtain ⟨r, tyB⟩ := erm.validity
      have tyAr := Static.Typed.crename tyA ξ
      have ihm' := ihm agr
      have hm := Erased.ctx_conv1 (Static.cren_conv0 .refl ξ) tyAr ihm'
      asimp
      exact .conv (Static.conv_pi (Static.cren_conv0 .refl ξ) .refl)
        (.lamEx (agr.key k1) k2 hm) (.pi tyA tyB)
  | @appIm Θ Γ Δ A B m m' n s erm tyn ihm =>
    intro Θ' ξ agr
    obtain ⟨r, tyP⟩ := erm.validity
    obtain ⟨t, tyB, _⟩ := Static.pi_inv tyP
    have tyBn := tyB.subst tyn
    asimp at tyBn
    have ihm' := ihm agr
    asimp at ihm'
    have eq : B[Chan.var_Chan; (n⟨ξ; (id : Nat → Nat)⟩)..] ≃ B[Chan.var_Chan; n..] :=
      Static.conv_beta (Static.cren_conv0 .refl ξ)
    exact .conv eq (.appIm ihm' (Static.Typed.crename tyn ξ)) tyBn
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrgΘ mrgΔ erm ern ihm ihn =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    obtain ⟨r, tyP⟩ := erm.validity
    obtain ⟨t, tyB, _⟩ := Static.pi_inv tyP
    have tyBn := tyB.subst ern.toStatic
    asimp at tyBn
    have ihm' := ihm agr1
    asimp at ihm'
    apply Erased.conv (Static.conv_beta (Static.cren_conv0 .refl ξ)) _ tyBn
    exact .appEx mrgΘ' mrgΔ ihm' (ihn agr2)
  | @pairIm Θ Γ Δ A B m n n' t tyS tym ern ihn =>
    intro Θ' ξ agr
    obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
    have tym' := Static.Typed.crename tym ξ
    have tyBm := tyB.subst tym'
    asimp at tyBm
    have ihn' := ihn agr
    asimp at ihn' ⊢
    have ihn'' : Θ' ⨾ Γ ⨾ Δ ⊢ n⟨ξ; (id : Nat → Nat)⟩ ~ n'⟨ξ; (id : Nat → Nat)⟩
        : B[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..] :=
      Erased.conv (ARS.conv_sym (Static.conv_beta (Static.cren_conv0 .refl ξ))) ihn' tyBm
    exact .pairIm tyS tym' ihn''
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrgΘ mrgΔ tyS erm ern ihm ihn =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
    have tym' := Static.Typed.crename erm.toStatic ξ
    have tyBm := tyB.subst tym'
    asimp at tyBm
    have ihn' := ihn agr2
    asimp at ihn' ⊢
    have ihn'' : Θ2' ⨾ Γ ⨾ Δ2 ⊢ n⟨ξ; (id : Nat → Nat)⟩ ~ n'⟨ξ; (id : Nat → Nat)⟩
        : B[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..] :=
      Erased.conv (ARS.conv_sym (Static.conv_beta (Static.cren_conv0 .refl ξ))) ihn' tyBm
    exact .pairEx mrgΘ' mrgΔ tyS (ihm agr1) ihn''
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have ihm' := ihm agr1
    have ihn' := ihn agr2
    have ihC := Static.Typed.crename tyC ξ
    have hwit := projMotive_wellSorted (i := .im) ihC tyC.wf
    have eqn : (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)]
        ≃ C[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)] := by
      have h := Static.cren_conv0 (m := C[Chan.var_Chan;
        Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)]) .refl ξ
      rwa [show (C[Chan.var_Chan;
            Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)])⟨ξ;
              (id : Nat → Nat)⟩
            = (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan;
              Term.pair (.var_Term 1) (.var_Term 0) .im t .: funcomp Term.var_Term (· + 2)]
            from by asimp; congr 1] at h
    have ern'' := Erased.conv (ARS.conv_sym eqn) ihn' hwit
    have eqC : (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..]
        ≃ C[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (Static.cren_conv0 .refl ξ))
        (Static.conv_subst (m..) (Static.cren_conv0 .refl ξ))
    asimp
    exact .conv eqC (.projIm mrgΘ' mrgΔ ihC ihm' ern'') (tyC.subst erm.toStatic)
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have ihm' := ihm agr1
    have ihn' := ihn agr2
    have ihC := Static.Typed.crename tyC ξ
    have hwit := projMotive_wellSorted (i := .ex) ihC tyC.wf
    have eqn : (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)]
        ≃ C[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)] := by
      have h := Static.cren_conv0 (m := C[Chan.var_Chan;
        Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)]) .refl ξ
      rwa [show (C[Chan.var_Chan;
            Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)])⟨ξ;
              (id : Nat → Nat)⟩
            = (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan;
              Term.pair (.var_Term 1) (.var_Term 0) .ex t .: funcomp Term.var_Term (· + 2)]
            from by asimp; congr 1] at h
    have ern'' := Erased.conv (ARS.conv_sym eqn) ihn' hwit
    have eqC : (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..]
        ≃ C[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (Static.cren_conv0 .refl ξ))
        (Static.conv_subst (m..) (Static.cren_conv0 .refl ξ))
    asimp
    exact .conv eqC (.projEx mrgΘ' mrgΔ ihC ihm' ern'') (tyC.subst erm.toStatic)
  | @one Θ Γ Δ emp wf k =>
    intro Θ' ξ agr; asimp; exact .one (agr.empty emp) wf k
  | @tt Θ Γ Δ emp wf k =>
    intro Θ' ξ agr; asimp; exact .tt (agr.empty emp) wf k
  | @ff Θ Γ Δ emp wf k =>
    intro Θ' ξ agr; asimp; exact .ff (agr.empty emp) wf k
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrgΘ mrgΔ tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have wf := erm.wf
    have tyA' := Static.Typed.crename tyA ξ
    have h1 := tyA'.subst (Static.Typed.tt wf.toStatic)
    have h2 := tyA'.subst (Static.Typed.ff wf.toStatic)
    have ihm' := ihm agr1
    have ihn1' := ihn1 agr2
    have ihn2' := ihn2 agr2
    have ern1' : Θ2' ⨾ Γ ⨾ Δ2 ⊢ n1⟨ξ; (id : Nat → Nat)⟩ ~ n1'⟨ξ; (id : Nat → Nat)⟩
        : (A⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; Term.tt..] :=
      Erased.conv (ARS.conv_sym (Static.conv_subst (Term.tt..) (Static.cren_conv0 .refl ξ))) ihn1' h1
    have ern2' : Θ2' ⨾ Γ ⨾ Δ2 ⊢ n2⟨ξ; (id : Nat → Nat)⟩ ~ n2'⟨ξ; (id : Nat → Nat)⟩
        : (A⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; Term.ff..] :=
      Erased.conv (ARS.conv_sym (Static.conv_subst (Term.ff..) (Static.cren_conv0 .refl ξ))) ihn2' h2
    have eq : (A⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..]
        ≃ A[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (Static.cren_conv0 .refl ξ))
        (Static.conv_subst (m..) (Static.cren_conv0 .refl ξ))
    asimp
    apply Erased.conv eq _ (tyA.subst erm.toStatic)
    exact .ite mrgΘ' mrgΔ tyA' ihm' ern1' ern2'
  | @pure Θ Γ Δ m m' A erm ihm =>
    intro Θ' ξ agr; asimp; exact .pure (ihm agr)
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrgΘ mrgΔ tyB erm ern ihm ihn =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have ihn' := ihn agr2
    asimp
    exact .mlet (s := s) mrgΘ' mrgΔ tyB (ihm agr1) ihn'
  | @chan Θ Γ Δ r x A js wf k tyA =>
    intro Θ' ξ agr
    have js' := agr.just js
    have tyAr := Static.Typed.crename tyA ξ
    have tych : Γ ⊢ Term.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩) : .srt .L := by
      apply Static.Typed.ch
      have h := Static.Typed.rename tyA (Static.Wf.agreeRen wf.toStatic)
      asimp at h
      exact h
    have eq : Term.ch r ((A⟨ξ; (id : Nat → Nat)⟩)⟨(id : Nat → Nat); (· + Γ.length)⟩)
        ≃ Term.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩) := by
      apply Static.conv_ch
      rw [show (A⟨ξ; (id : Nat → Nat)⟩)⟨(id : Nat → Nat); (· + Γ.length)⟩
            = (A⟨(id : Nat → Nat); (· + Γ.length)⟩)⟨ξ; (id : Nat → Nat)⟩ from by asimp]
      exact Static.cren_conv0 .refl ξ
    asimp
    exact .conv eq (Erased.chan js' wf k tyAr) tych
  | @fork Θ Γ Δ A m m' erm ihm =>
    intro Θ' ξ agr
    have wf := erm.wf
    cases wf with
    | @cons _ _ _ s' _ tyCh =>
      obtain ⟨tyA, _⟩ := Static.ch_inv tyCh
      have tyAr := Static.Typed.crename tyA ξ
      have ihm' := ihm agr
      have hm := Erased.ctx_conv1 (Static.conv_ch (Static.cren_conv0 .refl ξ))
        (Static.Typed.ch tyAr) ihm'
      asimp
      apply Erased.conv (Static.conv_M (Static.conv_ch (Static.cren_conv0 .refl ξ))) _
        (Static.Typed.M (Static.Typed.ch tyA))
      exact .fork hm
  | @recv Θ Γ Δ r1 r2 A B m m' i e erm ihm =>
    intro Θ' ξ agr; asimp; exact .recv e (ihm agr)
  | @send Θ Γ Δ r1 r2 A B m m' i e erm ihm =>
    intro Θ' ξ agr; asimp; exact .send e (ihm agr)
  | @close Θ Γ Δ b m m' erm ihm =>
    intro Θ' ξ agr; asimp; exact .close (ihm agr)
  | @conv Θ Γ Δ A B m m' s eq erm tyB ihm =>
    intro Θ' ξ agr
    exact .conv eq (ihm agr) tyB

/-! ## Channel strengthening/weakening. -/

  /-- Channel strengthening for erasure (Coq `era_cstrengthen`). -/
  lemma Erased.cstrengthen {Θ Γ Δ m m' A}
      (h : (Slot.none :: Θ) ⨾ Γ ⨾ Δ
      ⊢ m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ ~ m'⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A := by
  have h := h.crename (Θ' := Θ) (ξ := funcomp (id : Nat → Nat) (· - 1)) (.minus .O)
  have hmap : funcomp ((· - 1) : Nat → Nat) ((· + 1) : Nat → Nat) = (id : Nat → Nat) := by
    funext x; simp only [funcomp, id]; omega
  rw [show (m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨funcomp (id : Nat → Nat) (· - 1);
        (id : Nat → Nat)⟩ = m from by asimp; rw [hmap]; asimp,
      show (m'⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨funcomp (id : Nat → Nat) (· - 1);
        (id : Nat → Nat)⟩ = m' from by asimp; rw [hmap]; asimp] at h
  exact h

  /-- Channel weakening for erasure (Coq `era_cweaken`). -/
  lemma Erased.cweaken {Θ Γ Δ m m' A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) :
      (Slot.none :: Θ) ⨾ Γ ⨾ Δ
      ⊢ m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ ~ m'⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ : A := by
  have h := h.crename (.plus .O)
  rw [show m⟨funcomp Nat.succ (id : Nat → Nat); (id : Nat → Nat)⟩
        = m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ from by asimp,
      show m'⟨funcomp Nat.succ (id : Nat → Nat); (id : Nat → Nat)⟩
        = m'⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ from by asimp] at h
  exact h

/-! ## Inversion: the runtime side of a renamed erasure is itself a renaming. -/

/-- The erased side `x` of an erasure of a renamed source `cren ξ m` is itself `cren ξ m'`
    for some `m'` (Coq `era_cren_inv`). -/
lemma Erased.cren_inv {Θ Γ Δ x A} {m : Term} {ξ : Nat → Nat}
    (h : Θ ⨾ Γ ⨾ Δ ⊢ m⟨ξ; (id : Nat → Nat)⟩ ~ x : A) :
    ∃ m' : Term, x = m'⟨ξ; (id : Nat → Nat)⟩ := by
  generalize e : m⟨ξ; (id : Nat → Nat)⟩ = n at h
  induction h generalizing m ξ with
  | @var Θ Γ Δ x0 s A emp wf shs dhs =>
    exact ⟨m, e.symm⟩
  | @lamIm Θ Γ Δ A B m0 m0' s k1 k2 erm ihm =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with _ e1 _ _
    obtain ⟨n', hn'⟩ := ihm e1
    exact ⟨.lam .box n' .im s, by rw [hn']; asimp⟩
  | @lamEx Θ Γ Δ A B m0 m0' s t k1 k2 erm ihm =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with _ e1 _ _
    obtain ⟨n', hn'⟩ := ihm e1
    exact ⟨.lam .box n' .ex s, by rw [hn']; asimp⟩
  | @appIm Θ Γ Δ A B m0 m0' n s erm tyn ihm =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with e1 _ _
    obtain ⟨m'', hm''⟩ := ihm e1
    exact ⟨.app m'' .box .im, by rw [hm'']; asimp⟩
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m0 m0' n n' s mrgΘ mrgΔ erm ern ihm ihn =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with e1 e2 _
    obtain ⟨m'', hm''⟩ := ihm e1
    obtain ⟨n'', hn''⟩ := ihn e2
    exact ⟨.app m'' n'' .ex, by rw [hm'', hn'']; asimp⟩
  | @pairIm Θ Γ Δ A B m0 n n' t tyS tym ern ihn =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with _ e2 _ _
    obtain ⟨n'', hn''⟩ := ihn e2
    exact ⟨.pair .box n'' .im t, by rw [hn'']; asimp⟩
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m0 m0' n n' t mrgΘ mrgΔ tyS erm ern ihm ihn =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with e1 e2 _ _
    obtain ⟨m'', hm''⟩ := ihm e1
    obtain ⟨n'', hn''⟩ := ihn e2
    exact ⟨.pair m'' n'' .ex t, by rw [hm'', hn'']; asimp⟩
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m0 m0' n n' s r t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with _ e2 e3
    obtain ⟨m'', hm''⟩ := ihm e2
    obtain ⟨n'', hn''⟩ := ihn e3
    exact ⟨.proj .box m'' n'', by rw [hm'', hn'']; asimp⟩
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m0 m0' n n' s r1 r2 t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with _ e2 e3
    obtain ⟨m'', hm''⟩ := ihm e2
    obtain ⟨n'', hn''⟩ := ihn e3
    exact ⟨.proj .box m'' n'', by rw [hm'', hn'']; asimp⟩
  | one => exact ⟨m, e.symm⟩
  | tt => exact ⟨m, e.symm⟩
  | ff => exact ⟨m, e.symm⟩
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m0 m0' n1 n1' n2 n2' s mrgΘ mrgΔ tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with _ e2 e3 e4
    obtain ⟨m'', hm''⟩ := ihm e2
    obtain ⟨p1', hp1'⟩ := ihn1 e3
    obtain ⟨p2', hp2'⟩ := ihn2 e4
    exact ⟨.ite .box m'' p1' p2', by rw [hm'', hp1', hp2']; asimp⟩
  | @pure Θ Γ Δ m0 m0' A erm ihm =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with e1
    obtain ⟨m'', hm''⟩ := ihm e1
    exact ⟨.pure m'', by rw [hm'']; asimp⟩
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m0 m0' n n' A B s t mrgΘ mrgΔ tyB erm ern ihm ihn =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with e1 e2
    obtain ⟨m'', hm''⟩ := ihm e1
    obtain ⟨n'', hn''⟩ := ihn e2
    exact ⟨.mlet m'' n'', by rw [hm'', hn'']; asimp⟩
  | @chan Θ Γ Δ r x0 A js wf k tyA =>
    exact ⟨m, e.symm⟩
  | @fork Θ Γ Δ A m0 m0' erm ihm =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with _ e2
    obtain ⟨m'', hm''⟩ := ihm e2
    exact ⟨.fork .box m'', by rw [hm'']; asimp⟩
  | @recv Θ Γ Δ r1 r2 A B m0 m0' i e0 erm ihm =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with e1 _
    obtain ⟨m'', hm''⟩ := ihm e1
    exact ⟨.recv m'' i, by rw [hm'']; asimp⟩
  | @send Θ Γ Δ r1 r2 A B m0 m0' i e0 erm ihm =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with e1 _
    obtain ⟨m'', hm''⟩ := ihm e1
    exact ⟨.send m'' i, by rw [hm'']; asimp⟩
  | @close Θ Γ Δ b m0 m0' erm ihm =>
    cases m <;> asimp at e <;> first | exact Term.noConfusion e | skip
    injection e with _ e2
    obtain ⟨m'', hm''⟩ := ihm e2
    exact ⟨.close b m'', by rw [hm'']; asimp⟩
  | @conv Θ Γ Δ A B m0 m0' s eq erm tyB ihm =>
    exact ihm e

end TLLC.Erasure
