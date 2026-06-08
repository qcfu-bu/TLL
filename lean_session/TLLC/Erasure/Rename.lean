import TLLC.Erasure.Validity
import TLLC.Dynamic.Rename

/-!
# Erasure renaming

Port of `coq_session/era_weak.v`: the renaming-preservation metatheorem for the erasure relation
(Coq `era_rename`, here `Erased.rename`) and its weakening corollaries (Coq
`era_weakenU`/`era_weakenN`/`era_eweakenU`/`era_eweakenN`, here
`Erased.weakenU`/`weakenN`/`eweakenU`/`eweakenN`).

`era_rename` mirrors the dynamic `dyn_rename` (`Dynamic.Typed.rename`) almost line-for-line, simply
threading a second (erased) term `m'` alongside the source `m`. Accordingly it REUSES the dynamic
renaming-agreement relation `Dynamic.AgreeRen` and all its structural lemmas (`toStatic`, `key`,
`has`, `merge`, `size`, `Wf.rename`) directly — it does not define its own agreement relation.

Each case rebuilds the corresponding `Erased.*` constructor with both renamed terms, using the same
`rw [show … from by asimp]` reshapings, `Static.Typed.rename`/`Static.conv_ren`, and
`AgreeRen.toStatic`/`.merge`/`.key`/`.size` as the dynamic proof. Erased terms carry `.box` in
irrelevant slots; `.box⟨ξ;id⟩ = .box` by `asimp`, so the renamed erased constructors match by
defeq/`asimp` like the source.
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Renaming preserves the erasure relation (Coq `era_rename`). -/
lemma Erased.rename {Θ Γ Δ m m' A} (h : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) :
    ∀ {Γ' Δ' ξ}, AgreeRen ξ Γ Δ Γ' Δ' →
      Θ ⨾ Γ' ⨾ Δ' ⊢ m⟨(id : Nat → Nat); ξ⟩ ~ m'⟨(id : Nat → Nat); ξ⟩ : A⟨(id : Nat → Nat); ξ⟩ := by
  induction h with
  | @var Θ Γ Δ x s A emp wf shs dhs =>
    intro Γ' Δ' ξ agr
    asimp
    exact .var emp (wf.rename agr) (agr.toStatic.has shs) (agr.has dhs)
  | @lamIm Θ Γ Δ A B m m' s kΘ kΔ erm ihm =>
    intro Γ' Δ' ξ agr
    asimp
    cases erm.wf with
    | @null _ _ _ s' _ tyA =>
      exact .lamIm kΘ (agr.key kΔ) (ihm (.null tyA agr))
  | @lamEx Θ Γ Δ A B m m' s t kΘ kΔ erm ihm =>
    intro Γ' Δ' ξ agr
    asimp
    cases erm.wf with
    | @cons _ _ _ s' _ tyA =>
      exact .lamEx kΘ (agr.key kΔ) (ihm (.cons tyA agr))
  | @appIm Θ Γ Δ A B m m' n s erm tyn ihm =>
    intro Γ' Δ' ξ agr
    rw [show (B[Chan.var_Chan; n..])⟨(id : Nat → Nat); ξ⟩
          = (B⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (n⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp]
    have ihm' := ihm agr
    asimp at ihm'
    exact .appIm ihm' (Static.Typed.rename tyn agr.toStatic)
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrgΘ mrgΔ erm ern ihm ihn =>
    intro Γ' Δ' ξ agr
    rw [show (B[Chan.var_Chan; n..])⟨(id : Nat → Nat); ξ⟩
          = (B⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (n⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp]
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    have ihm' := ihm agr1
    asimp at ihm'
    exact .appEx mrgΘ mrgΔ' ihm' (ihn agr2)
  | @pairIm Θ Γ Δ A B m n n' t tyS tym ern ihn =>
    intro Γ' Δ' ξ agr
    have tym' := Static.Typed.rename tym agr.toStatic
    have ihn' := ihn agr
    have tyS' := Static.Typed.rename tyS agr.toStatic
    asimp at tyS' ⊢
    rw [show (B[Chan.var_Chan; m..])⟨(id : Nat → Nat); ξ⟩
          = (B⟨(id : Nat → Nat); upRen_Term_Term ξ⟩)[Chan.var_Chan; (m⟨(id : Nat → Nat); ξ⟩)..]
          from by asimp] at ihn'
    exact .pairIm tyS' tym' ihn'
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrgΘ mrgΔ tyS erm ern ihm ihn =>
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
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    intro Γ' Δ' ξ agr
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    cases tyC.wf with
    | @cons _ _ s' _ tyAB =>
      cases ern.wf with
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
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrgΘ mrgΔ tyC erm ern ihm ihn =>
    intro Γ' Δ' ξ agr
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    cases tyC.wf with
    | @cons _ _ s' _ tyAB =>
      cases ern.wf with
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
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrgΘ mrgΔ tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    intro Γ' Δ' ξ agr
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    have tyBool : Γ ⊢ Term.bool : Term.srt .U := .bool erm.toStatic.wf
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
  | @pure Θ Γ Δ m m' A erm ihm =>
    intro Γ' Δ' ξ agr; asimp; exact .pure (ihm agr)
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrgΘ mrgΔ tyB erm ern ihm ihn =>
    intro Γ' Δ' ξ agr
    obtain ⟨Δ1', Δ2', mrgΔ', agr1, agr2⟩ := agr.merge mrgΔ
    cases ern.wf with
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
  | @fork Θ Γ Δ A m m' erm ihm =>
    intro Γ' Δ' ξ agr
    asimp
    cases erm.wf with
    | @cons _ _ _ s' _ tyCh =>
      have ihm' := ihm (.cons tyCh agr)
      asimp at ihm'
      exact .fork ihm'
  | @recv Θ Γ Δ r1 r2 A B m m' i hxor erm ihm =>
    intro Γ' Δ' ξ agr; asimp; exact .recv hxor (ihm agr)
  | @send Θ Γ Δ r1 r2 A B m m' i hxor erm ihm =>
    intro Γ' Δ' ξ agr; asimp; exact .send hxor (ihm agr)
  | @close Θ Γ Δ b m m' erm ihm =>
    intro Γ' Δ' ξ agr; asimp; exact .close (ihm agr)
  | @conv Θ Γ Δ A B m m' s eq erm tyB ihm =>
    intro Γ' Δ' ξ agr
    exact .conv (Static.conv_ren ξ eq) (ihm agr) (Static.Typed.rename tyB agr.toStatic)

/-- Unrestricted weakening (Coq `era_weakenU`). -/
lemma Erased.weakenU {Θ Γ Δ m m' A B} (tyB : Γ ⊢ B : .srt Srt.U)
    (erm : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) :
    Θ ⨾ (B :: Γ) ⨾ (B :U Δ) ⊢ m⟨(id : Nat → Nat); ↑⟩ ~ m'⟨(id : Nat → Nat); ↑⟩ : A⟨(id : Nat → Nat); ↑⟩ :=
  erm.rename (.wkU tyB (.refl erm.wf))

/-- Null weakening (Coq `era_weakenN`). -/
lemma Erased.weakenN {Θ Γ Δ m m' A B s} (tyB : Γ ⊢ B : .srt s)
    (erm : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) :
    Θ ⨾ (B :: Γ) ⨾ (none :: Δ) ⊢ m⟨(id : Nat → Nat); ↑⟩ ~ m'⟨(id : Nat → Nat); ↑⟩ : A⟨(id : Nat → Nat); ↑⟩ :=
  erm.rename (.wkN tyB (.refl erm.wf))

/-- Unrestricted weakening up to equality (Coq `era_eweakenU`). -/
lemma Erased.eweakenU {Θ Γ Δ m m' n n' A A' B}
    (em : m' = m⟨(id : Nat → Nat); ↑⟩) (en : n' = n⟨(id : Nat → Nat); ↑⟩)
    (eA : A' = A⟨(id : Nat → Nat); ↑⟩)
    (tyB : Γ ⊢ B : .srt Srt.U) (erm : Θ ⨾ Γ ⨾ Δ ⊢ m ~ n : A) :
    Θ ⨾ (B :: Γ) ⨾ (B :U Δ) ⊢ m' ~ n' : A' := by
  subst em; subst en; subst eA; exact erm.weakenU tyB

/-- Null weakening up to equality (Coq `era_eweakenN`). -/
lemma Erased.eweakenN {Θ Γ Δ m m' n n' A A' B s}
    (em : m' = m⟨(id : Nat → Nat); ↑⟩) (en : n' = n⟨(id : Nat → Nat); ↑⟩)
    (eA : A' = A⟨(id : Nat → Nat); ↑⟩)
    (tyB : Γ ⊢ B : .srt s) (erm : Θ ⨾ Γ ⨾ Δ ⊢ m ~ n : A) :
    Θ ⨾ (B :: Γ) ⨾ (none :: Δ) ⊢ m' ~ n' : A' := by
  subst em; subst en; subst eA; exact erm.weakenN tyB

end TLLC.Erasure
