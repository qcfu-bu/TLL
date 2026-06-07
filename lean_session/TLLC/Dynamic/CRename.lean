import TLLC.Dynamic.Subst
import TLLC.Static.CRename

/-!
# Dynamic channel renaming

Port of `coq_session/dyn_cren.v`: the channel-renaming agreement relation `CtxCRen`
(Coq `dyn_ctx_cren`), which renames the *process* context `Θ` (a `Ctx` whose live slots hold channel
typings `Ch r A :L`); its structural lemmas (`CtxCRen.empty`/`key`/`just`/`merge`, Coq
`dyn_ctx_cren_empty`/`_key`/`_just`/`_merge`); the headline preservation metatheorem `Typed.crename`
(Coq `dyn_crename` — channel renaming preserves typing, renaming only the term `m` and the process
context `Θ`, leaving `Γ`/`Δ`/the type `A` fixed); and the channel strengthening/weakening corollaries
`Typed.cstrengthen`/`Typed.cweaken` (Coq `dyn_cstrengthen`/`dyn_cweaken`).

Channel renaming `cren ξ m` is the channel autosubst slot held at the identity term map:
`m⟨ξ; (id : Nat → Nat)⟩`. `cren (+1) m` (the weakening shift) is `m⟨((· + 1) : Nat → Nat); id⟩`
(cf. `Just.zero` in `Context.lean`). The agreement constructors mirror the Coq `upren`/`>>>`
combinators: `upRen_Chan_Chan ξ` lifts a channel renaming under a `Ch`-binding slot, `funcomp Nat.succ ξ`
is Coq `ξ >>> (+1)` (target gains a null slot), and `funcomp ξ (· - 1)` is Coq `(-1) >>> ξ` (source
has a null slot — note the *truncated* `Nat` subtraction, so the `(+1) >>> (-1) = id` identity in
`cstrengthen` is discharged by `omega`).

The proj/ite/chan reshapes reuse the static channel-renaming workhorse `Static.cren_conv0`
(`cren ξ m ≃ m`, since channels reduce freely) threaded through `conv`; the type is recovered via
the static `Static.Typed.crename`/`Static.Typed.subst`. The lam/fork context-conversions route through
the dynamic `Typed.ctx_conv0`/`ctx_conv1`, and the proj branch motive's well-sortedness is factored
into the helper `projMotive_wellSorted` (the static `Σ`-elim pair-injection substitution). Unlike the
static port, no per-binder `cren_up*_eq` bridges are needed: under a Term binder the channel map lift
`upRen_Term_Chan ξ` collapses to `ξ` and `asimp` discharges the body subjects directly.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- Channel-renaming agreement on the process context `Θ` (Coq `dyn_ctx_cren`). -/
inductive CtxCRen : (Nat → Nat) → Ctx → Ctx → Prop where
  | O {Θ} :
    CtxCRen (id : Nat → Nat) Θ Θ
  | ty {ξ r A Θ Θ'} :
    [] ⊢ A : .proto →
    CtxCRen ξ Θ Θ' →
    CtxCRen (upRen_Chan_Chan ξ)
      (.ch r A :L Θ) (.ch r (A⟨ξ; (id : Nat → Nat)⟩) :L Θ')
  | n {ξ Θ Θ'} :
    CtxCRen ξ Θ Θ' →
    CtxCRen (upRen_Chan_Chan ξ) (□: Θ) (□: Θ')
  | plus {ξ Θ Θ'} :
    CtxCRen ξ Θ Θ' →
    CtxCRen (funcomp Nat.succ ξ) Θ (□: Θ')
  | minus {ξ Θ Θ'} :
    CtxCRen ξ Θ Θ' →
    CtxCRen (funcomp ξ (· - 1)) (□: Θ) Θ'


/-! ## Structural lemmas. -/

/-- Channel renaming preserves emptiness of the process context (Coq `dyn_ctx_cren_empty`). -/
lemma CtxCRen.empty {Θ Θ' ξ} (agr : CtxCRen ξ Θ Θ') (emp : Empty Θ) : Empty Θ' := by
  induction agr with
  | O => exact emp
  | ty _ _ ih => cases emp
  | n _ ih => cases emp with | null e => exact .null (ih e)
  | plus _ ih => exact .null (ih emp)
  | minus _ ih => cases emp with | null e => exact ih e

/-- Channel renaming transports keys (Coq `dyn_ctx_cren_key`). -/
lemma CtxCRen.key {Θ Θ' ξ s} (agr : CtxCRen ξ Θ Θ') (k : Θ ▷ s) : Θ' ▷ s := by
  induction agr generalizing s with
  | O => exact k
  | ty _ _ ih => cases k with | L _ k' => exact .L _ (ih k')
  | n _ ih => cases k with | null k' => exact .null (ih k')
  | plus _ ih => exact .null (ih k)
  | minus _ ih => cases k with | null k' => exact ih k'

/-- Channel renaming transports `Just` lookups (Coq `dyn_ctx_cren_just`). -/
lemma CtxCRen.just {Θ Θ' A x ξ} (agr : CtxCRen ξ Θ Θ') (js : Just Θ x A) :
    Just Θ' (ξ x) (A⟨ξ; (id : Nat → Nat)⟩) := by
  induction agr generalizing A x with
  | @O Θ =>
    rw [show A⟨(id : Nat → Nat); (id : Nat → Nat)⟩ = A from by asimp]
    exact js
  | @ty ξ r A0 Θ Θ' tyA agr ih =>
    have hmap : funcomp (upRen_Chan_Chan ξ) Nat.succ = funcomp Nat.succ ξ := by
      funext y; cases y <;> rfl
    cases js with
    | zero emp =>
      -- lookup type is `(ch r A0)⟨+1; id⟩`; target slot holds `ch r (A0⟨ξ; id⟩)`
      rw [show ((Term.ch r A0)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨upRen_Chan_Chan ξ;
            (id : Nat → Nat)⟩
            = (Term.ch r (A0⟨ξ; (id : Nat → Nat)⟩))⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            from by asimp; rw [hmap]]
      exact Just.zero (agr.empty emp)
  | @n ξ Θ Θ' agr ih =>
    have hmap : funcomp (upRen_Chan_Chan ξ) Nat.succ = funcomp Nat.succ ξ := by
      funext y; cases y <;> rfl
    cases js with
    | @null _ A1 x0 js =>
      rw [show (A1⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨upRen_Chan_Chan ξ; (id : Nat → Nat)⟩
            = (A1⟨ξ; (id : Nat → Nat)⟩)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ from by
            asimp; rw [hmap]]
      exact Just.null (ih js)
  | @plus ξ Θ Θ' agr ih =>
    have h := Just.null (ih js)
    rw [show (A⟨ξ; (id : Nat → Nat)⟩)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
          = A⟨funcomp Nat.succ ξ; (id : Nat → Nat)⟩ from by asimp] at h
    exact h
  | @minus ξ Θ Θ' agr ih =>
    cases js with
    | @null _ A1 x0 js =>
      have ih' := ih js
      have hmap : funcomp (funcomp ξ (· - 1)) Nat.succ = ξ := by
        funext y; show ξ (y + 1 - 1) = ξ y; rw [Nat.add_sub_cancel]
      rw [show funcomp ξ (· - 1) (x0 + 1) = ξ x0 from by
            show ξ (x0 + 1 - 1) = ξ x0; rw [Nat.add_sub_cancel],
          show (A1⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨funcomp ξ (· - 1); (id : Nat → Nat)⟩
            = A1⟨ξ; (id : Nat → Nat)⟩ from by asimp; rw [hmap]]
      exact ih'

/-- Channel renaming is compatible with merge (Coq `dyn_ctx_cren_merge`). -/
lemma CtxCRen.merge {Θ1 Θ2 Θ Θ' ξ} (agr : CtxCRen ξ Θ Θ') :
    Merge Θ1 Θ2 Θ →
    ∃ Θ1' Θ2', Merge Θ1' Θ2' Θ' ∧ CtxCRen ξ Θ1 Θ1' ∧ CtxCRen ξ Θ2 Θ2' := by
  induction agr generalizing Θ1 Θ2 with
  | @O Θ => intro mrg; exact ⟨Θ1, Θ2, mrg, .O, .O⟩
  | @ty ξ r A Θ Θ' tyA agr ih =>
    intro mrg
    cases mrg with
    | right1 _ mrg' =>
      obtain ⟨Θ1', Θ2', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨.ch r (A⟨ξ; (id : Nat → Nat)⟩) :L Θ1', □: Θ2',
        .right1 _ mrg', .ty tyA agr1, .n agr2⟩
    | right2 _ mrg' =>
      obtain ⟨Θ1', Θ2', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨□: Θ1', .ch r (A⟨ξ; (id : Nat → Nat)⟩) :L Θ2',
        .right2 _ mrg', .n agr1, .ty tyA agr2⟩
  | @n ξ Θ Θ' agr ih =>
    intro mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θ1', Θ2', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨□: Θ1', □: Θ2', .null mrg', .n agr1, .n agr2⟩
  | @plus ξ Θ Θ' agr ih =>
    intro mrg
    obtain ⟨Θ1', Θ2', mrg', agr1, agr2⟩ := ih mrg
    exact ⟨□: Θ1', □: Θ2', .null mrg', .plus agr1, .plus agr2⟩
  | @minus ξ Θ Θ' agr ih =>
    intro mrg
    cases mrg with
    | null mrg' =>
      obtain ⟨Θ1', Θ2', mrg', agr1, agr2⟩ := ih mrg'
      exact ⟨Θ1', Θ2', mrg', .minus agr1, .minus agr2⟩

/-- Well-sortedness of the `proj` branch motive `C[⟨1,0⟩ .: (+2)]` under the pattern context
    `B :: A :: Γ` (the static `Σ`-elim pair-injection substitution, factored out of the proj case so
    both `projIm`/`projEx` can reuse it; mirrors the `hwit` construction in `Static.Typed.crename`). -/
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

/-! ## Channel renaming preserves typing. -/

/-- Channel renaming preserves dynamic typing (Coq `dyn_crename`). Only the term `m` and the process
    context `Θ` are renamed; `Γ`/`Δ` and the type `A` are left fixed (channels are context-stable). -/
lemma Typed.crename {Θ Γ Δ m A} (tym : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    ∀ {Θ' ξ}, CtxCRen ξ Θ Θ' → Θ' ⨾ Γ ⨾ Δ ⊢ m⟨ξ; (id : Nat → Nat)⟩ : A := by
  induction tym with
  | @var Θ Γ Δ x s A emp wf shs dhs =>
    intro Θ' ξ agr
    exact .var (agr.empty emp) wf shs dhs
  | @lamIm Θ Γ Δ A B m s k1 k2 tym ihm =>
    intro Θ' ξ agr
    cases tym.wf with
    | @null _ _ _ s' _ tyA =>
      obtain ⟨r, tyB⟩ := tym.validity
      have tyAr := Static.Typed.crename tyA ξ
      have ihm' := ihm agr
      have hm := Typed.ctx_conv0 (Static.cren_conv0 .refl ξ) tyAr ihm'
      asimp
      exact .conv (Static.conv_pi (Static.cren_conv0 .refl ξ) .refl)
        (.lamIm (agr.key k1) k2 hm) (.pi tyA tyB)
  | @lamEx Θ Γ Δ A B m s t k1 k2 tym ihm =>
    intro Θ' ξ agr
    cases tym.wf with
    | @cons _ _ _ s' _ tyA =>
      obtain ⟨r, tyB⟩ := tym.validity
      have tyAr := Static.Typed.crename tyA ξ
      have ihm' := ihm agr
      have hm := Typed.ctx_conv1 (Static.cren_conv0 .refl ξ) tyAr ihm'
      asimp
      exact .conv (Static.conv_pi (Static.cren_conv0 .refl ξ) .refl)
        (.lamEx (agr.key k1) k2 hm) (.pi tyA tyB)
  | @appIm Θ Γ Δ A B m n s tym tyn ihm =>
    intro Θ' ξ agr
    obtain ⟨r, tyP⟩ := tym.validity
    obtain ⟨t, tyB, _⟩ := Static.pi_inv tyP
    have tyBn := tyB.subst tyn
    asimp at tyBn
    have ihm' := ihm agr
    asimp at ihm'
    have eq : B[Chan.var_Chan; (n⟨ξ; (id : Nat → Nat)⟩)..] ≃ B[Chan.var_Chan; n..] :=
      Static.conv_beta (Static.cren_conv0 .refl ξ)
    exact .conv eq (.appIm ihm' (Static.Typed.crename tyn ξ)) tyBn
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrgΘ mrgΔ tym tyn ihm ihn =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    obtain ⟨r, tyP⟩ := tym.validity
    obtain ⟨t, tyB, _⟩ := Static.pi_inv tyP
    have tyBn := tyB.subst tyn.toStatic
    asimp at tyBn
    have ihm' := ihm agr1
    asimp at ihm'
    apply Typed.conv (Static.conv_beta (Static.cren_conv0 .refl ξ)) _ tyBn
    exact .appEx mrgΘ' mrgΔ ihm' (ihn agr2)
  | @pairIm Θ Γ Δ A B m n t tyS tym tyn ihn =>
    intro Θ' ξ agr
    obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
    have tym' := Static.Typed.crename tym ξ
    have tyBm := tyB.subst tym'
    asimp at tyBm
    have ihn' := ihn agr
    asimp at ihn' ⊢
    have ihn'' : Θ' ⨾ Γ ⨾ Δ ⊢ n⟨ξ; (id : Nat → Nat)⟩ : B[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..] :=
      Typed.conv (ARS.conv_sym (Static.conv_beta (Static.cren_conv0 .refl ξ))) ihn' tyBm
    exact .pairIm tyS tym' ihn''
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrgΘ mrgΔ tyS tym tyn ihm ihn =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
    have tym' := Static.Typed.crename tym.toStatic ξ
    have tyBm := tyB.subst tym'
    asimp at tyBm
    have ihn' := ihn agr2
    asimp at ihn' ⊢
    have ihn'' : Θ2' ⨾ Γ ⨾ Δ2 ⊢ n⟨ξ; (id : Nat → Nat)⟩ : B[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..] :=
      Typed.conv (ARS.conv_sym (Static.conv_beta (Static.cren_conv0 .refl ξ))) ihn' tyBm
    exact .pairEx mrgΘ' mrgΔ tyS (ihm agr1) ihn''
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have ihm' := ihm agr1
    have ihn' := ihn agr2
    have ihC := Static.Typed.crename tyC ξ
    -- the well-sorted renamed-motive substitution (built exactly as in `Static.Typed.crename`)
    have hwit := projMotive_wellSorted (i := .im) ihC tyC.wf
    -- reshape the branch under the renamed motive (channel ren commutes with the term subst)
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
    have tyn'' := Typed.conv (ARS.conv_sym eqn) ihn' hwit
    -- convert the projection's result type back to the un-renamed `C[m/]`
    have eqC : (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..]
        ≃ C[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (Static.cren_conv0 .refl ξ))
        (Static.conv_subst (m..) (Static.cren_conv0 .refl ξ))
    asimp
    exact .conv eqC (.projIm mrgΘ' mrgΔ ihC ihm' tyn'') (tyC.subst tym.toStatic)
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
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
    have tyn'' := Typed.conv (ARS.conv_sym eqn) ihn' hwit
    have eqC : (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..]
        ≃ C[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (Static.cren_conv0 .refl ξ))
        (Static.conv_subst (m..) (Static.cren_conv0 .refl ξ))
    asimp
    exact .conv eqC (.projEx mrgΘ' mrgΔ ihC ihm' tyn'') (tyC.subst tym.toStatic)
  | @one Θ Γ Δ emp wf k =>
    intro Θ' ξ agr; asimp; exact .one (agr.empty emp) wf k
  | @tt Θ Γ Δ emp wf k =>
    intro Θ' ξ agr; asimp; exact .tt (agr.empty emp) wf k
  | @ff Θ Γ Δ emp wf k =>
    intro Θ' ξ agr; asimp; exact .ff (agr.empty emp) wf k
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrgΘ mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have wf := tym.wf
    have tyA' := Static.Typed.crename tyA ξ
    have h1 := tyA'.subst (Static.Typed.tt wf.toStatic)
    have h2 := tyA'.subst (Static.Typed.ff wf.toStatic)
    have ihm' := ihm agr1
    have ihn1' := ihn1 agr2
    have ihn2' := ihn2 agr2
    have tyn1' : Θ2' ⨾ Γ ⨾ Δ2 ⊢ n1⟨ξ; (id : Nat → Nat)⟩
        : (A⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; Term.tt..] :=
      Typed.conv (ARS.conv_sym (Static.conv_subst (Term.tt..) (Static.cren_conv0 .refl ξ))) ihn1' h1
    have tyn2' : Θ2' ⨾ Γ ⨾ Δ2 ⊢ n2⟨ξ; (id : Nat → Nat)⟩
        : (A⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; Term.ff..] :=
      Typed.conv (ARS.conv_sym (Static.conv_subst (Term.ff..) (Static.cren_conv0 .refl ξ))) ihn2' h2
    have eq : (A⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..]
        ≃ A[Chan.var_Chan; m..] :=
      ARS.conv_trans (Static.conv_beta (Static.cren_conv0 .refl ξ))
        (Static.conv_subst (m..) (Static.cren_conv0 .refl ξ))
    asimp
    apply Typed.conv eq _ (tyA.subst tym.toStatic)
    exact .ite mrgΘ' mrgΔ tyA' ihm' tyn1' tyn2'
  | @pure Θ Γ Δ m A tym ihm =>
    intro Θ' ξ agr; asimp; exact .pure (ihm agr)
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrgΘ mrgΔ tyB tym tyn ihm ihn =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrgΘ', agr1, agr2⟩ := agr.merge mrgΘ
    have ihn' := ihn agr2
    asimp
    exact .mlet mrgΘ' mrgΔ tyB (ihm agr1) ihn'
  | @chan Θ Γ Δ r x A js wf k tyA =>
    intro Θ' ξ agr
    -- `js' : Just Θ' (ξ x) (ch r (A⟨ξ; id⟩))`
    have js' := agr.just js
    rw [show ((Term.ch r A))⟨ξ; (id : Nat → Nat)⟩ = Term.ch r (A⟨ξ; (id : Nat → Nat)⟩) from by asimp]
      at js'
    have tyAr := Static.Typed.crename tyA ξ
    -- well-sortedness of the goal type `ch r (A⟨id; +Γ.length⟩)`
    have tych : Γ ⊢ Term.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩) : .srt .L := by
      apply Static.Typed.ch
      have h := Static.Typed.rename tyA (Static.Wf.agreeRen wf.toStatic)
      asimp at h
      exact h
    -- conversion `ch r ((A⟨ξ;id⟩)⟨id; +Γ.length⟩) ≃ ch r (A⟨id; +Γ.length⟩)`
    have eq : Term.ch r ((A⟨ξ; (id : Nat → Nat)⟩)⟨(id : Nat → Nat); (· + Γ.length)⟩)
        ≃ Term.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩) := by
      apply Static.conv_ch
      rw [show (A⟨ξ; (id : Nat → Nat)⟩)⟨(id : Nat → Nat); (· + Γ.length)⟩
            = (A⟨(id : Nat → Nat); (· + Γ.length)⟩)⟨ξ; (id : Nat → Nat)⟩ from by asimp]
      exact Static.cren_conv0 .refl ξ
    asimp
    exact .conv eq (Typed.chan js' wf k tyAr) tych
  | @fork Θ Γ Δ A m tym ihm =>
    intro Θ' ξ agr
    have wf := tym.wf
    cases wf with
    | @cons _ _ _ s' _ tyCh =>
      obtain ⟨tyA, _⟩ := Static.ch_inv tyCh
      have tyAr := Static.Typed.crename tyA ξ
      have ihm' := ihm agr
      have hm := Typed.ctx_conv1 (Static.conv_ch (Static.cren_conv0 .refl ξ))
        (Static.Typed.ch tyAr) ihm'
      asimp
      apply Typed.conv (Static.conv_M (Static.conv_ch (Static.cren_conv0 .refl ξ))) _
        (Static.Typed.M (Static.Typed.ch tyA))
      exact .fork hm
  | @recv Θ Γ Δ r1 r2 A B m i e tym ihm =>
    intro Θ' ξ agr; asimp; exact .recv e (ihm agr)
  | @send Θ Γ Δ r1 r2 A B m i e tym ihm =>
    intro Θ' ξ agr; asimp; exact .send e (ihm agr)
  | @close Θ Γ Δ b m tym ihm =>
    intro Θ' ξ agr; asimp; exact .close (ihm agr)
  | @conv Θ Γ Δ A B m s eq tym tyB ihm =>
    intro Θ' ξ agr
    exact .conv eq (ihm agr) tyB

/-- Channel strengthening (Coq `dyn_cstrengthen`). -/
lemma Typed.cstrengthen {Θ Γ Δ m A}
    (tym : (□: Θ) ⨾ Γ ⨾ Δ ⊢ m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ : A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m : A := by
  have h := tym.crename (Θ' := Θ) (ξ := funcomp (id : Nat → Nat) (· - 1)) (.minus .O)
  have hmap : funcomp ((· - 1) : Nat → Nat) ((· + 1) : Nat → Nat) = (id : Nat → Nat) := by
    funext x; simp only [funcomp, id]; omega
  rw [show (m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨funcomp (id : Nat → Nat) (· - 1);
        (id : Nat → Nat)⟩ = m from by
        asimp; rw [hmap]; asimp] at h
  exact h

/-- Channel weakening (Coq `dyn_cweaken`). -/
lemma Typed.cweaken {Θ Γ Δ m A} (tym : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    (□: Θ) ⨾ Γ ⨾ Δ ⊢ m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ : A := by
  have h := tym.crename (.plus .O)
  rw [show m⟨funcomp Nat.succ (id : Nat → Nat); (id : Nat → Nat)⟩
        = m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ from by asimp] at h
  exact h

end TLLC.Dynamic
