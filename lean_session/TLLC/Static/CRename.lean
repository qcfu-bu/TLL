import TLLC.Static.Validity

/-!
# Static channel renaming

Port of `coq_session/sta_cren.v`: the channel-renaming compatibility lemmas for parallel reduction,
multi-step reduction and conversion (`cren_pstep0`/`cren_pstep`/`cren_pred0`/`cren_pred`/
`cren_conv0`/`cren_conv`, Coq `sta_cren_pstep0`/…), the arity/guardedness preservation lemmas
(`cren_arity_proto`/`cren_guarded`, Coq `sta_cren_arity_proto`/`sta_cren_guarded`), the headline
preservation metatheorem `Typed.crename` (Coq `sta_crename` — channel renaming preserves typing),
its up-to-equality variant `Typed.ecrename` (Coq `sta_ecrename`), and the inverse lemmas
`cren_arity_proto_inv`/`cren_guarded_inv`/`Typed.crename_inv` (Coq `sta_cren_arity_proto_inv`/…),
which strip a channel renaming.

Channel renaming is the *other* autosubst slot: where term renaming `Rename.lean` writes
`m⟨(id : Nat → Nat); ξ⟩` (channels fixed, term map renamed), channel renaming `cren ξ m` is
`m⟨ξ; (id : Nat → Nat)⟩` (the channel map renamed, term map fixed). Because `Chan` is a first-class
autosubst sort the channel-substitution algebra (`term_cren_beta1`/`term_cren_beta2`/
`term_cren_subst`) is discharged by `asimp`. Channels reduce freely (`PStep.chan : chan c ≈> chan c'`
for any `c c'`), which is exactly what makes `cren_pstep0` go through: renaming only touches channel
variables, and a renamed channel still reduces to the unrenamed reduct.

As elsewhere, Coq's implicit/explicit constructor pairs are merged via the `Rlv`/`Bool` tag; the Coq
`sta_letin0`/`sta_letin1` proj cases collapse into the single `proj` case. The Coq proof routes
through `sta0_type`; here we induct directly on `Typed`/`Wf` (via `Typed.rec` with a `Wf` motive),
recovering domain typings from `.wf` exactly as `Typed.rename`/`Typed.substitution` do, so the Coq
`sta0_to_sta`/`sta_sta0_type` bookkeeping is unnecessary.
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-! ## Compatibility of parallel reduction, multi-step and conversion with channel renaming. -/

/-- Bridge a one-Term-binder channel renaming of the redex back to the literal-`id` term slot. The
    term slot under a binder normalizes to `upRen_Term_Term id`, which is `id` (Lean autosubst
    artifact, no Coq counterpart); the channel slot lifts trivially (`upRen_Term_Chan ξ = ξ`). -/
private lemma pstep0_up1 {B B' : Term} (ξ : Nat → Nat) (h : B⟨ξ; (id : Nat → Nat)⟩ ≈> B') :
    B⟨ξ; upRen_Term_Term (id : Nat → Nat)⟩ ≈> B' := by
  rw [show upRen_Term_Term (id : Nat → Nat) = (id : Nat → Nat) from by asimp]; exact h

/-- The two-Term-binder version of `pstep0_up1` (for the `proj`/`projE` motive slot). -/
private lemma pstep0_up2 {B B' : Term} (ξ : Nat → Nat) (h : B⟨ξ; (id : Nat → Nat)⟩ ≈> B') :
    B⟨ξ; upRen_Term_Term (upRen_Term_Term (id : Nat → Nat))⟩ ≈> B' := by
  rw [show upRen_Term_Term (upRen_Term_Term (id : Nat → Nat)) = (id : Nat → Nat) from by asimp]
  exact h

/-- Channel renaming of the redex still reduces to the unrenamed reduct (Coq `sta_cren_pstep0`).
    This holds because the only positions a channel renaming touches are channel variables, and
    `PStep.chan` lets a renamed channel reduce to anything. -/
lemma cren_pstep0 {m n : Term} (ps : m ≈> n) (ξ : Nat → Nat) :
    m⟨ξ; (id : Nat → Nat)⟩ ≈> n := by
  induction ps generalizing ξ with
  | var => exact PStep.var
  | srt => exact PStep.srt
  | unit => exact PStep.unit
  | one => exact PStep.one
  | bool => exact PStep.bool
  | tt => exact PStep.tt
  | ff => exact PStep.ff
  | proto => exact PStep.proto
  | stop => exact PStep.stop
  | box => exact PStep.box
  | chan => exact PStep.chan
  | pi _ _ ihA ihB => exact PStep.pi (ihA ξ) (pstep0_up1 ξ (ihB ξ))
  | lam _ _ ihA ihm => exact PStep.lam (ihA ξ) (pstep0_up1 ξ (ihm ξ))
  | app _ _ ihm ihn => exact PStep.app (ihm ξ) (ihn ξ)
  | beta _ _ ihm ihn => exact PStep.beta (pstep0_up1 ξ (ihm ξ)) (ihn ξ)
  | sig _ _ ihA ihB => exact PStep.sig (ihA ξ) (pstep0_up1 ξ (ihB ξ))
  | pair _ _ ihm ihn => exact PStep.pair (ihm ξ) (ihn ξ)
  | proj _ _ _ ihA ihm ihn =>
    exact PStep.proj (pstep0_up1 ξ (ihA ξ)) (ihm ξ) (pstep0_up2 ξ (ihn ξ))
  | projE _ _ _ ihm1 ihm2 ihn =>
    exact PStep.projE (ihm1 ξ) (ihm2 ξ) (pstep0_up2 ξ (ihn ξ))
  | fix _ _ ihA ihm => exact PStep.fix (ihA ξ) (pstep0_up1 ξ (ihm ξ))
  | fixE _ _ ihA ihm => exact PStep.fixE (ihA ξ) (pstep0_up1 ξ (ihm ξ))
  | ite _ _ _ _ ihA ihm ihn1 ihn2 =>
    exact PStep.ite (pstep0_up1 ξ (ihA ξ)) (ihm ξ) (ihn1 ξ) (ihn2 ξ)
  | iteT _ ih => exact PStep.iteT (ih ξ)
  | iteF _ ih => exact PStep.iteF (ih ξ)
  | M _ ihA => exact PStep.M (ihA ξ)
  | pure _ ihm => exact PStep.pure (ihm ξ)
  | mlet _ _ ihm ihn => exact PStep.mlet (ihm ξ) (pstep0_up1 ξ (ihn ξ))
  | mletE _ _ ihm ihn => exact PStep.mletE (ihm ξ) (pstep0_up1 ξ (ihn ξ))
  | act _ _ ihA ihB => exact PStep.act (ihA ξ) (pstep0_up1 ξ (ihB ξ))
  | ch _ ihA => exact PStep.ch (ihA ξ)
  | fork _ _ ihA ihm => exact PStep.fork (ihA ξ) (pstep0_up1 ξ (ihm ξ))
  | recv _ ihm => exact PStep.recv (ihm ξ)
  | send _ ihm => exact PStep.send (ihm ξ)
  | close _ ihm => exact PStep.close (ihm ξ)

/-- Parallel reduction is closed under any simultaneous renaming of both autosubst slots; the
    channel specialization (term slot `id`) gives Coq `sta_cren_pstep`. A generic term slot `ζ`
    keeps the under-binder lift `upRen_Term_Term ζ` symbolic, avoiding the literal-`id` artifact, and
    the redex cases reduce to channel/term-substitution commutation (`asimp`). -/
private lemma pstep_ren {m n : Term} (ps : m ≈> n) (ξ ζ : Nat → Nat) :
    m⟨ξ; ζ⟩ ≈> n⟨ξ; ζ⟩ := by
  induction ps generalizing ξ ζ with
  | var => exact PStep.var
  | srt => exact PStep.srt
  | unit => exact PStep.unit
  | one => exact PStep.one
  | bool => exact PStep.bool
  | tt => exact PStep.tt
  | ff => exact PStep.ff
  | proto => exact PStep.proto
  | stop => exact PStep.stop
  | box => exact PStep.box
  | chan => exact PStep.chan
  | pi _ _ ihA ihB => exact PStep.pi (ihA ξ ζ) (ihB (upRen_Term_Chan ξ) (upRen_Term_Term ζ))
  | lam _ _ ihA ihm => exact PStep.lam (ihA ξ ζ) (ihm (upRen_Term_Chan ξ) (upRen_Term_Term ζ))
  | app _ _ ihm ihn => exact PStep.app (ihm ξ ζ) (ihn ξ ζ)
  | @beta A m m' n n' r s _ _ ihm ihn =>
    rw [show (m'[Chan.var_Chan; n'..])⟨ξ; ζ⟩
          = (m'⟨upRen_Term_Chan ξ; upRen_Term_Term ζ⟩)[Chan.var_Chan; (n'⟨ξ; ζ⟩)..]
          from by asimp]
    exact PStep.beta (ihm (upRen_Term_Chan ξ) (upRen_Term_Term ζ)) (ihn ξ ζ)
  | sig _ _ ihA ihB => exact PStep.sig (ihA ξ ζ) (ihB (upRen_Term_Chan ξ) (upRen_Term_Term ζ))
  | pair _ _ ihm ihn => exact PStep.pair (ihm ξ ζ) (ihn ξ ζ)
  | proj _ _ _ ihA ihm ihn =>
    exact PStep.proj (ihA (upRen_Term_Chan ξ) (upRen_Term_Term ζ)) (ihm ξ ζ)
      (ihn (upRen_Term_Chan (upRen_Term_Chan ξ)) (upRen_Term_Term (upRen_Term_Term ζ)))
  | @projE A m1 m1' m2 m2' n n' r s _ _ _ ihm1 ihm2 ihn =>
    rw [show (n'[Chan.var_Chan; m2' .: m1' .: Term.var_Term])⟨ξ; ζ⟩
          = (n'⟨upRen_Term_Chan (upRen_Term_Chan ξ); upRen_Term_Term (upRen_Term_Term ζ)⟩)[Chan.var_Chan;
              (m2'⟨ξ; ζ⟩) .: (m1'⟨ξ; ζ⟩) .: Term.var_Term]
          from by asimp]
    exact PStep.projE (ihm1 ξ ζ) (ihm2 ξ ζ)
      (ihn (upRen_Term_Chan (upRen_Term_Chan ξ)) (upRen_Term_Term (upRen_Term_Term ζ)))
  | fix _ _ ihA ihm => exact PStep.fix (ihA ξ ζ) (ihm (upRen_Term_Chan ξ) (upRen_Term_Term ζ))
  | @fixE A A' m m' _ _ ihA ihm =>
    rw [show (m'[Chan.var_Chan; (Term.fix A' m')..])⟨ξ; ζ⟩
          = (m'⟨upRen_Term_Chan ξ; upRen_Term_Term ζ⟩)[Chan.var_Chan; ((Term.fix A' m')⟨ξ; ζ⟩)..]
          from by asimp]
    exact PStep.fixE (ihA ξ ζ) (ihm (upRen_Term_Chan ξ) (upRen_Term_Term ζ))
  | ite _ _ _ _ ihA ihm ihn1 ihn2 =>
    exact PStep.ite (ihA (upRen_Term_Chan ξ) (upRen_Term_Term ζ)) (ihm ξ ζ) (ihn1 ξ ζ) (ihn2 ξ ζ)
  | iteT _ ih => exact PStep.iteT (ih ξ ζ)
  | iteF _ ih => exact PStep.iteF (ih ξ ζ)
  | M _ ihA => exact PStep.M (ihA ξ ζ)
  | pure _ ihm => exact PStep.pure (ihm ξ ζ)
  | mlet _ _ ihm ihn => exact PStep.mlet (ihm ξ ζ) (ihn (upRen_Term_Chan ξ) (upRen_Term_Term ζ))
  | @mletE m m' n n' _ _ ihm ihn =>
    rw [show (n'[Chan.var_Chan; m'..])⟨ξ; ζ⟩
          = (n'⟨upRen_Term_Chan ξ; upRen_Term_Term ζ⟩)[Chan.var_Chan; (m'⟨ξ; ζ⟩)..]
          from by asimp]
    exact PStep.mletE (ihm ξ ζ) (ihn (upRen_Term_Chan ξ) (upRen_Term_Term ζ))
  | act _ _ ihA ihB => exact PStep.act (ihA ξ ζ) (ihB (upRen_Term_Chan ξ) (upRen_Term_Term ζ))
  | ch _ ihA => exact PStep.ch (ihA ξ ζ)
  | fork _ _ ihA ihm => exact PStep.fork (ihA ξ ζ) (ihm (upRen_Term_Chan ξ) (upRen_Term_Term ζ))
  | recv _ ihm => exact PStep.recv (ihm ξ ζ)
  | send _ ihm => exact PStep.send (ihm ξ ζ)
  | close _ ihm => exact PStep.close (ihm ξ ζ)

/-- Parallel reduction is closed under channel renaming (Coq `sta_cren_pstep`). -/
lemma cren_pstep {m n : Term} (ps : m ≈> n) (ξ : Nat → Nat) :
    m⟨ξ; (id : Nat → Nat)⟩ ≈> n⟨ξ; (id : Nat → Nat)⟩ :=
  pstep_ren ps ξ (id : Nat → Nat)

/-- Multi-step reduction of the redex reaches the unrenamed reduct (Coq `sta_cren_pred0`). -/
lemma cren_pred0 {m n : Term} (rd : m ≈>* n) (ξ : Nat → Nat) :
    m⟨ξ; (id : Nat → Nat)⟩ ≈>* n := by
  induction rd with
  | refl => exact ARS.star1 (cren_pstep0 (pstep_refl _) ξ)
  | tail _ st ih => exact ih.tail st

/-- Multi-step reduction is closed under channel renaming (Coq `sta_cren_pred`). -/
lemma cren_pred {m n : Term} (rd : m ≈>* n) (ξ : Nat → Nat) :
    m⟨ξ; (id : Nat → Nat)⟩ ≈>* n⟨ξ; (id : Nat → Nat)⟩ := by
  induction rd with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (cren_pstep st ξ)

/-- Conversion of the redex stays convertible to the unrenamed reduct (Coq `sta_cren_conv0`). -/
lemma cren_conv0 {m n : Term} (cv : m ≃ n) (ξ : Nat → Nat) :
    m⟨ξ; (id : Nat → Nat)⟩ ≃ n := by
  induction cv with
  | refl => exact ARS.conv1 (cren_pstep0 (pstep_refl _) ξ)
  | tail _ st ih => exact ih.tail st
  | taili _ st ih => exact ih.taili st

/-- Conversion is closed under channel renaming (Coq `sta_cren_conv`). -/
lemma cren_conv {m n : Term} (cv : m ≃ n) (ξ : Nat → Nat) :
    m⟨ξ; (id : Nat → Nat)⟩ ≃ n⟨ξ; (id : Nat → Nat)⟩ := by
  induction cv with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (cren_pstep st ξ)
  | taili _ st ih => exact ih.taili (cren_pstep st ξ)

/-! ## Arity and guardedness under channel renaming. -/

/-- Protocol arity is preserved by channel renaming (Coq `sta_cren_arity_proto`). -/
lemma cren_arity_proto {A : Term} (ξ : Nat → Nat) (ar : ArityProto A) :
    ArityProto (A⟨ξ; (id : Nat → Nat)⟩) := by
  induction A generalizing ξ with
  | proto => exact ar
  | pi A B i s ihA ihB =>
    show ArityProto (B⟨ξ; upRen_Term_Term (id : Nat → Nat)⟩)
    rw [show upRen_Term_Term (id : Nat → Nat) = (id : Nat → Nat) from by asimp]
    exact ihB ξ ar
  | _ => exact ar.elim

/-- Guardedness is preserved by channel renaming (Coq `sta_cren_guarded`). Channel renaming leaves
    every term variable untouched, so guardedness is preserved verbatim. -/
lemma cren_guarded {i : Nat} {m : Term} (ξ : Nat → Nat) (gr : Guarded i m) :
    Guarded i (m⟨ξ; (id : Nat → Nat)⟩) := by
  induction m generalizing i ξ with
  | var_Term x => exact gr
  | pi A B s r ihA ihB =>
    obtain ⟨gA, gB⟩ := gr
    refine ⟨ihA ξ gA, ?_⟩
    have := ihB ξ gB
    asimp at this ⊢
    exact this
  | lam A m s r ihA ihm =>
    obtain ⟨gA, gm⟩ := gr
    refine ⟨ihA ξ gA, ?_⟩
    have := ihm ξ gm
    asimp at this ⊢
    exact this
  | app m n r ihm ihn =>
    obtain ⟨gm, gn⟩ := gr
    exact ⟨ihm ξ gm, ihn ξ gn⟩
  | sig A B s r ihA ihB =>
    obtain ⟨gA, gB⟩ := gr
    refine ⟨ihA ξ gA, ?_⟩
    have := ihB ξ gB
    asimp at this ⊢
    exact this
  | pair m n s r ihm ihn =>
    obtain ⟨gm, gn⟩ := gr
    exact ⟨ihm ξ gm, ihn ξ gn⟩
  | proj A m n ihA ihm ihn =>
    obtain ⟨gA, gm, gn⟩ := gr
    refine ⟨?_, ihm ξ gm, ?_⟩
    · have := ihA ξ gA
      asimp at this ⊢
      exact this
    · have := ihn ξ gn
      asimp at this ⊢
      exact this
  | fix A m ihA ihm =>
    obtain ⟨gA, gm⟩ := gr
    refine ⟨ihA ξ gA, ?_⟩
    have := ihm ξ gm
    asimp at this ⊢
    exact this
  | ite A m n1 n2 ihA ihm ihn1 ihn2 =>
    obtain ⟨gA, gm, gn1, gn2⟩ := gr
    refine ⟨?_, ihm ξ gm, ihn1 ξ gn1, ihn2 ξ gn2⟩
    have := ihA ξ gA
    asimp at this ⊢
    exact this
  | M A ihA => exact ihA ξ gr
  | pure m ihm => exact ihm ξ gr
  | mlet m n ihm ihn =>
    obtain ⟨gm, gn⟩ := gr
    refine ⟨ihm ξ gm, ?_⟩
    have := ihn ξ gn
    asimp at this ⊢
    exact this
  | act b A B r ihA ihB => exact ihA ξ gr
  | ch b A ihA => exact ihA ξ gr
  | fork A m ihA ihm =>
    obtain ⟨gA, gm⟩ := gr
    refine ⟨ihA ξ gA, ?_⟩
    have := ihm ξ gm
    asimp at this ⊢
    exact this
  | recv m r ihm => exact ihm ξ gr
  | send m r ihm => exact ihm ξ gr
  | close b m ihm => exact ihm ξ gr
  | srt => exact gr
  | unit => exact gr
  | one => exact gr
  | bool => exact gr
  | tt => exact gr
  | ff => exact gr
  | proto => exact gr
  | stop => exact gr
  | chan c => exact gr
  | box => exact gr

/-! ## Channel renaming preserves typing. -/

/-- Bridge the literal-`id` channel renaming of a body subterm to the under-Term-binder form
    `⟨upRen_Term_Chan ξ; upRen_Term_Term id⟩` expected by a typing constructor (a Lean autosubst
    artifact: a Term binder lifts both slots, but neither shift touches a channel renaming). -/
private lemma cren_up1_eq (B : Term) (ξ : Nat → Nat) :
    B⟨ξ; (id : Nat → Nat)⟩ = B⟨upRen_Term_Chan ξ; upRen_Term_Term (id : Nat → Nat)⟩ := by asimp

/-- The two-binder analog of `cren_up1_eq` (for the `proj`/`ite`-style bodies under two binders). -/
private lemma cren_up2_eq (B : Term) (ξ : Nat → Nat) :
    B⟨ξ; (id : Nat → Nat)⟩
      = B⟨upRen_Term_Chan (upRen_Term_Chan ξ);
          upRen_Term_Term (upRen_Term_Term (id : Nat → Nat))⟩ := by asimp

/-- Channel renaming preserves typing (Coq `sta_crename`). The conclusion type is *not* renamed:
    channels are context-free (a `chan x` has a closed protocol type weakened by the context length),
    so the renamed subject keeps the same type. Each constructor adapts its type with the conversion
    compatibility lemma `cren_conv0` (yielding `cren ξ A ≃ A`) threaded through `conv`/`ctx_conv`.

    The Coq proof routes through `sta0_type` (whose `lam`/`act`/`fork`/`chan` rules carry the domain
    typing with an induction hypothesis); we do the same via `Typed.toTyped0`, reading the level-0
    premises back with `Typed0.toTyped`. -/
lemma Typed.crename {Γ m A} (tym : Γ ⊢ m : A) :
    ∀ (ξ : Nat → Nat), Γ ⊢ m⟨ξ; (id : Nat → Nat)⟩ : A := by
  have ty := tym.toTyped0
  clear tym
  induction ty using Typed0.rec (motive_2 := fun _ _ => True) with
  | srt wf _ => intro ξ; exact .srt wf.toWf
  | var wf hs _ => intro ξ; exact .var wf.toWf hs
  | @pi Γ A B i s r t tyA tyB ihA ihB =>
    intro ξ
    have hB : (A⟨ξ; (id : Nat → Nat)⟩ :: Γ) ⊢ B⟨ξ; (id : Nat → Nat)⟩ : Term.srt t :=
      Typed.ctx_conv (cren_conv0 .refl ξ) (ihA ξ) (ihB ξ)
    rw [cren_up1_eq B ξ] at hB
    exact .pi (ihA ξ) hB
  | @lam Γ A B m i s r tyA tym ihA ihm =>
    intro ξ
    obtain ⟨t, tyB⟩ := tym.toTyped.validity
    have hm : (A⟨ξ; (id : Nat → Nat)⟩ :: Γ) ⊢ m⟨ξ; (id : Nat → Nat)⟩ : B :=
      Typed.ctx_conv (cren_conv0 .refl ξ) (ihA ξ) (ihm ξ)
    rw [cren_up1_eq m ξ] at hm
    exact .conv (conv_pi (cren_conv0 .refl ξ) .refl) (.lam hm) (.pi tyA.toTyped tyB)
  | @app Γ A B m n i s tym tyn ihm ihn =>
    intro ξ
    obtain ⟨r, tyPi⟩ := tym.toTyped.validity
    obtain ⟨t, tyB, _⟩ := pi_inv tyPi
    have tyBn := tyB.subst tyn.toTyped
    asimp at tyBn
    apply Typed.conv (conv_beta (cren_conv0 .refl ξ)) _ tyBn
    exact .app (ihm ξ) (ihn ξ)
  | @sig Γ A B i s r t ord1 ord2 tyA tyB ihA ihB =>
    intro ξ
    have hB : (A⟨ξ; (id : Nat → Nat)⟩ :: Γ) ⊢ B⟨ξ; (id : Nat → Nat)⟩ : Term.srt r :=
      Typed.ctx_conv (cren_conv0 .refl ξ) (ihA ξ) (ihB ξ)
    rw [cren_up1_eq B ξ] at hB
    exact .sig ord1 ord2 (ihA ξ) hB
  | @pair Γ A B m n i t tyS tym tyn ihS ihm ihn =>
    intro ξ
    obtain ⟨s, r, _, _, tyA, tyB, _⟩ := sig_inv tyS.toTyped
    have tyBm := tyB.subst (ihm ξ)
    asimp at tyBm
    have tyn' : Γ ⊢ n⟨ξ; (id : Nat → Nat)⟩ : B[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..] :=
      Typed.conv (ARS.conv_sym (conv_beta (cren_conv0 .refl ξ))) (ihn ξ) tyBm
    exact .pair tyS.toTyped (ihm ξ) tyn'
  | @proj Γ A B C m n i s t tyC tym tyn ihC ihm ihn =>
    intro ξ
    cases tyC.toTyped.wf with
    | @cons _ _ s0 wfΓ tySig =>
      obtain ⟨s1, r, ord1, ord2, tyA, tyB, _⟩ := sig_inv tySig
      have wf2 : Wf (B :: A :: Γ) := .cons (.cons wfΓ tyA) tyB
      -- weakening agreement `[ren (+2)]` and the well-sorted weakened sig
      have agr0 : (B :: A :: Γ) ⊢ funcomp Term.var_Term (· + 2) ⊣ Γ := by
        have h := ((AgreeSubst.refl wfΓ).wk2 (s := s1) tyA).wk2 (s := r) tyB
        rwa [show (fun x => ((Term.var_Term x)⟨(id : Nat → Nat); ↑⟩)⟨(id : Nat → Nat); ↑⟩)
              = funcomp Term.var_Term (· + 2) from by funext x; asimp] at h
      have tySig' := (Typed.sig ord1 ord2 tyA tyB).substitution agr0
      asimp at tySig'
      -- the pair injection `⟨1, 0⟩` typed at the weakened sig
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
      -- well-sortedness of the renamed-motive substitution
      have hwit := (ihC ξ).substitution agr
      -- retype the branch under the renamed motive (channel ren commutes with the term subst)
      have eqn : (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan;
            Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)]
          ≃ C[Chan.var_Chan;
            Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)] := by
        have h := cren_conv0 (m := C[Chan.var_Chan;
          Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)]) .refl ξ
        rwa [show (C[Chan.var_Chan;
              Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)])⟨ξ;
                (id : Nat → Nat)⟩
              = (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan;
                Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)]
              from by asimp; congr 1] at h
      have tyn' := Typed.conv (ARS.conv_sym eqn) (ihn ξ) hwit
      -- convert the projection's result type back to the un-renamed `C[m/]`
      have eqC : (C⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..]
          ≃ C[Chan.var_Chan; m..] :=
        ARS.conv_trans (conv_beta (cren_conv0 .refl ξ)) (conv_subst (m..) (cren_conv0 .refl ξ))
      have hC := ihC ξ
      rw [cren_up1_eq C ξ] at hC tyn' eqC
      rw [cren_up2_eq n ξ] at tyn'
      exact .conv eqC (.proj hC (ihm ξ) tyn') (tyC.toTyped.subst tym.toTyped)
  | @fix Γ A m s ar gr tyA tym ihA ihm =>
    intro ξ
    have hwk : (A :: Γ) ⊢ (A⟨ξ; (id : Nat → Nat)⟩)⟨(id : Nat → Nat); ↑⟩ : Term.srt s :=
      (ihA ξ).weaken tyA.toTyped
    have hm0 : (A :: Γ) ⊢ m⟨ξ; (id : Nat → Nat)⟩ : (A⟨ξ; (id : Nat → Nat)⟩)⟨(id : Nat → Nat); ↑⟩ :=
      Typed.conv (conv_ren Nat.succ (ARS.conv_sym (cren_conv0 .refl ξ))) (ihm ξ) hwk
    have hm1 : (A⟨ξ; (id : Nat → Nat)⟩ :: Γ) ⊢ m⟨ξ; (id : Nat → Nat)⟩
        : (A⟨ξ; (id : Nat → Nat)⟩)⟨(id : Nat → Nat); ↑⟩ :=
      Typed.ctx_conv (cren_conv0 .refl ξ) (ihA ξ) hm0
    have hg := cren_guarded (i := 0) ξ gr
    rw [cren_up1_eq m ξ] at hm1 hg
    exact .conv (cren_conv0 .refl ξ)
      (.fix (cren_arity_proto ξ ar) hg hm1) tyA.toTyped
  | @ite Γ A m n1 n2 s tyA tym tyn1 tyn2 ihA ihm ihn1 ihn2 =>
    intro ξ
    have wf := tym.toTyped.wf
    have hA : (Term.bool :: Γ) ⊢ A⟨ξ; (id : Nat → Nat)⟩ : Term.srt s := ihA ξ
    have h1 := (ihA ξ).subst (Typed.tt wf)
    have h2 := (ihA ξ).subst (Typed.ff wf)
    have tyn1' : Γ ⊢ n1⟨ξ; (id : Nat → Nat)⟩ : (A⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; Term.tt..] :=
      Typed.conv (ARS.conv_sym (conv_subst (Term.tt..) (cren_conv0 .refl ξ))) (ihn1 ξ) h1
    have tyn2' : Γ ⊢ n2⟨ξ; (id : Nat → Nat)⟩ : (A⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; Term.ff..] :=
      Typed.conv (ARS.conv_sym (conv_subst (Term.ff..) (cren_conv0 .refl ξ))) (ihn2 ξ) h2
    have eq : (A⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; (m⟨ξ; (id : Nat → Nat)⟩)..] ≃ A[Chan.var_Chan; m..] :=
      ARS.conv_trans (conv_beta (cren_conv0 .refl ξ)) (conv_subst (m..) (cren_conv0 .refl ξ))
    rw [cren_up1_eq A ξ] at hA tyn1' tyn2' eq
    exact .conv eq (.ite hA (ihm ξ) tyn1' tyn2') (tyA.toTyped.subst tym.toTyped)
  | unit wf _ => intro ξ; exact .unit wf.toWf
  | one wf _ => intro ξ; exact .one wf.toWf
  | bool wf _ => intro ξ; exact .bool wf.toWf
  | tt wf _ => intro ξ; exact .tt wf.toWf
  | ff wf _ => intro ξ; exact .ff wf.toWf
  | @M Γ A s tyA ihA => intro ξ; exact .M (ihA ξ)
  | @pure Γ m A tym ihm => intro ξ; exact .pure (ihm ξ)
  | @mlet Γ m n A B s tyB tym tyn ihB ihm ihn =>
    intro ξ
    have hn : (A :: Γ) ⊢ n⟨ξ; (id : Nat → Nat)⟩ : Term.M (B⟨(id : Nat → Nat); ↑⟩) := ihn ξ
    rw [cren_up1_eq n ξ] at hn
    exact .mlet tyB.toTyped (ihm ξ) hn
  | proto wf _ => intro ξ; exact .proto wf.toWf
  | stop wf _ => intro ξ; exact .stop wf.toWf
  | @act Γ b A B i s tyA tyB ihA ihB =>
    intro ξ
    have hB : (A⟨ξ; (id : Nat → Nat)⟩ :: Γ) ⊢ B⟨ξ; (id : Nat → Nat)⟩ : Term.proto :=
      Typed.ctx_conv (cren_conv0 .refl ξ) (ihA ξ) (ihB ξ)
    rw [cren_up1_eq B ξ] at hB
    exact .act hB
  | @ch Γ b A tyA ihA => intro ξ; exact .ch (ihA ξ)
  | @chan Γ b x A wf tyA ih ihA =>
    intro ξ
    exact .chan wf.toWf tyA.toTyped
  | @fork Γ A m s tyCh tym ihCh ihm =>
    intro ξ
    obtain ⟨tyA, _⟩ := ch_inv tyCh.toTyped
    have hm : (Term.ch true (A⟨ξ; (id : Nat → Nat)⟩) :: Γ) ⊢ m⟨ξ; (id : Nat → Nat)⟩ : Term.M .unit :=
      Typed.ctx_conv (conv_ch (cren_conv0 .refl ξ)) (ihCh ξ) (ihm ξ)
    rw [cren_up1_eq m ξ] at hm
    exact .conv (conv_M (conv_ch (cren_conv0 .refl ξ))) (.fork hm) (.M (.ch tyA))
  | @recv Γ r1 r2 A B m i e tym ihm => intro ξ; exact .recv e (ihm ξ)
  | @send Γ r1 r2 A B m i e tym ihm => intro ξ; exact .send e (ihm ξ)
  | @close Γ b m tym ihm => intro ξ; exact .close (ihm ξ)
  | @conv Γ A B m s eq tym tyB ihm ihB =>
    intro ξ
    exact .conv eq (ihm ξ) tyB.toTyped
  | nil => trivial
  | cons _ _ _ _ => trivial

end TLLC.Static
