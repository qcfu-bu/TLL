import TLLC.Static.Step

/-!
# Static confluence

Port of `coq_session/sta_conf.v`: parallel reduction `PStep` (`m ≈> n`), its closure under
substitution, the Tait–Martin-Löf diamond property, confluence and Church-Rosser, and the
parallel-reduction inversion + type-constructor injectivity lemmas (`solve_conv`).

As in `Step`, the Coq implicit/explicit constructor pairs are merged via the `Rlv`/`Bool` tag.
Channels reduce freely (`PStep.chan : chan c ≈> chan c'` for any `c c'`, Coq `sta_pstep_cvar`).
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Parallel reduction (Coq `sta_pstep`, `m ≈> n`). -/
inductive PStep : Term → Term → Prop where
  | var {x} :
    PStep (.var_Term x) (.var_Term x)
  | srt {s} :
    PStep (.srt s) (.srt s)
  | pi {A A' B B' r s} :
    PStep A A' →
    PStep B B' →
    PStep (.pi A B r s) (.pi A' B' r s)
  | lam {A A' m m' r s} :
    PStep A A' →
    PStep m m' →
    PStep (.lam A m r s) (.lam A' m' r s)
  | app {m m' n n' r} :
    PStep m m' →
    PStep n n' →
    PStep (.app m n r) (.app m' n' r)
  | beta {A m m' n n' r s} :
    PStep m m' →
    PStep n n' →
    PStep (.app (.lam A m r s) n r) (m'[Chan.var_Chan; n'..])
  | sig {A A' B B' r s} :
    PStep A A' →
    PStep B B' →
    PStep (.sig A B r s) (.sig A' B' r s)
  | pair {m m' n n' r s} :
    PStep m m' →
    PStep n n' →
    PStep (.pair m n r s) (.pair m' n' r s)
  | proj {A A' m m' n n'} :
    PStep A A' →
    PStep m m' →
    PStep n n' →
    PStep (.proj A m n) (.proj A' m' n')
  | projE {A m1 m1' m2 m2' n n' r s} :
    PStep m1 m1' →
    PStep m2 m2' →
    PStep n n' →
    PStep (.proj A (.pair m1 m2 r s) n) (n'[Chan.var_Chan; m2' .: m1' .: Term.var_Term])
  | fix {A A' m m'} :
    PStep A A' →
    PStep m m' →
    PStep (.fix A m) (.fix A' m')
  | fixE {A A' m m'} :
    PStep A A' →
    PStep m m' →
    PStep (.fix A m) (m'[Chan.var_Chan; (Term.fix A' m')..])
  | unit :
    PStep .unit .unit
  | one :
    PStep .one .one
  | bool :
    PStep .bool .bool
  | tt :
    PStep .tt .tt
  | ff :
    PStep .ff .ff
  | ite {A A' m m' n1 n1' n2 n2'} :
    PStep A A' →
    PStep m m' →
    PStep n1 n1' →
    PStep n2 n2' →
    PStep (.ite A m n1 n2) (.ite A' m' n1' n2')
  | iteT {A n1 n1' n2} :
    PStep n1 n1' →
    PStep (.ite A .tt n1 n2) n1'
  | iteF {A n1 n2 n2'} :
    PStep n2 n2' →
    PStep (.ite A .ff n1 n2) n2'
  | M {A A'} :
    PStep A A' →
    PStep (.M A) (.M A')
  | pure {m m'} :
    PStep m m' →
    PStep (.pure m) (.pure m')
  | mlet {m m' n n'} :
    PStep m m' →
    PStep n n' →
    PStep (.mlet m n) (.mlet m' n')
  | mletE {m m' n n'} :
    PStep m m' →
    PStep n n' →
    PStep (.mlet (.pure m) n) (n'[Chan.var_Chan; m'..])
  | proto :
    PStep .proto .proto
  | stop :
    PStep .stop .stop
  | act {b A A' B B' r} :
    PStep A A' →
    PStep B B' →
    PStep (.act b A B r) (.act b A' B' r)
  | ch {b A A'} :
    PStep A A' →
    PStep (.ch b A) (.ch b A')
  | chan {c c'} :
    PStep (.chan c) (.chan c')
  | fork {A A' m m'} :
    PStep A A' →
    PStep m m' →
    PStep (.fork A m) (.fork A' m')
  | recv {m m' r} :
    PStep m m' →
    PStep (.recv m r) (.recv m' r)
  | send {m m' r} :
    PStep m m' →
    PStep (.send m r) (.send m' r)
  | close {b m m'} :
    PStep m m' →
    PStep (.close b m) (.close b m')
  | box :
    PStep .box .box

@[inherit_doc] scoped infix:50 " ≈> " => PStep

/-- Parallel multi-step reduction (Coq `sta_pred`, `m ≈>* n`). -/
abbrev Pred : Term → Term → Prop := ARS.Star PStep
@[inherit_doc] scoped infix:50 " ≈>* " => Pred

/-- Static conversion (Coq `m ≃ n`). -/
abbrev SConv : Term → Term → Prop := ARS.Conv PStep
@[inherit_doc] scoped infix:50 (priority := high) " ≃ " => SConv

/-- Parallel reduction is reflexive (Coq `sta_pstep_refl`). -/
@[refl] lemma pstep_refl (m : Term) : m ≈> m := by
  induction m <;> first | exact PStep.chan | (constructor <;> assumption)

/-- Single-step reduction is closed under substitution (Coq `sta_step_subst`). -/

lemma step_subst {m n} (st : m ~> n) (σ : Nat → Term) :
    (m[Chan.var_Chan; σ]) ~> (n[Chan.var_Chan; σ]) := by
  induction st generalizing σ with
  | @beta A m n r s =>
      rw [show (m[Chan.var_Chan; n..])[Chan.var_Chan; σ]
            = (m[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (n[Chan.var_Chan; σ])..]
            from by asimp]
      exact Step.beta
  | @projE A m1 m2 n r s =>
      rw [show (n[Chan.var_Chan; m2 .: m1 .: Term.var_Term])[Chan.var_Chan; σ]
            = (n[Chan.var_Chan; up_Term_Term (up_Term_Term σ)])[Chan.var_Chan;
                (m2[Chan.var_Chan; σ]) .: (m1[Chan.var_Chan; σ]) .: Term.var_Term]
            from by asimp]
      exact Step.projE
  | @fixE A m =>
      rw [show (m[Chan.var_Chan; (Term.fix A m)..])[Chan.var_Chan; σ]
            = (m[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; ((Term.fix A m)[Chan.var_Chan; σ])..]
            from by asimp]
      exact Step.fixE
  | @mletE m n =>
      rw [show (n[Chan.var_Chan; m..])[Chan.var_Chan; σ]
            = (n[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m[Chan.var_Chan; σ])..]
            from by asimp]
      exact Step.mletE
  | iteT => exact Step.iteT
  | iteF => exact Step.iteF
  | piL _ ih => exact .piL (ih σ)
  | piR _ ih => exact .piR (ih (up_Term_Term σ))
  | lamL _ ih => exact .lamL (ih σ)
  | lamR _ ih => exact .lamR (ih (up_Term_Term σ))
  | appL _ ih => exact .appL (ih σ)
  | appR _ ih => exact .appR (ih σ)
  | sigL _ ih => exact .sigL (ih σ)
  | sigR _ ih => exact .sigR (ih (up_Term_Term σ))
  | pairL _ ih => exact .pairL (ih σ)
  | pairR _ ih => exact .pairR (ih σ)
  | projA _ ih => exact .projA (ih (up_Term_Term σ))
  | projM _ ih => exact .projM (ih σ)
  | projN _ ih => exact .projN (ih (up_Term_Term (up_Term_Term σ)))
  | fixL _ ih => exact .fixL (ih σ)
  | fixR _ ih => exact .fixR (ih (up_Term_Term σ))
  | iteA _ ih => exact .iteA (ih (up_Term_Term σ))
  | iteM _ ih => exact .iteM (ih σ)
  | iteN1 _ ih => exact .iteN1 (ih σ)
  | iteN2 _ ih => exact .iteN2 (ih σ)
  | M _ ih => exact .M (ih σ)
  | pure _ ih => exact .pure (ih σ)
  | mletL _ ih => exact .mletL (ih σ)
  | mletR _ ih => exact .mletR (ih (up_Term_Term σ))
  | actL _ ih => exact .actL (ih σ)
  | actR _ ih => exact .actR (ih (up_Term_Term σ))
  | ch _ ih => exact .ch (ih σ)
  | forkL _ ih => exact .forkL (ih σ)
  | forkR _ ih => exact .forkR (ih (up_Term_Term σ))
  | recv _ ih => exact .recv (ih σ)
  | send _ ih => exact .send (ih σ)
  | close _ ih => exact .close (ih σ)

/-- Single-step embeds into parallel reduction (Coq `sta_step_pstep`). -/

lemma step_pstep {m m'} (st : m ~> m') : m ≈> m' := by
  induction st with
  | beta => exact .beta (pstep_refl _) (pstep_refl _)
  | projE => exact .projE (pstep_refl _) (pstep_refl _) (pstep_refl _)
  | fixE => exact .fixE (pstep_refl _) (pstep_refl _)
  | mletE => exact .mletE (pstep_refl _) (pstep_refl _)
  | iteT => exact .iteT (pstep_refl _)
  | iteF => exact .iteF (pstep_refl _)
  | _ => first
    | (exact .pi (by assumption) (pstep_refl _))
    | (constructor <;> first | assumption | exact pstep_refl _)

/-- Multi-step reduction is closed under substitution (Coq `sta_red_subst`). -/

lemma red_subst {m n} (σ : Nat → Term) (r : m ~>* n) :
    (m[Chan.var_Chan; σ]) ~>* (n[Chan.var_Chan; σ]) := by
  induction r with
  | refl => exact .refl
  | tail _ st ih => exact ARS.star_trans ih (ARS.star1 (step_subst st σ))

/-- Multi-step embeds into parallel multi-step (Coq `sta_red_pred`). -/

lemma red_pred {m m'} (r : m ~>* m') : m ≈>* m' := by
  induction r with
  | refl => exact .refl
  | tail _ st ih => exact ARS.star_trans ih (ARS.star1 (step_pstep st))

/-- Parallel reduction is closed under substitution (Coq `sta_pstep_subst`). -/

lemma pstep_subst {m n} (ps : m ≈> n) (σ : Nat → Term) :
    (m[Chan.var_Chan; σ]) ≈> (n[Chan.var_Chan; σ]) := by
  induction ps generalizing σ with
  | var => exact pstep_refl _
  | srt => exact pstep_refl _
  | unit => exact pstep_refl _
  | one => exact pstep_refl _
  | bool => exact pstep_refl _
  | tt => exact pstep_refl _
  | ff => exact pstep_refl _
  | proto => exact pstep_refl _
  | stop => exact pstep_refl _
  | box => exact pstep_refl _
  | chan => exact PStep.chan
  | @beta A m m' n n' r s _ _ ihm ihn =>
      rw [show (m'[Chan.var_Chan; n'..])[Chan.var_Chan; σ]
            = (m'[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (n'[Chan.var_Chan; σ])..]
            from by asimp]
      exact PStep.beta (ihm (up_Term_Term σ)) (ihn σ)
  | @projE A m1 m1' m2 m2' n n' r s _ _ _ ihm1 ihm2 ihn =>
      rw [show (n'[Chan.var_Chan; m2' .: m1' .: Term.var_Term])[Chan.var_Chan; σ]
            = (n'[Chan.var_Chan; up_Term_Term (up_Term_Term σ)])[Chan.var_Chan;
                (m2'[Chan.var_Chan; σ]) .: (m1'[Chan.var_Chan; σ]) .: Term.var_Term]
            from by asimp]
      exact PStep.projE (ihm1 σ) (ihm2 σ) (ihn (up_Term_Term (up_Term_Term σ)))
  | @fixE A A' m m' _ _ ihA ihm =>
      rw [show (m'[Chan.var_Chan; (Term.fix A' m')..])[Chan.var_Chan; σ]
            = (m'[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan;
                ((Term.fix A' m')[Chan.var_Chan; σ])..]
            from by asimp]
      exact PStep.fixE (ihA σ) (ihm (up_Term_Term σ))
  | @mletE m m' n n' _ _ ihm ihn =>
      rw [show (n'[Chan.var_Chan; m'..])[Chan.var_Chan; σ]
            = (n'[Chan.var_Chan; up_Term_Term σ])[Chan.var_Chan; (m'[Chan.var_Chan; σ])..]
            from by asimp]
      exact PStep.mletE (ihm σ) (ihn (up_Term_Term σ))
  | iteT _ ih => exact PStep.iteT (ih σ)
  | iteF _ ih => exact PStep.iteF (ih σ)
  | pi _ _ ihA ihB => exact PStep.pi (ihA σ) (ihB (up_Term_Term σ))
  | lam _ _ ihA ihm => exact PStep.lam (ihA σ) (ihm (up_Term_Term σ))
  | app _ _ ihm ihn => exact PStep.app (ihm σ) (ihn σ)
  | sig _ _ ihA ihB => exact PStep.sig (ihA σ) (ihB (up_Term_Term σ))
  | pair _ _ ihm ihn => exact PStep.pair (ihm σ) (ihn σ)
  | proj _ _ _ ihA ihm ihn =>
      exact PStep.proj (ihA (up_Term_Term σ)) (ihm σ) (ihn (up_Term_Term (up_Term_Term σ)))
  | fix _ _ ihA ihm => exact PStep.fix (ihA σ) (ihm (up_Term_Term σ))
  | ite _ _ _ _ ihA ihm ihn1 ihn2 =>
      exact PStep.ite (ihA (up_Term_Term σ)) (ihm σ) (ihn1 σ) (ihn2 σ)
  | M _ ihA => exact PStep.M (ihA σ)
  | pure _ ihm => exact PStep.pure (ihm σ)
  | mlet _ _ ihm ihn => exact PStep.mlet (ihm σ) (ihn (up_Term_Term σ))
  | act _ _ ihA ihB => exact PStep.act (ihA σ) (ihB (up_Term_Term σ))
  | ch _ ihA => exact PStep.ch (ihA σ)
  | fork _ _ ihA ihm => exact PStep.fork (ihA σ) (ihm (up_Term_Term σ))
  | recv _ ihm => exact PStep.recv (ihm σ)
  | send _ ihm => exact PStep.send (ihm σ)
  | close _ ihm => exact PStep.close (ihm σ)


/-! ## Conversion congruence (the downstream-used cases; Coq's full congruence tower and
`sta_red_compat`/`sta_conv_compat` are dead scaffolding and omitted). -/

/-- Conversion is closed under substitution (Coq `sta_conv_subst`). -/

lemma conv_subst {m n} (σ : Nat → Term) (c : m ≃ n) :
    (m[Chan.var_Chan; σ]) ≃ (n[Chan.var_Chan; σ]) :=
  ARS.conv_hom (fun a => a[Chan.var_Chan; σ]) PStep (fun _ _ p => pstep_subst p σ) m n c

/-- Conversion congruence for `pi` (Coq `sta_conv_pi0`/`sta_conv_pi1`). -/

lemma conv_pi {A A' B B' r s} (cA : A ≃ A') (cB : B ≃ B') :
    (Term.pi A B r s) ≃ (Term.pi A' B' r s) :=
  ARS.conv_trans
    (ARS.conv_hom (fun a => Term.pi a B r s) PStep (fun _ _ p => PStep.pi p (pstep_refl _)) _ _ cA)
    (ARS.conv_hom (fun b => Term.pi A' b r s) PStep (fun _ _ p => PStep.pi (pstep_refl _) p) _ _ cB)

/-- Conversion congruence for `M` (Coq `sta_conv_io`). -/

lemma conv_M {A A'} (c : A ≃ A') : (Term.M A) ≃ (Term.M A') :=
  ARS.conv_hom (fun a => Term.M a) PStep (fun _ _ p => PStep.M p) _ _ c

/-- Conversion congruence for `ch` (Coq `sta_conv_ch`). -/

lemma conv_ch {b A A'} (c : A ≃ A') : (Term.ch b A) ≃ (Term.ch b A') :=
  ARS.conv_hom (fun a => Term.ch b a) PStep (fun _ _ p => PStep.ch p) _ _ c

/-! ## Parallel substitution and the diamond prerequisites. -/

/-- Pointwise parallel reduction of substitutions (Coq `sta_psstep`). -/
def PSstep (σ τ : Nat → Term) : Prop := ∀ x, (σ x) ≈> (τ x)

lemma psstep_refl (σ : Nat → Term) : PSstep σ σ := fun _ => pstep_refl _

private lemma pstep_shift {m n} (p : m ≈> n) :
    (ren_Term (id : Nat → Nat) Nat.succ m) ≈> (ren_Term (id : Nat → Nat) Nat.succ n) := by
  rw [show ren_Term (id : Nat → Nat) Nat.succ m
        = m[Chan.var_Chan; funcomp Term.var_Term Nat.succ] from by substify,
      show ren_Term (id : Nat → Nat) Nat.succ n
        = n[Chan.var_Chan; funcomp Term.var_Term Nat.succ] from by substify]
  exact pstep_subst p (funcomp Term.var_Term Nat.succ)

lemma psstep_up {σ τ} (h : PSstep σ τ) : PSstep (up_Term_Term σ) (up_Term_Term τ) := by
  intro x
  cases x with
  | zero => exact PStep.var
  | succ x => exact pstep_shift (h x)

/-- Parallel reduction is closed under parallel substitution (Coq `sta_pstep_compat`). -/

lemma pstep_compat {m n} (ps : m ≈> n) :
    ∀ {σ τ : Nat → Term}, PSstep σ τ → (m[Chan.var_Chan; σ]) ≈> (n[Chan.var_Chan; τ]) := by
  induction ps with
  | var => intro σ τ pst; exact pst _
  | srt => intro _ _ _; exact PStep.srt
  | unit => intro _ _ _; exact PStep.unit
  | one => intro _ _ _; exact PStep.one
  | bool => intro _ _ _; exact PStep.bool
  | tt => intro _ _ _; exact PStep.tt
  | ff => intro _ _ _; exact PStep.ff
  | proto => intro _ _ _; exact PStep.proto
  | stop => intro _ _ _; exact PStep.stop
  | box => intro _ _ _; exact PStep.box
  | chan => intro _ _ _; exact PStep.chan
  | @beta A m m' n n' r s _ _ ihm ihn =>
      intro σ τ pst
      rw [show (m'[Chan.var_Chan; n'..])[Chan.var_Chan; τ]
            = (m'[Chan.var_Chan; up_Term_Term τ])[Chan.var_Chan; (n'[Chan.var_Chan; τ])..]
            from by asimp]
      exact PStep.beta (ihm (psstep_up pst)) (ihn pst)
  | @projE A m1 m1' m2 m2' n n' r s _ _ _ ihm1 ihm2 ihn =>
      intro σ τ pst
      rw [show (n'[Chan.var_Chan; m2' .: m1' .: Term.var_Term])[Chan.var_Chan; τ]
            = (n'[Chan.var_Chan; up_Term_Term (up_Term_Term τ)])[Chan.var_Chan;
                (m2'[Chan.var_Chan; τ]) .: (m1'[Chan.var_Chan; τ]) .: Term.var_Term]
            from by asimp]
      exact PStep.projE (ihm1 pst) (ihm2 pst) (ihn (psstep_up (psstep_up pst)))
  | @fixE A A' m m' _ _ ihA ihm =>
      intro σ τ pst
      rw [show (m'[Chan.var_Chan; (Term.fix A' m')..])[Chan.var_Chan; τ]
            = (m'[Chan.var_Chan; up_Term_Term τ])[Chan.var_Chan;
                ((Term.fix A' m')[Chan.var_Chan; τ])..]
            from by asimp]
      exact PStep.fixE (ihA pst) (ihm (psstep_up pst))
  | @mletE m m' n n' _ _ ihm ihn =>
      intro σ τ pst
      rw [show (n'[Chan.var_Chan; m'..])[Chan.var_Chan; τ]
            = (n'[Chan.var_Chan; up_Term_Term τ])[Chan.var_Chan; (m'[Chan.var_Chan; τ])..]
            from by asimp]
      exact PStep.mletE (ihm pst) (ihn (psstep_up pst))
  | iteT _ ih => intro σ τ pst; exact PStep.iteT (ih pst)
  | iteF _ ih => intro σ τ pst; exact PStep.iteF (ih pst)
  | pi _ _ ihA ihB => intro σ τ pst; exact PStep.pi (ihA pst) (ihB (psstep_up pst))
  | lam _ _ ihA ihm => intro σ τ pst; exact PStep.lam (ihA pst) (ihm (psstep_up pst))
  | app _ _ ihm ihn => intro σ τ pst; exact PStep.app (ihm pst) (ihn pst)
  | sig _ _ ihA ihB => intro σ τ pst; exact PStep.sig (ihA pst) (ihB (psstep_up pst))
  | pair _ _ ihm ihn => intro σ τ pst; exact PStep.pair (ihm pst) (ihn pst)
  | proj _ _ _ ihA ihm ihn =>
      intro σ τ pst
      exact PStep.proj (ihA (psstep_up pst)) (ihm pst) (ihn (psstep_up (psstep_up pst)))
  | fix _ _ ihA ihm => intro σ τ pst; exact PStep.fix (ihA pst) (ihm (psstep_up pst))
  | ite _ _ _ _ ihA ihm ihn1 ihn2 =>
      intro σ τ pst
      exact PStep.ite (ihA (psstep_up pst)) (ihm pst) (ihn1 pst) (ihn2 pst)
  | M _ ihA => intro σ τ pst; exact PStep.M (ihA pst)
  | pure _ ihm => intro σ τ pst; exact PStep.pure (ihm pst)
  | mlet _ _ ihm ihn => intro σ τ pst; exact PStep.mlet (ihm pst) (ihn (psstep_up pst))
  | act _ _ ihA ihB => intro σ τ pst; exact PStep.act (ihA pst) (ihB (psstep_up pst))
  | ch _ ihA => intro σ τ pst; exact PStep.ch (ihA pst)
  | fork _ _ ihA ihm => intro σ τ pst; exact PStep.fork (ihA pst) (ihm (psstep_up pst))
  | recv _ ihm => intro σ τ pst; exact PStep.recv (ihm pst)
  | send _ ihm => intro σ τ pst; exact PStep.send (ihm pst)
  | close _ ihm => intro σ τ pst; exact PStep.close (ihm pst)

lemma psstep_compat {s1 s2 σ τ} (pst : PSstep σ τ) (p : s1 ≈> s2) :
    PSstep (s1 .: σ) (s2 .: τ) := by
  intro x; cases x with | zero => exact p | succ x => exact pst x

/-- Substitution of a single parallel-reducing term (Coq `sta_pstep_subst_term`). -/

lemma pstep_subst_term {m n n' : Term} (p : n ≈> n') :
    (m[Chan.var_Chan; n..]) ≈> (m[Chan.var_Chan; n'..]) :=
  pstep_compat (pstep_refl m) (psstep_compat (psstep_refl Term.var_Term) p)

/-- Parallel beta-compatibility (Coq `sta_pstep_compat_beta`). -/

lemma pstep_compat_beta {m m' n n' : Term} (pm : m ≈> m') (pn : n ≈> n') :
    (m[Chan.var_Chan; n..]) ≈> (m'[Chan.var_Chan; n'..]) :=
  pstep_compat pm (psstep_compat (psstep_refl Term.var_Term) pn)

/-- Conversion congruence for beta-substitution (Coq `sta_conv_beta`). -/

lemma conv_beta {m n1 n2 : Term} (c : n1 ≃ n2) :
    (m[Chan.var_Chan; n1..]) ≃ (m[Chan.var_Chan; n2..]) :=
  ARS.conv_hom (fun n => m[Chan.var_Chan; n..]) PStep (fun _ _ p => pstep_subst_term p) n1 n2 c

/-! ## The diamond property, confluence, and Church-Rosser. -/

/-- The Takahashi diamond for parallel reduction (Coq `sta_pstep_diamond`). -/

lemma pstep_diamond {m m1} (p1 : m ≈> m1) :
    ∀ {m2}, m ≈> m2 → ∃ m', m1 ≈> m' ∧ m2 ≈> m' := by
  induction p1 with
  | var => intro m2 p2; cases p2; exact ⟨_, .var, .var⟩
  | srt => intro m2 p2; cases p2; exact ⟨_, .srt, .srt⟩
  | unit => intro m2 p2; cases p2; exact ⟨_, .unit, .unit⟩
  | one => intro m2 p2; cases p2; exact ⟨_, .one, .one⟩
  | bool => intro m2 p2; cases p2; exact ⟨_, .bool, .bool⟩
  | tt => intro m2 p2; cases p2; exact ⟨_, .tt, .tt⟩
  | ff => intro m2 p2; cases p2; exact ⟨_, .ff, .ff⟩
  | proto => intro m2 p2; cases p2; exact ⟨_, .proto, .proto⟩
  | stop => intro m2 p2; cases p2; exact ⟨_, .stop, .stop⟩
  | box => intro m2 p2; cases p2; exact ⟨_, .box, .box⟩
  | @chan c c' => intro m2 p2; cases p2; exact ⟨Term.chan c, .chan, .chan⟩
  -- pure congruence cases
  | pi _ _ ihA ihB =>
      intro m2 p2; cases p2 with
      | pi pA2 pB2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hB1, hB2⟩ := ihB pB2
          exact ⟨_, .pi hA1 hB1, .pi hA2 hB2⟩
  | lam _ _ ihA ihm =>
      intro m2 p2; cases p2 with
      | lam pA2 pm2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          exact ⟨_, .lam hA1 hm1, .lam hA2 hm2⟩
  | sig _ _ ihA ihB =>
      intro m2 p2; cases p2 with
      | sig pA2 pB2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hB1, hB2⟩ := ihB pB2
          exact ⟨_, .sig hA1 hB1, .sig hA2 hB2⟩
  | pair _ _ ihm ihn =>
      intro m2 p2; cases p2 with
      | pair pm2 pn2 =>
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          obtain ⟨_, hn1, hn2⟩ := ihn pn2
          exact ⟨_, .pair hm1 hn1, .pair hm2 hn2⟩
  | act _ _ ihA ihB =>
      intro m2 p2; cases p2 with
      | act pA2 pB2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hB1, hB2⟩ := ihB pB2
          exact ⟨_, .act hA1 hB1, .act hA2 hB2⟩
  | M _ ihA =>
      intro m2 p2; cases p2 with
      | M pA2 => obtain ⟨_, hA1, hA2⟩ := ihA pA2; exact ⟨_, .M hA1, .M hA2⟩
  | pure _ ihm =>
      intro m2 p2; cases p2 with
      | pure pm2 => obtain ⟨_, hm1, hm2⟩ := ihm pm2; exact ⟨_, .pure hm1, .pure hm2⟩
  | ch _ ihA =>
      intro m2 p2; cases p2 with
      | ch pA2 => obtain ⟨_, hA1, hA2⟩ := ihA pA2; exact ⟨_, .ch hA1, .ch hA2⟩
  | fork _ _ ihA ihm =>
      intro m2 p2; cases p2 with
      | fork pA2 pm2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          exact ⟨_, .fork hA1 hm1, .fork hA2 hm2⟩
  | recv _ ihm =>
      intro m2 p2; cases p2 with
      | recv pm2 => obtain ⟨_, hm1, hm2⟩ := ihm pm2; exact ⟨_, .recv hm1, .recv hm2⟩
  | send _ ihm =>
      intro m2 p2; cases p2 with
      | send pm2 => obtain ⟨_, hm1, hm2⟩ := ihm pm2; exact ⟨_, .send hm1, .send hm2⟩
  | close _ ihm =>
      intro m2 p2; cases p2 with
      | close pm2 => obtain ⟨_, hm1, hm2⟩ := ihm pm2; exact ⟨_, .close hm1, .close hm2⟩
  -- redex-interaction cases (filled below)
  | @app _ _ _ _ _ pm _ ihm ihn =>
      intro m2 p2
      cases p2 with
      | app pm2 pn2 =>
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          obtain ⟨_, hn1, hn2⟩ := ihn pn2
          exact ⟨_, .app hm1 hn1, .app hm2 hn2⟩
      | @beta A _ _ _ _ _ _ pmb pnb =>
          obtain ⟨_, h1, h2⟩ := ihm (PStep.lam (pstep_refl A) pmb)
          obtain ⟨_, hn1, hn2⟩ := ihn pnb
          cases pm with
          | lam _ _ => cases h1 with
            | lam _ pmxb => cases h2 with
              | lam _ pmqx =>
                  exact ⟨_, PStep.beta pmxb hn1, pstep_compat_beta pmqx hn2⟩
  | @beta _ _ _ _ _ _ _ _ _ ihm ihn =>
      intro m2 p2
      cases p2 with
      | app pmq pnq =>
          cases pmq with
          | lam _ pmb2 =>
              obtain ⟨_, hm1, hm2⟩ := ihm pmb2
              obtain ⟨_, hn1, hn2⟩ := ihn pnq
              exact ⟨_, pstep_compat_beta hm1 hn1, PStep.beta hm2 hn2⟩
      | beta pmb2 pnb2 =>
          obtain ⟨_, hm1, hm2⟩ := ihm pmb2
          obtain ⟨_, hn1, hn2⟩ := ihn pnb2
          exact ⟨_, pstep_compat_beta hm1 hn1, pstep_compat_beta hm2 hn2⟩
  | @proj _ _ _ _ _ _ _ pm _ ihA ihm ihn =>
      intro m2 p2
      cases p2 with
      | proj pA2 pm2 pn2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          obtain ⟨_, hn1, hn2⟩ := ihn pn2
          exact ⟨_, .proj hA1 hm1 hn1, .proj hA2 hm2 hn2⟩
      | @projE _ _ _ _ _ _ _ _ _ pm1 pm2 pn2 =>
          obtain ⟨_, hpm1, hpm2⟩ := ihm (PStep.pair pm1 pm2)
          obtain ⟨_, hn1, hn2⟩ := ihn pn2
          cases pm with
          | pair _ _ => cases hpm1 with
            | pair hm1x hm2x => cases hpm2 with
              | pair hm1qx hm2qx =>
                  exact ⟨_, PStep.projE hm1x hm2x hn1,
                    pstep_compat hn2
                      (psstep_compat (psstep_compat (psstep_refl Term.var_Term) hm1qx) hm2qx)⟩
  | projE _ _ _ ihm1 ihm2 ihn =>
      intro m2 p2
      cases p2 with
      | proj _ pmq pn2 =>
          cases pmq with
          | pair pm1b pm2b =>
              obtain ⟨_, h11, h12⟩ := ihm1 pm1b
              obtain ⟨_, h21, h22⟩ := ihm2 pm2b
              obtain ⟨_, hn1, hn2⟩ := ihn pn2
              exact ⟨_,
                pstep_compat hn1
                  (psstep_compat (psstep_compat (psstep_refl Term.var_Term) h11) h21),
                PStep.projE h12 h22 hn2⟩
      | projE pm1b pm2b pn2 =>
          obtain ⟨_, h11, h12⟩ := ihm1 pm1b
          obtain ⟨_, h21, h22⟩ := ihm2 pm2b
          obtain ⟨_, hn1, hn2⟩ := ihn pn2
          exact ⟨_,
            pstep_compat hn1
              (psstep_compat (psstep_compat (psstep_refl Term.var_Term) h11) h21),
            pstep_compat hn2
              (psstep_compat (psstep_compat (psstep_refl Term.var_Term) h12) h22)⟩
  | @mlet _ _ _ _ pm _ ihm ihn =>
      intro m2 p2
      cases p2 with
      | mlet pm2 pn2 =>
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          obtain ⟨_, hn1, hn2⟩ := ihn pn2
          exact ⟨_, .mlet hm1 hn1, .mlet hm2 hn2⟩
      | @mletE _ _ _ _ pmb pnb =>
          obtain ⟨_, h1, h2⟩ := ihm (PStep.pure pmb)
          obtain ⟨_, hn1, hn2⟩ := ihn pnb
          cases pm with
          | pure _ => cases h1 with
            | pure pmxb => cases h2 with
              | pure pmqx =>
                  exact ⟨_, PStep.mletE pmxb hn1, pstep_compat_beta hn2 pmqx⟩
  | mletE _ _ ihm ihn =>
      intro m2 p2
      cases p2 with
      | mlet pmq pnq =>
          cases pmq with
          | pure pmb2 =>
              obtain ⟨_, hm1, hm2⟩ := ihm pmb2
              obtain ⟨_, hn1, hn2⟩ := ihn pnq
              exact ⟨_, pstep_compat_beta hn1 hm1, PStep.mletE hm2 hn2⟩
      | mletE pmb2 pnb2 =>
          obtain ⟨_, hm1, hm2⟩ := ihm pmb2
          obtain ⟨_, hn1, hn2⟩ := ihn pnb2
          exact ⟨_, pstep_compat_beta hn1 hm1, pstep_compat_beta hn2 hm2⟩
  | fix _ _ ihA ihm =>
      intro m2 p2
      cases p2 with
      | fix pA2 pm2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          exact ⟨_, .fix hA1 hm1, .fix hA2 hm2⟩
      | fixE pA2 pm2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          exact ⟨_, PStep.fixE hA1 hm1, pstep_compat_beta hm2 (PStep.fix hA2 hm2)⟩
  | fixE _ _ ihA ihm =>
      intro m2 p2
      cases p2 with
      | fix pA2 pm2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          exact ⟨_, pstep_compat_beta hm1 (PStep.fix hA1 hm1), PStep.fixE hA2 hm2⟩
      | fixE pA2 pm2 =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          exact ⟨_, pstep_compat_beta hm1 (PStep.fix hA1 hm1),
            pstep_compat_beta hm2 (PStep.fix hA2 hm2)⟩
  | @ite _ _ _ _ _ _ _ _ _ pm _ _ ihA ihm ihn1 ihn2 =>
      intro m2 p2
      cases p2 with
      | ite pA2 pm2 pn1q pn2q =>
          obtain ⟨_, hA1, hA2⟩ := ihA pA2
          obtain ⟨_, hm1, hm2⟩ := ihm pm2
          obtain ⟨_, hn11, hn12⟩ := ihn1 pn1q
          obtain ⟨_, hn21, hn22⟩ := ihn2 pn2q
          exact ⟨_, .ite hA1 hm1 hn11 hn21, .ite hA2 hm2 hn12 hn22⟩
      | iteT pn1q =>
          obtain ⟨_, hn1, hn2⟩ := ihn1 pn1q
          cases pm with
          | tt => exact ⟨_, PStep.iteT hn1, hn2⟩
      | iteF pn2q =>
          obtain ⟨_, hn1, hn2⟩ := ihn2 pn2q
          cases pm with
          | ff => exact ⟨_, PStep.iteF hn1, hn2⟩
  | iteT _ ih =>
      intro m2 p2
      cases p2 with
      | ite _ pm2 pn1q _ =>
          cases pm2 with
          | tt =>
              obtain ⟨_, hn1, hn2⟩ := ih pn1q
              exact ⟨_, hn1, PStep.iteT hn2⟩
      | iteT pn1q =>
          obtain ⟨_, hn1, hn2⟩ := ih pn1q
          exact ⟨_, hn1, hn2⟩
  | iteF _ ih =>
      intro m2 p2
      cases p2 with
      | ite _ pm2 _ pn2q =>
          cases pm2 with
          | ff =>
              obtain ⟨_, hn1, hn2⟩ := ih pn2q
              exact ⟨_, hn1, PStep.iteF hn2⟩
      | iteF pn2q =>
          obtain ⟨_, hn1, hn2⟩ := ih pn2q
          exact ⟨_, hn1, hn2⟩

/-- Strip lemma (Coq `strip`). -/

lemma pstep_strip {m m1 m2} (p : m ≈> m1) (r : m ≈>* m2) :
    ∃ m', m1 ≈>* m' ∧ m2 ≈> m' := by
  induction r generalizing m1 with
  | refl => exact ⟨m1, .refl, p⟩
  | tail _ p2 ih =>
      obtain ⟨m3, r2, p3⟩ := ih p
      obtain ⟨m4, p4, p5⟩ := pstep_diamond p3 p2
      exact ⟨m4, ARS.star_trans r2 (ARS.star1 p4), p5⟩

/-- Confluence of parallel reduction (Coq `confluence`). -/
theorem confluence : ARS.Confluent PStep := by
  intro x y z rxy rxz
  induction rxy generalizing z rxz with
  | refl => exact ⟨z, rxz, .refl⟩
  | tail _ p ih =>
      obtain ⟨z1, r2, r3⟩ := ih z rxz
      obtain ⟨z2, r4, p1⟩ := pstep_strip p r2
      exact ⟨z2, r4, ARS.star_trans r3 (ARS.star1 p1)⟩

/-- Church-Rosser for parallel reduction (Coq `church_rosser`). -/
theorem church_rosser : ARS.CR PStep := (ARS.confluent_cr).mp confluence

/-! ## Parallel-reduction inversion (Coq `sta_pred_*_inv`). -/

lemma pred_var_inv {x y} (rd : Term.var_Term x ≈>* y) : y = Term.var_Term x := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_chan_inv {c y} (rd : Term.chan c ≈>* y) : ∃ c', y = Term.chan c' := by
  induction rd with
  | refl => exact ⟨c, rfl⟩
  | tail _ st ih => obtain ⟨c', rfl⟩ := ih; cases st; exact ⟨_, rfl⟩

lemma pred_sort_inv {s x} (rd : Term.srt s ≈>* x) : x = Term.srt s := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_unit_inv {x} (rd : Term.unit ≈>* x) : x = Term.unit := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_one_inv {x} (rd : Term.one ≈>* x) : x = Term.one := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_bool_inv {x} (rd : Term.bool ≈>* x) : x = Term.bool := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_tt_inv {x} (rd : Term.tt ≈>* x) : x = Term.tt := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_ff_inv {x} (rd : Term.ff ≈>* x) : x = Term.ff := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_proto_inv {x} (rd : Term.proto ≈>* x) : x = Term.proto := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_stop_inv {x} (rd : Term.stop ≈>* x) : x = Term.stop := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_box_inv {x} (rd : Term.box ≈>* x) : x = Term.box := by
  induction rd with
  | refl => rfl
  | tail _ st ih => subst ih; cases st; rfl

lemma pred_M_inv {A x} (rd : Term.M A ≈>* x) :
    ∃ A', A ≈>* A' ∧ x = Term.M A' := by
  induction rd with
  | refl => exact ⟨A, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨A', rA, rfl⟩ := ih
      cases st with | M pA => exact ⟨_, ARS.star_trans rA (ARS.star1 pA), rfl⟩

lemma pred_pure_inv {m x} (rd : Term.pure m ≈>* x) :
    ∃ m', m ≈>* m' ∧ x = Term.pure m' := by
  induction rd with
  | refl => exact ⟨m, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨m', rA, rfl⟩ := ih
      cases st with | pure pA => exact ⟨_, ARS.star_trans rA (ARS.star1 pA), rfl⟩

lemma pred_ch_inv {b A x} (rd : Term.ch b A ≈>* x) :
    ∃ A', A ≈>* A' ∧ x = Term.ch b A' := by
  induction rd with
  | refl => exact ⟨A, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨A', rA, rfl⟩ := ih
      cases st with | ch pA => exact ⟨_, ARS.star_trans rA (ARS.star1 pA), rfl⟩

lemma pred_recv_inv {m r x} (rd : Term.recv m r ≈>* x) :
    ∃ m', m ≈>* m' ∧ x = Term.recv m' r := by
  induction rd with
  | refl => exact ⟨m, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨m', rA, rfl⟩ := ih
      cases st with | recv pA => exact ⟨_, ARS.star_trans rA (ARS.star1 pA), rfl⟩

lemma pred_send_inv {m r x} (rd : Term.send m r ≈>* x) :
    ∃ m', m ≈>* m' ∧ x = Term.send m' r := by
  induction rd with
  | refl => exact ⟨m, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨m', rA, rfl⟩ := ih
      cases st with | send pA => exact ⟨_, ARS.star_trans rA (ARS.star1 pA), rfl⟩

lemma pred_close_inv {b m x} (rd : Term.close b m ≈>* x) :
    ∃ m', m ≈>* m' ∧ x = Term.close b m' := by
  induction rd with
  | refl => exact ⟨m, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨m', rA, rfl⟩ := ih
      cases st with | close pA => exact ⟨_, ARS.star_trans rA (ARS.star1 pA), rfl⟩

lemma pred_pi_inv {A B r s x} (rd : Term.pi A B r s ≈>* x) :
    ∃ A' B', A ≈>* A' ∧ B ≈>* B' ∧ x = Term.pi A' B' r s := by
  induction rd with
  | refl => exact ⟨A, B, .refl, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨A', B', r1, r2, rfl⟩ := ih
      cases st with
      | pi p1 p2 =>
          exact ⟨_, _, ARS.star_trans r1 (ARS.star1 p1), ARS.star_trans r2 (ARS.star1 p2), rfl⟩

lemma pred_lam_inv {A m r s x} (rd : Term.lam A m r s ≈>* x) :
    ∃ A' m', A ≈>* A' ∧ m ≈>* m' ∧ x = Term.lam A' m' r s := by
  induction rd with
  | refl => exact ⟨A, m, .refl, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨A', m', r1, r2, rfl⟩ := ih
      cases st with
      | lam p1 p2 =>
          exact ⟨_, _, ARS.star_trans r1 (ARS.star1 p1), ARS.star_trans r2 (ARS.star1 p2), rfl⟩

lemma pred_sig_inv {A B r s x} (rd : Term.sig A B r s ≈>* x) :
    ∃ A' B', A ≈>* A' ∧ B ≈>* B' ∧ x = Term.sig A' B' r s := by
  induction rd with
  | refl => exact ⟨A, B, .refl, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨A', B', r1, r2, rfl⟩ := ih
      cases st with
      | sig p1 p2 =>
          exact ⟨_, _, ARS.star_trans r1 (ARS.star1 p1), ARS.star_trans r2 (ARS.star1 p2), rfl⟩

lemma pred_pair_inv {m n r s x} (rd : Term.pair m n r s ≈>* x) :
    ∃ m' n', m ≈>* m' ∧ n ≈>* n' ∧ x = Term.pair m' n' r s := by
  induction rd with
  | refl => exact ⟨m, n, .refl, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨m', n', r1, r2, rfl⟩ := ih
      cases st with
      | pair p1 p2 =>
          exact ⟨_, _, ARS.star_trans r1 (ARS.star1 p1), ARS.star_trans r2 (ARS.star1 p2), rfl⟩

lemma pred_act_inv {b A B r x} (rd : Term.act b A B r ≈>* x) :
    ∃ A' B', A ≈>* A' ∧ B ≈>* B' ∧ x = Term.act b A' B' r := by
  induction rd with
  | refl => exact ⟨A, B, .refl, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨A', B', r1, r2, rfl⟩ := ih
      cases st with
      | act p1 p2 =>
          exact ⟨_, _, ARS.star_trans r1 (ARS.star1 p1), ARS.star_trans r2 (ARS.star1 p2), rfl⟩

lemma pred_fork_inv {A m x} (rd : Term.fork A m ≈>* x) :
    ∃ A' m', A ≈>* A' ∧ m ≈>* m' ∧ x = Term.fork A' m' := by
  induction rd with
  | refl => exact ⟨A, m, .refl, .refl, rfl⟩
  | tail _ st ih =>
      obtain ⟨A', m', r1, r2, rfl⟩ := ih
      cases st with
      | fork p1 p2 =>
          exact ⟨_, _, ARS.star_trans r1 (ARS.star1 p1), ARS.star_trans r2 (ARS.star1 p2), rfl⟩

/-! ## Type-constructor injectivity under conversion (Coq `*_inj`). -/

lemma sort_inj {s1 s2} (c : Term.srt s1 ≃ Term.srt s2) : s1 = s2 := by
  obtain ⟨x, rx1, rx2⟩ := church_rosser _ _ c
  rw [pred_sort_inv rx1] at rx2
  simpa using pred_sort_inv rx2

lemma pi_inj {A A' B B' r r' s s'} (c : Term.pi A B r s ≃ Term.pi A' B' r' s') :
    (A ≃ A') ∧ (B ≃ B') ∧ r = r' ∧ s = s' := by
  obtain ⟨x, rx1, rx2⟩ := church_rosser _ _ c
  obtain ⟨A1, B1, rA1, rB1, e1⟩ := pred_pi_inv rx1
  obtain ⟨A2, B2, rA2, rB2, e2⟩ := pred_pi_inv rx2
  rw [e1] at e2; injection e2 with eA eB er es
  subst eA eB er es
  exact ⟨ARS.join_conv rA1 rA2, ARS.join_conv rB1 rB2, rfl, rfl⟩

lemma sig_inj {A A' B B' r r' s s'} (c : Term.sig A B r s ≃ Term.sig A' B' r' s') :
    (A ≃ A') ∧ (B ≃ B') ∧ r = r' ∧ s = s' := by
  obtain ⟨x, rx1, rx2⟩ := church_rosser _ _ c
  obtain ⟨A1, B1, rA1, rB1, e1⟩ := pred_sig_inv rx1
  obtain ⟨A2, B2, rA2, rB2, e2⟩ := pred_sig_inv rx2
  rw [e1] at e2; injection e2 with eA eB er es
  subst eA eB er es
  exact ⟨ARS.join_conv rA1 rA2, ARS.join_conv rB1 rB2, rfl, rfl⟩

lemma M_inj {A A'} (c : Term.M A ≃ Term.M A') : A ≃ A' := by
  obtain ⟨x, rx1, rx2⟩ := church_rosser _ _ c
  obtain ⟨A1, rA1, e1⟩ := pred_M_inv rx1
  obtain ⟨A2, rA2, e2⟩ := pred_M_inv rx2
  rw [e1] at e2; injection e2 with eA
  subst eA
  exact ARS.join_conv rA1 rA2

lemma act_inj {b b' A A' B B' r r'} (c : Term.act b A B r ≃ Term.act b' A' B' r') :
    (A ≃ A') ∧ (B ≃ B') ∧ b = b' ∧ r = r' := by
  obtain ⟨x, rx1, rx2⟩ := church_rosser _ _ c
  obtain ⟨A1, B1, rA1, rB1, e1⟩ := pred_act_inv rx1
  obtain ⟨A2, B2, rA2, rB2, e2⟩ := pred_act_inv rx2
  rw [e1] at e2; injection e2 with eb eA eB er
  subst eA eB eb er
  exact ⟨ARS.join_conv rA1 rA2, ARS.join_conv rB1 rB2, rfl, rfl⟩

lemma ch_inj {b b' A A'} (c : Term.ch b A ≃ Term.ch b' A') : b = b' ∧ (A ≃ A') := by
  obtain ⟨x, rx1, rx2⟩ := church_rosser _ _ c
  obtain ⟨A1, rA1, e1⟩ := pred_ch_inv rx1
  obtain ⟨A2, rA2, e2⟩ := pred_ch_inv rx2
  rw [e1] at e2; injection e2 with eb eA
  subst eA
  exact ⟨eb, ARS.join_conv rA1 rA2⟩

/-! ## The `false_conv` tactic (ported from SStructTT's `false_conv`).

Refutes impossible conversions: for a hypothesis `a ≃ b` with distinct head constructors,
Church-Rosser yields a common reduct `x` whose two `pred_*_inv` characterizations give
`a-form = b-form`, contradicted by `Term.noConfusion`. -/

/-- Church-Rosser in joinable form, for `false_conv`. -/
lemma cr {a b : Term} (h : a ≃ b) : ∃ x, a ≈>* x ∧ b ≈>* x := church_rosser a b h

namespace Tactic
open Lean Elab Tactic Meta

/-- Eliminate an `Exists` proof `m` using `elim`. -/
def existsElim (m : Expr) (elim : Expr → Expr → MetaM Expr) : MetaM Expr := do
  let mType ← whnf (← inferType m)
  match mType.getAppFnArgs with
  | (``Exists, #[a, p]) =>
    withLocalDecl `x BinderInfo.default a fun x =>
    withLocalDecl `y BinderInfo.default (.app p x) fun y => do
      let body ← mkLambdaFVars #[x, y] (← elim x y)
      mkAppOptM ``Exists.elim #[none, none, none, m, body]
  | _ => throwError "existsElim {mType}"

/-- Eliminate an `And` proof `m` using `elim`. -/
def andElim (m : Expr) (elim : Expr → Expr → MetaM Expr) : MetaM Expr := do
  let mType ← whnf (← inferType m)
  match mType.getAppFnArgs with
  | (``And, #[a, b]) =>
    withLocalDecl `x BinderInfo.default a fun x =>
    withLocalDecl `y BinderInfo.default b fun y => do
      let body ← mkLambdaFVars #[x, y] (← elim x y)
      mkAppM ``And.elim #[body, m]
  | _ => throwError "andElim {mType}"

/-- Collect the `Eq` conjuncts nested in a proof of `Exists`/`And`. -/
partial def prjEqs (m : Expr) (elim : Array Expr → MetaM Expr) : MetaM Expr := do
  let mType ← whnf (← inferType m)
  match mType.getAppFn.constName? with
  | some ``Exists =>
    existsElim m fun x y =>
      prjEqs x fun eqs1 =>
      prjEqs y fun eqs2 =>
      elim (eqs1 ++ eqs2)
  | some ``And =>
    andElim m fun x y =>
      prjEqs x fun eqs1 =>
      prjEqs y fun eqs2 =>
      elim (eqs1 ++ eqs2)
  | some ``Eq => elim #[m]
  | _ => elim #[]

/-- Gather all `_ ≃ _` hypotheses from the local context. -/
def getConvs (goal : MVarId) : MetaM (Array (Expr × Expr × Expr)) := do
  goal.withContext do
    let lctx ← getLCtx
    let mut acc := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let declType ← whnf (← inferType ldecl.toExpr)
      match declType.getAppFnArgs with
      | (``ARS.Conv, #[_, _, a, b]) => acc := acc.push (ldecl.toExpr, a, b)
      | _ => pure ()
    return acc

/-- Apply Church-Rosser + the two inversion lemmas, then `Term.noConfusion`. -/
def applyCR (goal : MVarId) (m l1 l2 : Expr) : MetaM Expr := do
  let crProof ← mkAppM ``cr #[m]
  existsElim crProof fun _ h =>
  andElim h fun h1 h2 => do
    let h1 ← mkAppM' l1 #[h1]
    let h2 ← mkAppM' l2 #[h2]
    prjEqs h1 fun es1 =>
    prjEqs h2 fun es2 => do
      let e1 ← mkAppM ``Eq.symm #[es1[0]!]
      let e2 ← mkAppM ``Eq.trans #[e1, es2[0]!]
      mkAppOptM ``Term.noConfusion #[← goal.getType, none, none, e2]

/-- Inversion lemma for a term's head constructor. -/
def getInvLemma (m : Expr) : MetaM Expr := do
  match m.getAppFn.constName? with
  | some ``Term.var_Term => return mkConst ``pred_var_inv
  | some ``Term.srt   => return mkConst ``pred_sort_inv
  | some ``Term.pi    => return mkConst ``pred_pi_inv
  | some ``Term.lam   => return mkConst ``pred_lam_inv
  | some ``Term.sig   => return mkConst ``pred_sig_inv
  | some ``Term.pair  => return mkConst ``pred_pair_inv
  | some ``Term.unit  => return mkConst ``pred_unit_inv
  | some ``Term.one   => return mkConst ``pred_one_inv
  | some ``Term.bool  => return mkConst ``pred_bool_inv
  | some ``Term.tt    => return mkConst ``pred_tt_inv
  | some ``Term.ff    => return mkConst ``pred_ff_inv
  | some ``Term.M     => return mkConst ``pred_M_inv
  | some ``Term.pure  => return mkConst ``pred_pure_inv
  | some ``Term.proto => return mkConst ``pred_proto_inv
  | some ``Term.stop  => return mkConst ``pred_stop_inv
  | some ``Term.act   => return mkConst ``pred_act_inv
  | some ``Term.ch    => return mkConst ``pred_ch_inv
  | some ``Term.chan  => return mkConst ``pred_chan_inv
  | some ``Term.fork  => return mkConst ``pred_fork_inv
  | some ``Term.recv  => return mkConst ``pred_recv_inv
  | some ``Term.send  => return mkConst ``pred_send_inv
  | some ``Term.close => return mkConst ``pred_close_inv
  | some ``Term.box   => return mkConst ``pred_box_inv
  | _ => throwError "getInvLemma: no inversion lemma for {m}"

/-- `false_conv` refutes impossible conversion proofs in the local context. -/
elab "false_conv" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let goalType ← getMainTarget
    for (m, a, b) in ← getConvs goal do
      let st ← saveState
      try
        let lemma_a ← getInvLemma a
        let lemma_b ← getInvLemma b
        let pf ← applyCR goal m lemma_a lemma_b
        if ← isDefEq goalType (← inferType pf) then
          closeMainGoal `false_conv pf
          return
      catch _ => restoreState st

end Tactic

example {A B : Term} {r : Rlv} {s : Srt} (h : (Term.srt s) ≃ (Term.pi A B r s)) : False := by
  false_conv

example {m A B : Term} {r : Rlv} {s : Srt} (h : (Term.M m) ≃ (Term.sig A B r s)) : False := by
  false_conv

end TLLC.Static
