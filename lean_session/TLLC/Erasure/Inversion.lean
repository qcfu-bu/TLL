import TLLC.Erasure.Subst

/-!
# Erasure form lemmas

Port of the `era_*_form` family from `coq_session/era_inv.v`: given an erasure of a specific *source*
shape, the *erased* runtime term has the corresponding shape. For each source constructor
`Θ ⨾ Γ ⨾ Δ ⊢ <source> ~ m' : A`, the lemma pins down the head of `m'` (with the irrelevant slots
forced to `.box`), leaving the surviving subterms existentially quantified.

Coq → Lean naming (drop the `era_` prefix, keep `_form`, merge the `0`/`1` AST tags into `.im`/`.ex`):
`era_var_form` → `var_form`; `era_lam0_form`/`era_lam1_form` → `lamIm_form`/`lamEx_form`;
`era_app0_form`/`era_app1_form` → `appIm_form`/`appEx_form`;
`era_pair0_form`/`era_pair1_form` → `pairIm_form`/`pairEx_form`; `era_letin_form` → `proj_form`
(LetIn = `.proj`, covering both Coq `LetIn0`/`LetIn1`); `era_ii_form` → `one_form`;
`era_tt_form`/`era_ff_form` → `tt_form`/`ff_form`; `era_ifte_form` → `ite_form`;
`era_return_form` → `pure_form`; `era_bind_form` → `mlet_form`; `era_cvar_form` → `chan_form`;
`era_fork_form` → `fork_form`; `era_recv0_form`/`era_recv1_form` → `recvIm_form`/`recvEx_form`;
`era_send0_form`/`era_send1_form` → `sendIm_form`/`sendEx_form`; `era_wait_form`/`era_close_form`
→ `wait_form`/`close_form`; `era_box_form` → `box_form`.

Each is proved by the generalize-then-induct idiom (mirroring `Dynamic/Inversion.lean`): generalize the
source term, induct on the erasure, build the form in the matching constructor case, recurse through the
`conv` case (the erased term is unchanged under `conv`), and refute every head-mismatched case via the
impossible subject equation `e` with `all_goals (exact absurd e (by simp))`.
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Form of an erased variable (Coq `era_var_form`). -/
lemma var_form {Θ Γ Δ m x B}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .var_Term x ~ m : B) :
    m = .var_Term x := by
  generalize e : Term.var_Term x = n
  rw [e] at er
  induction er generalizing x
  case var => cases e; rfl
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `lam .im` (Coq `era_lam0_form`). -/
lemma lamIm_form {Θ Γ Δ m X n B s}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .lam X n .im s ~ m : B) :
    ∃ n', m = .lam .box n' .im s := by
  generalize e : Term.lam X n .im s = x
  rw [e] at er
  induction er generalizing X n s
  case lamIm => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `lam .ex` (Coq `era_lam1_form`). -/
lemma lamEx_form {Θ Γ Δ m X n B s}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .lam X n .ex s ~ m : B) :
    ∃ n', m = .lam .box n' .ex s := by
  generalize e : Term.lam X n .ex s = x
  rw [e] at er
  induction er generalizing X n s
  case lamEx => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `app .im` (Coq `era_app0_form`). -/
lemma appIm_form {Θ Γ Δ m n1 n2 B}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .app n1 n2 .im ~ m : B) :
    ∃ n1', m = .app n1' .box .im := by
  generalize e : Term.app n1 n2 .im = x
  rw [e] at er
  induction er generalizing n1 n2
  case appIm => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `app .ex` (Coq `era_app1_form`). -/
lemma appEx_form {Θ Γ Δ m n1 n2 B}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .app n1 n2 .ex ~ m : B) :
    ∃ n1' n2', m = .app n1' n2' .ex := by
  generalize e : Term.app n1 n2 .ex = x
  rw [e] at er
  induction er generalizing n1 n2
  case appEx => cases e; exact ⟨_, _, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `pair .im` (Coq `era_pair0_form`). -/
lemma pairIm_form {Θ Γ Δ m n1 n2 A s}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .pair n1 n2 .im s ~ m : A) :
    ∃ n2', m = .pair .box n2' .im s := by
  generalize e : Term.pair n1 n2 .im s = x
  rw [e] at er
  induction er generalizing n1 n2 s
  case pairIm => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `pair .ex` (Coq `era_pair1_form`). -/
lemma pairEx_form {Θ Γ Δ m n1 n2 A s}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .pair n1 n2 .ex s ~ m : A) :
    ∃ n1' n2', m = .pair n1' n2' .ex s := by
  generalize e : Term.pair n1 n2 .ex s = x
  rw [e] at er
  induction er generalizing n1 n2 s
  case pairEx => cases e; exact ⟨_, _, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `proj` (LetIn, Coq `era_letin_form`; covers both `projIm`/`projEx`). -/
lemma proj_form {Θ Γ Δ m n1 n2 X A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .proj X n1 n2 ~ m : A) :
    ∃ n1' n2', m = .proj .box n1' n2' := by
  generalize e : Term.proj X n1 n2 = x
  rw [e] at er
  induction er generalizing X n1 n2
  case projIm => cases e; exact ⟨_, _, rfl⟩
  case projEx => cases e; exact ⟨_, _, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `one` (Coq `era_ii_form`). -/
lemma one_form {Θ Γ Δ m A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .one ~ m : A) :
    m = .one := by
  generalize e : Term.one = x
  rw [e] at er
  induction er
  case one => cases e; rfl
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `tt` (Coq `era_tt_form`). -/
lemma tt_form {Θ Γ Δ m A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .tt ~ m : A) :
    m = .tt := by
  generalize e : Term.tt = x
  rw [e] at er
  induction er
  case tt => cases e; rfl
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `ff` (Coq `era_ff_form`). -/
lemma ff_form {Θ Γ Δ m A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .ff ~ m : A) :
    m = .ff := by
  generalize e : Term.ff = x
  rw [e] at er
  induction er
  case ff => cases e; rfl
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `ite` (Coq `era_ifte_form`). -/
lemma ite_form {Θ Γ Δ m n1 n2 n3 X A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .ite X n1 n2 n3 ~ m : A) :
    ∃ n1' n2' n3', m = .ite .box n1' n2' n3' := by
  generalize e : Term.ite X n1 n2 n3 = x
  rw [e] at er
  induction er generalizing X n1 n2 n3
  case ite => cases e; exact ⟨_, _, _, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `pure` (Return, Coq `era_return_form`). -/
lemma pure_form {Θ Γ Δ m n A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .pure n ~ m : A) :
    ∃ n', m = .pure n' := by
  generalize e : Term.pure n = x
  rw [e] at er
  induction er generalizing n
  case pure => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `mlet` (Bind, Coq `era_bind_form`). -/
lemma mlet_form {Θ Γ Δ m n1 n2 A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .mlet n1 n2 ~ m : A) :
    ∃ n1' n2', m = .mlet n1' n2' := by
  generalize e : Term.mlet n1 n2 = x
  rw [e] at er
  induction er generalizing n1 n2
  case mlet => cases e; exact ⟨_, _, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased channel (CVar, Coq `era_cvar_form`). -/
lemma chan_form {Θ Γ Δ m x A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .chan (Chan.var_Chan x) ~ m : A) :
    m = .chan (Chan.var_Chan x) := by
  generalize e : Term.chan (Chan.var_Chan x) = n
  rw [e] at er
  induction er generalizing x
  case chan => cases e; rfl
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `fork` (Coq `era_fork_form`). -/
lemma fork_form {Θ Γ Δ m n X A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .fork X n ~ m : A) :
    ∃ n', m = .fork .box n' := by
  generalize e : Term.fork X n = x
  rw [e] at er
  induction er generalizing X n
  case fork => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `recv .im` (Coq `era_recv0_form`). -/
lemma recvIm_form {Θ Γ Δ m n A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .recv n .im ~ m : A) :
    ∃ n', m = .recv n' .im := by
  generalize e : Term.recv n .im = x
  rw [e] at er
  induction er generalizing n
  case recv => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `recv .ex` (Coq `era_recv1_form`). -/
lemma recvEx_form {Θ Γ Δ m n A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .recv n .ex ~ m : A) :
    ∃ n', m = .recv n' .ex := by
  generalize e : Term.recv n .ex = x
  rw [e] at er
  induction er generalizing n
  case recv => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `send .im` (Coq `era_send0_form`). -/
lemma sendIm_form {Θ Γ Δ m n A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .send n .im ~ m : A) :
    ∃ n', m = .send n' .im := by
  generalize e : Term.send n .im = x
  rw [e] at er
  induction er generalizing n
  case send => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `send .ex` (Coq `era_send1_form`). -/
lemma sendEx_form {Θ Γ Δ m n A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .send n .ex ~ m : A) :
    ∃ n', m = .send n' .ex := by
  generalize e : Term.send n .ex = x
  rw [e] at er
  induction er generalizing n
  case send => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `close false` (Wait, Coq `era_wait_form`). -/
lemma wait_form {Θ Γ Δ m n A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .close false n ~ m : A) :
    ∃ n', m = .close false n' := by
  generalize e : Term.close false n = x
  rw [e] at er
  induction er generalizing n
  case close => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Form of an erased `close true` (Close, Coq `era_close_form`). -/
lemma close_form {Θ Γ Δ m n A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .close true n ~ m : A) :
    ∃ n', m = .close true n' := by
  generalize e : Term.close true n = x
  rw [e] at er
  induction er generalizing n
  case close => cases e; exact ⟨_, rfl⟩
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- No source term erases to `.box` (Coq `era_box_form`). -/
lemma box_form {Θ Γ Δ m A} :
    ¬ Θ ⨾ Γ ⨾ Δ ⊢ m ~ .box : A := by
  intro er
  generalize e : Term.box = n
  rw [e] at er
  induction er
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

open TLLC.Static.Tactic

/-- Strengthened inversion for erased `lam .im` (Coq `era_lam0_invX`). -/
lemma lamIm_invX {Θ Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .lam A1 m1 .im s1 ~ .lam A2 m2 .im s1 : C)
    (c : C ≃ .pi A3 B .im s2)
    (tyB : A3 :: Γ ⊢ B : .srt t) :
    Θ ⨾ (A3 :: Γ) ⨾ (none :: Δ) ⊢ m1 ~ m2 : B := by
  generalize e1 : Term.lam A1 m1 .im s1 = n1
  generalize e2 : Term.lam A2 m2 .im s1 = n2
  rw [e1, e2] at er
  induction er generalizing A1 A2 A3 B m1 m2 s1 s2 t
  case lamIm =>
    rename_i _ _ erm _
    cases e1; cases e2
    obtain ⟨eqA, eqB, _, _⟩ := Static.pi_inj c
    cases erm.wf with
    | null wf' tyA =>
      cases tyB.wf with
      | cons _ tyA3 =>
        apply Erased.ctx_conv0 (ARS.conv_sym eqA) tyA3
        apply Erased.conv eqB erm
        exact Static.Typed.ctx_conv eqA tyA tyB
  case conv =>
    rename_i eq1 _ _ ih
    exact ih (ARS.conv_trans eq1 c) tyB e1 e2
  all_goals (exact absurd e1 (by simp))

/-- Strengthened inversion for erased `lam .ex` (Coq `era_lam1_invX`). -/
lemma lamEx_invX {Θ Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .lam A1 m1 .ex s1 ~ .lam A2 m2 .ex s1 : C)
    (c : C ≃ .pi A3 B .ex s2)
    (tyB : A3 :: Γ ⊢ B : .srt t) :
    ∃ r, Θ ⨾ (A3 :: Γ) ⨾ (A3 :⟨r⟩ Δ) ⊢ m1 ~ m2 : B := by
  generalize e1 : Term.lam A1 m1 .ex s1 = n1
  generalize e2 : Term.lam A2 m2 .ex s1 = n2
  rw [e1, e2] at er
  induction er generalizing A1 A2 A3 B m1 m2 s1 s2 t
  case lamEx =>
    rename_i r _ _ erm _
    cases e1; cases e2
    obtain ⟨eqA, eqB, _, _⟩ := Static.pi_inj c
    cases erm.wf with
    | cons wf' tyA =>
      cases tyB.wf with
      | cons _ tyA3 =>
        obtain ⟨A0, rd1, rd2⟩ := Static.church_rosser _ _ eqA
        have tyA0t := Static.Typed.prd tyA rd1
        have tyA0s := Static.Typed.prd tyA3 rd2
        have e := Static.Typed.unicity tyA0t tyA0s
        subst e
        refine ⟨r, ?_⟩
        apply Erased.ctx_conv1 (ARS.conv_sym eqA) tyA3
        apply Erased.conv eqB erm
        exact Static.Typed.ctx_conv eqA tyA tyB
  case conv =>
    rename_i eq1 _ _ ih
    exact ih (ARS.conv_trans eq1 c) tyB e1 e2
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `lam .im` (Coq `era_lam0_inv`). -/
lemma lamIm_inv {Θ Γ Δ m1 m2 A1 A2 A3 B s1 s2}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .lam A1 m1 .im s1 ~ .lam A2 m2 .im s1 : .pi A3 B .im s2) :
    Θ ⨾ (A3 :: Γ) ⨾ (none :: Δ) ⊢ m1 ~ m2 : B := by
  obtain ⟨t, tyPi⟩ := er.validity
  obtain ⟨r, tyB, _⟩ := Static.pi_inv tyPi
  exact lamIm_invX er .refl tyB

/-- Inversion for erased `lam .ex` (Coq `era_lam1_inv`). -/
lemma lamEx_inv {Θ Γ Δ m1 m2 A1 A2 A3 B s1 s2}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .lam A1 m1 .ex s1 ~ .lam A2 m2 .ex s1 : .pi A3 B .ex s2) :
    ∃ r, Θ ⨾ (A3 :: Γ) ⨾ (A3 :⟨r⟩ Δ) ⊢ m1 ~ m2 : B := by
  obtain ⟨t, tyPi⟩ := er.validity
  obtain ⟨r, tyB, _⟩ := Static.pi_inv tyPi
  exact lamEx_invX er .refl tyB

/-- Strengthened inversion for erased `pair .im` (Coq `era_pair0_invX`). -/
lemma pairIm_invX {Θ Γ Δ A B m1 m2 n1 n2 s r t C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .pair m1 n1 .im s ~ .pair m2 n2 .im s : C)
    (c : C ≃ .sig A B .im r)
    (tyS : Γ ⊢ .sig A B .im r : .srt t) :
    s = r ∧ m2 = .box ∧ Γ ⊢ m1 : A ∧ Θ ⨾ Γ ⨾ Δ ⊢ n1 ~ n2 : B[Chan.var_Chan; m1..] := by
  generalize e1 : Term.pair m1 n1 .im s = x
  generalize e2 : Term.pair m2 n2 .im s = y
  rw [e1, e2] at er
  induction er generalizing A B m1 m2 n1 n2 s r t
  case pairIm =>
    rename_i _ tym ern _
    cases e1; cases e2
    obtain ⟨eqA, eqB, _, esort⟩ := Static.sig_inj c
    obtain ⟨s0, r0, _, _, tyA0, tyB0, _⟩ := Static.sig_inv tyS
    refine ⟨esort, rfl, ?_, ?_⟩
    · exact Static.Typed.conv eqA tym tyA0
    · apply Erased.conv (Static.conv_subst _ eqB) ern
      apply Static.Typed.esubst rfl rfl tyB0
      exact Static.Typed.conv eqA tym tyA0
  case conv =>
    rename_i eq1 _ _ ih
    exact ih (ARS.conv_trans eq1 c) tyS e1 e2
  all_goals (exact absurd e1 (by simp))

/-- Strengthened inversion for erased `pair .ex` (Coq `era_pair1_invX`). -/
lemma pairEx_invX {Θ Γ Δ A B m1 m2 n1 n2 s r t C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .pair m1 n1 .ex s ~ .pair m2 n2 .ex s : C)
    (c : C ≃ .sig A B .ex r)
    (tyS : Γ ⊢ .sig A B .ex r : .srt t) :
    ∃ Θ1 Θ2 Δ1 Δ2,
      s = r ∧
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m1 ~ m2 : A ∧
      Θ2 ⨾ Γ ⨾ Δ2 ⊢ n1 ~ n2 : B[Chan.var_Chan; m1..] := by
  generalize e1 : Term.pair m1 n1 .ex s = x
  generalize e2 : Term.pair m2 n2 .ex s = y
  rw [e1, e2] at er
  induction er generalizing A B m1 m2 n1 n2 s r t
  case pairEx =>
    rename_i mrgΘ mrgΔ _ erm ern _ _
    cases e1; cases e2
    obtain ⟨eqA, eqB, _, esort⟩ := Static.sig_inj c
    obtain ⟨s0, r0, _, _, tyA0, tyB0, _⟩ := Static.sig_inv tyS
    refine ⟨_, _, _, _, esort, mrgΘ, mrgΔ, ?_, ?_⟩
    · exact Erased.conv eqA erm tyA0
    · apply Erased.conv (Static.conv_subst _ eqB) ern
      apply Static.Typed.esubst rfl rfl tyB0
      exact (Erased.conv eqA erm tyA0).toStatic
  case conv =>
    rename_i eq1 _ _ ih
    exact ih (ARS.conv_trans eq1 c) tyS e1 e2
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `pair .im` (Coq `era_pair0_inv`). -/
lemma pairIm_inv {Θ Γ Δ A B m1 m2 n1 n2 s r}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .pair m1 n1 .im s ~ .pair m2 n2 .im s : .sig A B .im r) :
    s = r ∧ m2 = .box ∧ Γ ⊢ m1 : A ∧ Θ ⨾ Γ ⨾ Δ ⊢ n1 ~ n2 : B[Chan.var_Chan; m1..] := by
  obtain ⟨t, tyS⟩ := er.validity
  exact pairIm_invX er .refl tyS

/-- Inversion for erased `pair .ex` (Coq `era_pair1_inv`). -/
lemma pairEx_inv {Θ Γ Δ A B m1 m2 n1 n2 s r}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .pair m1 n1 .ex s ~ .pair m2 n2 .ex s : .sig A B .ex r) :
    ∃ Θ1 Θ2 Δ1 Δ2,
      s = r ∧
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m1 ~ m2 : A ∧
      Θ2 ⨾ Γ ⨾ Δ2 ⊢ n1 ~ n2 : B[Chan.var_Chan; m1..] := by
  obtain ⟨t, tyS⟩ := er.validity
  exact pairEx_invX er .refl tyS

/-- Inversion for erased `app .im` (Coq `era_app0_inv`). -/
lemma appIm_inv {Θ Γ Δ m1 m2 n1 n2 C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .app m1 n1 .im ~ .app m2 n2 .im : C) :
    ∃ A B s,
      n2 = .box ∧
      Θ ⨾ Γ ⨾ Δ ⊢ m1 ~ m2 : .pi A B .im s ∧
      Γ ⊢ n1 : A ∧ (C ≃ B[Chan.var_Chan; n1..]) := by
  generalize e1 : Term.app m1 n1 .im = x
  generalize e2 : Term.app m2 n2 .im = y
  rw [e1, e2] at er
  induction er generalizing m1 m2 n1 n2
  case appIm =>
    rename_i erm tyn _
    cases e1; cases e2
    exact ⟨_, _, _, rfl, erm, tyn, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨A0, B0, s0, en2, erm0, tyn0, eq2⟩ := ih e1 e2
    exact ⟨A0, B0, s0, en2, erm0, tyn0, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `app .ex` (Coq `era_app1_inv`). -/
lemma appEx_inv {Θ Γ Δ m1 m2 n1 n2 C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .app m1 n1 .ex ~ .app m2 n2 .ex : C) :
    ∃ A B s Θ1 Θ2 Δ1 Δ2,
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m1 ~ m2 : .pi A B .ex s ∧
      Θ2 ⨾ Γ ⨾ Δ2 ⊢ n1 ~ n2 : A ∧
      (C ≃ B[Chan.var_Chan; n1..]) := by
  generalize e1 : Term.app m1 n1 .ex = x
  generalize e2 : Term.app m2 n2 .ex = y
  rw [e1, e2] at er
  induction er generalizing m1 m2 n1 n2
  case appEx =>
    rename_i mrgΘ mrgΔ erm ern _ _
    cases e1; cases e2
    exact ⟨_, _, _, _, _, _, _, mrgΘ, mrgΔ, erm, ern, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨A0, B0, s0, Θ1, Θ2, Δ1, Δ2, mrgΘ, mrgΔ, erm0, ern0, eq2⟩ := ih e1 e2
    exact ⟨A0, B0, s0, Θ1, Θ2, Δ1, Δ2, mrgΘ, mrgΔ, erm0, ern0,
      ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `one` (Coq `era_ii_inv`). -/
lemma one_inv {Θ Γ Δ A} (er : Θ ⨾ Γ ⨾ Δ ⊢ .one ~ .one : A) : Empty Θ := by
  generalize e2 : Term.one = y
  nth_rewrite 2 [e2] at er
  generalize e1 : Term.one = x at er
  induction er
  case one => rename_i emp _ _; exact emp
  case conv => rename_i _ _ _ ih; exact ih e2 e1
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `tt` (Coq `era_tt_inv`). -/
lemma tt_inv {Θ Γ Δ A} (er : Θ ⨾ Γ ⨾ Δ ⊢ .tt ~ .tt : A) : Empty Θ := by
  generalize e2 : Term.tt = y
  nth_rewrite 2 [e2] at er
  generalize e1 : Term.tt = x at er
  induction er
  case tt => rename_i emp _ _; exact emp
  case conv => rename_i _ _ _ ih; exact ih e2 e1
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `ff` (Coq `era_ff_inv`). -/
lemma ff_inv {Θ Γ Δ A} (er : Θ ⨾ Γ ⨾ Δ ⊢ .ff ~ .ff : A) : Empty Θ := by
  generalize e2 : Term.ff = y
  nth_rewrite 2 [e2] at er
  generalize e1 : Term.ff = x at er
  induction er
  case ff => rename_i emp _ _; exact emp
  case conv => rename_i _ _ _ ih; exact ih e2 e1
  all_goals (exact absurd e1 (by simp))

/-- Strengthened inversion for erased `pure` (Coq `era_return_invX`). -/
lemma pure_invX {Θ Γ Δ m1 m2 B}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .pure m1 ~ .pure m2 : B) :
    ∃ A, Θ ⨾ Γ ⨾ Δ ⊢ m1 ~ m2 : A ∧ (B ≃ .M A) := by
  generalize e1 : Term.pure m1 = x
  generalize e2 : Term.pure m2 = y
  rw [e1, e2] at er
  induction er generalizing m1 m2
  case pure =>
    rename_i erm _
    cases e1; cases e2
    exact ⟨_, erm, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨A0, erm0, eq2⟩ := ih e1 e2
    exact ⟨A0, erm0, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `pure` (Coq `era_return_inv`). -/
lemma pure_inv {Θ Γ Δ m1 m2 A}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .pure m1 ~ .pure m2 : .M A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m1 ~ m2 : A := by
  obtain ⟨B, erm, eq⟩ := pure_invX er
  have eq := Static.M_inj eq
  obtain ⟨s, tyM⟩ := er.validity
  obtain ⟨r, tyA, _⟩ := Static.M_inv tyM
  exact Erased.conv (ARS.conv_sym eq) erm tyA

/-- Strengthened inversion for erased `mlet` (Coq `era_bind_invX`). -/
lemma mlet_invX {Θ Γ Δ m1 m2 n1 n2 C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .mlet m1 n1 ~ .mlet m2 n2 : C) :
    ∃ Θ1 Θ2 Δ1 Δ2 A B s t,
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Γ ⊢ B : .srt t ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m1 ~ m2 : .M A ∧
      Θ2 ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ2) ⊢ n1 ~ n2 : .M (B⟨(id : Nat → Nat); ↑⟩) ∧
      (C ≃ .M B) := by
  generalize e1 : Term.mlet m1 n1 = x
  generalize e2 : Term.mlet m2 n2 = y
  rw [e1, e2] at er
  induction er generalizing m1 m2 n1 n2
  case mlet =>
    rename_i mrgΘ mrgΔ tyB erm ern _ _
    cases e1; cases e2
    exact ⟨_, _, _, _, _, _, _, _, mrgΘ, mrgΔ, tyB, erm, ern, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨Θ1, Θ2, Δ1, Δ2, A0, B1, s0, t, mrgΘ, mrgΔ, tyB1, erm0, ern, eq2⟩ := ih e1 e2
    exact ⟨Θ1, Θ2, Δ1, Δ2, A0, B1, s0, t, mrgΘ, mrgΔ, tyB1, erm0, ern,
      ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `mlet` (Coq `era_bind_inv`). -/
lemma mlet_inv {Θ Γ Δ m1 m2 n1 n2 B}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .mlet m1 n1 ~ .mlet m2 n2 : .M B) :
    ∃ Θ1 Θ2 Δ1 Δ2 A s,
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m1 ~ m2 : .M A ∧
      Θ2 ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ2) ⊢ n1 ~ n2 : .M (B⟨(id : Nat → Nat); ↑⟩) := by
  obtain ⟨Θ1, Θ2, Δ1, Δ2, A0, B0, s, t, mrgΘ, mrgΔ, tyB0, erm, ern, eq⟩ := mlet_invX er
  have eq := Static.M_inj eq
  obtain ⟨sM, tyMB⟩ := er.validity
  obtain ⟨rB, tyB, _⟩ := Static.M_inv tyMB
  cases ern.wf with
  | cons _ tyA =>
    refine ⟨Θ1, Θ2, Δ1, Δ2, A0, s, mrgΘ, mrgΔ, erm, ?_⟩
    have ce : B0⟨(id : Nat → Nat); ↑⟩ ≃ B⟨(id : Nat → Nat); ↑⟩ := by
      have h := Static.conv_subst (funcomp Term.var_Term Nat.succ) (ARS.conv_sym eq)
      have e1 : B0⟨(id : Nat → Nat); ↑⟩ = B0[Chan.var_Chan; funcomp Term.var_Term Nat.succ] := by
        asimp; substify
      have e2 : B⟨(id : Nat → Nat); ↑⟩ = B[Chan.var_Chan; funcomp Term.var_Term Nat.succ] := by
        asimp; substify
      rw [e1, e2]; exact h
    exact Erased.conv (Static.conv_M ce) ern (tyB.weaken tyA).M

/-- Inversion for erased channel (Coq `era_cvar_inv`). -/
lemma chan_inv {Θ Γ Δ x1 x2 B}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .chan (Chan.var_Chan x1) ~ .chan (Chan.var_Chan x2) : B) :
    ∃ r A,
      x1 = x2 ∧
      Just Θ x1 (.ch r A) ∧
      [] ⊢ A : .proto ∧
      (B ≃ .ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩)) := by
  generalize e1 : Term.chan (Chan.var_Chan x1) = m
  generalize e2 : Term.chan (Chan.var_Chan x2) = n
  rw [e1, e2] at er
  induction er generalizing x1 x2
  case chan =>
    rename_i js _ _ tyA
    cases e1; cases e2
    exact ⟨_, _, rfl, js, tyA, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r, A0, ex, js, tyA0, eq2⟩ := ih e1 e2
    exact ⟨r, A0, ex, js, tyA0, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `fork` (Coq `era_fork_inv`). -/
lemma fork_inv {Θ Γ Δ A1 A2 m1 m2 B}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .fork A1 m1 ~ .fork A2 m2 : B) :
    A2 = .box ∧
    Θ ⨾ (.ch true A1 :: Γ) ⨾ (.ch true A1 :L Δ) ⊢ m1 ~ m2 : .M .unit ∧
    (B ≃ .M (.ch false A1)) := by
  generalize e1 : Term.fork A1 m1 = x
  generalize e2 : Term.fork A2 m2 = y
  rw [e1, e2] at er
  induction er generalizing A1 A2 m1 m2
  case fork =>
    rename_i erm _
    cases e1; cases e2
    exact ⟨rfl, erm, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨eA2, erm0, eq2⟩ := ih e1 e2
    exact ⟨eA2, erm0, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `recv .im` (Coq `era_recv0_inv`). -/
lemma recvIm_inv {Θ Γ Δ m1 m2 C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .recv m1 .im ~ .recv m2 .im : C) :
    ∃ r1 r2 A B,
      xor r1 r2 = false ∧
      (C ≃ .M (.sig A (.ch r1 B) .im .L)) ∧
      Θ ⨾ Γ ⨾ Δ ⊢ m1 ~ m2 : .ch r1 (.act r2 A B .im) := by
  generalize e1 : Term.recv m1 .im = x
  generalize e2 : Term.recv m2 .im = y
  rw [e1, e2] at er
  induction er generalizing m1 m2
  case recv =>
    rename_i xor erm _
    cases e1; cases e2
    exact ⟨_, _, _, _, xor, .refl, erm⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r1, r2, A0, B0, xor, eq2, erm0⟩ := ih e1 e2
    exact ⟨r1, r2, A0, B0, xor, ARS.conv_trans (ARS.conv_sym eq1) eq2, erm0⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `recv .ex` (Coq `era_recv1_inv`). -/
lemma recvEx_inv {Θ Γ Δ m1 m2 C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .recv m1 .ex ~ .recv m2 .ex : C) :
    ∃ r1 r2 A B,
      xor r1 r2 = false ∧
      (C ≃ .M (.sig A (.ch r1 B) .ex .L)) ∧
      Θ ⨾ Γ ⨾ Δ ⊢ m1 ~ m2 : .ch r1 (.act r2 A B .ex) := by
  generalize e1 : Term.recv m1 .ex = x
  generalize e2 : Term.recv m2 .ex = y
  rw [e1, e2] at er
  induction er generalizing m1 m2
  case recv =>
    rename_i xor erm _
    cases e1; cases e2
    exact ⟨_, _, _, _, xor, .refl, erm⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r1, r2, A0, B0, xor, eq2, erm0⟩ := ih e1 e2
    exact ⟨r1, r2, A0, B0, xor, ARS.conv_trans (ARS.conv_sym eq1) eq2, erm0⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `send .im` (Coq `era_send0_inv`). -/
lemma sendIm_inv {Θ Γ Δ m1 m2 C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .send m1 .im ~ .send m2 .im : C) :
    ∃ r1 r2 A B,
      xor r1 r2 = true ∧
      (C ≃ .pi A (.M (.ch r1 B)) .im .L) ∧
      Θ ⨾ Γ ⨾ Δ ⊢ m1 ~ m2 : .ch r1 (.act r2 A B .im) := by
  generalize e1 : Term.send m1 .im = x
  generalize e2 : Term.send m2 .im = y
  rw [e1, e2] at er
  induction er generalizing m1 m2
  case send =>
    rename_i xor erm _
    cases e1; cases e2
    exact ⟨_, _, _, _, xor, .refl, erm⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r1, r2, A0, B0, xor, eq2, erm0⟩ := ih e1 e2
    exact ⟨r1, r2, A0, B0, xor, ARS.conv_trans (ARS.conv_sym eq1) eq2, erm0⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `send .ex` (Coq `era_send1_inv`). -/
lemma sendEx_inv {Θ Γ Δ m1 m2 C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .send m1 .ex ~ .send m2 .ex : C) :
    ∃ r1 r2 A B,
      xor r1 r2 = true ∧
      (C ≃ .pi A (.M (.ch r1 B)) .ex .L) ∧
      Θ ⨾ Γ ⨾ Δ ⊢ m1 ~ m2 : .ch r1 (.act r2 A B .ex) := by
  generalize e1 : Term.send m1 .ex = x
  generalize e2 : Term.send m2 .ex = y
  rw [e1, e2] at er
  induction er generalizing m1 m2
  case send =>
    rename_i xor erm _
    cases e1; cases e2
    exact ⟨_, _, _, _, xor, .refl, erm⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r1, r2, A0, B0, xor, eq2, erm0⟩ := ih e1 e2
    exact ⟨r1, r2, A0, B0, xor, ARS.conv_trans (ARS.conv_sym eq1) eq2, erm0⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `close false` (Wait, Coq `era_wait_inv`). -/
lemma wait_inv {Θ Γ Δ m1 m2 C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .close false m1 ~ .close false m2 : C) :
    (C ≃ .M .unit) ∧
    Θ ⨾ Γ ⨾ Δ ⊢ m1 ~ m2 : .ch false .stop := by
  generalize e1 : Term.close false m1 = x
  generalize e2 : Term.close false m2 = y
  rw [e1, e2] at er
  induction er generalizing m1 m2
  case close =>
    rename_i erm _
    cases e1; cases e2
    exact ⟨.refl, erm⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨eq2, erm0⟩ := ih e1 e2
    exact ⟨ARS.conv_trans (ARS.conv_sym eq1) eq2, erm0⟩
  all_goals (exact absurd e1 (by simp))

/-- Inversion for erased `close true` (Close, Coq `era_close_inv`). -/
lemma close_inv {Θ Γ Δ m1 m2 C}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ .close true m1 ~ .close true m2 : C) :
    (C ≃ .M .unit) ∧
    Θ ⨾ Γ ⨾ Δ ⊢ m1 ~ m2 : .ch true .stop := by
  generalize e1 : Term.close true m1 = x
  generalize e2 : Term.close true m2 = y
  rw [e1, e2] at er
  induction er generalizing m1 m2
  case close =>
    rename_i erm _
    cases e1; cases e2
    exact ⟨.refl, erm⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨eq2, erm0⟩ := ih e1 e2
    exact ⟨ARS.conv_trans (ARS.conv_sym eq1) eq2, erm0⟩
  all_goals (exact absurd e1 (by simp))

end TLLC.Erasure
