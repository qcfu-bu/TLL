import TLLC.Dynamic.Inversion
import TLLC.Dynamic.Step

/-!
# Monadic canonical forms (global-progress seed)

Port of `coq_session/dyn_prog.v` (excluded from the Coq `_CoqProject` — unfinished scaffolding toward
global progress). `Typed.monad_canonical` (Coq `dyn_monad_canonical`) is the canonical-forms lemma
for closed values of monadic type: a value `v` of a type convertible to `IO A` is either a returned
value `.pure u` (with `u` a value) or a suspended `Thunk` (a bind/fork/recv/send-application/close).

This is one of the two seeds (with `EvalCtx.lean`) for the Lean-only deadlock-freedom contribution.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static
open TLLC.Static.Tactic

/-- Canonical forms for closed values of monadic type (Coq `dyn_monad_canonical`). -/
lemma Typed.monad_canonical {Θ A v T} (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : T)
    (vl : Val v) (eq : .M A ≃ T) :
    (∃ u, Val u ∧ v = .pure u) ∨ Thunk v := by
  generalize eΓ : ([] : Static.Ctx) = Γ at ty
  generalize eΔ : ([] : Ctx) = Δ at ty
  induction ty generalizing A with
  | var _ _ _ dhs => subst eΔ; cases dhs
  | lamIm => false_conv
  | lamEx => false_conv
  | pairIm => false_conv
  | pairEx => false_conv
  | one => false_conv
  | tt => false_conv
  | ff => false_conv
  | chan => false_conv
  | send => false_conv
  | pure _ _ => cases vl with
    | pure vu => exact .inl ⟨_, vu, rfl⟩
    | thunk th => cases th
  | mlet _ _ _ _ _ _ _ => cases vl with | thunk th => exact .inr th
  | fork _ _ => cases vl with | thunk th => exact .inr th
  | recv _ _ _ => cases vl with | thunk th => exact .inr th
  | close _ _ => cases vl with | thunk th => exact .inr th
  | appIm _ _ _ => cases vl with | thunk th => exact .inr th
  | appEx _ _ _ _ _ _ => cases vl with | thunk th => exact .inr th
  | projIm _ _ _ _ _ _ _ => cases vl with | thunk th => cases th
  | projEx _ _ _ _ _ _ _ => cases vl with | thunk th => cases th
  | ite _ _ _ _ _ _ _ _ _ => cases vl with | thunk th => cases th
  | conv eq1 _ _ ihm => exact ihm vl (ARS.conv_trans eq (ARS.conv_sym eq1)) eΓ eΔ

private lemma appSendIm_result_M {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {n A B : Term} {s : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .im : .pi A B .im s) :
    ∃ r C, B[Chan.var_Chan; n..] ≃ (Term.M (.ch r C))[Chan.var_Chan; n..] := by
  obtain ⟨r, _r2, _A0, C, _xor, eqPi, _tyChan⟩ := sendIm_inv tySend
  obtain ⟨_, eqB, _, _⟩ := Static.pi_inj eqPi
  exact ⟨r, C, Static.conv_subst _ eqB⟩

private lemma appSendEx_result_M {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {v A B : Term} {s : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .ex : .pi A B .ex s) :
    ∃ r C, B[Chan.var_Chan; v..] ≃ (Term.M (.ch r C))[Chan.var_Chan; v..] := by
  obtain ⟨r, _r2, _A0, C, _xor, eqPi, _tyChan⟩ := sendEx_inv tySend
  obtain ⟨_, eqB, _, _⟩ := Static.pi_inj eqPi
  exact ⟨r, C, Static.conv_subst _ eqB⟩

private lemma appSendIm_not_pi {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {n A B A0 B0 : Term} {i : Rlv} {s s0 : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .im : .pi A0 B0 .im s0)
    (eq : .pi A B i s ≃ B0[Chan.var_Chan; n..]) : False := by
  obtain ⟨r, C, hM⟩ := appSendIm_result_M (n := n) tySend
  have h : Term.pi A B i s ≃ (Term.M (.ch r C))[Chan.var_Chan; n..] := ARS.conv_trans eq hM
  asimp at h
  false_conv

private lemma appSendEx_not_pi {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {v A B A0 B0 : Term} {i : Rlv} {s s0 : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .ex : .pi A0 B0 .ex s0)
    (eq : .pi A B i s ≃ B0[Chan.var_Chan; v..]) : False := by
  obtain ⟨r, C, hM⟩ := appSendEx_result_M (v := v) tySend
  have h : Term.pi A B i s ≃ (Term.M (.ch r C))[Chan.var_Chan; v..] := ARS.conv_trans eq hM
  asimp at h
  false_conv

private lemma appSendIm_not_sig {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {n A B A0 B0 : Term} {i : Rlv} {s s0 : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .im : .pi A0 B0 .im s0)
    (eq : .sig A B i s ≃ B0[Chan.var_Chan; n..]) : False := by
  obtain ⟨r, C, hM⟩ := appSendIm_result_M (n := n) tySend
  have h : Term.sig A B i s ≃ (Term.M (.ch r C))[Chan.var_Chan; n..] := ARS.conv_trans eq hM
  asimp at h
  false_conv

private lemma appSendEx_not_sig {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {v A B A0 B0 : Term} {i : Rlv} {s s0 : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .ex : .pi A0 B0 .ex s0)
    (eq : .sig A B i s ≃ B0[Chan.var_Chan; v..]) : False := by
  obtain ⟨r, C, hM⟩ := appSendEx_result_M (v := v) tySend
  have h : Term.sig A B i s ≃ (Term.M (.ch r C))[Chan.var_Chan; v..] := ARS.conv_trans eq hM
  asimp at h
  false_conv

private lemma appSendIm_not_bool {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {n A B : Term} {s : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .im : .pi A B .im s)
    (eq : .bool ≃ B[Chan.var_Chan; n..]) : False := by
  obtain ⟨r, C, hM⟩ := appSendIm_result_M (n := n) tySend
  have h : Term.bool ≃ (Term.M (.ch r C))[Chan.var_Chan; n..] := ARS.conv_trans eq hM
  asimp at h
  false_conv

private lemma appSendEx_not_bool {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {v A B : Term} {s : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .ex : .pi A B .ex s)
    (eq : .bool ≃ B[Chan.var_Chan; v..]) : False := by
  obtain ⟨r, C, hM⟩ := appSendEx_result_M (v := v) tySend
  have h : Term.bool ≃ (Term.M (.ch r C))[Chan.var_Chan; v..] := ARS.conv_trans eq hM
  asimp at h
  false_conv

private lemma appSendIm_not_ch {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {n A A0 B : Term} {r : Bool} {s : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .im : .pi A0 B .im s)
    (eq : .ch r A ≃ B[Chan.var_Chan; n..]) : False := by
  obtain ⟨r0, C, hM⟩ := appSendIm_result_M (n := n) tySend
  have h : Term.ch r A ≃ (Term.M (.ch r0 C))[Chan.var_Chan; n..] := ARS.conv_trans eq hM
  asimp at h
  false_conv

private lemma appSendEx_not_ch {Θ : PCtx} {Γ : Static.Ctx} {Δ : Ctx} {c : Nat}
    {v A A0 B : Term} {r : Bool} {s : Srt}
    (tySend : Θ ⨾ Γ ⨾ Δ ⊢ .send (.chan (Chan.var_Chan c)) .ex : .pi A0 B .ex s)
    (eq : .ch r A ≃ B[Chan.var_Chan; v..]) : False := by
  obtain ⟨r0, C, hM⟩ := appSendEx_result_M (v := v) tySend
  have h : Term.ch r A ≃ (Term.M (.ch r0 C))[Chan.var_Chan; v..] := ARS.conv_trans eq hM
  asimp at h
  false_conv

/-- Canonical forms for closed values of function type (report Lemmas 5.74 and 5.75). -/
lemma Typed.pi_canonical {Θ A B v T i s}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : T)
    (vl : Val v) (eq : .pi A B i s ≃ T) :
    (∃ A0 m s0, v = .lam A0 m i s0) ∨
      (∃ c, v = .send (.chan (Chan.var_Chan c)) i) := by
  generalize eΓ : ([] : Static.Ctx) = Γ at ty
  generalize eΔ : ([] : Ctx) = Δ at ty
  induction ty generalizing A B i s with
  | @var Θ Γ Δ x t A0 emp wf shs dhs => subst eΔ; cases dhs
  | @lamIm Θ Γ Δ A0 B0 m0 s0 kΘ kΔ tym ih =>
    obtain ⟨_, _, ei, _⟩ := Static.pi_inj eq
    cases ei
    exact .inl ⟨A0, m0, s0, rfl⟩
  | @lamEx Θ Γ Δ A0 B0 m0 s0 t kΘ kΔ tym ih =>
    obtain ⟨_, _, ei, _⟩ := Static.pi_inj eq
    cases ei
    exact .inl ⟨A0, m0, s0, rfl⟩
  | @send Θ Γ Δ r1 r2 A0 B0 m0 i0 hx tym ih =>
    obtain ⟨_, _, ei, _⟩ := Static.pi_inj eq
    cases ei
    cases vl with
    | send => exact .inr ⟨_, rfl⟩
    | thunk th => cases th
  | @appIm Θ Γ Δ A0 B0 m0 n0 s0 tym tyn ih =>
    cases vl with
    | thunk th => cases th with | appSendIm => exact (appSendIm_not_pi tym eq).elim
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 m0 n0 s0 mrgΘ mrgΔ tym tyn ihm ihn =>
    cases vl with
    | thunk th => cases th with | appSendEx _ => exact (appSendEx_not_pi tym eq).elim
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 C0 m0 n0 s0 r0 t0 mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    cases vl with | thunk th => cases th
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 C0 m0 n0 s0 r1 r2 t0 mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    cases vl with | thunk th => cases th
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 m0 n1 n2 s0 mrgΘ mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    cases vl with | thunk th => cases th
  | @conv Θ Γ Δ A0 B0 m0 s0 eq1 tym tyB ih =>
    exact ih vl (ARS.conv_trans eq (ARS.conv_sym eq1)) eΓ eΔ
  | _ => false_conv

/-- Canonical forms for closed values of pair type. -/
lemma Typed.sig_canonical {Θ A B v T i s}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : T)
    (vl : Val v) (eq : .sig A B i s ≃ T) :
    ∃ m1 m2 s0, Val (.pair m1 m2 i s0) ∧ v = .pair m1 m2 i s0 := by
  generalize eΓ : ([] : Static.Ctx) = Γ at ty
  generalize eΔ : ([] : Ctx) = Δ at ty
  induction ty generalizing A B i s with
  | @var Θ Γ Δ x t A0 emp wf shs dhs => subst eΔ; cases dhs
  | @pairIm Θ Γ Δ A0 B0 m0 n0 t0 tyS tym tyn ih =>
    obtain ⟨_, _, ei, _⟩ := Static.sig_inj eq
    cases ei
    cases vl with
    | pairIm hv => exact ⟨m0, n0, t0, .pairIm hv, rfl⟩
    | thunk th => cases th
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 m0 n0 t0 mrgΘ mrgΔ tyS tym tyn ihm ihn =>
    obtain ⟨_, _, ei, _⟩ := Static.sig_inj eq
    cases ei
    cases vl with
    | pairEx hv1 hv2 => exact ⟨m0, n0, t0, .pairEx hv1 hv2, rfl⟩
    | thunk th => cases th
  | @appIm Θ Γ Δ A0 B0 m0 n0 s0 tym tyn ih =>
    cases vl with | thunk th => cases th with | appSendIm => exact (appSendIm_not_sig tym eq).elim
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 m0 n0 s0 mrgΘ mrgΔ tym tyn ihm ihn =>
    cases vl with | thunk th => cases th with | appSendEx _ => exact (appSendEx_not_sig tym eq).elim
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 C0 m0 n0 s0 r0 t0 mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    cases vl with | thunk th => cases th
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 C0 m0 n0 s0 r1 r2 t0 mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    cases vl with | thunk th => cases th
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 m0 n1 n2 s0 mrgΘ mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    cases vl with | thunk th => cases th
  | @conv Θ Γ Δ A0 B0 m0 s0 eq1 tym tyB ih =>
    exact ih vl (ARS.conv_trans eq (ARS.conv_sym eq1)) eΓ eΔ
  | _ => false_conv

/-- Canonical forms for closed values of boolean type. -/
lemma Typed.bool_canonical {Θ v T}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : T)
    (vl : Val v) (eq : .bool ≃ T) : v = .tt ∨ v = .ff := by
  generalize eΓ : ([] : Static.Ctx) = Γ at ty
  generalize eΔ : ([] : Ctx) = Δ at ty
  induction ty with
  | @var Θ Γ Δ x t A0 emp wf shs dhs => subst eΔ; cases dhs
  | @tt Θ Γ Δ emp wf k => exact .inl rfl
  | @ff Θ Γ Δ emp wf k => exact .inr rfl
  | @appIm Θ Γ Δ A0 B0 m0 n0 s0 tym tyn ih =>
    cases vl with | thunk th => cases th with | appSendIm => exact (appSendIm_not_bool tym eq).elim
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 m0 n0 s0 mrgΘ mrgΔ tym tyn ihm ihn =>
    cases vl with | thunk th => cases th with | appSendEx _ => exact (appSendEx_not_bool tym eq).elim
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 C0 m0 n0 s0 r0 t0 mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    cases vl with | thunk th => cases th
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 C0 m0 n0 s0 r1 r2 t0 mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    cases vl with | thunk th => cases th
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 m0 n1 n2 s0 mrgΘ mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    cases vl with | thunk th => cases th
  | @conv Θ Γ Δ A0 B0 m0 s0 eq1 tym tyB ih =>
    exact ih vl (ARS.conv_trans eq (ARS.conv_sym eq1)) eΓ eΔ
  | _ => false_conv

/-- Canonical forms for closed values of channel type. -/
lemma Typed.ch_canonical {Θ r A v T}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : T)
    (vl : Val v) (eq : .ch r A ≃ T) :
    ∃ c, v = .chan (Chan.var_Chan c) := by
  generalize eΓ : ([] : Static.Ctx) = Γ at ty
  generalize eΔ : ([] : Ctx) = Δ at ty
  induction ty generalizing r A with
  | @var Θ Γ Δ x t A0 emp wf shs dhs => subst eΔ; cases dhs
  | @chan Θ Γ Δ r0 x A0 js wf k tyA => exact ⟨x, rfl⟩
  | @appIm Θ Γ Δ A0 B0 m0 n0 s0 tym tyn ih =>
    cases vl with | thunk th => cases th with | appSendIm => exact (appSendIm_not_ch tym eq).elim
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 m0 n0 s0 mrgΘ mrgΔ tym tyn ihm ihn =>
    cases vl with | thunk th => cases th with | appSendEx _ => exact (appSendEx_not_ch tym eq).elim
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 C0 m0 n0 s0 r0 t0 mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    cases vl with | thunk th => cases th
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 B0 C0 m0 n0 s0 r1 r2 t0 mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    cases vl with | thunk th => cases th
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A0 m0 n1 n2 s0 mrgΘ mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    cases vl with | thunk th => cases th
  | @conv Θ Γ Δ A0 B0 m0 s0 eq1 tym tyB ih =>
    exact ih vl (ARS.conv_trans eq (ARS.conv_sym eq1)) eΓ eΔ
  | _ => false_conv

/-- Program-level progress for closed dynamic terms (report Theorem 5.81). -/
theorem Typed.progress {Θ m A}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) :
    Val m ∨ ∃ n, m ~>> n := by
  generalize eΓ : ([] : Static.Ctx) = Γ at ty
  generalize eΔ : ([] : Ctx) = Δ at ty
  induction ty with
  | @var Θ Γ Δ x s A emp wf shs dhs =>
    subst eΔ
    cases dhs
  | @lamIm Θ Γ Δ A B m s kΘ kΔ tym ih =>
    exact .inl .lam
  | @lamEx Θ Γ Δ A B m s t kΘ kΔ tym ih =>
    exact .inl .lam
  | @appIm Θ Γ Δ A B m n s tym tyn ih =>
    subst eΓ
    subst eΔ
    cases ih rfl rfl with
    | inl vl =>
      cases tym.pi_canonical vl ARS.Conv.refl with
      | inl h =>
        obtain ⟨A0, m0, s0, rfl⟩ := h
        exact .inr ⟨_, .betaIm⟩
      | inr h =>
        obtain ⟨c, rfl⟩ := h
        exact .inl (.thunk .appSendIm)
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .appL st⟩
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrgΘ mrgΔ tym tyn ihm ihn =>
    subst eΓ
    subst eΔ
    cases mrgΔ
    cases ihm rfl rfl with
    | inl vlm =>
      cases ihn rfl rfl with
      | inl vln =>
        cases tym.pi_canonical vlm ARS.Conv.refl with
        | inl h =>
          obtain ⟨A0, m0, s0, rfl⟩ := h
          exact .inr ⟨_, .betaEx vln⟩
        | inr h =>
          obtain ⟨c, rfl⟩ := h
          exact .inl (.thunk (.appSendEx vln))
      | inr h =>
        obtain ⟨n', st⟩ := h
        exact .inr ⟨_, .appR st⟩
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .appL st⟩
  | @pairIm Θ Γ Δ A B m n t tyS tym tyn ih =>
    subst eΓ
    subst eΔ
    cases ih rfl rfl with
    | inl vln => exact .inl (.pairIm vln)
    | inr h =>
      obtain ⟨n', st⟩ := h
      exact .inr ⟨_, .pairR st⟩
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrgΘ mrgΔ tyS tym tyn ihm ihn =>
    subst eΓ
    subst eΔ
    cases mrgΔ
    cases ihm rfl rfl with
    | inl vlm =>
      cases ihn rfl rfl with
      | inl vln => exact .inl (.pairEx vlm vln)
      | inr h =>
        obtain ⟨n', st⟩ := h
        exact .inr ⟨_, .pairR st⟩
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .pairL st⟩
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    subst eΓ
    subst eΔ
    cases mrgΔ
    cases ihm rfl rfl with
    | inl vlm =>
      obtain ⟨m1, m2, s0, vlPair, rfl⟩ := tym.sig_canonical vlm ARS.Conv.refl
      exact .inr ⟨_, .projE vlPair⟩
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .projM st⟩
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
    subst eΓ
    subst eΔ
    cases mrgΔ
    cases ihm rfl rfl with
    | inl vlm =>
      obtain ⟨m1, m2, s0, vlPair, rfl⟩ := tym.sig_canonical vlm ARS.Conv.refl
      exact .inr ⟨_, .projE vlPair⟩
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .projM st⟩
  | @one Θ Γ Δ emp wf k =>
    exact .inl .one
  | @tt Θ Γ Δ emp wf k =>
    exact .inl .tt
  | @ff Θ Γ Δ emp wf k =>
    exact .inl .ff
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrgΘ mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    subst eΓ
    subst eΔ
    cases mrgΔ
    cases ihm rfl rfl with
    | inl vlm =>
      cases tym.bool_canonical vlm ARS.Conv.refl with
      | inl h =>
        subst h
        exact .inr ⟨_, .iteT⟩
      | inr h =>
        subst h
        exact .inr ⟨_, .iteF⟩
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .iteM st⟩
  | @pure Θ Γ Δ m A tym ih =>
    subst eΓ
    subst eΔ
    cases ih rfl rfl with
    | inl vlm => exact .inl (.pure vlm)
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .pure st⟩
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrgΘ mrgΔ tyB tym tyn ihm ihn =>
    subst eΓ
    subst eΔ
    cases mrgΔ
    cases ihm rfl rfl with
    | inl vlm =>
      cases tym.monad_canonical vlm ARS.Conv.refl with
      | inl h =>
        obtain ⟨v, vlv, rfl⟩ := h
        exact .inr ⟨_, .mletE vlv⟩
      | inr th =>
        exact .inl (.thunk (.mlet th))
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .mletL st⟩
  | @chan Θ Γ Δ r x A js wf k tyA =>
    exact .inl .chan
  | @fork Θ Γ Δ A m tym ih =>
    exact .inl (.thunk .fork)
  | @recv Θ Γ Δ r1 r2 A B m i hx tym ih =>
    subst eΓ
    subst eΔ
    cases ih rfl rfl with
    | inl vlm =>
      obtain ⟨c, rfl⟩ := tym.ch_canonical vlm ARS.Conv.refl
      exact .inl (.thunk .recv)
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .recv st⟩
  | @send Θ Γ Δ r1 r2 A B m i hx tym ih =>
    subst eΓ
    subst eΔ
    cases ih rfl rfl with
    | inl vlm =>
      obtain ⟨c, rfl⟩ := tym.ch_canonical vlm ARS.Conv.refl
      exact .inl .send
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .send st⟩
  | @close Θ Γ Δ b m tym ih =>
    subst eΓ
    subst eΔ
    cases ih rfl rfl with
    | inl vlm =>
      obtain ⟨c, rfl⟩ := tym.ch_canonical vlm ARS.Conv.refl
      exact .inl (.thunk .close)
    | inr h =>
      obtain ⟨m', st⟩ := h
      exact .inr ⟨_, .close st⟩
  | @conv Θ Γ Δ A B m s eq tym tyB ih =>
    exact ih eΓ eΔ

end TLLC.Dynamic
