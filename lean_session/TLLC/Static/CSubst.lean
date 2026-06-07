import TLLC.Static.CRename

/-!
# Static channel substitution

Port of `coq_session/sta_csubst.v`: the channel-*substitution* preservation metatheorem
`Typed.csubstitution` (Coq `sta_csubstitution` — channel substitution preserves typing), the bridge
`csubst_cren` relating a channel substitution to a channel renaming (Coq `sta_csubst_cren`), and the
channel/term substitution commutation lemmas `csubst_comm`/`csubst_comp`/`csubst_comp'` (Coq
`sta_csubst_comm`/`sta_csubst_comp`/`sta_csubst_comp'`) together with the supporting predicate
`anti_csubst` (Coq `sta_anti_csubst`) and its lift `anti_csubst_up` (Coq `sta_anti_csubst_up`).

Channel substitution is the *other* autosubst slot (the same one channel renaming `CRename.lean`
uses): where a term substitution `Subst.lean` writes `m[Chan.var_Chan; σ]` (channels fixed, term map
substituted), a channel substitution `csubst σ m` is `m[σ; Term.var_Term]` with `σ : Nat → Chan` (the
channel map substituted, term map fixed). Because `Chan` is a first-class autosubst sort whose *only*
constructor is `Chan.var_Chan`, every Lean `σ : Nat → Chan` automatically satisfies the Coq
`sta_agree_csubst` side condition (`∀ x, ∃ c, σ x = CVar c`); that hypothesis is therefore dropped
throughout — substituting a channel for a channel is the only thing the type system allows. This is
more restrictive than Coq (Coq could substitute an arbitrary term for a channel variable as long as
it happened to be a channel), but it is exactly the intended faithful rendering.

The headline mirrors the Coq proof: a channel substitution `m[σ; Term.var_Term]` coincides with the
channel renaming `m⟨csubst_ren σ; id⟩` (`csubst_cren`, where `csubst_ren σ = Chan` index extraction),
so `Typed.csubstitution` reduces to `Typed.crename` from `CRename.lean`. The commutation lemmas are
discharged by `asimp`: since `Chan` and `Term` are two sorts of one multi-sorted system, the
channel/term substitution interaction is pure substitution bookkeeping, leaving only the pointwise
side conditions (`csubst_comm`'s `cren_subst_agree`, `csubst_comp'`'s `anti_csubst`).
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-! ## Channel substitution as a channel renaming. -/

/-- The channel renaming underlying a channel substitution (Coq `csubst_ren`). Because `Chan` is a
    pure variable sort (`Chan.var_Chan` is its only constructor), the Coq `match σ x with CVar y => y`
    becomes a total destructor extracting the channel variable's index. -/
def csubst_ren (σ : Nat → Chan) : Nat → Nat := fun x => match σ x with | Chan.var_Chan y => y

/-- Re-tagging the extracted indices recovers the channel substitution (`Chan.var_Chan` is a
    section/retraction pair with `csubst_ren`); the Coq counterpart is the `have[c->]:=agr x` step in
    `sta_csubst_cren`, here total because `σ : Nat → Chan` is automatically channel-valued. -/
lemma csubst_ren_eq (σ : Nat → Chan) : funcomp Chan.var_Chan (csubst_ren σ) = σ := by
  funext x
  show Chan.var_Chan (csubst_ren σ x) = σ x
  unfold csubst_ren
  cases σ x with
  | var_Chan n => rfl

/-- A channel renaming on both slots written via substitution: renaming the channel slot by `ξ` and
    fixing the term slot equals substituting `funcomp Chan.var_Chan ξ` for channels (an instance of
    the autosubst `rinst_inst` law). -/
lemma cren_csubst (m : Term) (ξ : Nat → Nat) :
    m⟨ξ; (id : Nat → Nat)⟩ = m[funcomp Chan.var_Chan ξ; Term.var_Term] :=
  rinst_inst_Term ξ id (funcomp Chan.var_Chan ξ) Term.var_Term (fun _ => rfl) (fun _ => rfl) m

/-- Channel substitution is the channel renaming by its extracted indices (Coq `sta_csubst_cren`).
    The Coq `sta_agree_csubst σ` hypothesis is automatic here (`σ : Nat → Chan`). -/
lemma csubst_cren (m : Term) (σ : Nat → Chan) :
    m⟨csubst_ren σ; (id : Nat → Nat)⟩ = m[σ; Term.var_Term] := by
  rw [cren_csubst, csubst_ren_eq]

/-! ## Channel substitution preserves typing. -/

/-- Channel substitution preserves typing (Coq `sta_csubstitution`). The conclusion type is *not*
    substituted: channel types are context-free and closed, so the substituted subject keeps the same
    type. As in Coq, this reduces to channel renaming (`Typed.crename`) via `csubst_cren`. -/
lemma Typed.csubstitution {Γ m A} (tym : Γ ⊢ m : A) (σ : Nat → Chan) :
    Γ ⊢ m[σ; Term.var_Term] : A := by
  rw [← csubst_cren]
  exact tym.crename (csubst_ren σ)

/-- Up-to-equality variant of `Typed.csubstitution` (Coq-style `sta_ecsubstitution` convenience). -/
lemma Typed.ecsubstitution {Γ m m' A} {σ : Nat → Chan} (e : m' = m[σ; Term.var_Term])
    (tym : Γ ⊢ m : A) : Γ ⊢ m' : A := by
  subst e; exact tym.csubstitution σ

/-! ## Commutation of channel substitution with term substitution. -/

/-- Channel substitution commutes with a term substitution that is invariant under it (Coq
    `sta_csubst_comm`). The Coq side condition `cren_subst_agree σ2 σ2 (csubst_ren σ1)` becomes the
    pointwise `∀ x, σ2 x = (σ2 x)[σ1; Term.var_Term]` (`σ2`'s images are fixed by the channel
    substitution); the rest is substitution bookkeeping (`asimp`). -/
lemma csubst_comm (σ1 : Nat → Chan) (σ2 : Nat → Term) (m : Term)
    (h : ∀ x, σ2 x = (σ2 x)[σ1; Term.var_Term]) :
    (m[σ1; Term.var_Term])[Chan.var_Chan; σ2] = (m[Chan.var_Chan; σ2])[σ1; Term.var_Term] := by
  asimp
  congr 1
  funext x
  exact h x

/-- Channel substitution commutes with a term renaming (Coq `sta_csubst_comp`). A term renaming never
    introduces channels, so no side condition is needed (the Coq `sta_agree_csubst σ` hypothesis is
    automatic). -/
lemma csubst_comp (σ : Nat → Chan) (ξ : Nat → Nat) (m : Term) :
    (m[σ; Term.var_Term])⟨(id : Nat → Nat); ξ⟩ = (m⟨(id : Nat → Nat); ξ⟩)[σ; Term.var_Term] := by
  asimp

/-- A term substitution whose every image is closed under (any) channel substitution (Coq
    `sta_anti_csubst`). Such a substitution introduces no free channel variables, so it commutes with
    channel substitution unconditionally. -/
def anti_csubst (σ' : Nat → Term) : Prop :=
  ∀ x (σ0 : Nat → Chan), σ' x = (σ' x)[σ0; Term.var_Term]

/-- `anti_csubst` lifts under a term binder (Coq `sta_anti_csubst_up`). -/
lemma anti_csubst_up {σ : Nat → Term} (h : anti_csubst σ) : anti_csubst (up_Term_Term σ) := by
  intro x σ0
  cases x with
  | zero => rfl
  | succ x =>
    have e : up_Term_Term σ (x + 1) = (σ x)⟨(id : Nat → Nat); ↑⟩ := by asimp
    rw [e]
    conv_lhs => rw [h x σ0]
    asimp

/-- Channel substitution commutes with an `anti_csubst` term substitution (Coq `sta_csubst_comp'`). -/
lemma csubst_comp' (σ : Nat → Chan) (σ' : Nat → Term) (m : Term) (h : anti_csubst σ') :
    (m[σ; Term.var_Term])[Chan.var_Chan; σ'] = (m[Chan.var_Chan; σ'])[σ; Term.var_Term] := by
  asimp
  congr 1
  funext x
  exact h x σ

end TLLC.Static
