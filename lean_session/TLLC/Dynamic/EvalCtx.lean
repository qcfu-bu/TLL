import TLLC.Dynamic.Inversion
import TLLC.Dynamic.Step

/-!
# Evaluation contexts (global-progress seed)

Port of `coq_session/eval_ctx.v` (excluded from the Coq `_CoqProject` — unfinished scaffolding toward
global progress). An `EvalCtx` is a left-nested chain of monadic binds `Bind (Bind (… □ …) …) …`;
`EvalCtx.eval M m` plugs `m` into the hole. `evalCtx_inv` (Coq `dyn_eval_ctx_inv`) decomposes a
well-typed plugged term `Θ ; · ; · ⊢ eval M m : IO B` into the typing of the redex `m : IO A` and a
"continuation" that re-types `eval M n` for any replacement `n : IO A` over a compatible split of `Θ`.

This is one of the two seeds (with `Progress.lean`) for the Lean-only deadlock-freedom contribution.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- A monadic-bind evaluation context (Coq `eval_ctx`). -/
inductive EvalCtx where
  | hole
  | bnd (M : EvalCtx) (n : Term)

/-- Plug a term into the hole of an evaluation context (Coq `eval`). -/
def EvalCtx.eval : EvalCtx → Term → Term
  | .hole, m => m
  | .bnd M n, m => .mlet (M.eval m) n

/-- Decomposition of a well-typed plugged term (Coq `dyn_eval_ctx_inv`). -/
lemma evalCtx_inv {Θ} {M : EvalCtx} {m B} (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ M.eval m : .M B) :
    ∃ Θ1 Θ2 A,
      Merge Θ1 Θ2 Θ ∧
      (Θ1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M A) ∧
      (∀ Θ3 Θ' n,
        Merge Θ2 Θ3 Θ' →
        (Θ3 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ n : .M A) →
        Θ' ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ M.eval n : .M B) := by
  induction M generalizing Θ m B with
  | hole =>
    -- `eval hole m = m`, so `ty : Θ ⊢ m : .M B`.
    obtain ⟨Θ0, emp, mrg⟩ := ty.empty
    refine ⟨Θ, Θ0, B, mrg.sym, ty, ?_⟩
    intro Θ3 Θ' n mrg2 tyn
    -- `Θ0` empty, so the split `Θ0 ∘ Θ3 => Θ'` forces `Θ3 = Θ'`.
    have e := mrg2.emptyL emp; subst e
    exact tyn
  | bnd M' n' ih =>
    -- `eval (bind M' n') m = .mlet (eval M' m) n'`.
    obtain ⟨s, tyIO⟩ := ty.validity
    obtain ⟨r, tyB, _⟩ := Static.M_inv tyIO
    obtain ⟨Θ1, Θ2, Δ1, Δ2, A, t, mrg1, mrg2, tyM', tyn'⟩ := mlet_inv ty
    cases mrg2
    obtain ⟨Θ11, Θ12, A0, mrg3, tym, hcont⟩ := ih tyM'
    obtain ⟨Θa, mrga, mrgb⟩ := mrg1.splitR mrg3
    refine ⟨Θ11, Θa, A0, mrgb.sym, tym, ?_⟩
    intro Θ3 Θ' n mrgH tyn
    obtain ⟨Θc, mrgc, mrgd⟩ := mrgH.splitL mrga
    have tyM0 := hcont Θ3 Θc n mrgc tyn
    exact .mlet mrgd .nil tyB tyM0 tyn'

/-- Channel renaming of an evaluation context (Coq `CRename_evalctx`). -/
def EvalCtx.cren (ξ : Nat → Nat) : EvalCtx → EvalCtx
  | .hole => .hole
  | .bnd M n => .bnd (M.cren ξ) (n⟨ξ; (id : Nat → Nat)⟩)

/-- Channel renaming commutes with plugging (Coq `evalctx_cren`). -/
lemma evalctx_cren (ξ : Nat → Nat) (M : EvalCtx) (m : Term) :
    (M.eval m)⟨ξ; (id : Nat → Nat)⟩ = (M.cren ξ).eval (m⟨ξ; (id : Nat → Nat)⟩) := by
  induction M with
  | hole => rfl
  | bnd M' n ih =>
    show (Term.mlet (M'.eval m) n)⟨ξ; (id : Nat → Nat)⟩
      = Term.mlet ((M'.cren ξ).eval (m⟨ξ; (id : Nat → Nat)⟩)) (n⟨ξ; (id : Nat → Nat)⟩)
    asimp; rw [ih]

end TLLC.Dynamic
