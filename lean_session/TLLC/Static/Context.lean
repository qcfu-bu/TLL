import TLLC.Syntax
import TLLC.ARS

/-!
# Static contexts

Port of `coq_session/sta_ctx.v`. A static context is a list of types; `Has Γ x A` is the de Bruijn
lookup that shifts the looked-up type past the variables bound to its left (Coq `A.[ren (+1)]`,
here term-renaming by `↑` with channels fixed).
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Static context: a list of types (Coq `sta_ctx := seq term`). -/
abbrev Ctx := List Term

/-- de Bruijn lookup with shifting (Coq `sta_has`). -/
inductive Has : Ctx → Nat → Term → Prop
  | zero {Γ A} :
    Has (A :: Γ) 0 (A⟨(id : Nat → Nat); ↑⟩)
  | succ {Γ A B x} :
    Has Γ x A →
    Has (B :: Γ) (x + 1) (A⟨(id : Nat → Nat); ↑⟩)

end TLLC.Static
