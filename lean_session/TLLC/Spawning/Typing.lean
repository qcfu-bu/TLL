import TLLC.Dynamic.Typing
import TLLC.Spawning.Tree

/-!
# Spawning-tree typing

This file formalizes the spawning-tree validity rules from the companion report. Since the Lean
process layer uses the self-dual single-channel representation, a node/child endpoint is described
by a polarity `r` and a protocol `A`, i.e. the channel type `.ch r A`; the dual endpoint is `.ch (!r) A`.

The report's channel contexts for the contained terms contain only single endpoints. We record that
restriction explicitly with `PCtxSingle Θ` in the root and node constructors.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Lookup of a live endpoint inside a process context that may contain several single endpoints. -/
inductive PHas : PCtx → Nat → Bool → Term → Prop where
  | zero {Θ r A} :
    PHas (.one r A :: Θ) 0 r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
  | succ {Θ slot x r A} :
    PHas Θ x r A →
    PHas (slot :: Θ) (x + 1) r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)

mutual

/-- Valid root spawning trees, report judgment `⊩ P`. -/
inductive Typed : Tree → Prop where
  | root {Θ m ms ns} :
    PCtxSingle Θ →
    Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M .unit →
    ChildrenTyped Θ ms →
    SubtreesTyped ns →
    Typed (.root m ms ns)

/-- Valid non-root spawning trees, report judgment `ch^r⟨A⟩ ⊩ P`. -/
inductive TypedAt : Bool → Term → Tree → Prop where
  | node {Θ x r A m ms ns} :
    PCtxSingle Θ →
    PHas Θ x r A →
    Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M .unit →
    ChildrenTyped Θ ms →
    SubtreesTyped ns →
    TypedAt r A (.node (Chan.var_Chan x) m ms ns)

/-- Typing for a node's children against the endpoint context of the node's contained term. -/
inductive ChildrenTyped : PCtx → List (Prod Chan Tree) → Prop where
  | nil {Θ} :
    ChildrenTyped Θ []
  | cons {Θ x r A child children} :
    PHas Θ x r A →
    TypedAt (!r) A child →
    ChildrenTyped Θ children →
    ChildrenTyped Θ (Prod.mk (Chan.var_Chan x) child :: children)

/-- Typing for detached subtrees. -/
inductive SubtreesTyped : List Tree → Prop where
  | nil :
    SubtreesTyped []
  | cons {tree trees} :
    Typed tree →
    SubtreesTyped trees →
    SubtreesTyped (tree :: trees)

end

end TLLC.Spawning
