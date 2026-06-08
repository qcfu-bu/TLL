import TLLC.Dynamic.Typing
import TLLC.Spawning.Tree

/-!
# Spawning-tree typing

This file formalizes the spawning-tree validity rules from the companion report. Since the Lean
process layer uses the self-dual single-channel representation, a node/child endpoint is described
by a polarity `r` and a protocol `A`, i.e. the channel type `.ch r A`; the dual endpoint is `.ch (!r) A`.

The report's channel contexts for the contained terms contain only single endpoints, and the
children listed at a node account for exactly the child endpoints in that context. Roots use
`ChildrenTyped Θ ms`, which consumes every live endpoint of `Θ` as a child edge. Internal nodes use
`ChildrenTypedAt Θ x r A ms`, which consumes every live endpoint except the distinguished parent
endpoint `x : ch^r⟨A⟩`.
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

/-- Shifting a parent context slot increments all child-edge labels. The child trees themselves live
in their own endpoint contexts, so only the labels in the current node's child list are shifted. -/
def shiftChildren : List (Chan × Tree) → List (Chan × Tree)
  | [] => []
  | (Chan.var_Chan x, child) :: children => (Chan.var_Chan (x + 1), child) :: shiftChildren children

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
    ChildrenTypedAt Θ x r A ms →
    SubtreesTyped ns →
    TypedAt r A (.node (Chan.var_Chan x) m ms ns)

/-- Exact typing for a node's children against the endpoint context of the contained term.

Every live endpoint in the context must occur as a child edge. The front endpoint is labelled by
channel `0`; endpoints in the tail are shifted by one when embedded under the front slot. -/
inductive ChildrenTyped : PCtx → List (Prod Chan Tree) → Prop where
  | nil :
    ChildrenTyped [] []
  | none {Θ children} :
    ChildrenTyped Θ children →
    ChildrenTyped (.none :: Θ) (shiftChildren children)
  | one {Θ r A child children} :
    TypedAt (!r) (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) child →
    ChildrenTyped Θ children →
    ChildrenTyped (.one r A :: Θ) (Prod.mk (Chan.var_Chan 0) child :: shiftChildren children)

/-- Exact typing for a node's children when one endpoint is reserved as the parent endpoint. -/
inductive ChildrenTypedAt : PCtx → Nat → Bool → Term → List (Prod Chan Tree) → Prop where
  | parent {Θ r A children} :
    ChildrenTyped Θ children →
    ChildrenTypedAt (.one r A :: Θ) 0 r
      (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) (shiftChildren children)
  | none {Θ x r A children} :
    ChildrenTypedAt Θ x r A children →
    ChildrenTypedAt (.none :: Θ) (x + 1) r
      (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) (shiftChildren children)
  | one {Θ x r A r0 A0 child children} :
    TypedAt (!r0) (A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) child →
    ChildrenTypedAt Θ x r A children →
    ChildrenTypedAt (.one r0 A0 :: Θ) (x + 1) r
      (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
      (Prod.mk (Chan.var_Chan 0) child :: shiftChildren children)

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
