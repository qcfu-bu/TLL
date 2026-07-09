import TLLC.Process.SoupFlat
import TLLC.Spawning.Flatten
import TLLC.Spawning.Step
import TLLC.Spawning.Distinct

/-!
# The soup of a spawning tree

The prenex configuration of a flattened spawning tree, described structurally: one binder per
edge, one thread per node body, with a single global renaming carrying the (globally distinct)
edge names to binder indices. Both names of an edge — the label `c` in the parent's child map and
the channel `d` carried by the child node — map to the same binder.

This description feeds the reflection theorem (`TLLC/Spawning/Reflection.lean`): a machine step
fired on the soup pulls back through the renaming to a node body and an edge of the tree.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open TLLC.Process (Config SoupEquiv prenex)
open scoped TLLC.Static TLLC.Dynamic

/-! ## Bodies and edges -/

mutual

/-- All node bodies of a tree: this node's first, then the children's, then the subtrees'. -/
def treeBodies : Tree → List Term
  | .root m ms ns => m :: (childBodies ms ++ subBodies ns)
  | .node _ m ms ns => m :: (childBodies ms ++ subBodies ns)
termination_by tree => treeMeasure tree
decreasing_by all_goals (simp only [treeMeasure]; omega)

def childBodies : List (Chan × Tree) → List Term
  | [] => []
  | (_, child) :: ms => treeBodies child ++ childBodies ms
termination_by ms => childMeasure ms
decreasing_by all_goals (simp only [childMeasure]; omega)

def subBodies : List Tree → List Term
  | [] => []
  | t :: ns => treeBodies t ++ subBodies ns
termination_by ns => subMeasure ns
decreasing_by all_goals (simp only [subMeasure]; omega)

end

/-- The channel a (child) node carries toward its parent; junk for roots. -/
def childChan : Tree → Nat
  | .root _ _ _ => 0
  | .node d _ _ _ => chanIndex d

mutual

/-- The edges of a tree as (parent-side label, child-side channel) index pairs, in the same
canonical order as the children lists. -/
def treeEdges : Tree → List (Nat × Nat)
  | .root _ ms ns => childEdges ms ++ subEdges ns
  | .node _ _ ms ns => childEdges ms ++ subEdges ns
termination_by tree => treeMeasure tree
decreasing_by all_goals (simp only [treeMeasure]; omega)

def childEdges : List (Chan × Tree) → List (Nat × Nat)
  | [] => []
  | (c, child) :: ms =>
      (chanIndex c, childChan child) :: (treeEdges child ++ childEdges ms)
termination_by ms => childMeasure ms
decreasing_by all_goals (simp only [childMeasure]; omega)

def subEdges : List Tree → List (Nat × Nat)
  | [] => []
  | t :: ns => treeEdges t ++ subEdges ns
termination_by ns => subMeasure ns
decreasing_by all_goals (simp only [subMeasure]; omega)

end

end TLLC.Spawning
