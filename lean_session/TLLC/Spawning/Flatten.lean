import Mathlib.Tactic
import TLLC.Spawning.Tree

/-!
# Flattening spawning trees

This file formalizes the flattening operation from report page 28. A root spawning tree flattens to a
standard process configuration, while a node additionally exposes the channel by which it
communicates with its parent.

The report writes restrictions as named two-endpoint binders `ν c d`. The Lean process syntax uses
the self-dual single-channel binder `Proc.nu`; consequently a child edge `(c, Node d ...)` is compiled
by putting one fresh self-dual channel in scope and replacing the parent's endpoint `c` and the
child's parent endpoint `d` by that bound channel. Children are scoped one at a time by a nest of
`nu` binders.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation

/-- Extract the de Bruijn index from a channel variable. -/
def chanIndex : Chan → Nat
  | .var_Chan x => x

@[simp] lemma chanIndex_var (x : Nat) : chanIndex (.var_Chan x) = x := rfl

/-- Channel substitution for moving under one fresh binder and tying one named endpoint to it. The
selected endpoint becomes the freshly bound channel `0`; all other free channels are weakened. -/
def bindEndpointAt (depth : Nat) (c : Chan) (x : Nat) : Chan :=
  if x = chanIndex c + depth then .var_Chan 0 else .var_Chan (x + 1)

/-- Parallel composition of a list of processes with an accumulator. -/
def parAll (p : Proc) (ps : List Proc) : Proc :=
  ps.foldl Proc.par p

@[simp] lemma parAll_nil (p : Proc) : parAll p [] = p := rfl

@[simp] lemma parAll_cons (p q : Proc) (ps : List Proc) :
    parAll p (q :: ps) = parAll (.par p q) ps := rfl

mutual

/-- Size measure for spawning trees, used only to justify the mutual recursion below. -/
def treeSize : Tree → Nat
  | .root _ children subtrees => childListSize children + treeListSize subtrees + 2
  | .node _ _ children subtrees => childListSize children + treeListSize subtrees + 2

def childListSize : List (Chan × Tree) → Nat
  | [] => 0
  | (_, child) :: children => treeSize child + childListSize children + 1

def treeListSize : List Tree → Nat
  | [] => 0
  | tree :: trees => treeSize tree + treeListSize trees + 1

end

mutual

/-- Flatten a spawning tree to a standard process configuration, report notation `|P| = P`. -/
def Tree.flatten : Tree → Proc
  | .root m ms ns => flattenBody m ms ns
  | .node _ m ms ns => flattenBody m ms ns
termination_by tree => treeSize tree
decreasing_by
  all_goals
    simp only [treeSize]
    omega

/-- Flatten a non-root spawning tree to its parent endpoint and process, report notation
`|P| = (d, P)`.

The root case is present only to keep the raw operation total; the spawning-tree typing judgment uses
`TypedAt` for children, so well-typed child trees are nodes. -/
def Tree.flattenAt : Tree → Chan × Proc
  | .root m ms ns => (.var_Chan 0, flattenBody m ms ns)
  | .node d m ms ns => (d, flattenBody m ms ns)
termination_by tree => treeSize tree
decreasing_by
  all_goals
    simp only [treeSize]
    omega

def flattenBody (m : Term) (children : List (Chan × Tree)) (subtrees : List Tree) : Proc :=
  parAll (flattenChildren 0 (.tm m) children) (flattenSubtrees subtrees)
termination_by childListSize children + treeListSize subtrees + 1
decreasing_by
  all_goals omega

/-- Add the child processes to an accumulated body, introducing one fresh channel per child edge.
The `depth` parameter records how many restrictions already surround the body; an original endpoint
label `c` is therefore found at de Bruijn index `c + depth`. -/
def flattenChildren : Nat → Proc → List (Chan × Tree) → Proc
  | _, body, [] => body
  | depth, body, (c, child) :: children =>
      let (d, p) := child.flattenAt
      .nu (flattenChildren (depth + 1)
        (.par (body[bindEndpointAt depth c; Term.var_Term])
          (p[bindEndpointAt depth d; Term.var_Term]))
        children)
termination_by _ _ children => childListSize children
decreasing_by
  all_goals
    simp only [childListSize]
    omega

def flattenSubtrees : List Tree → List Proc
  | [] => []
  | tree :: trees => tree.flatten :: flattenSubtrees trees
termination_by trees => treeListSize trees
decreasing_by
  all_goals
    simp only [treeListSize]
    omega

end

@[simp] lemma Tree.flatten_root (m : Term) (children : List (Chan × Tree))
    (subtrees : List Tree) :
    Tree.flatten (.root m children subtrees) = flattenBody m children subtrees := by
  simp [Tree.flatten]

@[simp] lemma Tree.flatten_node (parent : Chan) (m : Term) (children : List (Chan × Tree))
    (subtrees : List Tree) :
    Tree.flatten (.node parent m children subtrees) = flattenBody m children subtrees := by
  simp [Tree.flatten]

@[simp] lemma Tree.flattenAt_root (m : Term) (children : List (Chan × Tree))
    (subtrees : List Tree) :
    Tree.flattenAt (.root m children subtrees) = (.var_Chan 0, flattenBody m children subtrees) := by
  simp [Tree.flattenAt]

@[simp] lemma Tree.flattenAt_node (parent : Chan) (m : Term) (children : List (Chan × Tree))
    (subtrees : List Tree) :
    Tree.flattenAt (.node parent m children subtrees) = (parent, flattenBody m children subtrees) := by
  simp [Tree.flattenAt]

@[simp] lemma flattenChildren_nil (depth : Nat) (body : Proc) :
    flattenChildren depth body [] = body := by
  simp [flattenChildren]

@[simp] lemma flattenSubtrees_nil : flattenSubtrees [] = [] := by
  simp [flattenSubtrees]

@[simp] lemma flattenSubtrees_cons (tree : Tree) (trees : List Tree) :
    flattenSubtrees (tree :: trees) = tree.flatten :: flattenSubtrees trees := by
  simp [flattenSubtrees]

/-- The explicit recursion over detached subtrees is extensionally the report's list map. -/
lemma flattenSubtrees_eq_map (trees : List Tree) :
    flattenSubtrees trees = trees.map Tree.flatten := by
  induction trees with
  | nil => simp
  | cons tree trees ih => simp [ih]

end TLLC.Spawning
