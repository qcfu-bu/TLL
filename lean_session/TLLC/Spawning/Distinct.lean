import Mathlib.Tactic
import TLLC.Spawning.Tree
import TLLC.Spawning.Channel

/-!
# Spawning-tree channel distinctness

A Barendregt-style freshness invariant for spawning trees: all de Bruijn channel indices appearing
anywhere in the tree (each node's parent endpoint, every child edge label at every depth, and the
labels/endpoints of detached subtrees) are pairwise distinct.

The spawning-tree typing judgments assign each node its own endpoint context independently, so
well-typed trees may reuse channel indices across levels (a grandchild edge may collide with a root
child edge). The flattening resolves such collisions via nested `bindEndpointAt`, but the simulation
proof (Lemma 5.86) needs the raw indices to be globally distinct, so `Distinct` is folded into the
spawning-tree typing judgment (`TLLC.Spawning.Typed`/`TypedAt`).

This file is kept upstream of `Spawning.Typing` (it must not depend on `Spawning.Flatten`, which
itself imports `Spawning.Typing`); it therefore carries its own termination measure.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation

/-! ## Termination measure (local copy, independent of `Spawning.Flatten`) -/

mutual
def treeMeasure : Tree → Nat
  | .root _ ms ns => childMeasure ms + subMeasure ns + 2
  | .node _ _ ms ns => childMeasure ms + subMeasure ns + 2
def childMeasure : List (Chan × Tree) → Nat
  | [] => 0
  | (_, child) :: ms => treeMeasure child + childMeasure ms + 1
def subMeasure : List Tree → Nat
  | [] => 0
  | t :: ns => treeMeasure t + subMeasure ns + 1
end

/-! ## Channel collection -/

mutual
/-- All channel indices appearing anywhere in a tree: each node's own endpoint, every child edge
label at every depth, and the labels/endpoints of detached subtrees. The labels at a node form a
clean prefix of the recursive interior, so distinctness extraction is straightforward. -/
def treeChans : Tree → List Nat
  | .root _ ms ns => (ms.map (fun e => chanIndex e.1)) ++ childInteriors ms ++ subInteriors ns
  | .node d _ ms ns =>
      chanIndex d :: ((ms.map (fun e => chanIndex e.1)) ++ childInteriors ms ++ subInteriors ns)
termination_by tree => treeMeasure tree
decreasing_by all_goals (simp only [treeMeasure]; omega)
def childInteriors : List (Chan × Tree) → List Nat
  | [] => []
  | (_, child) :: ms => treeChans child ++ childInteriors ms
termination_by ms => childMeasure ms
decreasing_by all_goals (simp only [childMeasure]; omega)
def subInteriors : List Tree → List Nat
  | [] => []
  | t :: ns => treeChans t ++ subInteriors ns
termination_by ns => subMeasure ns
decreasing_by all_goals (simp only [subMeasure]; omega)
end

/-- The channel-distinctness invariant: all channel indices in the tree are pairwise distinct. -/
def Distinct (t : Tree) : Prop := (treeChans t).Nodup

@[simp] lemma childInteriors_nil : childInteriors [] = [] := by simp [childInteriors]

@[simp] lemma childInteriors_cons (c : Chan) (child : Tree) (ms : List (Chan × Tree)) :
    childInteriors ((c, child) :: ms) = treeChans child ++ childInteriors ms := by
  simp [childInteriors]

@[simp] lemma subInteriors_nil : subInteriors [] = [] := by simp [subInteriors]

@[simp] lemma subInteriors_cons (t : Tree) (ns : List Tree) :
    subInteriors (t :: ns) = treeChans t ++ subInteriors ns := by simp [subInteriors]

lemma treeChans_root (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeChans (.root m ms ns) =
      (ms.map (fun e => chanIndex e.1)) ++ childInteriors ms ++ subInteriors ns := by
  simp [treeChans]

lemma treeChans_node (d : Chan) (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeChans (.node d m ms ns) =
      chanIndex d ::
        ((ms.map (fun e => chanIndex e.1)) ++ childInteriors ms ++ subInteriors ns) := by
  simp [treeChans]

/-- A child's channel list is a sublist of the interior of its sibling list. -/
lemma treeChans_sublist_childInteriors {c : Chan} {child : Tree} :
    ∀ {ms : List (Chan × Tree)}, (c, child) ∈ ms →
      List.Sublist (treeChans child) (childInteriors ms) := by
  intro ms
  induction ms with
  | nil => intro h; cases h
  | cons hd ms ih =>
      obtain ⟨c', child'⟩ := hd
      intro h
      rw [childInteriors_cons]
      rcases List.mem_cons.mp h with heq | hmem
      · obtain ⟨_, rfl⟩ := Prod.mk.injEq .. ▸ heq
        exact List.sublist_append_left _ _
      · exact (ih hmem).trans (List.sublist_append_right _ _)

lemma treeChans_sublist_subInteriors {sub : Tree} :
    ∀ {ns : List Tree}, sub ∈ ns → List.Sublist (treeChans sub) (subInteriors ns) := by
  intro ns
  induction ns with
  | nil => intro h; cases h
  | cons t ns ih =>
      intro h
      rw [subInteriors_cons]
      rcases List.mem_cons.mp h with rfl | hmem
      · exact List.sublist_append_left _ _
      · exact (ih hmem).trans (List.sublist_append_right _ _)

/-- `labels ++ interior` of a root's children is a sublist of the whole tree's channel list. -/
lemma labelsInteriors_sublist_root {m ms ns} :
    List.Sublist ((ms.map (fun e => chanIndex e.1)) ++ childInteriors ms)
      (treeChans (.root m ms ns)) := by
  rw [treeChans_root]; exact List.sublist_append_left _ _

lemma labelsInteriors_sublist_node {d m ms ns} :
    List.Sublist ((ms.map (fun e => chanIndex e.1)) ++ childInteriors ms)
      (treeChans (.node d m ms ns)) := by
  rw [treeChans_node]; exact (List.sublist_append_left _ _).trans (List.sublist_cons_self _ _)

/-- The interior of a root's children sits inside the root's full channel list. -/
lemma childInteriors_sublist_treeChans_root {m ms ns} :
    List.Sublist (childInteriors ms) (treeChans (.root m ms ns)) := by
  rw [treeChans_root]
  exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)

lemma childInteriors_sublist_treeChans_node {d m ms ns} :
    List.Sublist (childInteriors ms) (treeChans (.node d m ms ns)) := by
  rw [treeChans_node]
  exact ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _)).trans
    (List.sublist_cons_self _ _)

lemma subInteriors_sublist_treeChans_root {m ms ns} :
    List.Sublist (subInteriors ns) (treeChans (.root m ms ns)) := by
  rw [treeChans_root]
  exact List.sublist_append_right _ _

lemma subInteriors_sublist_treeChans_node {d m ms ns} :
    List.Sublist (subInteriors ns) (treeChans (.node d m ms ns)) := by
  rw [treeChans_node]
  exact (List.sublist_append_right _ _).trans (List.sublist_cons_self _ _)

/-- Distinctness is inherited by each child of a root. -/
lemma Distinct.child_root {m ms ns c child}
    (h : Distinct (.root m ms ns)) (mem : (c, child) ∈ ms) : Distinct child :=
  ((treeChans_sublist_childInteriors mem).trans childInteriors_sublist_treeChans_root).nodup h

lemma Distinct.child_node {d m ms ns c child}
    (h : Distinct (.node d m ms ns)) (mem : (c, child) ∈ ms) : Distinct child :=
  ((treeChans_sublist_childInteriors mem).trans childInteriors_sublist_treeChans_node).nodup h

lemma Distinct.subtree_root {m ms ns sub}
    (h : Distinct (.root m ms ns)) (mem : sub ∈ ns) : Distinct sub :=
  ((treeChans_sublist_subInteriors mem).trans subInteriors_sublist_treeChans_root).nodup h

lemma Distinct.subtree_node {d m ms ns sub}
    (h : Distinct (.node d m ms ns)) (mem : sub ∈ ns) : Distinct sub :=
  ((treeChans_sublist_subInteriors mem).trans subInteriors_sublist_treeChans_node).nodup h

end TLLC.Spawning
