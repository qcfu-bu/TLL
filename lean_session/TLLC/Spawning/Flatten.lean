import Mathlib.Tactic
import TLLC.Process.CSubst
import TLLC.Spawning.Tree
import TLLC.Spawning.Typing

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
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

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

/-- Keep the de Bruijn shape of a process context, but erase all live endpoints. -/
def erasePCtx : PCtx → PCtx
  | [] => []
  | _ :: Θ => .none :: erasePCtx Θ

@[simp] lemma erasePCtx_nil : erasePCtx [] = [] := rfl

@[simp] lemma erasePCtx_cons (slot : Slot) (Θ : PCtx) :
    erasePCtx (slot :: Θ) = .none :: erasePCtx Θ := rfl

lemma erasePCtx_empty (Θ : PCtx) : PEmpty (erasePCtx Θ) := by
  induction Θ with
  | nil => exact .nil
  | cons _ Θ ih => exact .none ih

/-- Erase every endpoint except the one at the given de Bruijn index. -/
def eraseExcept : PCtx → Nat → PCtx
  | [], _ => []
  | slot :: Θ, 0 => slot :: erasePCtx Θ
  | _ :: Θ, x + 1 => .none :: eraseExcept Θ x

@[simp] lemma eraseExcept_nil (x : Nat) : eraseExcept [] x = [] := by
  cases x <;> rfl

@[simp] lemma eraseExcept_zero (slot : Slot) (Θ : PCtx) :
    eraseExcept (slot :: Θ) 0 = slot :: erasePCtx Θ := rfl

@[simp] lemma eraseExcept_succ (slot : Slot) (Θ : PCtx) (x : Nat) :
    eraseExcept (slot :: Θ) (x + 1) = .none :: eraseExcept Θ x := rfl

lemma PHas.eraseExcept {Θ x r A} (has : PHas Θ x r A) :
    PJust (eraseExcept Θ x) x r A := by
  induction has with
  | zero =>
    simp
    exact PJust.zero (erasePCtx_empty _)
  | succ _ ih =>
    simp
    exact PJust.none ih

lemma bindEndpointAt_zero_eq :
    bindEndpointAt 0 (Chan.var_Chan 0) =
      up_Chan_Chan (funcomp (ren_Chan Nat.succ) Chan.var_Chan) := by
  funext x
  cases x with
  | zero => simp [bindEndpointAt, up_Chan_Chan]
  | succ x => simp [bindEndpointAt, up_Chan_Chan, funcomp, ren_Chan]

lemma bindEndpointAt_zero_agree {Θ r A} (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: .none :: erasePCtx Θ)
      (bindEndpointAt 0 (Chan.var_Chan 0)) (.one r A :: erasePCtx Θ) := by
  rw [bindEndpointAt_zero_eq]
  exact AgreeCSubst.ty (AgreeCSubst.pad (AgreeCSubst.nil (erasePCtx_empty Θ).procWf)) tyA

lemma parAll_typed {Θ p ps} (ty : TLLC.Process.Typed Θ p)
    (tys : ∀ q, q ∈ ps → TLLC.Process.Typed [] q) :
    TLLC.Process.Typed Θ (parAll p ps) := by
  induction ps generalizing Θ p with
  | nil =>
    simpa using ty
  | cons q qs ih =>
    have tyq : TLLC.Process.Typed [] q := tys q (by simp)
    have tyqs : ∀ q', q' ∈ qs → TLLC.Process.Typed [] q' := by
      intro q' hq'
      exact tys q' (by simp [hq'])
    obtain ⟨Θe, emp, mrg⟩ := TLLC.Process.procWf_emptyR ty.procWf
    have tyq' : TLLC.Process.Typed Θe q := tyq.empty_irrel PEmpty.nil emp
    exact ih (TLLC.Process.Typed.par mrg ty tyq') tyqs

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
  parAll (flattenChildren (.tm m) children) (flattenSubtrees subtrees)
termination_by childListSize children + treeListSize subtrees + 1
decreasing_by
  all_goals omega

/-- Add the child processes to an accumulated body, introducing one fresh channel per child edge. -/
def flattenChildren : Proc → List (Chan × Tree) → Proc
  | body, [] => body
  | body, (c, child) :: children =>
      let (d, p) := child.flattenAt
      .nu (.par
        ((flattenChildren body children)[bindEndpointAt 0 c; Term.var_Term])
        (p[bindEndpointAt 0 d; Term.var_Term]))
termination_by _ children => childListSize children
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

@[simp] lemma flattenChildren_nil (body : Proc) :
    flattenChildren body [] = body := by
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

lemma SubtreesTyped.flattenSubtrees_typed {trees}
    (tys : SubtreesTyped trees)
    (valid : ∀ {tree}, Typed tree → TLLC.Process.Typed [] tree.flatten) :
    ∀ q, q ∈ flattenSubtrees trees → TLLC.Process.Typed [] q := by
  induction trees with
  | nil =>
    intro q hq
    simp at hq
  | cons tree trees ih =>
    cases tys with
    | cons tyt tyts =>
      intro q hq
      simp at hq
      rcases hq with hq | hq
      · subst hq
        exact valid tyt
      · exact ih tyts q hq

lemma flattenBody_typed {Θ m children subtrees}
    (tyChildren : TLLC.Process.Typed Θ (flattenChildren (.tm m) children))
    (tySubtrees : ∀ q, q ∈ flattenSubtrees subtrees → TLLC.Process.Typed [] q) :
    TLLC.Process.Typed Θ (flattenBody m children subtrees) := by
  simp [flattenBody]
  exact parAll_typed tyChildren tySubtrees

lemma flattenChildren_nil_typed {Θ m}
    (tym : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M .unit) :
    TLLC.Process.Typed Θ (flattenChildren (.tm m) []) := by
  simp
  exact TLLC.Process.Typed.exp tym

end TLLC.Spawning
