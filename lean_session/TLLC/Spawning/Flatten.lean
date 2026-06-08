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

/-- Add `n` all-empty process-context slots in front of a context. -/
def nonePrefix (n : Nat) (Θ : PCtx) : PCtx :=
  List.replicate n Slot.none ++ Θ

@[simp] lemma nonePrefix_zero (Θ : PCtx) : nonePrefix 0 Θ = Θ := rfl

@[simp] lemma nonePrefix_succ (n : Nat) (Θ : PCtx) :
    nonePrefix (n + 1) Θ = Slot.none :: nonePrefix n Θ := by
  rw [nonePrefix, List.replicate_succ]
  rfl

lemma nonePrefix_empty {Θ} (emp : PEmpty Θ) : ∀ n, PEmpty (nonePrefix n Θ)
  | 0 => by simpa [nonePrefix] using emp
  | n + 1 => by simpa [nonePrefix_succ] using PEmpty.none (nonePrefix_empty emp n)

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

lemma shiftN_erasePCtx_agree {Θ : PCtx} (n : Nat) :
    AgreeCSubst (nonePrefix n (erasePCtx Θ))
      (fun x => Chan.var_Chan (x + n)) (erasePCtx Θ) := by
  induction n with
  | zero =>
    simpa [nonePrefix] using (AgreeCSubst.nil (erasePCtx_empty Θ).procWf)
  | succ n ih =>
    have h := AgreeCSubst.pad ih
    simpa [nonePrefix_succ, funcomp, ren_Chan, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h

lemma bindEndpointAt_zero_reserve_agree {Θ r A} (k : Nat) (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: nonePrefix (k + 1) (erasePCtx Θ))
      (Chan.var_Chan 0 .: fun x => Chan.var_Chan (x + (k + 2)))
      (.one r A :: erasePCtx Θ) := by
  have empTail : PEmpty (nonePrefix (k + 1) (erasePCtx Θ)) :=
    nonePrefix_empty (erasePCtx_empty Θ) (k + 1)
  have mrg : PMerge (nonePrefix (k + 2) (erasePCtx Θ))
      (.one r A :: nonePrefix (k + 1) (erasePCtx Θ))
      (.one r A :: nonePrefix (k + 1) (erasePCtx Θ)) :=
    PMerge.oneR empTail.merge_self
  have tyx : (.one r A :: nonePrefix (k + 1) (erasePCtx Θ)) ⨾
      ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ .chan (Chan.var_Chan 0) : .ch r A :=
    TLLC.Process.chanAt0 empTail tyA
  exact AgreeCSubst.wk1 mrg (shiftN_erasePCtx_agree (Θ := Θ) (k + 2)) tyx

/-- The substitution produced while peeling `p` all-empty prefix slots before the selected endpoint.
The parameter `n` is the total number of prefix slots that will ultimately be peeled. -/
def nonePrefixBindSubst (n p : Nat) : Nat → Chan :=
  fun i =>
    if i < p then Chan.var_Chan (n - p + 1 + i)
    else if i = p then Chan.var_Chan 0
    else Chan.var_Chan (i + n + 1 - p)

lemma nonePrefixBindSubst_succ {n p : Nat} (hp : p + 1 ≤ n) :
    (Chan.var_Chan (n - p) .: nonePrefixBindSubst n p) =
      nonePrefixBindSubst n (p + 1) := by
  funext j
  cases j with
  | zero =>
    simp [nonePrefixBindSubst]
    omega
  | succ i =>
    unfold nonePrefixBindSubst
    by_cases hi : i < p
    · simp [hi, Nat.succ_lt_succ hi]
      omega
    · have hnotlt : ¬ i + 1 < p + 1 := by omega
      by_cases hieq : i = p
      · subst i
        simp
      · simp [hi, hieq, hnotlt]
        omega

lemma nonePrefixBindSubst_self (n : Nat) :
    nonePrefixBindSubst n n = bindEndpointAt 0 (Chan.var_Chan n) := by
  funext i
  unfold nonePrefixBindSubst bindEndpointAt
  simp
  by_cases hlt : i < n
  · have hne : i ≠ n := by omega
    simp [hlt, hne]
    omega
  · by_cases heq : i = n
    · simp [heq]
    · simp [hlt, heq]
      omega

lemma bindEndpointAt_nonePrefix_go {Θ r A} (n p : Nat) (hp : p ≤ n)
    (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: nonePrefix (n + 1) (erasePCtx Θ))
      (nonePrefixBindSubst n p) (nonePrefix p (.one r A :: erasePCtx Θ)) := by
  induction p with
  | zero =>
    have agr := bindEndpointAt_zero_reserve_agree (Θ := Θ) (r := r) (A := A) n tyA
    convert agr using 1
    funext i
    cases i with
    | zero => simp [nonePrefixBindSubst]
    | succ i => simp [nonePrefixBindSubst, Nat.add_comm, Nat.add_left_comm]
  | succ p ih =>
    have hp0 : p ≤ n := Nat.le_trans (Nat.le_succ p) hp
    have agr := AgreeCSubst.wk0 (x := n - p) (ih hp0)
    rw [nonePrefixBindSubst_succ hp] at agr
    simpa [nonePrefix_succ] using agr

lemma bindEndpointAt_nonePrefix_agree {Θ r A} (n : Nat) (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: nonePrefix (n + 1) (erasePCtx Θ))
      (bindEndpointAt 0 (Chan.var_Chan n)) (nonePrefix n (.one r A :: erasePCtx Θ)) := by
  have agr := bindEndpointAt_nonePrefix_go (Θ := Θ) (r := r) (A := A) n n (Nat.le_refl n) tyA
  rw [nonePrefixBindSubst_self n] at agr
  exact agr

lemma chanAtN {Θe r A} (emp : PEmpty Θe) (tyA : [] ⊢ A : .proto) (n : Nat) :
    (nonePrefix n (.one r A :: Θe)) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
      .chan (Chan.var_Chan n) : .ch r A := by
  induction n with
  | zero =>
    simpa [nonePrefix] using TLLC.Process.chanAt0 emp tyA
  | succ n ih =>
    have h := TLLC.Dynamic.Typed.cweaken ih
    simpa [nonePrefix_succ] using h

lemma shift3_erasePCtx_agree {Θ : PCtx} :
    AgreeCSubst (.none :: .none :: .none :: erasePCtx Θ)
      (fun x => Chan.var_Chan (x + 3)) (erasePCtx Θ) := by
  simpa [nonePrefix] using (shiftN_erasePCtx_agree (Θ := Θ) 3)

lemma bindEndpointAt_one_tail_agree {Θ r A} (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: .none :: .none :: erasePCtx Θ)
      (Chan.var_Chan 0 .: fun x => Chan.var_Chan (x + 3))
      (.one r A :: erasePCtx Θ) := by
  simpa [nonePrefix, Nat.add_assoc] using
    (bindEndpointAt_zero_reserve_agree (Θ := Θ) (r := r) (A := A) 1 tyA)

lemma bindEndpointAt_one_none_agree {Θ r A} (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: .none :: .none :: erasePCtx Θ)
      (bindEndpointAt 0 (Chan.var_Chan 1)) (.none :: .one r A :: erasePCtx Θ) := by
  have agr : AgreeCSubst (.one r A :: .none :: .none :: erasePCtx Θ)
      (Chan.var_Chan 1 .: (Chan.var_Chan 0 .: fun x => Chan.var_Chan (x + 3)))
      (.none :: .one r A :: erasePCtx Θ) :=
    AgreeCSubst.wk0 (bindEndpointAt_one_tail_agree (Θ := Θ) tyA)
  convert agr using 1
  funext x
  cases x with
  | zero => simp [bindEndpointAt]
  | succ x =>
    cases x with
    | zero => simp [bindEndpointAt]
    | succ x => simp [bindEndpointAt, Nat.add_assoc]

lemma bindEndpointAt_one_one_agree {Θ r A r0 A0}
    (tyA : [] ⊢ A : .proto) (tyA0 : [] ⊢ A0 : .proto) :
    AgreeCSubst (.one r A :: .one r0 A0 :: .none :: erasePCtx Θ)
      (bindEndpointAt 0 (Chan.var_Chan 1)) (.one r0 A0 :: .one r A :: erasePCtx Θ) := by
  have agrTail : AgreeCSubst (.one r A :: .none :: .none :: erasePCtx Θ)
      (Chan.var_Chan 0 .: fun x => Chan.var_Chan (x + 3)) (.one r A :: erasePCtx Θ) :=
    bindEndpointAt_one_tail_agree tyA
  have tyPrefix : (.none :: .one r0 A0 :: .none :: erasePCtx Θ) ⨾
      ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ .chan (Chan.var_Chan 1) : .ch r0 A0 :=
    TLLC.Process.chanAt1 (PEmpty.none (erasePCtx_empty Θ)) tyA0
  have mrgTail : PMerge (.none :: .none :: erasePCtx Θ)
      (.one r0 A0 :: .none :: erasePCtx Θ)
      (.one r0 A0 :: .none :: erasePCtx Θ) :=
    PMerge.oneR (PEmpty.none (erasePCtx_empty Θ)).merge_self
  have mrg : PMerge (.one r A :: .none :: .none :: erasePCtx Θ)
      (.none :: .one r0 A0 :: .none :: erasePCtx Θ)
      (.one r A :: .one r0 A0 :: .none :: erasePCtx Θ) :=
    PMerge.oneL mrgTail
  have agr : AgreeCSubst (.one r A :: .one r0 A0 :: .none :: erasePCtx Θ)
      (Chan.var_Chan 1 .: (Chan.var_Chan 0 .: fun x => Chan.var_Chan (x + 3)))
      (.one r0 A0 :: .one r A :: erasePCtx Θ) :=
    AgreeCSubst.wk1 mrg agrTail tyPrefix
  convert agr using 1
  funext x
  cases x with
  | zero => simp [bindEndpointAt]
  | succ x =>
    cases x with
    | zero => simp [bindEndpointAt]
    | succ x => simp [bindEndpointAt, Nat.add_assoc]

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

lemma one_empty_irrel {Θ Θ' r A p} (ty : TLLC.Process.Typed (.one r A :: Θ) p)
    (emp : PEmpty Θ) (emp' : PEmpty Θ') :
    TLLC.Process.Typed (.one r A :: Θ') p :=
  ty.pctxEmptyRel (.one (.empty emp emp'))

lemma nu_par_typed {Θp Θc Θ p q r A} (tyA : [] ⊢ A : .proto)
    (mrg : PMerge Θp Θc Θ)
    (typ : TLLC.Process.Typed (.one r A :: Θp) p)
    (tyq : TLLC.Process.Typed (.one (!r) A :: Θc) q) :
    TLLC.Process.Typed Θ (.nu (.par p q)) :=
  TLLC.Process.Typed.res tyA (TLLC.Process.Typed.par (.split mrg) typ tyq)

lemma nu_par_empty_tail_typed {Θ p q r A} (emp : PEmpty Θ)
    (tyA : [] ⊢ A : .proto)
    (typ : TLLC.Process.Typed (.one r A :: Θ) p)
    (tyq : TLLC.Process.Typed (.one (!r) A :: Θ) q) :
    TLLC.Process.Typed Θ (.nu (.par p q)) :=
  nu_par_typed tyA emp.merge_self typ tyq

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

lemma shiftChildren_eq_nil {children : List (Chan × Tree)} :
    shiftChildren children = [] → children = [] := by
  cases children with
  | nil => intro _; rfl
  | cons child children =>
    cases child with
    | mk c tree =>
      cases c
      intro h
      contradiction

lemma ChildrenTyped.empty_of_eq_nil {Θ children} (tys : ChildrenTyped Θ children) :
    children = [] → PEmpty Θ := by
  induction Θ generalizing children with
  | nil =>
    intro _
    exact .nil
  | cons slot Θ ih =>
    intro hnil
    cases slot with
    | none =>
      cases tys with
      | none tys0 => exact .none (ih tys0 (shiftChildren_eq_nil hnil))
    | one _ _ =>
      cases tys with
      | one _ _ => contradiction
    | both _ =>
      cases tys

lemma ChildrenTyped.empty_of_nil {Θ} (tys : ChildrenTyped Θ []) : PEmpty Θ :=
  tys.empty_of_eq_nil rfl

lemma ChildrenTyped.flattenChildren_nil_typed {Θ body} (tys : ChildrenTyped Θ [])
    (tyBody : TLLC.Process.Typed Θ body) :
    TLLC.Process.Typed (erasePCtx Θ) (flattenChildren body []) := by
  have emp : PEmpty Θ := tys.empty_of_nil
  simpa using tyBody.empty_irrel emp (erasePCtx_empty Θ)

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

lemma flatten_root_nil_valid {Θ m subtrees}
    (tym : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M .unit)
    (tyChildren : ChildrenTyped Θ [])
    (tySubtrees : SubtreesTyped subtrees)
    (valid : ∀ {tree}, Typed tree → TLLC.Process.Typed [] tree.flatten) :
    TLLC.Process.Typed [] (flattenBody m [] subtrees) := by
  have tyBody : TLLC.Process.Typed (erasePCtx Θ) (flattenChildren (.tm m) []) :=
    tyChildren.flattenChildren_nil_typed (TLLC.Process.Typed.exp tym)
  have tySubs : ∀ q, q ∈ flattenSubtrees subtrees → TLLC.Process.Typed [] q :=
    tySubtrees.flattenSubtrees_typed valid
  have tyFlat : TLLC.Process.Typed (erasePCtx Θ) (flattenBody m [] subtrees) :=
    flattenBody_typed tyBody tySubs
  exact tyFlat.empty_irrel (erasePCtx_empty Θ) PEmpty.nil

lemma flattenChildren_cons_zero_typed {Θ r A body child children}
    (tyA : [] ⊢ A : .proto)
    (tyTail : TLLC.Process.Typed (.one r A :: erasePCtx Θ)
      (flattenChildren body (shiftChildren children)))
    (tyChild : TLLC.Process.Typed (.one (!r) A :: .none :: erasePCtx Θ)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term])) :
    TLLC.Process.Typed (.none :: erasePCtx Θ)
      (flattenChildren body ((Chan.var_Chan 0, child) :: shiftChildren children)) := by
  have tyParent : TLLC.Process.Typed (.one r A :: .none :: erasePCtx Θ)
      ((flattenChildren body (shiftChildren children))[bindEndpointAt 0 (Chan.var_Chan 0);
        Term.var_Term]) :=
    tyTail.csubstitution (bindEndpointAt_zero_agree (Θ := Θ) tyA)
  cases h : child.flattenAt with
  | mk d p =>
    simp [flattenChildren, h]
    exact nu_par_empty_tail_typed (.none (erasePCtx_empty Θ)) tyA tyParent (by
      simpa [h] using tyChild)

lemma flattenChildren_cons_nonePrefix_typed {Θ r A body child children Θc}
    (n : Nat) (tyA : [] ⊢ A : .proto)
    (tyTail : TLLC.Process.Typed (nonePrefix n (.one r A :: erasePCtx Θ))
      (flattenChildren body children))
    (tyChild : TLLC.Process.Typed (.one (!r) A :: Θc)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term]))
    (empC : PEmpty Θc) :
    TLLC.Process.Typed (nonePrefix (n + 1) (erasePCtx Θ))
      (flattenChildren body ((Chan.var_Chan n, child) :: children)) := by
  have tyParent : TLLC.Process.Typed (.one r A :: nonePrefix (n + 1) (erasePCtx Θ))
      ((flattenChildren body children)[bindEndpointAt 0 (Chan.var_Chan n); Term.var_Term]) :=
    tyTail.csubstitution (bindEndpointAt_nonePrefix_agree (Θ := Θ) n tyA)
  have wfOuter : ProcWf (nonePrefix (n + 1) (erasePCtx Θ)) :=
    (nonePrefix_empty (erasePCtx_empty Θ) (n + 1)).procWf
  obtain ⟨Θe, empE, mrg⟩ := TLLC.Process.procWf_emptyR wfOuter
  have tyChild' : TLLC.Process.Typed (.one (!r) A :: Θe)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term]) :=
    one_empty_irrel tyChild empC empE
  cases h : child.flattenAt with
  | mk d p =>
    simp [flattenChildren, h]
    exact nu_par_typed tyA mrg tyParent (by simpa [h] using tyChild')

lemma flattenChildren_cons_one_none_typed {Θ r A body child children Θc}
    (tyA : [] ⊢ A : .proto)
    (tyTail : TLLC.Process.Typed (.none :: .one r A :: erasePCtx Θ)
      (flattenChildren body children))
    (tyChild : TLLC.Process.Typed (.one (!r) A :: Θc)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term]))
    (empC : PEmpty Θc) :
    TLLC.Process.Typed (.none :: .none :: erasePCtx Θ)
      (flattenChildren body ((Chan.var_Chan 1, child) :: children)) := by
  simpa [nonePrefix] using
    (flattenChildren_cons_nonePrefix_typed (Θ := Θ) (r := r) (A := A) (body := body)
      (child := child) (children := children) (Θc := Θc) 1 tyA tyTail tyChild empC)

lemma flattenChildren_cons_one_one_typed {Θ r A r0 A0 body child children Θc}
    (tyA : [] ⊢ A : .proto) (tyA0 : [] ⊢ A0 : .proto)
    (tyTail : TLLC.Process.Typed (.one r0 A0 :: .one r A :: erasePCtx Θ)
      (flattenChildren body children))
    (tyChild : TLLC.Process.Typed (.one (!r) A :: Θc)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term]))
    (empC : PEmpty Θc) :
    TLLC.Process.Typed (.one r0 A0 :: .none :: erasePCtx Θ)
      (flattenChildren body ((Chan.var_Chan 1, child) :: children)) := by
  have tyParent : TLLC.Process.Typed (.one r A :: .one r0 A0 :: .none :: erasePCtx Θ)
      ((flattenChildren body children)[bindEndpointAt 0 (Chan.var_Chan 1); Term.var_Term]) :=
    tyTail.csubstitution (bindEndpointAt_one_one_agree (Θ := Θ) tyA tyA0)
  have wfOuter : ProcWf (.one r0 A0 :: .none :: erasePCtx Θ) :=
    .one (.none (erasePCtx_empty Θ).procWf) tyA0
  obtain ⟨Θe, empE, mrg⟩ := TLLC.Process.procWf_emptyR wfOuter
  have tyChild' : TLLC.Process.Typed (.one (!r) A :: Θe)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term]) :=
    one_empty_irrel tyChild empC empE
  cases h : child.flattenAt with
  | mk d p =>
    simp [flattenChildren, h]
    exact nu_par_typed tyA mrg tyParent (by simpa [h] using tyChild')

end TLLC.Spawning
