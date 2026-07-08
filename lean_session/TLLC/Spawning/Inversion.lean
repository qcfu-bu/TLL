import TLLC.Spawning.Distinct
import TLLC.Spawning.Flatten
import TLLC.Spawning.Step

/-!
# Spawning-tree typing inversions

Derived facts about the spawning-tree validity judgments used by both fidelity (Lemma 5.87,
`TLLC/Spawning/Fidelity.lean`) and the simulation development (`TLLC/Spawning/Simulation.lean`):
child-edge lookup and typing extraction, label distinctness and context-liveness
correspondences, the reserved-parent strengthening, END-redex typing preservation for detached
children, and the `splitChildrenByTerm` membership theory.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

lemma SubtreesTyped.typed_of_mem {trees : List Tree} {tree : Tree}
    (typed : SubtreesTyped trees) (member : tree ∈ trees) :
    Typed tree := by
  induction trees generalizing tree with
  | nil =>
      cases member
  | cons _ _ ih =>
      cases typed with
      | cons typedHead typedTail =>
          cases member with
          | head =>
              exact typedHead
          | tail _ memberTail =>
              exact ih typedTail memberTail

lemma Typed.subtree_typed {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {subtree : Tree}
    (typed : Typed (.root m children subtrees)) (member : subtree ∈ subtrees) :
    Typed subtree := by
  cases typed with
  | root _ _ _ typedSubtrees =>
      exact typedSubtrees.typed_of_mem member

lemma TypedAt.subtree_typed {parent : Chan} {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {subtree : Tree} {r : Bool} {A : Term}
    (typed : TypedAt r A (.node parent m children subtrees)) (member : subtree ∈ subtrees) :
    Typed subtree := by
  cases typed with
  | node _ _ _ _ typedSubtrees =>
      exact typedSubtrees.typed_of_mem member

lemma shiftChildren_mem_child {children : List (Chan × Tree)} {c : Chan} {child : Tree}
    (member : (c, child) ∈ shiftChildren children) :
    ∃ c', (c', child) ∈ children := by
  induction children with
  | nil =>
      cases member
  | cons edge children ih =>
      rcases edge with ⟨edgeChannel, edgeChild⟩
      cases edgeChannel with
      | var_Chan edgeIndex =>
          cases member with
          | head =>
              exact ⟨.var_Chan edgeIndex, by simp⟩
          | tail _ tail =>
              obtain ⟨c', memberTail⟩ := ih tail
              exact ⟨c', by simp [memberTail]⟩

def childLabels (children : List (Chan × Tree)) : List Chan :=
  children.map Prod.fst

lemma shiftChildren_mem_inv {children : List (Chan × Tree)} {x : Nat} {child : Tree}
    (member : (Chan.var_Chan (x + 1), child) ∈ shiftChildren children) :
    (Chan.var_Chan x, child) ∈ children := by
  induction children with
  | nil =>
      cases member
  | cons head children ih =>
      rcases head with ⟨c, headChild⟩
      cases c with
      | var_Chan y =>
          simp [shiftChildren] at member ⊢
          rcases member with eqHead | memberTail
          · rcases eqHead with ⟨hx, hchild⟩
            exact Or.inl ⟨hx, hchild⟩
          · exact Or.inr (ih memberTail)

lemma zero_notin_shiftLabels {children : List (Chan × Tree)} :
    Chan.var_Chan 0 ∉ childLabels (shiftChildren children) := by
  induction children with
  | nil =>
      simp [childLabels, shiftChildren]
  | cons head children ih =>
      rcases head with ⟨c, child⟩
      cases c with
      | var_Chan x =>
          simp [childLabels, shiftChildren]
          intro tree member
          apply ih
          exact List.mem_map.mpr ⟨(Chan.var_Chan 0, tree), member, rfl⟩

lemma zero_pair_notin_shift {children : List (Chan × Tree)} :
    ∀ child, (Chan.var_Chan 0, child) ∉ shiftChildren children := by
  intro child member
  exact zero_notin_shiftLabels (List.mem_map.mpr ⟨(Chan.var_Chan 0, child), member, rfl⟩)

lemma childLabels_nodup_shift {children : List (Chan × Tree)}
    (nodup : (childLabels children).Nodup) :
    (childLabels (shiftChildren children)).Nodup := by
  induction children with
  | nil =>
      simp [childLabels, shiftChildren]
  | cons head children ih =>
      rcases head with ⟨c, child⟩
      cases c with
      | var_Chan x =>
          simp [childLabels, shiftChildren] at nodup ⊢
          constructor
          · intro tree member
            exact nodup.1 tree (shiftChildren_mem_inv member)
          · exact ih nodup.2

lemma childLabels_shift_mem_inv {children : List (Chan × Tree)} {x : Nat}
    (member : Chan.var_Chan (x + 1) ∈ childLabels (shiftChildren children)) :
    Chan.var_Chan x ∈ childLabels children := by
  rcases List.mem_map.mp member with ⟨edge, memberEdge, eqEdge⟩
  rcases edge with ⟨c, child⟩
  cases c with
  | var_Chan y =>
      simp at eqEdge
      subst eqEdge
      exact List.mem_map.mpr ⟨(Chan.var_Chan x, child), shiftChildren_mem_inv memberEdge, rfl⟩

lemma ChildrenTyped.labels_nodup {Θ children}
    (typed : ChildrenTyped Θ children) :
    (childLabels children).Nodup := by
  refine ChildrenTyped.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ children _ => (childLabels children).Nodup)
    (motive_4 := fun _ _ _ _ children _ => (childLabels children).Nodup)
    (motive_5 := fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial)
    (by simp [childLabels])
    (fun _ ih => childLabels_nodup_shift ih)
    (fun _ _ _ ih => by
      simp [childLabels]
      exact ⟨zero_pair_notin_shift, childLabels_nodup_shift ih⟩)
    (fun _ ih => childLabels_nodup_shift ih)
    (fun _ ih => childLabels_nodup_shift ih)
    (fun _ _ _ ih => by
      simp [childLabels]
      exact ⟨zero_pair_notin_shift, childLabels_nodup_shift ih⟩)
    trivial
    (fun _ _ _ _ => trivial)
    typed

lemma ChildrenTypedAt.labels_nodup {Θ x r A children}
    (typed : ChildrenTypedAt Θ x r A children) :
    (childLabels children).Nodup := by
  refine ChildrenTypedAt.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ children _ => (childLabels children).Nodup)
    (motive_4 := fun _ _ _ _ children _ => (childLabels children).Nodup)
    (motive_5 := fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial)
    (by simp [childLabels])
    (fun _ ih => childLabels_nodup_shift ih)
    (fun _ _ _ ih => by
      simp [childLabels]
      exact ⟨zero_pair_notin_shift, childLabels_nodup_shift ih⟩)
    (fun _ ih => childLabels_nodup_shift ih)
    (fun _ ih => childLabels_nodup_shift ih)
    (fun _ _ _ ih => by
      simp [childLabels]
      exact ⟨zero_pair_notin_shift, childLabels_nodup_shift ih⟩)
    trivial
    (fun _ _ _ _ => trivial)
    typed

lemma ChildrenTyped.pos_of_label {Θ children c}
    (typed : ChildrenTyped Θ children) (member : c ∈ childLabels children) :
    CvarPos Θ (chanIndex c) true := by
  refine ChildrenTyped.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun Θ children _ =>
      ∀ c, c ∈ childLabels children → CvarPos Θ (chanIndex c) true)
    (motive_4 := fun Θ _ _ _ children _ =>
      ∀ c, c ∈ childLabels children → CvarPos Θ (chanIndex c) true)
    (motive_5 := fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial)
    (by simp [childLabels])
    (fun _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact False.elim (zero_notin_shiftLabels member)
          | succ x =>
              exact CvarPos.cons (ih (Chan.var_Chan x) (childLabels_shift_mem_inv member)))
    (fun _ _ _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact CvarPos.one
          | succ x =>
              simp [childLabels] at member
              rcases member with ⟨tree, memberTail⟩
              exact CvarPos.cons (ih (Chan.var_Chan x)
                (List.mem_map.mpr ⟨(Chan.var_Chan x, tree),
                  shiftChildren_mem_inv memberTail, rfl⟩)))
    (fun _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact False.elim (zero_notin_shiftLabels member)
          | succ x =>
              exact CvarPos.cons (ih (Chan.var_Chan x) (childLabels_shift_mem_inv member)))
    (fun _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact False.elim (zero_notin_shiftLabels member)
          | succ x =>
              exact CvarPos.cons (ih (Chan.var_Chan x) (childLabels_shift_mem_inv member)))
    (fun _ _ _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact CvarPos.one
          | succ x =>
              simp [childLabels] at member
              rcases member with ⟨tree, memberTail⟩
              exact CvarPos.cons (ih (Chan.var_Chan x)
                (List.mem_map.mpr ⟨(Chan.var_Chan x, tree),
                  shiftChildren_mem_inv memberTail, rfl⟩)))
    trivial
    (fun _ _ _ _ => trivial)
    typed c member

lemma ChildrenTypedAt.pos_of_label {Θ x r A children c}
    (typed : ChildrenTypedAt Θ x r A children) (member : c ∈ childLabels children) :
    CvarPos Θ (chanIndex c) true := by
  refine ChildrenTypedAt.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun Θ children _ =>
      ∀ c, c ∈ childLabels children → CvarPos Θ (chanIndex c) true)
    (motive_4 := fun Θ _ _ _ children _ =>
      ∀ c, c ∈ childLabels children → CvarPos Θ (chanIndex c) true)
    (motive_5 := fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial)
    (by simp [childLabels])
    (fun _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact False.elim (zero_notin_shiftLabels member)
          | succ x =>
              exact CvarPos.cons (ih (Chan.var_Chan x) (childLabels_shift_mem_inv member)))
    (fun _ _ _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact CvarPos.one
          | succ x =>
              simp [childLabels] at member
              rcases member with ⟨tree, memberTail⟩
              exact CvarPos.cons (ih (Chan.var_Chan x)
                (List.mem_map.mpr ⟨(Chan.var_Chan x, tree),
                  shiftChildren_mem_inv memberTail, rfl⟩)))
    (fun _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact False.elim (zero_notin_shiftLabels member)
          | succ x =>
              exact CvarPos.cons (ih (Chan.var_Chan x) (childLabels_shift_mem_inv member)))
    (fun _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact False.elim (zero_notin_shiftLabels member)
          | succ x =>
              exact CvarPos.cons (ih (Chan.var_Chan x) (childLabels_shift_mem_inv member)))
    (fun _ _ _ ih c member => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact CvarPos.one
          | succ x =>
              simp [childLabels] at member
              rcases member with ⟨tree, memberTail⟩
              exact CvarPos.cons (ih (Chan.var_Chan x)
                (List.mem_map.mpr ⟨(Chan.var_Chan x, tree),
                  shiftChildren_mem_inv memberTail, rfl⟩)))
    trivial
    (fun _ _ _ _ => trivial)
    typed c member

lemma ChildrenTyped.not_label_of_fresh {Θ m A children c}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A)
    (typed : ChildrenTyped Θ children) (fresh : chanFreshIn c m) :
    c ∉ childLabels children := by
  intro member
  cases c with
  | var_Chan x =>
      have pos := typed.pos_of_label member
      have occ := ty.occurs1 pos
      unfold chanFreshIn at fresh
      simp at occ fresh
      rw [fresh] at occ
      omega

lemma ChildrenTypedAt.not_label_of_fresh {Θ x r A m B children c}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : B)
    (typed : ChildrenTypedAt Θ x r A children) (fresh : chanFreshIn c m) :
    c ∉ childLabels children := by
  intro member
  cases c with
  | var_Chan y =>
      have pos := typed.pos_of_label member
      have occ := ty.occurs1 pos
      unfold chanFreshIn at fresh
      simp at occ fresh
      rw [fresh] at occ
      omega

lemma child_pair_notin_after {before after : List (Chan × Tree)} {c : Chan} {child : Tree}
    (nodup : (childLabels (before ++ (c, child) :: after)).Nodup) :
    ∀ tree, (c, tree) ∉ after := by
  induction before with
  | nil =>
      simp [childLabels] at nodup
      exact nodup.1
  | cons head before ih =>
      rcases head with ⟨e, sibling⟩
      simp [childLabels] at nodup
      exact ih (by simpa [childLabels] using nodup.2)

lemma child_pair_notin_before {before after : List (Chan × Tree)} {c : Chan} {child : Tree}
    (nodup : (childLabels (before ++ (c, child) :: after)).Nodup) :
    ∀ tree, (c, tree) ∉ before := by
  induction before with
  | nil =>
      simp
  | cons head before ih =>
      rcases head with ⟨e, sibling⟩
      simp [childLabels] at nodup ⊢
      intro tree
      constructor
      · intro eqLabel _
        exact nodup.1.2.1 eqLabel.symm
      · exact ih (by simpa [childLabels] using nodup.2) tree

lemma childLabel_notin_after {before after : List (Chan × Tree)} {c : Chan} {child : Tree}
    (nodup : (childLabels (before ++ (c, child) :: after)).Nodup) :
    c ∉ childLabels after := by
  intro member
  rcases List.mem_map.mp member with ⟨edge, memberEdge, eqEdge⟩
  rcases edge with ⟨e, tree⟩
  subst eqEdge
  exact child_pair_notin_after nodup tree memberEdge

lemma childLabel_notin_before {before after : List (Chan × Tree)} {c : Chan} {child : Tree}
    (nodup : (childLabels (before ++ (c, child) :: after)).Nodup) :
    c ∉ childLabels before := by
  intro member
  rcases List.mem_map.mp member with ⟨edge, memberEdge, eqEdge⟩
  rcases edge with ⟨e, tree⟩
  subst eqEdge
  exact child_pair_notin_before nodup tree memberEdge

lemma ChildrenTyped.typedAt_of_mem {Θ : PCtx} {children : List (Chan × Tree)}
    {c : Chan} {child : Tree}
    (typed : ChildrenTyped Θ children) (member : (c, child) ∈ children) :
    ∃ r A, TypedAt r A child := by
  induction Θ generalizing children c child with
  | nil =>
      cases typed
      cases member
  | cons _ Θ ih =>
      cases typed with
      | none typedTail =>
          obtain ⟨c', memberTail⟩ := shiftChildren_mem_child member
          exact ih typedTail memberTail
      | one typedChild typedTail =>
          cases member with
          | head =>
              exact ⟨_, _, typedChild⟩
          | tail _ memberTail =>
              obtain ⟨c', memberTailOriginal⟩ := shiftChildren_mem_child memberTail
              exact ih typedTail memberTailOriginal

lemma ChildrenTypedAt.typedAt_of_mem {Θ : PCtx} {x : Nat} {role : Bool} {protocol : Term}
    {children : List (Chan × Tree)} {c : Chan} {child : Tree}
    (typed : ChildrenTypedAt Θ x role protocol children) (member : (c, child) ∈ children) :
    ∃ r A, TypedAt r A child := by
  induction Θ generalizing x protocol children c child with
  | nil =>
      cases typed
  | cons _ Θ ih =>
      cases typed with
      | parent typedChildren =>
          obtain ⟨c', memberTail⟩ := shiftChildren_mem_child member
          exact typedChildren.typedAt_of_mem memberTail
      | none typedTail =>
          obtain ⟨c', memberTail⟩ := shiftChildren_mem_child member
          exact ih typedTail memberTail
      | one typedChild typedTail =>
          cases member with
          | head =>
              exact ⟨_, _, typedChild⟩
          | tail _ memberTail =>
              obtain ⟨c', memberTailOriginal⟩ := shiftChildren_mem_child memberTail
              exact ih typedTail memberTailOriginal

lemma ChildrenTyped.typedAt_of_mem_wf {Θ : PCtx} {children : List (Chan × Tree)}
    {c : Chan} {child : Tree}
    (typed : ChildrenTyped Θ children) (wf : ProcWf Θ) (member : (c, child) ∈ children) :
    ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) child := by
  induction Θ generalizing children c child with
  | nil =>
      cases typed
      cases member
  | cons slot Θ ih =>
      cases typed with
      | none typedTail =>
          cases wf with
          | none wfTail =>
              obtain ⟨c', memberTail⟩ := shiftChildren_mem_child member
              exact ih typedTail wfTail memberTail
      | one typedChild typedTail =>
          cases wf with
          | one wfTail tyA =>
              cases member with
              | head =>
                  exact ⟨_, _, tyA, typedChild⟩
              | tail _ memberTail =>
                  obtain ⟨c', memberTailOriginal⟩ := shiftChildren_mem_child memberTail
                  exact ih typedTail wfTail memberTailOriginal

lemma ChildrenTypedAt.typedAt_of_mem_wf {Θ : PCtx} {x : Nat} {role : Bool}
    {protocol : Term} {children : List (Chan × Tree)} {c : Chan} {child : Tree}
    (typed : ChildrenTypedAt Θ x role protocol children) (wf : ProcWf Θ)
    (member : (c, child) ∈ children) :
    ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) child := by
  induction Θ generalizing x protocol children c child with
  | nil =>
      cases typed
  | cons slot Θ ih =>
      cases typed with
      | parent typedChildren =>
          cases wf with
          | one wfTail _ =>
              obtain ⟨c', memberTail⟩ := shiftChildren_mem_child member
              exact typedChildren.typedAt_of_mem_wf wfTail memberTail
      | none typedTail =>
          cases wf with
          | none wfTail =>
              obtain ⟨c', memberTail⟩ := shiftChildren_mem_child member
              exact ih typedTail wfTail memberTail
      | one typedChild typedTail =>
          cases wf with
          | one wfTail tyA =>
              cases member with
              | head =>
                  exact ⟨_, _, tyA, typedChild⟩
              | tail _ memberTail =>
                  obtain ⟨c', memberTailOriginal⟩ := shiftChildren_mem_child memberTail
                  exact ih typedTail wfTail memberTailOriginal

lemma Typed.child_typedAt {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {c : Chan} {child : Tree}
    (typed : Typed (.root m children subtrees)) (member : (c, child) ∈ children) :
    ∃ r A, TypedAt r A child := by
  cases typed with
  | root _ _ typedChildren _ =>
      exact typedChildren.typedAt_of_mem member

lemma TypedAt.child_typedAt {parent : Chan} {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {c : Chan} {child : Tree} {r : Bool} {A : Term}
    (typed : TypedAt r A (.node parent m children subtrees)) (member : (c, child) ∈ children) :
    ∃ r A, TypedAt r A child := by
  cases typed with
  | node _ _ _ typedChildren _ =>
      exact typedChildren.typedAt_of_mem member

lemma Typed.child_typedAt_wf {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {c : Chan} {child : Tree}
    (typed : Typed (.root m children subtrees)) (member : (c, child) ∈ children) :
    ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) child := by
  cases typed with
  | root _ typedTerm typedChildren _ =>
      exact typedChildren.typedAt_of_mem_wf typedTerm.procWf member

lemma TypedAt.child_typedAt_wf {parent : Chan} {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {c : Chan} {child : Tree} {r : Bool} {A : Term}
    (typed : TypedAt r A (.node parent m children subtrees)) (member : (c, child) ∈ children) :
    ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) child := by
  cases typed with
  | node _ _ typedTerm typedChildren _ =>
      exact typedChildren.typedAt_of_mem_wf typedTerm.procWf member

lemma PHas.pos_true {Θ x r A} (has : PHas Θ x r A) :
    CvarPos Θ x true := by
  induction has with
  | zero =>
      exact CvarPos.one
  | succ _ ih =>
      exact CvarPos.cons ih

lemma evalctx_occurs_close_chan (M : EvalCtx) (b : Bool) (c : Chan) :
    occurs (chanIndex c) (M.eval (.close b (Term.chan c))) =
      occurs (chanIndex c) (M.eval (.pure .one)) + 1 := by
  induction M with
  | hole =>
      cases c with
      | var_Chan x =>
          simp [EvalCtx.eval, occurs, chanIndex]
  | bnd M n ih =>
      simp [EvalCtx.eval, occurs, ih, Nat.add_comm, Nat.add_left_comm]

lemma Typed.close_unused {M : EvalCtx} {b : Bool} {c : Chan}
    {children : List (Chan × Tree)} {subtrees : List Tree}
    (typed : Typed (.root (M.eval (.close b (Term.chan c))) children subtrees))
    (member : c ∈ childLabels children) :
    occurs (chanIndex c) (M.eval (.pure .one)) = 0 := by
  cases typed with
  | root _ typedTerm typedChildren _ =>
      have pos := typedChildren.pos_of_label member
      have occ := typedTerm.occurs1 pos
      rw [evalctx_occurs_close_chan] at occ
      omega

lemma TypedAt.close_unused {M : EvalCtx} {b : Bool} {c parent : Chan}
    {children : List (Chan × Tree)} {subtrees : List Tree} {r A}
    (typed : TypedAt r A (.node parent (M.eval (.close b (Term.chan c))) children subtrees))
    (member : c ∈ childLabels children) :
    occurs (chanIndex c) (M.eval (.pure .one)) = 0 := by
  cases typed with
  | node _ _ typedTerm typedChildren _ =>
      have pos := typedChildren.pos_of_label member
      have occ := typedTerm.occurs1 pos
      rw [evalctx_occurs_close_chan] at occ
      omega

lemma TypedAt.parent_close_unused {N : EvalCtx} {b : Bool} {d : Chan}
    {children : List (Chan × Tree)} {subtrees : List Tree} {r A}
    (typed : TypedAt r A (.node d (N.eval (.close b (Term.chan d))) children subtrees)) :
    occurs (chanIndex d) (N.eval (.pure .one)) = 0 := by
  cases d with
  | var_Chan x =>
      cases typed with
      | node _ has typedTerm _ _ =>
          have pos := has.pos_true
          have occ := typedTerm.occurs1 pos
          have h := evalctx_occurs_close_chan N b (Chan.var_Chan x)
          simp [chanIndex] at h occ ⊢
          rw [h] at occ
          omega

/-- Away from the closed endpoint, a close body has the same channel occurrences as its
post-step `pure one` form. -/
lemma close_term_occurs_eq (M : EvalCtx) (b : Bool) (c : Chan) (i : Nat)
    (ne : i ≠ chanIndex c) :
    occurs i (M.eval (.close b (Term.chan c))) = occurs i (M.eval (.pure .one)) := by
  induction M with
  | hole =>
      cases c with
      | var_Chan x =>
          simp only [chanIndex] at ne
          simp [EvalCtx.eval, occurs]
          omega
  | bnd M n ih =>
      simp [EvalCtx.eval, occurs, ih]

/-- Strengthen a reserved-parent children typing to a plain children typing: once the parent
endpoint (the single live slot of `Θ1`) is consumed, the merge complement `Θ2` types the same
children with no reserved slot. -/
lemma ChildrenTypedAt.strengthen {Θ1 : PCtx} {x : Nat} {r' : Bool} {B : Term}
    (just : PJust Θ1 x r' B) :
    ∀ {Θ2 Θ : PCtx} {r : Bool} {A : Term} {children : List (Chan × Tree)},
      PMerge Θ1 Θ2 Θ →
      ChildrenTypedAt Θ x r A children →
      ChildrenTyped Θ2 children := by
  induction just with
  | zero emp =>
      intro Θ2 Θ r A children mrg typed
      cases mrg with
      | oneL mrg' =>
          cases typed with
          | parent typedChildren =>
              rw [mrg'.emptyL emp]
              exact ChildrenTyped.none typedChildren
      | split mrg' =>
          cases typed
  | none _ ih =>
      intro Θ2 Θ r A children mrg typed
      cases mrg with
      | none mrg' =>
          cases typed with
          | none typed' =>
              exact ChildrenTyped.none (ih mrg' typed')
      | oneR mrg' =>
          cases typed with
          | one tyChild typed' =>
              exact ChildrenTyped.one tyChild (ih mrg' typed')
      | bothR mrg' =>
          cases typed

/-- Close-step typing preservation for the detached child: consuming the parent endpoint of a
closing node leaves a valid detached root tree. -/
lemma TypedAt.close_detached_typed {N : EvalCtx} {b : Bool} {d : Chan}
    {ms' : List (Chan × Tree)} {qs' : List Tree} {r : Bool} {A : Term}
    (typed : TypedAt r A (.node d (N.eval (.close b (Term.chan d))) ms' qs')) :
    Typed (.root (N.eval (.pure .one)) ms' qs') := by
  cases d with
  | var_Chan x =>
      cases typed with
      | node single has typedTerm typedChildren typedSubtrees =>
          obtain ⟨Θ1, Θ2, A0, mrg, tyClose, cont⟩ := evalCtx_inv typedTerm
          have hinv : (Term.M A0 ≃ Term.M .unit) ∧
              (Θ1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
                .chan (Chan.var_Chan x) : .ch b .stop) := by
            cases b
            · exact wait_inv tyClose
            · exact close_inv tyClose
          obtain ⟨eqA0, tyChan⟩ := hinv
          obtain ⟨r1, A1, just, _, _⟩ := chan_inv tyChan
          obtain ⟨s, tyMA0⟩ := tyClose.validity
          have tyPure : erasePCtx Θ2 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
              Term.pure .one : .M A0 :=
            Typed.conv (ARS.conv_sym eqA0)
              (Typed.pure (Typed.one (erasePCtx_empty Θ2) Wf.nil Key.nil)) tyMA0
          have tyTerm2 : Θ2 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
              N.eval (.pure .one) : .M .unit :=
            cont (erasePCtx Θ2) Θ2 (.pure .one) (PMerge.erasePCtx_right Θ2) tyPure
          exact Typed.root (PCtxSingle.split single mrg).2 tyTerm2
            (ChildrenTypedAt.strengthen just mrg typedChildren) typedSubtrees

/-- Occurrences of a plugged eval context decompose into context and hole parts. -/
lemma evalctx_occurs_plug (M : EvalCtx) (X : Term) (i : Nat) :
    occurs i (M.eval X) = occurs i (M.eval (.pure .one)) + occurs i X := by
  induction M with
  | hole => simp [EvalCtx.eval, occurs]
  | bnd M n ih =>
      simp [EvalCtx.eval, occurs, ih]
      omega

/-- Unfolding equation for `splitChildrenByTerm` on an absent head edge. -/
lemma splitChildrenByTerm_cons_pos {m : Term} {ex : Nat} {sib : Tree}
    {rest : List (Chan × Tree)} (hocc : occurs ex m = 0) :
    splitChildrenByTerm m ((Chan.var_Chan ex, sib) :: rest)
      = ((splitChildrenByTerm m rest).1,
          (Chan.var_Chan ex, sib) :: (splitChildrenByTerm m rest).2) := by
  simp [splitChildrenByTerm, hocc]

/-- Unfolding equation for `splitChildrenByTerm` on an occurring head edge. -/
lemma splitChildrenByTerm_cons_neg {m : Term} {ex : Nat} {sib : Tree}
    {rest : List (Chan × Tree)} (hocc : ¬ occurs ex m = 0) :
    splitChildrenByTerm m ((Chan.var_Chan ex, sib) :: rest)
      = ((Chan.var_Chan ex, sib) :: (splitChildrenByTerm m rest).1,
          (splitChildrenByTerm m rest).2) := by
  simp [splitChildrenByTerm, hocc]

/-- Membership and occurrence characterization of the first split component. -/
lemma splitChildrenByTerm_mem₁ {m : Term} :
    ∀ {ms : List (Chan × Tree)} {p : Chan × Tree},
      p ∈ (splitChildrenByTerm m ms).1 →
      p ∈ ms ∧ occurs (chanIndex p.1) m ≠ 0 := by
  intro ms
  induction ms with
  | nil =>
      intro p hp
      simp [splitChildrenByTerm] at hp
  | cons q rest ih =>
      intro p hp
      rcases q with ⟨e, sib⟩
      cases e with
      | var_Chan ex =>
          by_cases hocc : occurs ex m = 0
          · rw [splitChildrenByTerm_cons_pos hocc] at hp
            obtain ⟨hm, ho⟩ := ih hp
            exact ⟨by simp [hm], ho⟩
          · rw [splitChildrenByTerm_cons_neg hocc] at hp
            simp only [List.mem_cons] at hp
            rcases hp with h | hp
            · subst h
              exact ⟨by simp, by simpa [chanIndex] using hocc⟩
            · obtain ⟨hm, ho⟩ := ih hp
              exact ⟨by simp [hm], ho⟩

/-- Membership and occurrence characterization of the second split component. -/
lemma splitChildrenByTerm_mem₂ {m : Term} :
    ∀ {ms : List (Chan × Tree)} {p : Chan × Tree},
      p ∈ (splitChildrenByTerm m ms).2 →
      p ∈ ms ∧ occurs (chanIndex p.1) m = 0 := by
  intro ms
  induction ms with
  | nil =>
      intro p hp
      simp [splitChildrenByTerm] at hp
  | cons q rest ih =>
      intro p hp
      rcases q with ⟨e, sib⟩
      cases e with
      | var_Chan ex =>
          by_cases hocc : occurs ex m = 0
          · rw [splitChildrenByTerm_cons_pos hocc] at hp
            simp only [List.mem_cons] at hp
            rcases hp with h | hp
            · subst h
              exact ⟨by simp, by simpa [chanIndex] using hocc⟩
            · obtain ⟨hm, ho⟩ := ih hp
              exact ⟨by simp [hm], ho⟩
          · rw [splitChildrenByTerm_cons_neg hocc] at hp
            obtain ⟨hm, ho⟩ := ih hp
            exact ⟨by simp [hm], ho⟩

/-- Core freshness extraction: in a node/root with children `children` containing a child node
`(c, node d N grandkids gsubs)`, distinctness of `labels ++ interior` forces every grandchild
label `e` to be different from the child's endpoint `d` and from all sibling labels. -/
lemma grandchild_fresh {children : List (Chan × Tree)} {c d : Chan} {ct : Term}
    {grandkids : List (Chan × Tree)} {gsubs : List Tree}
    (hnodup : ((children.map (fun e => chanIndex e.1)) ++ childInteriors children).Nodup)
    (memChild : (c, .node d ct grandkids gsubs) ∈ children)
    {e : Chan} {gc : Tree} (memGc : (e, gc) ∈ grandkids) :
    chanIndex e ≠ chanIndex d ∧ e ∉ childLabels children := by
  rw [List.nodup_append] at hnodup
  obtain ⟨_, hinterior, hdisj⟩ := hnodup
  set selChild : Tree := .node d ct grandkids gsubs with hsel
  have hsub : List.Sublist (treeChans selChild) (childInteriors children) :=
    treeChans_sublist_childInteriors memChild
  have hmemSel : chanIndex e ∈ treeChans selChild := by
    rw [hsel, treeChans_node]
    exact List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨(e, gc), memGc, rfl⟩)))
  have hmemInt : chanIndex e ∈ childInteriors children := hsub.subset hmemSel
  have hnodupSel : (treeChans selChild).Nodup := hsub.nodup hinterior
  refine ⟨?_, ?_⟩
  · rw [hsel, treeChans_node, List.nodup_cons] at hnodupSel
    intro heq
    apply hnodupSel.1
    rw [← heq]
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨(e, gc), memGc, rfl⟩))
  · intro hmemLabel
    have hmapMem : chanIndex e ∈ children.map (fun x => chanIndex x.1) := by
      rcases List.mem_map.mp hmemLabel with ⟨edge, hedge, herfl⟩
      exact List.mem_map.mpr ⟨edge, hedge, by rw [herfl]⟩
    exact hdisj _ hmapMem _ hmemInt rfl

/-- In a node, a grandchild label differs from the node's own parent endpoint. -/
lemma grandchild_ne_node_parent {parent d : Chan} {mt ct : Term} {c : Chan}
    {children grandkids : List (Chan × Tree)} {gsubs subtrees : List Tree}
    (h : Distinct (.node parent mt children subtrees))
    (memChild : (c, .node d ct grandkids gsubs) ∈ children)
    {e : Chan} {gc : Tree} (memGc : (e, gc) ∈ grandkids) :
    chanIndex e ≠ chanIndex parent := by
  unfold Distinct at h
  rw [treeChans_node, List.nodup_cons] at h
  intro heq
  apply h.1
  rw [← heq]
  have hsub := treeChans_sublist_childInteriors memChild
  have hmemSel : chanIndex e ∈ treeChans (.node d ct grandkids gsubs) := by
    rw [treeChans_node]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨(e, gc), memGc, rfl⟩)))
  exact List.mem_append_left _ (List.mem_append_right _ (hsub.subset hmemSel))

/-- Forward direction of `childLabels_shift_mem_inv`. -/
lemma childLabels_shift_mem {children : List (Chan × Tree)} {x : Nat}
    (member : Chan.var_Chan x ∈ childLabels children) :
    Chan.var_Chan (x + 1) ∈ childLabels (shiftChildren children) := by
  induction children with
  | nil => simp [childLabels] at member
  | cons head children ih =>
      rcases head with ⟨c, child⟩
      cases c with
      | var_Chan y =>
          rw [shiftChildren]
          simp only [childLabels, List.map_cons, List.mem_cons] at member ⊢
          rcases member with heq | mem
          · left; rw [Chan.var_Chan.injEq] at heq ⊢; omega
          · exact Or.inr (ih mem)

/-- For root children, channels that are not child labels are absent from the context. -/
lemma ChildrenTyped.notLabel_false {Θ children c}
    (typed : ChildrenTyped Θ children) (notLabel : c ∉ childLabels children) :
    CvarPos Θ (chanIndex c) false := by
  refine ChildrenTyped.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun Θ children _ =>
      ∀ c, c ∉ childLabels children → CvarPos Θ (chanIndex c) false)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ => CvarPos.nil)
    (fun _ ih c notLabel => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact CvarPos.none
          | succ x =>
              exact CvarPos.cons (ih (Chan.var_Chan x)
                (fun hmem => notLabel (childLabels_shift_mem hmem))))
    (fun _ _ _ ih c notLabel => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact absurd (by simp [childLabels]) notLabel
          | succ x =>
              refine CvarPos.cons (ih (Chan.var_Chan x) (fun hmem => notLabel ?_))
              exact List.mem_cons_of_mem _ (childLabels_shift_mem hmem))
    (fun _ _ => trivial)
    (fun _ _ => trivial)
    (fun _ _ _ _ => trivial)
    trivial
    (fun _ _ _ _ => trivial)
    typed c notLabel

/-- For node children, channels that are neither a child label nor the reserved parent endpoint
are absent from the context. -/
lemma ChildrenTypedAt.notLabel_false {Θ x r A children c}
    (typed : ChildrenTypedAt Θ x r A children)
    (notLabel : c ∉ childLabels children) (notParent : chanIndex c ≠ x) :
    CvarPos Θ (chanIndex c) false := by
  refine ChildrenTypedAt.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun Θ children _ =>
      ∀ c, c ∉ childLabels children → CvarPos Θ (chanIndex c) false)
    (motive_4 := fun Θ x _ _ children _ =>
      ∀ c, c ∉ childLabels children → chanIndex c ≠ x → CvarPos Θ (chanIndex c) false)
    (motive_5 := fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ => CvarPos.nil)
    (fun _ ih c notLabel => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact CvarPos.none
          | succ x =>
              exact CvarPos.cons (ih (Chan.var_Chan x)
                (fun hmem => notLabel (childLabels_shift_mem hmem))))
    (fun _ _ _ ih c notLabel => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact absurd (by simp [childLabels]) notLabel
          | succ x =>
              refine CvarPos.cons (ih (Chan.var_Chan x) (fun hmem => notLabel ?_))
              exact List.mem_cons_of_mem _ (childLabels_shift_mem hmem))
    (fun _ ih c notLabel notParent => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact absurd rfl notParent
          | succ x =>
              exact CvarPos.cons (ih (Chan.var_Chan x)
                (fun hmem => notLabel (childLabels_shift_mem hmem))))
    (fun _ ih c notLabel notParent => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact CvarPos.none
          | succ x =>
              refine CvarPos.cons (ih (Chan.var_Chan x)
                (fun hmem => notLabel (childLabels_shift_mem hmem)) ?_)
              simp only [chanIndex] at notParent ⊢; omega)
    (fun _ _ _ ih c notLabel notParent => by
      cases c with
      | var_Chan x =>
          cases x with
          | zero => exact absurd (by simp [childLabels]) notLabel
          | succ x =>
              refine CvarPos.cons (ih (Chan.var_Chan x)
                (fun hmem => notLabel (List.mem_cons_of_mem _ (childLabels_shift_mem hmem))) ?_)
              simp only [chanIndex] at notParent ⊢; omega)
    trivial
    (fun _ _ _ _ => trivial)
    typed c notLabel notParent

/-- The split partition is a permutation of the original list (complement first). -/
lemma splitChildrenByTerm_perm (m : Term) :
    ∀ ms : List (Chan × Tree),
      List.Perm ((splitChildrenByTerm m ms).2 ++ (splitChildrenByTerm m ms).1) ms := by
  intro ms
  induction ms with
  | nil =>
      simp [splitChildrenByTerm]
  | cons q rest ih =>
      rcases q with ⟨e, sib⟩
      cases e with
      | var_Chan ex =>
          by_cases hocc : occurs ex m = 0
          · rw [splitChildrenByTerm_cons_pos hocc]
            simp only [List.cons_append]
            exact List.Perm.cons _ ih
          · rw [splitChildrenByTerm_cons_neg hocc]
            refine List.Perm.trans List.perm_middle ?_
            exact List.Perm.cons _ ih

/-- The first split component is a sublist of the original list. -/
lemma splitChildrenByTerm_sublist₁ (m : Term) :
    ∀ ms : List (Chan × Tree), List.Sublist (splitChildrenByTerm m ms).1 ms := by
  intro ms
  induction ms with
  | nil => simp [splitChildrenByTerm]
  | cons q rest ih =>
      rcases q with ⟨e, sib⟩
      cases e with
      | var_Chan ex =>
          by_cases hocc : occurs ex m = 0
          · rw [splitChildrenByTerm_cons_pos hocc]
            exact ih.trans (List.sublist_cons_self _ _)
          · rw [splitChildrenByTerm_cons_neg hocc]
            exact ih.cons₂ _

/-- A selected child node's own endpoint label is fresh among the sibling labels. -/
lemma child_node_label_fresh {children : List (Chan × Tree)} {c d : Chan} {ct : Term}
    {grandkids : List (Chan × Tree)} {gsubs : List Tree}
    (hnodup : ((children.map (fun e => chanIndex e.1)) ++ childInteriors children).Nodup)
    (memChild : (c, .node d ct grandkids gsubs) ∈ children) :
    d ∉ childLabels children := by
  rw [List.nodup_append] at hnodup
  obtain ⟨_, _, hdisj⟩ := hnodup
  set selChild : Tree := .node d ct grandkids gsubs with hsel
  have hsub : List.Sublist (treeChans selChild) (childInteriors children) :=
    treeChans_sublist_childInteriors memChild
  have hmemSel : chanIndex d ∈ treeChans selChild := by
    rw [hsel, treeChans_node]
    exact List.mem_cons_self ..
  have hmemInt : chanIndex d ∈ childInteriors children := hsub.subset hmemSel
  intro hmemLabel
  have hmapMem : chanIndex d ∈ children.map (fun x => chanIndex x.1) := by
    rcases List.mem_map.mp hmemLabel with ⟨edge, hedge, herfl⟩
    exact List.mem_map.mpr ⟨edge, hedge, by rw [herfl]⟩
  exact hdisj _ hmapMem _ hmemInt rfl

/-- In a node, a selected child's own endpoint differs from the node's parent endpoint. -/
lemma child_node_label_ne_parent {parent d : Chan} {mt ct : Term} {c : Chan}
    {children grandkids : List (Chan × Tree)} {gsubs subtrees : List Tree}
    (h : Distinct (.node parent mt children subtrees))
    (memChild : (c, .node d ct grandkids gsubs) ∈ children) :
    chanIndex d ≠ chanIndex parent := by
  unfold Distinct at h
  rw [treeChans_node, List.nodup_cons] at h
  intro heq
  apply h.1
  rw [← heq]
  have hsub := treeChans_sublist_childInteriors memChild
  have hmemSel : chanIndex d ∈ treeChans (.node d ct grandkids gsubs) := by
    rw [treeChans_node]
    exact List.mem_cons_self ..
  exact List.mem_append_left _ (List.mem_append_right _ (hsub.subset hmemSel))

end TLLC.Spawning
