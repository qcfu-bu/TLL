import TLLC.Process.Occurs
import TLLC.Process.Step
import TLLC.Spawning.Distinct
import TLLC.Spawning.Flatten
import TLLC.Spawning.Step

/-!
# Spawning-tree simulation

Lemma 5.86 for the productive spawning-tree step relation. Finished-subtree cleanup is not part of
`Step`; terminality and process structural congruence handle it separately.
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

lemma Step.node_result {parent : Chan} {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {tree : Tree}
    (step : Step (.node parent m children subtrees) tree) :
    ∃ m' children' subtrees', tree = .node parent m' children' subtrees' := by
  cases step <;> repeat first | exact ⟨_, _, _, rfl⟩

lemma Step.node_flattenAt_eq {parent : Chan} {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {tree : Tree}
    (step : Step (.node parent m children subtrees) tree) :
    tree.flattenAt = (parent, tree.flatten) := by
  obtain ⟨m', children', subtrees', rfl⟩ := step.node_result
  simp

lemma dynamic_thunk_csubst {m : Term} (thunk : Thunk m) :
    ∀ σ : Nat → Chan, Thunk (m[σ; Term.var_Term]) := by
  induction thunk using @TLLC.Dynamic.Thunk.rec
    (motive_2 := fun m _ => ∀ σ : Nat → Chan, Val (m[σ; Term.var_Term])) with
  | mlet thunk ih =>
      intro σ
      simpa using Thunk.mlet (ih σ)
  | fork =>
      intro σ
      simpa using (Thunk.fork (A := _))
  | recv =>
      intro σ
      simpa using (Thunk.recv (c := _))
  | appSendIm =>
      intro σ
      simpa using (Thunk.appSendIm (c := _))
  | appSendEx value ih =>
      intro σ
      simpa using Thunk.appSendEx (ih σ)
  | close =>
      intro σ
      simpa using (Thunk.close (c := _))
  | var =>
      simpa using (Val.var (x := _))
  | lam =>
      simpa using (Val.lam (A := _))
  | pairIm value ih =>
      simpa using Val.pairIm (ih _)
  | pairEx valueLeft valueRight ihLeft ihRight =>
      simpa using Val.pairEx (ihLeft _) (ihRight _)
  | one =>
      simpa using Val.one
  | tt =>
      simpa using Val.tt
  | ff =>
      simpa using Val.ff
  | pure value ih =>
      simpa using Val.pure (ih _)
  | chan =>
      simpa using (Val.chan (x := _))
  | send =>
      simpa using (Val.send (c := _))
  | thunk thunk ih =>
      simpa using Val.thunk (ih _)

lemma dynamic_val_csubst {m : Term} (value : Val m) :
    ∀ σ : Nat → Chan, Val (m[σ; Term.var_Term]) := by
  induction value using @TLLC.Dynamic.Val.rec
    (motive_1 := fun m _ => ∀ σ : Nat → Chan, Thunk (m[σ; Term.var_Term])) with
  | mlet thunk ih =>
      simpa using Thunk.mlet (ih _)
  | fork =>
      simpa using (Thunk.fork (A := _))
  | recv =>
      simpa using (Thunk.recv (c := _))
  | appSendIm =>
      simpa using (Thunk.appSendIm (c := _))
  | appSendEx value ih =>
      simpa using Thunk.appSendEx (ih _)
  | close =>
      simpa using (Thunk.close (c := _))
  | var =>
      intro σ
      simpa using (Val.var (x := _))
  | lam =>
      intro σ
      simpa using (Val.lam (A := _))
  | pairIm value ih =>
      intro σ
      simpa using Val.pairIm (ih σ)
  | pairEx valueLeft valueRight ihLeft ihRight =>
      intro σ
      simpa using Val.pairEx (ihLeft σ) (ihRight σ)
  | one =>
      intro σ
      simpa using Val.one
  | tt =>
      intro σ
      simpa using Val.tt
  | ff =>
      intro σ
      simpa using Val.ff
  | pure value ih =>
      intro σ
      simpa using Val.pure (ih σ)
  | chan =>
      intro σ
      simpa using (Val.chan (x := _))
  | send =>
      intro σ
      simpa using (Val.send (c := _))
  | thunk thunk ih =>
      intro σ
      simpa using Val.thunk (ih σ)

lemma dynamic_step_csubst {m n : Term} (step : TLLC.Dynamic.Step m n) :
    ∀ σ : Nat → Chan,
      TLLC.Dynamic.Step (m[σ; Term.var_Term]) (n[σ; Term.var_Term]) := by
  induction step with
  | appL step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.appL (ih σ)
  | appR step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.appR (ih σ)
  | betaIm =>
      rename_i A m n s
      intro σ
      convert
        (TLLC.Dynamic.Step.betaIm (A := A[σ; Term.var_Term])
          (m := m[σ; Term.var_Term]) (n := n[σ; Term.var_Term]) (s := s))
        using 1 <;> asimp
  | betaEx value =>
      rename_i A m v s
      intro σ
      convert
        (TLLC.Dynamic.Step.betaEx (A := A[σ; Term.var_Term])
          (m := m[σ; Term.var_Term]) (v := v[σ; Term.var_Term]) (s := s)
          (dynamic_val_csubst value σ))
        using 1 <;> asimp
  | pairL step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.pairL (ih σ)
  | pairR step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.pairR (ih σ)
  | projM step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.projM (ih σ)
  | projE value =>
      rename_i A m1 m2 n i s
      intro σ
      convert
        (TLLC.Dynamic.Step.projE (A := A[σ; Term.var_Term])
          (m1 := m1[σ; Term.var_Term]) (m2 := m2[σ; Term.var_Term])
          (n := n[σ; Term.var_Term]) (i := i) (s := s)
          (dynamic_val_csubst value σ))
        using 1 <;> asimp
  | fixE =>
      rename_i A m
      intro σ
      convert
        (TLLC.Dynamic.Step.fixE (A := A[σ; Term.var_Term])
          (m := m[σ; Term.var_Term]))
        using 1 <;> asimp
  | iteM step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.iteM (ih σ)
  | iteT =>
      intro σ
      simpa using (TLLC.Dynamic.Step.iteT (A := _) (n1 := _) (n2 := _))
  | iteF =>
      intro σ
      simpa using (TLLC.Dynamic.Step.iteF (A := _) (n1 := _) (n2 := _))
  | pure step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.pure (ih σ)
  | mletL step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.mletL (ih σ)
  | mletE value =>
      rename_i v n
      intro σ
      convert
        (TLLC.Dynamic.Step.mletE (v := v[σ; Term.var_Term])
          (n := n[σ; Term.var_Term]) (dynamic_val_csubst value σ))
        using 1 <;> asimp
  | recv step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.recv (ih σ)
  | send step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.send (ih σ)
  | close step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.close (ih σ)

lemma evalctx_cren_comp (M : EvalCtx) (ξ ζ : Nat → Nat) :
    (M.cren ξ).cren ζ = M.cren (funcomp ζ ξ) := by
  induction M with
  | hole =>
      rfl
  | bnd M n ih =>
      simp [EvalCtx.cren, ih]
      asimp

lemma evalctx_csubst (σ : Nat → Chan) (M : EvalCtx) (m : Term) :
    (M.eval m)[σ; Term.var_Term] =
      (M.cren (TLLC.Static.csubst_ren σ)).eval (m[σ; Term.var_Term]) := by
  rw [← TLLC.Static.csubst_cren]
  rw [evalctx_cren]
  rw [TLLC.Static.csubst_cren]

lemma bindEndpointAt_self_term {c : Chan} {σ : Nat → Chan} :
    (Term.chan c)[bindEndpointAt 0 c; Term.var_Term][up_Chan_Chan σ; Term.var_Term] =
      TLLC.Process.cvar 0 := by
  cases c with
  | var_Chan x =>
      asimp
      unfold bindEndpointAt chanIndex
      simp
      asimp

lemma congrTerm_csubst_of_eqv {r : Rlv} {m : Term} {i : Nat} {σ τ : Nat → Chan}
    (eqv : ∀ x, x ≠ i → σ x = τ x)
    (unused : r = .ex → occurs i m = 0) :
    TLLC.Process.CongrTerm r (m[σ; Term.var_Term]) (m[τ; Term.var_Term]) := by
  induction m generalizing r i σ τ with
  | var_Term x =>
      asimp
      exact TLLC.Process.CongrTerm.var
  | srt s =>
      asimp
      exact TLLC.Process.CongrTerm.srt
  | pi A B r2 s ihA ihB =>
      asimp
      exact TLLC.Process.CongrTerm.pi (ihA (r := .im) eqv (by intro h; cases h))
        (ihB (r := .im) eqv (by intro h; cases h))
  | lam A m r2 s ihA ihm =>
      asimp
      exact TLLC.Process.CongrTerm.lam (ihA (r := .im) eqv (by intro h; cases h))
        (ihm (r := r) eqv (by
          intro hr
          exact unused hr))
  | app m n r2 ihm ihn =>
      asimp
      refine TLLC.Process.CongrTerm.app
        (ihm (r := r) eqv ?_)
        (ihn (r := TLLC.Process.under r r2) eqv ?_)
      · intro hr
        cases r2 with
        | im =>
            simpa [occurs] using unused hr
        | ex =>
            have h := unused hr
            simpa [occurs] using Nat.eq_zero_of_add_eq_zero_right h
      · intro hr
        cases r <;> cases r2
        · cases hr
        · cases hr
        · cases hr
        · have h := unused rfl
          simpa [occurs] using Nat.eq_zero_of_add_eq_zero_left h
  | sig A B r2 s ihA ihB =>
      asimp
      exact TLLC.Process.CongrTerm.sig (ihA (r := .im) eqv (by intro h; cases h))
        (ihB (r := .im) eqv (by intro h; cases h))
  | pair m n r2 s ihm ihn =>
      asimp
      refine TLLC.Process.CongrTerm.pair
        (ihm (r := TLLC.Process.under r r2) eqv ?_)
        (ihn (r := r) eqv ?_)
      · intro hr
        cases r <;> cases r2
        · cases hr
        · cases hr
        · cases hr
        · have h := unused rfl
          simpa [occurs] using Nat.eq_zero_of_add_eq_zero_right h
      · intro hr
        cases r2 with
        | im =>
            simpa [occurs] using unused hr
        | ex =>
            have h := unused hr
            simpa [occurs] using Nat.eq_zero_of_add_eq_zero_left h
  | proj C m n ihC ihm ihn =>
      asimp
      refine TLLC.Process.CongrTerm.proj (ihC (r := .im) eqv (by intro h; cases h))
        (ihm (r := r) eqv ?_) (ihn (r := r) eqv ?_)
      · intro hr
        have h := unused hr
        simpa [occurs] using Nat.eq_zero_of_add_eq_zero_right h
      · intro hr
        have h := unused hr
        simpa [occurs] using Nat.eq_zero_of_add_eq_zero_left h
  | fix A m ihA ihm =>
      asimp
      exact TLLC.Process.CongrTerm.fix (ihA (r := .im) eqv (by intro h; cases h))
        (ihm (r := r) eqv (by intro hr; exact unused hr))
  | unit =>
      asimp
      exact TLLC.Process.CongrTerm.unit
  | one =>
      asimp
      exact TLLC.Process.CongrTerm.one
  | bool =>
      asimp
      exact TLLC.Process.CongrTerm.bool
  | tt =>
      asimp
      exact TLLC.Process.CongrTerm.tt
  | ff =>
      asimp
      exact TLLC.Process.CongrTerm.ff
  | ite A m n1 n2 ihA ihm ihn1 ihn2 =>
      asimp
      refine TLLC.Process.CongrTerm.ite (ihA (r := .im) eqv (by intro h; cases h))
        (ihm (r := r) eqv ?_) (ihn1 (r := r) eqv ?_) (ihn2 (r := r) eqv ?_)
      · intro hr
        have h := unused hr
        simpa [occurs] using Nat.eq_zero_of_add_eq_zero_right h
      · intro hr
        have h := unused hr
        have hmax : max (occurs i n1) (occurs i n2) = 0 :=
          Nat.eq_zero_of_add_eq_zero_left h
        omega
      · intro hr
        have h := unused hr
        have hmax : max (occurs i n1) (occurs i n2) = 0 :=
          Nat.eq_zero_of_add_eq_zero_left h
        omega
  | M A ihA =>
      asimp
      exact TLLC.Process.CongrTerm.M (ihA (r := .im) eqv (by intro h; cases h))
  | pure m ihm =>
      asimp
      exact TLLC.Process.CongrTerm.pure
        (ihm (r := r) eqv (by intro hr; exact unused hr))
  | mlet m n ihm ihn =>
      asimp
      refine TLLC.Process.CongrTerm.mlet (ihm (r := r) eqv ?_) (ihn (r := r) eqv ?_)
      · intro hr
        have h := unused hr
        simpa [occurs] using Nat.eq_zero_of_add_eq_zero_right h
      · intro hr
        have h := unused hr
        simpa [occurs] using Nat.eq_zero_of_add_eq_zero_left h
  | proto =>
      asimp
      exact TLLC.Process.CongrTerm.proto
  | stop =>
      asimp
      exact TLLC.Process.CongrTerm.stop
  | act b A B r2 ihA ihB =>
      asimp
      exact TLLC.Process.CongrTerm.act (ihA (r := .im) eqv (by intro h; cases h))
        (ihB (r := .im) eqv (by intro h; cases h))
  | ch b A ihA =>
      asimp
      exact TLLC.Process.CongrTerm.ch (ihA (r := .im) eqv (by intro h; cases h))
  | chan c =>
      cases r with
      | im =>
          asimp
          exact TLLC.Process.CongrTerm.chan_im
      | ex =>
          cases c with
          | var_Chan x =>
              have hx : x ≠ i := by
                intro hxi
                have hocc := unused rfl
                simp [occurs, hxi] at hocc
              asimp
              rw [eqv x hx]
              exact TLLC.Process.CongrTerm.chan_ex
  | fork A m ihA ihm =>
      asimp
      exact TLLC.Process.CongrTerm.fork (ihA (r := .im) eqv (by intro h; cases h))
        (ihm (r := r) eqv (by intro hr; exact unused hr))
  | recv m r2 ihm =>
      asimp
      exact TLLC.Process.CongrTerm.recv
        (ihm (r := r) eqv (by intro hr; exact unused hr))
  | send m r2 ihm =>
      asimp
      exact TLLC.Process.CongrTerm.send
        (ihm (r := r) eqv (by intro hr; exact unused hr))
  | close b m ihm =>
      asimp
      exact TLLC.Process.CongrTerm.close
        (ihm (r := r) eqv (by intro hr; exact unused hr))
  | box =>
      asimp
      exact TLLC.Process.CongrTerm.box

lemma dynamic_val_crename {m : Term} (value : Val m) :
    ∀ ξ : Nat → Nat, Val (m⟨ξ; (id : Nat → Nat)⟩) := by
  intro ξ
  have renamed := dynamic_val_csubst value (fun x => Chan.var_Chan (ξ x))
  convert renamed using 1
  rw [← TLLC.Static.csubst_cren]
  congr

lemma dynamic_step_crename {m n : Term} (step : TLLC.Dynamic.Step m n) :
    ∀ ξ : Nat → Nat,
      TLLC.Dynamic.Step (m⟨ξ; (id : Nat → Nat)⟩) (n⟨ξ; (id : Nat → Nat)⟩) := by
  intro ξ
  have renamed := dynamic_step_csubst step (fun x => Chan.var_Chan (ξ x))
  convert renamed using 1
  · rw [← TLLC.Static.csubst_cren]
    congr
  · rw [← TLLC.Static.csubst_cren]
    congr

lemma process_csubst_cren (p : Proc) (σ : Nat → Chan) :
    p⟨TLLC.Static.csubst_ren σ; (id : Nat → Nat)⟩ = p[σ; Term.var_Term] := by
  induction p generalizing σ with
  | tm m =>
      asimp
      rw [TLLC.Static.csubst_cren m σ]
  | par p q ihp ihq =>
      asimp
      rw [ihp σ, ihq σ]
  | nu p ih =>
      asimp
      have hren :
          (var_zero .: TLLC.Static.csubst_ren σ >> ↑) =
            TLLC.Static.csubst_ren (up_Chan_Chan σ) := by
        funext x
        cases x <;> rfl
      rw [hren]
      rw [ih (up_Chan_Chan σ)]
      asimp

lemma process_congr0_crename {p q : Proc} (congr : TLLC.Process.CongrProc p q) :
    ∀ ξ : Nat → Nat,
      TLLC.Process.CongrProc (p⟨ξ; (id : Nat → Nat)⟩) (q⟨ξ; (id : Nat → Nat)⟩) := by
  induction congr with
  | tm e =>
      intro ξ
      simpa using TLLC.Process.CongrProc.tm (TLLC.Process.CongrTerm.crename e ξ)
  | par_sym =>
      intro ξ
      simpa using TLLC.Process.CongrProc.par_sym
  | assoc =>
      intro ξ
      simpa using TLLC.Process.CongrProc.assoc
  | scope =>
      rename_i p q
      intro ξ
      convert (TLLC.Process.CongrProc.scope
        (p := p⟨upRen_Chan_Chan ξ; (id : Nat → Nat)⟩)
        (q := q⟨ξ; (id : Nat → Nat)⟩)) using 1
      · asimp
        congr 3
  | exch =>
      rename_i p
      intro ξ
      convert (TLLC.Process.CongrProc.exch
        (p := p⟨upRen_Chan_Chan (upRen_Chan_Chan ξ); (id : Nat → Nat)⟩)) using 1
        ; asimp
      · congr 2
  | par cp cq ihp ihq =>
      intro ξ
      simpa using TLLC.Process.CongrProc.par (ihp ξ) (ihq ξ)
  | res cp ihp =>
      intro ξ
      simpa using TLLC.Process.CongrProc.res (ihp (upRen_Chan_Chan ξ))
  | «end» =>
      intro ξ
      simpa using TLLC.Process.CongrProc.end

lemma process_congr_crename {p q : Proc} (congr : TLLC.Process.Congruence p q) :
    ∀ ξ : Nat → Nat,
      TLLC.Process.Congruence (p⟨ξ; (id : Nat → Nat)⟩) (q⟨ξ; (id : Nat → Nat)⟩) := by
  intro ξ
  induction congr with
  | refl =>
      exact TLLC.ARS.Conv.refl
  | tail _ step ih =>
      exact TLLC.ARS.Conv.tail ih (process_congr0_crename step ξ)
  | taili _ step ih =>
      exact TLLC.ARS.Conv.taili ih (process_congr0_crename step ξ)

lemma process_congr_csubst {p q : Proc} (congr : TLLC.Process.Congruence p q) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Congruence (p[σ; Term.var_Term]) (q[σ; Term.var_Term]) := by
  intro σ
  have renamed := process_congr_crename congr (TLLC.Static.csubst_ren σ)
  rw [process_csubst_cren p σ] at renamed
  rw [process_csubst_cren q σ] at renamed
  exact renamed

lemma process_congr0_parallel_left {p q r : Proc}
    (congr : TLLC.Process.CongrProc p q) :
    TLLC.Process.Congruence (.par p r) (.par q r) := by
  exact ARS.conv_trans
    (ARS.conv1i (TLLC.Process.CongrProc.end (p := .par p r)))
    (ARS.conv_trans
      (ARS.conv1i (TLLC.Process.CongrProc.assoc (o := p) (p := r) (q := .tm (.pure .one))))
      (ARS.conv1 (TLLC.Process.CongrProc.par congr (TLLC.Process.CongrProc.end (p := r)))))

lemma process_congr_parallel_left {p q r : Proc}
    (congr : TLLC.Process.Congruence p q) :
    TLLC.Process.Congruence (.par p r) (.par q r) := by
  induction congr with
  | refl =>
      exact ARS.Conv.refl
  | tail _ step ih =>
      exact ARS.conv_trans ih (process_congr0_parallel_left (r := r) step)
  | taili _ step ih =>
      exact ARS.conv_trans ih (ARS.conv_sym (process_congr0_parallel_left (r := r) step))

lemma process_congr_parallel_right {p q r : Proc}
    (congr : TLLC.Process.Congruence p q) :
    TLLC.Process.Congruence (.par r p) (.par r q) := by
  exact ARS.conv_trans
    (ARS.conv1 TLLC.Process.CongrProc.par_sym)
    (ARS.conv_trans (process_congr_parallel_left (r := r) congr)
      (ARS.conv1 TLLC.Process.CongrProc.par_sym))

lemma process_congr0_res {p q : Proc}
    (congr : TLLC.Process.CongrProc p q) :
    TLLC.Process.Congruence (.nu p) (.nu q) := by
  exact ARS.conv1 (TLLC.Process.CongrProc.res congr)

lemma process_congr_res {p q : Proc}
    (congr : TLLC.Process.Congruence p q) :
    TLLC.Process.Congruence (.nu p) (.nu q) := by
  induction congr with
  | refl =>
      exact ARS.Conv.refl
  | tail _ step ih =>
      exact ARS.conv_trans ih (process_congr0_res step)
  | taili _ step ih =>
      exact ARS.conv_trans ih (ARS.conv_sym (process_congr0_res step))

lemma process_congr_csubst_of_eqv {p : Proc} {i : Nat} {σ τ : Nat → Chan}
    (eqv : ∀ x, x ≠ i → σ x = τ x)
    (unused : TLLC.Process.procOccurs i p = 0) :
    TLLC.Process.Congruence (p[σ; Term.var_Term]) (p[τ; Term.var_Term]) := by
  induction p generalizing i σ τ with
  | tm m =>
      asimp
      exact ARS.conv1 (TLLC.Process.CongrProc.tm
        (congrTerm_csubst_of_eqv (r := .ex) eqv (by intro _; exact unused)))
  | par p q ihp ihq =>
      asimp at unused ⊢
      have hp : TLLC.Process.procOccurs i p = 0 :=
        Nat.eq_zero_of_add_eq_zero_right unused
      have hq : TLLC.Process.procOccurs i q = 0 :=
        Nat.eq_zero_of_add_eq_zero_left unused
      exact ARS.conv_trans
        (process_congr_parallel_left (r := q[σ; Term.var_Term]) (ihp eqv hp))
        (process_congr_parallel_right (r := p[τ; Term.var_Term]) (ihq eqv hq))
  | nu p ih =>
      asimp at unused ⊢
      have eqvUp : ∀ x, x ≠ i + 1 → up_Chan_Chan σ x = up_Chan_Chan τ x := by
        intro x hx
        cases x with
        | zero =>
            rfl
        | succ x =>
            have hx' : x ≠ i := by
              intro h
              apply hx
              omega
            simpa [funcomp] using congrArg (ren_Chan Nat.succ) (eqv x hx')
      exact process_congr_res (ih eqvUp unused)
/-- Channel substitutions that agree on every channel that explicitly occurs in `m` induce a term
congruence (implicit channels are erased). The "occurs"-dual of `congrTerm_csubst_of_eqv`. -/
lemma congrTerm_csubst_of_occurs {r : Rlv} {m : Term} {σ τ : Nat → Chan}
    (occ : r = .ex → ∀ k, occurs k m ≠ 0 → σ k = τ k) :
    TLLC.Process.CongrTerm r (m[σ; Term.var_Term]) (m[τ; Term.var_Term]) := by
  induction m generalizing r σ τ with
  | var_Term x => asimp; exact TLLC.Process.CongrTerm.var
  | srt s => asimp; exact TLLC.Process.CongrTerm.srt
  | pi A B r2 s ihA ihB =>
      asimp
      exact TLLC.Process.CongrTerm.pi (ihA (r := .im) (by intro h; cases h))
        (ihB (r := .im) (by intro h; cases h))
  | lam A m r2 s ihA ihm =>
      asimp
      exact TLLC.Process.CongrTerm.lam (ihA (r := .im) (by intro h; cases h))
        (ihm (r := r) (fun hr k hk => occ hr k (by simpa [occurs] using hk)))
  | app m n r2 ihm ihn =>
      asimp
      refine TLLC.Process.CongrTerm.app (ihm (r := r) ?_)
        (ihn (r := TLLC.Process.under r r2) ?_)
      · intro hr k hk
        exact occ hr k (by cases r2 <;> simp [occurs] <;> omega)
      · intro hr k hk
        cases r2 with
        | im => cases r <;> simp [TLLC.Process.under] at hr
        | ex => exact occ (by cases r <;> simp_all [TLLC.Process.under]) k (by simp [occurs]; omega)
  | sig A B r2 s ihA ihB =>
      asimp
      exact TLLC.Process.CongrTerm.sig (ihA (r := .im) (by intro h; cases h))
        (ihB (r := .im) (by intro h; cases h))
  | pair m n r2 s ihm ihn =>
      asimp
      refine TLLC.Process.CongrTerm.pair (ihm (r := TLLC.Process.under r r2) ?_)
        (ihn (r := r) ?_)
      · intro hr k hk
        cases r2 with
        | im => cases r <;> simp [TLLC.Process.under] at hr
        | ex => exact occ (by cases r <;> simp_all [TLLC.Process.under]) k (by simp [occurs]; omega)
      · intro hr k hk
        exact occ hr k (by cases r2 <;> simp [occurs] <;> omega)
  | proj C m n ihC ihm ihn =>
      asimp
      refine TLLC.Process.CongrTerm.proj (ihC (r := .im) (by intro h; cases h))
        (ihm (r := r) ?_) (ihn (r := r) ?_)
      · intro hr k hk; exact occ hr k (by simp [occurs]; omega)
      · intro hr k hk; exact occ hr k (by simp [occurs]; omega)
  | fix A m ihA ihm =>
      asimp
      exact TLLC.Process.CongrTerm.fix (ihA (r := .im) (by intro h; cases h))
        (ihm (r := r) (fun hr k hk => occ hr k (by simpa [occurs] using hk)))
  | unit => asimp; exact TLLC.Process.CongrTerm.unit
  | one => asimp; exact TLLC.Process.CongrTerm.one
  | bool => asimp; exact TLLC.Process.CongrTerm.bool
  | tt => asimp; exact TLLC.Process.CongrTerm.tt
  | ff => asimp; exact TLLC.Process.CongrTerm.ff
  | ite A m n1 n2 ihA ihm ihn1 ihn2 =>
      asimp
      refine TLLC.Process.CongrTerm.ite (ihA (r := .im) (by intro h; cases h))
        (ihm (r := r) ?_) (ihn1 (r := r) ?_) (ihn2 (r := r) ?_)
      · intro hr k hk; exact occ hr k (by simp [occurs]; omega)
      · intro hr k hk; exact occ hr k (by simp [occurs]; omega)
      · intro hr k hk; exact occ hr k (by simp [occurs]; omega)
  | M A ihA => asimp; exact TLLC.Process.CongrTerm.M (ihA (r := .im) (by intro h; cases h))
  | pure m ihm =>
      asimp
      exact TLLC.Process.CongrTerm.pure
        (ihm (r := r) (fun hr k hk => occ hr k (by simpa [occurs] using hk)))
  | mlet m n ihm ihn =>
      asimp
      refine TLLC.Process.CongrTerm.mlet (ihm (r := r) ?_) (ihn (r := r) ?_)
      · intro hr k hk; exact occ hr k (by simp [occurs]; omega)
      · intro hr k hk; exact occ hr k (by simp [occurs]; omega)
  | proto => asimp; exact TLLC.Process.CongrTerm.proto
  | stop => asimp; exact TLLC.Process.CongrTerm.stop
  | act b A B r2 ihA ihB =>
      asimp
      exact TLLC.Process.CongrTerm.act (ihA (r := .im) (by intro h; cases h))
        (ihB (r := .im) (by intro h; cases h))
  | ch b A ihA =>
      asimp; exact TLLC.Process.CongrTerm.ch (ihA (r := .im) (by intro h; cases h))
  | chan c =>
      cases r with
      | im => asimp; exact TLLC.Process.CongrTerm.chan_im
      | ex =>
          cases c with
          | var_Chan x =>
              asimp
              rw [occ rfl x (by simp [occurs])]
              exact TLLC.Process.CongrTerm.chan_ex
  | fork A m ihA ihm =>
      asimp
      exact TLLC.Process.CongrTerm.fork (ihA (r := .im) (by intro h; cases h))
        (ihm (r := r) (fun hr k hk => occ hr k (by simpa [occurs] using hk)))
  | recv m r2 ihm =>
      asimp
      exact TLLC.Process.CongrTerm.recv
        (ihm (r := r) (fun hr k hk => occ hr k (by simpa [occurs] using hk)))
  | send m r2 ihm =>
      asimp
      exact TLLC.Process.CongrTerm.send
        (ihm (r := r) (fun hr k hk => occ hr k (by simpa [occurs] using hk)))
  | close b m ihm =>
      asimp
      exact TLLC.Process.CongrTerm.close
        (ihm (r := r) (fun hr k hk => occ hr k (by simpa [occurs] using hk)))
  | box => asimp; exact TLLC.Process.CongrTerm.box

/-- Process analogue of `congrTerm_csubst_of_occurs`. -/
lemma process_congr_csubst_of_occurs {p : Proc} {σ τ : Nat → Chan}
    (occ : ∀ k, TLLC.Process.procOccurs k p ≠ 0 → σ k = τ k) :
    TLLC.Process.Congruence (p[σ; Term.var_Term]) (p[τ; Term.var_Term]) := by
  induction p generalizing σ τ with
  | tm m =>
      asimp
      exact ARS.conv1 (TLLC.Process.CongrProc.tm
        (congrTerm_csubst_of_occurs (r := .ex) (fun _ k hk => occ k hk)))
  | par p q ihp ihq =>
      asimp
      refine ARS.conv_trans
        (process_congr_parallel_left (r := q[σ; Term.var_Term]) (ihp ?_))
        (process_congr_parallel_right (r := p[τ; Term.var_Term]) (ihq ?_))
      · intro k hk; exact occ k (by simp [TLLC.Process.procOccurs]; omega)
      · intro k hk; exact occ k (by simp [TLLC.Process.procOccurs]; omega)
  | nu p ih =>
      asimp
      apply process_congr_res
      apply ih
      intro k hk
      cases k with
      | zero => rfl
      | succ k =>
          have := occ k (by simpa [TLLC.Process.procOccurs] using hk)
          simpa [funcomp] using congrArg (ren_Chan Nat.succ) this


lemma occurs_csubst_zero_of_all {m : Term} {σ : Nat → Chan} {i : Nat}
    (zero : ∀ j, occurs j m = 0) :
    occurs i (m[σ; Term.var_Term]) = 0 := by
  induction m generalizing i σ with
  | var_Term x =>
      rfl
  | srt s =>
      rfl
  | pi A B r s ihA ihB =>
      rfl
  | lam A m r s ihA ihm =>
      asimp
      exact ihm (fun j => zero j)
  | app m n r ihm ihn =>
      cases r with
      | im =>
          asimp
          exact ihm (fun j => zero j)
      | ex =>
          asimp
          have zm : ∀ j, occurs j m = 0 := by
            intro j
            exact Nat.eq_zero_of_add_eq_zero_right (zero j)
          have zn : ∀ j, occurs j n = 0 := by
            intro j
            exact Nat.eq_zero_of_add_eq_zero_left (zero j)
          simp [occurs, ihm zm, ihn zn]
  | sig A B r s ihA ihB =>
      rfl
  | pair m n r s ihm ihn =>
      cases r with
      | im =>
          asimp
          exact ihn (fun j => zero j)
      | ex =>
          asimp
          have zm : ∀ j, occurs j m = 0 := by
            intro j
            exact Nat.eq_zero_of_add_eq_zero_right (zero j)
          have zn : ∀ j, occurs j n = 0 := by
            intro j
            exact Nat.eq_zero_of_add_eq_zero_left (zero j)
          simp [occurs, ihm zm, ihn zn]
  | proj C m n ihC ihm ihn =>
      asimp
      have zm : ∀ j, occurs j m = 0 := by
        intro j
        exact Nat.eq_zero_of_add_eq_zero_right (zero j)
      have zn : ∀ j, occurs j n = 0 := by
        intro j
        exact Nat.eq_zero_of_add_eq_zero_left (zero j)
      simp [occurs, ihm zm, ihn zn]
  | fix A m ihA ihm =>
      asimp
      exact ihm (fun j => zero j)
  | unit =>
      rfl
  | one =>
      rfl
  | bool =>
      rfl
  | tt =>
      rfl
  | ff =>
      rfl
  | ite A m n1 n2 ihA ihm ihn1 ihn2 =>
      asimp
      have zm : ∀ j, occurs j m = 0 := by
        intro j
        exact Nat.eq_zero_of_add_eq_zero_right (zero j)
      have zmax : ∀ j, max (occurs j n1) (occurs j n2) = 0 := by
        intro j
        exact Nat.eq_zero_of_add_eq_zero_left (zero j)
      have zn1 : ∀ j, occurs j n1 = 0 := by
        intro j
        have h := zmax j
        omega
      have zn2 : ∀ j, occurs j n2 = 0 := by
        intro j
        have h := zmax j
        omega
      simp [occurs, ihm zm, ihn1 zn1, ihn2 zn2]
  | M A ihA =>
      rfl
  | pure m ihm =>
      asimp
      exact ihm (fun j => zero j)
  | mlet m n ihm ihn =>
      asimp
      have zm : ∀ j, occurs j m = 0 := by
        intro j
        exact Nat.eq_zero_of_add_eq_zero_right (zero j)
      have zn : ∀ j, occurs j n = 0 := by
        intro j
        exact Nat.eq_zero_of_add_eq_zero_left (zero j)
      simp [occurs, ihm zm, ihn zn]
  | proto =>
      rfl
  | stop =>
      rfl
  | act b A B r ihA ihB =>
      rfl
  | ch b A ihA =>
      rfl
  | chan c =>
      cases c with
      | var_Chan x =>
          have h := zero x
          simp [occurs] at h
  | fork A m ihA ihm =>
      asimp
      exact ihm (fun j => zero j)
  | recv m r ihm =>
      asimp
      exact ihm (fun j => zero j)
  | send m r ihm =>
      asimp
      exact ihm (fun j => zero j)
  | close b m ihm =>
      asimp
      exact ihm (fun j => zero j)
  | box =>
      rfl

lemma congrTerm_consume_endpoint {r : Rlv} {m : Term} {c : Chan} {σ : Nat → Chan}
    (unused : r = .ex → occurs (chanIndex c) m = 0) :
    TLLC.Process.CongrTerm r
      (((m[bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term])⟨((· - 1) : Nat → Nat);
        (id : Nat → Nat)⟩)
      (m[σ; Term.var_Term]) := by
  cases c with
  | var_Chan x =>
      convert (congrTerm_csubst_of_eqv (r := r) (m := m) (i := x)
        (σ := fun y => ((bindEndpointAt 0 (Chan.var_Chan x) y)[up_Chan_Chan σ])⟨((· - 1) : Nat → Nat)⟩)
        (τ := σ)
        (by
          intro y hy
          unfold bindEndpointAt chanIndex
          simp [hy]
          cases hσ : σ y with
          | var_Chan z =>
              asimp
              rw [hσ]
              asimp
              change Chan.var_Chan ((z + 1) - 1) = Chan.var_Chan z
              congr)
        (by simpa using unused)) using 1
      asimp

lemma evalctx_consume_endpoint_pure_one {M : EvalCtx} {c : Chan} {σ : Nat → Chan}
    (unused : occurs (chanIndex c) (M.eval (.pure .one)) = 0) :
    TLLC.Process.CongrTerm .ex
      ((((M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 c))).cren
        (TLLC.Static.csubst_ren (up_Chan_Chan σ))).cren ((· - 1) : Nat → Nat)).eval
          (.pure .one))
      ((M.eval (.pure .one))[σ; Term.var_Term]) := by
  convert congrTerm_consume_endpoint (r := .ex) (m := M.eval (.pure .one)) (c := c) (σ := σ)
    (by intro _; exact unused) using 1
  · rw [evalctx_csubst]
    rw [evalctx_csubst]
    asimp
    exact (evalctx_cren ((· - 1) : Nat → Nat)
      ((M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 c))).cren
        (TLLC.Static.csubst_ren (up_Chan_Chan σ))) (.pure .one)).symm

lemma process_congr_pred_succ_of_unused {p : Proc}
    (unused : TLLC.Process.procOccurs 0 p = 0) :
    TLLC.Process.Congruence p
      (p⟨(fun x => (x - 1) + 1); (id : Nat → Nat)⟩) := by
  have congr := process_congr_csubst_of_eqv (p := p) (i := 0)
    (σ := Chan.var_Chan) (τ := fun x => Chan.var_Chan ((x - 1) + 1))
    (by
      intro x hx
      cases x with
      | zero =>
          contradiction
      | succ x =>
          simp)
    unused
  convert congr using 1
  · asimp
  · rw [← process_csubst_cren]
    congr

lemma process_congr_scope_out_right {p q : Proc}
    (unused : TLLC.Process.procOccurs 0 q = 0) :
    TLLC.Process.Congruence (.nu (.par p q))
      (.par (.nu p) (q⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩)) := by
  have qCongr := process_congr_pred_succ_of_unused (p := q) unused
  have inside :
      TLLC.Process.Congruence (.nu (.par p q))
        (.nu (.par p
          ((q⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨((· + 1) : Nat → Nat);
            (id : Nat → Nat)⟩))) := by
    apply process_congr_res
    apply process_congr_parallel_right
    convert qCongr using 1
    asimp
  exact ARS.conv_trans inside (ARS.conv1i TLLC.Process.CongrProc.scope)

lemma process_congr_scope_out_left {p q : Proc}
    (unused : TLLC.Process.procOccurs 0 p = 0) :
    TLLC.Process.Congruence (.nu (.par p q))
      (.par (p⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩) (.nu q)) := by
  exact ARS.conv_trans
    (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym))
    (ARS.conv_trans
      (process_congr_scope_out_right (p := q) (q := p) unused)
      (ARS.conv1 TLLC.Process.CongrProc.par_sym))

lemma process_step_scope_unused_right {p p' q : Proc}
    (unused : TLLC.Process.procOccurs 0 q = 0)
    (step : TLLC.Process.Step (.nu p) (.nu p')) :
    TLLC.Process.Step (.nu (.par p q)) (.nu (.par p' q)) := by
  exact TLLC.Process.Step.congr
    (process_congr_scope_out_right (p := p) (q := q) unused)
    (TLLC.Process.Step.congr
      (ARS.conv1 TLLC.Process.CongrProc.par_sym)
      (TLLC.Process.Step.par
        (o := q⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩) step)
      (ARS.conv1 TLLC.Process.CongrProc.par_sym))
    (ARS.conv_sym (process_congr_scope_out_right (p := p') (q := q) unused))

lemma process_step_scope_unused_left {p q q' : Proc}
    (unused : TLLC.Process.procOccurs 0 p = 0)
    (step : TLLC.Process.Step (.nu q) (.nu q')) :
    TLLC.Process.Step (.nu (.par p q)) (.nu (.par p q')) := by
  exact TLLC.Process.Step.congr
    (process_congr_scope_out_left (p := p) (q := q) unused)
    (TLLC.Process.Step.par
      (o := p⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩) step)
    (ARS.conv_sym (process_congr_scope_out_left (p := p) (q := q') unused))

lemma process_step_scope_remove_unused_right {p p' q : Proc}
    (unused : TLLC.Process.procOccurs 0 q = 0)
    (step : TLLC.Process.Step (.nu p) p') :
    TLLC.Process.Step (.nu (.par p q))
      (.par p' (q⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩)) := by
  exact TLLC.Process.Step.congr
    (process_congr_scope_out_right (p := p) (q := q) unused)
    (TLLC.Process.Step.congr
      (ARS.conv1 TLLC.Process.CongrProc.par_sym)
      (TLLC.Process.Step.par
        (o := q⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩) step)
      (ARS.conv1 TLLC.Process.CongrProc.par_sym))
    ARS.Conv.refl

lemma Typed.flatten_occurs0 {tree : Tree} (typed : Typed tree) (i : Nat) :
    TLLC.Process.procOccurs i tree.flatten = 0 := by
  have ty := typed.flatten_typed
  exact ty.procOccurs0 (by cases i <;> rfl)

lemma TypedAt.flattenAt_occurs_succ {r A tree} (tyA : ([] : Static.Ctx) ⊢ A : .proto)
    (typed : TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) tree) (i : Nat) :
    TLLC.Process.procOccurs (i + 1)
      ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term]) = 0 := by
  have ty := typed.flattenAt_typed tyA
  exact ty.procOccurs0 (by rfl)

lemma SubtreesTyped.flattenSubtrees_occurs0 {trees : List Tree} {p : Proc} {i : Nat}
    (typed : SubtreesTyped trees) (member : p ∈ flattenSubtrees trees) :
    TLLC.Process.procOccurs i p = 0 := by
  induction trees generalizing p with
  | nil =>
      simp at member
  | cons tree trees ih =>
      cases typed with
      | cons typedTree typedTrees =>
          simp at member
          rcases member with h | h
          · subst h
            exact typedTree.flatten_occurs0 i
          · exact ih typedTrees h

lemma procOccurs_parAll_zero {body : Proc} {processes : List Proc} {i : Nat}
    (bodyZero : TLLC.Process.procOccurs i body = 0)
    (processesZero : ∀ p, p ∈ processes → TLLC.Process.procOccurs i p = 0) :
    TLLC.Process.procOccurs i (parAll body processes) = 0 := by
  induction processes generalizing body with
  | nil =>
      simpa [parAll] using bodyZero
  | cons p processes ih =>
      have pZero : TLLC.Process.procOccurs i p = 0 := processesZero p (by simp)
      have restZero : ∀ q, q ∈ processes → TLLC.Process.procOccurs i q = 0 := by
        intro q hq
        exact processesZero q (by simp [hq])
      exact ih (body := .par body p) (by simp [TLLC.Process.procOccurs, bodyZero, pZero])
        restZero

lemma process_step_scope_parAll_right {p p' : Proc} (processes : List Proc)
    (processesZero : ∀ q, q ∈ processes → TLLC.Process.procOccurs 0 q = 0)
    (step : TLLC.Process.Step (.nu p) (.nu p')) :
    TLLC.Process.Step (.nu (parAll p processes)) (.nu (parAll p' processes)) := by
  induction processes generalizing p p' with
  | nil =>
      simpa [parAll] using step
  | cons q processes ih =>
      have qZero : TLLC.Process.procOccurs 0 q = 0 := processesZero q (by simp)
      have restZero : ∀ r, r ∈ processes → TLLC.Process.procOccurs 0 r = 0 := by
        intro r hr
        exact processesZero r (by simp [hr])
      have stepQ : TLLC.Process.Step (.nu (.par p q)) (.nu (.par p' q)) :=
        process_step_scope_unused_right qZero step
      simpa [parAll] using ih restZero stepQ

lemma process_step_scope_remove_parAll_right {p p' : Proc} (processes : List Proc)
    (processesZero : ∀ q, q ∈ processes → TLLC.Process.procOccurs 0 q = 0)
    (step : TLLC.Process.Step (.nu p) p') :
    TLLC.Process.Step (.nu (parAll p processes))
      (parAll p' (processes.map
        (fun q => q⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩))) := by
  induction processes generalizing p p' with
  | nil =>
      simpa [parAll] using step
  | cons q processes ih =>
      have qZero : TLLC.Process.procOccurs 0 q = 0 := processesZero q (by simp)
      have restZero : ∀ r, r ∈ processes → TLLC.Process.procOccurs 0 r = 0 := by
        intro r hr
        exact processesZero r (by simp [hr])
      have stepQ : TLLC.Process.Step (.nu (.par p q))
          (.par p' (q⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩)) :=
        process_step_scope_remove_unused_right qZero step
      simpa [parAll] using ih restZero stepQ

lemma process_step_crename_zero {p q : Proc} (step : TLLC.Process.Step p q) :
    ∀ ξ : Nat → Nat, ξ 0 = 0 →
      TLLC.Process.Step (p⟨ξ; (id : Nat → Nat)⟩) (q⟨ξ; (id : Nat → Nat)⟩) := by
  induction step with
  | exp step =>
      intro ξ _
      simpa using TLLC.Process.Step.exp (dynamic_step_crename step ξ)
  | fork eqTerm eqCtx =>
      rename_i A m m' N N'
      intro ξ _
      subst eqTerm
      subst eqCtx
      convert (TLLC.Process.Step.fork
        (A := A⟨ξ; (id : Nat → Nat)⟩)
        (m := m⟨ξ; (id : Nat → Nat)⟩)
        (m' := (m⟨ξ; (id : Nat → Nat)⟩)⟨((· + 1) : Nat → Nat);
          (id : Nat → Nat)⟩)
        (N := N.cren ξ)
        (N' := (N.cren ξ).cren ((· + 1) : Nat → Nat)) rfl rfl) using 1
      · asimp
        rw [evalctx_cren]
        asimp
      · asimp
        rw [evalctx_cren]
        rw [evalctx_cren_comp]
        rw [show funcomp (upRen_Chan_Chan ξ) ((· + 1) : Nat → Nat) =
            funcomp ((· + 1) : Nat → Nat) ξ from by funext x; rfl]
        rw [← evalctx_cren_comp]
        asimp
        congr 3
  | comIm =>
      rename_i M N m
      intro ξ _
      convert (TLLC.Process.Step.comIm
        (M := M.cren (upRen_Chan_Chan ξ))
        (N := N.cren (upRen_Chan_Chan ξ))
        (m := m⟨upRen_Chan_Chan ξ; (id : Nat → Nat)⟩)) using 1
      all_goals
        asimp
        rw [evalctx_cren]
        rw [evalctx_cren]
        asimp
  | comEx value =>
      rename_i M N v
      intro ξ _
      convert (TLLC.Process.Step.comEx
        (M := M.cren (upRen_Chan_Chan ξ))
        (N := N.cren (upRen_Chan_Chan ξ))
        (v := v⟨upRen_Chan_Chan ξ; (id : Nat → Nat)⟩)
        (dynamic_val_crename value (upRen_Chan_Chan ξ))) using 1
      all_goals
        asimp
        rw [evalctx_cren]
        rw [evalctx_cren]
        asimp
  | «end» eqM eqN =>
      rename_i M N M' N'
      intro ξ h0
      subst eqM
      subst eqN
      convert (TLLC.Process.Step.end
        (M := M.cren (upRen_Chan_Chan ξ))
        (N := N.cren (upRen_Chan_Chan ξ))
        (M' := (M.cren (upRen_Chan_Chan ξ)).cren ((· - 1) : Nat → Nat))
        (N' := (N.cren (upRen_Chan_Chan ξ)).cren ((· - 1) : Nat → Nat)) rfl rfl) using 1
      · asimp
        rw [evalctx_cren]
        rw [evalctx_cren]
        asimp
      · asimp
        rw [evalctx_cren]
        rw [evalctx_cren]
        asimp
        rw [evalctx_cren_comp M ((· - 1) : Nat → Nat) ξ]
        rw [evalctx_cren_comp N ((· - 1) : Nat → Nat) ξ]
        rw [evalctx_cren_comp M (upRen_Chan_Chan ξ) ((· - 1) : Nat → Nat)]
        rw [evalctx_cren_comp N (upRen_Chan_Chan ξ) ((· - 1) : Nat → Nat)]
        rw [show funcomp ((· - 1) : Nat → Nat) (upRen_Chan_Chan ξ) =
            funcomp ξ ((· - 1) : Nat → Nat) from by
              funext x
              cases x with
              | zero =>
                  exact h0.symm
              | succ x =>
                  rfl]
  | par step ih =>
      intro ξ h0
      simpa using TLLC.Process.Step.par (ih ξ h0)
  | res step ih =>
      intro ξ h0
      simpa using TLLC.Process.Step.res (ih (upRen_Chan_Chan ξ) rfl)
  | congr left step right ih =>
      intro ξ h0
      exact TLLC.Process.Step.congr (process_congr_crename left ξ) (ih ξ h0)
        (process_congr_crename right ξ)

lemma process_step_parallel_left {p q r : Proc}
    (step : TLLC.Process.Step p q) :
    TLLC.Process.Step (.par p r) (.par q r) := by
  exact TLLC.Process.Step.congr
    (ARS.conv1 TLLC.Process.CongrProc.par_sym)
    (TLLC.Process.Step.par (o := r) step)
    (ARS.conv1 TLLC.Process.CongrProc.par_sym)

lemma process_step_parAll_accumulator {p q : Proc} (processes : List Proc)
    (step : TLLC.Process.Step p q) :
    TLLC.Process.Step (parAll p processes) (parAll q processes) := by
  induction processes generalizing p q with
  | nil =>
      simpa using step
  | cons process processes ih =>
      simpa [parAll] using
        ih (p := .par p process) (q := .par q process)
          (process_step_parallel_left (r := process) step)

lemma process_congr_parAll_accumulator {p q : Proc} (processes : List Proc)
    (congr : TLLC.Process.Congruence p q) :
    TLLC.Process.Congruence (parAll p processes) (parAll q processes) := by
  induction processes generalizing p q with
  | nil =>
      simpa using congr
  | cons process processes ih =>
      simpa [parAll] using
        ih (p := .par p process) (q := .par q process)
          (process_congr_parallel_left (r := process) congr)

lemma process_congr_par_parAll_right (p q : Proc) (processes : List Proc) :
    TLLC.Process.Congruence (.par p (parAll q processes))
      (parAll (.par p q) processes) := by
  induction processes generalizing q with
  | nil =>
      exact ARS.Conv.refl
  | cons r processes ih =>
      simpa [parAll] using ARS.conv_trans
        (ih (.par q r))
        (process_congr_parAll_accumulator processes
          (ARS.conv1 (TLLC.Process.CongrProc.assoc (o := p) (p := q) (q := r))))

lemma process_congr_parAll_accumulator_csubst {p q : Proc} (processes : List Proc)
    (congr : ∀ σ : Nat → Chan,
      TLLC.Process.Congruence (p[σ; Term.var_Term]) (q[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Congruence
        ((parAll p processes)[σ; Term.var_Term])
        ((parAll q processes)[σ; Term.var_Term]) := by
  induction processes generalizing p q with
  | nil =>
      intro σ
      simpa [parAll] using congr σ
  | cons process processes ih =>
      intro σ
      simpa [parAll] using
        ih (p := .par p process) (q := .par q process)
          (fun σ => by
            asimp
            exact process_congr_parallel_left (r := process[σ; Term.var_Term]) (congr σ)) σ

lemma process_step_parAll_list {body old new : Proc} (before after : List Proc)
    (step : TLLC.Process.Step old new) :
    TLLC.Process.Step
      (parAll body (before ++ old :: after))
      (parAll body (before ++ new :: after)) := by
  induction before generalizing body with
  | nil =>
      simpa [parAll] using
        process_step_parAll_accumulator after
          (TLLC.Process.Step.par (o := body) step)
  | cons process before ih =>
      simpa [parAll, List.cons_append] using
        ih (body := .par body process)

lemma process_congr_parAll_list {body old new : Proc} (before after : List Proc)
    (congr : TLLC.Process.Congruence old new) :
    TLLC.Process.Congruence
      (parAll body (before ++ old :: after))
      (parAll body (before ++ new :: after)) := by
  induction before generalizing body with
  | nil =>
      simpa [parAll] using
        process_congr_parAll_accumulator after
          (process_congr_parallel_right (r := body) congr)
  | cons process before ih =>
      simpa [parAll, List.cons_append] using
        ih (body := .par body process)

lemma process_congr_scope_right {p q : Proc} :
    TLLC.Process.Congruence (.par p (.nu q))
      (.nu (.par (p⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) q)) := by
  exact ARS.conv_trans
    (ARS.conv1 TLLC.Process.CongrProc.par_sym)
    (ARS.conv_trans
      (ARS.conv1 TLLC.Process.CongrProc.scope)
      (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym)))

lemma process_congr_exch {p : Proc} :
    TLLC.Process.Congruence (.nu (.nu p))
      (.nu (.nu (p[TLLC.Process.exch; Term.var_Term]))) := by
  exact ARS.conv1 TLLC.Process.CongrProc.exch

lemma process_congr_exch_symm {p : Proc} :
    TLLC.Process.Congruence (.nu (.nu (p[TLLC.Process.exch; Term.var_Term])))
      (.nu (.nu p)) := by
  exact ARS.conv1i TLLC.Process.CongrProc.exch

lemma process_congr_swap_right {a b c : Proc} :
    TLLC.Process.Congruence (.par (.par a b) c) (.par (.par a c) b) := by
  exact ARS.conv_trans
    (ARS.conv1i (TLLC.Process.CongrProc.assoc (o := a) (p := b) (q := c)))
    (ARS.conv_trans
      (process_congr_parallel_right (r := a) (ARS.conv1 TLLC.Process.CongrProc.par_sym))
      (ARS.conv1 (TLLC.Process.CongrProc.assoc (o := a) (p := c) (q := b))))

lemma process_congr_parAll_push_right (body p : Proc) (processes : List Proc) :
    TLLC.Process.Congruence (parAll (.par body p) processes)
      (parAll body (processes ++ [p])) := by
  induction processes generalizing body with
  | nil =>
      exact ARS.Conv.refl
  | cons q processes ih =>
      simpa [parAll, List.cons_append] using ARS.conv_trans
        (process_congr_parAll_accumulator processes
          (process_congr_swap_right (a := body) (b := p) (c := q)))
        (ih (body := .par body q))

lemma process_step_comIm_edge_csubst {M N : EvalCtx} {payloadTerm : Term} {c d : Chan}
    (payload : implicitPayload c d payloadTerm) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.app (.send (Term.chan c) .im) payloadTerm .im))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.recv (Term.chan d) .im))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.nu (.par
          (.tm (((M.eval (.pure (Term.chan c)))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.pure (.pair payloadTerm (Term.chan d) .im .L)))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term])))) := by
  intro σ
  cases c with
  | var_Chan parentIndex =>
    cases d with
    | var_Chan childIndex =>
      have payloadEq :
          payloadTerm[(fun x => if x = parentIndex then Chan.var_Chan 0 else Chan.var_Chan (x + 1)) >>
              [Chan.var_Chan var_zero .: σ >> ⟨↑⟩]; Term.var_Term] =
            payloadTerm[(fun x => if x = childIndex then Chan.var_Chan 0 else Chan.var_Chan (x + 1)) >>
              [Chan.var_Chan var_zero .: σ >> ⟨↑⟩]; Term.var_Term] := by
        convert payload σ using 1 <;>
          (asimp; unfold bindEndpointAt chanIndex; simp)
      convert (TLLC.Process.Step.comIm
        (M := (M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan parentIndex)))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ)))
        (N := (N.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan childIndex)))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ)))
        (m := payloadTerm[bindEndpointAt 0 (Chan.var_Chan parentIndex); Term.var_Term][up_Chan_Chan σ;
          Term.var_Term])) using 1
      all_goals
        repeat rw [evalctx_csubst]
        asimp
        unfold bindEndpointAt chanIndex
        simp
        try rw [← payloadEq]
        try constructor
        all_goals try trivial
        try asimp

lemma process_step_comIm_edge_symm_csubst {M N : EvalCtx} {payloadTerm : Term} {c d : Chan}
    (payload : implicitPayload c d payloadTerm) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.recv (Term.chan c) .im))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.app (.send (Term.chan d) .im) payloadTerm .im))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.nu (.par
          (.tm (((M.eval (.pure (.pair payloadTerm (Term.chan c) .im .L)))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.pure (Term.chan d)))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term])))) := by
  intro σ
  exact TLLC.Process.Step.congr
    (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym))
    (process_step_comIm_edge_csubst (M := N) (N := M) (payloadTerm := payloadTerm)
      (c := d) (d := c) (implicitPayload_symm payload) σ)
    (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym))

lemma process_step_sendIm_last_csubst {M N : EvalCtx} {payloadTerm : Term} {c d : Chan}
    (before : List (Chan × Tree)) (payload : implicitPayload c d payloadTerm) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        ((flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .im) payloadTerm .im)))
          (before ++ [(c, .node d (N.eval (.recv (Term.chan d) .im)) [] [])]))[σ;
            Term.var_Term])
        ((flattenChildren (.tm (M.eval (.pure (Term.chan c))))
          (before ++
            [(c, .node d (N.eval (.pure (.pair payloadTerm (Term.chan d) .im .L))) [] [])]))[σ;
              Term.var_Term]) := by
  induction before with
  | nil =>
      intro σ
      simp [flattenChildren, flattenBody, parAll]
      simpa using process_step_comIm_edge_csubst (M := M) (N := N)
        (payloadTerm := payloadTerm) (c := c) (d := d) payload σ
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f p =>
          have tailStep := ih (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := p[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                tailStep)
            using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

lemma process_step_recvIm_last_csubst {M N : EvalCtx} {payloadTerm : Term} {c d : Chan}
    (before : List (Chan × Tree)) (payload : implicitPayload c d payloadTerm) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        ((flattenChildren (.tm (M.eval (.recv (Term.chan c) .im)))
          (before ++
            [(c, .node d (N.eval (.app (.send (Term.chan d) .im) payloadTerm .im)) [] [])]))[σ;
              Term.var_Term])
        ((flattenChildren (.tm (M.eval (.pure (.pair payloadTerm (Term.chan c) .im .L))))
          (before ++ [(c, .node d (N.eval (.pure (Term.chan d))) [] [])]))[σ;
            Term.var_Term]) := by
  induction before with
  | nil =>
      intro σ
      simp [flattenChildren, flattenBody, parAll]
      simpa using process_step_comIm_edge_symm_csubst (M := M) (N := N)
        (payloadTerm := payloadTerm) (c := c) (d := d) payload σ
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f p =>
          have tailStep := ih (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := p[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                tailStep)
            using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

lemma process_step_comEx_edge_csubst {M N : EvalCtx} {valueTerm : Term} {c d : Chan}
    (value : Val valueTerm) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.app (.send (Term.chan c) .ex) valueTerm .ex))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.recv (Term.chan d) .ex))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.nu (.par
          (.tm (((M.eval (.pure (Term.chan c)))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 d))).cren
            (TLLC.Static.csubst_ren (up_Chan_Chan σ))).eval
              (.pure (.pair
                (valueTerm[bindEndpointAt 0 c; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                (TLLC.Process.cvar 0) .ex .L)))))) := by
  intro σ
  cases c with
  | var_Chan parentIndex =>
    cases d with
    | var_Chan childIndex =>
      convert (TLLC.Process.Step.comEx
        (M := (M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan parentIndex)))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ)))
        (N := (N.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan childIndex)))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ)))
        (v := valueTerm[bindEndpointAt 0 (Chan.var_Chan parentIndex); Term.var_Term][up_Chan_Chan σ;
          Term.var_Term])
        (dynamic_val_csubst (dynamic_val_csubst value (bindEndpointAt 0 (Chan.var_Chan parentIndex)))
          (up_Chan_Chan σ))) using 1
      all_goals
        repeat rw [evalctx_csubst]
        asimp
        unfold bindEndpointAt chanIndex
        simp
        try constructor
        all_goals try trivial
        try asimp

lemma process_step_comEx_edge_symm_csubst {M N : EvalCtx} {valueTerm : Term} {c d : Chan}
    (value : Val valueTerm) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.recv (Term.chan c) .ex))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.app (.send (Term.chan d) .ex) valueTerm .ex))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.nu (.par
          (.tm (((M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 c))).cren
            (TLLC.Static.csubst_ren (up_Chan_Chan σ))).eval
              (.pure (.pair
                (valueTerm[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                (TLLC.Process.cvar 0) .ex .L))))
          (.tm (((N.eval (.pure (Term.chan d)))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term])))) := by
  intro σ
  exact TLLC.Process.Step.congr
    (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym))
    (process_step_comEx_edge_csubst (M := N) (N := M) (valueTerm := valueTerm)
      (c := d) (d := c) value σ)
    (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym))

lemma process_step_end_edge_csubst {M N : EvalCtx} {c d : Chan} :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.close true (Term.chan c)))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.close false (Term.chan d)))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.par
          (.tm ((((M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 c))).cren
            (TLLC.Static.csubst_ren (up_Chan_Chan σ))).cren ((· - 1) : Nat → Nat)).eval
              (.pure .one)))
          (.tm ((((N.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 d))).cren
            (TLLC.Static.csubst_ren (up_Chan_Chan σ))).cren ((· - 1) : Nat → Nat)).eval
              (.pure .one)))) := by
  intro σ
  cases c with
  | var_Chan parentIndex =>
    cases d with
    | var_Chan childIndex =>
      convert (TLLC.Process.Step.end
        (M := (M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan parentIndex)))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ)))
        (N := (N.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan childIndex)))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ)))
        rfl rfl) using 1
      · repeat rw [evalctx_csubst]
        asimp
        unfold bindEndpointAt chanIndex
        simp
        try constructor
        all_goals try trivial
        try asimp

lemma process_step_end_edge_symm_csubst {M N : EvalCtx} {c d : Chan} :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.close false (Term.chan c)))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.close true (Term.chan d)))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.par
          (.tm ((((M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 c))).cren
            (TLLC.Static.csubst_ren (up_Chan_Chan σ))).cren ((· - 1) : Nat → Nat)).eval
              (.pure .one)))
          (.tm ((((N.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 d))).cren
            (TLLC.Static.csubst_ren (up_Chan_Chan σ))).cren ((· - 1) : Nat → Nat)).eval
              (.pure .one)))) := by
  intro σ
  exact TLLC.Process.Step.congr
    (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym))
    (process_step_end_edge_csubst (M := N) (N := M) (c := d) (d := c) σ)
    (ARS.conv1 TLLC.Process.CongrProc.par_sym)

lemma process_congr_end_target_csubst {M N : EvalCtx} {c d : Chan} {σ : Nat → Chan}
    (pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0)
    (cUnused : occurs (chanIndex d) (N.eval (.pure .one)) = 0) :
    TLLC.Process.Congruence
      (.par
        (.tm ((((M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 c))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ))).cren ((· - 1) : Nat → Nat)).eval
            (.pure .one)))
        (.tm ((((N.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 d))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ))).cren ((· - 1) : Nat → Nat)).eval
            (.pure .one))))
      (.par
        (.tm ((M.eval (.pure .one))[σ; Term.var_Term]))
        (.tm ((N.eval (.pure .one))[σ; Term.var_Term]))) := by
  exact ARS.conv1 (TLLC.Process.CongrProc.par
    (TLLC.Process.CongrProc.tm
      (evalctx_consume_endpoint_pure_one (M := M) (c := c) (σ := σ) pUnused))
    (TLLC.Process.CongrProc.tm
      (evalctx_consume_endpoint_pure_one (M := N) (c := d) (σ := σ) cUnused)))

lemma process_step_end_final_csubst {M N : EvalCtx} {c d : Chan}
    (pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0)
    (cUnused : occurs (chanIndex d) (N.eval (.pure .one)) = 0) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.close true (Term.chan c)))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.close false (Term.chan d)))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.par
          (.tm ((M.eval (.pure .one))[σ; Term.var_Term]))
          (.tm ((N.eval (.pure .one))[σ; Term.var_Term]))) := by
  intro σ
  exact TLLC.Process.Step.congr ARS.Conv.refl
    (process_step_end_edge_csubst (M := M) (N := N) (c := c) (d := d) σ)
    (process_congr_end_target_csubst (M := M) (N := N) (c := c) (d := d)
      (σ := σ) pUnused cUnused)

lemma process_step_end_final_symm_csubst {M N : EvalCtx} {c d : Chan}
    (pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0)
    (cUnused : occurs (chanIndex d) (N.eval (.pure .one)) = 0) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.close false (Term.chan c)))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.close true (Term.chan d)))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.par
          (.tm ((M.eval (.pure .one))[σ; Term.var_Term]))
          (.tm ((N.eval (.pure .one))[σ; Term.var_Term]))) := by
  intro σ
  exact TLLC.Process.Step.congr ARS.Conv.refl
    (process_step_end_edge_symm_csubst (M := M) (N := N) (c := c) (d := d) σ)
    (process_congr_end_target_csubst (M := M) (N := N) (c := c) (d := d)
      (σ := σ) pUnused cUnused)

lemma parAll_csubst (body : Proc) (processes : List Proc) :
    ∀ σ : Nat → Chan,
      (parAll body processes)[σ; Term.var_Term] =
        parAll (body[σ; Term.var_Term])
          (processes.map (fun process => process[σ; Term.var_Term])) := by
  induction processes generalizing body with
  | nil =>
    intro σ
    simp [parAll]
  | cons process processes ih =>
    intro σ
    simpa [parAll] using ih (.par body process) σ

lemma process_step_flattenSubtrees_list {body : Proc} {subtree subtree' : Tree}
    (before after : List Tree)
    (step : TLLC.Process.Step subtree.flatten subtree'.flatten) :
    TLLC.Process.Step
      (parAll body (flattenSubtrees (before ++ subtree :: after)))
      (parAll body (flattenSubtrees (before ++ subtree' :: after))) := by
  simpa [flattenSubtrees_eq_map, List.map_append] using
    process_step_parAll_list (body := body)
      (before.map Tree.flatten) (after.map Tree.flatten) step

lemma process_step_flattenSubtrees_list_csubst {body : Proc} {subtree subtree' : Tree}
    (before after : List Tree)
    (step : ∀ σ : Nat → Chan,
      TLLC.Process.Step (subtree.flatten[σ; Term.var_Term])
        (subtree'.flatten[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        ((parAll body (flattenSubtrees (before ++ subtree :: after)))[σ; Term.var_Term])
        ((parAll body (flattenSubtrees (before ++ subtree' :: after)))[σ; Term.var_Term]) := by
  intro σ
  rw [parAll_csubst]
  rw [parAll_csubst]
  simpa [flattenSubtrees_eq_map, List.map_append, List.map_map] using
    process_step_parAll_list (body := body[σ; Term.var_Term])
      ((before.map Tree.flatten).map (fun process => process[σ; Term.var_Term]))
      ((after.map Tree.flatten).map (fun process => process[σ; Term.var_Term]))
      (step σ)

lemma process_congr_flattenSubtrees_list_csubst {body : Proc} {subtree subtree' : Tree}
    (before after : List Tree)
    (congr : ∀ σ : Nat → Chan,
      TLLC.Process.Congruence (subtree.flatten[σ; Term.var_Term])
        (subtree'.flatten[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Congruence
        ((parAll body (flattenSubtrees (before ++ subtree :: after)))[σ; Term.var_Term])
        ((parAll body (flattenSubtrees (before ++ subtree' :: after)))[σ; Term.var_Term]) := by
  intro σ
  rw [parAll_csubst]
  rw [parAll_csubst]
  simpa [flattenSubtrees_eq_map, List.map_append, List.map_map] using
    process_congr_parAll_list (body := body[σ; Term.var_Term])
      ((before.map Tree.flatten).map (fun process => process[σ; Term.var_Term]))
      ((after.map Tree.flatten).map (fun process => process[σ; Term.var_Term]))
      (congr σ)

lemma process_step_flattenChildren_body_csubst {body body' : Proc}
    (children : List (Chan × Tree))
    (step : ∀ σ : Nat → Chan,
      TLLC.Process.Step (body[σ; Term.var_Term]) (body'[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step ((flattenChildren body children)[σ; Term.var_Term])
        ((flattenChildren body' children)[σ; Term.var_Term]) := by
  induction children with
  | nil =>
      intro σ
      simpa [flattenChildren] using step σ
  | cons edge children ih =>
      intro σ
      rcases edge with ⟨c, child⟩
      rw [flattenChildren]
      rw [flattenChildren]
      cases h : child.flattenAt with
      | mk d childProcess =>
          have tailStep := ih (fun x => (bindEndpointAt 0 c x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := childProcess[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ;
                  Term.var_Term])
                tailStep)
            using 1
          · simp
            asimp
          · simp
            asimp

lemma process_step_flattenChildren_child_csubst {body : Proc} {c d : Chan}
    {child child' : Tree} (before after : List (Chan × Tree))
    (childAt : child.flattenAt = (d, child.flatten))
    (childAt' : child'.flattenAt = (d, child'.flatten))
    (step : ∀ σ : Nat → Chan,
      TLLC.Process.Step (child.flatten[σ; Term.var_Term])
        (child'.flatten[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        ((flattenChildren body (before ++ (c, child) :: after))[σ; Term.var_Term])
        ((flattenChildren body (before ++ (c, child') :: after))[σ; Term.var_Term]) := by
  induction before generalizing body with
  | nil =>
      intro σ
      simp only [List.nil_append]
      have childStep := step (fun x => (bindEndpointAt 0 d x)[up_Chan_Chan σ])
      convert
        TLLC.Process.Step.res
          (TLLC.Process.Step.par
            (o := (((flattenChildren body after)[bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ;
              Term.var_Term]))
            childStep)
        using 1
      · simp [flattenChildren, childAt]
        asimp
      · simp [flattenChildren, childAt']
        asimp
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f siblingProcess =>
          have tailStep := ih (body := body) (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := siblingProcess[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ;
                  Term.var_Term])
                tailStep)
            using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

lemma process_congr_flattenChildren_child_csubst {body : Proc} {c d : Chan}
    {child child' : Tree} (before after : List (Chan × Tree))
    (childAt : child.flattenAt = (d, child.flatten))
    (childAt' : child'.flattenAt = (d, child'.flatten))
    (congr : ∀ σ : Nat → Chan,
      TLLC.Process.Congruence (child.flatten[σ; Term.var_Term])
        (child'.flatten[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Congruence
        ((flattenChildren body (before ++ (c, child) :: after))[σ; Term.var_Term])
        ((flattenChildren body (before ++ (c, child') :: after))[σ; Term.var_Term]) := by
  induction before generalizing body with
  | nil =>
      intro σ
      simp only [List.nil_append]
      have childCongr := congr (fun x => (bindEndpointAt 0 d x)[up_Chan_Chan σ])
      have resCongr := process_congr_res (process_congr_parallel_right
        (r := ((flattenChildren body after)[bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ;
          Term.var_Term]) childCongr)
      convert resCongr using 1
      · simp [flattenChildren, childAt]
        asimp
      · simp [flattenChildren, childAt']
        asimp
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f p =>
          have tailCongr := ih (body := body) (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          have resCongr := process_congr_res (process_congr_parallel_left
            (r := p[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
            tailCongr)
          convert resCongr using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

lemma process_congr_flattenChildren_body_csubst {body body' : Proc}
    (children : List (Chan × Tree))
    (congr : ∀ σ : Nat → Chan,
      TLLC.Process.Congruence (body[σ; Term.var_Term]) (body'[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Congruence ((flattenChildren body children)[σ; Term.var_Term])
        ((flattenChildren body' children)[σ; Term.var_Term]) := by
  induction children with
  | nil =>
      intro σ
      simpa [flattenChildren] using congr σ
  | cons edge children ih =>
      intro σ
      rcases edge with ⟨c, child⟩
      rw [flattenChildren]
      rw [flattenChildren]
      cases h : child.flattenAt with
      | mk d p =>
          have tailCongr := ih (fun x => (bindEndpointAt 0 c x)[up_Chan_Chan σ])
          have resCongr := process_congr_res (process_congr_parallel_left
            (r := p[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
            tailCongr)
          convert resCongr using 1
          · simp
            asimp
          · simp
            asimp

lemma process_step_flattenChildren_body {body body' : Proc}
    (children : List (Chan × Tree))
    (step : ∀ σ : Nat → Chan,
      TLLC.Process.Step (body[σ; Term.var_Term]) (body'[σ; Term.var_Term])) :
    TLLC.Process.Step (flattenChildren body children) (flattenChildren body' children) := by
  convert process_step_flattenChildren_body_csubst children step Chan.var_Chan using 1 <;> asimp

/-! ## Child-edge reordering (report's "rearrange by Proc-Congr") -/

/-- Flattening a concatenated child list folds the suffix into a new base. -/
lemma flattenChildren_append (body : Proc) (l X : List (Chan × Tree)) :
    flattenChildren body (l ++ X) = flattenChildren (flattenChildren body X) l := by
  induction l generalizing body with
  | nil => simp
  | cons edge l ih =>
      rcases edge with ⟨c, child⟩
      rw [List.cons_append, flattenChildren, flattenChildren]
      cases h : child.flattenAt with
      | mk d p =>
          simp only [h]
          rw [ih]

/-- Reshape `.nu (.par (.nu W) Y)` into double-`nu` normal form via the scope congruence. -/
lemma swap_normal_form (W Y : Proc) :
    TLLC.Process.Congruence
      (.nu (.par (.nu W) Y))
      (.nu (.nu (.par W (Y⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)))) :=
  process_congr_res (ARS.conv1 TLLC.Process.CongrProc.scope)

/-- Core de Bruijn algebra for swapping two adjacent child edges in a flattened child list: the two
fresh channels commute (`exch`), and by linearity (`f1`/`f2`) neither sibling process mentions the
other's parent endpoint. This is the report's *"apply structural congruence to rearrange the
scoping"* step, made precise for the self-dual single-channel encoding. -/
lemma flattenChildren_swap2 (B : Proc) (c1 c2 d1 d2 : Chan) (p1 p2 : Proc)
    (hne : chanIndex c1 ≠ chanIndex c2)
    (f1 : TLLC.Process.procOccurs (chanIndex c1 + 1)
      (p2[bindEndpointAt 0 d2; Term.var_Term]) = 0)
    (f2 : TLLC.Process.procOccurs (chanIndex c2 + 1)
      (p1[bindEndpointAt 0 d1; Term.var_Term]) = 0) :
    TLLC.Process.Congruence
      (.nu (.par (.nu (.par
          (B[bindEndpointAt 0 c2; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 c1); Term.var_Term])
          (p2[bindEndpointAt 0 d2; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 c1); Term.var_Term])))
        (p1[bindEndpointAt 0 d1; Term.var_Term])))
      (.nu (.par (.nu (.par
          (B[bindEndpointAt 0 c1; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 c2); Term.var_Term])
          (p1[bindEndpointAt 0 d1; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 c2); Term.var_Term])))
        (p2[bindEndpointAt 0 d2; Term.var_Term]))) := by
  -- L into double-nu normal form, then exch
  refine ARS.conv_trans (swap_normal_form _ _) ?_
  refine ARS.conv_trans (process_congr_exch) ?_
  -- S into double-nu normal form (reverse direction)
  refine ARS.conv_trans ?_ (ARS.conv_sym (swap_normal_form _ _))
  -- both sides are nu nu (par (par _ _) _); peel the two nu's
  refine process_congr_res (process_congr_res ?_)
  simp only [(show ∀ (a b : Proc) (σ : Nat → Chan),
    (Proc.par a b)[σ; Term.var_Term] = Proc.par (a[σ; Term.var_Term]) (b[σ; Term.var_Term])
    from fun _ _ _ => rfl)]
  set P1 := p1[bindEndpointAt 0 d1; Term.var_Term] with hP1
  set P2 := p2[bindEndpointAt 0 d2; Term.var_Term] with hP2
  -- the base process moves by a pure substitution identity (needs only c1 ≠ c2)
  have leafB :
      B[bindEndpointAt 0 c2; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 c1); Term.var_Term][
        Process.exch; Term.var_Term] =
      B[bindEndpointAt 0 c1; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 c2); Term.var_Term] := by
    obtain ⟨a⟩ := c1
    obtain ⟨b⟩ := c2
    asimp
    congr 1
    funext x
    simp only [chanIndex] at hne
    rcases eq_or_ne x a with rfl | hxa
    · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
    rcases eq_or_ne x b with rfl | hxb
    · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
    · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
  -- the receiving sibling moves by a congruence (uses f1: c1 ∉ that sibling)
  have leaf2 :
      TLLC.Process.Congruence
        (P2[up_Chan_Chan (bindEndpointAt 0 c1); Term.var_Term][Process.exch; Term.var_Term])
        (P2⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) := by
    rw [show P2⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
          = P2[(fun x => Chan.var_Chan (x + 1)); Term.var_Term] from by
        rw [← process_csubst_cren]; rfl]
    conv_lhs => simp only [asimp_lemmas]
    apply process_congr_csubst_of_eqv (i := chanIndex c1 + 1) _ f1
    intro x hx
    obtain ⟨a⟩ := c1
    simp only [chanIndex] at hx
    rcases x with _ | k
    · simp [scons, asimp_lemmas]
    · rcases eq_or_ne k a with rfl | hk
      · omega
      · simp [bindEndpointAt, chanIndex, scons, funcomp, hk, asimp_lemmas]
  -- the moved sibling itself (uses f2: c2 ∉ that sibling)
  have leaf1 :
      TLLC.Process.Congruence
        (P1⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩[Process.exch; Term.var_Term])
        (P1[up_Chan_Chan (bindEndpointAt 0 c2); Term.var_Term]) := by
    conv_lhs => simp only [asimp_lemmas]
    apply process_congr_csubst_of_eqv (i := chanIndex c2 + 1) _ f2
    intro x hx
    obtain ⟨b⟩ := c2
    simp only [chanIndex] at hx
    rcases x with _ | k
    · simp [scons, asimp_lemmas]
    · rcases eq_or_ne k b with rfl | hk
      · omega
      · simp [bindEndpointAt, chanIndex, scons, funcomp, hk, asimp_lemmas]
  -- assemble: swap the two sibling positions, then rewrite the three leaves
  refine ARS.conv_trans process_congr_swap_right ?_
  rw [leafB]
  exact ARS.conv_trans
    (process_congr_parallel_left (process_congr_parallel_right leaf1))
    (process_congr_parallel_right leaf2)

/-- `flattenChildren`-level adjacent swap. The freshness premises say each sibling's flattened body
does not mention the other sibling's parent endpoint (linearity); in use they come from
`TypedAt.flattenAt_occurs_succ`. -/
lemma flattenChildren_swap_adjacent (body : Proc) (c1 c2 : Chan) (ch1 ch2 : Tree)
    (rest : List (Chan × Tree))
    (hne : chanIndex c1 ≠ chanIndex c2)
    (f1 : TLLC.Process.procOccurs (chanIndex c1 + 1)
      ((ch2.flattenAt).2[bindEndpointAt 0 (ch2.flattenAt).1; Term.var_Term]) = 0)
    (f2 : TLLC.Process.procOccurs (chanIndex c2 + 1)
      ((ch1.flattenAt).2[bindEndpointAt 0 (ch1.flattenAt).1; Term.var_Term]) = 0) :
    TLLC.Process.Congruence
      (flattenChildren body ((c1, ch1) :: (c2, ch2) :: rest))
      (flattenChildren body ((c2, ch2) :: (c1, ch1) :: rest)) := by
  cases h1 : ch1.flattenAt with
  | mk d1 p1 =>
  cases h2 : ch2.flattenAt with
  | mk d2 p2 =>
    simp only [h1, h2] at f1 f2
    simp only [flattenChildren, h1, h2,
      (show ∀ (p : Proc) (σ : Nat → Chan),
          (Proc.nu p)[σ; Term.var_Term] = Proc.nu (p[up_Chan_Chan σ; Term.var_Term])
        from fun _ _ => rfl),
      (show ∀ (a b : Proc) (σ : Nat → Chan),
          (Proc.par a b)[σ; Term.var_Term] = Proc.par (a[σ; Term.var_Term]) (b[σ; Term.var_Term])
        from fun _ _ _ => rfl)]
    exact flattenChildren_swap2 (flattenChildren body rest) c1 c2 d1 d2 p1 p2 hne f1 f2

/-- Adjacent swap with freshness supplied by typing (`flattenAt_occurs_succ`). -/
lemma flattenChildren_swap_adjacent_typed (body : Proc) (c1 c2 : Chan) (ch1 ch2 : Tree)
    (rest : List (Chan × Tree)) (hne : chanIndex c1 ≠ chanIndex c2)
    (ty1 : ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) ch1)
    (ty2 : ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) ch2) :
    TLLC.Process.Congruence
      (flattenChildren body ((c1, ch1) :: (c2, ch2) :: rest))
      (flattenChildren body ((c2, ch2) :: (c1, ch1) :: rest)) := by
  obtain ⟨r1, A1, tyA1, t1⟩ := ty1
  obtain ⟨r2, A2, tyA2, t2⟩ := ty2
  exact flattenChildren_swap_adjacent body c1 c2 ch1 ch2 rest hne
    (t2.flattenAt_occurs_succ tyA2 (chanIndex c1)) (t1.flattenAt_occurs_succ tyA1 (chanIndex c2))

/-- Lift a congruence between two child lists through one shared prefix edge. -/
lemma flattenChildren_congr_prefix_one (body : Proc) (e : Chan) (sib : Tree)
    (A A' : List (Chan × Tree))
    (cong : TLLC.Process.Congruence (flattenChildren body A) (flattenChildren body A')) :
    TLLC.Process.Congruence
      (flattenChildren body ((e, sib) :: A)) (flattenChildren body ((e, sib) :: A')) := by
  cases hs : sib.flattenAt with
  | mk ds sp =>
    have eqL : flattenChildren body ((e, sib) :: A) = .nu (.par
        ((flattenChildren body A)[bindEndpointAt 0 e; Term.var_Term])
        (sp[bindEndpointAt 0 ds; Term.var_Term])) := by simp only [flattenChildren, hs]
    have eqR : flattenChildren body ((e, sib) :: A') = .nu (.par
        ((flattenChildren body A')[bindEndpointAt 0 e; Term.var_Term])
        (sp[bindEndpointAt 0 ds; Term.var_Term])) := by simp only [flattenChildren, hs]
    rw [eqL, eqR]
    exact process_congr_res (process_congr_parallel_left (process_congr_csubst cong _))

/-- Move the head child of a flattened list to the last position (report's "rearrange by Proc-Congr").
The typing premises supply distinctness and linearity freshness. -/
lemma flattenChildren_move_head_to_last (body : Proc) (c : Chan) (child : Tree)
    (tyChild : ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) child) :
    ∀ (r : List (Chan × Tree)),
    (∀ e sib, (e, sib) ∈ r → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib) →
    (∀ e sib, (e, sib) ∈ r → chanIndex c ≠ chanIndex e) →
    TLLC.Process.Congruence
      (flattenChildren body ((c, child) :: r)) (flattenChildren body (r ++ [(c, child)])) := by
  intro r
  induction r with
  | nil => intro _ _; exact ARS.Conv.refl
  | cons edge r' ih =>
      rcases edge with ⟨e, sib⟩
      intro tyR distinct
      refine ARS.conv_trans
        (flattenChildren_swap_adjacent_typed body c e child sib r'
          (distinct e sib (by simp)) tyChild (tyR e sib (by simp))) ?_
      have ihC := ih (fun e' sib' mem => tyR e' sib' (List.mem_cons_of_mem _ mem))
        (fun e' sib' mem => distinct e' sib' (List.mem_cons_of_mem _ mem))
      simp only [List.cons_append]
      exact flattenChildren_congr_prefix_one body e sib ((c, child) :: r') (r' ++ [(c, child)]) ihC

/-- Lift a child-list congruence through an arbitrary prefix `l`. -/
lemma flattenChildren_congr_prefix (body : Proc) (l A A' : List (Chan × Tree))
    (cong : TLLC.Process.Congruence (flattenChildren body A) (flattenChildren body A')) :
    TLLC.Process.Congruence
      (flattenChildren body (l ++ A)) (flattenChildren body (l ++ A')) := by
  induction l with
  | nil => simpa using cong
  | cons edge l ih =>
      rcases edge with ⟨e, sib⟩
      simpa only [List.cons_append] using
        flattenChildren_congr_prefix_one body e sib (l ++ A) (l ++ A') ih

/-- Move a child at an arbitrary position to the last position (general "rearrange by Proc-Congr"). -/
lemma flattenChildren_move_to_last (body : Proc) (c : Chan) (child : Tree)
    (l r : List (Chan × Tree))
    (tyChild : ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) child)
    (tyR : ∀ e sib, (e, sib) ∈ r → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (distinct : ∀ e sib, (e, sib) ∈ r → chanIndex c ≠ chanIndex e) :
    TLLC.Process.Congruence
      (flattenChildren body (l ++ (c, child) :: r))
      (flattenChildren body ((l ++ r) ++ [(c, child)])) := by
  have h := flattenChildren_congr_prefix body l ((c, child) :: r) (r ++ [(c, child)])
    (flattenChildren_move_head_to_last body c child tyChild r tyR distinct)
  simpa [List.append_assoc] using h

/-! ## Exposing the receiver body (report's "Proc-Scope/Proc-Par to isolate") -/

/-- Abstract extrusion congruence: pull a grandchild `nu` out past the parent `nu` (`scope_right` then
`exch` then `assoc`). After this, the parent channel is the INNER `nu`'s `cvar 0` and the grandchild
`GP` is a parallel spectator referencing the OUTER `nu`. -/
lemma extrude_one_congr (A X GP : Proc) :
    TLLC.Process.Congruence
      (.nu (.par A (.nu (.par X GP))))
      (.nu (.nu (.par
        (.par (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩[Process.exch; Term.var_Term])
              (X[Process.exch; Term.var_Term]))
        (GP[Process.exch; Term.var_Term])))) := by
  refine ARS.conv_trans (process_congr_res process_congr_scope_right) ?_
  refine ARS.conv_trans process_congr_exch ?_
  simp only [(show ∀ (a b : Proc) (σ : Nat → Chan),
    (Proc.par a b)[σ; Term.var_Term] = Proc.par (a[σ; Term.var_Term]) (b[σ; Term.var_Term])
    from fun _ _ _ => rfl)]
  exact process_congr_res (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.assoc))

/-- A com step `nu(par A B) ⇛ nu(par A' B')` lifts through parallel spectators `SS` on the receiver
side (each with `procOccurs 0 = 0`). This is the report's "Proc-Par to set aside the other subtrees";
it is abstract in the edge step, so it serves both `comIm` and `comEx` (the `end` step removes the `nu`
and instead uses `process_step_scope_remove_parAll_right`). -/
lemma step_par_parAll_spectators (A B A' B' : Proc) (SS : List Proc)
    (ssZero : ∀ q, q ∈ SS → TLLC.Process.procOccurs 0 q = 0)
    (edge : TLLC.Process.Step (.nu (.par A B)) (.nu (.par A' B'))) :
    TLLC.Process.Step
      (.nu (.par A (parAll B SS))) (.nu (.par A' (parAll B' SS))) :=
  TLLC.Process.Step.congr
    (process_congr_res (process_congr_par_parAll_right A B SS))
    (process_step_scope_parAll_right SS ssZero edge)
    (process_congr_res (ARS.conv_sym (process_congr_par_parAll_right A' B' SS)))

/-- The implicit com fires with arbitrary parallel spectators `SS` on the receiver side. This handles a
selected child's detached subtrees `qs'`; the grandchildren `ms'` still require scope-extrusion. -/
lemma comIm_edge_parAll (M N : EvalCtx) (payload : Term) (c d : Chan) (SS : List Proc)
    (imp : implicitPayload c d payload)
    (ssZero : ∀ q, q ∈ SS → TLLC.Process.procOccurs 0 q = 0) (σ : Nat → Chan) :
    TLLC.Process.Step
      (.nu (.par
        (.tm (((M.eval (.app (.send (Term.chan c) .im) payload .im))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
        (parAll (.tm (((N.eval (.recv (Term.chan d) .im))[bindEndpointAt 0 d;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])) SS)))
      (.nu (.par
        (.tm (((M.eval (.pure (Term.chan c)))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
        (parAll (.tm (((N.eval (.pure (.pair payload (Term.chan d) .im .L)))[bindEndpointAt 0 d;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])) SS))) :=
  step_par_parAll_spectators _ _ _ _ SS ssZero
    (process_step_comIm_edge_csubst (M := M) (N := N) (payloadTerm := payload) (c := c) (d := d) imp σ)

/-- Conditional `occurs`-under-renaming: `i` does not occur in `m⟨ξ⟩` provided every channel that `ξ`
maps onto `i` is already absent from `m`. -/
lemma occurs_cren_zero {i : Nat} {ξ : Nat → Nat} {m : Term}
    (h : ∀ k, ξ k = i → occurs k m = 0) :
    occurs i (m⟨ξ; (id : Nat → Nat)⟩) = 0 := by
  induction m generalizing i ξ with
  | var_Term _ => rfl
  | srt _ => rfl
  | pi _ _ _ _ _ _ => rfl
  | lam _ _ _ _ _ ihm => asimp; exact ihm h
  | app a b r iha ihb =>
      cases r with
      | im => asimp; exact iha (fun k hk => by have := h k hk; simpa [occurs] using this)
      | ex =>
          asimp
          have ha := iha (fun k hk => by have := h k hk; simp [occurs] at this; omega)
          have hb := ihb (fun k hk => by have := h k hk; simp [occurs] at this; omega)
          simp [occurs, ha, hb]
  | sig _ _ _ _ _ _ => rfl
  | pair a b r s iha ihb =>
      cases r with
      | im => asimp; exact ihb (fun k hk => by have := h k hk; simpa [occurs] using this)
      | ex =>
          asimp
          have ha := iha (fun k hk => by have := h k hk; simp [occurs] at this; omega)
          have hb := ihb (fun k hk => by have := h k hk; simp [occurs] at this; omega)
          simp [occurs, ha, hb]
  | proj C a b ihC iha ihb =>
      asimp
      have ha := iha (fun k hk => by have := h k hk; simp [occurs] at this; omega)
      have hb := ihb (fun k hk => by have := h k hk; simp [occurs] at this; omega)
      simp [occurs, ha, hb]
  | fix _ _ _ ihm => asimp; exact ihm h
  | unit => rfl
  | one => rfl
  | bool => rfl
  | tt => rfl
  | ff => rfl
  | ite C a b1 b2 ihC iha ihb1 ihb2 =>
      asimp
      have ha := iha (fun k hk => by have := h k hk; simp [occurs] at this; omega)
      have hb1 := ihb1 (fun k hk => by have := h k hk; simp [occurs] at this; omega)
      have hb2 := ihb2 (fun k hk => by have := h k hk; simp [occurs] at this; omega)
      simp [occurs, ha, hb1, hb2]
  | M _ _ => rfl
  | pure _ ihm => asimp; exact ihm h
  | mlet a b iha ihb =>
      asimp
      have ha := iha (fun k hk => by have := h k hk; simp [occurs] at this; omega)
      have hb := ihb (fun k hk => by have := h k hk; simp [occurs] at this; omega)
      simp [occurs, ha, hb]
  | proto => rfl
  | stop => rfl
  | act _ _ _ _ _ _ => rfl
  | ch _ _ _ => rfl
  | chan c =>
      cases c with
      | var_Chan y =>
          asimp
          show (if ξ y = i then 1 else 0) = 0
          rw [if_neg]
          intro hy
          have := h y hy
          simp [occurs] at this
  | fork _ _ _ ihm => asimp; exact ihm h
  | recv _ _ ihm => asimp; exact ihm h
  | send _ _ ihm => asimp; exact ihm h
  | close _ _ ihm => asimp; exact ihm h
  | box => rfl

/-- Conditional `procOccurs`-under-renaming, the process analogue of `occurs_cren_zero`. -/
lemma procOccurs_cren_zero {i : Nat} {ξ : Nat → Nat} {p : Proc}
    (h : ∀ k, ξ k = i → TLLC.Process.procOccurs k p = 0) :
    TLLC.Process.procOccurs i (p⟨ξ; (id : Nat → Nat)⟩) = 0 := by
  induction p generalizing i ξ with
  | tm m =>
      show occurs i (m⟨ξ; (id : Nat → Nat)⟩) = 0
      exact occurs_cren_zero h
  | par a b iha ihb =>
      have ha := iha (fun k hk => by have := h k hk; simp [TLLC.Process.procOccurs] at this; omega)
      have hb := ihb (fun k hk => by have := h k hk; simp [TLLC.Process.procOccurs] at this; omega)
      asimp
      simp only [TLLC.Process.procOccurs, ha, hb]
  | nu q ih =>
      asimp
      show TLLC.Process.procOccurs (i + 1) (q⟨upRen_Chan_Chan ξ; (id : Nat → Nat)⟩) = 0
      apply ih
      intro k hk
      cases k with
      | zero => simp [upRen_Chan_Chan, asimp_lemmas] at hk
      | succ j =>
          have hj : ξ j = i := by
            asimp at hk
            simp only [funcomp, Nat.succ_eq_add_one] at hk
            omega
          have := h j hj
          simpa [TLLC.Process.procOccurs] using this

/-- Conditional `procOccurs`-under-substitution. -/
lemma procOccurs_csubst_zero {i : Nat} {τ : Nat → Chan} {p : Proc}
    (h : ∀ k, τ k = Chan.var_Chan i → TLLC.Process.procOccurs k p = 0) :
    TLLC.Process.procOccurs i (p[τ; Term.var_Term]) = 0 := by
  rw [← process_csubst_cren]
  apply procOccurs_cren_zero
  intro k hk
  apply h k
  have hτ : τ k = Chan.var_Chan (Static.csubst_ren τ k) := by
    unfold Static.csubst_ren; cases τ k with | var_Chan y => rfl
  rw [hτ, hk]

set_option maxHeartbeats 1000000 in
/-- SS-free implicit-com edge with grandchildren `ms'`; each grandchild extrudes to a spectator and
the core `comIm` fires on the exposed `.tm recv`. -/
lemma comIm_edge_grandchildren (M N : EvalCtx) (payload : Term) (c d : Chan)
    (imp : implicitPayload c d payload) :
    ∀ (ms' : List (Chan × Tree)) (σ : Nat → Chan),
      (∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
        TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc) →
      (∀ pre e gc suf, ms' = pre ++ (e, gc) :: suf →
        TLLC.Process.procOccurs (chanIndex e)
          (flattenChildren (.tm (N.eval (.recv (Term.chan d) .im))) suf) = 0) →
      (∀ pre e gc suf, ms' = pre ++ (e, gc) :: suf →
        TLLC.Process.procOccurs (chanIndex e)
          (flattenChildren (.tm (N.eval (.pure (.pair payload (Term.chan d) .im .L)))) suf) = 0) →
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.app (.send (Term.chan c) .im) payload .im))[bindEndpointAt 0 c;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          ((flattenChildren (.tm (N.eval (.recv (Term.chan d) .im))) ms')[bindEndpointAt 0 d;
            Term.var_Term][up_Chan_Chan σ; Term.var_Term])))
        (.nu (.par
          (.tm (((M.eval (.pure (Term.chan c)))[bindEndpointAt 0 c;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          ((flattenChildren (.tm (N.eval (.pure (.pair payload (Term.chan d) .im .L)))) ms')[
            bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term]))) := by
  intro ms'
  induction ms' with
  | nil =>
      intro σ _ _ _
      simp only [flattenChildren]
      exact process_step_comIm_edge_csubst (M := M) (N := N) (payloadTerm := payload)
        (c := c) (d := d) imp σ
  | cons edge rest ih =>
      intro σ tyMs eFreshRecv eFreshRpair
      obtain ⟨e, gc⟩ := edge
      cases hgc : gc.flattenAt with
      | mk gp GP =>
        set σ' : Nat → Chan := σ >> ⟨((· + 1) : Nat → Nat)⟩ with hσ'
        have tyRest : ∀ e gc, (e, gc) ∈ rest → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc :=
          fun e gc mem => tyMs e gc (List.mem_cons_of_mem _ mem)
        have fRecvRest : ∀ pre e' gc' suf, rest = pre ++ (e', gc') :: suf →
            TLLC.Process.procOccurs (chanIndex e')
              (flattenChildren (.tm (N.eval (.recv (Term.chan d) .im))) suf) = 0 :=
          fun pre e' gc' suf h => eFreshRecv ((e, gc) :: pre) e' gc' suf (by rw [h]; rfl)
        have fRpairRest : ∀ pre e' gc' suf, rest = pre ++ (e', gc') :: suf →
            TLLC.Process.procOccurs (chanIndex e')
              (flattenChildren (.tm (N.eval (.pure (.pair payload (Term.chan d) .im .L)))) suf) = 0 :=
          fun pre e' gc' suf h => eFreshRpair ((e, gc) :: pre) e' gc' suf (by rw [h]; rfl)
        have innerStep := ih σ' tyRest fRecvRest fRpairRest
        simp only [flattenChildren, hgc,
          (show ∀ (p : Proc) (τ : Nat → Chan),
              (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
            from fun _ _ => rfl),
          (show ∀ (a b : Proc) (τ : Nat → Chan),
              (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
            from fun _ _ _ => rfl)]
        set Q1exp : Proc :=
          (GP[bindEndpointAt 0 gp; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 d);
            Term.var_Term][up_Chan_Chan (up_Chan_Chan σ); Term.var_Term])[TLLC.Process.exch;
            Term.var_Term] with hQ1exp
        -- leaf facts (algebra + freshness)
        -- shared substitution identity: ↑ then exch absorbs into σ' = σ >> ⟨↑⟩
        have key : ∀ (m : Term),
            (m[up_Chan_Chan σ; Term.var_Term])⟨((· + 1) : Nat → Nat);
              (id : Nat → Nat)⟩[TLLC.Process.exch; Term.var_Term]
              = m[up_Chan_Chan σ'; Term.var_Term] := by
          intro m
          rw [hσ']
          asimp
          congr 1
        have leafA :
            (Proc.tm (((M.eval (.app (.send (Term.chan c) .im) payload .im))[bindEndpointAt 0 c;
                Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))⟨((· + 1) : Nat → Nat);
                (id : Nat → Nat)⟩[TLLC.Process.exch; Term.var_Term]
              = Proc.tm (((M.eval (.app (.send (Term.chan c) .im) payload .im))[bindEndpointAt 0 c;
                Term.var_Term])[up_Chan_Chan σ'; Term.var_Term]) := by
          show Proc.tm _ = Proc.tm _; congr 1; exact key _
        have leafA' :
            (Proc.tm (((M.eval (.pure (Term.chan c)))[bindEndpointAt 0 c;
                Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))⟨((· + 1) : Nat → Nat);
                (id : Nat → Nat)⟩[TLLC.Process.exch; Term.var_Term]
              = Proc.tm (((M.eval (.pure (Term.chan c)))[bindEndpointAt 0 c;
                Term.var_Term])[up_Chan_Chan σ'; Term.var_Term]) := by
          show Proc.tm _ = Proc.tm _; congr 1; exact key _
        have leafPof : ∀ (R : Proc), TLLC.Process.procOccurs (chanIndex e) R = 0 →
            TLLC.Process.Congruence
              ((R[bindEndpointAt 0 e; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 d);
                Term.var_Term][up_Chan_Chan (up_Chan_Chan σ); Term.var_Term])[TLLC.Process.exch;
                Term.var_Term])
              (R[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ'; Term.var_Term]) := by
          intro R fresh
          rw [hσ']
          conv_lhs => simp only [asimp_lemmas]
          conv_rhs => simp only [asimp_lemmas]
          apply process_congr_csubst_of_eqv (i := chanIndex e) _ fresh
          intro x hx
          rcases eq_or_ne x (chanIndex d) with hxd | hxd
          · subst hxd
            simp [bindEndpointAt, scons, funcomp, asimp_lemmas, hx]
          · cases hσx : σ x with
            | var_Chan j =>
                simp [bindEndpointAt, scons, funcomp, asimp_lemmas, hx, hxd, hσx]
        have leafP := leafPof _ (eFreshRecv [] e gc rest rfl)
        have leafP' := leafPof _ (eFreshRpair [] e gc rest rfl)
        have parPush : ∀ (a b : Proc), (Proc.par a b)[TLLC.Process.exch; Term.var_Term]
            = Proc.par (a[TLLC.Process.exch; Term.var_Term]) (b[TLLC.Process.exch; Term.var_Term]) :=
          fun _ _ => rfl
        refine TLLC.Process.Step.congr ?cL
          (TLLC.Process.Step.res
            (process_step_scope_unused_right (q := Q1exp) ?q1zero innerStep)) ?cR
        case q1zero =>
          obtain ⟨r0, A0, tyA0, tyGc⟩ := tyMs e gc (by simp)
          have yFresh : ∀ i, TLLC.Process.procOccurs (i + 1)
              (GP[bindEndpointAt 0 gp; Term.var_Term]) = 0 := by
            intro i
            have hh := tyGc.flattenAt_occurs_succ tyA0 i
            rw [hgc] at hh
            exact hh
          rw [hQ1exp]
          apply procOccurs_csubst_zero; intro k hk
          obtain rfl : k = 1 := by
            rcases k with _ | _ | j <;> simp_all [Process.exch, cexch, scons]
          apply procOccurs_csubst_zero; intro k hk
          obtain rfl : k = 1 := by
            rcases k with _ | _ | j
            · simp_all [up_Chan_Chan, scons]
            · rfl
            · exfalso
              cases hσj : σ j with
              | var_Chan m =>
                  simp [up_Chan_Chan, scons, funcomp, asimp_lemmas, hσj] at hk
          apply procOccurs_csubst_zero; intro k hk
          rcases k with _ | j
          · simp [up_Chan_Chan, scons] at hk
          · exact yFresh j
        case cL =>
          refine ARS.conv_trans (process_congr_res process_congr_scope_right) ?_
          refine ARS.conv_trans process_congr_exch ?_
          simp only [parPush]
          refine ARS.conv_trans (process_congr_res (process_congr_res
            (ARS.conv1 (TLLC.Process.CongrProc.assoc)))) ?_
          refine process_congr_res (process_congr_res ?_)
          refine ARS.conv_trans (process_congr_parallel_left ?inner)
            (process_congr_parallel_right ?cQ)
          case inner =>
            refine ARS.conv_trans (process_congr_parallel_left ?cX)
              (process_congr_parallel_right leafP)
            case cX => rw [leafA]; exact ARS.Conv.refl
          case cQ => exact ARS.Conv.refl
        case cR =>
          refine ARS.conv_trans ?_
            (ARS.conv_sym (process_congr_res process_congr_scope_right))
          refine ARS.conv_trans ?_ (ARS.conv_sym process_congr_exch)
          simp only [parPush]
          refine ARS.conv_trans ?_ (ARS.conv_sym (process_congr_res (process_congr_res
            (ARS.conv1 (TLLC.Process.CongrProc.assoc)))))
          refine process_congr_res (process_congr_res ?_)
          refine ARS.conv_trans (process_congr_parallel_left ?inner)
            (process_congr_parallel_right ?cQ)
          case inner =>
            refine ARS.conv_trans (process_congr_parallel_left ?cX)
              (process_congr_parallel_right (ARS.conv_sym leafP'))
            case cX => rw [leafA']; exact ARS.Conv.refl
          case cQ => exact ARS.Conv.refl

/-- Core of lemma (B), implicit case: `comIm` fires through the receiver child's grandchildren
`flattenChildren (.tm (N op)) ms'`. Induct on `ms'`, extruding one grandchild nu per step
(`extrude_one_congr`); the exposed inner com is the IH at `σ⁺ = fun y => (σ y)⟨↑⟩` (with the `e`-slot
sent to `0`). `mFresh`: the parent body does not mention any grandchild edge (linearity). -/
lemma comIm_through_FC (M N : EvalCtx) (payload : Term) (c d : Chan)
    (imp : implicitPayload c d payload) :
    ∀ (ms' : List (Chan × Tree)),
    (∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc) →
    (∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .im) payload .im)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0) →
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      (.nu (.par
        (((Proc.tm (M.eval (.app (.send (Term.chan c) .im) payload .im)))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.recv (Term.chan d) .im))) ms')[bindEndpointAt 0 d;
          Term.var_Term][up_Chan_Chan σ; Term.var_Term])))
      (.nu (.par
        (((Proc.tm (M.eval (.pure (Term.chan c))))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.pure (.pair payload (Term.chan d) .im .L)))) ms')[
          bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term]))) := by
  intro ms'
  induction ms' with
  | nil =>
      intro _ _ σ
      simp only [flattenChildren_nil]
      exact process_step_comIm_edge_csubst (M := M) (N := N) (payloadTerm := payload)
        (c := c) (d := d) imp σ
  | cons edge ms'' ih =>
      rcases edge with ⟨e, gc⟩
      intro tyMs mFresh σ
      cases hg : gc.flattenAt with
      | mk dg gp =>
        simp only [flattenChildren, hg,
          (show ∀ (p : Proc) (τ : Nat → Chan),
              (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
            from fun _ _ => rfl),
          (show ∀ (a b : Proc) (τ : Nat → Chan),
              (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
            from fun _ _ _ => rfl)]
        refine TLLC.Process.Step.congr (extrude_one_congr _ _ _) ?_
          (ARS.conv_sym (extrude_one_congr _ _ _))
        refine TLLC.Process.Step.res (process_step_scope_unused_right ?gpFresh ?innerCom)
        case gpFresh =>
          obtain ⟨r', A', tyA', tgc⟩ := tyMs e gc (by simp)
          have hgp : ∀ i, TLLC.Process.procOccurs (i + 1)
              (gp[bindEndpointAt 0 dg; Term.var_Term]) = 0 := by
            intro i; simpa [hg] using tgc.flattenAt_occurs_succ tyA' i
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by rcases k with _ | _ | k <;> simp_all [Process.exch, cexch]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by
            rcases k with _ | _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · rfl
            · exfalso
              cases hσ : σ k with
              | var_Chan j => simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hkd : k = chanIndex d + 1 := by
            rcases k with _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · by_cases hkd : k = chanIndex d
              · subst hkd; rfl
              · exfalso
                simp_all [up_Chan_Chan, bindEndpointAt, chanIndex, scons, funcomp, asimp_lemmas]
          subst hkd
          exact hgp (chanIndex d)
        case innerCom =>
          have key := ih (fun e' gc' mem => tyMs e' gc' (List.mem_cons_of_mem _ mem))
            (fun e' gc' mem => mFresh e' gc' (List.mem_cons_of_mem _ mem))
            (fun y => if y = chanIndex e then Chan.var_Chan 0
                      else Chan.var_Chan (chanIndex (σ y) + 1))
          refine TLLC.Process.Step.congr ?congL key ?congR
          case congL =>
            apply process_congr_res
            refine ARS.conv_trans (process_congr_parallel_left ?cA)
              (process_congr_parallel_right ?cF)
            case cF =>
              have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
              asimp
              convert ARS.Conv.refl using 2
              funext x
              rcases eq_or_ne x (chanIndex d) with rfl | hxd
              · unfold bindEndpointAt
                simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case cA =>
              apply ARS.conv1
              apply TLLC.Process.CongrProc.tm
              asimp
              refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
                (fun _ => (mFresh e gc (by simp)).2.1)
              intro x hx
              rcases eq_or_ne x (chanIndex c) with rfl | hxc
              · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]
          case congR =>
            apply ARS.conv_sym
            apply process_congr_res
            refine ARS.conv_trans (process_congr_parallel_left ?cA')
              (process_congr_parallel_right ?cF')
            case cF' =>
              have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
              asimp
              convert ARS.Conv.refl using 2
              funext x
              rcases eq_or_ne x (chanIndex d) with rfl | hxd
              · unfold bindEndpointAt
                simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case cA' =>
              apply ARS.conv1
              apply TLLC.Process.CongrProc.tm
              asimp
              refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
                (fun _ => (mFresh e gc (by simp)).2.2)
              intro x hx
              rcases eq_or_ne x (chanIndex c) with rfl | hxc
              · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]

/-- Mirror of `comIm_through_FC` for implicit receive: the parent receives and the selected child
sends. Verbatim copy with the parent/child terms swapped and the symmetric base step. -/
lemma comIm_through_FC_symm (M N : EvalCtx) (payload : Term) (c d : Chan)
    (imp : implicitPayload c d payload) :
    ∀ (ms' : List (Chan × Tree)),
    (∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc) →
    (∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.recv (Term.chan c) .im)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (.pair payload (Term.chan c) .im .L))) = 0) →
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      (.nu (.par
        (((Proc.tm (M.eval (.recv (Term.chan c) .im)))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.app (.send (Term.chan d) .im) payload .im))) ms')[
          bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term])))
      (.nu (.par
        (((Proc.tm (M.eval (.pure (.pair payload (Term.chan c) .im .L))))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.pure (Term.chan d)))) ms')[
          bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term]))) := by
  intro ms'
  induction ms' with
  | nil =>
      intro _ _ σ
      simp only [flattenChildren_nil]
      exact process_step_comIm_edge_symm_csubst (M := M) (N := N) (payloadTerm := payload)
        (c := c) (d := d) imp σ
  | cons edge ms'' ih =>
      rcases edge with ⟨e, gc⟩
      intro tyMs mFresh σ
      cases hg : gc.flattenAt with
      | mk dg gp =>
        simp only [flattenChildren, hg,
          (show ∀ (p : Proc) (τ : Nat → Chan),
              (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
            from fun _ _ => rfl),
          (show ∀ (a b : Proc) (τ : Nat → Chan),
              (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
            from fun _ _ _ => rfl)]
        refine TLLC.Process.Step.congr (extrude_one_congr _ _ _) ?_
          (ARS.conv_sym (extrude_one_congr _ _ _))
        refine TLLC.Process.Step.res (process_step_scope_unused_right ?gpFresh ?innerCom)
        case gpFresh =>
          obtain ⟨r', A', tyA', tgc⟩ := tyMs e gc (by simp)
          have hgp : ∀ i, TLLC.Process.procOccurs (i + 1)
              (gp[bindEndpointAt 0 dg; Term.var_Term]) = 0 := by
            intro i; simpa [hg] using tgc.flattenAt_occurs_succ tyA' i
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by rcases k with _ | _ | k <;> simp_all [Process.exch, cexch]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by
            rcases k with _ | _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · rfl
            · exfalso
              cases hσ : σ k with
              | var_Chan j => simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hkd : k = chanIndex d + 1 := by
            rcases k with _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · by_cases hkd : k = chanIndex d
              · subst hkd; rfl
              · exfalso
                simp_all [up_Chan_Chan, bindEndpointAt, chanIndex, scons, funcomp, asimp_lemmas]
          subst hkd
          exact hgp (chanIndex d)
        case innerCom =>
          have key := ih (fun e' gc' mem => tyMs e' gc' (List.mem_cons_of_mem _ mem))
            (fun e' gc' mem => mFresh e' gc' (List.mem_cons_of_mem _ mem))
            (fun y => if y = chanIndex e then Chan.var_Chan 0
                      else Chan.var_Chan (chanIndex (σ y) + 1))
          refine TLLC.Process.Step.congr ?congL key ?congR
          case congL =>
            apply process_congr_res
            refine ARS.conv_trans (process_congr_parallel_left ?cA)
              (process_congr_parallel_right ?cF)
            case cF =>
              have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
              asimp
              convert ARS.Conv.refl using 2
              funext x
              rcases eq_or_ne x (chanIndex d) with rfl | hxd
              · unfold bindEndpointAt
                simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case cA =>
              apply ARS.conv1
              apply TLLC.Process.CongrProc.tm
              asimp
              refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
                (fun _ => (mFresh e gc (by simp)).2.1)
              intro x hx
              rcases eq_or_ne x (chanIndex c) with rfl | hxc
              · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]
          case congR =>
            apply ARS.conv_sym
            apply process_congr_res
            refine ARS.conv_trans (process_congr_parallel_left ?cA')
              (process_congr_parallel_right ?cF')
            case cF' =>
              have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
              asimp
              convert ARS.Conv.refl using 2
              funext x
              rcases eq_or_ne x (chanIndex d) with rfl | hxd
              · unfold bindEndpointAt
                simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case cA' =>
              apply ARS.conv1
              apply TLLC.Process.CongrProc.tm
              asimp
              refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
                (fun _ => (mFresh e gc (by simp)).2.2)
              intro x hx
              rcases eq_or_ne x (chanIndex c) with rfl | hxc
              · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]

/-- Base of the implicit-send last-edge step: the selected child is the only one. Combines
`comIm_through_FC` (through the child's grandchildren `ms'`) with `step_par_parAll_spectators`
(the child's subtrees `qs'` as parallel spectators). -/
lemma sendIm_base_step (M N : EvalCtx) (o : Term) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (imp : implicitPayload c d o)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .im) o .im)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .im) o .im)))
        [(c, .node d (N.eval (.recv (Term.chan d) .im)) ms' qs')])[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (Term.chan c))))
        [(c, .node d (N.eval (.pure (.pair o (Term.chan d) .im .L))) ms' qs')])[σ;
          Term.var_Term]) := by
  simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, flattenBody, parAll_csubst,
    (show ∀ (p : Proc) (τ : Nat → Chan),
        (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
      from fun _ _ => rfl),
    (show ∀ (a b : Proc) (τ : Nat → Chan),
        (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
      from fun _ _ _ => rfl)]
  refine step_par_parAll_spectators _ _ _ _ _ ?ssZero
    (comIm_through_FC M N o c d imp ms' tyMs mFresh σ)
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨q1, ⟨q0, hq0mem, rfl⟩, rfl⟩ := hq
  apply procOccurs_csubst_zero; intro k _
  apply procOccurs_csubst_zero; intro j _
  exact qsZero q0 hq0mem j

/-- The implicit-send last-edge step over the `before` siblings (the selected child is last). -/
lemma sendIm_over_before (M N : EvalCtx) (o : Term) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (imp : implicitPayload c d o)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .im) o .im)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (before : List (Chan × Tree)) :
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .im) o .im)))
        (before ++ [(c, .node d (N.eval (.recv (Term.chan d) .im)) ms' qs')]))[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (Term.chan c))))
        (before ++ [(c, .node d (N.eval (.pure (.pair o (Term.chan d) .im .L))) ms' qs')]))[σ;
          Term.var_Term]) := by
  induction before with
  | nil =>
      intro σ
      simpa using sendIm_base_step M N o c d ms' qs' imp tyMs mFresh qsZero σ
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f p =>
          have tailStep := ih (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := p[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                tailStep)
            using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

/-- The full implicit-send children-body step: move the selected child to last (congruence), then
fire the last-edge step. This is `bodyStep` for the rootSendIm/nodeSendIm cases. -/
lemma sendIm_bodyStep (M N : EvalCtx) (o : Term) (c d : Chan)
    (ms' qs' : _) (l r : List (Chan × Tree))
    (imp : implicitPayload c d o)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .im) o .im)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (tyChild : ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
        (Tree.node d (N.eval (.recv (Term.chan d) .im)) ms' qs'))
    (tyR : ∀ e sib, (e, sib) ∈ r → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (distinctR : ∀ e sib, (e, sib) ∈ r → chanIndex c ≠ chanIndex e)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .im) o .im)))
        (l ++ (c, .node d (N.eval (.recv (Term.chan d) .im)) ms' qs') :: r))[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (Term.chan c))))
        ((l ++ r) ++ [(c, .node d (N.eval (.pure (.pair o (Term.chan d) .im .L))) ms' qs')]))[σ;
          Term.var_Term]) := by
  refine TLLC.Process.Step.congr ?_
    (sendIm_over_before M N o c d ms' qs' imp tyMs mFresh qsZero (l ++ r) σ) ARS.Conv.refl
  exact process_congr_csubst
    (flattenChildren_move_to_last (.tm (M.eval (.app (.send (Term.chan c) .im) o .im)))
      c (Tree.node d (N.eval (.recv (Term.chan d) .im)) ms' qs') l r tyChild tyR distinctR) σ

/-- Mirror of `sendIm_base_step` for implicit receive. -/
lemma recvIm_base_step (M N : EvalCtx) (o : Term) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (imp : implicitPayload c d o)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.recv (Term.chan c) .im)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (.pair o (Term.chan c) .im .L))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.recv (Term.chan c) .im)))
        [(c, .node d (N.eval (.app (.send (Term.chan d) .im) o .im)) ms' qs')])[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (.pair o (Term.chan c) .im .L))))
        [(c, .node d (N.eval (.pure (Term.chan d))) ms' qs')])[σ;
          Term.var_Term]) := by
  simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, flattenBody, parAll_csubst,
    (show ∀ (p : Proc) (τ : Nat → Chan),
        (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
      from fun _ _ => rfl),
    (show ∀ (a b : Proc) (τ : Nat → Chan),
        (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
      from fun _ _ _ => rfl)]
  refine step_par_parAll_spectators _ _ _ _ _ ?ssZero
    (comIm_through_FC_symm M N o c d imp ms' tyMs mFresh σ)
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨q1, ⟨q0, hq0mem, rfl⟩, rfl⟩ := hq
  apply procOccurs_csubst_zero; intro k _
  apply procOccurs_csubst_zero; intro j _
  exact qsZero q0 hq0mem j

/-- The implicit-receive last-edge step over the `before` siblings (the selected child is last). -/
lemma recvIm_over_before (M N : EvalCtx) (o : Term) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (imp : implicitPayload c d o)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.recv (Term.chan c) .im)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (.pair o (Term.chan c) .im .L))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (before : List (Chan × Tree)) :
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.recv (Term.chan c) .im)))
        (before ++
          [(c, .node d (N.eval (.app (.send (Term.chan d) .im) o .im)) ms' qs')]))[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (.pair o (Term.chan c) .im .L))))
        (before ++ [(c, .node d (N.eval (.pure (Term.chan d))) ms' qs')]))[σ;
          Term.var_Term]) := by
  induction before with
  | nil =>
      intro σ
      simpa using recvIm_base_step M N o c d ms' qs' imp tyMs mFresh qsZero σ
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f p =>
          have tailStep := ih (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := p[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                tailStep)
            using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

/-- The full implicit-receive children-body step. This is `bodyStep` for the rootRecvIm/nodeRecvIm
cases. -/
lemma recvIm_bodyStep (M N : EvalCtx) (o : Term) (c d : Chan)
    (ms' qs' : _) (l r : List (Chan × Tree))
    (imp : implicitPayload c d o)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.recv (Term.chan c) .im)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (.pair o (Term.chan c) .im .L))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (tyChild : ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
        (Tree.node d (N.eval (.app (.send (Term.chan d) .im) o .im)) ms' qs'))
    (tyR : ∀ e sib, (e, sib) ∈ r → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (distinctR : ∀ e sib, (e, sib) ∈ r → chanIndex c ≠ chanIndex e)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.recv (Term.chan c) .im)))
        (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .im) o .im)) ms' qs') :: r))[σ;
          Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (.pair o (Term.chan c) .im .L))))
        ((l ++ r) ++ [(c, .node d (N.eval (.pure (Term.chan d))) ms' qs')]))[σ;
          Term.var_Term]) := by
  refine TLLC.Process.Step.congr ?_
    (recvIm_over_before M N o c d ms' qs' imp tyMs mFresh qsZero (l ++ r) σ) ARS.Conv.refl
  exact process_congr_csubst
    (flattenChildren_move_to_last (.tm (M.eval (.recv (Term.chan c) .im)))
      c (Tree.node d (N.eval (.app (.send (Term.chan d) .im) o .im)) ms' qs') l r
      tyChild tyR distinctR) σ

/-- The implicit-receive body term and its post-step pure-pair form have the same channel
occurrences: the implicit payload is erased, both reduce to `chan c` in the hole. -/
lemma recvIm_term_occurs_eq (M : EvalCtx) (c : Chan) (o : Term) (i : Nat) :
    occurs i (M.eval (.recv (Term.chan c) .im)) =
      occurs i (M.eval (.pure (.pair o (Term.chan c) .im .L))) := by
  induction M with
  | hole => cases c with | var_Chan x => simp [EvalCtx.eval, occurs]
  | bnd M n ih => simp [EvalCtx.eval, occurs, ih]
/-- The close edge step threaded through the selected child's grandchildren `ms'`. The parent `nu`
is removed by the close; the child's flattened body (close consumed → `pure one`, grandchildren
preserved) floats out as a parallel process. -/
lemma end_through_FC (M N : EvalCtx) (c d : Chan)
    (pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0)
    (cUnused : occurs (chanIndex d) (N.eval (.pure .one)) = 0) :
    ∀ (ms' : List (Chan × Tree)),
    (∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc) →
    (∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.close true (Term.chan c))) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure .one)) = 0) →
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      (.nu (.par
        (((Proc.tm (M.eval (.close true (Term.chan c))))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.close false (Term.chan d)))) ms')[bindEndpointAt 0 d;
          Term.var_Term][up_Chan_Chan σ; Term.var_Term])))
      (.par
        ((Proc.tm (M.eval (.pure .one)))[σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.pure .one))) ms')[σ; Term.var_Term])) := by
  intro ms'
  induction ms' with
  | nil =>
      intro _ _ σ
      simp only [flattenChildren_nil]
      exact process_step_end_final_csubst (M := M) (N := N) (c := c) (d := d) pUnused cUnused σ
  | cons edge ms'' ih =>
      rcases edge with ⟨e, gc⟩
      intro tyMs mFresh σ
      cases hg : gc.flattenAt with
      | mk dg gp =>
        simp only [flattenChildren, hg,
          (show ∀ (p : Proc) (τ : Nat → Chan),
              (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
            from fun _ _ => rfl),
          (show ∀ (a b : Proc) (τ : Nat → Chan),
              (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
            from fun _ _ _ => rfl)]
        refine TLLC.Process.Step.congr (extrude_one_congr _ _ _)
          (TLLC.Process.Step.res
            (process_step_scope_remove_unused_right ?gpFresh
              (TLLC.Process.Step.congr ?cL
                (ih (fun e' gc' mem => tyMs e' gc' (List.mem_cons_of_mem _ mem))
                    (fun e' gc' mem => mFresh e' gc' (List.mem_cons_of_mem _ mem))
                    (fun y => if y = chanIndex e then Chan.var_Chan 0
                              else Chan.var_Chan (chanIndex (σ y) + 1)))
                ARS.Conv.refl)))
          ?rhsConv
        case gpFresh =>
          obtain ⟨r', A', tyA', tgc⟩ := tyMs e gc (by simp)
          have hgp : ∀ i, TLLC.Process.procOccurs (i + 1)
              (gp[bindEndpointAt 0 dg; Term.var_Term]) = 0 := by
            intro i; simpa [hg] using tgc.flattenAt_occurs_succ tyA' i
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by rcases k with _ | _ | k <;> simp_all [Process.exch, cexch]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by
            rcases k with _ | _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · rfl
            · exfalso
              cases hσ : σ k with
              | var_Chan j => simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hkd : k = chanIndex d + 1 := by
            rcases k with _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · by_cases hkd : k = chanIndex d
              · subst hkd; rfl
              · exfalso
                simp_all [up_Chan_Chan, bindEndpointAt, chanIndex, scons, funcomp, asimp_lemmas]
          subst hkd
          exact hgp (chanIndex d)
        case cL =>
          apply process_congr_res
          refine ARS.conv_trans (process_congr_parallel_left ?cA)
            (process_congr_parallel_right ?cF)
          case cF =>
            have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
            asimp
            convert ARS.Conv.refl using 2
            funext x
            clear ih pUnused cUnused tyMs mFresh
            rcases eq_or_ne x (chanIndex d) with rfl | hxd
            · unfold bindEndpointAt
              simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
            rcases eq_or_ne x (chanIndex e) with rfl | hxe
            · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            · cases hσ : σ x with
              | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
          case cA =>
            apply ARS.conv1
            apply TLLC.Process.CongrProc.tm
            asimp
            refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
              (fun _ => (mFresh e gc (by simp)).2.1)
            intro x hx
            rcases eq_or_ne x (chanIndex c) with rfl | hxc
            · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
            · cases hσ : σ x with
              | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]
        case rhsConv =>
          refine ARS.conv_trans
            (process_congr_res (ARS.conv1i TLLC.Process.CongrProc.assoc)) ?_
          refine ARS.conv_trans (process_congr_scope_out_left ?Afresh) ?_
          case Afresh =>
            apply procOccurs_csubst_zero
            intro k hk
            by_cases hke : k = chanIndex e
            · subst hke; exact (mFresh e gc (by simp)).2.2
            · exfalso; simp [hke, Chan.var_Chan.injEq] at hk
          refine ARS.conv_trans
            (process_congr_parallel_left ?Mpart)
            (process_congr_parallel_right ?nupart)
          case Mpart =>
            apply ARS.conv1
            apply TLLC.Process.CongrProc.tm
            asimp
            refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
              (fun _ => (mFresh e gc (by simp)).2.2)
            intro x hx
            cases hσ : σ x with
            | var_Chan k => simp_all [chanIndex, asimp_lemmas, funcomp]
          case nupart =>
            apply process_congr_res
            refine ARS.conv_trans
              (process_congr_parallel_left ?Bpart)
              (process_congr_parallel_right ?Cpart)
            case Bpart =>
              asimp
              convert ARS.Conv.refl using 2
              funext x
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case Cpart =>
              obtain ⟨r', A', tyA', tgc⟩ := tyMs e gc (by simp)
              have hgp : ∀ i, TLLC.Process.procOccurs (i + 1)
                  (gp[bindEndpointAt 0 dg; Term.var_Term]) = 0 := by
                intro i; simpa [hg] using tgc.flattenAt_occurs_succ tyA' i
              generalize gp[bindEndpointAt 0 dg; Term.var_Term] = q at hgp ⊢
              asimp
              apply process_congr_csubst_of_occurs
              intro k hk
              rcases k with _ | k
              · simp [scons, asimp_lemmas]
              · exact absurd (hgp k) hk

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

/-- The detached child's flattened body is a closed process. -/
lemma TypedAt.close_detached_occurs0 {N : EvalCtx} {b : Bool} {d : Chan}
    {ms' : List (Chan × Tree)} {qs' : List Tree} {r : Bool} {A : Term}
    (typed : TypedAt r A (.node d (N.eval (.close b (Term.chan d))) ms' qs')) (i : Nat) :
    TLLC.Process.procOccurs i (flattenBody (N.eval (.pure .one)) ms' qs') = 0 := by
  simpa using typed.close_detached_typed.flatten_occurs0 i

/-- A raw renaming is the substitution by the corresponding variable-valued map. -/
lemma process_cren_eq_csubst (p : Proc) (ξ : Nat → Nat) :
    p⟨ξ; (id : Nat → Nat)⟩ = p[fun x => Chan.var_Chan (ξ x); Term.var_Term] := by
  rw [← process_csubst_cren]
  rfl

/-- A closed process is congruent across any substitution-then-renaming instance. -/
lemma process_congr_closed_subst_cren {q : Proc}
    (closed : ∀ i, TLLC.Process.procOccurs i q = 0)
    (τ1 τ2 : Nat → Chan) (ξ : Nat → Nat) :
    TLLC.Process.Congruence
      ((q[τ1; Term.var_Term])⟨ξ; (id : Nat → Nat)⟩)
      (q[τ2; Term.var_Term]) := by
  rw [process_cren_eq_csubst]
  asimp
  exact process_congr_csubst_of_occurs (fun k hk => absurd (closed k) hk)

/-- Two-substitution variant of `process_congr_closed_subst_cren`. -/
lemma process_congr_closed_subst2_cren {q : Proc}
    (closed : ∀ i, TLLC.Process.procOccurs i q = 0)
    (τ0 τ1 τ2 : Nat → Chan) (ξ : Nat → Nat) :
    TLLC.Process.Congruence
      ((q[τ0; Term.var_Term][τ1; Term.var_Term])⟨ξ; (id : Nat → Nat)⟩)
      (q[τ2; Term.var_Term]) := by
  rw [process_cren_eq_csubst]
  asimp
  exact process_congr_csubst_of_occurs (fun k hk => absurd (closed k) hk)

/-- Pointwise congruence of mapped spectator lists under `parAll`. -/
lemma process_congr_parAll_map_pointwise {α : Type _} (body : Proc) (f g : α → Proc)
    (l : List α) (h : ∀ x, x ∈ l → TLLC.Process.Congruence (f x) (g x)) :
    TLLC.Process.Congruence (parAll body (l.map f)) (parAll body (l.map g)) := by
  induction l generalizing body with
  | nil => exact ARS.Conv.refl
  | cons x l ih =>
      simp only [List.map_cons, parAll_cons]
      exact ARS.conv_trans
        (process_congr_parAll_accumulator (l.map f)
          (process_congr_parallel_right (h x (by simp))))
        (ih (.par body (g x)) (fun y hy => h y (by simp [hy])))

/-- Mirror of `end_through_FC` with the closing polarities swapped: the parent waits
(`close false`) and the selected child closes (`close true`). -/
lemma end_through_FC_symm (M N : EvalCtx) (c d : Chan)
    (pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0)
    (cUnused : occurs (chanIndex d) (N.eval (.pure .one)) = 0) :
    ∀ (ms' : List (Chan × Tree)),
    (∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc) →
    (∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.close false (Term.chan c))) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure .one)) = 0) →
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      (.nu (.par
        (((Proc.tm (M.eval (.close false (Term.chan c))))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.close true (Term.chan d)))) ms')[bindEndpointAt 0 d;
          Term.var_Term][up_Chan_Chan σ; Term.var_Term])))
      (.par
        ((Proc.tm (M.eval (.pure .one)))[σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.pure .one))) ms')[σ; Term.var_Term])) := by
  intro ms'
  induction ms' with
  | nil =>
      intro _ _ σ
      simp only [flattenChildren_nil]
      exact process_step_end_final_symm_csubst (M := M) (N := N) (c := c) (d := d)
        pUnused cUnused σ
  | cons edge ms'' ih =>
      rcases edge with ⟨e, gc⟩
      intro tyMs mFresh σ
      cases hg : gc.flattenAt with
      | mk dg gp =>
        simp only [flattenChildren, hg,
          (show ∀ (p : Proc) (τ : Nat → Chan),
              (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
            from fun _ _ => rfl),
          (show ∀ (a b : Proc) (τ : Nat → Chan),
              (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
            from fun _ _ _ => rfl)]
        refine TLLC.Process.Step.congr (extrude_one_congr _ _ _)
          (TLLC.Process.Step.res
            (process_step_scope_remove_unused_right ?gpFresh
              (TLLC.Process.Step.congr ?cL
                (ih (fun e' gc' mem => tyMs e' gc' (List.mem_cons_of_mem _ mem))
                    (fun e' gc' mem => mFresh e' gc' (List.mem_cons_of_mem _ mem))
                    (fun y => if y = chanIndex e then Chan.var_Chan 0
                              else Chan.var_Chan (chanIndex (σ y) + 1)))
                ARS.Conv.refl)))
          ?rhsConv
        case gpFresh =>
          obtain ⟨r', A', tyA', tgc⟩ := tyMs e gc (by simp)
          have hgp : ∀ i, TLLC.Process.procOccurs (i + 1)
              (gp[bindEndpointAt 0 dg; Term.var_Term]) = 0 := by
            intro i; simpa [hg] using tgc.flattenAt_occurs_succ tyA' i
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by rcases k with _ | _ | k <;> simp_all [Process.exch, cexch]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by
            rcases k with _ | _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · rfl
            · exfalso
              cases hσ : σ k with
              | var_Chan j => simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hkd : k = chanIndex d + 1 := by
            rcases k with _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · by_cases hkd : k = chanIndex d
              · subst hkd; rfl
              · exfalso
                simp_all [up_Chan_Chan, bindEndpointAt, chanIndex, scons, funcomp, asimp_lemmas]
          subst hkd
          exact hgp (chanIndex d)
        case cL =>
          apply process_congr_res
          refine ARS.conv_trans (process_congr_parallel_left ?cA)
            (process_congr_parallel_right ?cF)
          case cF =>
            have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
            asimp
            convert ARS.Conv.refl using 2
            funext x
            clear ih pUnused cUnused tyMs mFresh
            rcases eq_or_ne x (chanIndex d) with rfl | hxd
            · unfold bindEndpointAt
              simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
            rcases eq_or_ne x (chanIndex e) with rfl | hxe
            · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            · cases hσ : σ x with
              | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
          case cA =>
            apply ARS.conv1
            apply TLLC.Process.CongrProc.tm
            asimp
            refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
              (fun _ => (mFresh e gc (by simp)).2.1)
            intro x hx
            rcases eq_or_ne x (chanIndex c) with rfl | hxc
            · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
            · cases hσ : σ x with
              | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]
        case rhsConv =>
          refine ARS.conv_trans
            (process_congr_res (ARS.conv1i TLLC.Process.CongrProc.assoc)) ?_
          refine ARS.conv_trans (process_congr_scope_out_left ?Afresh) ?_
          case Afresh =>
            apply procOccurs_csubst_zero
            intro k hk
            by_cases hke : k = chanIndex e
            · subst hke; exact (mFresh e gc (by simp)).2.2
            · exfalso; simp [hke, Chan.var_Chan.injEq] at hk
          refine ARS.conv_trans
            (process_congr_parallel_left ?Mpart)
            (process_congr_parallel_right ?nupart)
          case Mpart =>
            apply ARS.conv1
            apply TLLC.Process.CongrProc.tm
            asimp
            refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
              (fun _ => (mFresh e gc (by simp)).2.2)
            intro x hx
            cases hσ : σ x with
            | var_Chan k => simp_all [chanIndex, asimp_lemmas, funcomp]
          case nupart =>
            apply process_congr_res
            refine ARS.conv_trans
              (process_congr_parallel_left ?Bpart)
              (process_congr_parallel_right ?Cpart)
            case Bpart =>
              asimp
              convert ARS.Conv.refl using 2
              funext x
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case Cpart =>
              obtain ⟨r', A', tyA', tgc⟩ := tyMs e gc (by simp)
              have hgp : ∀ i, TLLC.Process.procOccurs (i + 1)
                  (gp[bindEndpointAt 0 dg; Term.var_Term]) = 0 := by
                intro i; simpa [hg] using tgc.flattenAt_occurs_succ tyA' i
              generalize gp[bindEndpointAt 0 dg; Term.var_Term] = q at hgp ⊢
              asimp
              apply process_congr_csubst_of_occurs
              intro k hk
              rcases k with _ | k
              · simp [scons, asimp_lemmas]
              · exact absurd (hgp k) hk

/-- Boolean-dispatching wrapper for the end edge: parent `close b` against child `close !b`. -/
lemma end_through_FC_bool (M N : EvalCtx) (b : Bool) (c d : Chan)
    (pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0)
    (cUnused : occurs (chanIndex d) (N.eval (.pure .one)) = 0) :
    ∀ (ms' : List (Chan × Tree)),
    (∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc) →
    (∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.close b (Term.chan c))) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure .one)) = 0) →
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      (.nu (.par
        (((Proc.tm (M.eval (.close b (Term.chan c))))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.close (!b) (Term.chan d)))) ms')[bindEndpointAt 0 d;
          Term.var_Term][up_Chan_Chan σ; Term.var_Term])))
      (.par
        ((Proc.tm (M.eval (.pure .one)))[σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.pure .one))) ms')[σ; Term.var_Term])) := by
  cases b
  · exact end_through_FC_symm M N c d pUnused cUnused
  · exact end_through_FC M N c d pUnused cUnused

/-- The end edge fires on a singleton child list; the detached child body floats out in parallel. -/
lemma end_base_step (M N : EvalCtx) (b : Bool) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0)
    (cUnused : occurs (chanIndex d) (N.eval (.pure .one)) = 0)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.close b (Term.chan c))) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure .one)) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.close b (Term.chan c))))
        [(c, .node d (N.eval (.close (!b) (Term.chan d))) ms' qs')])[σ; Term.var_Term])
      (.par
        ((Proc.tm (M.eval (.pure .one)))[σ; Term.var_Term])
        ((flattenBody (N.eval (.pure .one)) ms' qs')[σ; Term.var_Term])) := by
  simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, flattenBody, parAll_csubst,
    List.map_map,
    (show ∀ (p : Proc) (τ : Nat → Chan),
        (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
      from fun _ _ => rfl),
    (show ∀ (a b : Proc) (τ : Nat → Chan),
        (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
      from fun _ _ _ => rfl)]
  refine TLLC.Process.Step.congr
    (process_congr_res (process_congr_par_parAll_right _ _ _))
    (process_step_scope_remove_parAll_right _ ?ssZero
      (end_through_FC_bool M N b c d pUnused cUnused ms' tyMs mFresh σ))
    ?rhs
  case ssZero =>
    intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    apply procOccurs_csubst_zero; intro k _
    apply procOccurs_csubst_zero; intro j _
    exact qsZero q0 hq0 j
  case rhs =>
    refine ARS.conv_trans (ARS.conv_sym (process_congr_par_parAll_right _ _ _)) ?_
    refine process_congr_parallel_right ?_
    rw [List.map_map]
    exact process_congr_parAll_map_pointwise _ _ _ (flattenSubtrees qs')
      (fun q0 hq0 => process_congr_closed_subst2_cren (fun i => qsZero q0 hq0 i) _ _ _ _)

/-- The end step over the `before` siblings (the selected child is last); the detached child body
extrudes past every sibling binder. -/
lemma end_over_before (M N : EvalCtx) (b : Bool) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0)
    (cUnused : occurs (chanIndex d) (N.eval (.pure .one)) = 0)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.close b (Term.chan c))) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure .one)) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (detachedZero : ∀ i, TLLC.Process.procOccurs i
      (flattenBody (N.eval (.pure .one)) ms' qs') = 0)
    (before : List (Chan × Tree)) :
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.close b (Term.chan c))))
        (before ++ [(c, .node d (N.eval (.close (!b) (Term.chan d))) ms' qs')]))[σ;
          Term.var_Term])
      (.par
        ((flattenChildren (.tm (M.eval (.pure .one))) before)[σ; Term.var_Term])
        ((flattenBody (N.eval (.pure .one)) ms' qs')[σ; Term.var_Term])) := by
  induction before with
  | nil =>
      intro σ
      simpa using end_base_step M N b c d ms' qs' pUnused cUnused tyMs mFresh qsZero σ
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f sp =>
          have tailStep := ih (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert TLLC.Process.Step.congr ARS.Conv.refl
            (TLLC.Process.Step.res
              (process_step_parallel_left
                (r := sp[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                tailStep)) ?cR using 1
          · simp [flattenChildren, siblingAt]
            asimp
          case cR =>
            refine ARS.conv_trans (process_congr_res process_congr_swap_right) ?_
            refine ARS.conv_trans (process_congr_scope_out_right
              (procOccurs_csubst_zero (fun k _ => detachedZero k))) ?_
            refine ARS.conv_trans (process_congr_parallel_right
              (process_congr_closed_subst_cren detachedZero _ σ _)) ?_
            refine process_congr_parallel_left ?_
            have hY : (flattenChildren (.tm (M.eval (.pure .one))) ((e, sibling) :: before))[σ;
                Term.var_Term]
                = .nu (.par
                  ((flattenChildren (.tm (M.eval (.pure .one))) before)[fun x =>
                    (bindEndpointAt 0 e x)[up_Chan_Chan σ]; Term.var_Term])
                  (sp[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])) := by
              simp [flattenChildren, siblingAt]
              asimp
            rw [hY]
            exact ARS.Conv.refl

/-- The full end children-body step: move the selected child to last, then fire the end edge.
This is `bodyStep` for the wait/close cases. -/
lemma end_bodyStep (M N : EvalCtx) (b : Bool) (c d : Chan)
    (ms' qs' : _) (l r : List (Chan × Tree))
    (pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0)
    (cUnused : occurs (chanIndex d) (N.eval (.pure .one)) = 0)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.close b (Term.chan c))) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure .one)) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (detachedZero : ∀ i, TLLC.Process.procOccurs i
      (flattenBody (N.eval (.pure .one)) ms' qs') = 0)
    (tyChild : ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
        (Tree.node d (N.eval (.close (!b) (Term.chan d))) ms' qs'))
    (tyR : ∀ e sib, (e, sib) ∈ r → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (distinctR : ∀ e sib, (e, sib) ∈ r → chanIndex c ≠ chanIndex e)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.close b (Term.chan c))))
        (l ++ (c, .node d (N.eval (.close (!b) (Term.chan d))) ms' qs') :: r))[σ; Term.var_Term])
      (.par
        ((flattenChildren (.tm (M.eval (.pure .one))) (l ++ r))[σ; Term.var_Term])
        ((flattenBody (N.eval (.pure .one)) ms' qs')[σ; Term.var_Term])) := by
  refine TLLC.Process.Step.congr ?_
    (end_over_before M N b c d ms' qs' pUnused cUnused tyMs mFresh qsZero detachedZero
      (l ++ r) σ) ARS.Conv.refl
  exact process_congr_csubst
    (flattenChildren_move_to_last (.tm (M.eval (.close b (Term.chan c))))
      c (Tree.node d (N.eval (.close (!b) (Term.chan d))) ms' qs') l r tyChild tyR distinctR) σ

/-- Occurrences of a plugged eval context decompose into context and hole parts. -/
lemma evalctx_occurs_plug (M : EvalCtx) (X : Term) (i : Nat) :
    occurs i (M.eval X) = occurs i (M.eval (.pure .one)) + occurs i X := by
  induction M with
  | hole => simp [EvalCtx.eval, occurs]
  | bnd M n ih =>
      simp [EvalCtx.eval, occurs, ih]
      omega

/-- A raw channel renaming of a term is the substitution by the variable-valued map. -/
lemma term_cren_eq_csubst (m : Term) (ξ : Nat → Nat) :
    m⟨ξ; (id : Nat → Nat)⟩ = m[fun x => Chan.var_Chan (ξ x); Term.var_Term] := by
  rw [← TLLC.Static.csubst_cren]
  rfl

/-- `CongrTerm` is closed under simultaneous channel/term substitution. -/
lemma congrTerm_subst {r : Rlv} {m m' : Term} (e : TLLC.Process.CongrTerm r m m') :
    ∀ (σ : Nat → Chan) (θ : Nat → Term),
      TLLC.Process.CongrTerm r (m[σ; θ]) (m'[σ; θ]) := by
  induction e with
  | var =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.refl _ _
  | srt =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.srt
  | pi eA eB ihA ihB =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.pi (ihA _ _) (ihB _ _)
  | lam eA em ihA ihm =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.lam (ihA _ _) (ihm _ _)
  | app em en ihm ihn =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.app (ihm _ _) (ihn _ _)
  | sig eA eB ihA ihB =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.sig (ihA _ _) (ihB _ _)
  | pair em en ihm ihn =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.pair (ihm _ _) (ihn _ _)
  | proj eC em en ihC ihm ihn =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.proj (ihC _ _) (ihm _ _) (ihn _ _)
  | fix eA em ihA ihm =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.fix (ihA _ _) (ihm _ _)
  | unit =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.unit
  | one =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.one
  | bool =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.bool
  | tt =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.tt
  | ff =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.ff
  | ite eA em en1 en2 ihA ihm ihn1 ihn2 =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.ite (ihA _ _) (ihm _ _) (ihn1 _ _) (ihn2 _ _)
  | M eA ihA =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.M (ihA _ _)
  | pure em ihm =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.pure (ihm _ _)
  | mlet em en ihm ihn =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.mlet (ihm _ _) (ihn _ _)
  | proto =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.proto
  | stop =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.stop
  | act eA eB ihA ihB =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.act (ihA _ _) (ihB _ _)
  | ch eA ihA =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.ch (ihA _ _)
  | chan_im =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.chan_im
  | chan_ex =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.chan_ex
  | fork eA em ihA ihm =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.fork (ihA _ _) (ihm _ _)
  | recv em ihm =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.recv (ihm _ _)
  | send em ihm =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.send (ihm _ _)
  | close em ihm =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.close (ihm _ _)
  | box =>
      intro σ θ
      asimp
      exact TLLC.Process.CongrTerm.box

/-- Renamed eval contexts around a fixed hole are `CongrTerm`-congruent when the renamings agree
off a channel absent from the context. -/
lemma congrTerm_evalctx_cren_agree (M : EvalCtx) (X : Term) (i : Nat) (ξ1 ξ2 : Nat → Nat)
    (agree : ∀ x, x ≠ i → ξ1 x = ξ2 x)
    (fresh : occurs i (M.eval (.pure .one)) = 0) :
    TLLC.Process.CongrTerm .ex ((M.cren ξ1).eval X) ((M.cren ξ2).eval X) := by
  induction M with
  | hole => exact TLLC.Process.CongrTerm.refl _ _
  | bnd M n ih =>
      have hsplit : occurs i (M.eval (.pure .one)) = 0 ∧ occurs i n = 0 := by
        have h := fresh
        simp [EvalCtx.eval, occurs] at h
        omega
      show TLLC.Process.CongrTerm .ex
        (.mlet ((M.cren ξ1).eval X) (n⟨ξ1; (id : Nat → Nat)⟩))
        (.mlet ((M.cren ξ2).eval X) (n⟨ξ2; (id : Nat → Nat)⟩))
      refine TLLC.Process.CongrTerm.mlet (ih hsplit.1) ?_
      rw [term_cren_eq_csubst n ξ1, term_cren_eq_csubst n ξ2]
      exact congrTerm_csubst_of_eqv (i := i)
        (fun x hx => by rw [agree x hx]) (fun _ => hsplit.2)

/-- The fork redex fires under any channel substitution, producing the freshly scoped parent
endpoint `c` and child endpoint `d` in flattened form. -/
lemma process_step_fork_edge_csubst {M : EvalCtx} {A m : Term} {c d : Chan}
    (freshC : occurs (chanIndex c) (M.eval (.fork A m)) = 0)
    (freshD : occurs (chanIndex d) (M.eval (.fork A m)) = 0) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        ((Proc.tm (M.eval (.fork A m)))[σ; Term.var_Term])
        (.nu (.par
          (.tm (((M.eval (.pure (Term.chan c)))[bindEndpointAt 0 c;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((m[Chan.var_Chan; (Term.chan d)..])[bindEndpointAt 0 d;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term])))) := by
  intro σ
  have hCM : occurs (chanIndex c) (M.eval (.pure .one)) = 0 := by
    have h := evalctx_occurs_plug M (.fork A m) (chanIndex c)
    omega
  have hDm : occurs (chanIndex d) m = 0 := by
    have h := evalctx_occurs_plug M (.fork A m) (chanIndex d)
    simp [occurs] at h
    omega
  have hsrc : (Proc.tm (M.eval (.fork A m)))[σ; Term.var_Term]
      = .tm ((M.cren (TLLC.Static.csubst_ren σ)).eval
          (.fork (A[σ; Term.var_Term]) (m[σ; Term.var_Term]))) := by
    show Proc.tm ((M.eval (.fork A m))[σ; Term.var_Term]) = _
    rw [evalctx_csubst]
    asimp
  rw [hsrc]
  refine TLLC.Process.Step.congr ARS.Conv.refl
    (TLLC.Process.Step.fork (A := A[σ; Term.var_Term]) (m := m[σ; Term.var_Term])
      (N := M.cren (TLLC.Static.csubst_ren σ)) rfl rfl)
    (process_congr_res (ARS.conv_trans
      (process_congr_parallel_left (ARS.conv1 (TLLC.Process.CongrProc.tm ?Mside)))
      (process_congr_parallel_right (ARS.conv1 (TLLC.Process.CongrProc.tm ?mside)))))
  case Mside =>
    have hR : (M.eval (.pure (Term.chan c)))[bindEndpointAt 0 c;
        Term.var_Term][up_Chan_Chan σ; Term.var_Term]
        = ((M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 c))).cren
            (TLLC.Static.csubst_ren (up_Chan_Chan σ))).eval
              (.pure (TLLC.Process.cvar 0)) := by
      rw [evalctx_csubst, evalctx_csubst]
      asimp
      congr 1
      cases c with
      | var_Chan cx =>
          asimp
          unfold bindEndpointAt chanIndex
          simp
          simp [funcomp, scons, asimp_lemmas]
    rw [hR, evalctx_cren_comp, evalctx_cren_comp]
    refine congrTerm_evalctx_cren_agree M _ (chanIndex c) _ _ ?_ hCM
    intro x hx
    cases c with
    | var_Chan cx =>
        simp only [chanIndex] at hx
        cases hσ : σ x with
        | var_Chan y =>
            simp [funcomp, TLLC.Static.csubst_ren, bindEndpointAt, chanIndex, hx, hσ,
              up_Chan_Chan, scons, asimp_lemmas]
  case mside =>
    have base : TLLC.Process.CongrTerm .ex
        (m[fun x => Chan.var_Chan (chanIndex (σ x) + 1); Term.var_Term])
        (m[fun x => if x = chanIndex d then Chan.var_Chan 0
            else Chan.var_Chan (chanIndex (σ x) + 1); Term.var_Term]) := by
      refine congrTerm_csubst_of_eqv (i := chanIndex d) ?_ (fun _ => hDm)
      intro x hx
      simp [hx]
    have base' := congrTerm_subst base Chan.var_Chan
      ((TLLC.Process.cvar 0) .: Term.var_Term)
    convert base' using 1
    · asimp
      congr 1
    · asimp
      cases d with
      | var_Chan dx =>
          congr 1
          · funext x
            rcases eq_or_ne x dx with rfl | hx
            · simp [bindEndpointAt, chanIndex, funcomp, up_Chan_Chan, scons, asimp_lemmas]
            · cases hσ : σ x with
              | var_Chan y =>
                  simp [bindEndpointAt, chanIndex, funcomp, up_Chan_Chan, scons, hx, hσ,
                    asimp_lemmas]
          · funext x
            cases x with
            | zero =>
                simp [bindEndpointAt, chanIndex, funcomp, up_Chan_Chan, scons, asimp_lemmas]
            | succ n =>
                asimp

/-- Hoist a sibling edge `(e, gc)` into a node child: the fresh parent/child pair `c`/`d`
scopes outward past `e` by the swap-normal-form/`exch` dance. Linearity supplies the leaf
freshness facts. -/
lemma flattenChildren_hoist_one (X : Proc) (e c d : Chan) (gc : Tree) (m' : Term)
    (acc : List (Chan × Tree))
    (hec : chanIndex e ≠ chanIndex c)
    (hed : chanIndex e ≠ chanIndex d)
    (freshX : TLLC.Process.procOccurs (chanIndex e) X = 0)
    (gpFresh : ∀ k, TLLC.Process.procOccurs (k + 1)
      ((gc.flattenAt).2[bindEndpointAt 0 (gc.flattenAt).1; Term.var_Term]) = 0) :
    TLLC.Process.Congruence
      (flattenChildren X [(e, gc), (c, .node d m' acc [])])
      (flattenChildren X [(c, .node d m' ((e, gc) :: acc) [])]) := by
  cases hgc : gc.flattenAt with
  | mk f gp =>
    simp only [hgc] at gpFresh
    simp only [flattenChildren, flattenChildren_nil, hgc, Tree.flattenAt_node, flattenBody,
      flattenSubtrees_nil, parAll_nil,
      (show ∀ (p : Proc) (τ : Nat → Chan),
          (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
        from fun _ _ => rfl),
      (show ∀ (a b : Proc) (τ : Nat → Chan),
          (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
        from fun _ _ _ => rfl)]
    set FC := flattenChildren (.tm m') acc with hFC
    set GP := gp[bindEndpointAt 0 f; Term.var_Term] with hGP
    refine ARS.conv_trans (swap_normal_form _ _) ?_
    refine ARS.conv_trans process_congr_exch ?_
    refine ARS.conv_trans ?_ (ARS.conv_sym (ARS.conv_trans
      (process_congr_res process_congr_scope_right)
      (process_congr_res (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.assoc)))))
    refine process_congr_res (process_congr_res ?_)
    simp only [(show ∀ (a b : Proc) (σ : Nat → Chan),
      (Proc.par a b)[σ; Term.var_Term] = Proc.par (a[σ; Term.var_Term]) (b[σ; Term.var_Term])
      from fun _ _ _ => rfl)]
    have fX : TLLC.Process.procOccurs (chanIndex e + 1)
        (X[bindEndpointAt 0 c; Term.var_Term]) = 0 := by
      apply procOccurs_csubst_zero
      intro k hk
      have hke : k = chanIndex e := by
        by_cases hkc : k = chanIndex c
        · subst hkc
          unfold bindEndpointAt at hk
          simp [Chan.var_Chan.injEq] at hk
        · unfold bindEndpointAt at hk
          simp [hkc, Chan.var_Chan.injEq] at hk
          omega
      rw [hke]
      exact freshX
    have leafX : TLLC.Process.Congruence
        (X[bindEndpointAt 0 c; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 e);
          Term.var_Term][Process.exch; Term.var_Term])
        ((X[bindEndpointAt 0 c; Term.var_Term])⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) := by
      set XC := X[bindEndpointAt 0 c; Term.var_Term] with hXC
      rw [show XC⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            = XC[(fun x => Chan.var_Chan (x + 1)); Term.var_Term] from by
          rw [← process_csubst_cren]; rfl]
      conv_lhs => simp only [asimp_lemmas]
      apply process_congr_csubst_of_eqv (i := chanIndex e + 1) _ fX
      intro x hx
      obtain ⟨a⟩ := e
      simp only [chanIndex] at hx
      rcases x with _ | k
      · simp [scons, asimp_lemmas]
      · rcases eq_or_ne k a with rfl | hk
        · omega
        · simp [bindEndpointAt, chanIndex, scons, funcomp, hk, asimp_lemmas]
    have leafF :
        FC[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 e);
          Term.var_Term][Process.exch; Term.var_Term] =
        FC[bindEndpointAt 0 e; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 d);
          Term.var_Term] := by
      obtain ⟨a⟩ := e
      obtain ⟨b⟩ := d
      asimp
      congr 1
      funext x
      simp only [chanIndex] at hed
      rcases eq_or_ne x a with rfl | hxa
      · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
      rcases eq_or_ne x b with rfl | hxb
      · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
      · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
    have leafG : TLLC.Process.Congruence
        (GP⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩[Process.exch; Term.var_Term])
        (GP[up_Chan_Chan (bindEndpointAt 0 d); Term.var_Term]) := by
      conv_lhs => simp only [asimp_lemmas]
      apply process_congr_csubst_of_eqv (i := chanIndex d + 1) _ (gpFresh (chanIndex d))
      intro x hx
      obtain ⟨b⟩ := d
      simp only [chanIndex] at hx
      rcases x with _ | k
      · simp [scons, asimp_lemmas]
      · rcases eq_or_ne k b with rfl | hk
        · omega
        · simp [bindEndpointAt, chanIndex, scons, funcomp, hk, asimp_lemmas]
    rw [leafF]
    exact ARS.conv_trans
      (process_congr_parallel_left (process_congr_parallel_left leafX))
      (process_congr_parallel_right leafG)

/-- Iterated hoisting: a whole sibling segment moves under the freshly spawned node. -/
lemma flattenChildren_hoist_children (X : Proc) (c d : Chan) (m' : Term) :
    ∀ (moving acc : List (Chan × Tree)),
    (∀ e gc, (e, gc) ∈ moving →
      chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
      TLLC.Process.procOccurs (chanIndex e) X = 0 ∧
      ∀ k, TLLC.Process.procOccurs (k + 1)
        ((gc.flattenAt).2[bindEndpointAt 0 (gc.flattenAt).1; Term.var_Term]) = 0) →
    TLLC.Process.Congruence
      (flattenChildren X (moving ++ [(c, .node d m' acc [])]))
      (flattenChildren X [(c, .node d m' (moving ++ acc) [])]) := by
  intro moving
  induction moving using List.reverseRecOn with
  | nil =>
      intro acc _
      exact ARS.Conv.refl
  | append_singleton ms p ih =>
      rcases p with ⟨e, gc⟩
      intro acc h
      have hhead := h e gc (by simp)
      have step1 : TLLC.Process.Congruence
          (flattenChildren X ((ms ++ [(e, gc)]) ++ [(c, .node d m' acc [])]))
          (flattenChildren X (ms ++ [(c, .node d m' ((e, gc) :: acc) [])])) := by
        rw [List.append_assoc]
        exact flattenChildren_congr_prefix X ms _ _
          (flattenChildren_hoist_one X e c d gc m' acc
            hhead.1 hhead.2.1 hhead.2.2.1 hhead.2.2.2)
      refine ARS.conv_trans step1 ?_
      have hrest := ih ((e, gc) :: acc) (fun e' gc' mem => h e' gc' (by simp [mem]))
      simpa [List.append_assoc] using hrest

/-- The fork step over the `before` siblings: the redex fires innermost and spawns the fresh
`c`/`d` edge with a bare node. -/
lemma fork_over_before (M : EvalCtx) (A m : Term) (c d : Chan)
    (freshC : occurs (chanIndex c) (M.eval (.fork A m)) = 0)
    (freshD : occurs (chanIndex d) (M.eval (.fork A m)) = 0)
    (before : List (Chan × Tree)) :
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.fork A m))) before)[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (Term.chan c))))
        (before ++ [(c, .node d (m[Chan.var_Chan; (Term.chan d)..]) [] [])]))[σ;
          Term.var_Term]) := by
  induction before with
  | nil =>
      intro σ
      simpa [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, flattenBody,
        flattenSubtrees_nil, parAll_nil,
        (show ∀ (p : Proc) (τ : Nat → Chan),
            (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
          from fun _ _ => rfl),
        (show ∀ (a b : Proc) (τ : Nat → Chan),
            (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
          from fun _ _ _ => rfl),
        (show ∀ (t : Term) (τ : Nat → Chan),
            (Proc.tm t)[τ; Term.var_Term] = Proc.tm (t[τ; Term.var_Term])
          from fun _ _ => rfl)] using process_step_fork_edge_csubst freshC freshD σ
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f sp =>
          have tailStep := ih (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := sp[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                tailStep)
            using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

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

/-- Move the head child past a prefix of siblings (stopping before a suffix). -/
lemma flattenChildren_move_head_past (body : Proc) (c : Chan) (child : Tree)
    (tyChild : ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) child) :
    ∀ (l suffix : List (Chan × Tree)),
    (∀ e sib, (e, sib) ∈ l → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib) →
    (∀ e sib, (e, sib) ∈ l → chanIndex c ≠ chanIndex e) →
    TLLC.Process.Congruence
      (flattenChildren body ((c, child) :: (l ++ suffix)))
      (flattenChildren body (l ++ (c, child) :: suffix)) := by
  intro l
  induction l with
  | nil =>
      intro suffix _ _
      exact ARS.Conv.refl
  | cons edge l' ih =>
      rcases edge with ⟨e, sib⟩
      intro suffix tyL distinctL
      refine ARS.conv_trans
        (flattenChildren_swap_adjacent_typed body c e child sib (l' ++ suffix)
          (distinctL e sib (by simp)) tyChild (tyL e sib (by simp))) ?_
      simp only [List.cons_append]
      exact flattenChildren_congr_prefix_one body e sib _ _
        (ih suffix (fun e' sib' mem => tyL e' sib' (List.mem_cons_of_mem _ mem))
          (fun e' sib' mem => distinctL e' sib' (List.mem_cons_of_mem _ mem)))

/-- Reorder a child list into its `splitChildrenByTerm` partition (complement first). -/
lemma flattenChildren_partition_congr (body : Proc) (m : Term) :
    ∀ (ms : List (Chan × Tree)),
    (∀ e sib, (e, sib) ∈ ms → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib) →
    (childLabels ms).Nodup →
    TLLC.Process.Congruence
      (flattenChildren body ms)
      (flattenChildren body
        ((splitChildrenByTerm m ms).2 ++ (splitChildrenByTerm m ms).1)) := by
  intro ms
  induction ms with
  | nil =>
      intro _ _
      exact ARS.Conv.refl
  | cons q rest ih =>
      rcases q with ⟨e, sib⟩
      intro tyMs nodup
      have tyRest : ∀ e' sib', (e', sib') ∈ rest → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib' :=
        fun e' sib' mem => tyMs e' sib' (List.mem_cons_of_mem _ mem)
      have nodupRest : (childLabels rest).Nodup := by
        simpa [childLabels] using nodup.of_cons
      have ihRest := ih tyRest nodupRest
      cases e with
      | var_Chan ex =>
          by_cases hocc : occurs ex m = 0
          · rw [splitChildrenByTerm_cons_pos hocc]
            refine ARS.conv_trans
              (flattenChildren_congr_prefix_one body _ sib _ _ ihRest) ?_
            simp only [List.cons_append]
            exact ARS.Conv.refl
          · rw [splitChildrenByTerm_cons_neg hocc]
            refine ARS.conv_trans
              (flattenChildren_congr_prefix_one body _ sib _ _ ihRest) ?_
            refine flattenChildren_move_head_past body (Chan.var_Chan ex) sib
              (tyMs (Chan.var_Chan ex) sib (by simp)) _ _ ?_ ?_
            · intro e' sib' mem
              exact tyRest e' sib' (splitChildrenByTerm_mem₂ mem).1
            · intro e' sib' mem hidx
              have hmem : (e', sib') ∈ rest := (splitChildrenByTerm_mem₂ mem).1
              have hlab : Chan.var_Chan ex ∈ childLabels rest := by
                cases e' with
                | var_Chan ex' =>
                    simp only [chanIndex] at hidx
                    subst hidx
                    exact List.mem_map.mpr ⟨(Chan.var_Chan ex, sib'), hmem, rfl⟩
              have hnotin : Chan.var_Chan ex ∉ childLabels rest := by
                have hcons : childLabels ((Chan.var_Chan ex, sib) :: rest)
                    = Chan.var_Chan ex :: childLabels rest := rfl
                rw [hcons] at nodup
                exact (List.nodup_cons.mp nodup).1
              exact hnotin hlab

/-- Away from `c`, the returned-endpoint body has the same occurrences as the bare context. -/
lemma pure_chan_term_occurs_eq (M : EvalCtx) (c : Chan) (i : Nat) (ne : i ≠ chanIndex c) :
    occurs i (M.eval (.pure (Term.chan c))) = occurs i (M.eval (.pure .one)) := by
  induction M with
  | hole =>
      cases c with
      | var_Chan x =>
          simp only [chanIndex] at ne
          simp [EvalCtx.eval, occurs]
          omega
  | bnd M n ih =>
      simp [EvalCtx.eval, occurs, ih]

/-- The full fork children-body step: reorder by the payload partition, fire the fork edge, and
hoist the payload-occurring children under the freshly spawned node. This is `bodyStep` for the
rootFork/nodeFork cases. -/
lemma fork_bodyStep (M : EvalCtx) (A m : Term) (c d : Chan) (ms : List (Chan × Tree))
    (freshC : occurs (chanIndex c) (M.eval (.fork A m)) = 0)
    (freshD : occurs (chanIndex d) (M.eval (.fork A m)) = 0)
    (tyMs : ∀ e sib, (e, sib) ∈ ms → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (nodup : (childLabels ms).Nodup)
    (linear : ∀ e sib, (e, sib) ∈ ms → occurs (chanIndex e) (M.eval (.fork A m)) ≤ 1)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.fork A m))) ms)[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (Term.chan c))))
        (forkChildren m c d ms))[σ; Term.var_Term]) := by
  have freshCm : occurs (chanIndex c) m = 0 := by
    have h := evalctx_occurs_plug M (.fork A m) (chanIndex c)
    simp [occurs] at h
    omega
  have freshDm : occurs (chanIndex d) m = 0 := by
    have h := evalctx_occurs_plug M (.fork A m) (chanIndex d)
    simp [occurs] at h
    omega
  have hoistHyp : ∀ e gc, (e, gc) ∈ (splitChildrenByTerm m ms).1 →
      chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
      TLLC.Process.procOccurs (chanIndex e) (Proc.tm (M.eval (.pure (Term.chan c)))) = 0 ∧
      ∀ k, TLLC.Process.procOccurs (k + 1)
        ((gc.flattenAt).2[bindEndpointAt 0 (gc.flattenAt).1; Term.var_Term]) = 0 := by
    intro e gc mem
    obtain ⟨memMs, hoccE'⟩ := splitChildrenByTerm_mem₁ mem
    have hoccE : occurs (chanIndex e) m ≠ 0 := hoccE'
    have hec : chanIndex e ≠ chanIndex c := by
      intro h; rw [h] at hoccE; exact hoccE freshCm
    have hed : chanIndex e ≠ chanIndex d := by
      intro h; rw [h] at hoccE; exact hoccE freshDm
    refine ⟨hec, hed, ?_, ?_⟩
    · show occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0
      rw [pure_chan_term_occurs_eq M c (chanIndex e) hec]
      have hlin := linear e gc memMs
      have h1 := evalctx_occurs_plug M (.fork A m) (chanIndex e)
      simp [occurs] at h1
      omega
    · obtain ⟨r, A', tyA', tgc⟩ := tyMs e gc memMs
      exact fun k => tgc.flattenAt_occurs_succ tyA' k
  refine TLLC.Process.Step.congr
    (process_congr_csubst
      (flattenChildren_partition_congr (.tm (M.eval (.fork A m))) m ms tyMs nodup) σ)
    (fork_over_before M A m c d freshC freshD
      ((splitChildrenByTerm m ms).2 ++ (splitChildrenByTerm m ms).1) σ)
    ?_
  refine process_congr_csubst ?_ σ
  rw [show forkChildren m c d ms
      = (splitChildrenByTerm m ms).2 ++
          [(c, Tree.node d (m[Chan.var_Chan; (Term.chan d)..])
            (splitChildrenByTerm m ms).1 [])] from rfl]
  rw [List.append_assoc]
  refine flattenChildren_congr_prefix _ (splitChildrenByTerm m ms).2 _ _ ?_
  have h := flattenChildren_hoist_children (.tm (M.eval (.pure (Term.chan c)))) c d
    (m[Chan.var_Chan; (Term.chan d)..]) (splitChildrenByTerm m ms).1 [] hoistHyp
  simpa using h

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

/-- The implicit-send body term and its post-step pure form have the same channel occurrences:
the implicit payload is erased, both reduce to `chan c` in the hole. -/
lemma sendIm_term_occurs_eq (M : EvalCtx) (c : Chan) (o : Term) (i : Nat) :
    occurs i (M.eval (.app (.send (Term.chan c) .im) o .im)) =
      occurs i (M.eval (.pure (Term.chan c))) := by
  induction M with
  | hole => cases c with | var_Chan x => simp [EvalCtx.eval, occurs]
  | bnd M n ih => simp [EvalCtx.eval, occurs, ih]

/-- `parAll` over an appended snoc list. -/
lemma parAll_snoc (a b : Proc) (SS : List Proc) :
    parAll a (SS ++ [b]) = .par (parAll a SS) b := by
  simp [parAll, List.foldl_append]

/-- A closed process is congruent to any substitution instance of itself. -/
lemma process_congr_closed_csubst_id {q : Proc}
    (closed : ∀ i, TLLC.Process.procOccurs i q = 0) (τ : Nat → Chan) :
    TLLC.Process.Congruence (q[τ; Term.var_Term]) q := by
  have h := process_congr_csubst_of_occurs (p := q) (σ := τ) (τ := Chan.var_Chan)
    (fun k hk => absurd (closed k) hk)
  convert h using 2
  asimp

/-- A `nu` scopes out of a `parAll` of closed spectators. -/
lemma process_congr_parAll_scope_closed (p : Proc) :
    ∀ SS : List Proc,
    (∀ q, q ∈ SS → ∀ i, TLLC.Process.procOccurs i q = 0) →
    TLLC.Process.Congruence (parAll (.nu p) SS) (.nu (parAll p SS)) := by
  intro SS
  induction SS generalizing p with
  | nil =>
      intro _
      exact ARS.Conv.refl
  | cons q SS' ih =>
      intro h
      simp only [parAll_cons]
      have hq : TLLC.Process.Congruence (.par (.nu p) q) (.nu (.par p q)) := by
        refine ARS.conv_trans ?_ (ARS.conv_sym
          (process_congr_scope_out_right (h q (by simp) 0)))
        refine process_congr_parallel_right ?_
        rw [process_cren_eq_csubst]
        exact ARS.conv_sym (process_congr_closed_csubst_id (h q (by simp)) _)
      refine ARS.conv_trans
        (process_congr_parAll_accumulator SS' hq) ?_
      exact ih (.par p q) (fun q' hq' i => h q' (by simp [hq']) i)

/-- Prepending a child to a node's child list wraps the flattened body in one fresh binder,
provided the detached subtrees are closed. -/
lemma flattenBody_cons_child_congr (m'' : Term) (e : Chan) (gc : Tree)
    (kids : List (Chan × Tree)) (qs' : List Tree)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0) :
    TLLC.Process.Congruence
      (flattenBody m'' ((e, gc) :: kids) qs')
      (.nu (.par ((flattenBody m'' kids qs')[bindEndpointAt 0 e; Term.var_Term])
        ((gc.flattenAt).2[bindEndpointAt 0 (gc.flattenAt).1; Term.var_Term]))) := by
  cases hgc : gc.flattenAt with
  | mk f gp =>
    simp only [flattenBody, hgc]
    have hunf : flattenChildren (.tm m'') ((e, gc) :: kids)
        = .nu (.par ((flattenChildren (.tm m'') kids)[bindEndpointAt 0 e; Term.var_Term])
            (gp[bindEndpointAt 0 f; Term.var_Term])) := by
      simp only [flattenChildren, hgc]
    rw [hunf]
    refine ARS.conv_trans (process_congr_parAll_scope_closed _ _ qsZero) ?_
    refine process_congr_res ?_
    refine ARS.conv_trans (process_congr_parAll_push_right _ _ _) ?_
    rw [parAll_snoc]
    refine process_congr_parallel_left ?_
    simp only [flattenBody, parAll_csubst]
    conv_lhs => rw [← List.map_id (flattenSubtrees qs')]
    exact process_congr_parAll_map_pointwise _ _ _ (flattenSubtrees qs')
      (fun q hq => ARS.conv_sym (process_congr_closed_csubst_id (fun i => qsZero q hq i) _))

/-- Abstract hoist congruence: a sibling binder `e` moves inside the fresh `c`/`d` binder,
attaching to the child-side component. Extracted swap-normal-form/`exch` dance. -/
lemma hoist_core (X FB GP : Proc) (e c d : Chan)
    (hec : chanIndex e ≠ chanIndex c)
    (hed : chanIndex e ≠ chanIndex d)
    (freshX : TLLC.Process.procOccurs (chanIndex e) X = 0)
    (gpFresh : ∀ k, TLLC.Process.procOccurs (k + 1) GP = 0) :
    TLLC.Process.Congruence
      (.nu (.par
        (.nu (.par
          (X[bindEndpointAt 0 c; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 e);
            Term.var_Term])
          (FB[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 e);
            Term.var_Term])))
        GP))
      (.nu (.par (X[bindEndpointAt 0 c; Term.var_Term])
        (.nu (.par
          (FB[bindEndpointAt 0 e; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 d);
            Term.var_Term])
          (GP[up_Chan_Chan (bindEndpointAt 0 d); Term.var_Term]))))) := by
  refine ARS.conv_trans (swap_normal_form _ _) ?_
  refine ARS.conv_trans process_congr_exch ?_
  refine ARS.conv_trans ?_ (ARS.conv_sym (ARS.conv_trans
    (process_congr_res process_congr_scope_right)
    (process_congr_res (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.assoc)))))
  refine process_congr_res (process_congr_res ?_)
  simp only [(show ∀ (a b : Proc) (σ : Nat → Chan),
    (Proc.par a b)[σ; Term.var_Term] = Proc.par (a[σ; Term.var_Term]) (b[σ; Term.var_Term])
    from fun _ _ _ => rfl)]
  have fX : TLLC.Process.procOccurs (chanIndex e + 1)
      (X[bindEndpointAt 0 c; Term.var_Term]) = 0 := by
    apply procOccurs_csubst_zero
    intro k hk
    have hke : k = chanIndex e := by
      by_cases hkc : k = chanIndex c
      · subst hkc
        unfold bindEndpointAt at hk
        simp [Chan.var_Chan.injEq] at hk
      · unfold bindEndpointAt at hk
        simp [hkc, Chan.var_Chan.injEq] at hk
        omega
    rw [hke]
    exact freshX
  have leafX : TLLC.Process.Congruence
      (X[bindEndpointAt 0 c; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 e);
        Term.var_Term][Process.exch; Term.var_Term])
      ((X[bindEndpointAt 0 c; Term.var_Term])⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) := by
    set XC := X[bindEndpointAt 0 c; Term.var_Term] with hXC
    rw [show XC⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
          = XC[(fun x => Chan.var_Chan (x + 1)); Term.var_Term] from by
        rw [← process_csubst_cren]; rfl]
    conv_lhs => simp only [asimp_lemmas]
    apply process_congr_csubst_of_eqv (i := chanIndex e + 1) _ fX
    intro x hx
    obtain ⟨a⟩ := e
    simp only [chanIndex] at hx
    rcases x with _ | k
    · simp [scons, asimp_lemmas]
    · rcases eq_or_ne k a with rfl | hk
      · omega
      · simp [bindEndpointAt, chanIndex, scons, funcomp, hk, asimp_lemmas]
  have leafF :
      FB[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 e);
        Term.var_Term][Process.exch; Term.var_Term] =
      FB[bindEndpointAt 0 e; Term.var_Term][up_Chan_Chan (bindEndpointAt 0 d);
        Term.var_Term] := by
    obtain ⟨a⟩ := e
    obtain ⟨b⟩ := d
    asimp
    congr 1
    funext x
    simp only [chanIndex] at hed
    rcases eq_or_ne x a with rfl | hxa
    · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
    rcases eq_or_ne x b with rfl | hxb
    · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
    · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
  have leafG : TLLC.Process.Congruence
      (GP⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩[Process.exch; Term.var_Term])
      (GP[up_Chan_Chan (bindEndpointAt 0 d); Term.var_Term]) := by
    conv_lhs => simp only [asimp_lemmas]
    apply process_congr_csubst_of_eqv (i := chanIndex d + 1) _ (gpFresh (chanIndex d))
    intro x hx
    obtain ⟨b⟩ := d
    simp only [chanIndex] at hx
    rcases x with _ | k
    · simp [scons, asimp_lemmas]
    · rcases eq_or_ne k b with rfl | hk
      · omega
      · simp [bindEndpointAt, chanIndex, scons, funcomp, hk, asimp_lemmas]
  rw [leafF]
  exact ARS.conv_trans
    (process_congr_parallel_left (process_congr_parallel_left leafX))
    (process_congr_parallel_right leafG)

/-- Generalized hoist: a sibling edge `(e, gc)` moves under an arbitrary node child (with
grandchildren `kids` and closed detached subtrees `qs'`). -/
lemma flattenChildren_hoist_one' (X : Proc) (e c d : Chan) (gc : Tree) (m'' : Term)
    (kids : List (Chan × Tree)) (qs' : List Tree)
    (hec : chanIndex e ≠ chanIndex c)
    (hed : chanIndex e ≠ chanIndex d)
    (freshX : TLLC.Process.procOccurs (chanIndex e) X = 0)
    (gpFresh : ∀ k, TLLC.Process.procOccurs (k + 1)
      ((gc.flattenAt).2[bindEndpointAt 0 (gc.flattenAt).1; Term.var_Term]) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0) :
    TLLC.Process.Congruence
      (flattenChildren X [(e, gc), (c, .node d m'' kids qs')])
      (flattenChildren X [(c, .node d m'' ((e, gc) :: kids) qs')]) := by
  cases hgc : gc.flattenAt with
  | mk f gp =>
    simp only [hgc] at gpFresh
    have hbody := flattenBody_cons_child_congr m'' e gc kids qs' qsZero
    rw [hgc] at hbody
    have hR : TLLC.Process.Congruence
        (flattenChildren X [(c, Tree.node d m'' ((e, gc) :: kids) qs')])
        (.nu (.par (X[bindEndpointAt 0 c; Term.var_Term])
          (.nu (.par
            ((flattenBody m'' kids qs')[bindEndpointAt 0 e; Term.var_Term][up_Chan_Chan
              (bindEndpointAt 0 d); Term.var_Term])
            ((gp[bindEndpointAt 0 f; Term.var_Term])[up_Chan_Chan (bindEndpointAt 0 d);
              Term.var_Term]))))) := by
      have hunf : flattenChildren X [(c, Tree.node d m'' ((e, gc) :: kids) qs')]
          = .nu (.par (X[bindEndpointAt 0 c; Term.var_Term])
              ((flattenBody m'' ((e, gc) :: kids) qs')[bindEndpointAt 0 d;
                Term.var_Term])) := by
        simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node]
      rw [hunf]
      refine process_congr_res (process_congr_parallel_right ?_)
      refine ARS.conv_trans (process_congr_csubst hbody _) ?_
      simp only [(show ∀ (p : Proc) (τ : Nat → Chan),
          (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
        from fun _ _ => rfl),
        (show ∀ (a b : Proc) (τ : Nat → Chan),
          (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
        from fun _ _ _ => rfl)]
      exact ARS.Conv.refl
    refine ARS.conv_trans ?_ (ARS.conv_sym hR)
    have hunfL : flattenChildren X [(e, gc), (c, Tree.node d m'' kids qs')]
        = .nu (.par
            ((Proc.nu (.par (X[bindEndpointAt 0 c; Term.var_Term])
              ((flattenBody m'' kids qs')[bindEndpointAt 0 d; Term.var_Term])))[
                bindEndpointAt 0 e; Term.var_Term])
            (gp[bindEndpointAt 0 f; Term.var_Term])) := by
      simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, hgc]
    rw [hunfL]
    simp only [(show ∀ (p : Proc) (τ : Nat → Chan),
        (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
      from fun _ _ => rfl),
      (show ∀ (a b : Proc) (τ : Nat → Chan),
        (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
      from fun _ _ _ => rfl)]
    exact hoist_core X (flattenBody m'' kids qs') (gp[bindEndpointAt 0 f; Term.var_Term])
      e c d hec hed freshX gpFresh

/-- Iterated generalized hoisting: a whole sibling segment moves under the node child. -/
lemma flattenChildren_hoist_children' (X : Proc) (c d : Chan) (m'' : Term)
    (qs' : List Tree)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0) :
    ∀ (moving kids : List (Chan × Tree)),
    (∀ e gc, (e, gc) ∈ moving →
      chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
      TLLC.Process.procOccurs (chanIndex e) X = 0 ∧
      ∀ k, TLLC.Process.procOccurs (k + 1)
        ((gc.flattenAt).2[bindEndpointAt 0 (gc.flattenAt).1; Term.var_Term]) = 0) →
    TLLC.Process.Congruence
      (flattenChildren X (moving ++ [(c, .node d m'' kids qs')]))
      (flattenChildren X [(c, .node d m'' (moving ++ kids) qs')]) := by
  intro moving
  induction moving using List.reverseRecOn with
  | nil =>
      intro kids _
      exact ARS.Conv.refl
  | append_singleton ms p ih =>
      rcases p with ⟨e, gc⟩
      intro kids h
      have hhead := h e gc (by simp)
      have step1 : TLLC.Process.Congruence
          (flattenChildren X ((ms ++ [(e, gc)]) ++ [(c, .node d m'' kids qs')]))
          (flattenChildren X (ms ++ [(c, .node d m'' ((e, gc) :: kids) qs')])) := by
        rw [List.append_assoc]
        exact flattenChildren_congr_prefix X ms _ _
          (flattenChildren_hoist_one' X e c d gc m'' kids qs'
            hhead.1 hhead.2.1 hhead.2.2.1 hhead.2.2.2 qsZero)
      refine ARS.conv_trans step1 ?_
      have hrest := ih ((e, gc) :: kids) (fun e' gc' mem => h e' gc' (by simp [mem]))
      simpa [List.append_assoc] using hrest

/-- Rotate two child-list segments (a congruence, by iterated move-to-last). -/
lemma flattenChildren_rotate_congr (body : Proc) :
    ∀ (front back : List (Chan × Tree)),
    (∀ e sib, (e, sib) ∈ front ++ back → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib) →
    (childLabels (front ++ back)).Nodup →
    TLLC.Process.Congruence
      (flattenChildren body (front ++ back))
      (flattenChildren body (back ++ front)) := by
  intro front
  induction front with
  | nil =>
      intro back _ _
      simp
      exact ARS.Conv.refl
  | cons a front' ih =>
      rcases a with ⟨e, sib⟩
      intro back tyAll nodup
      simp only [List.cons_append] at nodup tyAll ⊢
      have tyRest : ∀ e' sib', (e', sib') ∈ front' ++ back →
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib' :=
        fun e' sib' mem => tyAll e' sib' (List.mem_cons_of_mem _ mem)
      have distinctRest : ∀ e' sib', (e', sib') ∈ front' ++ back →
          chanIndex e ≠ chanIndex e' := by
        intro e' sib' mem hidx
        have hcons : childLabels ((e, sib) :: (front' ++ back))
            = e :: childLabels (front' ++ back) := rfl
        rw [hcons] at nodup
        refine (List.nodup_cons.mp nodup).1 ?_
        have he' : e = e' := by
          cases e with
          | var_Chan a => cases e' with
            | var_Chan b => simp only [chanIndex] at hidx; rw [hidx]
        rw [he']
        exact List.mem_map.mpr ⟨(e', sib'), mem, rfl⟩
      refine ARS.conv_trans
        (flattenChildren_move_to_last body e sib [] (front' ++ back)
          (tyAll e sib (by simp)) tyRest distinctRest) ?_
      simp only [List.nil_append]
      have hperm : (childLabels ((front' ++ back) ++ [(e, sib)])).Nodup := by
        have h1 : childLabels ((front' ++ back) ++ [(e, sib)])
            = childLabels (front' ++ back) ++ [e] := by
          simp [childLabels]
        have h2 : childLabels ((e, sib) :: (front' ++ back))
            = e :: childLabels (front' ++ back) := rfl
        rw [h1]
        rw [h2] at nodup
        exact (List.perm_append_singleton _ _).nodup_iff.mpr nodup
      have hrec := ih (back ++ [(e, sib)])
        (by
          intro e' sib' mem
          refine tyAll e' sib' ?_
          rcases List.mem_append.mp mem with h | h
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
          · rcases List.mem_append.mp h with h | h
            · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
            · simp at h
              simp [h])
        (by
          have hassoc : front' ++ (back ++ [(e, sib)]) = (front' ++ back) ++ [(e, sib)] := by
            simp [List.append_assoc]
          rw [hassoc]
          exact hperm)
      have hlist : (back ++ [(e, sib)]) ++ front' = back ++ (e, sib) :: front' := by
        simp
      rw [hlist] at hrec
      rw [List.append_assoc]
      exact hrec

/-- A `CongrTerm`-congruent pair of holes stays congruent under a fixed eval context. -/
lemma congrTerm_evalctx_congr (M : EvalCtx) {X Y : Term}
    (h : TLLC.Process.CongrTerm .ex X Y) :
    TLLC.Process.CongrTerm .ex (M.eval X) (M.eval Y) := by
  induction M with
  | hole => exact h
  | bnd M n ih =>
      exact TLLC.Process.CongrTerm.mlet ih (TLLC.Process.CongrTerm.refl _ _)

/-- The explicit com edge in tree form: the sent value re-binds from the parent endpoint `c` to
the child endpoint `d`, justified by `c`/`d` being absent from the value. -/
lemma process_step_comEx_edge_tree_csubst {M N : EvalCtx} {v : Term} {c d : Chan}
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.app (.send (Term.chan c) .ex) v .ex))[bindEndpointAt 0 c;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.recv (Term.chan d) .ex))[bindEndpointAt 0 d;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.nu (.par
          (.tm (((M.eval (.pure (Term.chan c)))[bindEndpointAt 0 c;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.pure (.pair v (Term.chan d) .ex .L)))[bindEndpointAt 0 d;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term])))) := by
  intro σ
  have hT : (N.eval (.pure (.pair v (Term.chan d) .ex .L)))[bindEndpointAt 0 d;
      Term.var_Term][up_Chan_Chan σ; Term.var_Term]
      = ((N.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 d))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ))).eval
            (.pure (.pair (v[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ;
              Term.var_Term]) (TLLC.Process.cvar 0) .ex .L)) := by
    rw [evalctx_csubst, evalctx_csubst]
    asimp
    congr 1
    cases d with
    | var_Chan dx =>
        asimp
        unfold bindEndpointAt chanIndex
        simp
        simp [funcomp, scons, asimp_lemmas]
  have h1 : TLLC.Process.CongrTerm .ex
      (Term.pure (.pair (v[bindEndpointAt 0 c; Term.var_Term][up_Chan_Chan σ;
        Term.var_Term]) (TLLC.Process.cvar 0) .ex .L))
      (Term.pure (.pair (v[(fun x => Chan.var_Chan (x + 1)); Term.var_Term][up_Chan_Chan σ;
        Term.var_Term]) (TLLC.Process.cvar 0) .ex .L)) := by
    refine TLLC.Process.CongrTerm.pure (TLLC.Process.CongrTerm.pair ?_
      (TLLC.Process.CongrTerm.refl _ _))
    asimp
    refine congrTerm_csubst_of_eqv (i := chanIndex c) ?_ (fun _ => hcv)
    intro x hx
    cases c with
    | var_Chan cx =>
        simp only [chanIndex] at hx
        cases hσ : σ x with
        | var_Chan y =>
            simp [bindEndpointAt, chanIndex, funcomp, up_Chan_Chan, scons, hx, hσ,
              asimp_lemmas]
  have h2 : TLLC.Process.CongrTerm .ex
      (Term.pure (.pair (v[(fun x => Chan.var_Chan (x + 1)); Term.var_Term][up_Chan_Chan σ;
        Term.var_Term]) (TLLC.Process.cvar 0) .ex .L))
      (Term.pure (.pair (v[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ;
        Term.var_Term]) (TLLC.Process.cvar 0) .ex .L)) := by
    refine TLLC.Process.CongrTerm.pure (TLLC.Process.CongrTerm.pair ?_
      (TLLC.Process.CongrTerm.refl _ _))
    asimp
    refine congrTerm_csubst_of_eqv (i := chanIndex d) ?_ (fun _ => hdv)
    intro x hx
    cases d with
    | var_Chan dx =>
        simp only [chanIndex] at hx
        cases hσ : σ x with
        | var_Chan y =>
            simp [bindEndpointAt, chanIndex, funcomp, up_Chan_Chan, scons, hx, hσ,
              asimp_lemmas]
  refine TLLC.Process.Step.congr ARS.Conv.refl
    (process_step_comEx_edge_csubst (M := M) (N := N) (valueTerm := v)
      (c := c) (d := d) value σ)
    ?_
  rw [hT]
  exact ARS.conv_trans
    (process_congr_res (process_congr_parallel_right (ARS.conv1
      (TLLC.Process.CongrProc.tm (congrTerm_evalctx_congr _ h1)))))
    (process_congr_res (process_congr_parallel_right (ARS.conv1
      (TLLC.Process.CongrProc.tm (congrTerm_evalctx_congr _ h2)))))

/-- Mirror of `process_step_comEx_edge_tree_csubst` for the receive direction. -/
lemma process_step_comEx_edge_tree_symm_csubst {M N : EvalCtx} {v : Term} {c d : Chan}
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.recv (Term.chan c) .ex))[bindEndpointAt 0 c;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.app (.send (Term.chan d) .ex) v .ex))[bindEndpointAt 0 d;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.nu (.par
          (.tm (((M.eval (.pure (.pair v (Term.chan c) .ex .L)))[bindEndpointAt 0 c;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.pure (Term.chan d)))[bindEndpointAt 0 d;
            Term.var_Term])[up_Chan_Chan σ; Term.var_Term])))) := by
  intro σ
  exact TLLC.Process.Step.congr
    (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym))
    (process_step_comEx_edge_tree_csubst (M := N) (N := M) (v := v)
      (c := d) (d := c) value hdv hcv σ)
    (process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym))

/-- Lift a body congruence of same-endpoint node children through a single-edge flatten. -/
lemma flattenChildren_node_congr (X : Proc) (c d : Chan) (m1 m2 : Term)
    (k1 k2 : List (Chan × Tree)) (q1 q2 : List Tree)
    (h : TLLC.Process.Congruence (flattenBody m1 k1 q1) (flattenBody m2 k2 q2)) :
    TLLC.Process.Congruence
      (flattenChildren X [(c, .node d m1 k1 q1)])
      (flattenChildren X [(c, .node d m2 k2 q2)]) := by
  simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node]
  exact process_congr_res (process_congr_parallel_right (process_congr_csubst h _))

set_option maxRecDepth 4096 in
/-- `comEx` fires through the receiver child's grandchildren; clone of `comIm_through_FC` with
the explicit-value edge. -/
lemma comEx_through_FC (M N : EvalCtx) (v : Term) (c d : Chan)
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0) :
    ∀ (ms' : List (Chan × Tree)),
    (∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc) →
    (∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0) →
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      (.nu (.par
        (((Proc.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex))) ms')[bindEndpointAt 0 d;
          Term.var_Term][up_Chan_Chan σ; Term.var_Term])))
      (.nu (.par
        (((Proc.tm (M.eval (.pure (Term.chan c))))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.pure (.pair v (Term.chan d) .ex .L)))) ms')[
          bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term]))) := by
  intro ms'
  induction ms' with
  | nil =>
      intro _ _ σ
      simp only [flattenChildren_nil]
      exact process_step_comEx_edge_tree_csubst (M := M) (N := N) (v := v)
        (c := c) (d := d) value hcv hdv σ
  | cons edge ms'' ih =>
      rcases edge with ⟨e, gc⟩
      intro tyMs mFresh σ
      cases hg : gc.flattenAt with
      | mk dg gp =>
        simp only [flattenChildren, hg,
          (show ∀ (p : Proc) (τ : Nat → Chan),
              (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
            from fun _ _ => rfl),
          (show ∀ (a b : Proc) (τ : Nat → Chan),
              (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
            from fun _ _ _ => rfl)]
        refine TLLC.Process.Step.congr (extrude_one_congr _ _ _) ?_
          (ARS.conv_sym (extrude_one_congr _ _ _))
        refine TLLC.Process.Step.res (process_step_scope_unused_right ?gpFresh ?innerCom)
        case gpFresh =>
          obtain ⟨r', A', tyA', tgc⟩ := tyMs e gc (by simp)
          have hgp : ∀ i, TLLC.Process.procOccurs (i + 1)
              (gp[bindEndpointAt 0 dg; Term.var_Term]) = 0 := by
            intro i; simpa [hg] using tgc.flattenAt_occurs_succ tyA' i
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by rcases k with _ | _ | k <;> simp_all [Process.exch, cexch]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by
            rcases k with _ | _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · rfl
            · exfalso
              cases hσ : σ k with
              | var_Chan j => simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hkd : k = chanIndex d + 1 := by
            rcases k with _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · by_cases hkd : k = chanIndex d
              · subst hkd; rfl
              · exfalso
                simp_all [up_Chan_Chan, bindEndpointAt, chanIndex, scons, funcomp, asimp_lemmas]
          subst hkd
          exact hgp (chanIndex d)
        case innerCom =>
          have key := ih (fun e' gc' mem => tyMs e' gc' (List.mem_cons_of_mem _ mem))
            (fun e' gc' mem => mFresh e' gc' (List.mem_cons_of_mem _ mem))
            (fun y => if y = chanIndex e then Chan.var_Chan 0
                      else Chan.var_Chan (chanIndex (σ y) + 1))
          refine TLLC.Process.Step.congr ?congL key ?congR
          case congL =>
            apply process_congr_res
            refine ARS.conv_trans (process_congr_parallel_left ?cA)
              (process_congr_parallel_right ?cF)
            case cF =>
              have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
              asimp
              convert ARS.Conv.refl using 2
              funext x
              clear ih tyMs mFresh key value hcv hdv
              rcases eq_or_ne x (chanIndex d) with rfl | hxd
              · unfold bindEndpointAt
                simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case cA =>
              apply ARS.conv1
              apply TLLC.Process.CongrProc.tm
              asimp
              refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
                (fun _ => (mFresh e gc (by simp)).2.1)
              intro x hx
              rcases eq_or_ne x (chanIndex c) with rfl | hxc
              · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]
          case congR =>
            apply ARS.conv_sym
            apply process_congr_res
            refine ARS.conv_trans (process_congr_parallel_left ?cA')
              (process_congr_parallel_right ?cF')
            case cF' =>
              have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
              asimp
              convert ARS.Conv.refl using 2
              funext x
              clear ih tyMs mFresh key value hcv hdv
              rcases eq_or_ne x (chanIndex d) with rfl | hxd
              · unfold bindEndpointAt
                simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case cA' =>
              apply ARS.conv1
              apply TLLC.Process.CongrProc.tm
              asimp
              refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
                (fun _ => (mFresh e gc (by simp)).2.2)
              intro x hx
              rcases eq_or_ne x (chanIndex c) with rfl | hxc
              · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]

set_option maxRecDepth 4096 in
/-- Mirror of `comEx_through_FC` for explicit receive: the parent receives and the selected child
sends. -/
lemma comEx_through_FC_symm (M N : EvalCtx) (v : Term) (c d : Chan)
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0) :
    ∀ (ms' : List (Chan × Tree)),
    (∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc) →
    (∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.recv (Term.chan c) .ex)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (.pair v (Term.chan c) .ex .L))) = 0) →
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      (.nu (.par
        (((Proc.tm (M.eval (.recv (Term.chan c) .ex)))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.app (.send (Term.chan d) .ex) v .ex))) ms')[
          bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term])))
      (.nu (.par
        (((Proc.tm (M.eval (.pure (.pair v (Term.chan c) .ex .L))))[bindEndpointAt 0 c;
          Term.var_Term])[up_Chan_Chan σ; Term.var_Term])
        ((flattenChildren (.tm (N.eval (.pure (Term.chan d)))) ms')[
          bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term]))) := by
  intro ms'
  induction ms' with
  | nil =>
      intro _ _ σ
      simp only [flattenChildren_nil]
      exact process_step_comEx_edge_tree_symm_csubst (M := M) (N := N) (v := v)
        (c := c) (d := d) value hcv hdv σ
  | cons edge ms'' ih =>
      rcases edge with ⟨e, gc⟩
      intro tyMs mFresh σ
      cases hg : gc.flattenAt with
      | mk dg gp =>
        simp only [flattenChildren, hg,
          (show ∀ (p : Proc) (τ : Nat → Chan),
              (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
            from fun _ _ => rfl),
          (show ∀ (a b : Proc) (τ : Nat → Chan),
              (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
            from fun _ _ _ => rfl)]
        refine TLLC.Process.Step.congr (extrude_one_congr _ _ _) ?_
          (ARS.conv_sym (extrude_one_congr _ _ _))
        refine TLLC.Process.Step.res (process_step_scope_unused_right ?gpFresh ?innerCom)
        case gpFresh =>
          obtain ⟨r', A', tyA', tgc⟩ := tyMs e gc (by simp)
          have hgp : ∀ i, TLLC.Process.procOccurs (i + 1)
              (gp[bindEndpointAt 0 dg; Term.var_Term]) = 0 := by
            intro i; simpa [hg] using tgc.flattenAt_occurs_succ tyA' i
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by rcases k with _ | _ | k <;> simp_all [Process.exch, cexch]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hk1 : k = 1 := by
            rcases k with _ | _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · rfl
            · exfalso
              cases hσ : σ k with
              | var_Chan j => simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
          subst hk1
          apply procOccurs_csubst_zero
          intro k hk
          have hkd : k = chanIndex d + 1 := by
            rcases k with _ | k
            · simp_all [up_Chan_Chan, scons, funcomp, asimp_lemmas]
            · by_cases hkd : k = chanIndex d
              · subst hkd; rfl
              · exfalso
                simp_all [up_Chan_Chan, bindEndpointAt, chanIndex, scons, funcomp, asimp_lemmas]
          subst hkd
          exact hgp (chanIndex d)
        case innerCom =>
          have key := ih (fun e' gc' mem => tyMs e' gc' (List.mem_cons_of_mem _ mem))
            (fun e' gc' mem => mFresh e' gc' (List.mem_cons_of_mem _ mem))
            (fun y => if y = chanIndex e then Chan.var_Chan 0
                      else Chan.var_Chan (chanIndex (σ y) + 1))
          refine TLLC.Process.Step.congr ?congL key ?congR
          case congL =>
            apply process_congr_res
            refine ARS.conv_trans (process_congr_parallel_left ?cA)
              (process_congr_parallel_right ?cF)
            case cF =>
              have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
              asimp
              convert ARS.Conv.refl using 2
              funext x
              clear ih tyMs mFresh key value hcv hdv
              rcases eq_or_ne x (chanIndex d) with rfl | hxd
              · unfold bindEndpointAt
                simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case cA =>
              apply ARS.conv1
              apply TLLC.Process.CongrProc.tm
              asimp
              refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
                (fun _ => (mFresh e gc (by simp)).2.1)
              intro x hx
              rcases eq_or_ne x (chanIndex c) with rfl | hxc
              · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]
          case congR =>
            apply ARS.conv_sym
            apply process_congr_res
            refine ARS.conv_trans (process_congr_parallel_left ?cA')
              (process_congr_parallel_right ?cF')
            case cF' =>
              have hed : chanIndex e ≠ chanIndex d := (mFresh e gc (by simp)).1
              asimp
              convert ARS.Conv.refl using 2
              funext x
              clear ih tyMs mFresh key value hcv hdv
              rcases eq_or_ne x (chanIndex d) with rfl | hxd
              · unfold bindEndpointAt
                simp_all [chanIndex, asimp_lemmas, funcomp, eq_comm]
              rcases eq_or_ne x (chanIndex e) with rfl | hxe
              · simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => simp_all [bindEndpointAt, chanIndex, asimp_lemmas, funcomp]
            case cA' =>
              apply ARS.conv1
              apply TLLC.Process.CongrProc.tm
              asimp
              refine congrTerm_csubst_of_eqv (i := chanIndex e) ?_
                (fun _ => (mFresh e gc (by simp)).2.2)
              intro x hx
              rcases eq_or_ne x (chanIndex c) with rfl | hxc
              · unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp]
              · cases hσ : σ x with
                | var_Chan k => unfold bindEndpointAt; simp_all [chanIndex, asimp_lemmas, funcomp, hx]

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

/-- The explicit-send edge fires on a singleton child list with the child's detached subtrees
as spectators. -/
lemma sendEx_base_step (M N : EvalCtx) (v : Term) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        [(c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs')])[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (Term.chan c))))
        [(c, .node d (N.eval (.pure (.pair v (Term.chan d) .ex .L))) ms' qs')])[σ;
          Term.var_Term]) := by
  simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, flattenBody, parAll_csubst,
    (show ∀ (p : Proc) (τ : Nat → Chan),
        (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
      from fun _ _ => rfl),
    (show ∀ (a b : Proc) (τ : Nat → Chan),
        (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
      from fun _ _ _ => rfl)]
  refine step_par_parAll_spectators _ _ _ _ _ ?ssZero
    (comEx_through_FC M N v c d value hcv hdv ms' tyMs mFresh σ)
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨q1, ⟨q0, hq0mem, rfl⟩, rfl⟩ := hq
  apply procOccurs_csubst_zero; intro k _
  apply procOccurs_csubst_zero; intro j _
  exact qsZero q0 hq0mem j

/-- The explicit-send last-edge step over the `before` siblings. -/
lemma sendEx_over_before (M N : EvalCtx) (v : Term) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (before : List (Chan × Tree)) :
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        (before ++ [(c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs')]))[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (Term.chan c))))
        (before ++ [(c, .node d (N.eval (.pure (.pair v (Term.chan d) .ex .L))) ms' qs')]))[σ;
          Term.var_Term]) := by
  induction before with
  | nil =>
      intro σ
      simpa using sendEx_base_step M N v c d ms' qs' value hcv hdv tyMs mFresh qsZero σ
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f sp =>
          have tailStep := ih (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := sp[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                tailStep)
            using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

/-- The explicit-receive edge fires on a singleton child list. -/
lemma recvEx_base_step (M N : EvalCtx) (v : Term) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.recv (Term.chan c) .ex)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (.pair v (Term.chan c) .ex .L))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.recv (Term.chan c) .ex)))
        [(c, .node d (N.eval (.app (.send (Term.chan d) .ex) v .ex)) ms' qs')])[σ;
          Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (.pair v (Term.chan c) .ex .L))))
        [(c, .node d (N.eval (.pure (Term.chan d))) ms' qs')])[σ; Term.var_Term]) := by
  simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, flattenBody, parAll_csubst,
    (show ∀ (p : Proc) (τ : Nat → Chan),
        (Proc.nu p)[τ; Term.var_Term] = Proc.nu (p[up_Chan_Chan τ; Term.var_Term])
      from fun _ _ => rfl),
    (show ∀ (a b : Proc) (τ : Nat → Chan),
        (Proc.par a b)[τ; Term.var_Term] = Proc.par (a[τ; Term.var_Term]) (b[τ; Term.var_Term])
      from fun _ _ _ => rfl)]
  refine step_par_parAll_spectators _ _ _ _ _ ?ssZero
    (comEx_through_FC_symm M N v c d value hcv hdv ms' tyMs mFresh σ)
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨q1, ⟨q0, hq0mem, rfl⟩, rfl⟩ := hq
  apply procOccurs_csubst_zero; intro k _
  apply procOccurs_csubst_zero; intro j _
  exact qsZero q0 hq0mem j

/-- The explicit-receive last-edge step over the `before` siblings. -/
lemma recvEx_over_before (M N : EvalCtx) (v : Term) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.recv (Term.chan c) .ex)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (.pair v (Term.chan c) .ex .L))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (before : List (Chan × Tree)) :
    ∀ σ : Nat → Chan,
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.recv (Term.chan c) .ex)))
        (before ++ [(c, .node d (N.eval (.app (.send (Term.chan d) .ex) v .ex)) ms' qs')]))[σ;
          Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (.pair v (Term.chan c) .ex .L))))
        (before ++ [(c, .node d (N.eval (.pure (Term.chan d))) ms' qs')]))[σ;
          Term.var_Term]) := by
  induction before with
  | nil =>
      intro σ
      simpa using recvEx_base_step M N v c d ms' qs' value hcv hdv tyMs mFresh qsZero σ
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f sp =>
          have tailStep := ih (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := sp[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ; Term.var_Term])
                tailStep)
            using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

/-- The full explicit-send children-body step: move the selected child last, reorder by the
value partition, fire the com, then hoist the value-occurring siblings under the child. -/
lemma sendEx_bodyStep (M N : EvalCtx) (v : Term) (c d : Chan)
    (ms' qs' : _) (l r : List (Chan × Tree))
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0)
    (tyMs : ∀ e gc, (e, gc) ∈ ms' → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (tySibs : ∀ e sib, (e, sib) ∈ l ++ r → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (nodupSibs : (childLabels (l ++ r)).Nodup)
    (mFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0)
    (sFresh : ∀ e sib, (e, sib) ∈ (splitChildrenByTerm v (l ++ r)).1 →
      chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0)
    (nodupNew : (childLabels ((splitChildrenByTerm v (l ++ r)).1 ++ ms')).Nodup)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (tyChild : ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
        (Tree.node d (N.eval (.recv (Term.chan d) .ex)) ms' qs'))
    (tyR : ∀ e sib, (e, sib) ∈ r → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (distinctR : ∀ e sib, (e, sib) ∈ r → chanIndex c ≠ chanIndex e)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r))[σ; Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (Term.chan c))))
        (sendExChildren v c d N ms' qs' (l ++ r)))[σ; Term.var_Term]) := by
  refine TLLC.Process.Step.congr (process_congr_csubst ?pre σ)
    (sendEx_over_before M N v c d ms' qs' value hcv hdv tyMs mFresh qsZero
      ((splitChildrenByTerm v (l ++ r)).2 ++ (splitChildrenByTerm v (l ++ r)).1) σ)
    (process_congr_csubst ?post σ)
  case pre =>
    refine ARS.conv_trans
      (flattenChildren_move_to_last _ c
        (Tree.node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') l r tyChild tyR distinctR) ?_
    rw [flattenChildren_append _ (l ++ r), flattenChildren_append
      _ ((splitChildrenByTerm v (l ++ r)).2 ++ (splitChildrenByTerm v (l ++ r)).1)]
    exact flattenChildren_partition_congr _ v (l ++ r) tySibs nodupSibs
  case post =>
    rw [show sendExChildren v c d N ms' qs' (l ++ r)
        = (splitChildrenByTerm v (l ++ r)).2 ++
            [(c, Tree.node d (N.eval (.pure (.pair v (Term.chan d) .ex .L)))
              (ms' ++ (splitChildrenByTerm v (l ++ r)).1) qs')] from rfl]
    rw [List.append_assoc]
    refine ARS.conv_trans (flattenChildren_congr_prefix _
      (splitChildrenByTerm v (l ++ r)).2 _ _
      (flattenChildren_hoist_children' (.tm (M.eval (.pure (Term.chan c)))) c d
        (N.eval (.pure (.pair v (Term.chan d) .ex .L))) qs' qsZero
        (splitChildrenByTerm v (l ++ r)).1 ms' ?hoistHyp)) ?rot
    case hoistHyp =>
      intro e gc mem
      refine ⟨(sFresh e gc mem).1, (sFresh e gc mem).2.1, (sFresh e gc mem).2.2, ?_⟩
      obtain ⟨r0, A0, tyA0, tgc⟩ := tySibs e gc (splitChildrenByTerm_mem₁ mem).1
      exact fun k => tgc.flattenAt_occurs_succ tyA0 k
    case rot =>
      refine flattenChildren_congr_prefix _ (splitChildrenByTerm v (l ++ r)).2 _ _ ?_
      refine flattenChildren_node_congr _ c d _ _ _ _ _ _ ?_
      have hin := flattenChildren_rotate_congr
        (.tm (N.eval (.pure (.pair v (Term.chan d) .ex .L))))
        (splitChildrenByTerm v (l ++ r)).1 ms'
        (by
          intro e sib mem
          rcases List.mem_append.mp mem with h | h
          · exact tySibs e sib (splitChildrenByTerm_mem₁ h).1
          · exact tyMs e sib h)
        nodupNew
      simp only [flattenBody]
      exact process_congr_parAll_accumulator _ hin

/-- The full explicit-receive children-body step: reorder the child's grandchildren by the value
partition, hoist the value-occurring ones out to the parent, then fire the com. -/
lemma recvEx_bodyStep (M N : EvalCtx) (v : Term) (c d : Chan)
    (ms' qs' : _) (l r : List (Chan × Tree))
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0)
    (tyKids : ∀ e gc, (e, gc) ∈ ms' → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (nodupKids : (childLabels ms').Nodup)
    (kidFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.recv (Term.chan c) .ex)) = 0)
    (s2Fresh : ∀ e gc, (e, gc) ∈ (splitChildrenByTerm v ms').2 →
      occurs (chanIndex e) (M.eval (.pure (.pair v (Term.chan c) .ex .L))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (tyChild : ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
        (Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex)) ms' qs'))
    (tyR : ∀ e sib, (e, sib) ∈ r → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (distinctR : ∀ e sib, (e, sib) ∈ r → chanIndex c ≠ chanIndex e)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((flattenChildren (.tm (M.eval (.recv (Term.chan c) .ex)))
        (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .ex) v .ex)) ms' qs') :: r))[σ;
          Term.var_Term])
      ((flattenChildren (.tm (M.eval (.pure (.pair v (Term.chan c) .ex .L))))
        (recvExChildren v c d N ms' qs' (l ++ r)))[σ; Term.var_Term]) := by
  have s2sub : ∀ e gc, (e, gc) ∈ (splitChildrenByTerm v ms').2 → (e, gc) ∈ ms' :=
    fun e gc mem => (splitChildrenByTerm_mem₂ mem).1
  have s1sub : ∀ e gc, (e, gc) ∈ (splitChildrenByTerm v ms').1 → (e, gc) ∈ ms' :=
    fun e gc mem => (splitChildrenByTerm_mem₁ mem).1
  have mFresh : ∀ e gc, (e, gc) ∈ (splitChildrenByTerm v ms').2 →
      chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.recv (Term.chan c) .ex)) = 0 ∧
      occurs (chanIndex e) (M.eval (.pure (.pair v (Term.chan c) .ex .L))) = 0 :=
    fun e gc mem => ⟨(kidFresh e gc (s2sub e gc mem)).2.1,
      (kidFresh e gc (s2sub e gc mem)).2.2, s2Fresh e gc mem⟩
  refine TLLC.Process.Step.congr (process_congr_csubst ?pre σ)
    (recvEx_over_before M N v c d (splitChildrenByTerm v ms').2 qs' value hcv hdv
      (fun e gc mem => tyKids e gc (s2sub e gc mem)) mFresh qsZero
      ((l ++ r) ++ (splitChildrenByTerm v ms').1) σ)
    (process_congr_csubst ?post σ)
  case pre =>
    refine ARS.conv_trans
      (flattenChildren_move_to_last _ c
        (Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex)) ms' qs') l r
        tyChild tyR distinctR) ?_
    -- reorder the child's own children into `s1 ++ s2`
    have hperm2 : (childLabels ((splitChildrenByTerm v ms').2 ++
        (splitChildrenByTerm v ms').1)).Nodup := by
      have hp := splitChildrenByTerm_perm v ms'
      have : List.Perm (childLabels ((splitChildrenByTerm v ms').2 ++
          (splitChildrenByTerm v ms').1)) (childLabels ms') := hp.map _
      exact this.nodup_iff.mpr nodupKids
    have hchild : TLLC.Process.Congruence
        (flattenChildren (.tm (M.eval (.recv (Term.chan c) .ex)))
          ((l ++ r) ++ [(c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
            ms' qs')]))
        (flattenChildren (.tm (M.eval (.recv (Term.chan c) .ex)))
          ((l ++ r) ++ [(c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
            ((splitChildrenByTerm v ms').1 ++ (splitChildrenByTerm v ms').2) qs')])) := by
      refine flattenChildren_congr_prefix _ (l ++ r) _ _ ?_
      refine flattenChildren_node_congr _ c d _ _ _ _ _ _ ?_
      have hin := ARS.conv_trans
        (flattenChildren_partition_congr
          (.tm (N.eval (.app (.send (Term.chan d) .ex) v .ex))) v ms' tyKids nodupKids)
        (flattenChildren_rotate_congr
          (.tm (N.eval (.app (.send (Term.chan d) .ex) v .ex)))
          (splitChildrenByTerm v ms').2 (splitChildrenByTerm v ms').1
          (by
            intro e sib mem
            rcases List.mem_append.mp mem with h | h
            · exact tyKids e sib (s2sub e sib h)
            · exact tyKids e sib (s1sub e sib h))
          hperm2)
      simp only [flattenBody]
      exact process_congr_parAll_accumulator _ hin
    refine ARS.conv_trans hchild ?_
    -- hoist the value-occurring grandchildren out of the child
    refine ARS.conv_trans (flattenChildren_congr_prefix _ (l ++ r) _ _
      (ARS.conv_sym
        (flattenChildren_hoist_children' (.tm (M.eval (.recv (Term.chan c) .ex))) c d
          (N.eval (.app (.send (Term.chan d) .ex) v .ex)) qs' qsZero
          (splitChildrenByTerm v ms').1 (splitChildrenByTerm v ms').2 ?hoistHyp))) ?_
    case hoistHyp =>
      intro e gc mem
      have hk := kidFresh e gc (s1sub e gc mem)
      refine ⟨hk.1, hk.2.1, hk.2.2, ?_⟩
      obtain ⟨r0, A0, tyA0, tgc⟩ := tyKids e gc (s1sub e gc mem)
      exact fun k => tgc.flattenAt_occurs_succ tyA0 k
    rw [← List.append_assoc]
    exact ARS.Conv.refl
  case post =>
    rw [show recvExChildren v c d N ms' qs' (l ++ r)
        = (l ++ r) ++ (splitChildrenByTerm v ms').1 ++
            [(c, Tree.node d (N.eval (.pure (Term.chan d)))
              (splitChildrenByTerm v ms').2 qs')] from rfl]
    exact ARS.Conv.refl


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

/-- `parAll` over an appended list. -/
lemma parAll_append (a : Proc) (l1 l2 : List Proc) :
    parAll a (l1 ++ l2) = parAll (parAll a l1) l2 := by
  simp [parAll, List.foldl_append]

/-- `parAll` congruence under permutation of the spectator list. -/
lemma process_congr_parAll_perm (X : Proc) {l1 l2 : List Proc} (h : List.Perm l1 l2) :
    TLLC.Process.Congruence (parAll X l1) (parAll X l2) := by
  induction h generalizing X with
  | nil => exact ARS.Conv.refl
  | cons a _ ih =>
      simp only [parAll_cons]
      exact ih (.par X a)
  | swap a b l =>
      simp only [parAll_cons]
      exact process_congr_parAll_accumulator l (process_congr_swap_right (a := X) (b := b) (c := a))
  | trans _ _ ih1 ih2 =>
      exact ARS.conv_trans (ih1 X) (ih2 X)

/-- A congruence of flatten bases lifts through the child wrappers. -/
lemma process_congr_flattenChildren_base {b1 b2 : Proc} (children : List (Chan × Tree))
    (h : TLLC.Process.Congruence b1 b2) :
    TLLC.Process.Congruence (flattenChildren b1 children) (flattenChildren b2 children) := by
  have hh := process_congr_flattenChildren_body_csubst children
    (fun σ => process_congr_csubst h σ) Chan.var_Chan
  have e1 : (flattenChildren b1 children)[Chan.var_Chan; Term.var_Term]
      = flattenChildren b1 children := by asimp
  have e2 : (flattenChildren b2 children)[Chan.var_Chan; Term.var_Term]
      = flattenChildren b2 children := by asimp
  rw [e1, e2] at hh
  exact hh

/-- A closed `parAll` tail at the flatten base floats out of all child wrappers. -/
lemma flattenChildren_float_parAll (SS : List Proc)
    (ssClosed : ∀ q, q ∈ SS → ∀ i, TLLC.Process.procOccurs i q = 0) :
    ∀ (W : List (Chan × Tree)) (body : Proc),
    TLLC.Process.Congruence
      (flattenChildren (parAll body SS) W)
      (parAll (flattenChildren body W) SS) := by
  intro W
  induction W with
  | nil =>
      intro body
      simp only [flattenChildren_nil]
      exact ARS.Conv.refl
  | cons edge W' ih =>
      intro body
      rcases edge with ⟨e, sib⟩
      cases hsib : sib.flattenAt with
      | mk f sp =>
          have hunf : ∀ b : Proc, flattenChildren b ((e, sib) :: W')
              = .nu (.par ((flattenChildren b W')[bindEndpointAt 0 e; Term.var_Term])
                  (sp[bindEndpointAt 0 f; Term.var_Term])) := by
            intro b
            simp only [flattenChildren, hsib]
          rw [hunf, hunf]
          have pushSS : TLLC.Process.Congruence
              ((parAll (flattenChildren body W') SS)[bindEndpointAt 0 e; Term.var_Term])
              (parAll ((flattenChildren body W')[bindEndpointAt 0 e; Term.var_Term]) SS) := by
            rw [parAll_csubst]
            conv_rhs => rw [show SS = SS.map id from (List.map_id SS).symm]
            exact process_congr_parAll_map_pointwise _ _ _ SS
              (fun q hq => process_congr_closed_csubst_id (fun i => ssClosed q hq i) _)
          have inner : TLLC.Process.Congruence
              (.par (parAll ((flattenChildren body W')[bindEndpointAt 0 e; Term.var_Term]) SS)
                (sp[bindEndpointAt 0 f; Term.var_Term]))
              (parAll (.par ((flattenChildren body W')[bindEndpointAt 0 e; Term.var_Term])
                (sp[bindEndpointAt 0 f; Term.var_Term])) SS) := by
            refine ARS.conv_trans (ARS.conv1 TLLC.Process.CongrProc.par_sym) ?_
            refine ARS.conv_trans (process_congr_par_parAll_right _ _ _) ?_
            exact process_congr_parAll_accumulator SS
              (ARS.conv1 TLLC.Process.CongrProc.par_sym)
          refine ARS.conv_trans (process_congr_res (process_congr_parallel_left
            (process_congr_csubst (ih body) _))) ?_
          refine ARS.conv_trans (process_congr_res (process_congr_parallel_left pushSS)) ?_
          refine ARS.conv_trans (process_congr_res inner) ?_
          exact ARS.conv_sym (process_congr_parAll_scope_closed _ SS ssClosed)

/-- Extract a node child's closed detached subtrees to the top level of a singleton flatten. -/
lemma flattenChildren_single_extract (B : Proc) (c d : Chan) (m'' : Term)
    (kids : List (Chan × Tree)) (qsC : List Tree)
    (qsZero : ∀ q, q ∈ flattenSubtrees qsC → ∀ i, TLLC.Process.procOccurs i q = 0) :
    TLLC.Process.Congruence
      (flattenChildren B [(c, .node d m'' kids qsC)])
      (parAll (flattenChildren B [(c, .node d m'' kids [])]) (flattenSubtrees qsC)) := by
  have hunf1 : flattenChildren B [(c, Tree.node d m'' kids qsC)]
      = .nu (.par (B[bindEndpointAt 0 c; Term.var_Term])
          ((parAll (flattenChildren (.tm m'') kids) (flattenSubtrees qsC))[bindEndpointAt 0 d;
            Term.var_Term])) := by
    simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, flattenBody]
  have hunf2 : flattenChildren B [(c, Tree.node d m'' kids [])]
      = .nu (.par (B[bindEndpointAt 0 c; Term.var_Term])
          ((flattenChildren (.tm m'') kids)[bindEndpointAt 0 d; Term.var_Term])) := by
    simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, flattenBody,
      flattenSubtrees_nil, parAll_nil]
  rw [hunf1, hunf2]
  have pushSS : TLLC.Process.Congruence
      ((parAll (flattenChildren (.tm m'') kids) (flattenSubtrees qsC))[bindEndpointAt 0 d;
        Term.var_Term])
      (parAll ((flattenChildren (.tm m'') kids)[bindEndpointAt 0 d; Term.var_Term])
        (flattenSubtrees qsC)) := by
    rw [parAll_csubst]
    conv_rhs => rw [show flattenSubtrees qsC = (flattenSubtrees qsC).map id
      from (List.map_id _).symm]
    exact process_congr_parAll_map_pointwise _ _ _ (flattenSubtrees qsC)
      (fun q hq => process_congr_closed_csubst_id (fun i => qsZero q hq i) _)
  refine ARS.conv_trans (process_congr_res (process_congr_parallel_right pushSS)) ?_
  refine ARS.conv_trans (process_congr_res (process_congr_par_parAll_right _ _ _)) ?_
  exact ARS.conv_sym (process_congr_parAll_scope_closed _ _ qsZero)

/-- Flip a bare parent/child edge: both endpoints bind to the same fresh channel, so the two
orientations are `par`-symmetric. -/
lemma flattenChildren_flip_edge (mP mC : Term) (c d : Chan) :
    TLLC.Process.Congruence
      (flattenChildren (.tm mP) [(c, .node d mC [] [])])
      (flattenChildren (.tm mC) [(d, .node c mP [] [])]) := by
  have hunf : ∀ (a b : Term) (x y : Chan), flattenChildren (.tm a) [(x, Tree.node y b [] [])]
      = .nu (.par ((Proc.tm a)[bindEndpointAt 0 x; Term.var_Term])
          ((Proc.tm b)[bindEndpointAt 0 y; Term.var_Term])) := by
    intro a b x y
    simp only [flattenChildren, flattenChildren_nil, Tree.flattenAt_node, flattenBody,
      flattenSubtrees_nil, parAll_nil]
  rw [hunf, hunf]
  exact process_congr_res (ARS.conv1 TLLC.Process.CongrProc.par_sym)


/-- Outer `parAll` groups commute. -/
lemma parAll_parAll_swap (X : Proc) (A B : List Proc) :
    TLLC.Process.Congruence (parAll (parAll X A) B) (parAll (parAll X B) A) := by
  rw [← parAll_append, ← parAll_append]
  exact process_congr_parAll_perm X (List.perm_append_comm)

/-- The full forward children-body step: re-root the selected edge by structural congruence
(the old parent becomes a child of the receiver), then fire the explicit com in the new
orientation. -/
lemma forward_bodyStep (M N : EvalCtx) (v : Term) (c d : Chan)
    (ms' : List (Chan × Tree)) (qs qs' : List Tree) (l r : List (Chan × Tree))
    (value : Val v)
    (hcv : occurs (chanIndex c) v = 0)
    (hdv : occurs (chanIndex d) v = 0)
    (tyKids : ∀ e gc, (e, gc) ∈ ms' → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) gc)
    (tySibs : ∀ e sib, (e, sib) ∈ l ++ r → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (nodupSibs : (childLabels (l ++ r)).Nodup)
    (nodupKids : (childLabels ms').Nodup)
    (disjKidsSibs : ∀ a, a ∈ childLabels (l ++ r) → a ∉ childLabels ms')
    (kidFresh : ∀ e gc, (e, gc) ∈ ms' →
      chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0)
    (sibW2 : ∀ e sib, (e, sib) ∈ (splitChildrenByTerm v (l ++ r)).2 →
      chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
      occurs (chanIndex e) (N.eval (.recv (Term.chan d) .ex)) = 0 ∧
      occurs (chanIndex e) (N.eval (.pure (.pair v (Term.chan d) .ex .L))) = 0)
    (qsZero : ∀ q, q ∈ flattenSubtrees qs → ∀ i, TLLC.Process.procOccurs i q = 0)
    (qsZero' : ∀ q, q ∈ flattenSubtrees qs' → ∀ i, TLLC.Process.procOccurs i q = 0)
    (tyChild : ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
        (Tree.node d (N.eval (.recv (Term.chan d) .ex)) ms' qs'))
    (tyR : ∀ e sib, (e, sib) ∈ r → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib)
    (distinctR : ∀ e sib, (e, sib) ∈ r → chanIndex c ≠ chanIndex e)
    (σ : Nat → Chan) :
    TLLC.Process.Step
      ((parAll (flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r))
        (flattenSubtrees qs))[σ; Term.var_Term])
      ((parAll (flattenChildren (.tm (N.eval (.pure (.pair v (Term.chan d) .ex .L))))
        (forwardChildren v c d M ms' (l ++ r) qs))
        (flattenSubtrees qs'))[σ; Term.var_Term]) := by
  set W1 := (splitChildrenByTerm v (l ++ r)).1 with hW1
  set W2 := (splitChildrenByTerm v (l ++ r)).2 with hW2
  have tyW1 : ∀ e sib, (e, sib) ∈ W1 → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib :=
    fun e sib mem => tySibs e sib (splitChildrenByTerm_mem₁ mem).1
  have tyW2 : ∀ e sib, (e, sib) ∈ W2 → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
      TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib :=
    fun e sib mem => tySibs e sib (splitChildrenByTerm_mem₂ mem).1
  have permSibs : List.Perm (childLabels (W2 ++ W1)) (childLabels (l ++ r)) :=
    (splitChildrenByTerm_perm v (l ++ r)).map _
  have nodupW21 : (childLabels (W2 ++ W1)).Nodup := permSibs.nodup_iff.mpr nodupSibs
  -- === the re-rooting congruence (identity level) ===
  -- L1: move-to-last + partition
  have congL1 : TLLC.Process.Congruence
      (flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r))
      (flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        ((W2 ++ W1) ++ [(c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs')])) := by
    refine ARS.conv_trans
      (flattenChildren_move_to_last _ c
        (Tree.node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') l r tyChild tyR distinctR) ?_
    rw [flattenChildren_append _ (l ++ r), flattenChildren_append _ (W2 ++ W1)]
    exact flattenChildren_partition_congr _ v (l ++ r) tySibs nodupSibs
  -- L2: hoist the child's kids out
  have congL2 : TLLC.Process.Congruence
      (flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        ((W2 ++ W1) ++ [(c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs')]))
      (flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        (((W2 ++ W1) ++ ms') ++ [(c, .node d (N.eval (.recv (Term.chan d) .ex)) [] qs')])) := by
    have h := flattenChildren_hoist_children'
      (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex))) c d
      (N.eval (.recv (Term.chan d) .ex)) qs' qsZero' ms' []
      (by
        intro e gc mem
        obtain ⟨rr, A0, tyA0, tgc⟩ := tyKids e gc mem
        exact ⟨(kidFresh e gc mem).1, (kidFresh e gc mem).2.1, (kidFresh e gc mem).2.2,
          fun k => tgc.flattenAt_occurs_succ tyA0 k⟩)
    rw [show ((W2 ++ W1) ++ ms') ++
          [(c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) [] qs')]
        = (W2 ++ W1) ++ (ms' ++
          [(c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) [] qs')]) from by
      rw [List.append_assoc]]
    refine flattenChildren_congr_prefix _ (W2 ++ W1) _ _ ?_
    simpa using ARS.conv_sym h
  -- L3: extract the child's detached subtrees
  have congL3 : TLLC.Process.Congruence
      (flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        (((W2 ++ W1) ++ ms') ++ [(c, .node d (N.eval (.recv (Term.chan d) .ex)) [] qs')]))
      (parAll (flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        (((W2 ++ W1) ++ ms') ++ [(c, .node d (N.eval (.recv (Term.chan d) .ex)) [] [])]))
        (flattenSubtrees qs')) := by
    rw [flattenChildren_append _ ((W2 ++ W1) ++ ms'),
        flattenChildren_append _ ((W2 ++ W1) ++ ms')]
    refine ARS.conv_trans (process_congr_flattenChildren_base _
      (flattenChildren_single_extract _ c d (N.eval (.recv (Term.chan d) .ex)) [] qs'
        qsZero')) ?_
    exact flattenChildren_float_parAll (flattenSubtrees qs') qsZero' _ _
  -- L4: flip the innermost edge
  have congL4 : TLLC.Process.Congruence
      (flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        (((W2 ++ W1) ++ ms') ++ [(c, .node d (N.eval (.recv (Term.chan d) .ex)) [] [])]))
      (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        (((W2 ++ W1) ++ ms') ++
          [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) [] [])])) := by
    rw [flattenChildren_append _ ((W2 ++ W1) ++ ms'),
        flattenChildren_append _ ((W2 ++ W1) ++ ms')]
    exact process_congr_flattenChildren_base _
      (flattenChildren_flip_edge (M.eval (.app (.send (Term.chan c) .ex) v .ex))
        (N.eval (.recv (Term.chan d) .ex)) c d)
  -- L5: reorder the wrappers to `(ms' ++ W1) ++ W2`
  have congL5 : TLLC.Process.Congruence
      (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        (((W2 ++ W1) ++ ms') ++
          [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) [] [])]))
      (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        (((ms' ++ W1) ++ W2) ++
          [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) [] [])])) := by
    rw [flattenChildren_append _ ((W2 ++ W1) ++ ms'),
        flattenChildren_append _ ((ms' ++ W1) ++ W2)]
    have tyAll : ∀ e sib, (e, sib) ∈ (W2 ++ W1) ++ ms' →
        ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
      intro e sib mem
      rcases List.mem_append.mp mem with h | h
      · rcases List.mem_append.mp h with h | h
        · exact tyW2 e sib h
        · exact tyW1 e sib h
      · exact tyKids e sib h
    have nodupAll : (childLabels ((W2 ++ W1) ++ ms')).Nodup := by
      rw [show childLabels ((W2 ++ W1) ++ ms')
          = childLabels (W2 ++ W1) ++ childLabels ms' from by simp [childLabels]]
      refine List.Nodup.append nodupW21 nodupKids ?_
      intro a ha1 ha2
      exact disjKidsSibs a (permSibs.subset ha1) ha2
    refine ARS.conv_trans (flattenChildren_rotate_congr _ (W2 ++ W1) ms' tyAll nodupAll) ?_
    have tyAll2 : ∀ e sib, (e, sib) ∈ W2 ++ W1 →
        ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
      intro e sib mem
      rcases List.mem_append.mp mem with h | h
      · exact tyW2 e sib h
      · exact tyW1 e sib h
    have hrot2 := flattenChildren_rotate_congr
      (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) [] [])])
      W2 W1 tyAll2 nodupW21
    refine ARS.conv_trans (flattenChildren_congr_prefix _ ms' _ _ hrot2) ?_
    rw [show ms' ++ (W1 ++ W2) = (ms' ++ W1) ++ W2 from by rw [List.append_assoc]]
    exact ARS.Conv.refl
  -- L6: hoist `W2` into the flipped child
  have congL6 : TLLC.Process.Congruence
      (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        (((ms' ++ W1) ++ W2) ++
          [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) [] [])]))
      (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        ((ms' ++ W1) ++
          [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) W2 [])])) := by
    have h := flattenChildren_hoist_children'
      (.tm (N.eval (.recv (Term.chan d) .ex))) d c
      (M.eval (.app (.send (Term.chan c) .ex) v .ex)) [] (by simp) W2 []
      (by
        intro e sib mem
        obtain ⟨rr, A0, tyA0, tsib⟩ := tyW2 e sib mem
        exact ⟨(sibW2 e sib mem).2.1, (sibW2 e sib mem).1, (sibW2 e sib mem).2.2.1,
          fun k => tsib.flattenAt_occurs_succ tyA0 k⟩)
    rw [List.append_assoc]
    refine flattenChildren_congr_prefix _ (ms' ++ W1) _ _ ?_
    simpa using h
  -- L7: insert `qs` as the flipped child's detached subtrees
  have congL7 : TLLC.Process.Congruence
      (parAll (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        ((ms' ++ W1) ++
          [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) W2 [])]))
        (flattenSubtrees qs))
      (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        ((ms' ++ W1) ++
          [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) W2 qs)])) := by
    rw [flattenChildren_append _ (ms' ++ W1), flattenChildren_append _ (ms' ++ W1)]
    refine ARS.conv_trans (ARS.conv_sym
      (flattenChildren_float_parAll (flattenSubtrees qs) qsZero _ _)) ?_
    refine process_congr_flattenChildren_base _ ?_
    exact ARS.conv_sym (flattenChildren_single_extract _ d c
      (M.eval (.app (.send (Term.chan c) .ex) v .ex)) W2 qs qsZero)
  -- assemble the full congruence, apply the com, and close
  have preCong : TLLC.Process.Congruence
      (parAll (flattenChildren (.tm (M.eval (.app (.send (Term.chan c) .ex) v .ex)))
        (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r))
        (flattenSubtrees qs))
      (parAll (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        ((ms' ++ W1) ++
          [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) W2 qs)]))
        (flattenSubtrees qs')) := by
    refine ARS.conv_trans (process_congr_parAll_accumulator _
      (ARS.conv_trans congL1 (ARS.conv_trans congL2 congL3))) ?_
    refine ARS.conv_trans (parAll_parAll_swap _ _ _) ?_
    refine process_congr_parAll_accumulator _ ?_
    refine ARS.conv_trans (process_congr_parAll_accumulator _
      (ARS.conv_trans congL4 (ARS.conv_trans congL5 congL6))) ?_
    exact congL7
  have comStep := recvEx_over_before N M v d c W2 qs value hdv hcv tyW2
    (fun e sib mem => ⟨(sibW2 e sib mem).1, (sibW2 e sib mem).2.2.1,
      (sibW2 e sib mem).2.2.2⟩)
    qsZero (ms' ++ W1) σ
  have main : TLLC.Process.Step
      ((parAll (flattenChildren (.tm (N.eval (.recv (Term.chan d) .ex)))
        ((ms' ++ W1) ++
          [(d, .node c (M.eval (.app (.send (Term.chan c) .ex) v .ex)) W2 qs)]))
        (flattenSubtrees qs'))[σ; Term.var_Term])
      ((parAll (flattenChildren (.tm (N.eval (.pure (.pair v (Term.chan d) .ex .L))))
        ((ms' ++ W1) ++
          [(d, .node c (M.eval (.pure (Term.chan c))) W2 qs)]))
        (flattenSubtrees qs'))[σ; Term.var_Term]) := by
    rw [parAll_csubst, parAll_csubst]
    exact process_step_parAll_accumulator _ comStep
  refine TLLC.Process.Step.congr (process_congr_csubst preCong σ) main
    (process_congr_csubst ?post σ)
  case post =>
    rw [show forwardChildren v c d M ms' (l ++ r) qs
        = ms' ++ (splitChildrenByTerm v (l ++ r)).1 ++
            [(d, Tree.node c (M.eval (.pure (Term.chan c)))
              (splitChildrenByTerm v (l ++ r)).2 qs)] from rfl]
    rw [show (ms' ++ W1) ++ [(d, Tree.node c (M.eval (.pure (Term.chan c))) W2 qs)]
        = ms' ++ (W1 ++ [(d, Tree.node c (M.eval (.pure (Term.chan c))) W2 qs)]) from by
      rw [List.append_assoc]]
    exact ARS.Conv.refl

/-- Lemma 5.86 for productive spawning-tree steps, strengthened under channel substitution. -/
theorem simulation_csubst {p q : Tree}
    (typed : Typed p ∨ ∃ r A, TypedAt r A p)
    (distinct : Distinct p)
    (step : Step p q) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step (p.flatten[σ; Term.var_Term]) (q.flatten[σ; Term.var_Term]) := by
  induction step with
  | rootFork freshC freshD =>
      rename_i M A m c d children subtrees
      have freshC' : occurs (chanIndex c) (M.eval (.fork A m)) = 0 := by
        cases c with | var_Chan cx => exact freshC
      have freshD' : occurs (chanIndex d) (M.eval (.fork A m)) = 0 := by
        cases d with | var_Chan dx => exact freshD
      have tyMs : ∀ e sib, (e, sib) ∈ children → ∃ r A', ([] : Static.Ctx) ⊢ A' : .proto ∧
          TypedAt r (A'⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedRoot => exact typedRoot.child_typedAt_wf mem
        | inr h => obtain ⟨r, A', h⟩ := h; cases h
      have nodup : (childLabels children).Nodup := by
        cases typed with
        | inl ty =>
            cases ty with
            | root _ _ typedChildren _ => exact typedChildren.labels_nodup
        | inr ty => obtain ⟨r, A', ty⟩ := ty; cases ty
      have linear : ∀ e sib, (e, sib) ∈ children →
          occurs (chanIndex e) (M.eval (.fork A m)) ≤ 1 := by
        intro e sib mem
        cases typed with
        | inl ty =>
            cases ty with
            | root single typedTerm typedChildren typedSubtrees =>
                exact le_of_eq (typedTerm.occurs1 (typedChildren.pos_of_label
                  (List.mem_map.mpr ⟨(e, sib), mem, rfl⟩)))
        | inr ty => obtain ⟨r, A', ty⟩ := ty; cases ty
      intro σ
      have bodyStep := fork_bodyStep M A m c d children freshC' freshD' tyMs nodup linear σ
      simpa [Tree.flatten_root, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | nodeFork freshC freshD =>
      rename_i M parent A m c d children subtrees
      have freshC' : occurs (chanIndex c) (M.eval (.fork A m)) = 0 := by
        cases c with | var_Chan cx => exact freshC
      have freshD' : occurs (chanIndex d) (M.eval (.fork A m)) = 0 := by
        cases d with | var_Chan dx => exact freshD
      have tyMs : ∀ e sib, (e, sib) ∈ children → ∃ r A', ([] : Static.Ctx) ⊢ A' : .proto ∧
          TypedAt r (A'⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl ty => cases ty
        | inr h =>
            obtain ⟨r, A', h⟩ := h
            exact h.child_typedAt_wf mem
      have nodup : (childLabels children).Nodup := by
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A', ty⟩ := ty
            cases ty with
            | node _ _ _ typedChildren _ => exact typedChildren.labels_nodup
      have linear : ∀ e sib, (e, sib) ∈ children →
          occurs (chanIndex e) (M.eval (.fork A m)) ≤ 1 := by
        intro e sib mem
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A', ty⟩ := ty
            cases ty with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact le_of_eq (typedTerm.occurs1 (typedChildren.pos_of_label
                  (List.mem_map.mpr ⟨(e, sib), mem, rfl⟩)))
      intro σ
      have bodyStep := fork_bodyStep M A m c d children freshC' freshD' tyMs nodup linear σ
      simpa [Tree.flatten_node, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | rootWait =>
      rename_i M N c d before after childChildren subtrees childSubtrees
      have labels :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees) ::
                after)).Nodup := by
        cases typed with
        | inl ty =>
            cases ty with
            | root _ _ typedChildren _ =>
                exact typedChildren.labels_nodup
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty
      have cAfter := childLabel_notin_after labels
      have pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0 := by
        cases typed with
        | inl ty =>
            exact ty.close_unused (by simp [childLabels])
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees) := by
        cases typed with
        | inl ty =>
            exact ty.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees)
              (by simp)
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have cUnused := typedChild.parent_close_unused
      have memSel :
          (c, Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees) ::
                after := by simp
      have hnodup := labelsInteriors_sublist_root.nodup distinct
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.close false (Term.chan c))) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure .one)) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have hzero : occurs (chanIndex e) (M.eval (.close false (Term.chan c))) = 0 := by
          cases typed with
          | inl typedRoot =>
              cases typedRoot with
              | root single typedTerm typedChildren typedSubtrees =>
                  exact typedTerm.occurs0 (typedChildren.notLabel_false hfresh.2)
          | inr typedAtRoot => obtain ⟨r, A, h⟩ := typedAtRoot; cases h
        refine ⟨hfresh.1, hzero, ?_⟩
        have hec : chanIndex e ≠ chanIndex c := by
          intro h
          apply hfresh.2
          have hce : e = c := by
            cases e with
            | var_Chan ex => cases c with
              | var_Chan cx => simp only [chanIndex] at h; rw [h]
          rw [hce]
          exact List.mem_map.mpr ⟨(c, _), memSel, rfl⟩
        rw [← close_term_occurs_eq M false c (chanIndex e) hec]
        exact hzero
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have detachedZero := typedChild.close_detached_occurs0
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
        | inr typedAtRoot => obtain ⟨r, A, h⟩ := typedAtRoot; cases h
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := end_bodyStep M N false c d childChildren childSubtrees before after
        pUnused cUnused (fun e gc mem => typedChild.child_typedAt_wf mem) mFresh qsZero
        detachedZero ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_root, flattenBody, parAll_csubst, flattenSubtrees_eq_map,
        List.map_append] using
        TLLC.Process.Step.congr ARS.Conv.refl
          (process_step_parAll_accumulator
            ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep)
          (process_congr_parAll_push_right _ _ _)
  | nodeWait =>
      rename_i M N parent c d before after childChildren subtrees childSubtrees
      have labels :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees) ::
                after)).Nodup := by
        cases typed with
        | inl ty =>
            cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node _ _ _ typedChildren _ =>
                exact typedChildren.labels_nodup
      have cAfter := childLabel_notin_after labels
      have pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0 := by
        cases typed with
        | inl ty =>
            cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.close_unused (by simp [childLabels])
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees) := by
        cases typed with
        | inl ty =>
            cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees)
              (by simp)
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have cUnused := typedChild.parent_close_unused
      have memSel :
          (c, Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.close true (Term.chan d))) childChildren childSubtrees) ::
                after := by simp
      have hnodup := labelsInteriors_sublist_node.nodup distinct
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.close false (Term.chan c))) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure .one)) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have eParent := grandchild_ne_node_parent distinct memSel memGc
        have hzero : occurs (chanIndex e) (M.eval (.close false (Term.chan c))) = 0 := by
          cases typed with
          | inl typedNode => cases typedNode
          | inr typedAtNode =>
              obtain ⟨r, A, typedAtNode⟩ := typedAtNode
              cases typedAtNode with
              | node single has typedTerm typedChildren typedSubtrees =>
                  exact typedTerm.occurs0 (typedChildren.notLabel_false hfresh.2 eParent)
        refine ⟨hfresh.1, hzero, ?_⟩
        have hec : chanIndex e ≠ chanIndex c := by
          intro h
          apply hfresh.2
          have hce : e = c := by
            cases e with
            | var_Chan ex => cases c with
              | var_Chan cx => simp only [chanIndex] at h; rw [h]
          rw [hce]
          exact List.mem_map.mpr ⟨(c, _), memSel, rfl⟩
        rw [← close_term_occurs_eq M false c (chanIndex e) hec]
        exact hzero
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have detachedZero := typedChild.close_detached_occurs0
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedNode => cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact typedAtNode.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := end_bodyStep M N false c d childChildren childSubtrees before after
        pUnused cUnused (fun e gc mem => typedChild.child_typedAt_wf mem) mFresh qsZero
        detachedZero ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_node, flattenBody, parAll_csubst, flattenSubtrees_eq_map,
        List.map_append] using
        TLLC.Process.Step.congr ARS.Conv.refl
          (process_step_parAll_accumulator
            ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep)
          (process_congr_parAll_push_right _ _ _)
  | rootClose =>
      rename_i M N c d before after childChildren subtrees childSubtrees
      have labels :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees) ::
                after)).Nodup := by
        cases typed with
        | inl ty =>
            cases ty with
            | root _ _ typedChildren _ =>
                exact typedChildren.labels_nodup
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty
      have cAfter := childLabel_notin_after labels
      have pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0 := by
        cases typed with
        | inl ty =>
            exact ty.close_unused (by simp [childLabels])
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees) := by
        cases typed with
        | inl ty =>
            exact ty.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees)
              (by simp)
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have cUnused := typedChild.parent_close_unused
      have memSel :
          (c, Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees) ::
                after := by simp
      have hnodup := labelsInteriors_sublist_root.nodup distinct
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.close true (Term.chan c))) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure .one)) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have hzero : occurs (chanIndex e) (M.eval (.close true (Term.chan c))) = 0 := by
          cases typed with
          | inl typedRoot =>
              cases typedRoot with
              | root single typedTerm typedChildren typedSubtrees =>
                  exact typedTerm.occurs0 (typedChildren.notLabel_false hfresh.2)
          | inr typedAtRoot => obtain ⟨r, A, h⟩ := typedAtRoot; cases h
        refine ⟨hfresh.1, hzero, ?_⟩
        have hec : chanIndex e ≠ chanIndex c := by
          intro h
          apply hfresh.2
          have hce : e = c := by
            cases e with
            | var_Chan ex => cases c with
              | var_Chan cx => simp only [chanIndex] at h; rw [h]
          rw [hce]
          exact List.mem_map.mpr ⟨(c, _), memSel, rfl⟩
        rw [← close_term_occurs_eq M true c (chanIndex e) hec]
        exact hzero
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have detachedZero := typedChild.close_detached_occurs0
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
        | inr typedAtRoot => obtain ⟨r, A, h⟩ := typedAtRoot; cases h
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := end_bodyStep M N true c d childChildren childSubtrees before after
        pUnused cUnused (fun e gc mem => typedChild.child_typedAt_wf mem) mFresh qsZero
        detachedZero ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_root, flattenBody, parAll_csubst, flattenSubtrees_eq_map,
        List.map_append] using
        TLLC.Process.Step.congr ARS.Conv.refl
          (process_step_parAll_accumulator
            ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep)
          (process_congr_parAll_push_right _ _ _)
  | nodeClose =>
      rename_i M N parent c d before after childChildren subtrees childSubtrees
      have labels :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees) ::
                after)).Nodup := by
        cases typed with
        | inl ty =>
            cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node _ _ _ typedChildren _ =>
                exact typedChildren.labels_nodup
      have cAfter := childLabel_notin_after labels
      have pUnused : occurs (chanIndex c) (M.eval (.pure .one)) = 0 := by
        cases typed with
        | inl ty =>
            cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.close_unused (by simp [childLabels])
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees) := by
        cases typed with
        | inl ty =>
            cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees)
              (by simp)
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have cUnused := typedChild.parent_close_unused
      have memSel :
          (c, Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.close false (Term.chan d))) childChildren childSubtrees) ::
                after := by simp
      have hnodup := labelsInteriors_sublist_node.nodup distinct
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.close true (Term.chan c))) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure .one)) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have eParent := grandchild_ne_node_parent distinct memSel memGc
        have hzero : occurs (chanIndex e) (M.eval (.close true (Term.chan c))) = 0 := by
          cases typed with
          | inl typedNode => cases typedNode
          | inr typedAtNode =>
              obtain ⟨r, A, typedAtNode⟩ := typedAtNode
              cases typedAtNode with
              | node single has typedTerm typedChildren typedSubtrees =>
                  exact typedTerm.occurs0 (typedChildren.notLabel_false hfresh.2 eParent)
        refine ⟨hfresh.1, hzero, ?_⟩
        have hec : chanIndex e ≠ chanIndex c := by
          intro h
          apply hfresh.2
          have hce : e = c := by
            cases e with
            | var_Chan ex => cases c with
              | var_Chan cx => simp only [chanIndex] at h; rw [h]
          rw [hce]
          exact List.mem_map.mpr ⟨(c, _), memSel, rfl⟩
        rw [← close_term_occurs_eq M true c (chanIndex e) hec]
        exact hzero
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have detachedZero := typedChild.close_detached_occurs0
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedNode => cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact typedAtNode.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := end_bodyStep M N true c d childChildren childSubtrees before after
        pUnused cUnused (fun e gc mem => typedChild.child_typedAt_wf mem) mFresh qsZero
        detachedZero ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_node, flattenBody, parAll_csubst, flattenSubtrees_eq_map,
        List.map_append] using
        TLLC.Process.Step.congr ARS.Conv.refl
          (process_step_parAll_accumulator
            ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep)
          (process_congr_parAll_push_right _ _ _)
  | rootSendEx value =>
      rename_i M N v c d before after childChildren subtrees childSubtrees
      have labelsNodup :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
                after)).Nodup := by
        cases typed with
        | inl ty =>
            cases ty with
            | root _ _ typedChildren _ => exact typedChildren.labels_nodup
        | inr ty => obtain ⟨r, A, ty⟩ := ty; cases ty
      have cNotAfter := childLabel_notin_after labelsNodup
      have memSel :
          (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
                after := by simp
      have hnodup := labelsInteriors_sublist_root.nodup distinct
      have cLabel : c ∈ childLabels
          (before ++
            (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
              after) :=
        List.mem_map.mpr ⟨(c, _), memSel, rfl⟩
      have occAtLabel : ∀ e, e ∈ childLabels
          (before ++
            (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
              after) →
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 1 := by
        intro e he
        cases typed with
        | inl ty =>
            cases ty with
            | root single typedTerm typedChildren typedSubtrees =>
                exact typedTerm.occurs1 (typedChildren.pos_of_label he)
        | inr ty => obtain ⟨r, A, h⟩ := ty; cases h
      have occFresh : ∀ e, e ∉ childLabels
          (before ++
            (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
              after) →
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 := by
        intro e he
        cases typed with
        | inl ty =>
            cases ty with
            | root single typedTerm typedChildren typedSubtrees =>
                exact typedTerm.occurs0 (typedChildren.notLabel_false he)
        | inr ty => obtain ⟨r, A, h⟩ := ty; cases h
      have hcv : occurs (chanIndex c) v = 0 := by
        have h1 := occAtLabel c cLabel
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex c)
        cases c with
        | var_Chan cx =>
            simp [occurs, chanIndex] at h1 h2 ⊢
            omega
      have hdv : occurs (chanIndex d) v = 0 := by
        have h1 := occFresh d (child_node_label_fresh hnodup memSel)
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex d)
        cases c with
        | var_Chan cx =>
            cases d with
            | var_Chan dx =>
                simp [occurs, chanIndex] at h1 h2 ⊢
                omega
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) := by
        cases typed with
        | inl ty =>
            exact ty.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees)
              (by simp)
        | inr ty => obtain ⟨r, A, ty⟩ := ty; cases ty
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have tySibs : ∀ e sib, (e, sib) ∈ before ++ after →
          ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedRoot =>
            refine typedRoot.child_typedAt_wf (c := e) (child := sib) ?_
            rcases List.mem_append.mp mem with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
        | inr ty => obtain ⟨r, A, h⟩ := ty; cases h
      have nodupSibs : (childLabels (before ++ after)).Nodup := by
        refine List.Nodup.sublist ?_ labelsNodup
        exact ((List.sublist_cons_self _ after).append_left before).map _
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have hzero := occFresh e hfresh.2
        refine ⟨hfresh.1, hzero, ?_⟩
        have hec : chanIndex e ≠ chanIndex c := by
          intro h
          apply hfresh.2
          have hce : e = c := by
            cases e with
            | var_Chan ex => cases c with
              | var_Chan cx => simp only [chanIndex] at h; rw [h]
          rw [hce]
          exact cLabel
        rw [pure_chan_term_occurs_eq M c (chanIndex e) hec]
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex e)
        omega
      have sFresh : ∀ e sib, (e, sib) ∈ (splitChildrenByTerm v (before ++ after)).1 →
          chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0 := by
        intro e sib mem
        obtain ⟨memSib, hoccE'⟩ := splitChildrenByTerm_mem₁ mem
        have hoccE : occurs (chanIndex e) v ≠ 0 := hoccE'
        have hec : chanIndex e ≠ chanIndex c := by
          intro h; rw [h] at hoccE; exact hoccE hcv
        have hed : chanIndex e ≠ chanIndex d := by
          intro h; rw [h] at hoccE; exact hoccE hdv
        refine ⟨hec, hed, ?_⟩
        have eLabel : e ∈ childLabels
            (before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
                after) := by
          refine List.mem_map.mpr ⟨(e, sib), ?_, rfl⟩
          rcases List.mem_append.mp memSib with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
        have h1 := occAtLabel e eLabel
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex e)
        rw [pure_chan_term_occurs_eq M c (chanIndex e) hec]
        have h3 : occurs (chanIndex e) (Term.app (.send (Term.chan c) .ex) v .ex)
            = (if chanIndex c = chanIndex e then 1 else 0) + occurs (chanIndex e) v := by
          cases c with
          | var_Chan cx => simp [occurs, chanIndex]
        rw [if_neg (fun h => hec h.symm)] at h3
        omega
      have nodupNew : (childLabels ((splitChildrenByTerm v (before ++ after)).1 ++
          childChildren)).Nodup := by
        have h1 : (childLabels (splitChildrenByTerm v (before ++ after)).1).Nodup :=
          List.Nodup.sublist ((splitChildrenByTerm_sublist₁ v (before ++ after)).map _) nodupSibs
        have h2 : (childLabels childChildren).Nodup := by
          cases typedChild with
          | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
              exact typedChildrenChild.labels_nodup
        rw [show childLabels ((splitChildrenByTerm v (before ++ after)).1 ++ childChildren)
            = childLabels (splitChildrenByTerm v (before ++ after)).1 ++
                childLabels childChildren from by simp [childLabels]]
        refine List.Nodup.append h1 h2 ?_
        intro a ha1 ha2
        rcases List.mem_map.mp ha2 with ⟨⟨e2, gc2⟩, hmem2, rfl⟩
        have hfresh2 := grandchild_fresh hnodup memSel hmem2
        apply hfresh2.2
        rcases List.mem_map.mp ha1 with ⟨⟨e1, sib1⟩, hmem1, heq⟩
        have hmemSib : (e1, sib1) ∈ before ++ after := (splitChildrenByTerm_mem₁ hmem1).1
        refine List.mem_map.mpr ⟨(e1, sib1), ?_, heq⟩
        rcases List.mem_append.mp hmemSib with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
        | inr ty => obtain ⟨r, A, h⟩ := ty; cases h
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cNotAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := sendEx_bodyStep M N v c d childChildren childSubtrees before after
        value hcv hdv (fun e gc mem => typedChild.child_typedAt_wf mem) tySibs nodupSibs
        mFresh sFresh nodupNew qsZero
        ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_root, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | nodeSendEx value freshP =>
      rename_i M N parent v c d before after childChildren subtrees childSubtrees
      have labelsNodup :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
                after)).Nodup := by
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node _ _ _ typedChildren _ => exact typedChildren.labels_nodup
      have cNotAfter := childLabel_notin_after labelsNodup
      have memSel :
          (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
                after := by simp
      have hnodup := labelsInteriors_sublist_node.nodup distinct
      have cLabel : c ∈ childLabels
          (before ++
            (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
              after) :=
        List.mem_map.mpr ⟨(c, _), memSel, rfl⟩
      have occAtLabel : ∀ e, e ∈ childLabels
          (before ++
            (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
              after) →
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 1 := by
        intro e he
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedTerm.occurs1 (typedChildren.pos_of_label he)
      have occFresh : ∀ e, e ∉ childLabels
          (before ++
            (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
              after) →
          chanIndex e ≠ chanIndex parent →
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 := by
        intro e he heParent
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedTerm.occurs0 (typedChildren.notLabel_false he heParent)
      have hcv : occurs (chanIndex c) v = 0 := by
        have h1 := occAtLabel c cLabel
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex c)
        cases c with
        | var_Chan cx =>
            simp [occurs, chanIndex] at h1 h2 ⊢
            omega
      have hdv : occurs (chanIndex d) v = 0 := by
        have h1 := occFresh d (child_node_label_fresh hnodup memSel)
          (child_node_label_ne_parent distinct memSel)
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex d)
        cases c with
        | var_Chan cx =>
            cases d with
            | var_Chan dx =>
                simp [occurs, chanIndex] at h1 h2 ⊢
                omega
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) := by
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees)
              (by simp)
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have tySibs : ∀ e sib, (e, sib) ∈ before ++ after →
          ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            refine ty.child_typedAt_wf (c := e) (child := sib) ?_
            rcases List.mem_append.mp mem with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      have nodupSibs : (childLabels (before ++ after)).Nodup := by
        refine List.Nodup.sublist ?_ labelsNodup
        exact ((List.sublist_cons_self _ after).append_left before).map _
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have eParent := grandchild_ne_node_parent distinct memSel memGc
        have hzero := occFresh e hfresh.2 eParent
        refine ⟨hfresh.1, hzero, ?_⟩
        have hec : chanIndex e ≠ chanIndex c := by
          intro h
          apply hfresh.2
          have hce : e = c := by
            cases e with
            | var_Chan ex => cases c with
              | var_Chan cx => simp only [chanIndex] at h; rw [h]
          rw [hce]
          exact cLabel
        rw [pure_chan_term_occurs_eq M c (chanIndex e) hec]
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex e)
        omega
      have sFresh : ∀ e sib, (e, sib) ∈ (splitChildrenByTerm v (before ++ after)).1 →
          chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0 := by
        intro e sib mem
        obtain ⟨memSib, hoccE'⟩ := splitChildrenByTerm_mem₁ mem
        have hoccE : occurs (chanIndex e) v ≠ 0 := hoccE'
        have hec : chanIndex e ≠ chanIndex c := by
          intro h; rw [h] at hoccE; exact hoccE hcv
        have hed : chanIndex e ≠ chanIndex d := by
          intro h; rw [h] at hoccE; exact hoccE hdv
        refine ⟨hec, hed, ?_⟩
        have eLabel : e ∈ childLabels
            (before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
                after) := by
          refine List.mem_map.mpr ⟨(e, sib), ?_, rfl⟩
          rcases List.mem_append.mp memSib with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
        have h1 := occAtLabel e eLabel
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex e)
        rw [pure_chan_term_occurs_eq M c (chanIndex e) hec]
        have h3 : occurs (chanIndex e) (Term.app (.send (Term.chan c) .ex) v .ex)
            = (if chanIndex c = chanIndex e then 1 else 0) + occurs (chanIndex e) v := by
          cases c with
          | var_Chan cx => simp [occurs, chanIndex]
        rw [if_neg (fun h => hec h.symm)] at h3
        omega
      have nodupNew : (childLabels ((splitChildrenByTerm v (before ++ after)).1 ++
          childChildren)).Nodup := by
        have h1 : (childLabels (splitChildrenByTerm v (before ++ after)).1).Nodup :=
          List.Nodup.sublist ((splitChildrenByTerm_sublist₁ v (before ++ after)).map _) nodupSibs
        have h2 : (childLabels childChildren).Nodup := by
          cases typedChild with
          | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
              exact typedChildrenChild.labels_nodup
        rw [show childLabels ((splitChildrenByTerm v (before ++ after)).1 ++ childChildren)
            = childLabels (splitChildrenByTerm v (before ++ after)).1 ++
                childLabels childChildren from by simp [childLabels]]
        refine List.Nodup.append h1 h2 ?_
        intro a ha1 ha2
        rcases List.mem_map.mp ha2 with ⟨⟨e2, gc2⟩, hmem2, rfl⟩
        have hfresh2 := grandchild_fresh hnodup memSel hmem2
        apply hfresh2.2
        rcases List.mem_map.mp ha1 with ⟨⟨e1, sib1⟩, hmem1, heq⟩
        have hmemSib : (e1, sib1) ∈ before ++ after := (splitChildrenByTerm_mem₁ hmem1).1
        refine List.mem_map.mpr ⟨(e1, sib1), ?_, heq⟩
        rcases List.mem_append.mp hmemSib with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cNotAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := sendEx_bodyStep M N v c d childChildren childSubtrees before after
        value hcv hdv (fun e gc mem => typedChild.child_typedAt_wf mem) tySibs nodupSibs
        mFresh sFresh nodupNew qsZero
        ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_node, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | rootRecvEx value =>
      rename_i M N v c d before after childChildren subtrees childSubtrees
      have labelsNodup :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
                childChildren childSubtrees) :: after)).Nodup := by
        cases typed with
        | inl ty =>
            cases ty with
            | root _ _ typedChildren _ => exact typedChildren.labels_nodup
        | inr ty => obtain ⟨r, A, ty⟩ := ty; cases ty
      have cNotAfter := childLabel_notin_after labelsNodup
      have memSel :
          (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
            childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
                childChildren childSubtrees) :: after := by simp
      have hnodup := labelsInteriors_sublist_root.nodup distinct
      have cLabel : c ∈ childLabels
          (before ++
            (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
              childChildren childSubtrees) :: after) :=
        List.mem_map.mpr ⟨(c, _), memSel, rfl⟩
      have occFresh : ∀ e, e ∉ childLabels
          (before ++
            (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
              childChildren childSubtrees) :: after) →
          occurs (chanIndex e) (M.eval (.recv (Term.chan c) .ex)) = 0 := by
        intro e he
        cases typed with
        | inl ty =>
            cases ty with
            | root single typedTerm typedChildren typedSubtrees =>
                exact typedTerm.occurs0 (typedChildren.notLabel_false he)
        | inr ty => obtain ⟨r, A, h⟩ := ty; cases h
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
                childChildren childSubtrees) := by
        cases typed with
        | inl ty =>
            exact ty.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
                childChildren childSubtrees)
              (by simp)
        | inr ty => obtain ⟨r, A, ty⟩ := ty; cases ty
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have hdNotLabel := child_node_label_fresh hnodup memSel
      have hcd : chanIndex c ≠ chanIndex d := by
        cases c with
        | var_Chan cx =>
            cases d with
            | var_Chan dx =>
                intro h
                simp only [chanIndex] at h
                subst h
                exact hdNotLabel cLabel
      have kidNotC : ∀ e gc, (e, gc) ∈ childChildren → chanIndex e ≠ chanIndex c := by
        intro e gc memGc h
        have hfresh := grandchild_fresh hnodup memSel memGc
        apply hfresh.2
        have hce : e = c := by
          cases e with
          | var_Chan ex => cases c with
            | var_Chan cx => simp only [chanIndex] at h; rw [h]
        rw [hce]
        exact cLabel
      have hcChild : occurs (chanIndex c)
          (N.eval (.app (.send (Term.chan d) .ex) v .ex)) = 0 := by
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            refine typedTermChild.occurs0 (typedChildrenChild.notLabel_false ?_ ?_)
            · intro hmem
              rcases List.mem_map.mp hmem with ⟨⟨e2, gc2⟩, hmem2, heq⟩
              exact kidNotC e2 gc2 hmem2 (by rw [show e2 = c from heq])
            · exact hcd
      have hcv : occurs (chanIndex c) v = 0 := by
        have h2 := evalctx_occurs_plug N (.app (.send (Term.chan d) .ex) v .ex) (chanIndex c)
        cases c with
        | var_Chan cx =>
            cases d with
            | var_Chan dx =>
                simp [occurs, chanIndex] at hcChild h2 ⊢
                omega
      have hdv : occurs (chanIndex d) v = 0 := by
        have h1 : occurs (chanIndex d)
            (N.eval (.app (.send (Term.chan d) .ex) v .ex)) = 1 := by
          cases d with
          | var_Chan dx =>
              cases typedChild with
              | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
                  exact typedTermChild.occurs1 has.pos_true
        have h2 := evalctx_occurs_plug N (.app (.send (Term.chan d) .ex) v .ex) (chanIndex d)
        cases d with
        | var_Chan dx =>
            simp [occurs, chanIndex] at h1 h2 ⊢
            omega
      have kidFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.recv (Term.chan c) .ex)) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        exact ⟨kidNotC e gc memGc, hfresh.1, occFresh e hfresh.2⟩
      have s2Fresh : ∀ e gc, (e, gc) ∈ (splitChildrenByTerm v childChildren).2 →
          occurs (chanIndex e) (M.eval (.pure (.pair v (Term.chan c) .ex .L))) = 0 := by
        intro e gc mem
        obtain ⟨memKid, hoccE'⟩ := splitChildrenByTerm_mem₂ mem
        have hoccE : occurs (chanIndex e) v = 0 := hoccE'
        have hk := kidFresh e gc memKid
        have h1 := hk.2.2
        have h2 := evalctx_occurs_plug M (.recv (Term.chan c) .ex) (chanIndex e)
        have h3 := evalctx_occurs_plug M (.pure (.pair v (Term.chan c) .ex .L)) (chanIndex e)
        have hec := hk.1
        cases c with
        | var_Chan cx =>
            cases e with
            | var_Chan ex =>
                simp only [chanIndex] at hec
                simp [occurs, chanIndex, Ne.symm hec] at h1 h2 h3 hoccE ⊢
                omega
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have nodupKids : (childLabels childChildren).Nodup := by
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedChildrenChild.labels_nodup
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
        | inr ty => obtain ⟨r, A, h⟩ := ty; cases h
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cNotAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := recvEx_bodyStep M N v c d childChildren childSubtrees before after
        value hcv hdv (fun e gc mem => typedChild.child_typedAt_wf mem) nodupKids
        kidFresh s2Fresh qsZero
        ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_root, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | nodeRecvEx value =>
      rename_i M N parent v c d before after childChildren subtrees childSubtrees
      have labelsNodup :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
                childChildren childSubtrees) :: after)).Nodup := by
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node _ _ _ typedChildren _ => exact typedChildren.labels_nodup
      have cNotAfter := childLabel_notin_after labelsNodup
      have memSel :
          (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
            childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
                childChildren childSubtrees) :: after := by simp
      have hnodup := labelsInteriors_sublist_node.nodup distinct
      have cLabel : c ∈ childLabels
          (before ++
            (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
              childChildren childSubtrees) :: after) :=
        List.mem_map.mpr ⟨(c, _), memSel, rfl⟩
      have occFresh : ∀ e, e ∉ childLabels
          (before ++
            (c, Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
              childChildren childSubtrees) :: after) →
          chanIndex e ≠ chanIndex parent →
          occurs (chanIndex e) (M.eval (.recv (Term.chan c) .ex)) = 0 := by
        intro e he heParent
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedTerm.occurs0 (typedChildren.notLabel_false he heParent)
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
                childChildren childSubtrees) := by
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.app (.send (Term.chan d) .ex) v .ex))
                childChildren childSubtrees)
              (by simp)
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have hdNotLabel := child_node_label_fresh hnodup memSel
      have kidNotC : ∀ e gc, (e, gc) ∈ childChildren → chanIndex e ≠ chanIndex c := by
        intro e gc memGc h
        have hfresh := grandchild_fresh hnodup memSel memGc
        apply hfresh.2
        have hce : e = c := by
          cases e with
          | var_Chan ex => cases c with
            | var_Chan cx => simp only [chanIndex] at h; rw [h]
        rw [hce]
        exact cLabel
      have hcd : chanIndex c ≠ chanIndex d := by
        cases c with
        | var_Chan cx =>
            cases d with
            | var_Chan dx =>
                intro h
                simp only [chanIndex] at h
                subst h
                exact hdNotLabel cLabel
      have hcChild : occurs (chanIndex c)
          (N.eval (.app (.send (Term.chan d) .ex) v .ex)) = 0 := by
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            refine typedTermChild.occurs0 (typedChildrenChild.notLabel_false ?_ ?_)
            · intro hmem
              rcases List.mem_map.mp hmem with ⟨⟨e2, gc2⟩, hmem2, heq⟩
              exact kidNotC e2 gc2 hmem2 (by rw [show e2 = c from heq])
            · exact hcd
      have hcv : occurs (chanIndex c) v = 0 := by
        have h2 := evalctx_occurs_plug N (.app (.send (Term.chan d) .ex) v .ex) (chanIndex c)
        cases c with
        | var_Chan cx =>
            cases d with
            | var_Chan dx =>
                simp [occurs, chanIndex] at hcChild h2 ⊢
                omega
      have hdv : occurs (chanIndex d) v = 0 := by
        have h1 : occurs (chanIndex d)
            (N.eval (.app (.send (Term.chan d) .ex) v .ex)) = 1 := by
          cases d with
          | var_Chan dx =>
              cases typedChild with
              | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
                  exact typedTermChild.occurs1 has.pos_true
        have h2 := evalctx_occurs_plug N (.app (.send (Term.chan d) .ex) v .ex) (chanIndex d)
        cases d with
        | var_Chan dx =>
            simp [occurs, chanIndex] at h1 h2 ⊢
            omega
      have kidFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.recv (Term.chan c) .ex)) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have eParent := grandchild_ne_node_parent distinct memSel memGc
        exact ⟨kidNotC e gc memGc, hfresh.1, occFresh e hfresh.2 eParent⟩
      have s2Fresh : ∀ e gc, (e, gc) ∈ (splitChildrenByTerm v childChildren).2 →
          occurs (chanIndex e) (M.eval (.pure (.pair v (Term.chan c) .ex .L))) = 0 := by
        intro e gc mem
        obtain ⟨memKid, hoccE'⟩ := splitChildrenByTerm_mem₂ mem
        have hoccE : occurs (chanIndex e) v = 0 := hoccE'
        have hk := kidFresh e gc memKid
        have h1 := hk.2.2
        have h2 := evalctx_occurs_plug M (.recv (Term.chan c) .ex) (chanIndex e)
        have h3 := evalctx_occurs_plug M (.pure (.pair v (Term.chan c) .ex .L)) (chanIndex e)
        have hec := hk.1
        cases c with
        | var_Chan cx =>
            cases e with
            | var_Chan ex =>
                simp only [chanIndex] at hec
                simp [occurs, chanIndex, Ne.symm hec] at h1 h2 h3 hoccE ⊢
                omega
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have nodupKids : (childLabels childChildren).Nodup := by
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedChildrenChild.labels_nodup
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cNotAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := recvEx_bodyStep M N v c d childChildren childSubtrees before after
        value hcv hdv (fun e gc mem => typedChild.child_typedAt_wf mem) nodupKids
        kidFresh s2Fresh qsZero
        ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_node, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | rootSendIm implicitPayload =>
      rename_i M N payload c d before after childChildren subtrees childSubtrees
      have labelsNodup :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees) ::
                after)).Nodup := by
        cases typed with
        | inl typedRoot =>
            cases typedRoot with
            | root single typedTerm typedChildren typedSubtrees =>
                exact typedChildren.labels_nodup
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot
      have cNotBefore := childLabel_notin_before labelsNodup
      have cNotAfter := childLabel_notin_after labelsNodup
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees) := by
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees)
              (by simp)
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have memSel :
          (c, Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees) ::
                after := by simp
      have hnodup := labelsInteriors_sublist_root.nodup distinct
      -- Per grandchild edge, distinctness gives `e ≠ d` and `e` not a root child label; the root
      -- term typing then forces `occurs (chanIndex e) M = 0`.
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .im) payload .im)) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have hzero : occurs (chanIndex e)
            (M.eval (.app (.send (Term.chan c) .im) payload .im)) = 0 := by
          cases typed with
          | inl typedRoot =>
              cases typedRoot with
              | root single typedTerm typedChildren typedSubtrees =>
                  exact typedTerm.occurs0 (typedChildren.notLabel_false hfresh.2)
          | inr typedAtRoot => obtain ⟨r, A, h⟩ := typedAtRoot; cases h
        exact ⟨hfresh.1, hzero, by rw [← sendIm_term_occurs_eq M c payload]; exact hzero⟩
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
        | inr typedAtRoot => obtain ⟨r, A, h⟩ := typedAtRoot; cases h
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cNotAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := sendIm_bodyStep M N payload c d childChildren childSubtrees before after
        implicitPayload (fun e gc mem => typedChild.child_typedAt_wf mem) mFresh qsZero
        ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_root, flattenBody, parAll_csubst, sendImChildren] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | nodeSendIm implicitPayload =>
      rename_i M N parent payload c d before after childChildren subtrees childSubtrees
      have labelsNodup :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees) ::
                after)).Nodup := by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            cases typedAtNode with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedChildren.labels_nodup
      have cNotBefore := childLabel_notin_before labelsNodup
      have cNotAfter := childLabel_notin_after labelsNodup
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees) := by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact typedAtNode.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees)
              (by simp)
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have memSel :
          (c, Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .im)) childChildren childSubtrees) ::
                after := by simp
      have hnodup := labelsInteriors_sublist_node.nodup distinct
      -- Node version: grandchild labels must additionally avoid the node's own parent endpoint
      -- (the reserved slot of `ChildrenTypedAt`), supplied by `grandchild_ne_node_parent`.
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .im) payload .im)) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure (Term.chan c))) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have eParent := grandchild_ne_node_parent distinct memSel memGc
        have hzero : occurs (chanIndex e)
            (M.eval (.app (.send (Term.chan c) .im) payload .im)) = 0 := by
          cases typed with
          | inl typedNode => cases typedNode
          | inr typedAtNode =>
              obtain ⟨r, A, typedAtNode⟩ := typedAtNode
              cases typedAtNode with
              | node single has typedTerm typedChildren typedSubtrees =>
                  exact typedTerm.occurs0 (typedChildren.notLabel_false hfresh.2 eParent)
        exact ⟨hfresh.1, hzero, by rw [← sendIm_term_occurs_eq M c payload]; exact hzero⟩
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedNode => cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact typedAtNode.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cNotAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := sendIm_bodyStep M N payload c d childChildren childSubtrees before after
        implicitPayload (fun e gc mem => typedChild.child_typedAt_wf mem) mFresh qsZero
        ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_node, flattenBody, parAll_csubst, sendImChildren] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | rootRecvIm implicitPayload =>
      rename_i M N payload c d before after childChildren subtrees childSubtrees
      have labelsNodup :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
                childChildren childSubtrees) :: after)).Nodup := by
        cases typed with
        | inl typedRoot =>
            cases typedRoot with
            | root single typedTerm typedChildren typedSubtrees =>
                exact typedChildren.labels_nodup
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot
      have cNotBefore := childLabel_notin_before labelsNodup
      have cNotAfter := childLabel_notin_after labelsNodup
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
                childChildren childSubtrees) := by
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
                childChildren childSubtrees)
              (by simp)
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have memSel :
          (c, Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
            childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
                childChildren childSubtrees) :: after := by simp
      have hnodup := labelsInteriors_sublist_root.nodup distinct
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.recv (Term.chan c) .im)) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure (.pair payload (Term.chan c) .im .L))) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have hzero : occurs (chanIndex e) (M.eval (.recv (Term.chan c) .im)) = 0 := by
          cases typed with
          | inl typedRoot =>
              cases typedRoot with
              | root single typedTerm typedChildren typedSubtrees =>
                  exact typedTerm.occurs0 (typedChildren.notLabel_false hfresh.2)
          | inr typedAtRoot => obtain ⟨r, A, h⟩ := typedAtRoot; cases h
        exact ⟨hfresh.1, hzero, by rw [← recvIm_term_occurs_eq M c payload]; exact hzero⟩
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
        | inr typedAtRoot => obtain ⟨r, A, h⟩ := typedAtRoot; cases h
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cNotAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := recvIm_bodyStep M N payload c d childChildren childSubtrees before after
        implicitPayload (fun e gc mem => typedChild.child_typedAt_wf mem) mFresh qsZero
        ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_root, flattenBody, parAll_csubst, recvImChildren] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | nodeRecvIm implicitPayload =>
      rename_i M N parent payload c d before after childChildren subtrees childSubtrees
      have labelsNodup :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
                childChildren childSubtrees) :: after)).Nodup := by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            cases typedAtNode with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedChildren.labels_nodup
      have cNotBefore := childLabel_notin_before labelsNodup
      have cNotAfter := childLabel_notin_after labelsNodup
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
                childChildren childSubtrees) := by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact typedAtNode.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
                childChildren childSubtrees)
              (by simp)
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have memSel :
          (c, Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
            childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.app (.send (Term.chan d) .im) payload .im))
                childChildren childSubtrees) :: after := by simp
      have hnodup := labelsInteriors_sublist_node.nodup distinct
      have mFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.recv (Term.chan c) .im)) = 0 ∧
          occurs (chanIndex e) (M.eval (.pure (.pair payload (Term.chan c) .im .L))) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have eParent := grandchild_ne_node_parent distinct memSel memGc
        have hzero : occurs (chanIndex e) (M.eval (.recv (Term.chan c) .im)) = 0 := by
          cases typed with
          | inl typedNode => cases typedNode
          | inr typedAtNode =>
              obtain ⟨r, A, typedAtNode⟩ := typedAtNode
              cases typedAtNode with
              | node single has typedTerm typedChildren typedSubtrees =>
                  exact typedTerm.occurs0 (typedChildren.notLabel_false hfresh.2 eParent)
        exact ⟨hfresh.1, hzero, by rw [← recvIm_term_occurs_eq M c payload]; exact hzero⟩
      have qsZero : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl typedNode => cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact typedAtNode.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cNotAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := recvIm_bodyStep M N payload c d childChildren childSubtrees before after
        implicitPayload (fun e gc mem => typedChild.child_typedAt_wf mem) mFresh qsZero
        ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_node, flattenBody, parAll_csubst, recvImChildren] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun p => p[σ; Term.var_Term])) bodyStep
  | nodeForward value occursP =>
      rename_i M N parent v c d before after childChildren subtrees childSubtrees
      have labelsNodup :
          (childLabels
            (before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
                after)).Nodup := by
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node _ _ _ typedChildren _ => exact typedChildren.labels_nodup
      have cNotBefore := childLabel_notin_before labelsNodup
      have cNotAfter := childLabel_notin_after labelsNodup
      have memSel :
          (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ∈
            before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
                after := by simp
      have hnodup := labelsInteriors_sublist_node.nodup distinct
      have cLabel : c ∈ childLabels
          (before ++
            (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
              after) :=
        List.mem_map.mpr ⟨(c, _), memSel, rfl⟩
      have occAtLabel : ∀ e, e ∈ childLabels
          (before ++
            (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
              after) →
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 1 := by
        intro e he
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedTerm.occurs1 (typedChildren.pos_of_label he)
      have occFresh : ∀ e, e ∉ childLabels
          (before ++
            (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
              after) →
          chanIndex e ≠ chanIndex parent →
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 := by
        intro e he heParent
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedTerm.occurs0 (typedChildren.notLabel_false he heParent)
      have hcv : occurs (chanIndex c) v = 0 := by
        have h1 := occAtLabel c cLabel
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex c)
        cases c with
        | var_Chan cx =>
            simp [occurs, chanIndex] at h1 h2 ⊢
            omega
      have hdv : occurs (chanIndex d) v = 0 := by
        have h1 := occFresh d (child_node_label_fresh hnodup memSel)
          (child_node_label_ne_parent distinct memSel)
        have h2 := evalctx_occurs_plug M (.app (.send (Term.chan c) .ex) v .ex) (chanIndex d)
        cases c with
        | var_Chan cx =>
            cases d with
            | var_Chan dx =>
                simp [occurs, chanIndex] at h1 h2 ⊢
                omega
      have tyChild :
          ∃ r A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
              (Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) := by
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.child_typedAt_wf (c := c)
              (child := Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees)
              (by simp)
      obtain ⟨rChild, AChild, tyAChild, typedChild⟩ := tyChild
      have hdNotLabel := child_node_label_fresh hnodup memSel
      have tySibs : ∀ e sib, (e, sib) ∈ before ++ after →
          ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
            TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            refine ty.child_typedAt_wf (c := e) (child := sib) ?_
            rcases List.mem_append.mp mem with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      have nodupSibs : (childLabels (before ++ after)).Nodup := by
        refine List.Nodup.sublist ?_ labelsNodup
        exact ((List.sublist_cons_self _ after).append_left before).map _
      have nodupKids : (childLabels childChildren).Nodup := by
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedChildrenChild.labels_nodup
      have sibLabelFull : ∀ e sib, (e, sib) ∈ before ++ after →
          e ∈ childLabels
            (before ++
              (c, Tree.node d (N.eval (.recv (Term.chan d) .ex)) childChildren childSubtrees) ::
                after) := by
        intro e sib mem
        refine List.mem_map.mpr ⟨(e, sib), ?_, rfl⟩
        rcases List.mem_append.mp mem with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      have disjKidsSibs : ∀ a, a ∈ childLabels (before ++ after) →
          a ∉ childLabels childChildren := by
        intro a ha hmem
        rcases List.mem_map.mp hmem with ⟨⟨e2, gc2⟩, hmem2, heq⟩
        have hfresh2 := grandchild_fresh hnodup memSel hmem2
        apply hfresh2.2
        rw [show e2 = a from heq]
        rcases List.mem_map.mp ha with ⟨⟨e1, sib1⟩, hmem1, heq1⟩
        rw [← heq1]
        exact sibLabelFull e1 sib1 hmem1
      have kidFresh : ∀ e gc, (e, gc) ∈ childChildren →
          chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (M.eval (.app (.send (Term.chan c) .ex) v .ex)) = 0 := by
        intro e gc memGc
        have hfresh := grandchild_fresh hnodup memSel memGc
        have eParent := grandchild_ne_node_parent distinct memSel memGc
        refine ⟨?_, hfresh.1, occFresh e hfresh.2 eParent⟩
        intro h
        apply hfresh.2
        have hce : e = c := by
          cases e with
          | var_Chan ex => cases c with
            | var_Chan cx => simp only [chanIndex] at h; rw [h]
        rw [hce]
        exact cLabel
      have cNotSibs : c ∉ childLabels (before ++ after) := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨⟨e1, sib1⟩, hmem1, heq1⟩
        rcases List.mem_append.mp hmem1 with h | h
        · exact cNotBefore (heq1 ▸ List.mem_map.mpr ⟨(e1, sib1), h, rfl⟩)
        · exact cNotAfter (heq1 ▸ List.mem_map.mpr ⟨(e1, sib1), h, rfl⟩)
      have sibW2 : ∀ e sib, (e, sib) ∈ (splitChildrenByTerm v (before ++ after)).2 →
          chanIndex e ≠ chanIndex c ∧ chanIndex e ≠ chanIndex d ∧
          occurs (chanIndex e) (N.eval (.recv (Term.chan d) .ex)) = 0 ∧
          occurs (chanIndex e) (N.eval (.pure (.pair v (Term.chan d) .ex .L))) = 0 := by
        intro e sib mem
        obtain ⟨memSib, hoccE'⟩ := splitChildrenByTerm_mem₂ mem
        have hoccE : occurs (chanIndex e) v = 0 := hoccE'
        have eSib : e ∈ childLabels (before ++ after) :=
          List.mem_map.mpr ⟨(e, sib), memSib, rfl⟩
        have hec : chanIndex e ≠ chanIndex c := by
          intro h
          apply cNotSibs
          have hce : c = e := by
            cases c with
            | var_Chan cx => cases e with
              | var_Chan ex => simp only [chanIndex] at h; rw [h]
          rw [hce]
          exact eSib
        have hed : chanIndex e ≠ chanIndex d := by
          cases d with
          | var_Chan dx =>
              cases e with
              | var_Chan ex =>
                  intro h
                  simp only [chanIndex] at h
                  subst h
                  exact hdNotLabel (sibLabelFull _ sib memSib)
        have hrecv : occurs (chanIndex e) (N.eval (.recv (Term.chan d) .ex)) = 0 := by
          cases typedChild with
          | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
              refine typedTermChild.occurs0 (typedChildrenChild.notLabel_false ?_ ?_)
              · intro hmem
                exact disjKidsSibs e eSib hmem
              · exact hed
        refine ⟨hec, hed, hrecv, ?_⟩
        have h2 := evalctx_occurs_plug N (.recv (Term.chan d) .ex) (chanIndex e)
        have h3 := evalctx_occurs_plug N (.pure (.pair v (Term.chan d) .ex .L)) (chanIndex e)
        cases d with
        | var_Chan dx =>
            cases e with
            | var_Chan ex =>
                simp only [chanIndex] at hed
                simp [occurs, chanIndex, Ne.symm hed] at hrecv h2 h3 hoccE ⊢
                omega
      have qsZero : ∀ q, q ∈ flattenSubtrees subtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            cases ty with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedSubtrees.flattenSubtrees_occurs0 hq
      have qsZero' : ∀ q, q ∈ flattenSubtrees childSubtrees →
          ∀ i, TLLC.Process.procOccurs i q = 0 := by
        intro q hq i
        cases typedChild with
        | node single has typedTermChild typedChildrenChild typedSubtreesChild =>
            exact typedSubtreesChild.flattenSubtrees_occurs0 hq
      have tyR : ∀ e sib, (e, sib) ∈ after → ∃ rr A, ([] : Static.Ctx) ⊢ A : .proto ∧
          TypedAt rr (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) sib := by
        intro e sib mem
        cases typed with
        | inl ty => cases ty
        | inr ty =>
            obtain ⟨r, A, ty⟩ := ty
            exact ty.child_typedAt_wf
              (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
      have distinctR : ∀ e sib, (e, sib) ∈ after → chanIndex c ≠ chanIndex e := by
        intro e sib mem hidx
        apply cNotAfter
        have hce : c = e := by
          cases c with
          | var_Chan cx => cases e with
            | var_Chan ex => simp only [chanIndex] at hidx; rw [hidx]
        rw [hce]
        exact List.mem_map.mpr ⟨(e, sib), mem, rfl⟩
      intro σ
      have bodyStep := forward_bodyStep M N v c d childChildren subtrees childSubtrees
        before after value hcv hdv
        (fun e gc mem => typedChild.child_typedAt_wf mem) tySibs nodupSibs nodupKids
        disjKidsSibs kidFresh sibW2 qsZero qsZero'
        ⟨rChild, AChild, tyAChild, typedChild⟩ tyR distinctR σ
      simpa [Tree.flatten_node, flattenBody] using bodyStep
  | rootChild stepChild ih =>
      rename_i m c child child' before after subtrees
      obtain ⟨rChild, AChild, typedChild⟩ := by
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt (c := c) (child := child) (by simp)
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot
      have childStep := ih (Or.inr ⟨rChild, AChild, typedChild⟩) (distinct.child_root (c := c) (by simp))
      cases typedChild with
      | node single has typedTerm typedChildren typedSubtrees =>
          rename_i Θ x mChild childrenChild subtreesChild
          intro σ
          have childAt :
              (Tree.node (.var_Chan x) mChild childrenChild subtreesChild).flattenAt =
                (.var_Chan x, (Tree.node (.var_Chan x) mChild childrenChild subtreesChild).flatten) := by
            simp
          have childAt' : child'.flattenAt = (.var_Chan x, child'.flatten) :=
            Step.node_flattenAt_eq stepChild
          have bodyStep :
              TLLC.Process.Step
                ((flattenChildren (.tm m)
                  (before ++ (c, Tree.node (.var_Chan x) mChild childrenChild subtreesChild) :: after))[σ;
                    Term.var_Term])
                ((flattenChildren (.tm m) (before ++ (c, child') :: after))[σ; Term.var_Term]) :=
            process_step_flattenChildren_child_csubst
              (body := .tm m) (c := c) (d := .var_Chan x)
              before after childAt childAt' childStep σ
          simpa [Tree.flatten_root, flattenBody, parAll_csubst] using
            process_step_parAll_accumulator
              ((flattenSubtrees subtrees).map (fun process => process[σ; Term.var_Term])) bodyStep
  | nodeChild stepChild ih =>
      rename_i parent m c child child' before after subtrees
      obtain ⟨rChild, AChild, typedChild⟩ := by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact typedAtNode.child_typedAt (c := c) (child := child) (by simp)
      have childStep := ih (Or.inr ⟨rChild, AChild, typedChild⟩) (distinct.child_node (c := c) (by simp))
      cases typedChild with
      | node single has typedTerm typedChildren typedSubtrees =>
          rename_i Θ x mChild childrenChild subtreesChild
          intro σ
          have childAt :
              (Tree.node (.var_Chan x) mChild childrenChild subtreesChild).flattenAt =
                (.var_Chan x, (Tree.node (.var_Chan x) mChild childrenChild subtreesChild).flatten) := by
            simp
          have childAt' : child'.flattenAt = (.var_Chan x, child'.flatten) :=
            Step.node_flattenAt_eq stepChild
          have bodyStep :
              TLLC.Process.Step
                ((flattenChildren (.tm m)
                  (before ++ (c, Tree.node (.var_Chan x) mChild childrenChild subtreesChild) :: after))[σ;
                    Term.var_Term])
                ((flattenChildren (.tm m) (before ++ (c, child') :: after))[σ; Term.var_Term]) :=
            process_step_flattenChildren_child_csubst
              (body := .tm m) (c := c) (d := .var_Chan x)
              before after childAt childAt' childStep σ
          simpa [Tree.flatten_node, flattenBody, parAll_csubst] using
            process_step_parAll_accumulator
              ((flattenSubtrees subtrees).map (fun process => process[σ; Term.var_Term])) bodyStep
  | rootSubtree stepSubtree ih =>
      rename_i m children subtree subtree' before after
      have subtreeStep := ih (by
        cases typed with
        | inl typedRoot =>
            exact Or.inl (typedRoot.subtree_typed (by simp))
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot) (distinct.subtree_root (by simp))
      intro σ
      simpa [Tree.flatten_root, flattenBody] using
        process_step_flattenSubtrees_list_csubst (body := flattenChildren (.tm m) children)
          before after subtreeStep σ
  | nodeSubtree stepSubtree ih =>
      rename_i parent m children subtree subtree' before after
      have subtreeStep := ih (by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact Or.inl (typedAtNode.subtree_typed (by simp))) (distinct.subtree_node (by simp))
      intro σ
      simpa [Tree.flatten_node, flattenBody] using
        process_step_flattenSubtrees_list_csubst (body := flattenChildren (.tm m) children)
          before after subtreeStep σ
  | rootExpr termStep =>
      rename_i m m' children subtrees
      intro σ
      have bodyStep :
          TLLC.Process.Step ((flattenChildren (.tm m) children)[σ; Term.var_Term])
            ((flattenChildren (.tm m') children)[σ; Term.var_Term]) :=
        process_step_flattenChildren_body_csubst children (fun σ => by
          simpa using TLLC.Process.Step.exp (dynamic_step_csubst termStep σ)) σ
      simpa [Tree.flatten_root, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun process => process[σ; Term.var_Term])) bodyStep
  | nodeExpr termStep =>
      rename_i parent m m' children subtrees
      intro σ
      have bodyStep :
          TLLC.Process.Step ((flattenChildren (.tm m) children)[σ; Term.var_Term])
            ((flattenChildren (.tm m') children)[σ; Term.var_Term]) :=
        process_step_flattenChildren_body_csubst children (fun σ => by
          simpa using TLLC.Process.Step.exp (dynamic_step_csubst termStep σ)) σ
      simpa [Tree.flatten_node, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun process => process[σ; Term.var_Term])) bodyStep

/-- Lemma 5.86 for productive spawning-tree steps. -/
theorem simulation {p q : Tree}
    (typed : Typed p ∨ ∃ r A, TypedAt r A p)
    (distinct : Distinct p)
    (step : Step p q) :
    TLLC.Process.Step p.flatten q.flatten := by
  convert simulation_csubst typed distinct step Chan.var_Chan using 1 <;> asimp

end TLLC.Spawning
