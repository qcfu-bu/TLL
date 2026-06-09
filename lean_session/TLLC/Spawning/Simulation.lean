import TLLC.Process.Occurs
import TLLC.Process.Step
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

/-- Lemma 5.86 for productive spawning-tree steps, strengthened under channel substitution. -/
theorem simulation_csubst {p q : Tree}
    (typed : Typed p ∨ ∃ r A, TypedAt r A p)
    (step : Step p q) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step (p.flatten[σ; Term.var_Term]) (q.flatten[σ; Term.var_Term]) := by
  induction step with
  | rootFork freshC freshD =>
      rename_i M A m c d children subtrees
      have cFreshChildren : c ∉ childLabels children := by
        cases typed with
        | inl typedRoot =>
            cases typedRoot with
            | root single typedTerm typedChildren typedSubtrees =>
                exact typedChildren.not_label_of_fresh typedTerm freshC
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot
      have dFreshChildren : d ∉ childLabels children := by
        cases typed with
        | inl typedRoot =>
            cases typedRoot with
            | root single typedTerm typedChildren typedSubtrees =>
                exact typedChildren.not_label_of_fresh typedTerm freshD
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot
      sorry
  | nodeFork freshC freshD =>
      rename_i parent M A m c d children subtrees
      have cFreshChildren : c ∉ childLabels children := by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            cases typedAtNode with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedChildren.not_label_of_fresh typedTerm freshC
      have dFreshChildren : d ∉ childLabels children := by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            cases typedAtNode with
            | node single has typedTerm typedChildren typedSubtrees =>
                exact typedChildren.not_label_of_fresh typedTerm freshD
      sorry
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
      have cBefore := childLabel_notin_before labels
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
      have cFree := typedChild.flattenAt_occurs_succ tyAChild
      sorry
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
      have cBefore := childLabel_notin_before labels
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
      have cFree := typedChild.flattenAt_occurs_succ tyAChild
      sorry
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
      have cBefore := childLabel_notin_before labels
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
      have cFree := typedChild.flattenAt_occurs_succ tyAChild
      sorry
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
      have cBefore := childLabel_notin_before labels
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
      have cFree := typedChild.flattenAt_occurs_succ tyAChild
      sorry
  | rootSendEx => sorry
  | nodeSendEx => sorry
  | rootRecvEx => sorry
  | nodeRecvEx => sorry
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
      have childPosFree := typedChild.flattenAt_occurs_succ tyAChild
      sorry
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
      have childPosFree := typedChild.flattenAt_occurs_succ tyAChild
      sorry
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
      have childPosFree := typedChild.flattenAt_occurs_succ tyAChild
      sorry
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
      have childPosFree := typedChild.flattenAt_occurs_succ tyAChild
      sorry
  | nodeForward => sorry
  | rootChild stepChild ih =>
      rename_i m c child child' before after subtrees
      obtain ⟨rChild, AChild, typedChild⟩ := by
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt (c := c) (child := child) (by simp)
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot
      have childStep := ih (Or.inr ⟨rChild, AChild, typedChild⟩)
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
      have childStep := ih (Or.inr ⟨rChild, AChild, typedChild⟩)
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
            cases typedAtRoot)
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
            exact Or.inl (typedAtNode.subtree_typed (by simp)))
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
    (step : Step p q) :
    TLLC.Process.Step p.flatten q.flatten := by
  convert simulation_csubst typed step Chan.var_Chan using 1 <;> asimp

end TLLC.Spawning
