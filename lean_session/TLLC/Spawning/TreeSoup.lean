import TLLC.Process.SoupFlat
import TLLC.Process.SoupStep
import TLLC.Spawning.Flatten
import TLLC.Spawning.Step
import TLLC.Spawning.Distinct
import TLLC.Spawning.Simulation

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
open TLLC.Process (Config SoupEquiv SoupG prenex cswap liftBinders parConfig nuConfig
  tren_ext tren_comp tren_id tsmap_ext tsmap_comp tsmap_id tren_pure_one)
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

/-- The number of live threads contributed by each constructor, used to locate bodies. -/
@[simp] lemma treeBodies_root (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeBodies (.root m ms ns) = m :: (childBodies ms ++ subBodies ns) := by
  rw [treeBodies]

@[simp] lemma treeBodies_node (d : Chan) (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeBodies (.node d m ms ns) = m :: (childBodies ms ++ subBodies ns) := by
  rw [treeBodies]

@[simp] lemma childBodies_nil : childBodies [] = [] := by rw [childBodies]

@[simp] lemma childBodies_cons (c : Chan) (child : Tree) (ms : List (Chan × Tree)) :
    childBodies ((c, child) :: ms) = treeBodies child ++ childBodies ms := by
  rw [childBodies]

@[simp] lemma subBodies_nil : subBodies [] = [] := by rw [subBodies]

@[simp] lemma subBodies_cons (t : Tree) (ns : List Tree) :
    subBodies (t :: ns) = treeBodies t ++ subBodies ns := by
  rw [subBodies]

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

@[simp] lemma treeEdges_root (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeEdges (.root m ms ns) = childEdges ms ++ subEdges ns := by
  rw [treeEdges]

@[simp] lemma treeEdges_node (d : Chan) (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeEdges (.node d m ms ns) = childEdges ms ++ subEdges ns := by
  rw [treeEdges]

@[simp] lemma childEdges_nil : childEdges [] = [] := by rw [childEdges]

@[simp] lemma childEdges_cons (c : Chan) (child : Tree) (ms : List (Chan × Tree)) :
    childEdges ((c, child) :: ms) =
      (chanIndex c, childChan child) :: (treeEdges child ++ childEdges ms) := by
  rw [childEdges]

@[simp] lemma subEdges_nil : subEdges [] = [] := by rw [subEdges]

@[simp] lemma subEdges_cons (t : Tree) (ns : List Tree) :
    subEdges (t :: ns) = treeEdges t ++ subEdges ns := by
  rw [subEdges]

/-! ## The canonical edge renaming -/

/-- The canonical name→binder renaming of an edge list: a name belonging to the `p`-th edge maps
to binder `p`; every other name embeds above the binders. -/
def edgeRen : List (Nat × Nat) → Nat → Nat
  | [], x => x
  | e :: es, x => if e.1 = x ∨ e.2 = x then 0 else edgeRen es x + 1

@[simp] lemma edgeRen_nil (x : Nat) : edgeRen [] x = x := rfl

lemma edgeRen_cons_hit {e : Nat × Nat} {x : Nat} (h : e.1 = x ∨ e.2 = x)
    (es : List (Nat × Nat)) : edgeRen (e :: es) x = 0 := by
  rw [edgeRen, if_pos h]

lemma edgeRen_cons_miss {e : Nat × Nat} {x : Nat} (h1 : e.1 ≠ x) (h2 : e.2 ≠ x)
    (es : List (Nat × Nat)) : edgeRen (e :: es) x = edgeRen es x + 1 := by
  rw [edgeRen, if_neg (by tauto)]

/-- Names foreign to the edge list embed above the binders. -/
lemma edgeRen_junk : ∀ {es : List (Nat × Nat)} {x : Nat},
    (∀ e ∈ es, e.1 ≠ x ∧ e.2 ≠ x) → edgeRen es x = es.length + x := by
  intro es
  induction es with
  | nil => intro x _; simp
  | cons e es ih =>
      intro x h
      rw [edgeRen_cons_miss (h e (by simp)).1 (h e (by simp)).2,
        ih (fun e' he' => h e' (by simp [he']))]
      simp [List.length_cons]
      omega

/-- Names of the `p`-th edge map to `p`, provided they avoid all earlier edges. -/
lemma edgeRen_hit : ∀ {es : List (Nat × Nat)} {p : Nat} {ed : Nat × Nat} {x : Nat},
    getElem? es p = some ed → (ed.1 = x ∨ ed.2 = x) →
    (∀ q e', q < p → getElem? es q = some e' → e'.1 ≠ x ∧ e'.2 ≠ x) →
    edgeRen es x = p := by
  intro es
  induction es with
  | nil => intro p ed x h _ _; cases h
  | cons e es ih =>
      intro p ed x h hx hbefore
      cases p with
      | zero =>
          rw [List.getElem?_cons_zero] at h
          obtain rfl := Option.some.inj h
          exact edgeRen_cons_hit hx es
      | succ p =>
          rw [List.getElem?_cons_succ] at h
          have he : e.1 ≠ x ∧ e.2 ≠ x := hbefore 0 e (by omega) List.getElem?_cons_zero
          rw [edgeRen_cons_miss he.1 he.2,
            ih h hx (fun q e' hq hq' =>
              hbefore (q + 1) e' (by omega) (by rw [List.getElem?_cons_succ]; exact hq'))]

/-- A name that misses a prefix of edges renames through the suffix, shifted. -/
lemma edgeRen_append_miss : ∀ {es1 : List (Nat × Nat)} {x : Nat} (es2 : List (Nat × Nat)),
    (∀ e ∈ es1, e.1 ≠ x ∧ e.2 ≠ x) →
    edgeRen (es1 ++ es2) x = es1.length + edgeRen es2 x := by
  intro es1
  induction es1 with
  | nil => intro x es2 _; simp
  | cons e es1 ih =>
      intro x es2 h
      rw [List.cons_append, edgeRen_cons_miss (h e (by simp)).1 (h e (by simp)).2,
        ih es2 (fun e' he' => h e' (by simp [he']))]
      simp [List.length_cons]
      omega

/-- A name hitting a prefix of edges ignores the suffix. -/
lemma edgeRen_append_hit : ∀ {es1 : List (Nat × Nat)} {x : Nat} (es2 : List (Nat × Nat)),
    edgeRen es1 x < es1.length →
    edgeRen (es1 ++ es2) x = edgeRen es1 x := by
  intro es1
  induction es1 with
  | nil => intro x es2 h; simp at h
  | cons e es1 ih =>
      intro x es2 h
      by_cases hx : e.1 = x ∨ e.2 = x
      · rw [List.cons_append, edgeRen_cons_hit hx, edgeRen_cons_hit hx]
      · push Not at hx
        rw [edgeRen_cons_miss hx.1 hx.2] at h
        rw [List.cons_append, edgeRen_cons_miss hx.1 hx.2, edgeRen_cons_miss hx.1 hx.2,
          ih es2 (by simp [List.length_cons] at h; omega)]

/-! ## Soup equivalence under lifted renamings -/

private lemma cswap_liftBinders_comm {k i j : Nat} (ξ : Nat → Nat) (hi : i < k) (hj : j < k) :
    ∀ x, cswap i j (liftBinders k ξ x) = liftBinders k ξ (cswap i j x) := by
  intro x
  rcases Nat.lt_or_ge x k with hx | hx
  · rw [TLLC.Process.liftBinders_lt _ hx]
    have hlt : cswap i j x < k := by
      unfold TLLC.Process.cswap
      split_ifs <;> omega
    rw [TLLC.Process.liftBinders_lt _ hlt]
  · rw [TLLC.Process.liftBinders_ge _ hx,
      TLLC.Process.cswap_ne (x := x) (by omega) (by omega),
      TLLC.Process.cswap_ne (x := k + ξ (x - k)) (by omega) (by omega),
      TLLC.Process.liftBinders_ge _ hx]

private lemma soupG_map_lift {ξ : Nat → Nat} {c c' : Config}
    (h : SoupG c c') :
    SoupEquiv (c.1, c.2.map (fun m => m⟨liftBinders c.1 ξ; (id : Nat → Nat)⟩))
      (c'.1, c'.2.map (fun m => m⟨liftBinders c'.1 ξ; (id : Nat → Nat)⟩)) := by
  cases h with
  | @perm k ts ts' hp =>
      exact TLLC.Process.SoupEquiv.perm (hp.map _)
  | @congr k ts ts' hc =>
      exact TLLC.Process.SoupEquiv.congr (TLLC.Process.forall₂_congr_map _ hc)
  | @garbage k ts =>
      refine ARS.conv1 ?_
      rw [List.map_cons, tren_pure_one]
      exact TLLC.Process.SoupG.garbage
  | @swap k ts i j hi hj =>
      have e : (ts.map (fun m => m⟨cswap i j; (id : Nat → Nat)⟩)).map
          (fun m => m⟨liftBinders k ξ; (id : Nat → Nat)⟩) =
          (ts.map (fun m => m⟨liftBinders k ξ; (id : Nat → Nat)⟩)).map
            (fun m => m⟨cswap i j; (id : Nat → Nat)⟩) := by
        rw [tsmap_comp, tsmap_comp]
        exact tsmap_ext ts (fun x => (cswap_liftBinders_comm ξ hi hj x).symm)
      rw [show ((k, ts.map (fun m => m⟨cswap i j; (id : Nat → Nat)⟩)) : Config).1 = k from rfl]
      rw [show ((k, ts.map (fun m => m⟨cswap i j; (id : Nat → Nat)⟩)) : Config).2 =
        ts.map (fun m => m⟨cswap i j; (id : Nat → Nat)⟩) from rfl]
      rw [e]
      exact TLLC.Process.SoupEquiv.swap i j hi hj

/-- The soup equivalence is congruent under renaming every thread by a bijection lifted over the
binders. -/
lemma soupEquiv_map_lift {ξ : Nat → Nat} {c c' : Config} (h : SoupEquiv c c') :
    SoupEquiv (c.1, c.2.map (fun m => m⟨liftBinders c.1 ξ; (id : Nat → Nat)⟩))
      (c'.1, c'.2.map (fun m => m⟨liftBinders c'.1 ξ; (id : Nat → Nat)⟩)) := by
  induction h with
  | refl => exact ARS.Conv.refl
  | tail _ hg ih => exact ARS.conv_trans ih (soupG_map_lift hg)
  | taili _ hg ih => exact ARS.conv_trans ih (ARS.conv_sym (soupG_map_lift hg))

/-! ## The canonical soup of a tree -/

/-- The canonical soup of a spawning tree under a global name→binder renaming: one binder per
edge, one thread per node body. -/
def treeSoup (σ : Nat → Nat) (t : Tree) : Config :=
  ((treeEdges t).length, (treeBodies t).map (fun b => b⟨σ; (id : Nat → Nat)⟩))

/-- A renaming describing the tree's edges: both names of the `p`-th edge map to binder `p`, and
names foreign to the tree map above the binders. -/
structure TreeRen (σ : Nat → Nat) (t : Tree) : Prop where
  realizes : ∀ p (hp : p < (treeEdges t).length),
    σ ((treeEdges t).get ⟨p, hp⟩).1 = p ∧ σ ((treeEdges t).get ⟨p, hp⟩).2 = p
  junkHigh : ∀ x, x ∉ treeChans t → (treeEdges t).length ≤ σ x

/-- The canonical soup of a children list together with the owning node's body. -/
def childSoup (m : Term) (ms : List (Chan × Tree)) : Config :=
  ((childEdges ms).length,
    (m :: childBodies ms).map (fun b => b⟨edgeRen (childEdges ms); (id : Nat → Nat)⟩))

/-! ## Context support of the children typing judgments -/

private lemma shiftChildren_labels (ms : List (Chan × Tree)) :
    (shiftChildren ms).map (fun e => chanIndex e.1) =
      ms.map (fun e => chanIndex e.1 + 1) := by
  induction ms with
  | nil => rfl
  | cons p ms ih =>
      obtain ⟨c, ch⟩ := p
      cases c with
      | var_Chan x =>
          simp only [shiftChildren, List.map_cons, ih]
          rfl

/-- Every live slot of a children context is a child label. -/
lemma ChildrenTyped.support : ∀ {Θ : PCtx} {ms : List (Chan × Tree)}, ChildrenTyped Θ ms →
    ∀ x, TLLC.Process.pcount Θ x ≠ 0 → x ∈ ms.map (fun e => chanIndex e.1) := by
  intro Θ
  induction Θ with
  | nil =>
      intro ms h x hx
      cases h with
      | nil => exact absurd rfl hx
  | cons s Θ ih =>
      intro ms h x hx
      cases h with
      | none hrest =>
          cases x with
          | zero => exact absurd rfl hx
          | succ x =>
              have hmem := ih hrest x hx
              rw [shiftChildren_labels]
              obtain ⟨e, he, hex⟩ := List.mem_map.mp hmem
              exact List.mem_map.mpr ⟨e, he, by omega⟩
      | one hch hrest =>
          cases x with
          | zero =>
              rw [List.map_cons]
              exact List.mem_cons.mpr (.inl rfl)
          | succ x =>
              have hmem := ih hrest x hx
              rw [List.map_cons, shiftChildren_labels]
              refine List.mem_cons.mpr (.inr ?_)
              obtain ⟨e, he, hex⟩ := List.mem_map.mp hmem
              exact List.mem_map.mpr ⟨e, he, by omega⟩

/-- Every live slot of a parent-reserving children context is the parent or a child label. -/
lemma ChildrenTypedAt.support : ∀ {Θ : PCtx} {p : Nat} {r : Bool} {A : Term}
    {ms : List (Chan × Tree)}, ChildrenTypedAt Θ p r A ms →
    ∀ x, TLLC.Process.pcount Θ x ≠ 0 → x = p ∨ x ∈ ms.map (fun e => chanIndex e.1) := by
  intro Θ
  induction Θ with
  | nil => intro p r A ms h x hx; cases h
  | cons s Θ ih =>
      intro p r A ms h x hx
      cases h with
      | parent hch =>
          cases x with
          | zero => exact .inl rfl
          | succ x =>
              have hmem := hch.support x hx
              rw [shiftChildren_labels]
              obtain ⟨e, he, hex⟩ := List.mem_map.mp hmem
              exact .inr (List.mem_map.mpr ⟨e, he, by omega⟩)
      | none hrest =>
          cases x with
          | zero => exact absurd rfl hx
          | succ x =>
              rcases ih hrest x hx with rfl | hmem
              · exact .inl rfl
              · rw [shiftChildren_labels]
                obtain ⟨e, he, hex⟩ := List.mem_map.mp hmem
                exact .inr (List.mem_map.mpr ⟨e, he, by omega⟩)
      | one hch hrest =>
          cases x with
          | zero =>
              rw [List.map_cons]
              exact .inr (List.mem_cons.mpr (.inl rfl))
          | succ x =>
              rcases ih hrest x hx with rfl | hmem
              · exact .inl rfl
              · rw [List.map_cons, shiftChildren_labels]
                refine .inr (List.mem_cons.mpr (.inr ?_))
                obtain ⟨e, he, hex⟩ := List.mem_map.mp hmem
                exact List.mem_map.mpr ⟨e, he, by omega⟩

/-! ## Edge names and distinctness -/

/-- Both names of every edge, flattened in edge order. -/
def edgeNames (es : List (Nat × Nat)) : List Nat :=
  es.flatMap (fun e => [e.1, e.2])

@[simp] lemma edgeNames_nil : edgeNames [] = [] := rfl

@[simp] lemma edgeNames_cons (e : Nat × Nat) (es : List (Nat × Nat)) :
    edgeNames (e :: es) = e.1 :: e.2 :: edgeNames es := rfl

lemma edgeNames_append (l r : List (Nat × Nat)) :
    edgeNames (l ++ r) = edgeNames l ++ edgeNames r := by
  unfold edgeNames
  exact List.flatMap_append ..

private lemma mem_edgeNames_of_mem {es : List (Nat × Nat)} {e : Nat × Nat} (h : e ∈ es) :
    e.1 ∈ edgeNames es ∧ e.2 ∈ edgeNames es := by
  constructor <;> (unfold edgeNames; exact List.mem_flatMap.mpr ⟨e, h, by simp⟩)

/-- The channels of a tree below the node's own endpoint. -/
def treeChansTail : Tree → List Nat
  | .root _ ms ns => (ms.map (fun e => chanIndex e.1)) ++ childInteriors ms ++ subInteriors ns
  | .node _ _ ms ns => (ms.map (fun e => chanIndex e.1)) ++ childInteriors ms ++ subInteriors ns

@[simp] lemma treeChansTail_root (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeChansTail (.root m ms ns) =
      (ms.map (fun e => chanIndex e.1)) ++ childInteriors ms ++ subInteriors ns := rfl

@[simp] lemma treeChansTail_node (d : Chan) (m : Term) (ms : List (Chan × Tree))
    (ns : List Tree) :
    treeChansTail (.node d m ms ns) =
      (ms.map (fun e => chanIndex e.1)) ++ childInteriors ms ++ subInteriors ns := rfl

lemma treeChans_eq_tail_root (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeChans (.root m ms ns) = treeChansTail (.root m ms ns) := by
  rw [treeChans_root, treeChansTail_root]

lemma treeChans_eq_tail_node (d : Chan) (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeChans (.node d m ms ns) = chanIndex d :: treeChansTail (.node d m ms ns) := by
  rw [treeChans_node, treeChansTail_node]

/-- Shifting the labels leaves the interiors unchanged. -/
lemma childInteriors_shiftChildren : ∀ (ms : List (Chan × Tree)),
    childInteriors (shiftChildren ms) = childInteriors ms := by
  intro ms
  induction ms with
  | nil => rfl
  | cons p ms ih =>
      obtain ⟨c, ch⟩ := p
      cases c with
      | var_Chan x =>
          show childInteriors ((Chan.var_Chan (x + 1), ch) :: shiftChildren ms) = _
          rw [childInteriors_cons, childInteriors_cons, ih]

/-- Renamings that agree on every explicitly occurring channel produce congruent terms (local
copy of the lemma in `TLLC/Spawning/Reflection.lean`). -/
private lemma congrTerm_cren_of_occurs' {m : Term} {ξ ζ : Nat → Nat}
    (h : ∀ x, occurs x m ≠ 0 → ξ x = ζ x) :
    TLLC.Process.CongrTerm .ex (m⟨ξ; (id : Nat → Nat)⟩) (m⟨ζ; (id : Nat → Nat)⟩) := by
  have e1 : m⟨ξ; (id : Nat → Nat)⟩ =
      m[(fun x => Chan.var_Chan (ξ x)); Term.var_Term] := by
    rw [← TLLC.Static.csubst_cren]
    exact tren_ext m (fun x => rfl)
  have e2 : m⟨ζ; (id : Nat → Nat)⟩ =
      m[(fun x => Chan.var_Chan (ζ x)); Term.var_Term] := by
    rw [← TLLC.Static.csubst_cren]
    exact tren_ext m (fun x => rfl)
  rw [e1, e2]
  exact congrTerm_csubst_of_occurs (fun _ x hx => by rw [h x hx])

/-- The endpoint-binding substitution is the renaming sending the bound name to `0` and shifting
everything else up. -/
private lemma csubst_ren_bindEndpointAt (c : Chan) :
    ∀ x, TLLC.Static.csubst_ren (bindEndpointAt 0 c) x =
      if x = chanIndex c then 0 else x + 1 := by
  intro x
  unfold TLLC.Static.csubst_ren bindEndpointAt
  simp only [Nat.add_zero]
  split_ifs <;> rfl

/-- Every edge name is hit by the canonical renaming. -/
private lemma edgeRen_lt_of_mem_names : ∀ {es : List (Nat × Nat)} {x : Nat},
    x ∈ edgeNames es → edgeRen es x < es.length := by
  intro es
  induction es with
  | nil => intro x hx; cases hx
  | cons e es ih =>
      intro x hx
      rw [edgeNames_cons] at hx
      by_cases h : e.1 = x ∨ e.2 = x
      · rw [edgeRen_cons_hit h]
        simp
      · push Not at h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd rfl h.1
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd rfl h.2
        rw [edgeRen_cons_miss h.1 h.2]
        have := ih hx
        simp [List.length_cons]
        omega

/-- Every top-level label is an edge name of the children scope. -/
private lemma labels_mem_edgeNames : ∀ {ms : List (Chan × Tree)} {x : Nat},
    x ∈ ms.map (fun e => chanIndex e.1) → x ∈ edgeNames (childEdges ms) := by
  intro ms
  induction ms with
  | nil => intro x hx; cases hx
  | cons p ms ih =>
      obtain ⟨c, ch⟩ := p
      intro x hx
      rw [List.map_cons] at hx
      rw [childEdges_cons, edgeNames_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
        rw [edgeNames_append]
        exact List.mem_append.mpr (.inr (ih hx))

/-- Assembling two canonically-renamed blocks: the parallel composition of the soups of two
disjoint edge scopes is the soup of the appended scope. Explicit occurrences must either hit
their own block's edges or avoid both blocks' edges; implicit occurrences are absorbed by the
congruence generator. -/
private lemma forall₂_map_rel {R : Term → Term → Prop} {f g : Term → Term} :
    ∀ (l : List Term), (∀ b ∈ l, R (f b) (g b)) → List.Forall₂ R (l.map f) (l.map g) := by
  intro l
  induction l with
  | nil => intro _; exact .nil
  | cons b l ih =>
      intro h
      exact .cons (h b (by simp)) (ih (fun b' hb' => h b' (by simp [hb'])))

private lemma parConfig_edgeRen_assemble {es1 es2 : List (Nat × Nat)} {l1 l2 : List Term}
    (h1 : ∀ b ∈ l1, ∀ x, occurs x b ≠ 0 →
      edgeRen es1 x < es1.length ∨ (∀ e ∈ es1 ++ es2, e.1 ≠ x ∧ e.2 ≠ x))
    (h2 : ∀ b ∈ l2, ∀ x, occurs x b ≠ 0 →
      (edgeRen es2 x < es2.length ∧ (∀ e ∈ es1, e.1 ≠ x ∧ e.2 ≠ x)) ∨
      (∀ e ∈ es1 ++ es2, e.1 ≠ x ∧ e.2 ≠ x)) :
    SoupEquiv
      (parConfig (es1.length, l1.map (fun b => b⟨edgeRen es1; (id : Nat → Nat)⟩))
        (es2.length, l2.map (fun b => b⟨edgeRen es2; (id : Nat → Nat)⟩)))
      ((es1 ++ es2).length, (l1 ++ l2).map (fun b => b⟨edgeRen (es1 ++ es2);
        (id : Nat → Nat)⟩)) := by
  show SoupEquiv (es1.length + es2.length,
    (l1.map (fun b => b⟨edgeRen es1; (id : Nat → Nat)⟩)).map
      (fun b => b⟨TLLC.Process.shiftAbove es1.length es2.length; (id : Nat → Nat)⟩) ++
    (l2.map (fun b => b⟨edgeRen es2; (id : Nat → Nat)⟩)).map
      (fun b => b⟨(· + es1.length); (id : Nat → Nat)⟩)) _
  rw [tsmap_comp, tsmap_comp,
    show (es1 ++ es2).length = es1.length + es2.length from by
      rw [List.length_append],
    List.map_append]
  refine TLLC.Process.SoupEquiv.congr ?_
  refine TLLC.Process.forall₂_append ?_ ?_
  · -- left block: shiftAbove ∘ edgeRen es1 agrees with edgeRen (es1 ++ es2) at explicit names
    refine forall₂_map_rel l1 (fun b hb => congrTerm_cren_of_occurs' (fun x hx => ?_))
    rcases h1 b hb x hx with hhit | havoid
    · show TLLC.Process.shiftAbove es1.length es2.length (edgeRen es1 x) = _
      rw [TLLC.Process.shiftAbove_lt hhit, edgeRen_append_hit es2 hhit]
    · show TLLC.Process.shiftAbove es1.length es2.length (edgeRen es1 x) = _
      rw [edgeRen_junk (fun e he => havoid e (List.mem_append.mpr (.inl he))),
        TLLC.Process.shiftAbove_ge (by omega), edgeRen_junk havoid, List.length_append]
      omega
  · -- right block: (+ |es1|) ∘ edgeRen es2 agrees with edgeRen (es1 ++ es2) at explicit names
    refine forall₂_map_rel l2 (fun b hb => congrTerm_cren_of_occurs' (fun x hx => ?_))
    rcases h2 b hb x hx with ⟨hhit, havoid1⟩ | havoid
    · show edgeRen es2 x + es1.length = edgeRen (es1 ++ es2) x
      rw [edgeRen_append_miss es2 havoid1]
      omega
    · show edgeRen es2 x + es1.length = edgeRen (es1 ++ es2) x
      rw [edgeRen_junk (fun e he => havoid e (List.mem_append.mpr (.inr he))),
        edgeRen_junk havoid, List.length_append]
      omega

/-! ## Folding the prenex over parallel compositions -/

private lemma foldl_parConfig_base_congr : ∀ (ps : List Proc) {c c' : Config},
    SoupEquiv c c' →
    SoupEquiv (ps.foldl (fun c q => parConfig c (prenex q)) c)
      (ps.foldl (fun c q => parConfig c (prenex q)) c') := by
  intro ps
  induction ps with
  | nil => intro c c' h; exact h
  | cons q ps ih =>
      intro c c' h
      exact ih (TLLC.Process.SoupEquiv.parConfig_left _ h)

private lemma prenex_parAll : ∀ (ps : List Proc) (p : Proc),
    prenex (parAll p ps) = ps.foldl (fun c q => parConfig c (prenex q)) (prenex p) := by
  intro ps
  induction ps with
  | nil => intro p; rfl
  | cons q ps ih =>
      intro p
      rw [parAll_cons, ih, TLLC.Process.prenex_par]
      rfl

private lemma soupEquiv_foldl_parConfig : ∀ {ps : List Proc} {targets : List Config},
    List.Forall₂ (fun q d => SoupEquiv (prenex q) d) ps targets →
    ∀ {c c' : Config}, SoupEquiv c c' →
    SoupEquiv (ps.foldl (fun acc q => parConfig acc (prenex q)) c)
      (targets.foldl parConfig c') := by
  intro ps targets h
  induction h with
  | nil => intro c c' hcc; exact hcc
  | cons hqd _ ih =>
      intro c c' hcc
      exact ih (TLLC.Process.SoupEquiv.parConfig_congr hcc hqd)

/-- Folding canonically-renamed subtree blocks onto a canonically-renamed base: the result is
the soup of the appended edge scope. -/
private lemma foldl_edgeRen_assemble : ∀ (ns : List Tree) (es : List (Nat × Nat)) (l : List Term),
    (∀ b ∈ l, ∀ x, occurs x b ≠ 0 →
      edgeRen es x < es.length ∨
      ((∀ e ∈ es, e.1 ≠ x ∧ e.2 ≠ x) ∧ x ∉ subInteriors ns)) →
    (∀ n ∈ ns, (treeChans n).Nodup →
      SoupEquiv (prenex n.flatten) (treeSoup (edgeRen (treeEdges n)) n) ∧
      (∀ b ∈ treeBodies n, ∀ x, occurs x b ≠ 0 → x ∈ treeChans n) ∧
      (∀ y ∈ edgeNames (treeEdges n), y ∈ treeChans n) ∧
      (∀ y ∈ treeChans n, y ∈ edgeNames (treeEdges n))) →
    (∀ y ∈ edgeNames es, y ∉ subInteriors ns) →
    (subInteriors ns).Nodup →
    SoupEquiv
      ((ns.map Tree.flatten).foldl (fun c q => parConfig c (prenex q))
        (es.length, l.map (fun b => b⟨edgeRen es; (id : Nat → Nat)⟩)))
      ((es ++ subEdges ns).length,
        (l ++ subBodies ns).map (fun b => b⟨edgeRen (es ++ subEdges ns);
          (id : Nat → Nat)⟩)) := by
  intro ns
  induction ns with
  | nil =>
      intro es l _ _ _ _
      rw [subEdges_nil, subBodies_nil, List.append_nil, List.append_nil]
      exact ARS.Conv.refl
  | cons n ns' ih =>
      intro es l h1 hper h5 h6
      have hsubn : List.Sublist (treeChans n) (subInteriors (n :: ns')) :=
        treeChans_sublist_subInteriors (List.mem_cons_self ..)
      rw [subInteriors_cons] at h6
      obtain ⟨hndn, hndns', hdisj⟩ := List.nodup_append.mp h6
      obtain ⟨hAn, hBn, hCn, hDn⟩ := hper n (List.mem_cons_self ..) hndn
      show SoupEquiv ((ns'.map Tree.flatten).foldl (fun c q => parConfig c (prenex q))
        (parConfig (es.length, l.map (fun b => b⟨edgeRen es; (id : Nat → Nat)⟩))
          (prenex n.flatten))) _
      refine ARS.conv_trans (foldl_parConfig_base_congr _
        (ARS.conv_trans (TLLC.Process.SoupEquiv.parConfig_right _ hAn)
          (parConfig_edgeRen_assemble (es2 := treeEdges n) (l2 := treeBodies n) ?_ ?_))) ?_
      · -- base threads against the extended scope
        intro b hb x hx
        rcases h1 b hb x hx with hhit | ⟨havoid, hnot⟩
        · exact .inl hhit
        · refine .inr (fun e he => ?_)
          rcases List.mem_append.mp he with he | he
          · exact havoid e he
          · have hnames := mem_edgeNames_of_mem he
            constructor
            · intro h
              exact hnot (hsubn.subset (hCn x (h ▸ hnames.1)))
            · intro h
              exact hnot (hsubn.subset (hCn x (h ▸ hnames.2)))
      · -- subtree threads: their explicit names hit their own edges and avoid the base scope
        intro b hb x hx
        have hxn := hBn b hb x hx
        have hedge := hDn x hxn
        refine .inl ⟨edgeRen_lt_of_mem_names hedge, ?_⟩
        intro e he
        have hxes : x ∉ edgeNames es := fun hmem => h5 x hmem (hsubn.subset hxn)
        exact ⟨fun h => hxes (h ▸ (mem_edgeNames_of_mem he).1),
          fun h => hxes (h ▸ (mem_edgeNames_of_mem he).2)⟩
      · -- recurse with the extended scope
        rw [subEdges_cons, subBodies_cons, ← List.append_assoc, ← List.append_assoc]
        refine ih (es ++ treeEdges n) (l ++ treeBodies n) ?_ ?_ ?_ hndns'
        · intro b hb x hx
          rcases List.mem_append.mp hb with hb | hb
          · rcases h1 b hb x hx with hhit | ⟨havoid, hnot⟩
            · refine .inl ?_
              rw [edgeRen_append_hit (treeEdges n) hhit, List.length_append]
              omega
            · have hnotn : x ∉ treeChans n := fun hmem =>
                hnot (hsubn.subset hmem)
              refine .inr ⟨?_, ?_⟩
              · intro e he
                rcases List.mem_append.mp he with he | he
                · exact havoid e he
                · have hnames := mem_edgeNames_of_mem he
                  exact ⟨fun h => hnotn (hCn x (h ▸ hnames.1)),
                    fun h => hnotn (hCn x (h ▸ hnames.2))⟩
              · intro hmem
                exact hnot (by rw [subInteriors_cons]; exact List.mem_append.mpr (.inr hmem))
          · have hxn := hBn b hb x hx
            have hedge := hDn x hxn
            have hxes : ∀ e ∈ es, e.1 ≠ x ∧ e.2 ≠ x := by
              intro e he
              have hxesm : x ∉ edgeNames es := fun hmem => h5 x hmem (hsubn.subset hxn)
              exact ⟨fun h => hxesm (h ▸ (mem_edgeNames_of_mem he).1),
                fun h => hxesm (h ▸ (mem_edgeNames_of_mem he).2)⟩
            refine .inl ?_
            rw [edgeRen_append_miss (treeEdges n) hxes, List.length_append]
            have := edgeRen_lt_of_mem_names hedge
            omega
        · intro n' hn' hndn'
          exact hper n' (List.mem_cons_of_mem _ hn') hndn'
        · intro y hy
          rw [edgeNames_append] at hy
          rcases List.mem_append.mp hy with hy | hy
          · intro hmem
            exact h5 y hy (by rw [subInteriors_cons]; exact List.mem_append.mpr (.inr hmem))
          · intro hmem
            exact (hdisj y (hCn y hy) y hmem) rfl

/-- Only edge names are hit by the canonical renaming. -/
private lemma mem_names_of_edgeRen_lt : ∀ {es : List (Nat × Nat)} {x : Nat},
    edgeRen es x < es.length → x ∈ edgeNames es := by
  intro es
  induction es with
  | nil => intro x hx; simp at hx
  | cons e es ih =>
      intro x hx
      rw [edgeNames_cons]
      by_cases h : e.1 = x ∨ e.2 = x
      · rcases h with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (h ▸ List.mem_cons_self ..)
      · push Not at h
        rw [edgeRen_cons_miss h.1 h.2] at hx
        rw [List.length_cons] at hx
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih (by omega)))

/-- The binder re-index of the peeled-edge assembly: parent-block binders move above the
child block, child binders shift up by one, the new restriction becomes binder `0`. -/
private def consRen (ER EC : Nat) (p : Nat) : Nat :=
  if p < ER then 1 + EC + p
  else if p < ER + EC then 1 + (p - ER)
  else if p = ER + EC then 0 else p

private def consRenInv (ER EC : Nat) (q : Nat) : Nat :=
  if q = 0 then ER + EC
  else if q < 1 + EC then ER + (q - 1)
  else if q < 1 + EC + ER then q - (1 + EC)
  else q

private lemma consRen_inv1 (ER EC : Nat) : ∀ p, consRenInv ER EC (consRen ER EC p) = p := by
  intro p
  unfold consRen consRenInv
  split_ifs <;> omega

private lemma consRen_inv2 (ER EC : Nat) : ∀ q, consRen ER EC (consRenInv ER EC q) = q := by
  intro q
  unfold consRen consRenInv
  split_ifs <;> omega

private lemma consRen_fix (ER EC : Nat) : ∀ p, ER + EC + 1 ≤ p → consRen ER EC p = p := by
  intro p hp
  unfold consRen
  split_ifs <;> omega

/-- Pointwise agreement of the parent-block composite renaming with the extended canonical
renaming, at every explicitly used name. -/
private lemma consRen_left {ℓ xc : Nat} {child : Tree} {rest : List (Chan × Tree)}
    (hcc : childChan child = xc)
    (hCr : ∀ y ∈ edgeNames (childEdges rest),
      y ∈ (rest.map (fun e => chanIndex e.1)) ++ childInteriors rest)
    (hCch : ∀ y ∈ edgeNames (treeEdges child), y ∈ treeChansTail child)
    (hchans : treeChans child = xc :: treeChansTail child)
    (hℓ : ℓ ∉ (rest.map (fun e => chanIndex e.1)) ++ childInteriors rest)
    (hdisjCR : ∀ y ∈ treeChans child,
      y ∉ (rest.map (fun e => chanIndex e.1)) ++ childInteriors rest)
    {x : Nat}
    (hx : x = ℓ ∨ edgeRen (childEdges rest) x < (childEdges rest).length ∨
      (∀ e ∈ childEdges ((Chan.var_Chan ℓ, child) :: rest), e.1 ≠ x ∧ e.2 ≠ x)) :
    consRen (childEdges rest).length (treeEdges child).length
      (TLLC.Process.shiftAbove (childEdges rest).length (treeEdges child).length
        (liftBinders (childEdges rest).length
          (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan ℓ)))
          (edgeRen (childEdges rest) x))) =
    edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest)) x := by
  have hρ := csubst_ren_bindEndpointAt (Chan.var_Chan ℓ)
  rcases hx with rfl | hhit | hjunk
  case inr.inr =>
    have hjunk' : ∀ e ∈ childEdges rest, e.1 ≠ x ∧ e.2 ≠ x := by
      intro e he
      refine hjunk e ?_
      rw [childEdges_cons]
      exact List.mem_cons_of_mem _ (List.mem_append.mpr (.inr he))
    have hxℓ : x ≠ ℓ := by
      intro h
      have := (hjunk (chanIndex (Chan.var_Chan ℓ), childChan child)
        (by rw [childEdges_cons]; exact List.mem_cons_self ..)).1
      exact this (by rw [h]; rfl)
    rw [edgeRen_junk hjunk', TLLC.Process.liftBinders_ge _ (by omega),
      show (childEdges rest).length + x - (childEdges rest).length = x from by omega,
      hρ x, if_neg (show ¬(x = chanIndex (Chan.var_Chan ℓ)) from fun h => hxℓ h),
      TLLC.Process.shiftAbove_ge (by omega),
      edgeRen_junk hjunk, childEdges_cons, List.length_cons, List.length_append]
    unfold consRen
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    omega
  · have h1 : edgeRen (childEdges rest) x = (childEdges rest).length + x :=
      edgeRen_junk (fun e he => by
        have hn := mem_edgeNames_of_mem he
        constructor
        · intro h
          refine hℓ ?_
          rw [← h]
          exact hCr _ hn.1
        · intro h
          refine hℓ ?_
          rw [← h]
          exact hCr _ hn.2)
    rw [h1, TLLC.Process.liftBinders_ge _ (by omega),
      show (childEdges rest).length + x - (childEdges rest).length = x from by omega,
      hρ x, if_pos (show x = chanIndex (Chan.var_Chan x) from rfl), Nat.add_zero,
      TLLC.Process.shiftAbove_ge (by omega),
      childEdges_cons,
      edgeRen_cons_hit (e := (chanIndex (Chan.var_Chan x), childChan child)) (x := x)
        (.inl rfl) (treeEdges child ++ childEdges rest)]
    unfold consRen
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  · have hxnames : x ∈ edgeNames (childEdges rest) := mem_names_of_edgeRen_lt hhit
    have hxLI := hCr _ hxnames
    have hxc : x ∉ treeChans child := fun h => hdisjCR x h hxLI
    have hne1 : chanIndex (Chan.var_Chan ℓ) ≠ x := by
      intro h
      refine hℓ ?_
      have hh : ℓ = x := h
      rw [hh]
      exact hxLI
    have hne2 : childChan child ≠ x := by
      intro h
      refine hxc ?_
      rw [hchans, ← hcc, ← h]
      exact List.mem_cons_self ..
    have havoidC : ∀ e ∈ treeEdges child, e.1 ≠ x ∧ e.2 ≠ x := by
      intro e he
      have hn := mem_edgeNames_of_mem he
      constructor
      · intro h
        exact hxc (by rw [hchans]; exact List.mem_cons_of_mem _ (hCch _ (h ▸ hn.1)))
      · intro h
        exact hxc (by rw [hchans]; exact List.mem_cons_of_mem _ (hCch _ (h ▸ hn.2)))
    rw [TLLC.Process.liftBinders_lt _ hhit, TLLC.Process.shiftAbove_lt hhit,
      childEdges_cons, edgeRen_cons_miss hne1 hne2,
      edgeRen_append_miss (childEdges rest) havoidC]
    unfold consRen
    rw [if_pos hhit]
    omega

/-- Pointwise agreement of the child-block composite renaming with the extended canonical
renaming, at every explicitly used name. -/
private lemma consRen_right {ℓ xc : Nat} {child : Tree} {rest : List (Chan × Tree)}
    (hcc : childChan child = xc)
    (hCch : ∀ y ∈ edgeNames (treeEdges child), y ∈ treeChansTail child)
    (hDch : ∀ y ∈ treeChansTail child, y ∈ edgeNames (treeEdges child))
    (hchans : treeChans child = xc :: treeChansTail child)
    (hxctail : xc ∉ treeChansTail child)
    (hℓc : ℓ ∉ treeChans child)
    {x : Nat} (hx : x ∈ treeChans child) :
    consRen (childEdges rest).length (treeEdges child).length
      (liftBinders (treeEdges child).length
        (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan xc)))
        (edgeRen (treeEdges child) x) + (childEdges rest).length) =
    edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest)) x := by
  have hρ := csubst_ren_bindEndpointAt (Chan.var_Chan xc)
  rw [hchans] at hx
  rcases List.mem_cons.mp hx with rfl | hxtail
  · have h1 : edgeRen (treeEdges child) x = (treeEdges child).length + x :=
      edgeRen_junk (fun e he => by
        have hn := mem_edgeNames_of_mem he
        constructor
        · intro h
          refine hxctail ?_
          rw [← h]
          exact hCch _ hn.1
        · intro h
          refine hxctail ?_
          rw [← h]
          exact hCch _ hn.2)
    rw [h1, TLLC.Process.liftBinders_ge _ (by omega),
      show (treeEdges child).length + x - (treeEdges child).length = x from by omega,
      hρ x, if_pos (show x = chanIndex (Chan.var_Chan x) from rfl), Nat.add_zero,
      childEdges_cons,
      edgeRen_cons_hit (e := (chanIndex (Chan.var_Chan ℓ), childChan child)) (x := x)
        (.inr hcc) (treeEdges child ++ childEdges rest)]
    unfold consRen
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  · have hhitC : edgeRen (treeEdges child) x < (treeEdges child).length :=
      edgeRen_lt_of_mem_names (hDch _ hxtail)
    have hne1 : chanIndex (Chan.var_Chan ℓ) ≠ x := by
      intro h
      refine hℓc ?_
      rw [hchans]
      have hh : ℓ = x := h
      rw [hh]
      exact List.mem_cons_of_mem _ hxtail
    have hne2 : childChan child ≠ x := by
      intro h
      rw [hcc] at h
      refine hxctail ?_
      rw [h]
      exact hxtail
    rw [TLLC.Process.liftBinders_lt _ hhitC,
      childEdges_cons, edgeRen_cons_miss hne1 hne2,
      edgeRen_append_hit (childEdges rest) hhitC]
    unfold consRen
    rw [if_neg (by omega), if_pos (by omega)]
    omega

/-- Assembling one peeled child edge: the restriction over the endpoint-bound parent block and
child block is the canonical soup of the extended children list. All side facts are semantic:
descriptions of the two blocks, explicit-occurrence bounds, and name distinctness. -/
private lemma children_cons_assemble {ℓ xc : Nat} {m : Term} {child : Tree}
    {rest : List (Chan × Tree)}
    (hflatAt : child.flattenAt = (Chan.var_Chan xc, child.flatten))
    (hcc : childChan child = xc)
    (hchans : treeChans child = xc :: treeChansTail child)
    (hAr : SoupEquiv (prenex (flattenChildren (.tm m) rest))
      ((childEdges rest).length,
        (m :: childBodies rest).map (fun b => b⟨edgeRen (childEdges rest); (id : Nat → Nat)⟩)))
    (hAch : SoupEquiv (prenex child.flatten)
      ((treeEdges child).length,
        (treeBodies child).map (fun b => b⟨edgeRen (treeEdges child); (id : Nat → Nat)⟩)))
    (hBase : ∀ b ∈ m :: childBodies rest, ∀ x, occurs x b ≠ 0 →
      x = ℓ ∨ edgeRen (childEdges rest) x < (childEdges rest).length ∨
      (∀ e ∈ childEdges ((Chan.var_Chan ℓ, child) :: rest), e.1 ≠ x ∧ e.2 ≠ x))
    (hBch : ∀ b ∈ treeBodies child, ∀ x, occurs x b ≠ 0 → x ∈ treeChans child)
    (hCr : ∀ y ∈ edgeNames (childEdges rest), y ∈ (rest.map (fun e => chanIndex e.1)) ++
      childInteriors rest)
    (hCch : ∀ y ∈ edgeNames (treeEdges child), y ∈ treeChansTail child)
    (hDch : ∀ y ∈ treeChansTail child, y ∈ edgeNames (treeEdges child))
    (hℓ : ℓ ∉ (rest.map (fun e => chanIndex e.1)) ++ childInteriors rest)
    (hℓc : ℓ ∉ treeChans child)
    (hxcr : xc ∉ (rest.map (fun e => chanIndex e.1)) ++ childInteriors rest)
    (hndC : (treeChans child).Nodup)
    (hdisjCR : ∀ y ∈ treeChans child,
      y ∉ (rest.map (fun e => chanIndex e.1)) ++ childInteriors rest) :
    SoupEquiv (prenex (flattenChildren (.tm m) ((Chan.var_Chan ℓ, child) :: rest)))
      (childSoup m ((Chan.var_Chan ℓ, child) :: rest)) := by
  have heq : flattenChildren (.tm m) ((Chan.var_Chan ℓ, child) :: rest) =
      .nu (.par
        ((flattenChildren (.tm m) rest)[bindEndpointAt 0 (Chan.var_Chan ℓ); Term.var_Term])
        (child.flatten[bindEndpointAt 0 (Chan.var_Chan xc); Term.var_Term])) := by
    simp [flattenChildren, hflatAt]
  rw [heq, TLLC.Process.prenex_nu, TLLC.Process.prenex_par,
    ← process_csubst_cren (flattenChildren (.tm m) rest)
      (bindEndpointAt 0 (Chan.var_Chan ℓ)),
    ← process_csubst_cren child.flatten (bindEndpointAt 0 (Chan.var_Chan xc)),
    TLLC.Process.prenex_cren, TLLC.Process.prenex_cren]
  refine ARS.conv_trans (TLLC.Process.SoupEquiv.nuConfig_congr
    (TLLC.Process.SoupEquiv.parConfig_congr
      (soupEquiv_map_lift (ξ := TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan ℓ)))
        hAr)
      (soupEquiv_map_lift (ξ := TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan xc)))
        hAch))) ?_
  have hxctail : xc ∉ treeChansTail child := by
    have hh := hndC
    rw [hchans] at hh
    exact (List.nodup_cons.mp hh).1
  show SoupEquiv
    ((childEdges rest).length + (treeEdges child).length + 1,
      (((m :: childBodies rest).map
          (fun b => b⟨edgeRen (childEdges rest); (id : Nat → Nat)⟩)).map
        (fun b => b⟨liftBinders (childEdges rest).length
          (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan ℓ)));
          (id : Nat → Nat)⟩)).map
        (fun b => b⟨TLLC.Process.shiftAbove (childEdges rest).length
          (treeEdges child).length; (id : Nat → Nat)⟩) ++
      (((treeBodies child).map
          (fun b => b⟨edgeRen (treeEdges child); (id : Nat → Nat)⟩)).map
        (fun b => b⟨liftBinders (treeEdges child).length
          (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan xc)));
          (id : Nat → Nat)⟩)).map
        (fun b => b⟨(· + (childEdges rest).length); (id : Nat → Nat)⟩))
    (childSoup m ((Chan.var_Chan ℓ, child) :: rest))
  rw [tsmap_comp, tsmap_comp, tsmap_comp, tsmap_comp]
  refine ARS.conv_trans (TLLC.Process.SoupEquiv.ren
    (consRen (childEdges rest).length (treeEdges child).length)
    (consRenInv (childEdges rest).length (treeEdges child).length)
    (consRen_inv1 _ _) (consRen_inv2 _ _) (consRen_fix _ _)) ?_
  rw [List.map_append, tsmap_comp, tsmap_comp]
  refine ARS.conv_trans (TLLC.Process.SoupEquiv.congr
    (TLLC.Process.forall₂_append
      (forall₂_map_rel
        (g := fun b => b⟨edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest));
          (id : Nat → Nat)⟩)
        (m :: childBodies rest)
        (fun b hb => congrTerm_cren_of_occurs' (fun x hx => ?_)))
      (forall₂_map_rel
        (g := fun b => b⟨edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest));
          (id : Nat → Nat)⟩)
        (treeBodies child)
        (fun b hb => congrTerm_cren_of_occurs' (fun x hx => ?_))))) ?_
  · show consRen (childEdges rest).length (treeEdges child).length
      (TLLC.Process.shiftAbove (childEdges rest).length (treeEdges child).length
        (liftBinders (childEdges rest).length
          (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan ℓ)))
          (edgeRen (childEdges rest) x))) =
      edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest)) x
    exact consRen_left hcc hCr hCch hchans hℓ hdisjCR (hBase b hb x hx)
  · show consRen (childEdges rest).length (treeEdges child).length
      (liftBinders (treeEdges child).length
        (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan xc)))
        (edgeRen (treeEdges child) x) + (childEdges rest).length) =
      edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest)) x
    exact consRen_right hcc hCch hDch hchans hxctail hℓc (hBch b hb x hx)
  · unfold childSoup
    rw [show (childEdges ((Chan.var_Chan ℓ, child) :: rest)).length =
        (childEdges rest).length + (treeEdges child).length + 1 from by
      rw [childEdges_cons, List.length_cons, List.length_append]
      omega]
    rw [childBodies_cons]
    refine TLLC.Process.SoupEquiv.perm ?_
    have e : List.map
        (fun b => b⟨edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest));
          (id : Nat → Nat)⟩)
        (m :: (treeBodies child ++ childBodies rest)) =
        m⟨edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest)); (id : Nat → Nat)⟩ ::
        (List.map (fun b => b⟨edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest));
          (id : Nat → Nat)⟩) (treeBodies child) ++
        List.map (fun b => b⟨edgeRen (childEdges ((Chan.var_Chan ℓ, child) :: rest));
          (id : Nat → Nat)⟩) (childBodies rest)) := by
      rw [List.map_cons, List.map_append]
    rw [e]
    exact List.Perm.cons _ List.perm_append_comm

/-- Locate the edge a name belongs to. -/
lemma mem_edgeNames_getElem : ∀ {es : List (Nat × Nat)} {a : Nat},
    a ∈ edgeNames es → ∃ (p : Nat) (ed : Nat × Nat),
      getElem? es p = some ed ∧ (ed.1 = a ∨ ed.2 = a) := by
  intro es
  induction es with
  | nil => intro a ha; cases ha
  | cons e es ih =>
      intro a ha
      rw [edgeNames_cons] at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨0, e, List.getElem?_cons_zero, .inl rfl⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨0, e, List.getElem?_cons_zero, .inr rfl⟩
      · obtain ⟨p, ed, hp, hed⟩ := ih ha
        exact ⟨p + 1, ed, by rw [List.getElem?_cons_succ]; exact hp, hed⟩

/-- Renaming can only merge occurrences: the count at an image bounds the count at a preimage. -/
lemma occurs_cren_ge {f : Nat → Nat} (x : Nat) :
    ∀ m : Term, occurs x m ≤ occurs (f x) (m⟨f; (id : Nat → Nat)⟩) := by
  intro m
  induction m with
  | var_Term _ => exact Nat.le_refl _
  | srt _ => exact Nat.le_refl _
  | pi _ _ _ _ _ _ => exact Nat.le_refl _
  | lam _ _ _ _ _ ihm => asimp at ihm ⊢; simp only [occurs]; omega
  | app _ _ i0 ihm ihn =>
      cases i0 <;> (asimp at ihm ihn ⊢; simp only [occurs]; omega)
  | sig _ _ _ _ _ _ => exact Nat.le_refl _
  | pair _ _ i0 _ ihm ihn =>
      cases i0 <;> (asimp at ihm ihn ⊢; simp only [occurs]; omega)
  | proj _ _ _ _ ihm ihn => asimp at ihm ihn ⊢; simp only [occurs]; omega
  | fix _ _ _ ihm => asimp at ihm ⊢; simp only [occurs]; omega
  | unit => exact Nat.le_refl _
  | one => exact Nat.le_refl _
  | bool => exact Nat.le_refl _
  | tt => exact Nat.le_refl _
  | ff => exact Nat.le_refl _
  | ite _ _ _ _ _ ihm ihn1 ihn2 =>
      asimp at ihm ihn1 ihn2 ⊢; simp only [occurs]; omega
  | M _ _ => exact Nat.le_refl _
  | pure _ ihm => asimp at ihm ⊢; simp only [occurs]; omega
  | mlet _ _ ihm ihn => asimp at ihm ihn ⊢; simp only [occurs]; omega
  | proto => exact Nat.le_refl _
  | stop => exact Nat.le_refl _
  | act _ _ _ _ _ _ => exact Nat.le_refl _
  | ch _ _ _ => exact Nat.le_refl _
  | chan c =>
      cases c with
      | var_Chan y =>
          asimp
          show (if y = x then 1 else 0) ≤ (if f y = f x then 1 else 0)
          split_ifs with h1 h2 <;> first | omega | (exact absurd (by rw [h1]) h2)
  | fork _ _ _ ihm => asimp at ihm ⊢; simp only [occurs]; omega
  | recv _ _ ihm => asimp at ihm ⊢; simp only [occurs]; omega
  | send _ _ ihm => asimp at ihm ⊢; simp only [occurs]; omega
  | close _ _ ihm => asimp at ihm ⊢; simp only [occurs]; omega
  | box => exact Nat.le_refl _

/-! ## Replaying a body step on the tree -/

private lemma getElem?_append_split {α : Type _} {l r : List α} {i : Nat} {a : α}
    (h : getElem? (l ++ r) i = some a) :
    (i < l.length ∧ getElem? l i = some a) ∨
    (l.length ≤ i ∧ getElem? r (i - l.length) = some a) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · refine .inl ⟨hi, ?_⟩
    rw [← h]
    exact (List.getElem?_append_left hi).symm
  · refine .inr ⟨hi, ?_⟩
    rw [← h]
    exact (List.getElem?_append_right hi).symm

private lemma set_append_lt {α : Type _} : ∀ {l : List α} (r : List α) {i : Nat},
    i < l.length → ∀ (a : α), (l ++ r).set i a = l.set i a ++ r := by
  intro l
  induction l with
  | nil => intro r i hi a; simp at hi
  | cons x t ih =>
      intro r i hi a
      cases i with
      | zero => rfl
      | succ i =>
          show x :: (t ++ r).set i a = x :: (t.set i a ++ r)
          rw [ih r (by simp at hi; omega) a]

private lemma set_append_ge {α : Type _} : ∀ {l : List α} (r : List α) {i : Nat},
    l.length ≤ i → ∀ (a : α), (l ++ r).set i a = l ++ r.set (i - l.length) a := by
  intro l
  induction l with
  | nil => intro r i _ a; rfl
  | cons x t ih =>
      intro r i hi a
      cases i with
      | zero => simp at hi
      | succ i =>
          show x :: (t ++ r).set i a = x :: (t ++ r.set (i + 1 - (t.length + 1)) a)
          rw [ih r (by simp at hi; omega) a,
            show i + 1 - (t.length + 1) = i - t.length from by omega]

private lemma labels_surgery (l r : List (Chan × Tree)) (c : Chan) (x y : Tree) :
    (l ++ (c, x) :: r).map (fun e => chanIndex e.1) =
      (l ++ (c, y) :: r).map (fun e => chanIndex e.1) := by
  rw [List.map_append, List.map_append, List.map_cons, List.map_cons]

mutual

/-- Replaying a term step of the `i`-th body on the tree: fire the corresponding expression rule
under the path congruences. The step changes no channel structure. -/
lemma bodyStep_tree : ∀ (t : Tree) (i : Nat) (b b' : Term),
    getElem? (treeBodies t) i = some b → TLLC.Dynamic.Step b b' →
    ∃ t', Step t t' ∧ treeBodies t' = (treeBodies t).set i b' ∧
      treeEdges t' = treeEdges t ∧ treeChans t' = treeChans t ∧
      childChan t' = childChan t
  | .root m ms ns, i, b, b', hi, st => by
      rw [treeBodies_root] at hi
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hi
          obtain rfl := Option.some.inj hi
          exact ⟨.root b' ms ns, Step.rootExpr st,
            by rw [treeBodies_root, treeBodies_root]; rfl,
            by rw [treeEdges_root, treeEdges_root],
            by rw [treeChans_root, treeChans_root], rfl⟩
      | succ i =>
          rw [List.getElem?_cons_succ] at hi
          rcases getElem?_append_split hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩
          · obtain ⟨l, c, child, child', r, rfl, stc, hcc', hb, he, hin⟩ :=
              bodyStep_children ms i b b' hi' st
            refine ⟨.root m (l ++ (c, child') :: r) ns,
              Step.rootChild stc (fun x hx hnx => absurd (hcc' ▸ hx) hnx), ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_root, treeBodies_root, hb, List.set_cons_succ,
                set_append_lt _ hlt]
            · rw [treeEdges_root, treeEdges_root, he]
            · rw [treeChans_root, treeChans_root, hin, labels_surgery l r c child' child]
          · obtain ⟨l, sub, sub', r, rfl, sts, hcs', hb, he, hin⟩ :=
              bodyStep_subs ns (i - (childBodies ms).length) b b' hi' st
            refine ⟨.root m ms (l ++ sub' :: r),
              Step.rootSubtree sts (fun x hx hnx => absurd (hcs' ▸ hx) hnx), ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_root, treeBodies_root, hb, List.set_cons_succ,
                set_append_ge _ hge]
            · rw [treeEdges_root, treeEdges_root, he]
            · rw [treeChans_root, treeChans_root, hin]
  | .node d m ms ns, i, b, b', hi, st => by
      rw [treeBodies_node] at hi
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hi
          obtain rfl := Option.some.inj hi
          exact ⟨.node d b' ms ns, Step.nodeExpr st,
            by rw [treeBodies_node, treeBodies_node]; rfl,
            by rw [treeEdges_node, treeEdges_node],
            by rw [treeChans_node, treeChans_node], rfl⟩
      | succ i =>
          rw [List.getElem?_cons_succ] at hi
          rcases getElem?_append_split hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩
          · obtain ⟨l, c, child, child', r, rfl, stc, hcc', hb, he, hin⟩ :=
              bodyStep_children ms i b b' hi' st
            refine ⟨.node d m (l ++ (c, child') :: r) ns,
              Step.nodeChild stc (fun x hx hnx => absurd (hcc' ▸ hx) hnx), ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_node, treeBodies_node, hb, List.set_cons_succ,
                set_append_lt _ hlt]
            · rw [treeEdges_node, treeEdges_node, he]
            · rw [treeChans_node, treeChans_node, hin, labels_surgery l r c child' child]
          · obtain ⟨l, sub, sub', r, rfl, sts, hcs', hb, he, hin⟩ :=
              bodyStep_subs ns (i - (childBodies ms).length) b b' hi' st
            refine ⟨.node d m ms (l ++ sub' :: r),
              Step.nodeSubtree sts (fun x hx hnx => absurd (hcs' ▸ hx) hnx), ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_node, treeBodies_node, hb, List.set_cons_succ,
                set_append_ge _ hge]
            · rw [treeEdges_node, treeEdges_node, he]
            · rw [treeChans_node, treeChans_node, hin]
termination_by t _ _ _ _ _ => treeMeasure t
decreasing_by all_goals (simp only [treeMeasure]; omega)

/-- Replaying a body step inside a children list. -/
private lemma bodyStep_children : ∀ (ms : List (Chan × Tree)) (i : Nat) (b b' : Term),
    getElem? (childBodies ms) i = some b → TLLC.Dynamic.Step b b' →
    ∃ (l : List (Chan × Tree)) (c : Chan) (child child' : Tree) (r : List (Chan × Tree)),
      ms = l ++ (c, child) :: r ∧ Step child child' ∧
      treeChans child' = treeChans child ∧
      childBodies (l ++ (c, child') :: r) = (childBodies ms).set i b' ∧
      childEdges (l ++ (c, child') :: r) = childEdges ms ∧
      childInteriors (l ++ (c, child') :: r) = childInteriors ms
  | [], i, b, b', hi, st => by
      rw [childBodies_nil] at hi
      exact absurd hi (by simp)
  | (c, child) :: ms, i, b, b', hi, st => by
      rw [childBodies_cons] at hi
      rcases getElem?_append_split hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩
      · obtain ⟨child', stc, hb, he, hcs, hcc⟩ := bodyStep_tree child i b b' hi' st
        refine ⟨[], c, child, child', ms, rfl, stc, hcs, ?_, ?_, ?_⟩
        · rw [List.nil_append, childBodies_cons, childBodies_cons, hb,
            set_append_lt _ hlt]
        · rw [List.nil_append, childEdges_cons, childEdges_cons, he, hcc]
        · rw [List.nil_append, childInteriors_cons, childInteriors_cons, hcs]
      · obtain ⟨l, c', child₀, child₀', r, rfl, stc, hcs, hb, he, hin⟩ :=
          bodyStep_children ms (i - (treeBodies child).length) b b' hi' st
        refine ⟨(c, child) :: l, c', child₀, child₀', r, rfl, stc, hcs, ?_, ?_, ?_⟩
        · rw [List.cons_append, childBodies_cons, childBodies_cons, hb,
            set_append_ge _ hge]
        · rw [List.cons_append, childEdges_cons, childEdges_cons, he]
        · rw [List.cons_append, childInteriors_cons, childInteriors_cons, hin]
termination_by ms _ _ _ _ _ => childMeasure ms
decreasing_by all_goals (simp only [childMeasure]; omega)

/-- Replaying a body step inside a subtree list. -/
private lemma bodyStep_subs : ∀ (ns : List Tree) (i : Nat) (b b' : Term),
    getElem? (subBodies ns) i = some b → TLLC.Dynamic.Step b b' →
    ∃ (l : List Tree) (sub sub' : Tree) (r : List Tree),
      ns = l ++ sub :: r ∧ Step sub sub' ∧
      treeChans sub' = treeChans sub ∧
      subBodies (l ++ sub' :: r) = (subBodies ns).set i b' ∧
      subEdges (l ++ sub' :: r) = subEdges ns ∧
      subInteriors (l ++ sub' :: r) = subInteriors ns
  | [], i, b, b', hi, st => by
      rw [subBodies_nil] at hi
      exact absurd hi (by simp)
  | sub :: ns, i, b, b', hi, st => by
      rw [subBodies_cons] at hi
      rcases getElem?_append_split hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩
      · obtain ⟨sub', sts, hb, he, hcs, _⟩ := bodyStep_tree sub i b b' hi' st
        refine ⟨[], sub, sub', ns, rfl, sts, hcs, ?_, ?_, ?_⟩
        · rw [List.nil_append, subBodies_cons, subBodies_cons, hb, set_append_lt _ hlt]
        · rw [List.nil_append, subEdges_cons, subEdges_cons, he]
        · rw [List.nil_append, subInteriors_cons, subInteriors_cons, hcs]
      · obtain ⟨l, sub₀, sub₀', r, rfl, sts, hcs, hb, he, hin⟩ :=
          bodyStep_subs ns (i - (treeBodies sub).length) b b' hi' st
        refine ⟨sub :: l, sub₀, sub₀', r, rfl, sts, hcs, ?_, ?_, ?_⟩
        · rw [List.cons_append, subBodies_cons, subBodies_cons, hb, set_append_ge _ hge]
        · rw [List.cons_append, subEdges_cons, subEdges_cons, he]
        · rw [List.cons_append, subInteriors_cons, subInteriors_cons, hin]
termination_by ns _ _ _ _ _ => subMeasure ns
decreasing_by all_goals (simp only [subMeasure]; omega)

end

/-! ## Permutation congruence of the children functions -/

lemma childBodies_perm : ∀ {ms₁ ms₂ : List (Chan × Tree)}, ms₁.Perm ms₂ →
    (childBodies ms₁).Perm (childBodies ms₂) := by
  intro ms₁ ms₂ h
  induction h with
  | nil => exact List.Perm.refl _
  | cons p _ ih =>
      obtain ⟨c, ch⟩ := p
      rw [childBodies_cons, childBodies_cons]
      exact ih.append_left _
  | swap p q _ =>
      obtain ⟨c₁, ch₁⟩ := p
      obtain ⟨c₂, ch₂⟩ := q
      rw [childBodies_cons, childBodies_cons, childBodies_cons, childBodies_cons,
        ← List.append_assoc, ← List.append_assoc]
      exact (List.perm_append_comm.append_right _)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma childEdges_perm : ∀ {ms₁ ms₂ : List (Chan × Tree)}, ms₁.Perm ms₂ →
    (childEdges ms₁).Perm (childEdges ms₂) := by
  intro ms₁ ms₂ h
  induction h with
  | nil => exact List.Perm.refl _
  | cons p _ ih =>
      obtain ⟨c, ch⟩ := p
      rw [childEdges_cons, childEdges_cons]
      exact (ih.append_left _).cons _
  | swap p q _ =>
      obtain ⟨c₁, ch₁⟩ := p
      obtain ⟨c₂, ch₂⟩ := q
      rw [childEdges_cons, childEdges_cons, childEdges_cons, childEdges_cons]
      refine (List.Perm.cons _ List.perm_middle).trans ?_
      refine (List.Perm.swap _ _ _).trans ?_
      refine List.Perm.cons _ ?_
      refine (List.Perm.cons _ ?_).trans List.perm_middle.symm
      rw [← List.append_assoc, ← List.append_assoc]
      exact (List.perm_append_comm.append_right _)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma childInteriors_perm : ∀ {ms₁ ms₂ : List (Chan × Tree)}, ms₁.Perm ms₂ →
    (childInteriors ms₁).Perm (childInteriors ms₂) := by
  intro ms₁ ms₂ h
  induction h with
  | nil => exact List.Perm.refl _
  | cons p _ ih =>
      obtain ⟨c, ch⟩ := p
      rw [childInteriors_cons, childInteriors_cons]
      exact ih.append_left _
  | swap p q _ =>
      obtain ⟨c₁, ch₁⟩ := p
      obtain ⟨c₂, ch₂⟩ := q
      rw [childInteriors_cons, childInteriors_cons, childInteriors_cons,
        childInteriors_cons, ← List.append_assoc, ← List.append_assoc]
      exact (List.perm_append_comm.append_right _)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The occurrence split partitions the children. -/
lemma splitChildren_perm (v : Term) : ∀ (ms : List (Chan × Tree)),
    ((splitChildrenByTerm v ms).1 ++ (splitChildrenByTerm v ms).2).Perm ms := by
  intro ms
  induction ms with
  | nil => exact List.Perm.refl _
  | cons p ms ih =>
      obtain ⟨c, ch⟩ := p
      cases c with
      | var_Chan x =>
          by_cases h : Dynamic.occurs x v = 0
          · simp only [splitChildrenByTerm, if_pos h]
            exact List.perm_middle.trans (ih.cons _)
          · simp only [splitChildrenByTerm, if_neg h]
            exact ih.cons _

/-- The canonical-soup description and its side facts, proved by mutual induction over the
spawning-tree typing derivation. The five motives:
tree-level (`Typed`/`TypedAt`): the prenex soup of the flattening is the canonical tree soup,
bodies explicitly mention only tree channels, and the edge names embed into the channel list
below the node's endpoint; children-level: the same for `flattenChildren` at every label-shift
level; subtree-level: pointwise tree-level facts. -/
private def treeSoupMotive (t : Tree) : Prop :=
  (treeChans t).Nodup →
  SoupEquiv (prenex t.flatten) (treeSoup (edgeRen (treeEdges t)) t) ∧
  (∀ b ∈ treeBodies t, ∀ x, occurs x b ≠ 0 → x ∈ treeChans t) ∧
  (edgeNames (treeEdges t)).Subperm (treeChansTail t) ∧
  (∀ y ∈ treeChansTail t, y ∈ edgeNames (treeEdges t))

private def childSoupMotive (ms : List (Chan × Tree)) : Prop :=
  ∀ (ℓ : Nat) (m : Term),
    (∀ x, occurs x m ≠ 0 →
      x ∈ (shiftChildrenN ℓ ms).map (fun e => chanIndex e.1) ∨
      (∀ e ∈ childEdges (shiftChildrenN ℓ ms), e.1 ≠ x ∧ e.2 ≠ x)) →
    ((shiftChildrenN ℓ ms).map (fun e => chanIndex e.1) ++
      childInteriors (shiftChildrenN ℓ ms)).Nodup →
    SoupEquiv (prenex (flattenChildren (.tm m) (shiftChildrenN ℓ ms)))
      (childSoup m (shiftChildrenN ℓ ms)) ∧
    (∀ b ∈ childBodies (shiftChildrenN ℓ ms), ∀ x, occurs x b ≠ 0 →
      x ∈ (shiftChildrenN ℓ ms).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN ℓ ms)) ∧
    (edgeNames (childEdges (shiftChildrenN ℓ ms))).Subperm
      ((shiftChildrenN ℓ ms).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN ℓ ms)) ∧
    (∀ y ∈ (shiftChildrenN ℓ ms).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN ℓ ms),
      y ∈ edgeNames (childEdges (shiftChildrenN ℓ ms)))

private def subSoupMotive (ns : List Tree) : Prop :=
  (subInteriors ns).Nodup →
  (∀ n ∈ ns, (treeChans n).Nodup →
    SoupEquiv (prenex n.flatten) (treeSoup (edgeRen (treeEdges n)) n) ∧
    (∀ b ∈ treeBodies n, ∀ x, occurs x b ≠ 0 → x ∈ treeChans n) ∧
    (∀ y ∈ edgeNames (treeEdges n), y ∈ treeChans n) ∧
    (∀ y ∈ treeChans n, y ∈ edgeNames (treeEdges n))) ∧
  (∀ b ∈ subBodies ns, ∀ x, occurs x b ≠ 0 → x ∈ subInteriors ns) ∧
  (edgeNames (subEdges ns)).Subperm (subInteriors ns) ∧
  (∀ y ∈ subInteriors ns, y ∈ edgeNames (subEdges ns))

private theorem tree_soup_core {t : Tree} (ty : Typed t) : treeSoupMotive t := by
  refine Typed.rec
    (motive_1 := fun t _ => treeSoupMotive t)
    (motive_2 := fun r A t _ => treeSoupMotive t)
    (motive_3 := fun Θ ms _ => childSoupMotive ms)
    (motive_4 := fun Θ x r A ms _ => childSoupMotive ms)
    (motive_5 := fun ns _ => subSoupMotive ns)
    ?root ?node ?childrenNil ?childrenNone ?childrenOne ?atParent ?atNone ?atOne
    ?subsNil ?subsCons ty
  case root =>
    intro Θ m ms ns hsingle tym hch hsub ihCh ihSub hnd
    rw [treeChans_root] at hnd
    obtain ⟨hndL, hndS, hdisjLS⟩ := List.nodup_append.mp hnd
    have hmL : ∀ x, occurs x m ≠ 0 → x ∈ ms.map (fun e => chanIndex e.1) := by
      intro x hx
      refine hch.support x ?_
      rw [← TLLC.Process.dynOccursCount tym x]
      exact hx
    have hm : ∀ x, occurs x m ≠ 0 →
        x ∈ (shiftChildrenN 0 ms).map (fun e => chanIndex e.1) ∨
        (∀ e ∈ childEdges (shiftChildrenN 0 ms), e.1 ≠ x ∧ e.2 ≠ x) := by
      intro x hx
      rw [shiftChildrenN_zero]
      exact .inl (hmL x hx)
    have hndL' : ((shiftChildrenN 0 ms).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN 0 ms)).Nodup := by
      rw [shiftChildrenN_zero]
      exact hndL
    obtain ⟨hAc, hBc, hCc, hDc⟩ := ihCh 0 m hm hndL'
    rw [shiftChildrenN_zero] at hAc hBc hCc hDc
    obtain ⟨hAs, hBs, hCs, hDs⟩ := ihSub hndS
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Tree.flatten_root, flattenBody, prenex_parAll, flattenSubtrees_eq_map]
      refine ARS.conv_trans (foldl_parConfig_base_congr _ hAc) ?_
      refine ARS.conv_trans
        (foldl_edgeRen_assemble ns (childEdges ms) (m :: childBodies ms)
          ?_ hAs ?_ hndS) ?_
      · intro b hb x hx
        rcases List.mem_cons.mp hb with rfl | hb
        · exact .inl (edgeRen_lt_of_mem_names (labels_mem_edgeNames (hmL x hx)))
        · exact .inl (edgeRen_lt_of_mem_names (hDc x (hBc b hb x hx)))
      · intro y hy
        exact fun hmem => (hdisjLS y (hCc.subset hy) y hmem) rfl
      · unfold treeSoup
        rw [treeEdges_root, treeBodies_root]
        exact ARS.Conv.refl
    · intro b hb x hx
      rw [treeBodies_root] at hb
      rw [treeChans_root]
      rcases List.mem_cons.mp hb with rfl | hb
      · have hpc : TLLC.Process.pcount Θ x ≠ 0 := by
          rw [← TLLC.Process.dynOccursCount tym x]
          exact hx
        exact List.mem_append.mpr (.inl (List.mem_append.mpr
          (.inl (hch.support x hpc))))
      · rcases List.mem_append.mp hb with hb | hb
        · have := hBc b hb x hx
          rcases List.mem_append.mp this with h | h
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h)))
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
        · exact List.mem_append.mpr (.inr (hBs b hb x hx))
    · rw [treeEdges_root, edgeNames_append, treeChansTail_root]
      exact List.Subperm.append hCc hCs
    · intro y hy
      rw [treeChansTail_root] at hy
      rw [treeEdges_root, edgeNames_append]
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append.mpr (.inl (hDc y hy))
      · exact List.mem_append.mpr (.inr (hDs y hy))
  case node =>
    intro Θ x r A m ms ns hsingle hhas tym hch hsub ihCh ihSub hnd
    rw [treeChans_node] at hnd
    rw [List.nodup_cons] at hnd
    obtain ⟨hp, hnd'⟩ := hnd
    obtain ⟨hndL, hndS, hdisjLS⟩ := List.nodup_append.mp hnd'
    have hndL' : ((shiftChildrenN 0 ms).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN 0 ms)).Nodup := by
      rw [shiftChildrenN_zero]
      exact hndL
    -- extract the edge-name embedding first, with a body-free instantiation
    obtain ⟨_, _, hCc, _⟩ := ihCh 0 Term.one (fun y hy => absurd rfl hy) hndL'
    rw [shiftChildrenN_zero] at hCc
    have hm : ∀ y, occurs y m ≠ 0 →
        y ∈ (shiftChildrenN 0 ms).map (fun e => chanIndex e.1) ∨
        (∀ e ∈ childEdges (shiftChildrenN 0 ms), e.1 ≠ y ∧ e.2 ≠ y) := by
      intro y hy
      rw [shiftChildrenN_zero]
      have hpc : TLLC.Process.pcount Θ y ≠ 0 := by
        rw [← TLLC.Process.dynOccursCount tym y]
        exact hy
      rcases hch.support y hpc with rfl | hlab
      · refine .inr (fun e he => ?_)
        have hmem := mem_edgeNames_of_mem he
        constructor
        · intro h
          exact hp (List.mem_append.mpr (.inl (hCc.subset (h ▸ hmem.1))))
        · intro h
          exact hp (List.mem_append.mpr (.inl (hCc.subset (h ▸ hmem.2))))
      · exact .inl hlab
    obtain ⟨hAc, hBc, _, hDc⟩ := ihCh 0 m hm hndL'
    rw [shiftChildrenN_zero] at hAc hBc hDc
    obtain ⟨hAs, hBs, hCs, hDs⟩ := ihSub hndS
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Tree.flatten_node, flattenBody, prenex_parAll, flattenSubtrees_eq_map]
      refine ARS.conv_trans (foldl_parConfig_base_congr _ hAc) ?_
      refine ARS.conv_trans
        (foldl_edgeRen_assemble ns (childEdges ms) (m :: childBodies ms)
          ?_ hAs ?_ hndS) ?_
      · intro b hb y hy
        rcases List.mem_cons.mp hb with rfl | hb
        · have hpc : TLLC.Process.pcount Θ y ≠ 0 := by
            rw [← TLLC.Process.dynOccursCount tym y]
            exact hy
          rcases hch.support y hpc with rfl | hlab
          · refine .inr ⟨?_, ?_⟩
            · intro e he
              have hmem := mem_edgeNames_of_mem he
              constructor
              · intro h
                exact hp (List.mem_append.mpr (.inl (hCc.subset (h ▸ hmem.1))))
              · intro h
                exact hp (List.mem_append.mpr (.inl (hCc.subset (h ▸ hmem.2))))
            · intro hmem
              exact hp (List.mem_append.mpr (.inr hmem))
          · exact .inl (edgeRen_lt_of_mem_names (labels_mem_edgeNames hlab))
        · exact .inl (edgeRen_lt_of_mem_names (hDc y (hBc b hb y hy)))
      · intro y hy
        exact fun hmem => (hdisjLS y (hCc.subset hy) y hmem) rfl
      · unfold treeSoup
        rw [treeEdges_node, treeBodies_node]
        exact ARS.Conv.refl
    · intro b hb y hy
      rw [treeBodies_node] at hb
      rw [treeChans_node]
      rcases List.mem_cons.mp hb with rfl | hb
      · have hpc : TLLC.Process.pcount Θ y ≠ 0 := by
          rw [← TLLC.Process.dynOccursCount tym y]
          exact hy
        rcases hch.support y hpc with rfl | hlab
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr
            (.inl (List.mem_append.mpr (.inl hlab))))
      · rcases List.mem_append.mp hb with hb | hb
        · have := hBc b hb y hy
          rcases List.mem_append.mp this with h | h
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr
              (.inl (List.mem_append.mpr (.inl h))))
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr
              (.inl (List.mem_append.mpr (.inr h))))
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr (.inr (hBs b hb y hy)))
    · rw [treeEdges_node, edgeNames_append, treeChansTail_node]
      exact List.Subperm.append hCc hCs
    · intro y hy
      rw [treeChansTail_node] at hy
      rw [treeEdges_node, edgeNames_append]
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append.mpr (.inl (hDc y hy))
      · exact List.mem_append.mpr (.inr (hDs y hy))
  case childrenNil =>
    intro ℓ m hm hnd
    rw [shiftChildrenN_nil] at hm hnd ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [flattenChildren_nil, TLLC.Process.prenex_tm]
      unfold childSoup
      rw [childEdges_nil]
      have e : m⟨edgeRen []; (id : Nat → Nat)⟩ = m := by
        rw [tren_ext m (ξ := edgeRen []) (ζ := (id : Nat → Nat)) (fun x => rfl), tren_id]
      rw [show (m :: childBodies []).map
          (fun b => b⟨edgeRen []; (id : Nat → Nat)⟩) = [m] from by
        rw [childBodies_nil]
        simp only [List.map_cons, List.map_nil, e]]
      exact ARS.Conv.refl
    · intro b hb
      rw [childBodies_nil] at hb
      cases hb
    · rw [childEdges_nil, edgeNames_nil]
      exact List.nil_subperm
    · intro y hy
      rw [childInteriors_nil, List.map_nil] at hy
      cases hy
  case childrenNone =>
    intro Θ children _ ih ℓ m hm hnd
    rw [shiftChildrenN_shiftChildren] at hm hnd ⊢
    exact ih (ℓ + 1) m hm hnd
  case childrenOne =>
    intro Θ r A child children hchild hrest ihChild ihTail ℓ m hm hnd
    rw [shiftChildrenN_one_cons] at hm hnd ⊢
    cases child with
    | root mc msc nsc => cases hchild
    | node d mc msc nsc =>
    cases d with
    | var_Chan xc =>
    rw [List.map_cons, childInteriors_cons] at hnd
    obtain ⟨hℓbig, hndbig⟩ := List.nodup_cons.mp hnd
    obtain ⟨hndL', hndCX, hdisjL'⟩ := List.nodup_append.mp hndbig
    obtain ⟨hndC, hndI', hdisjCI⟩ := List.nodup_append.mp hndCX
    have hndT : ((shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children)).Nodup := by
      rw [List.nodup_append]
      exact ⟨hndL', hndI', fun a ha b hb => hdisjL' a ha b (List.mem_append.mpr (.inr hb))⟩
    have hℓr : ℓ ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children) := by
      intro hmem
      refine hℓbig ?_
      rcases List.mem_append.mp hmem with h | h
      · exact List.mem_append.mpr (.inl h)
      · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr h)))
    have hℓcC : ℓ ∉ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc) := by
      intro hmem
      exact hℓbig (List.mem_append.mpr (.inr (List.mem_append.mpr (.inl hmem))))
    have hxcC : xc ∈ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc) := by
      rw [treeChans_node]
      exact List.mem_cons_self ..
    have hdisjCRF : ∀ y ∈ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc),
        y ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
          childInteriors (shiftChildrenN (ℓ + 1) children) := by
      intro y hy hmem
      rcases List.mem_append.mp hmem with h | h
      · exact (hdisjL' y h y (List.mem_append.mpr (.inl hy))) rfl
      · exact (hdisjCI y hy y h) rfl
    have hxcr' : xc ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children) := hdisjCRF xc hxcC
    obtain ⟨hAch, hBch, hCch, hDch⟩ := ihChild hndC
    obtain ⟨_, hBr, hCr', hDr'⟩ := ihTail (ℓ + 1) Term.one (fun y hy => absurd rfl hy) hndT
    have hmr : ∀ x, occurs x m ≠ 0 →
        x ∈ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ∨
        (∀ e ∈ childEdges (shiftChildrenN (ℓ + 1) children), e.1 ≠ x ∧ e.2 ≠ x) := by
      intro x hx
      rcases hm x hx with hmem | havoid
      · rw [List.map_cons] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · have hxl : x = ℓ := h
          refine .inr (fun e he => ?_)
          have hn := mem_edgeNames_of_mem he
          constructor
          · intro hh
            exact hℓr ((hh.trans hxl) ▸ hCr'.subset hn.1)
          · intro hh
            exact hℓr ((hh.trans hxl) ▸ hCr'.subset hn.2)
        · exact .inl h
      · refine .inr (fun e he => havoid e ?_)
        rw [childEdges_cons]
        exact List.mem_cons_of_mem _ (List.mem_append.mpr (.inr he))
    obtain ⟨hAr, _, _, _⟩ := ihTail (ℓ + 1) m hmr hndT
    refine ⟨children_cons_assemble (xc := xc)
      (by rw [Tree.flattenAt_node, Tree.flatten_node]) rfl
      (treeChans_eq_tail_node (Chan.var_Chan xc) mc msc nsc)
      hAr hAch ?_ hBch
      (fun y hy => hCr'.subset hy) (fun y hy => hCch.subset hy)
      hDch hℓr hℓcC hxcr' hndC hdisjCRF, ?_, ?_, ?_⟩
    · intro b hb x hx
      rcases List.mem_cons.mp hb with rfl | hb
      · rcases hm x hx with hmem | havoid
        · rw [List.map_cons] at hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact .inl h
          · exact .inr (.inl (edgeRen_lt_of_mem_names (labels_mem_edgeNames h)))
        · exact .inr (.inr havoid)
      · exact .inr (.inl (edgeRen_lt_of_mem_names (hDr' x (hBr b hb x hx))))
    · intro b hb x hx
      rw [childBodies_cons] at hb
      rw [List.map_cons, childInteriors_cons]
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl (hBch b hb x hx))))
      · rcases List.mem_append.mp (hBr b hb x hx) with h | h
        · exact List.mem_append.mpr (.inl (List.mem_cons_of_mem _ h))
        · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr h)))
    · rw [childEdges_cons, edgeNames_cons, edgeNames_append, List.map_cons,
        childInteriors_cons, treeChans_eq_tail_node]
      obtain ⟨w, pw, sw⟩ := List.Subperm.append hCch hCr'
      refine List.Subperm.trans
        ⟨chanIndex (Chan.var_Chan ℓ) :: childChan (Tree.node (Chan.var_Chan xc) mc msc nsc) :: w,
          (pw.cons _).cons _, (sw.cons₂ _).cons₂ _⟩
        (List.Perm.subperm ?_)
      refine List.Perm.cons _ ?_
      refine List.Perm.trans (List.Perm.cons _ ?_) List.perm_middle.symm
      exact List.perm_append_comm_assoc _ _ _
    · intro y hy
      rw [List.map_cons, childInteriors_cons] at hy
      rw [childEdges_cons, edgeNames_cons]
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          rw [edgeNames_append]
          exact List.mem_append.mpr (.inr (hDr' y (List.mem_append.mpr (.inl hy))))
      · rcases List.mem_append.mp hy with hy | hy
        · rw [treeChans_eq_tail_node] at hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
            rw [edgeNames_append]
            exact List.mem_append.mpr (.inl (hDch y hy))
        · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          rw [edgeNames_append]
          exact List.mem_append.mpr (.inr (hDr' y (List.mem_append.mpr (.inr hy))))
  case atParent =>
    intro Θ r A children _ ih ℓ m hm hnd
    rw [shiftChildrenN_shiftChildren] at hm hnd ⊢
    exact ih (ℓ + 1) m hm hnd
  case atNone =>
    intro Θ x r A children _ ih ℓ m hm hnd
    rw [shiftChildrenN_shiftChildren] at hm hnd ⊢
    exact ih (ℓ + 1) m hm hnd
  case atOne =>
    intro Θ x r A r0 A0 child children hchild hrest ihChild ihTail ℓ m hm hnd
    rw [shiftChildrenN_one_cons] at hm hnd ⊢
    cases child with
    | root mc msc nsc => cases hchild
    | node d mc msc nsc =>
    cases d with
    | var_Chan xc =>
    rw [List.map_cons, childInteriors_cons] at hnd
    obtain ⟨hℓbig, hndbig⟩ := List.nodup_cons.mp hnd
    obtain ⟨hndL', hndCX, hdisjL'⟩ := List.nodup_append.mp hndbig
    obtain ⟨hndC, hndI', hdisjCI⟩ := List.nodup_append.mp hndCX
    have hndT : ((shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children)).Nodup := by
      rw [List.nodup_append]
      exact ⟨hndL', hndI', fun a ha b hb => hdisjL' a ha b (List.mem_append.mpr (.inr hb))⟩
    have hℓr : ℓ ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children) := by
      intro hmem
      refine hℓbig ?_
      rcases List.mem_append.mp hmem with h | h
      · exact List.mem_append.mpr (.inl h)
      · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr h)))
    have hℓcC : ℓ ∉ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc) := by
      intro hmem
      exact hℓbig (List.mem_append.mpr (.inr (List.mem_append.mpr (.inl hmem))))
    have hxcC : xc ∈ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc) := by
      rw [treeChans_node]
      exact List.mem_cons_self ..
    have hdisjCRF : ∀ y ∈ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc),
        y ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
          childInteriors (shiftChildrenN (ℓ + 1) children) := by
      intro y hy hmem
      rcases List.mem_append.mp hmem with h | h
      · exact (hdisjL' y h y (List.mem_append.mpr (.inl hy))) rfl
      · exact (hdisjCI y hy y h) rfl
    have hxcr' : xc ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children) := hdisjCRF xc hxcC
    obtain ⟨hAch, hBch, hCch, hDch⟩ := ihChild hndC
    obtain ⟨_, hBr, hCr', hDr'⟩ := ihTail (ℓ + 1) Term.one (fun y hy => absurd rfl hy) hndT
    have hmr : ∀ x, occurs x m ≠ 0 →
        x ∈ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ∨
        (∀ e ∈ childEdges (shiftChildrenN (ℓ + 1) children), e.1 ≠ x ∧ e.2 ≠ x) := by
      intro x hx
      rcases hm x hx with hmem | havoid
      · rw [List.map_cons] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · have hxl : x = ℓ := h
          refine .inr (fun e he => ?_)
          have hn := mem_edgeNames_of_mem he
          constructor
          · intro hh
            exact hℓr ((hh.trans hxl) ▸ hCr'.subset hn.1)
          · intro hh
            exact hℓr ((hh.trans hxl) ▸ hCr'.subset hn.2)
        · exact .inl h
      · refine .inr (fun e he => havoid e ?_)
        rw [childEdges_cons]
        exact List.mem_cons_of_mem _ (List.mem_append.mpr (.inr he))
    obtain ⟨hAr, _, _, _⟩ := ihTail (ℓ + 1) m hmr hndT
    refine ⟨children_cons_assemble (xc := xc)
      (by rw [Tree.flattenAt_node, Tree.flatten_node]) rfl
      (treeChans_eq_tail_node (Chan.var_Chan xc) mc msc nsc)
      hAr hAch ?_ hBch
      (fun y hy => hCr'.subset hy) (fun y hy => hCch.subset hy)
      hDch hℓr hℓcC hxcr' hndC hdisjCRF, ?_, ?_, ?_⟩
    · intro b hb x hx
      rcases List.mem_cons.mp hb with rfl | hb
      · rcases hm x hx with hmem | havoid
        · rw [List.map_cons] at hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact .inl h
          · exact .inr (.inl (edgeRen_lt_of_mem_names (labels_mem_edgeNames h)))
        · exact .inr (.inr havoid)
      · exact .inr (.inl (edgeRen_lt_of_mem_names (hDr' x (hBr b hb x hx))))
    · intro b hb x hx
      rw [childBodies_cons] at hb
      rw [List.map_cons, childInteriors_cons]
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl (hBch b hb x hx))))
      · rcases List.mem_append.mp (hBr b hb x hx) with h | h
        · exact List.mem_append.mpr (.inl (List.mem_cons_of_mem _ h))
        · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr h)))
    · rw [childEdges_cons, edgeNames_cons, edgeNames_append, List.map_cons,
        childInteriors_cons, treeChans_eq_tail_node]
      obtain ⟨w, pw, sw⟩ := List.Subperm.append hCch hCr'
      refine List.Subperm.trans
        ⟨chanIndex (Chan.var_Chan ℓ) :: childChan (Tree.node (Chan.var_Chan xc) mc msc nsc) :: w,
          (pw.cons _).cons _, (sw.cons₂ _).cons₂ _⟩
        (List.Perm.subperm ?_)
      refine List.Perm.cons _ ?_
      refine List.Perm.trans (List.Perm.cons _ ?_) List.perm_middle.symm
      exact List.perm_append_comm_assoc _ _ _
    · intro y hy
      rw [List.map_cons, childInteriors_cons] at hy
      rw [childEdges_cons, edgeNames_cons]
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          rw [edgeNames_append]
          exact List.mem_append.mpr (.inr (hDr' y (List.mem_append.mpr (.inl hy))))
      · rcases List.mem_append.mp hy with hy | hy
        · rw [treeChans_eq_tail_node] at hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
            rw [edgeNames_append]
            exact List.mem_append.mpr (.inl (hDch y hy))
        · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          rw [edgeNames_append]
          exact List.mem_append.mpr (.inr (hDr' y (List.mem_append.mpr (.inr hy))))
  case subsNil =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn
      cases hn
    · intro b hb
      rw [subBodies_nil] at hb
      cases hb
    · rw [subEdges_nil, edgeNames_nil]
      exact List.nil_subperm
    · intro y hy
      rw [subInteriors_nil] at hy
      cases hy
  case subsCons =>
    intro tree trees htree _ ihTree ihTrees hnd
    rw [subInteriors_cons] at hnd
    obtain ⟨hnd1, hnd2, _⟩ := List.nodup_append.mp hnd
    have hTail : treeChansTail tree = treeChans tree := by
      cases htree with
      | root _ _ _ _ => rw [treeChans_eq_tail_root]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn hndn
      rcases List.mem_cons.mp hn with rfl | hn
      · obtain ⟨hA, hB, hC, hD⟩ := ihTree hndn
        exact ⟨hA, hB, fun y hy => hTail ▸ hC.subset hy,
          fun y hy => hD y (hTail.symm ▸ hy)⟩
      · exact (ihTrees hnd2).1 n hn hndn
    · intro b hb x hx
      rw [subBodies_cons] at hb
      rw [subInteriors_cons]
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append.mpr (.inl ((ihTree hnd1).2.1 b hb x hx))
      · exact List.mem_append.mpr (.inr ((ihTrees hnd2).2.1 b hb x hx))
    · rw [subEdges_cons, edgeNames_append, subInteriors_cons]
      exact List.Subperm.append (hTail ▸ (ihTree hnd1).2.2.1) (ihTrees hnd2).2.2.1
    · intro y hy
      rw [subInteriors_cons] at hy
      rw [subEdges_cons, edgeNames_append]
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append.mpr (.inl ((ihTree hnd1).2.2.2 y (hTail ▸ hy)))
      · exact List.mem_append.mpr (.inr ((ihTrees hnd2).2.2.2 y hy))

/-- The description for typed nodes (same induction, rooted at `TypedAt`). -/
private theorem tree_soup_core_at {r : Bool} {A : Term} {t : Tree} (ty : TypedAt r A t) :
    treeSoupMotive t := by
  refine TypedAt.rec
    (motive_1 := fun t _ => treeSoupMotive t)
    (motive_2 := fun r A t _ => treeSoupMotive t)
    (motive_3 := fun Θ ms _ => childSoupMotive ms)
    (motive_4 := fun Θ x r A ms _ => childSoupMotive ms)
    (motive_5 := fun ns _ => subSoupMotive ns)
    ?root ?node ?childrenNil ?childrenNone ?childrenOne ?atParent ?atNone ?atOne
    ?subsNil ?subsCons ty
  case root =>
    intro Θ m ms ns hsingle tym hch hsub ihCh ihSub hnd
    rw [treeChans_root] at hnd
    obtain ⟨hndL, hndS, hdisjLS⟩ := List.nodup_append.mp hnd
    have hmL : ∀ x, occurs x m ≠ 0 → x ∈ ms.map (fun e => chanIndex e.1) := by
      intro x hx
      refine hch.support x ?_
      rw [← TLLC.Process.dynOccursCount tym x]
      exact hx
    have hm : ∀ x, occurs x m ≠ 0 →
        x ∈ (shiftChildrenN 0 ms).map (fun e => chanIndex e.1) ∨
        (∀ e ∈ childEdges (shiftChildrenN 0 ms), e.1 ≠ x ∧ e.2 ≠ x) := by
      intro x hx
      rw [shiftChildrenN_zero]
      exact .inl (hmL x hx)
    have hndL' : ((shiftChildrenN 0 ms).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN 0 ms)).Nodup := by
      rw [shiftChildrenN_zero]
      exact hndL
    obtain ⟨hAc, hBc, hCc, hDc⟩ := ihCh 0 m hm hndL'
    rw [shiftChildrenN_zero] at hAc hBc hCc hDc
    obtain ⟨hAs, hBs, hCs, hDs⟩ := ihSub hndS
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Tree.flatten_root, flattenBody, prenex_parAll, flattenSubtrees_eq_map]
      refine ARS.conv_trans (foldl_parConfig_base_congr _ hAc) ?_
      refine ARS.conv_trans
        (foldl_edgeRen_assemble ns (childEdges ms) (m :: childBodies ms)
          ?_ hAs ?_ hndS) ?_
      · intro b hb x hx
        rcases List.mem_cons.mp hb with rfl | hb
        · exact .inl (edgeRen_lt_of_mem_names (labels_mem_edgeNames (hmL x hx)))
        · exact .inl (edgeRen_lt_of_mem_names (hDc x (hBc b hb x hx)))
      · intro y hy
        exact fun hmem => (hdisjLS y (hCc.subset hy) y hmem) rfl
      · unfold treeSoup
        rw [treeEdges_root, treeBodies_root]
        exact ARS.Conv.refl
    · intro b hb x hx
      rw [treeBodies_root] at hb
      rw [treeChans_root]
      rcases List.mem_cons.mp hb with rfl | hb
      · have hpc : TLLC.Process.pcount Θ x ≠ 0 := by
          rw [← TLLC.Process.dynOccursCount tym x]
          exact hx
        exact List.mem_append.mpr (.inl (List.mem_append.mpr
          (.inl (hch.support x hpc))))
      · rcases List.mem_append.mp hb with hb | hb
        · have := hBc b hb x hx
          rcases List.mem_append.mp this with h | h
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h)))
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
        · exact List.mem_append.mpr (.inr (hBs b hb x hx))
    · rw [treeEdges_root, edgeNames_append, treeChansTail_root]
      exact List.Subperm.append hCc hCs
    · intro y hy
      rw [treeChansTail_root] at hy
      rw [treeEdges_root, edgeNames_append]
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append.mpr (.inl (hDc y hy))
      · exact List.mem_append.mpr (.inr (hDs y hy))
  case node =>
    intro Θ x r A m ms ns hsingle hhas tym hch hsub ihCh ihSub hnd
    rw [treeChans_node] at hnd
    rw [List.nodup_cons] at hnd
    obtain ⟨hp, hnd'⟩ := hnd
    obtain ⟨hndL, hndS, hdisjLS⟩ := List.nodup_append.mp hnd'
    have hndL' : ((shiftChildrenN 0 ms).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN 0 ms)).Nodup := by
      rw [shiftChildrenN_zero]
      exact hndL
    -- extract the edge-name embedding first, with a body-free instantiation
    obtain ⟨_, _, hCc, _⟩ := ihCh 0 Term.one (fun y hy => absurd rfl hy) hndL'
    rw [shiftChildrenN_zero] at hCc
    have hm : ∀ y, occurs y m ≠ 0 →
        y ∈ (shiftChildrenN 0 ms).map (fun e => chanIndex e.1) ∨
        (∀ e ∈ childEdges (shiftChildrenN 0 ms), e.1 ≠ y ∧ e.2 ≠ y) := by
      intro y hy
      rw [shiftChildrenN_zero]
      have hpc : TLLC.Process.pcount Θ y ≠ 0 := by
        rw [← TLLC.Process.dynOccursCount tym y]
        exact hy
      rcases hch.support y hpc with rfl | hlab
      · refine .inr (fun e he => ?_)
        have hmem := mem_edgeNames_of_mem he
        constructor
        · intro h
          exact hp (List.mem_append.mpr (.inl (hCc.subset (h ▸ hmem.1))))
        · intro h
          exact hp (List.mem_append.mpr (.inl (hCc.subset (h ▸ hmem.2))))
      · exact .inl hlab
    obtain ⟨hAc, hBc, _, hDc⟩ := ihCh 0 m hm hndL'
    rw [shiftChildrenN_zero] at hAc hBc hDc
    obtain ⟨hAs, hBs, hCs, hDs⟩ := ihSub hndS
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Tree.flatten_node, flattenBody, prenex_parAll, flattenSubtrees_eq_map]
      refine ARS.conv_trans (foldl_parConfig_base_congr _ hAc) ?_
      refine ARS.conv_trans
        (foldl_edgeRen_assemble ns (childEdges ms) (m :: childBodies ms)
          ?_ hAs ?_ hndS) ?_
      · intro b hb y hy
        rcases List.mem_cons.mp hb with rfl | hb
        · have hpc : TLLC.Process.pcount Θ y ≠ 0 := by
            rw [← TLLC.Process.dynOccursCount tym y]
            exact hy
          rcases hch.support y hpc with rfl | hlab
          · refine .inr ⟨?_, ?_⟩
            · intro e he
              have hmem := mem_edgeNames_of_mem he
              constructor
              · intro h
                exact hp (List.mem_append.mpr (.inl (hCc.subset (h ▸ hmem.1))))
              · intro h
                exact hp (List.mem_append.mpr (.inl (hCc.subset (h ▸ hmem.2))))
            · intro hmem
              exact hp (List.mem_append.mpr (.inr hmem))
          · exact .inl (edgeRen_lt_of_mem_names (labels_mem_edgeNames hlab))
        · exact .inl (edgeRen_lt_of_mem_names (hDc y (hBc b hb y hy)))
      · intro y hy
        exact fun hmem => (hdisjLS y (hCc.subset hy) y hmem) rfl
      · unfold treeSoup
        rw [treeEdges_node, treeBodies_node]
        exact ARS.Conv.refl
    · intro b hb y hy
      rw [treeBodies_node] at hb
      rw [treeChans_node]
      rcases List.mem_cons.mp hb with rfl | hb
      · have hpc : TLLC.Process.pcount Θ y ≠ 0 := by
          rw [← TLLC.Process.dynOccursCount tym y]
          exact hy
        rcases hch.support y hpc with rfl | hlab
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr
            (.inl (List.mem_append.mpr (.inl hlab))))
      · rcases List.mem_append.mp hb with hb | hb
        · have := hBc b hb y hy
          rcases List.mem_append.mp this with h | h
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr
              (.inl (List.mem_append.mpr (.inl h))))
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr
              (.inl (List.mem_append.mpr (.inr h))))
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr (.inr (hBs b hb y hy)))
    · rw [treeEdges_node, edgeNames_append, treeChansTail_node]
      exact List.Subperm.append hCc hCs
    · intro y hy
      rw [treeChansTail_node] at hy
      rw [treeEdges_node, edgeNames_append]
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append.mpr (.inl (hDc y hy))
      · exact List.mem_append.mpr (.inr (hDs y hy))
  case childrenNil =>
    intro ℓ m hm hnd
    rw [shiftChildrenN_nil] at hm hnd ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [flattenChildren_nil, TLLC.Process.prenex_tm]
      unfold childSoup
      rw [childEdges_nil]
      have e : m⟨edgeRen []; (id : Nat → Nat)⟩ = m := by
        rw [tren_ext m (ξ := edgeRen []) (ζ := (id : Nat → Nat)) (fun x => rfl), tren_id]
      rw [show (m :: childBodies []).map
          (fun b => b⟨edgeRen []; (id : Nat → Nat)⟩) = [m] from by
        rw [childBodies_nil]
        simp only [List.map_cons, List.map_nil, e]]
      exact ARS.Conv.refl
    · intro b hb
      rw [childBodies_nil] at hb
      cases hb
    · rw [childEdges_nil, edgeNames_nil]
      exact List.nil_subperm
    · intro y hy
      rw [childInteriors_nil, List.map_nil] at hy
      cases hy
  case childrenNone =>
    intro Θ children _ ih ℓ m hm hnd
    rw [shiftChildrenN_shiftChildren] at hm hnd ⊢
    exact ih (ℓ + 1) m hm hnd
  case childrenOne =>
    intro Θ r A child children hchild hrest ihChild ihTail ℓ m hm hnd
    rw [shiftChildrenN_one_cons] at hm hnd ⊢
    cases child with
    | root mc msc nsc => cases hchild
    | node d mc msc nsc =>
    cases d with
    | var_Chan xc =>
    rw [List.map_cons, childInteriors_cons] at hnd
    obtain ⟨hℓbig, hndbig⟩ := List.nodup_cons.mp hnd
    obtain ⟨hndL', hndCX, hdisjL'⟩ := List.nodup_append.mp hndbig
    obtain ⟨hndC, hndI', hdisjCI⟩ := List.nodup_append.mp hndCX
    have hndT : ((shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children)).Nodup := by
      rw [List.nodup_append]
      exact ⟨hndL', hndI', fun a ha b hb => hdisjL' a ha b (List.mem_append.mpr (.inr hb))⟩
    have hℓr : ℓ ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children) := by
      intro hmem
      refine hℓbig ?_
      rcases List.mem_append.mp hmem with h | h
      · exact List.mem_append.mpr (.inl h)
      · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr h)))
    have hℓcC : ℓ ∉ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc) := by
      intro hmem
      exact hℓbig (List.mem_append.mpr (.inr (List.mem_append.mpr (.inl hmem))))
    have hxcC : xc ∈ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc) := by
      rw [treeChans_node]
      exact List.mem_cons_self ..
    have hdisjCRF : ∀ y ∈ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc),
        y ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
          childInteriors (shiftChildrenN (ℓ + 1) children) := by
      intro y hy hmem
      rcases List.mem_append.mp hmem with h | h
      · exact (hdisjL' y h y (List.mem_append.mpr (.inl hy))) rfl
      · exact (hdisjCI y hy y h) rfl
    have hxcr' : xc ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children) := hdisjCRF xc hxcC
    obtain ⟨hAch, hBch, hCch, hDch⟩ := ihChild hndC
    obtain ⟨_, hBr, hCr', hDr'⟩ := ihTail (ℓ + 1) Term.one (fun y hy => absurd rfl hy) hndT
    have hmr : ∀ x, occurs x m ≠ 0 →
        x ∈ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ∨
        (∀ e ∈ childEdges (shiftChildrenN (ℓ + 1) children), e.1 ≠ x ∧ e.2 ≠ x) := by
      intro x hx
      rcases hm x hx with hmem | havoid
      · rw [List.map_cons] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · have hxl : x = ℓ := h
          refine .inr (fun e he => ?_)
          have hn := mem_edgeNames_of_mem he
          constructor
          · intro hh
            exact hℓr ((hh.trans hxl) ▸ hCr'.subset hn.1)
          · intro hh
            exact hℓr ((hh.trans hxl) ▸ hCr'.subset hn.2)
        · exact .inl h
      · refine .inr (fun e he => havoid e ?_)
        rw [childEdges_cons]
        exact List.mem_cons_of_mem _ (List.mem_append.mpr (.inr he))
    obtain ⟨hAr, _, _, _⟩ := ihTail (ℓ + 1) m hmr hndT
    refine ⟨children_cons_assemble (xc := xc)
      (by rw [Tree.flattenAt_node, Tree.flatten_node]) rfl
      (treeChans_eq_tail_node (Chan.var_Chan xc) mc msc nsc)
      hAr hAch ?_ hBch
      (fun y hy => hCr'.subset hy) (fun y hy => hCch.subset hy)
      hDch hℓr hℓcC hxcr' hndC hdisjCRF, ?_, ?_, ?_⟩
    · intro b hb x hx
      rcases List.mem_cons.mp hb with rfl | hb
      · rcases hm x hx with hmem | havoid
        · rw [List.map_cons] at hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact .inl h
          · exact .inr (.inl (edgeRen_lt_of_mem_names (labels_mem_edgeNames h)))
        · exact .inr (.inr havoid)
      · exact .inr (.inl (edgeRen_lt_of_mem_names (hDr' x (hBr b hb x hx))))
    · intro b hb x hx
      rw [childBodies_cons] at hb
      rw [List.map_cons, childInteriors_cons]
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl (hBch b hb x hx))))
      · rcases List.mem_append.mp (hBr b hb x hx) with h | h
        · exact List.mem_append.mpr (.inl (List.mem_cons_of_mem _ h))
        · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr h)))
    · rw [childEdges_cons, edgeNames_cons, edgeNames_append, List.map_cons,
        childInteriors_cons, treeChans_eq_tail_node]
      obtain ⟨w, pw, sw⟩ := List.Subperm.append hCch hCr'
      refine List.Subperm.trans
        ⟨chanIndex (Chan.var_Chan ℓ) :: childChan (Tree.node (Chan.var_Chan xc) mc msc nsc) :: w,
          (pw.cons _).cons _, (sw.cons₂ _).cons₂ _⟩
        (List.Perm.subperm ?_)
      refine List.Perm.cons _ ?_
      refine List.Perm.trans (List.Perm.cons _ ?_) List.perm_middle.symm
      exact List.perm_append_comm_assoc _ _ _
    · intro y hy
      rw [List.map_cons, childInteriors_cons] at hy
      rw [childEdges_cons, edgeNames_cons]
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          rw [edgeNames_append]
          exact List.mem_append.mpr (.inr (hDr' y (List.mem_append.mpr (.inl hy))))
      · rcases List.mem_append.mp hy with hy | hy
        · rw [treeChans_eq_tail_node] at hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
            rw [edgeNames_append]
            exact List.mem_append.mpr (.inl (hDch y hy))
        · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          rw [edgeNames_append]
          exact List.mem_append.mpr (.inr (hDr' y (List.mem_append.mpr (.inr hy))))
  case atParent =>
    intro Θ r A children _ ih ℓ m hm hnd
    rw [shiftChildrenN_shiftChildren] at hm hnd ⊢
    exact ih (ℓ + 1) m hm hnd
  case atNone =>
    intro Θ x r A children _ ih ℓ m hm hnd
    rw [shiftChildrenN_shiftChildren] at hm hnd ⊢
    exact ih (ℓ + 1) m hm hnd
  case atOne =>
    intro Θ x r A r0 A0 child children hchild hrest ihChild ihTail ℓ m hm hnd
    rw [shiftChildrenN_one_cons] at hm hnd ⊢
    cases child with
    | root mc msc nsc => cases hchild
    | node d mc msc nsc =>
    cases d with
    | var_Chan xc =>
    rw [List.map_cons, childInteriors_cons] at hnd
    obtain ⟨hℓbig, hndbig⟩ := List.nodup_cons.mp hnd
    obtain ⟨hndL', hndCX, hdisjL'⟩ := List.nodup_append.mp hndbig
    obtain ⟨hndC, hndI', hdisjCI⟩ := List.nodup_append.mp hndCX
    have hndT : ((shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children)).Nodup := by
      rw [List.nodup_append]
      exact ⟨hndL', hndI', fun a ha b hb => hdisjL' a ha b (List.mem_append.mpr (.inr hb))⟩
    have hℓr : ℓ ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children) := by
      intro hmem
      refine hℓbig ?_
      rcases List.mem_append.mp hmem with h | h
      · exact List.mem_append.mpr (.inl h)
      · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr h)))
    have hℓcC : ℓ ∉ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc) := by
      intro hmem
      exact hℓbig (List.mem_append.mpr (.inr (List.mem_append.mpr (.inl hmem))))
    have hxcC : xc ∈ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc) := by
      rw [treeChans_node]
      exact List.mem_cons_self ..
    have hdisjCRF : ∀ y ∈ treeChans (Tree.node (Chan.var_Chan xc) mc msc nsc),
        y ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
          childInteriors (shiftChildrenN (ℓ + 1) children) := by
      intro y hy hmem
      rcases List.mem_append.mp hmem with h | h
      · exact (hdisjL' y h y (List.mem_append.mpr (.inl hy))) rfl
      · exact (hdisjCI y hy y h) rfl
    have hxcr' : xc ∉ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ++
        childInteriors (shiftChildrenN (ℓ + 1) children) := hdisjCRF xc hxcC
    obtain ⟨hAch, hBch, hCch, hDch⟩ := ihChild hndC
    obtain ⟨_, hBr, hCr', hDr'⟩ := ihTail (ℓ + 1) Term.one (fun y hy => absurd rfl hy) hndT
    have hmr : ∀ x, occurs x m ≠ 0 →
        x ∈ (shiftChildrenN (ℓ + 1) children).map (fun e => chanIndex e.1) ∨
        (∀ e ∈ childEdges (shiftChildrenN (ℓ + 1) children), e.1 ≠ x ∧ e.2 ≠ x) := by
      intro x hx
      rcases hm x hx with hmem | havoid
      · rw [List.map_cons] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · have hxl : x = ℓ := h
          refine .inr (fun e he => ?_)
          have hn := mem_edgeNames_of_mem he
          constructor
          · intro hh
            exact hℓr ((hh.trans hxl) ▸ hCr'.subset hn.1)
          · intro hh
            exact hℓr ((hh.trans hxl) ▸ hCr'.subset hn.2)
        · exact .inl h
      · refine .inr (fun e he => havoid e ?_)
        rw [childEdges_cons]
        exact List.mem_cons_of_mem _ (List.mem_append.mpr (.inr he))
    obtain ⟨hAr, _, _, _⟩ := ihTail (ℓ + 1) m hmr hndT
    refine ⟨children_cons_assemble (xc := xc)
      (by rw [Tree.flattenAt_node, Tree.flatten_node]) rfl
      (treeChans_eq_tail_node (Chan.var_Chan xc) mc msc nsc)
      hAr hAch ?_ hBch
      (fun y hy => hCr'.subset hy) (fun y hy => hCch.subset hy)
      hDch hℓr hℓcC hxcr' hndC hdisjCRF, ?_, ?_, ?_⟩
    · intro b hb x hx
      rcases List.mem_cons.mp hb with rfl | hb
      · rcases hm x hx with hmem | havoid
        · rw [List.map_cons] at hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact .inl h
          · exact .inr (.inl (edgeRen_lt_of_mem_names (labels_mem_edgeNames h)))
        · exact .inr (.inr havoid)
      · exact .inr (.inl (edgeRen_lt_of_mem_names (hDr' x (hBr b hb x hx))))
    · intro b hb x hx
      rw [childBodies_cons] at hb
      rw [List.map_cons, childInteriors_cons]
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl (hBch b hb x hx))))
      · rcases List.mem_append.mp (hBr b hb x hx) with h | h
        · exact List.mem_append.mpr (.inl (List.mem_cons_of_mem _ h))
        · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr h)))
    · rw [childEdges_cons, edgeNames_cons, edgeNames_append, List.map_cons,
        childInteriors_cons, treeChans_eq_tail_node]
      obtain ⟨w, pw, sw⟩ := List.Subperm.append hCch hCr'
      refine List.Subperm.trans
        ⟨chanIndex (Chan.var_Chan ℓ) :: childChan (Tree.node (Chan.var_Chan xc) mc msc nsc) :: w,
          (pw.cons _).cons _, (sw.cons₂ _).cons₂ _⟩
        (List.Perm.subperm ?_)
      refine List.Perm.cons _ ?_
      refine List.Perm.trans (List.Perm.cons _ ?_) List.perm_middle.symm
      exact List.perm_append_comm_assoc _ _ _
    · intro y hy
      rw [List.map_cons, childInteriors_cons] at hy
      rw [childEdges_cons, edgeNames_cons]
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          rw [edgeNames_append]
          exact List.mem_append.mpr (.inr (hDr' y (List.mem_append.mpr (.inl hy))))
      · rcases List.mem_append.mp hy with hy | hy
        · rw [treeChans_eq_tail_node] at hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
            rw [edgeNames_append]
            exact List.mem_append.mpr (.inl (hDch y hy))
        · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          rw [edgeNames_append]
          exact List.mem_append.mpr (.inr (hDr' y (List.mem_append.mpr (.inr hy))))
  case subsNil =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn
      cases hn
    · intro b hb
      rw [subBodies_nil] at hb
      cases hb
    · rw [subEdges_nil, edgeNames_nil]
      exact List.nil_subperm
    · intro y hy
      rw [subInteriors_nil] at hy
      cases hy
  case subsCons =>
    intro tree trees htree _ ihTree ihTrees hnd
    rw [subInteriors_cons] at hnd
    obtain ⟨hnd1, hnd2, _⟩ := List.nodup_append.mp hnd
    have hTail : treeChansTail tree = treeChans tree := by
      cases htree with
      | root _ _ _ _ => rw [treeChans_eq_tail_root]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn hndn
      rcases List.mem_cons.mp hn with rfl | hn
      · obtain ⟨hA, hB, hC, hD⟩ := ihTree hndn
        exact ⟨hA, hB, fun y hy => hTail ▸ hC.subset hy,
          fun y hy => hD y (hTail.symm ▸ hy)⟩
      · exact (ihTrees hnd2).1 n hn hndn
    · intro b hb x hx
      rw [subBodies_cons] at hb
      rw [subInteriors_cons]
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append.mpr (.inl ((ihTree hnd1).2.1 b hb x hx))
      · exact List.mem_append.mpr (.inr ((ihTrees hnd2).2.1 b hb x hx))
    · rw [subEdges_cons, edgeNames_append, subInteriors_cons]
      exact List.Subperm.append (hTail ▸ (ihTree hnd1).2.2.1) (ihTrees hnd2).2.2.1
    · intro y hy
      rw [subInteriors_cons] at hy
      rw [subEdges_cons, edgeNames_append]
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append.mpr (.inl ((ihTree hnd1).2.2.2 y (hTail ▸ hy)))
      · exact List.mem_append.mpr (.inr ((ihTrees hnd2).2.2.2 y hy))


/-- A duplicate-free edge list is realized by its canonical renaming. -/
private lemma edgeRen_realizes : ∀ {es : List (Nat × Nat)}, (edgeNames es).Nodup →
    ∀ p (hp : p < es.length),
      edgeRen es (es.get ⟨p, hp⟩).1 = p ∧ edgeRen es (es.get ⟨p, hp⟩).2 = p := by
  intro es
  induction es with
  | nil => intro _ p hp; exact absurd hp (by simp)
  | cons e es ih =>
      intro hnd p hp
      rw [edgeNames_cons, List.nodup_cons, List.nodup_cons] at hnd
      obtain ⟨h1, h2, hnd'⟩ := hnd
      cases p with
      | zero =>
          exact ⟨edgeRen_cons_hit (.inl rfl) es, edgeRen_cons_hit (.inr rfl) es⟩
      | succ p =>
          have hp' : p < es.length := by
            simp [List.length_cons] at hp
            omega
          have hget : (e :: es).get ⟨p + 1, hp⟩ = es.get ⟨p, hp'⟩ := rfl
          rw [hget]
          have hmem := mem_edgeNames_of_mem (List.get_mem es ⟨p, hp'⟩)
          have hne1 : e.1 ≠ (es.get ⟨p, hp'⟩).1 := by
            intro h
            exact h1 (by rw [h]; exact List.mem_cons_of_mem _ hmem.1)
          have hne1' : e.2 ≠ (es.get ⟨p, hp'⟩).1 := by
            intro h
            exact h2 (by rw [h]; exact hmem.1)
          have hne2 : e.1 ≠ (es.get ⟨p, hp'⟩).2 := by
            intro h
            exact h1 (by rw [h]; exact List.mem_cons_of_mem _ hmem.2)
          have hne2' : e.2 ≠ (es.get ⟨p, hp'⟩).2 := by
            intro h
            exact h2 (by rw [h]; exact hmem.2)
          rw [edgeRen_cons_miss hne1 hne1', edgeRen_cons_miss hne2 hne2',
            (ih hnd' p hp').1, (ih hnd' p hp').2]
          exact ⟨rfl, rfl⟩

/-- The canonical edge renaming of a valid distinct tree describes its edges. -/
lemma treeRen_edgeRen {t : Tree} (ty : Typed t) (distinct : Distinct t) :
    TreeRen (edgeRen (treeEdges t)) t := by
  have hsub : (edgeNames (treeEdges t)).Subperm (treeChansTail t) :=
    (tree_soup_core ty distinct).2.2.1
  have hchans : treeChansTail t = treeChans t := by
    cases ty with
    | root _ _ _ _ => rw [treeChans_eq_tail_root]
  have hnd : (edgeNames (treeEdges t)).Nodup := by
    obtain ⟨l, hperm, hsl⟩ := hsub
    exact hperm.nodup_iff.mp (hsl.nodup (hchans ▸ distinct))
  refine ⟨edgeRen_realizes hnd, ?_⟩
  intro x hx
  have havoid : ∀ e ∈ treeEdges t, e.1 ≠ x ∧ e.2 ≠ x := by
    intro e he
    have hmem := mem_edgeNames_of_mem he
    constructor
    · intro h
      exact hx (hchans ▸ hsub.subset (h ▸ hmem.1))
    · intro h
      exact hx (hchans ▸ hsub.subset (h ▸ hmem.2))
  rw [edgeRen_junk havoid]
  omega

/-- **Tree-soup description.** The prenex soup of a valid distinct tree is, up to the soup
equivalence, the canonical tree soup. -/
theorem tree_soup' {t : Tree} (typed : Typed t) (distinct : Distinct t) :
    ∃ σ, TreeRen σ t ∧ SoupEquiv (prenex t.flatten) (treeSoup σ t) :=
  ⟨edgeRen (treeEdges t), treeRen_edgeRen typed distinct,
    ((tree_soup_core typed) distinct).1⟩

/-- The edge names of a valid distinct tree are distinct. -/
lemma edgeNames_nodup {t : Tree} (ty : Typed t) (distinct : Distinct t) :
    (edgeNames (treeEdges t)).Nodup := by
  have hsub : (edgeNames (treeEdges t)).Subperm (treeChansTail t) :=
    (tree_soup_core ty distinct).2.2.1
  have hchans : treeChansTail t = treeChans t := by
    cases ty with
    | root _ _ _ _ => rw [treeChans_eq_tail_root]
  obtain ⟨l, hperm, hsl⟩ := hsub
  exact hperm.nodup_iff.mp (hsl.nodup (hchans ▸ distinct))

/-- The tree-soup description for typed nodes. -/
theorem tree_soup_desc_at {r : Bool} {A : Term} {t : Tree} (ty : TypedAt r A t)
    (hnd : (treeChans t).Nodup) :
    SoupEquiv (prenex t.flatten) (treeSoup (edgeRen (treeEdges t)) t) ∧
    (∀ b ∈ treeBodies t, ∀ x, occurs x b ≠ 0 → x ∈ treeChans t) ∧
    (edgeNames (treeEdges t)).Subperm (treeChansTail t) ∧
    (∀ y ∈ treeChansTail t, y ∈ edgeNames (treeEdges t)) :=
  tree_soup_core_at ty hnd

/-- The tree-soup description at the canonical renaming, with its side facts: bodies explicitly
mention only tree channels, and the edge names enumerate the channels below the node's own
endpoint. -/
theorem tree_soup_desc {t : Tree} (typed : Typed t) (distinct : Distinct t) :
    SoupEquiv (prenex t.flatten) (treeSoup (edgeRen (treeEdges t)) t) ∧
    (∀ b ∈ treeBodies t, ∀ x, occurs x b ≠ 0 → x ∈ treeChans t) ∧
    (edgeNames (treeEdges t)).Subperm (treeChansTail t) ∧
    (∀ y ∈ treeChansTail t, y ∈ edgeNames (treeEdges t)) :=
  tree_soup_core typed distinct

/-- Decompose membership in the children bodies. -/
lemma mem_childBodies : ∀ {ms : List (Chan × Tree)} {b : Term},
    b ∈ childBodies ms → ∃ c ch, (c, ch) ∈ ms ∧ b ∈ treeBodies ch := by
  intro ms
  induction ms with
  | nil => intro b hb; rw [childBodies_nil] at hb; cases hb
  | cons p ms ih =>
      obtain ⟨c, ch⟩ := p
      intro b hb
      rw [childBodies_cons] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ⟨c, ch, List.mem_cons_self .., hb⟩
      · obtain ⟨c', ch', hmem, hb'⟩ := ih hb
        exact ⟨c', ch', List.mem_cons_of_mem _ hmem, hb'⟩

/-- Decompose membership in the subtree bodies. -/
lemma mem_subBodies : ∀ {ns : List Tree} {b : Term},
    b ∈ subBodies ns → ∃ n, n ∈ ns ∧ b ∈ treeBodies n := by
  intro ns
  induction ns with
  | nil => intro b hb; rw [subBodies_nil] at hb; cases hb
  | cons n ns ih =>
      intro b hb
      rw [subBodies_cons] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ⟨n, List.mem_cons_self .., hb⟩
      · obtain ⟨n', hmem, hb'⟩ := ih hb
        exact ⟨n', List.mem_cons_of_mem _ hmem, hb'⟩

private lemma childBodies_append : ∀ (l r : List (Chan × Tree)),
    childBodies (l ++ r) = childBodies l ++ childBodies r := by
  intro l
  induction l with
  | nil => intro r; rw [List.nil_append, childBodies_nil, List.nil_append]
  | cons p l ih =>
      obtain ⟨c, ch⟩ := p
      intro r
      rw [List.cons_append, childBodies_cons, childBodies_cons, ih, List.append_assoc]

private lemma childInteriors_append : ∀ (l r : List (Chan × Tree)),
    childInteriors (l ++ r) = childInteriors l ++ childInteriors r := by
  intro l
  induction l with
  | nil => intro r; rw [List.nil_append, childInteriors_nil, List.nil_append]
  | cons p l ih =>
      obtain ⟨c, ch⟩ := p
      intro r
      rw [List.cons_append, childInteriors_cons, childInteriors_cons, ih, List.append_assoc]

private lemma subBodies_append : ∀ (l r : List Tree),
    subBodies (l ++ r) = subBodies l ++ subBodies r := by
  intro l
  induction l with
  | nil => intro r; rw [List.nil_append, subBodies_nil, List.nil_append]
  | cons n l ih =>
      intro r
      rw [List.cons_append, subBodies_cons, subBodies_cons, ih, List.append_assoc]

private lemma subInteriors_append : ∀ (l r : List Tree),
    subInteriors (l ++ r) = subInteriors l ++ subInteriors r := by
  intro l
  induction l with
  | nil => intro r; rw [List.nil_append, subInteriors_nil, List.nil_append]
  | cons n l ih =>
      intro r
      rw [List.cons_append, subInteriors_cons, subInteriors_cons, ih, List.append_assoc]

private lemma childEdges_append : ∀ (l r : List (Chan × Tree)),
    childEdges (l ++ r) = childEdges l ++ childEdges r := by
  intro l
  induction l with
  | nil => intro r; rw [List.nil_append, childEdges_nil, List.nil_append]
  | cons p l ih =>
      obtain ⟨c, ch⟩ := p
      intro r
      rw [List.cons_append, childEdges_cons, childEdges_cons, ih, ← List.append_assoc]
      rfl

private lemma subEdges_append : ∀ (l r : List Tree),
    subEdges (l ++ r) = subEdges l ++ subEdges r := by
  intro l
  induction l with
  | nil => intro r; rw [List.nil_append, subEdges_nil, List.nil_append]
  | cons n l ih =>
      intro r
      rw [List.cons_append, subEdges_cons, subEdges_cons, ih, List.append_assoc]

/-! ## Multiset views of bodies and edges

The Ex-communication and close rules reshuffle children lists (ordered insertion, merging,
occurrence splits), so the body and edge lists of a reduct are only *permutations* of the
surgically updated originals. Following the multiset view of `treeChans` in
`TLLC/Spawning/Distinct.lean`, we give permutation-invariant collectors. Edges are normalized
with `sortPair`, making the orientation flip of `nodeForward` (the fired parent-child edge
reverses direction) invisible. -/

/-- Order-normalize an edge pair. -/
def sortPair (e : Nat × Nat) : Nat × Nat := if e.1 ≤ e.2 then e else (e.2, e.1)

lemma sortPair_comm (a b : Nat) : sortPair (a, b) = sortPair (b, a) := by
  simp only [sortPair]
  split <;> split <;> simp only [Prod.mk.injEq] <;> omega

/-- Multiset of all node bodies of a tree. -/
def treeBodiesM (t : Tree) : Multiset Term := (treeBodies t : List Term)

def childBodiesM (ms : List (Chan × Tree)) : Multiset Term := (childBodies ms : List Term)

def subBodiesM (ns : List Tree) : Multiset Term := (subBodies ns : List Term)

@[simp] lemma childBodiesM_nil : childBodiesM [] = 0 := by
  rw [childBodiesM, childBodies_nil, Multiset.coe_nil]

@[simp] lemma childBodiesM_cons (c : Chan) (t : Tree) (ms : List (Chan × Tree)) :
    childBodiesM ((c, t) :: ms) = treeBodiesM t + childBodiesM ms := by
  rw [childBodiesM, childBodies_cons, ← Multiset.coe_add]
  rfl

@[simp] lemma childBodiesM_append (l r : List (Chan × Tree)) :
    childBodiesM (l ++ r) = childBodiesM l + childBodiesM r := by
  rw [childBodiesM, childBodies_append, ← Multiset.coe_add]
  rfl

lemma childBodiesM_perm {ms ms' : List (Chan × Tree)} (h : List.Perm ms ms') :
    childBodiesM ms = childBodiesM ms' :=
  Multiset.coe_eq_coe.mpr (childBodies_perm h)

@[simp] lemma subBodiesM_nil : subBodiesM [] = 0 := by
  rw [subBodiesM, subBodies_nil, Multiset.coe_nil]

@[simp] lemma subBodiesM_cons (t : Tree) (ns : List Tree) :
    subBodiesM (t :: ns) = treeBodiesM t + subBodiesM ns := by
  rw [subBodiesM, subBodies_cons, ← Multiset.coe_add]
  rfl

@[simp] lemma subBodiesM_append (l r : List Tree) :
    subBodiesM (l ++ r) = subBodiesM l + subBodiesM r := by
  rw [subBodiesM, subBodies_append, ← Multiset.coe_add]
  rfl

@[simp] lemma treeBodiesM_root (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeBodiesM (.root m ms ns) = m ::ₘ (childBodiesM ms + subBodiesM ns) := by
  rw [treeBodiesM, treeBodies_root, ← Multiset.cons_coe, ← Multiset.coe_add]
  rfl

@[simp] lemma treeBodiesM_node (d : Chan) (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeBodiesM (.node d m ms ns) = m ::ₘ (childBodiesM ms + subBodiesM ns) := by
  rw [treeBodiesM, treeBodies_node, ← Multiset.cons_coe, ← Multiset.coe_add]
  rfl

/-- Multiset of the order-normalized edges of a tree. -/
def treeEdgesM (t : Tree) : Multiset (Nat × Nat) := ((treeEdges t).map sortPair : List (Nat × Nat))

def childEdgesM (ms : List (Chan × Tree)) : Multiset (Nat × Nat) :=
  ((childEdges ms).map sortPair : List (Nat × Nat))

def subEdgesM (ns : List Tree) : Multiset (Nat × Nat) :=
  ((subEdges ns).map sortPair : List (Nat × Nat))

@[simp] lemma childEdgesM_nil : childEdgesM [] = 0 := by
  rw [childEdgesM, childEdges_nil, List.map_nil, Multiset.coe_nil]

@[simp] lemma childEdgesM_cons (c : Chan) (t : Tree) (ms : List (Chan × Tree)) :
    childEdgesM ((c, t) :: ms) =
      sortPair (chanIndex c, childChan t) ::ₘ (treeEdgesM t + childEdgesM ms) := by
  rw [childEdgesM, childEdges_cons, List.map_cons, List.map_append, ← Multiset.cons_coe,
    ← Multiset.coe_add]
  rfl

@[simp] lemma childEdgesM_append (l r : List (Chan × Tree)) :
    childEdgesM (l ++ r) = childEdgesM l + childEdgesM r := by
  rw [childEdgesM, childEdges_append, List.map_append, ← Multiset.coe_add]
  rfl

lemma childEdgesM_perm {ms ms' : List (Chan × Tree)} (h : List.Perm ms ms') :
    childEdgesM ms = childEdgesM ms' :=
  Multiset.coe_eq_coe.mpr ((childEdges_perm h).map _)

@[simp] lemma subEdgesM_nil : subEdgesM [] = 0 := by
  rw [subEdgesM, subEdges_nil, List.map_nil, Multiset.coe_nil]

@[simp] lemma subEdgesM_cons (t : Tree) (ns : List Tree) :
    subEdgesM (t :: ns) = treeEdgesM t + subEdgesM ns := by
  rw [subEdgesM, subEdges_cons, List.map_append, ← Multiset.coe_add]
  rfl

@[simp] lemma subEdgesM_append (l r : List Tree) :
    subEdgesM (l ++ r) = subEdgesM l + subEdgesM r := by
  rw [subEdgesM, subEdges_append, List.map_append, ← Multiset.coe_add]
  rfl

@[simp] lemma treeEdgesM_root (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeEdgesM (.root m ms ns) = childEdgesM ms + subEdgesM ns := by
  rw [treeEdgesM, treeEdges_root, List.map_append, ← Multiset.coe_add]
  rfl

@[simp] lemma treeEdgesM_node (d : Chan) (m : Term) (ms : List (Chan × Tree)) (ns : List Tree) :
    treeEdgesM (.node d m ms ns) = childEdgesM ms + subEdgesM ns := by
  rw [treeEdgesM, treeEdges_node, List.map_append, ← Multiset.coe_add]
  rfl

/-! ### The reshuffle operations, in the multiset views -/

lemma childBodiesM_insertChild (c : Chan) (t : Tree) (ms : List (Chan × Tree)) :
    childBodiesM (insertChild c t ms) = treeBodiesM t + childBodiesM ms := by
  rw [childBodiesM_perm (insertChild_perm c t ms), childBodiesM_cons]

lemma childBodiesM_mergeChildren (extra base : List (Chan × Tree)) :
    childBodiesM (mergeChildren extra base) = childBodiesM extra + childBodiesM base := by
  rw [childBodiesM_perm (mergeChildren_perm extra base), childBodiesM_append]

lemma childBodiesM_split (v : Term) (ms : List (Chan × Tree)) :
    childBodiesM (splitChildrenByTerm v ms).1 + childBodiesM (splitChildrenByTerm v ms).2 =
      childBodiesM ms := by
  rw [← childBodiesM_append, childBodiesM_perm (splitChildren_perm v ms)]

lemma childEdgesM_insertChild (c : Chan) (t : Tree) (ms : List (Chan × Tree)) :
    childEdgesM (insertChild c t ms) =
      sortPair (chanIndex c, childChan t) ::ₘ (treeEdgesM t + childEdgesM ms) := by
  rw [childEdgesM_perm (insertChild_perm c t ms), childEdgesM_cons]

lemma childEdgesM_mergeChildren (extra base : List (Chan × Tree)) :
    childEdgesM (mergeChildren extra base) = childEdgesM extra + childEdgesM base := by
  rw [childEdgesM_perm (mergeChildren_perm extra base), childEdgesM_append]

lemma childEdgesM_split (v : Term) (ms : List (Chan × Tree)) :
    childEdgesM (splitChildrenByTerm v ms).1 + childEdgesM (splitChildrenByTerm v ms).2 =
      childEdgesM ms := by
  rw [← childEdgesM_append, childEdgesM_perm (splitChildren_perm v ms)]

/-- Locate the constructor of an edge index inside a children list: either it is the
parent-child edge of one of the entries, or it lies inside an entry's subtree. -/
private lemma childEdges_locate : ∀ (ms : List (Chan × Tree)) {e : Nat} {c d : Nat},
    getElem? (childEdges ms) e = some (c, d) →
    (∃ (l : List (Chan × Tree)) (ch : Tree) (r : List (Chan × Tree)),
      ms = l ++ (Chan.var_Chan c, ch) :: r ∧ d = childChan ch) ∨
    (∃ (l : List (Chan × Tree)) (c₀ : Chan) (ch : Tree) (r : List (Chan × Tree)) (e' : Nat),
      ms = l ++ (c₀, ch) :: r ∧ getElem? (treeEdges ch) e' = some (c, d) ∧
      treeMeasure ch ≤ childMeasure ms) := by
  intro ms
  induction ms with
  | nil => intro e c d h; rw [childEdges_nil] at h; exact absurd h (by simp)
  | cons p ms ih =>
      obtain ⟨c₀, ch⟩ := p
      intro e c d h
      rw [childEdges_cons] at h
      cases e with
      | zero =>
          rw [List.getElem?_cons_zero] at h
          obtain h' := Option.some.inj h
          obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ h'
          cases c₀ with
          | var_Chan x =>
              refine .inl ⟨[], ch, ms, ?_, h2.symm⟩
              rw [List.nil_append]
              have hx : x = c := h1
              rw [hx]
      | succ e =>
          rw [List.getElem?_cons_succ] at h
          rcases getElem?_append_split h with ⟨hlt, h'⟩ | ⟨hge, h'⟩
          · refine .inr ⟨[], c₀, ch, ms, e, rfl, h', ?_⟩
            simp only [childMeasure]
            omega
          · rcases ih h' with ⟨l, ch', r, rfl, hd⟩ | ⟨l, c₁, ch', r, e', rfl, h'', hmeas⟩
            · exact .inl ⟨(c₀, ch) :: l, ch', r, rfl, hd⟩
            · refine .inr ⟨(c₀, ch) :: l, c₁, ch', r, e', rfl, h'', ?_⟩
              simp only [childMeasure]
              omega

/-- Locate the subtree containing an edge index of a subtree list. -/
private lemma subEdges_locate : ∀ (ns : List Tree) {e : Nat} {c d : Nat},
    getElem? (subEdges ns) e = some (c, d) →
    ∃ (l : List Tree) (n : Tree) (r : List Tree) (e' : Nat),
      ns = l ++ n :: r ∧ getElem? (treeEdges n) e' = some (c, d) ∧
      treeMeasure n ≤ subMeasure ns := by
  intro ns
  induction ns with
  | nil => intro e c d h; rw [subEdges_nil] at h; exact absurd h (by simp)
  | cons n ns ih =>
      intro e c d h
      rw [subEdges_cons] at h
      rcases getElem?_append_split h with ⟨hlt, h'⟩ | ⟨hge, h'⟩
      · refine ⟨[], n, ns, e, rfl, h', ?_⟩
        simp only [subMeasure]
        omega
      · obtain ⟨l, n', r, e', rfl, h'', hmeas⟩ := ih h'
        refine ⟨n :: l, n', r, e', rfl, h'', ?_⟩
        simp only [subMeasure]
        omega

/-- Only a node's own body can explicitly hold its parent endpoint. -/
lemma parentName_unique {r : Bool} {A : Term} {dc : Chan} {m : Term}
    {ms : List (Chan × Tree)} {ns : List Tree}
    (ty : TypedAt r A (.node dc m ms ns))
    (hnd : (treeChans (.node dc m ms ns)).Nodup) :
    ∀ x b, getElem? (treeBodies (.node dc m ms ns)) x = some b →
      occurs (chanIndex dc) b ≠ 0 → x = 0 := by
  intro x b hx hocc
  cases x with
  | zero => rfl
  | succ x =>
      exfalso
      rw [treeBodies_node, List.getElem?_cons_succ] at hx
      rw [treeChans_node, List.nodup_cons] at hnd
      obtain ⟨hhead, hnd'⟩ := hnd
      have hbmem : b ∈ childBodies ms ++ subBodies ns := List.mem_of_getElem? hx
      cases ty with
      | @node Θ xp rp Ap _ _ _ hsingle hhas tym hch hsub =>
      rcases List.mem_append.mp hbmem with hb | hb
      · obtain ⟨c, ch, hmem, hb'⟩ := mem_childBodies hb
        obtain ⟨rc, Ac, hty⟩ := hch.typedAt_of_mem hmem
        have hndc : (treeChans ch).Nodup :=
          (((treeChans_sublist_childInteriors hmem).trans
            ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))).nodup hnd')
        have hB := (tree_soup_desc_at hty hndc).2.1 b hb' _ hocc
        refine hhead ?_
        exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr
          ((treeChans_sublist_childInteriors hmem).subset hB))))
      · obtain ⟨n, hmem, hb'⟩ := mem_subBodies hb
        obtain hty := hsub.typed_of_mem hmem
        have hndn : (treeChans n).Nodup :=
          ((treeChans_sublist_subInteriors hmem).trans
            (List.sublist_append_right _ _)).nodup hnd'
        have hB := (tree_soup_desc hty hndn).2.1 b hb' _ hocc
        refine hhead ?_
        exact List.mem_append.mpr (.inr
          ((treeChans_sublist_subInteriors hmem).subset hB))

/-- Only the owning node's body can explicitly hold one of its child labels (root form). -/
lemma labelName_unique_root {m : Term} {ms : List (Chan × Tree)} {ns : List Tree}
    (ty : Typed (.root m ms ns)) (hnd : (treeChans (.root m ms ns)).Nodup)
    {c : Chan} {ch : Tree} (hmem : (c, ch) ∈ ms) :
    ∀ x b, getElem? (treeBodies (.root m ms ns)) x = some b →
      occurs (chanIndex c) b ≠ 0 → x = 0 := by
  intro x b hx hocc
  cases x with
  | zero => rfl
  | succ x =>
      exfalso
      rw [treeBodies_root, List.getElem?_cons_succ] at hx
      rw [treeChans_root] at hnd
      obtain ⟨hndLI, hndS, hdisjS⟩ := List.nodup_append.mp hnd
      obtain ⟨hndL, hndI, hdisjLI⟩ := List.nodup_append.mp hndLI
      have hlab : chanIndex c ∈ ms.map (fun e => chanIndex e.1) :=
        List.mem_map.mpr ⟨(c, ch), hmem, rfl⟩
      have hbmem : b ∈ childBodies ms ++ subBodies ns := List.mem_of_getElem? hx
      cases ty with
      | @root Θ _ _ _ hsingle tym hch hsub =>
      rcases List.mem_append.mp hbmem with hb | hb
      · obtain ⟨c', ch', hmem', hb'⟩ := mem_childBodies hb
        obtain ⟨rc, Ac, hty⟩ := hch.typedAt_of_mem hmem'
        have hndc : (treeChans ch').Nodup :=
          ((treeChans_sublist_childInteriors hmem').nodup hndI)
        have hB := (tree_soup_desc_at hty hndc).2.1 b hb' _ hocc
        exact (hdisjLI _ hlab _
          ((treeChans_sublist_childInteriors hmem').subset hB)) rfl
      · obtain ⟨n, hmem', hb'⟩ := mem_subBodies hb
        have hty := hsub.typed_of_mem hmem'
        have hndn : (treeChans n).Nodup :=
          ((treeChans_sublist_subInteriors hmem').nodup hndS)
        have hB := (tree_soup_desc hty hndn).2.1 b hb' _ hocc
        exact (hdisjS _ (List.mem_append.mpr (.inl hlab)) _
          ((treeChans_sublist_subInteriors hmem').subset hB)) rfl

/-- Only the owning node's body can explicitly hold one of its child labels (node form). -/
lemma labelName_unique_node {dc : Chan} {m : Term} {ms : List (Chan × Tree)} {ns : List Tree}
    {r : Bool} {A : Term}
    (ty : TypedAt r A (.node dc m ms ns)) (hnd : (treeChans (.node dc m ms ns)).Nodup)
    {c : Chan} {ch : Tree} (hmem : (c, ch) ∈ ms) :
    ∀ x b, getElem? (treeBodies (.node dc m ms ns)) x = some b →
      occurs (chanIndex c) b ≠ 0 → x = 0 := by
  intro x b hx hocc
  cases x with
  | zero => rfl
  | succ x =>
      exfalso
      rw [treeBodies_node, List.getElem?_cons_succ] at hx
      rw [treeChans_node, List.nodup_cons] at hnd
      obtain ⟨_, hnd'⟩ := hnd
      obtain ⟨hndLI, hndS, hdisjS⟩ := List.nodup_append.mp hnd'
      obtain ⟨hndL, hndI, hdisjLI⟩ := List.nodup_append.mp hndLI
      have hlab : chanIndex c ∈ ms.map (fun e => chanIndex e.1) :=
        List.mem_map.mpr ⟨(c, ch), hmem, rfl⟩
      have hbmem : b ∈ childBodies ms ++ subBodies ns := List.mem_of_getElem? hx
      cases ty with
      | @node Θ xp rp Ap _ _ _ hsingle hhas tym hch hsub =>
      rcases List.mem_append.mp hbmem with hb | hb
      · obtain ⟨c', ch', hmem', hb'⟩ := mem_childBodies hb
        obtain ⟨rc, Ac, hty⟩ := hch.typedAt_of_mem hmem'
        have hndc : (treeChans ch').Nodup :=
          ((treeChans_sublist_childInteriors hmem').nodup hndI)
        have hB := (tree_soup_desc_at hty hndc).2.1 b hb' _ hocc
        exact (hdisjLI _ hlab _
          ((treeChans_sublist_childInteriors hmem').subset hB)) rfl
      · obtain ⟨n, hmem', hb'⟩ := mem_subBodies hb
        have hty := hsub.typed_of_mem hmem'
        have hndn : (treeChans n).Nodup :=
          ((treeChans_sublist_subInteriors hmem').nodup hndS)
        have hB := (tree_soup_desc hty hndn).2.1 b hb' _ hocc
        exact (hdisjS _ (List.mem_append.mpr (.inl hlab)) _
          ((treeChans_sublist_subInteriors hmem').subset hB)) rfl

/-- Index arithmetic: the head of a middle block in the assembled bodies list. -/
private lemma getElem?_cons_append_block {x b : Term} {L B R S : List Term}
    (hB : getElem? B 0 = some b) :
    getElem? (x :: ((L ++ (B ++ R)) ++ S)) (1 + L.length) = some b := by
  rw [show 1 + L.length = L.length + 1 from by omega, List.getElem?_cons_succ]
  have hpos : 0 < B.length := by
    cases B with
    | nil => exact absurd hB (by simp)
    | cons _ _ => simp
  have h1 : L.length < (L ++ (B ++ R)).length := by
    rw [List.length_append, List.length_append]
    omega
  rw [List.getElem?_append_left h1,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_append_left hpos]
  exact hB

private lemma treeMeasure_le_childMeasure' {c : Chan} {child : Tree} :
    ∀ {ms : List (Chan × Tree)}, (c, child) ∈ ms → treeMeasure child ≤ childMeasure ms
  | (c', t') :: ms, h => by
      rcases List.mem_cons.mp h with he | h
      · cases he
        simp only [childMeasure]
        omega
      · have := treeMeasure_le_childMeasure' h
        simp only [childMeasure]
        omega

private lemma treeMeasure_le_subMeasure' {sub : Tree} :
    ∀ {ns : List Tree}, sub ∈ ns → treeMeasure sub ≤ subMeasure ns
  | t' :: ns, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [subMeasure]
        omega
      · have := treeMeasure_le_subMeasure' h
        simp only [subMeasure]
        omega

/-- Index arithmetic: reading inside the subtree block of the assembled bodies list. -/
private lemma getElem?_sub_block_eq {x : Term} {CB SL B SR : List Term} {k : Nat}
    (hk : k < B.length) :
    getElem? (x :: (CB ++ (SL ++ (B ++ SR)))) (1 + CB.length + SL.length + k) =
      getElem? B k := by
  rw [show 1 + CB.length + SL.length + k = (CB.length + (SL.length + k)) + 1 from by omega,
    List.getElem?_cons_succ,
    List.getElem?_append_right (by omega),
    show CB.length + (SL.length + k) - CB.length = SL.length + k from by omega,
    List.getElem?_append_right (by omega),
    show SL.length + k - SL.length = k from by omega,
    List.getElem?_append_left hk]

/-- Index arithmetic: writing inside the subtree block of the assembled bodies list. -/
private lemma set_sub_block_eq {x : Term} {CB SL B SR : List Term} {k : Nat}
    (hk : k < B.length) (a : Term) :
    (x :: (CB ++ (SL ++ (B ++ SR)))).set (1 + CB.length + SL.length + k) a =
      x :: (CB ++ (SL ++ (B.set k a ++ SR))) := by
  rw [show 1 + CB.length + SL.length + k = (CB.length + (SL.length + k)) + 1 from by omega,
    List.set_cons_succ,
    set_append_ge _ (by omega) _,
    show CB.length + (SL.length + k) - CB.length = SL.length + k from by omega,
    set_append_ge _ (by omega) _,
    show SL.length + k - SL.length = k from by omega,
    set_append_lt _ hk _]

/-- Index arithmetic: reading inside a middle block of the assembled bodies list. -/
private lemma getElem?_block_eq {x : Term} {L B R S : List Term} {k : Nat}
    (hk : k < B.length) :
    getElem? (x :: ((L ++ (B ++ R)) ++ S)) (1 + L.length + k) = getElem? B k := by
  rw [show 1 + L.length + k = (L.length + k) + 1 from by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by
      rw [List.length_append, List.length_append]
      omega),
    List.getElem?_append_right (by omega),
    show L.length + k - L.length = k from by omega,
    List.getElem?_append_left hk]

/-- Index arithmetic: writing inside a middle block of the assembled bodies list. -/
private lemma set_block_eq {x : Term} {L B R S : List Term} {k : Nat}
    (hk : k < B.length) (a : Term) :
    (x :: ((L ++ (B ++ R)) ++ S)).set (1 + L.length + k) a =
      x :: ((L ++ (B.set k a ++ R)) ++ S) := by
  rw [show 1 + L.length + k = (L.length + k) + 1 from by omega, List.set_cons_succ,
    set_append_lt _ (by
      rw [List.length_append, List.length_append]
      omega) _,
    set_append_ge _ (by omega) _,
    show L.length + k - L.length = k from by omega,
    set_append_lt _ hk _]

/-- The canonical renaming hits an index only through a name of that edge. -/
private lemma edgeRen_hit_inv : ∀ {es : List (Nat × Nat)} {x : Nat},
    edgeRen es x < es.length →
    ∃ ed, getElem? es (edgeRen es x) = some ed ∧ (ed.1 = x ∨ ed.2 = x) := by
  intro es
  induction es with
  | nil => intro x h; simp at h
  | cons e es ih =>
      intro x h
      by_cases hx : e.1 = x ∨ e.2 = x
      · rw [edgeRen_cons_hit hx]
        exact ⟨e, List.getElem?_cons_zero, hx⟩
      · push Not at hx
        rw [edgeRen_cons_miss hx.1 hx.2] at h ⊢
        rw [List.length_cons] at h
        obtain ⟨ed, hed, hx'⟩ := ih (x := x) (by omega)
        exact ⟨ed, by rw [List.getElem?_cons_succ]; exact hed, hx'⟩

/-- With pairwise-distinct edge names, a name determines its edge pair. -/
private lemma edge_pair_unique : ∀ {es : List (Nat × Nat)}, (edgeNames es).Nodup →
    ∀ {p q : Nat} {ed ed' : Nat × Nat} {x : Nat},
    getElem? es p = some ed → getElem? es q = some ed' →
    (ed.1 = x ∨ ed.2 = x) → (ed'.1 = x ∨ ed'.2 = x) → p = q := by
  intro es
  induction es with
  | nil => intro _ p q ed ed' x hp _ _ _; exact absurd hp (by simp)
  | cons e es ih =>
      intro hnd p q ed ed' x hp hq hx hx'
      rw [edgeNames_cons, List.nodup_cons] at hnd
      obtain ⟨h1, hnd2⟩ := hnd
      rw [List.nodup_cons] at hnd2
      obtain ⟨h2, hnd3⟩ := hnd2
      cases p with
      | zero =>
          cases q with
          | zero => rfl
          | succ q =>
              exfalso
              rw [List.getElem?_cons_zero] at hp
              obtain rfl := Option.some.inj hp
              rw [List.getElem?_cons_succ] at hq
              have hmem := mem_edgeNames_of_mem (List.mem_of_getElem? hq)
              rcases hx with rfl | rfl
              · rcases hx' with h | h
                · exact h1 (List.mem_cons_of_mem _ (h ▸ hmem.1))
                · exact h1 (List.mem_cons_of_mem _ (h ▸ hmem.2))
              · rcases hx' with h | h
                · exact h2 (h ▸ hmem.1)
                · exact h2 (h ▸ hmem.2)
      | succ p =>
          cases q with
          | zero =>
              exfalso
              rw [List.getElem?_cons_zero] at hq
              obtain rfl := Option.some.inj hq
              rw [List.getElem?_cons_succ] at hp
              have hmem := mem_edgeNames_of_mem (List.mem_of_getElem? hp)
              rcases hx' with rfl | rfl
              · rcases hx with h | h
                · exact h1 (List.mem_cons_of_mem _ (h ▸ hmem.1))
                · exact h1 (List.mem_cons_of_mem _ (h ▸ hmem.2))
              · rcases hx with h | h
                · exact h2 (h ▸ hmem.1)
                · exact h2 (h ▸ hmem.2)
          | succ q =>
              rw [List.getElem?_cons_succ] at hp hq
              rw [ih hnd3 hp hq hx hx']

/-- The index bijection induced by a permutation of the edge list. -/
private def edgePermRen (es es' : List (Nat × Nat)) (p : Nat) : Nat :=
  if p < es.length then edgeRen es' (es.getD p (0, 0)).1 else p

private lemma getD_of_lt {es : List (Nat × Nat)} {p : Nat} (hp : p < es.length) :
    getElem? es p = some (es.getD p (0, 0)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  rfl

/-- Both names of a pair in a duplicate-free edge list rename to the same index. -/
private lemma edgeRen_pair_eq {es : List (Nat × Nat)} (hnd : (edgeNames es).Nodup)
    {ed : Nat × Nat} (hmem : ed ∈ es) : edgeRen es ed.1 = edgeRen es ed.2 := by
  have hn := mem_edgeNames_of_mem hmem
  have h1 := edgeRen_lt_of_mem_names hn.1
  have h2 := edgeRen_lt_of_mem_names hn.2
  obtain ⟨ed1, hed1, hx1⟩ := edgeRen_hit_inv h1
  obtain ⟨ed2, hed2, hx2⟩ := edgeRen_hit_inv h2
  obtain ⟨pm, hpm⟩ := List.getElem?_of_mem hmem
  have e1 := edge_pair_unique hnd hed1 hpm hx1 (.inl rfl)
  have e2 := edge_pair_unique hnd hed2 hpm hx2 (.inr rfl)
  rw [e1, e2]

/-- The induced index map is inverted by the reverse map. -/
private lemma edgePermRen_inv {es es' : List (Nat × Nat)} (hperm : es.Perm es')
    (hnd : (edgeNames es).Nodup) (hnd' : (edgeNames es').Nodup) :
    ∀ p, edgePermRen es' es (edgePermRen es es' p) = p := by
  intro p
  unfold edgePermRen
  by_cases hp : p < es.length
  · rw [if_pos hp]
    have hget := getD_of_lt hp
    have hmem : es.getD p (0, 0) ∈ es := List.mem_of_getElem? hget
    have hmem' : es.getD p (0, 0) ∈ es' := hperm.subset hmem
    have hn' := mem_edgeNames_of_mem hmem'
    have hlt' : edgeRen es' (es.getD p (0, 0)).1 < es'.length :=
      edgeRen_lt_of_mem_names hn'.1
    rw [if_pos hlt']
    obtain ⟨ed', hed', hx'⟩ := edgeRen_hit_inv hlt'
    have hgetD' : es'.getD (edgeRen es' (es.getD p (0, 0)).1) (0, 0) = ed' := by
      have := getD_of_lt hlt'
      rw [hed'] at this
      exact (Option.some.inj this).symm
    rw [hgetD']
    -- ed' and the p-th edge share the name, hence are the same pair, at position p in es
    have hmemEd' : ed' ∈ es := hperm.symm.subset (List.mem_of_getElem? hed')
    obtain ⟨p₂, hp₂⟩ := List.getElem?_of_mem hmemEd'
    have hne1 : edgeRen es ed'.1 < es.length :=
      edgeRen_lt_of_mem_names (mem_edgeNames_of_mem hmemEd').1
    obtain ⟨ed₁, hed₁, hx₁⟩ := edgeRen_hit_inv hne1
    have e1 := edge_pair_unique hnd hed₁ hp₂ hx₁ (.inl rfl)
    have e2 := edge_pair_unique hnd hp₂ hget hx' (.inl rfl)
    exact e1.trans e2
  · rw [if_neg hp, if_neg (by rw [← hperm.length_eq]; omega)]

/-- Re-indexing a soup along a permutation of its edge list: the canonical renamings of the two
orders agree up to the induced binder bijection at explicit names, and up to congruence at
implicit ones. -/
lemma treeSoup_reindex {es es' : List (Nat × Nat)} (hperm : es.Perm es')
    (hnd : (edgeNames es).Nodup) (hnd' : (edgeNames es').Nodup) (ts : List Term)
    (hocc : ∀ b ∈ ts, ∀ x, occurs x b ≠ 0 →
      x ∈ edgeNames es ∨ (∀ ed ∈ es, ed.1 ≠ x ∧ ed.2 ≠ x)) :
    SoupEquiv (es.length, ts.map (fun b => b⟨edgeRen es; (id : Nat → Nat)⟩))
      (es'.length, ts.map (fun b => b⟨edgeRen es'; (id : Nat → Nat)⟩)) := by
  have hlen := hperm.length_eq
  refine ARS.conv_trans (TLLC.Process.SoupEquiv.ren
    (edgePermRen es es') (edgePermRen es' es)
    (edgePermRen_inv hperm hnd hnd')
    (edgePermRen_inv (es := es') (es' := es) hperm.symm hnd' hnd)
    (fun x hx => by unfold edgePermRen; rw [if_neg (by omega)])) ?_
  · rw [tsmap_comp, show es.length = es'.length from hlen]
    refine TLLC.Process.SoupEquiv.congr (forall₂_map_rel
      (g := fun b => b⟨edgeRen es'; (id : Nat → Nat)⟩) ts (fun b hb =>
      congrTerm_cren_of_occurs' (fun x hx => ?_)))
    show edgePermRen es es' (edgeRen es x) = edgeRen es' x
    rcases hocc b hb x hx with hmem | havoid
    · have hlt := edgeRen_lt_of_mem_names hmem
      unfold edgePermRen
      rw [if_pos hlt]
      obtain ⟨ed, hed, hx'⟩ := edgeRen_hit_inv hlt
      have hgetD : es.getD (edgeRen es x) (0, 0) = ed := by
        have h := getD_of_lt hlt
        rw [hed] at h
        exact (Option.some.inj h).symm
      rw [hgetD]
      have hmemed' : ed ∈ es' := hperm.subset (List.mem_of_getElem? hed)
      rcases hx' with h | h
      · rw [h]
      · rw [edgeRen_pair_eq hnd' hmemed', h]
    · have h1 : edgeRen es x = es.length + x := edgeRen_junk havoid
      have havoid' : ∀ ed ∈ es', ed.1 ≠ x ∧ ed.2 ≠ x := fun ed hed =>
        havoid ed (hperm.symm.subset hed)
      have h2 : edgeRen es' x = es'.length + x := edgeRen_junk havoid'
      unfold edgePermRen
      rw [h1, if_neg (by omega), h2, hlen]

/-! ## Replaying a fork -/

private lemma add_around {α : Type _} (x : α) {X' X O N S : Multiset α}
    (h : X' + O = X + N) :
    (x ::ₘ (X' + S)) + O = (x ::ₘ (X + S)) + N := by
  simp only [← Multiset.singleton_add]
  calc ({x} + (X' + S)) + O = (X' + O) + ({x} + S) := by abel
    _ = (X + N) + ({x} + S) := by rw [h]
    _ = ({x} + (X + S)) + N := by abel

private lemma add_around' {α : Type _} {X' X O N S : Multiset α}
    (h : X' + O = X + N) :
    (X' + S) + O = (X + S) + N := by
  calc (X' + S) + O = (X' + O) + S := by abel
    _ = (X + N) + S := by rw [h]
    _ = (X + S) + N := by abel

private lemma add_around₂ {α : Type _} (x : α) {X' X O N S : Multiset α}
    (h : X' + O = X + N) :
    (x ::ₘ (S + X')) + O = (x ::ₘ (S + X)) + N := by
  simp only [← Multiset.singleton_add]
  calc ({x} + (S + X')) + O = (X' + O) + ({x} + S) := by abel
    _ = (X + N) + ({x} + S) := by rw [h]
    _ = ({x} + (S + X)) + N := by abel

private lemma add_around'' {α : Type _} {X' X O N S : Multiset α}
    (h : X' + O = X + N) :
    (S + X') + O = (S + X) + N := by
  calc (S + X') + O = (X' + O) + S := by abel
    _ = (X + N) + S := by rw [h]
    _ = (S + X) + N := by abel

mutual

/-- Replaying a fork of the `i`-th body on the tree, with endpoints `c`, `d` fresh for the whole
tree: fire the fork rule at the holder under the path congruences. -/
lemma bodyFork_tree : ∀ (t : Tree) {c d : Nat},
    c ∉ treeChans t → d ∉ treeChans t → c ≠ d →
    ∀ (i : Nat) (M₀ : EvalCtx) (A₀ m₀ : Term),
    getElem? (treeBodies t) i = some (M₀.eval (.fork A₀ m₀)) →
    occurs c (M₀.eval (.fork A₀ m₀)) = 0 →
    occurs d (M₀.eval (.fork A₀ m₀)) = 0 →
    ∃ t', Step t t' ∧
      treeBodiesM t' + {M₀.eval (.fork A₀ m₀)} =
        treeBodiesM t + ({M₀.eval (.pure (.chan (Chan.var_Chan c)))} +
          {m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]}) ∧
      treeEdgesM t' = treeEdgesM t + {sortPair (c, d)} ∧
      treeChansM t' = treeChansM t + ({c} + {d}) ∧
      childChan t' = childChan t
  | .root m ms ns, c, d, hc, hd, hcd, i, M₀, A₀, m₀, hi, hoc, hod => by
      rw [treeBodies_root] at hi
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hi
          obtain rfl := Option.some.inj hi
          refine ⟨.root (M₀.eval (.pure (.chan (Chan.var_Chan c))))
            (forkChildren m₀ (Chan.var_Chan c) (Chan.var_Chan d) ms) ns,
            Step.rootFork hoc hod ⟨hc, hd, hcd⟩, ?_, ?_, ?_, rfl⟩
          · simp only [treeBodiesM_root, treeBodiesM_node, forkChildren,
              childBodiesM_insertChild, subBodiesM_nil]
            rw [← childBodiesM_split m₀ ms]
            simp only [← Multiset.singleton_add]
            abel
          · simp only [treeEdgesM_root, treeEdgesM_node, forkChildren,
              childEdgesM_insertChild, subEdgesM_nil, childChan, chanIndex]
            rw [← childEdgesM_split m₀ ms]
            simp only [← Multiset.singleton_add]
            abel
          · simp only [treeChansM_root, treeChansM_node, forkChildren,
              childChansM_insertChild, subChansM_nil, chanIndex]
            rw [← childChansM_split m₀ ms]
            simp only [← Multiset.singleton_add]
            abel
      | succ i =>
          rw [List.getElem?_cons_succ] at hi
          have hcI : c ∉ childInteriors ms := fun hmem => hc (by
            rw [treeChans_root]
            exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hmem))))
          have hdI : d ∉ childInteriors ms := fun hmem => hd (by
            rw [treeChans_root]
            exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hmem))))
          have hcS : c ∉ subInteriors ns := fun hmem => hc (by
            rw [treeChans_root]
            exact List.mem_append.mpr (.inr hmem))
          have hdS : d ∉ subInteriors ns := fun hmem => hd (by
            rw [treeChans_root]
            exact List.mem_append.mpr (.inr hmem))
          rcases getElem?_append_split hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩
          · obtain ⟨l, c₀, child, child', r, rfl, stc, hch, hb, he, hchans⟩ :=
              bodyFork_children ms hcI hdI hcd i M₀ A₀ m₀ hi' hoc hod
            refine ⟨.root m (l ++ (c₀, child') :: r) ns,
              Step.rootChild stc (fun x hx hnx => ?_), ?_, ?_, ?_, rfl⟩
            · have hx' : x ∈ treeChansM child' := mem_treeChansM.mpr hx
              rw [hch] at hx'
              rcases Multiset.mem_add.mp hx' with hin | hcd'
              · exact absurd (mem_treeChansM.mp hin) hnx
              · rcases Multiset.mem_add.mp hcd' with h | h
                · rw [Multiset.mem_singleton.mp h]
                  exact hc
                · rw [Multiset.mem_singleton.mp h]
                  exact hd
            · simp only [treeBodiesM_root]
              exact add_around m hb
            · simp only [treeEdgesM_root]
              rw [he]
              abel
            · simp only [treeChansM_root]
              rw [hchans]
              abel
          · obtain ⟨l, sub, sub', r, rfl, sts, hch, hb, he, hchans⟩ :=
              bodyFork_subs ns hcS hdS hcd (i - (childBodies ms).length) M₀ A₀ m₀ hi' hoc hod
            refine ⟨.root m ms (l ++ sub' :: r),
              Step.rootSubtree sts (fun x hx hnx => ?_), ?_, ?_, ?_, rfl⟩
            · have hx' : x ∈ treeChansM sub' := mem_treeChansM.mpr hx
              rw [hch] at hx'
              rcases Multiset.mem_add.mp hx' with hin | hcd'
              · exact absurd (mem_treeChansM.mp hin) hnx
              · rcases Multiset.mem_add.mp hcd' with h | h
                · rw [Multiset.mem_singleton.mp h]
                  exact hc
                · rw [Multiset.mem_singleton.mp h]
                  exact hd
            · simp only [treeBodiesM_root]
              exact add_around₂ m hb
            · simp only [treeEdgesM_root]
              rw [he]
              abel
            · simp only [treeChansM_root]
              rw [hchans]
              abel
  | .node dc m ms ns, c, d, hc, hd, hcd, i, M₀, A₀, m₀, hi, hoc, hod => by
      rw [treeBodies_node] at hi
      cases dc with
      | var_Chan xp =>
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hi
          obtain rfl := Option.some.inj hi
          by_cases hxp : Dynamic.occurs xp m₀ = 0
          · refine ⟨.node (Chan.var_Chan xp) (M₀.eval (.pure (.chan (Chan.var_Chan c))))
              (forkChildren m₀ (Chan.var_Chan c) (Chan.var_Chan d) ms) ns,
              Step.nodeFork hoc hod hxp ⟨hc, hd, hcd⟩, ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_root, treeBodiesM_node, forkChildren,
                childBodiesM_insertChild, subBodiesM_nil]
              rw [← childBodiesM_split m₀ ms]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeEdgesM_root, treeEdgesM_node, forkChildren,
                childEdgesM_insertChild, subEdgesM_nil, childChan, chanIndex]
              rw [← childEdgesM_split m₀ ms]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeChansM_root, treeChansM_node, forkChildren,
                childChansM_insertChild, subChansM_nil, chanIndex]
              rw [← childChansM_split m₀ ms]
              simp only [← Multiset.singleton_add]
              abel
          · refine ⟨.node (Chan.var_Chan xp)
              (m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..])
              (forkForwardChildren m₀ (Chan.var_Chan c) (Chan.var_Chan d) M₀ ms ns) [],
              Step.nodeForkForward hoc hod hxp ⟨hc, hd, hcd⟩, ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_root, treeBodiesM_node, forkForwardChildren,
                childBodiesM_insertChild, subBodiesM_nil]
              rw [← childBodiesM_split m₀ ms]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeEdgesM_root, treeEdgesM_node, forkForwardChildren,
                childEdgesM_insertChild, subEdgesM_nil, childChan, chanIndex]
              rw [sortPair_comm d c]
              rw [← childEdgesM_split m₀ ms]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeChansM_root, treeChansM_node, forkForwardChildren,
                childChansM_insertChild, subChansM_nil, chanIndex]
              rw [← childChansM_split m₀ ms]
              simp only [← Multiset.singleton_add]
              abel
      | succ i =>
          rw [List.getElem?_cons_succ] at hi
          have hcI : c ∉ childInteriors ms := fun hmem => hc (by
            rw [treeChans_node]
            exact List.mem_cons_of_mem _
              (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hmem)))))
          have hdI : d ∉ childInteriors ms := fun hmem => hd (by
            rw [treeChans_node]
            exact List.mem_cons_of_mem _
              (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hmem)))))
          have hcS : c ∉ subInteriors ns := fun hmem => hc (by
            rw [treeChans_node]
            exact List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hmem)))
          have hdS : d ∉ subInteriors ns := fun hmem => hd (by
            rw [treeChans_node]
            exact List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hmem)))
          rcases getElem?_append_split hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩
          · obtain ⟨l, c₀, child, child', r, rfl, stc, hch, hb, he, hchans⟩ :=
              bodyFork_children ms hcI hdI hcd i M₀ A₀ m₀ hi' hoc hod
            refine ⟨.node (Chan.var_Chan xp) m (l ++ (c₀, child') :: r) ns,
              Step.nodeChild stc (fun x hx hnx => ?_), ?_, ?_, ?_, rfl⟩
            · have hx' : x ∈ treeChansM child' := mem_treeChansM.mpr hx
              rw [hch] at hx'
              rcases Multiset.mem_add.mp hx' with hin | hcd'
              · exact absurd (mem_treeChansM.mp hin) hnx
              · rcases Multiset.mem_add.mp hcd' with h | h
                · rw [Multiset.mem_singleton.mp h]
                  exact hc
                · rw [Multiset.mem_singleton.mp h]
                  exact hd
            · simp only [treeBodiesM_node]
              exact add_around m hb
            · simp only [treeEdgesM_node]
              rw [he]
              abel
            · simp only [treeChansM_node]
              rw [hchans]
              simp only [← Multiset.singleton_add]
              abel
          · obtain ⟨l, sub, sub', r, rfl, sts, hch, hb, he, hchans⟩ :=
              bodyFork_subs ns hcS hdS hcd (i - (childBodies ms).length) M₀ A₀ m₀ hi' hoc hod
            refine ⟨.node (Chan.var_Chan xp) m ms (l ++ sub' :: r),
              Step.nodeSubtree sts (fun x hx hnx => ?_), ?_, ?_, ?_, rfl⟩
            · have hx' : x ∈ treeChansM sub' := mem_treeChansM.mpr hx
              rw [hch] at hx'
              rcases Multiset.mem_add.mp hx' with hin | hcd'
              · exact absurd (mem_treeChansM.mp hin) hnx
              · rcases Multiset.mem_add.mp hcd' with h | h
                · rw [Multiset.mem_singleton.mp h]
                  exact hc
                · rw [Multiset.mem_singleton.mp h]
                  exact hd
            · simp only [treeBodiesM_node]
              exact add_around₂ m hb
            · simp only [treeEdgesM_node]
              rw [he]
              abel
            · simp only [treeChansM_node]
              rw [hchans]
              simp only [← Multiset.singleton_add]
              abel

/-- Replaying a fork inside a children list. -/
private lemma bodyFork_children : ∀ (ms : List (Chan × Tree)) {c d : Nat},
    c ∉ childInteriors ms → d ∉ childInteriors ms → c ≠ d →
    ∀ (i : Nat) (M₀ : EvalCtx) (A₀ m₀ : Term),
    getElem? (childBodies ms) i = some (M₀.eval (.fork A₀ m₀)) →
    occurs c (M₀.eval (.fork A₀ m₀)) = 0 →
    occurs d (M₀.eval (.fork A₀ m₀)) = 0 →
    ∃ (l : List (Chan × Tree)) (c₀ : Chan) (child child' : Tree) (r : List (Chan × Tree)),
      ms = l ++ (c₀, child) :: r ∧ Step child child' ∧
      treeChansM child' = treeChansM child + ({c} + {d}) ∧
      childBodiesM (l ++ (c₀, child') :: r) + {M₀.eval (.fork A₀ m₀)} =
        childBodiesM ms + ({M₀.eval (.pure (.chan (Chan.var_Chan c)))} +
          {m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]}) ∧
      childEdgesM (l ++ (c₀, child') :: r) = childEdgesM ms + {sortPair (c, d)} ∧
      childChansM (l ++ (c₀, child') :: r) = childChansM ms + ({c} + {d})
  | [], c, d, hcI, hdI, hcd, i, M₀, A₀, m₀, hi, hoc, hod => by
      rw [childBodies_nil] at hi
      exact absurd hi (by simp)
  | (c₀, child) :: ms, c, d, hcI, hdI, hcd, i, M₀, A₀, m₀, hi, hoc, hod => by
      rw [childBodies_cons] at hi
      have hcT : c ∉ treeChans child := fun h => hcI (by
        rw [childInteriors_cons]
        exact List.mem_append.mpr (.inl h))
      have hdT : d ∉ treeChans child := fun h => hdI (by
        rw [childInteriors_cons]
        exact List.mem_append.mpr (.inl h))
      have hcI' : c ∉ childInteriors ms := fun h => hcI (by
        rw [childInteriors_cons]
        exact List.mem_append.mpr (.inr h))
      have hdI' : d ∉ childInteriors ms := fun h => hdI (by
        rw [childInteriors_cons]
        exact List.mem_append.mpr (.inr h))
      rcases getElem?_append_split hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩
      · obtain ⟨child', stc, hb, he, hch, hcc⟩ :=
          bodyFork_tree child hcT hdT hcd i M₀ A₀ m₀ hi' hoc hod
        refine ⟨[], c₀, child, child', ms, rfl, stc, hch, ?_, ?_, ?_⟩
        · simp only [List.nil_append, childBodiesM_cons]
          exact add_around' hb
        · simp only [List.nil_append, childEdgesM_cons, hcc, he,
            ← Multiset.singleton_add]
          abel
        · simp only [List.nil_append, childChansM_cons, hch, ← Multiset.singleton_add]
          abel
      · obtain ⟨l, c₁, child₀, child₀', r, rfl, stc, hch, hb, he, hchans⟩ :=
          bodyFork_children ms hcI' hdI' hcd (i - (treeBodies child).length) M₀ A₀ m₀
            hi' hoc hod
        refine ⟨(c₀, child) :: l, c₁, child₀, child₀', r, rfl, stc, hch, ?_, ?_, ?_⟩
        · simp only [List.cons_append, childBodiesM_cons]
          exact add_around'' hb
        · simp only [List.cons_append, childEdgesM_cons, he, ← Multiset.singleton_add]
          abel
        · simp only [List.cons_append, childChansM_cons, hchans, ← Multiset.singleton_add]
          abel

/-- Replaying a fork inside a subtree list. -/
private lemma bodyFork_subs : ∀ (ns : List Tree) {c d : Nat},
    c ∉ subInteriors ns → d ∉ subInteriors ns → c ≠ d →
    ∀ (i : Nat) (M₀ : EvalCtx) (A₀ m₀ : Term),
    getElem? (subBodies ns) i = some (M₀.eval (.fork A₀ m₀)) →
    occurs c (M₀.eval (.fork A₀ m₀)) = 0 →
    occurs d (M₀.eval (.fork A₀ m₀)) = 0 →
    ∃ (l : List Tree) (sub sub' : Tree) (r : List Tree),
      ns = l ++ sub :: r ∧ Step sub sub' ∧
      treeChansM sub' = treeChansM sub + ({c} + {d}) ∧
      subBodiesM (l ++ sub' :: r) + {M₀.eval (.fork A₀ m₀)} =
        subBodiesM ns + ({M₀.eval (.pure (.chan (Chan.var_Chan c)))} +
          {m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]}) ∧
      subEdgesM (l ++ sub' :: r) = subEdgesM ns + {sortPair (c, d)} ∧
      subChansM (l ++ sub' :: r) = subChansM ns + ({c} + {d})
  | [], c, d, hcS, hdS, hcd, i, M₀, A₀, m₀, hi, hoc, hod => by
      rw [subBodies_nil] at hi
      exact absurd hi (by simp)
  | sub :: ns, c, d, hcS, hdS, hcd, i, M₀, A₀, m₀, hi, hoc, hod => by
      rw [subBodies_cons] at hi
      have hcT : c ∉ treeChans sub := fun h => hcS (by
        rw [subInteriors_cons]
        exact List.mem_append.mpr (.inl h))
      have hdT : d ∉ treeChans sub := fun h => hdS (by
        rw [subInteriors_cons]
        exact List.mem_append.mpr (.inl h))
      have hcS' : c ∉ subInteriors ns := fun h => hcS (by
        rw [subInteriors_cons]
        exact List.mem_append.mpr (.inr h))
      have hdS' : d ∉ subInteriors ns := fun h => hdS (by
        rw [subInteriors_cons]
        exact List.mem_append.mpr (.inr h))
      rcases getElem?_append_split hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩
      · obtain ⟨sub', sts, hb, he, hch, _⟩ :=
          bodyFork_tree sub hcT hdT hcd i M₀ A₀ m₀ hi' hoc hod
        refine ⟨[], sub, sub', ns, rfl, sts, hch, ?_, ?_, ?_⟩
        · simp only [List.nil_append, subBodiesM_cons]
          exact add_around' hb
        · simp only [List.nil_append, subEdgesM_cons, he]
          abel
        · simp only [List.nil_append, subChansM_cons, hch]
          abel
      · obtain ⟨l, sub₀, sub₀', r, rfl, sts, hch, hb, he, hchans⟩ :=
          bodyFork_subs ns hcS' hdS' hcd (i - (treeBodies sub).length) M₀ A₀ m₀ hi' hoc hod
        refine ⟨sub :: l, sub₀, sub₀', r, rfl, sts, hch, ?_, ?_, ?_⟩
        · simp only [List.cons_append, subBodiesM_cons]
          exact add_around'' hb
        · simp only [List.cons_append, subEdgesM_cons, he]
          abel
        · simp only [List.cons_append, subChansM_cons, hchans]
          abel

end

/-! ## Reindexing across an unordered-edge-multiset-preserving surgery -/

/-- Lift a permutation of a mapped list back through the map. -/
private lemma perm_map_lift {α β : Type _} (f : α → β) {L l₂ : List β} (h : L.Perm l₂) :
    ∀ {l₁ : List α}, l₁.map f = L → ∃ l₀, l₁.Perm l₀ ∧ l₀.map f = l₂ := by
  induction h with
  | nil =>
      intro l₁ h1
      exact ⟨l₁, .refl _, h1⟩
  | cons a h ih =>
      intro l₁ h1
      cases l₁ with
      | nil => simp at h1
      | cons x l₁ =>
          rw [List.map_cons] at h1
          injection h1 with hx hL
          obtain ⟨l₀, hp, hm⟩ := ih hL
          exact ⟨x :: l₀, hp.cons x, by rw [List.map_cons, hm, hx]⟩
  | swap a b L =>
      intro l₁ h1
      cases l₁ with
      | nil => simp at h1
      | cons u l₁ =>
          cases l₁ with
          | nil => simp at h1
          | cons w l₁ =>
              simp only [List.map_cons] at h1
              injection h1 with hu h1
              injection h1 with hw h1
              exact ⟨w :: u :: l₁, List.Perm.swap w u l₁, by
                rw [List.map_cons, List.map_cons, hu, hw, h1]⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      intro l₁ h1
      obtain ⟨l₀, hp, hm⟩ := ih₁ h1
      obtain ⟨l₀', hp', hm'⟩ := ih₂ hm
      exact ⟨l₀', hp.trans hp', hm'⟩

/-- Two pairs normalize equally exactly when they are equal or flipped. -/
private lemma sortPair_eq_cases {a b : Nat × Nat} (h : sortPair a = sortPair b) :
    b = a ∨ b = (a.2, a.1) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [sortPair] at h
  split at h <;> split at h <;> simp only [Prod.mk.injEq] at h ⊢ <;> omega

/-- The canonical renaming only sees the edge list up to per-pair flips. -/
private lemma edgeRen_eq_of_sortPair_eq : ∀ {es es' : List (Nat × Nat)},
    es.map sortPair = es'.map sortPair → edgeRen es = edgeRen es' := by
  intro es
  induction es with
  | nil =>
      intro es' h
      rw [List.map_nil] at h
      rw [List.map_eq_nil_iff.mp h.symm]
  | cons e es ih =>
      intro es' h
      cases es' with
      | nil => simp at h
      | cons e' es' =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨he, hes⟩ := h
          funext x
          have hcond : (e.1 = x ∨ e.2 = x) ↔ (e'.1 = x ∨ e'.2 = x) := by
            rcases sortPair_eq_cases he with rfl | rfl
            · exact Iff.rfl
            · exact ⟨fun h => h.symm, fun h => h.symm⟩
          rw [edgeRen, edgeRen, ih hes]
          by_cases hx : e.1 = x ∨ e.2 = x
          · rw [if_pos hx, if_pos (hcond.mp hx)]
          · rw [if_neg hx, if_neg (fun hc => hx (hcond.mpr hc))]

/-- Edge names are permuted by per-pair flips. -/
private lemma edgeNames_perm_of_sortPair_eq : ∀ {es es' : List (Nat × Nat)},
    es.map sortPair = es'.map sortPair → (edgeNames es).Perm (edgeNames es') := by
  intro es
  induction es with
  | nil =>
      intro es' h
      rw [List.map_nil] at h
      rw [List.map_eq_nil_iff.mp h.symm]
  | cons e es ih =>
      intro es' h
      cases es' with
      | nil => simp at h
      | cons e' es' =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨he, hes⟩ := h
          rw [edgeNames_cons, edgeNames_cons]
          rcases sortPair_eq_cases he with rfl | rfl
          · exact ((ih hes).cons _).cons _
          · exact (List.Perm.swap _ _ _).trans (((ih hes).cons _).cons _)

/-- Reindex a soup across any surgery preserving the unordered-edge multiset: the two canonical
renamings produce soup-equivalent configurations on the same thread list. -/
lemma treeSoup_reindexM {es es' : List (Nat × Nat)}
    (hM : (↑(es.map sortPair) : Multiset (Nat × Nat)) = ↑(es'.map sortPair))
    (hnd : (edgeNames es).Nodup) (hnd' : (edgeNames es').Nodup) (ts : List Term) :
    SoupEquiv (es.length, ts.map (fun b => b⟨edgeRen es; (id : Nat → Nat)⟩))
      (es'.length, ts.map (fun b => b⟨edgeRen es'; (id : Nat → Nat)⟩)) := by
  obtain ⟨es₀, hp, hmap⟩ := perm_map_lift sortPair (Multiset.coe_eq_coe.mp hM) rfl
  have hren : edgeRen es₀ = edgeRen es' := edgeRen_eq_of_sortPair_eq hmap
  have hnames : (edgeNames es₀).Perm (edgeNames es') := edgeNames_perm_of_sortPair_eq hmap
  have hnd₀ : (edgeNames es₀).Nodup := hnames.nodup_iff.mpr hnd'
  have hlen : es₀.length = es'.length := by
    have h := congrArg List.length hmap
    rwa [List.length_map, List.length_map] at h
  have h1 := treeSoup_reindex hp hnd hnd₀ ts (fun b _ x _ => by
    by_cases hx : x ∈ edgeNames es
    · exact .inl hx
    · refine .inr (fun ed hed => ⟨fun hh => hx ?_, fun hh => hx ?_⟩)
      · exact hh ▸ (mem_edgeNames_of_mem hed).1
      · exact hh ▸ (mem_edgeNames_of_mem hed).2)
  rwa [hlen, hren] at h1

/-! ## Helpers for the reshuffling continuations -/

/-- Replacing a known element at a position, in the multiset view. -/
lemma coe_set_add {α : Type _} : ∀ {ts : List α} {p : Nat} {b : α},
    getElem? ts p = some b → ∀ (a : α),
    (↑(ts.set p a) : Multiset α) + {b} = ↑ts + {a} := by
  intro ts
  induction ts with
  | nil => intro p b h; simp at h
  | cons x ts ih =>
      intro p b h a
      cases p with
      | zero =>
          rw [List.getElem?_cons_zero] at h
          obtain rfl := Option.some.inj h
          rw [List.set_cons_zero]
          simp only [← Multiset.cons_coe, ← Multiset.singleton_add]
          abel
      | succ p =>
          rw [List.getElem?_cons_succ] at h
          rw [List.set_cons_succ]
          simp only [← Multiset.cons_coe, ← Multiset.singleton_add]
          calc ({x} + ↑(ts.set p a)) + {b} = {x} + ((↑(ts.set p a) : Multiset α) + {b}) := by
                abel
            _ = {x} + ((↑ts : Multiset α) + {a}) := by rw [ih h a]
            _ = ({x} + ↑ts) + {a} := by abel

private lemma childBodiesM_middle (l r : List (Chan × Tree)) (c : Chan) (t : Tree) :
    childBodiesM (l ++ (c, t) :: r) = treeBodiesM t + childBodiesM (l ++ r) := by
  simp only [childBodiesM_append, childBodiesM_cons]
  abel

private lemma childEdgesM_middle (l r : List (Chan × Tree)) (c : Chan) (t : Tree) :
    childEdgesM (l ++ (c, t) :: r) =
      sortPair (chanIndex c, childChan t) ::ₘ (treeEdgesM t + childEdgesM (l ++ r)) := by
  simp only [childEdgesM_append, childEdgesM_cons, ← Multiset.singleton_add]
  abel

private lemma childChansM_middle (l r : List (Chan × Tree)) (c : Chan) (t : Tree) :
    childChansM (l ++ (c, t) :: r) = (chanIndex c ::ₘ treeChansM t) + childChansM (l ++ r) := by
  simp only [childChansM_append, childChansM_cons, ← Multiset.singleton_add]
  abel

private lemma subBodiesM_middle (l r : List Tree) (t : Tree) :
    subBodiesM (l ++ t :: r) = treeBodiesM t + subBodiesM (l ++ r) := by
  simp only [subBodiesM_append, subBodiesM_cons]
  abel

private lemma subEdgesM_middle (l r : List Tree) (t : Tree) :
    subEdgesM (l ++ t :: r) = treeEdgesM t + subEdgesM (l ++ r) := by
  simp only [subEdgesM_append, subEdgesM_cons]
  abel

private lemma subChansM_middle (l r : List Tree) (t : Tree) :
    subChansM (l ++ t :: r) = treeChansM t + subChansM (l ++ r) := by
  simp only [subChansM_append, subChansM_cons]
  abel

private lemma stepAvoids_of_chansM_le {sub sub' whole : Tree}
    (h : treeChansM sub' ≤ treeChansM sub) : stepAvoids sub sub' whole := by
  intro x hx hnx
  exact absurd (mem_treeChansM.mp (Multiset.mem_of_le h (mem_treeChansM.mpr hx))) hnx

private lemma wrap_bodiesM_child {O N' : Multiset Term} {ch ch' : Tree}
    (h : treeBodiesM ch' + O = treeBodiesM ch + N')
    (m : Term) (l r : List (Chan × Tree)) (c₀ : Chan) (ns : List Tree) :
    (m ::ₘ (childBodiesM (l ++ (c₀, ch') :: r) + subBodiesM ns)) + O =
      (m ::ₘ (childBodiesM (l ++ (c₀, ch) :: r) + subBodiesM ns)) + N' := by
  calc (m ::ₘ (childBodiesM (l ++ (c₀, ch') :: r) + subBodiesM ns)) + O
      = (treeBodiesM ch' + O) + ({m} + (childBodiesM (l ++ r) + subBodiesM ns)) := by
        simp only [childBodiesM_middle, ← Multiset.singleton_add]
        abel
    _ = (treeBodiesM ch + N') + ({m} + (childBodiesM (l ++ r) + subBodiesM ns)) := by
        rw [h]
    _ = (m ::ₘ (childBodiesM (l ++ (c₀, ch) :: r) + subBodiesM ns)) + N' := by
        simp only [childBodiesM_middle, ← Multiset.singleton_add]
        abel

private lemma wrap_bodiesM_sub {O N' : Multiset Term} {n n' : Tree}
    (h : treeBodiesM n' + O = treeBodiesM n + N')
    (m : Term) (ms : List (Chan × Tree)) (l r : List Tree) :
    (m ::ₘ (childBodiesM ms + subBodiesM (l ++ n' :: r))) + O =
      (m ::ₘ (childBodiesM ms + subBodiesM (l ++ n :: r))) + N' := by
  calc (m ::ₘ (childBodiesM ms + subBodiesM (l ++ n' :: r))) + O
      = (treeBodiesM n' + O) + ({m} + (childBodiesM ms + subBodiesM (l ++ r))) := by
        simp only [subBodiesM_middle, ← Multiset.singleton_add]
        abel
    _ = (treeBodiesM n + N') + ({m} + (childBodiesM ms + subBodiesM (l ++ r))) := by
        rw [h]
    _ = (m ::ₘ (childBodiesM ms + subBodiesM (l ++ n :: r))) + N' := by
        simp only [subBodiesM_middle, ← Multiset.singleton_add]
        abel

private lemma wrap_edgesM_child {E : Multiset (Nat × Nat)} {ch ch' : Tree}
    (h : treeEdgesM ch' + E = treeEdgesM ch) (hcc : childChan ch' = childChan ch)
    (l r : List (Chan × Tree)) (c₀ : Chan) (ns : List Tree) :
    (childEdgesM (l ++ (c₀, ch') :: r) + subEdgesM ns) + E =
      childEdgesM (l ++ (c₀, ch) :: r) + subEdgesM ns := by
  calc (childEdgesM (l ++ (c₀, ch') :: r) + subEdgesM ns) + E
      = (treeEdgesM ch' + E) +
          ({sortPair (chanIndex c₀, childChan ch)} + (childEdgesM (l ++ r) + subEdgesM ns)) := by
        simp only [childEdgesM_middle, hcc, ← Multiset.singleton_add]
        abel
    _ = treeEdgesM ch +
          ({sortPair (chanIndex c₀, childChan ch)} + (childEdgesM (l ++ r) + subEdgesM ns)) := by
        rw [h]
    _ = childEdgesM (l ++ (c₀, ch) :: r) + subEdgesM ns := by
        simp only [childEdgesM_middle, ← Multiset.singleton_add]
        abel

private lemma wrap_edgesM_sub {E : Multiset (Nat × Nat)} {n n' : Tree}
    (h : treeEdgesM n' + E = treeEdgesM n)
    (ms : List (Chan × Tree)) (l r : List Tree) :
    (childEdgesM ms + subEdgesM (l ++ n' :: r)) + E =
      childEdgesM ms + subEdgesM (l ++ n :: r) := by
  calc (childEdgesM ms + subEdgesM (l ++ n' :: r)) + E
      = (treeEdgesM n' + E) + (childEdgesM ms + subEdgesM (l ++ r)) := by
        simp only [subEdgesM_middle]
        abel
    _ = treeEdgesM n + (childEdgesM ms + subEdgesM (l ++ r)) := by rw [h]
    _ = childEdgesM ms + subEdgesM (l ++ n :: r) := by
        simp only [subEdgesM_middle]
        abel

private lemma wrap_chansM_child {C : Multiset Nat} {ch ch' : Tree}
    (h : treeChansM ch' + C = treeChansM ch)
    (l r : List (Chan × Tree)) (c₀ : Chan) (ns : List Tree) :
    (childChansM (l ++ (c₀, ch') :: r) + subChansM ns) + C =
      childChansM (l ++ (c₀, ch) :: r) + subChansM ns := by
  calc (childChansM (l ++ (c₀, ch') :: r) + subChansM ns) + C
      = (treeChansM ch' + C) + ({chanIndex c₀} + (childChansM (l ++ r) + subChansM ns)) := by
        simp only [childChansM_middle, ← Multiset.singleton_add]
        abel
    _ = treeChansM ch + ({chanIndex c₀} + (childChansM (l ++ r) + subChansM ns)) := by
        rw [h]
    _ = childChansM (l ++ (c₀, ch) :: r) + subChansM ns := by
        simp only [childChansM_middle, ← Multiset.singleton_add]
        abel

private lemma wrap_chansM_child_cons {C : Multiset Nat} {ch ch' : Tree} {x : Nat}
    (h : treeChansM ch' + C = treeChansM ch)
    (l r : List (Chan × Tree)) (c₀ : Chan) (ns : List Tree) :
    (x ::ₘ (childChansM (l ++ (c₀, ch') :: r) + subChansM ns)) + C =
      x ::ₘ (childChansM (l ++ (c₀, ch) :: r) + subChansM ns) := by
  simp only [← Multiset.singleton_add]
  calc ({x} + (childChansM (l ++ (c₀, ch') :: r) + subChansM ns)) + C
      = ((childChansM (l ++ (c₀, ch') :: r) + subChansM ns) + C) + {x} := by abel
    _ = (childChansM (l ++ (c₀, ch) :: r) + subChansM ns) + {x} := by
        rw [wrap_chansM_child h l r c₀ ns]
    _ = {x} + (childChansM (l ++ (c₀, ch) :: r) + subChansM ns) := by abel

private lemma wrap_chansM_sub {C : Multiset Nat} {n n' : Tree}
    (h : treeChansM n' + C = treeChansM n)
    (ms : List (Chan × Tree)) (l r : List Tree) :
    (childChansM ms + subChansM (l ++ n' :: r)) + C =
      childChansM ms + subChansM (l ++ n :: r) := by
  calc (childChansM ms + subChansM (l ++ n' :: r)) + C
      = (treeChansM n' + C) + (childChansM ms + subChansM (l ++ r)) := by
        simp only [subChansM_middle]
        abel
    _ = treeChansM n + (childChansM ms + subChansM (l ++ r)) := by rw [h]
    _ = childChansM ms + subChansM (l ++ n :: r) := by
        simp only [subChansM_middle]
        abel

private lemma wrap_chansM_sub_cons {C : Multiset Nat} {n n' : Tree} {x : Nat}
    (h : treeChansM n' + C = treeChansM n)
    (ms : List (Chan × Tree)) (l r : List Tree) :
    (x ::ₘ (childChansM ms + subChansM (l ++ n' :: r))) + C =
      x ::ₘ (childChansM ms + subChansM (l ++ n :: r)) := by
  simp only [← Multiset.singleton_add]
  calc ({x} + (childChansM ms + subChansM (l ++ n' :: r))) + C
      = ((childChansM ms + subChansM (l ++ n' :: r)) + C) + {x} := by abel
    _ = (childChansM ms + subChansM (l ++ n :: r)) + {x} := by
        rw [wrap_chansM_sub h ms l r]
    _ = {x} + (childChansM ms + subChansM (l ++ n :: r)) := by abel

/-! ## Reindexing across an edge removal -/

/-- A name missing from the `e`-th edge never renames to binder `e`. -/
private lemma edgeRen_ne_of_miss : ∀ {es : List (Nat × Nat)} {e : Nat} {c d : Nat},
    getElem? es e = some (c, d) → ∀ x, x ≠ c → x ≠ d → edgeRen es x ≠ e := by
  intro es
  induction es with
  | nil => intro e c d h; simp at h
  | cons ed es ih =>
      intro e c d h x hxc hxd
      cases e with
      | zero =>
          rw [List.getElem?_cons_zero] at h
          obtain rfl := Option.some.inj h
          rw [edgeRen_cons_miss (Ne.symm hxc) (Ne.symm hxd)]
          omega
      | succ e =>
          rw [List.getElem?_cons_succ] at h
          by_cases hhit : ed.1 = x ∨ ed.2 = x
          · rw [edgeRen_cons_hit hhit]
            omega
          · push Not at hhit
            rw [edgeRen_cons_miss hhit.1 hhit.2]
            have := ih h x hxc hxd
            omega

/-- Removing the `e`-th edge conjugates the canonical renaming by the binder discard, on names
foreign to that edge. -/
private lemma edgeRen_eraseIdx : ∀ {es : List (Nat × Nat)} {e : Nat} {c d : Nat},
    getElem? es e = some (c, d) → ∀ x, x ≠ c → x ≠ d →
    edgeRen (es.eraseIdx e) x = TLLC.Process.unbind e (edgeRen es x) := by
  intro es
  induction es with
  | nil => intro e c d h; simp at h
  | cons ed es ih =>
      intro e c d h x hxc hxd
      cases e with
      | zero =>
          rw [List.getElem?_cons_zero] at h
          obtain rfl := Option.some.inj h
          show edgeRen es x = TLLC.Process.unbind 0 (edgeRen ((c, d) :: es) x)
          rw [edgeRen_cons_miss (Ne.symm hxc) (Ne.symm hxd)]
          unfold TLLC.Process.unbind
          simp
      | succ e =>
          rw [List.getElem?_cons_succ] at h
          show edgeRen (ed :: es.eraseIdx e) x = _
          by_cases hhit : ed.1 = x ∨ ed.2 = x
          · rw [edgeRen_cons_hit hhit, edgeRen_cons_hit hhit]
            unfold TLLC.Process.unbind
            simp
          · push Not at hhit
            rw [edgeRen_cons_miss hhit.1 hhit.2, edgeRen_cons_miss hhit.1 hhit.2,
              ih h x hxc hxd]
            have hne := edgeRen_ne_of_miss h x hxc hxd
            unfold TLLC.Process.unbind
            by_cases hlt : edgeRen es x < e
            · rw [if_pos hlt, if_pos (by omega)]
            · rw [if_neg hlt, if_neg (by omega)]
              omega

/-- Removing an indexed element, in the multiset view. -/
private lemma coe_map_eraseIdx : ∀ {es : List (Nat × Nat)} {e : Nat} {ed : Nat × Nat},
    getElem? es e = some ed →
    (↑((es.eraseIdx e).map sortPair) : Multiset (Nat × Nat)) + {sortPair ed} =
      ↑(es.map sortPair) := by
  intro es
  induction es with
  | nil => intro e ed h; simp at h
  | cons ed₀ es ih =>
      intro e ed h
      cases e with
      | zero =>
          rw [List.getElem?_cons_zero] at h
          obtain rfl := Option.some.inj h
          show (↑(es.map sortPair) : Multiset (Nat × Nat)) + {sortPair ed₀} =
            ↑((ed₀ :: es).map sortPair)
          rw [List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add]
          abel
      | succ e =>
          rw [List.getElem?_cons_succ] at h
          show (↑((ed₀ :: es.eraseIdx e).map sortPair) : Multiset (Nat × Nat)) + {sortPair ed} =
            ↑((ed₀ :: es).map sortPair)
          rw [List.map_cons, List.map_cons, ← Multiset.cons_coe, ← Multiset.cons_coe,
            ← Multiset.singleton_add, ← Multiset.singleton_add, add_assoc,
            ih h]

/-- Edge names of the reduced list embed in the original names. -/
private lemma edgeNames_eraseIdx_sublist : ∀ (es : List (Nat × Nat)) (e : Nat),
    (edgeNames (es.eraseIdx e)).Sublist (edgeNames es) := by
  intro es
  induction es with
  | nil => intro e; simp [List.eraseIdx]
  | cons ed es ih =>
      intro e
      cases e with
      | zero =>
          show (edgeNames es).Sublist (edgeNames (ed :: es))
          rw [edgeNames_cons]
          exact ((List.sublist_cons_self _ _).trans (List.sublist_cons_self _ _))
      | succ e =>
          show (edgeNames (ed :: es.eraseIdx e)).Sublist (edgeNames (ed :: es))
          rw [edgeNames_cons, edgeNames_cons]
          exact ((ih e).cons_cons _).cons_cons _

/-- Reindex a soup across an edge removal: on threads that do not mention the removed edge's
names explicitly, the canonical soup of the reduced edge list is equivalent to the original
soup with the removed binder discarded. -/
lemma treeSoup_remove {es es' : List (Nat × Nat)} {e c d : Nat}
    (hedge : getElem? es e = some (c, d))
    (hM : (↑(es'.map sortPair) : Multiset (Nat × Nat)) + {sortPair (c, d)} =
      ↑(es.map sortPair))
    (hnd : (edgeNames es).Nodup) (hnd' : (edgeNames es').Nodup)
    (ts : List Term)
    (hocc : ∀ b ∈ ts, occurs c b = 0 ∧ occurs d b = 0) :
    SoupEquiv (es'.length, ts.map (fun b => b⟨edgeRen es'; (id : Nat → Nat)⟩))
      (es.length - 1,
        ts.map (fun b =>
          b⟨fun x => TLLC.Process.unbind e (edgeRen es x); (id : Nat → Nat)⟩)) := by
  have hMeq : (↑(es'.map sortPair) : Multiset (Nat × Nat)) =
      ↑((es.eraseIdx e).map sortPair) :=
    add_right_cancel (hM.trans (coe_map_eraseIdx hedge).symm)
  have hnd₀ : (edgeNames (es.eraseIdx e)).Nodup :=
    (edgeNames_eraseIdx_sublist es e).nodup hnd
  have helt : e < es.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hedge
    cases hedge
  have hlen : (es.eraseIdx e).length = es.length - 1 := by
    rw [List.length_eraseIdx]
    simp [helt]
  refine ARS.conv_trans (treeSoup_reindexM hMeq hnd' hnd₀ ts) ?_
  rw [hlen]
  refine ARS.conv1 (SoupG.congr ?_)
  refine forall₂_map_rel ts (fun b hb => congrTerm_cren_of_occurs' (fun x hx => ?_))
  have hxc : x ≠ c := by
    intro hcon
    exact hx (hcon ▸ (hocc b hb).1)
  have hxd : x ≠ d := by
    intro hcon
    exact hx (hcon ▸ (hocc b hb).2)
  exact edgeRen_eraseIdx hedge x hxc hxd

/-- The edge-navigation package: positions of the two endpoint bodies (with occurrence
witnesses for the own name and exclusions for the opposite name), and the two
implicit-communication firing continuations. -/
private def EdgePkg (t : Tree) (c d : Nat) : Prop :=
  ∃ (pi pj : Nat), pi ≠ pj ∧
    (∃ bpi, getElem? (treeBodies t) pi = some bpi ∧
      occurs c bpi ≠ 0 ∧ occurs d bpi = 0) ∧
    (∃ bpj, getElem? (treeBodies t) pj = some bpj ∧
      occurs d bpj ≠ 0 ∧ occurs c bpj = 0) ∧
    (∀ (M₀ N₀ : EvalCtx) (o₀ : Term),
      getElem? (treeBodies t) pi =
        some (M₀.eval (.app (.send (.chan (Chan.var_Chan c)) .im) o₀ .im)) →
      getElem? (treeBodies t) pj =
        some (N₀.eval (.recv (.chan (Chan.var_Chan d)) .im)) →
      ∃ t', Step t t' ∧
        treeBodies t' = ((treeBodies t).set pi
          (M₀.eval (.pure (.chan (Chan.var_Chan c))))).set pj
          (N₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan d)) .im .L))) ∧
        treeEdges t' = treeEdges t ∧ treeChans t' = treeChans t ∧
        childChan t' = childChan t) ∧
    (∀ (M₀ N₀ : EvalCtx) (o₀ : Term),
      getElem? (treeBodies t) pj =
        some (N₀.eval (.app (.send (.chan (Chan.var_Chan d)) .im) o₀ .im)) →
      getElem? (treeBodies t) pi =
        some (M₀.eval (.recv (.chan (Chan.var_Chan c)) .im)) →
      ∃ t', Step t t' ∧
        treeBodies t' = ((treeBodies t).set pi
          (M₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan c)) .im .L)))).set pj
          (N₀.eval (.pure (.chan (Chan.var_Chan d)))) ∧
        treeEdges t' = treeEdges t ∧ treeChans t' = treeChans t ∧
        childChan t' = childChan t) ∧
    (∀ (M₀ N₀ : EvalCtx) (v₀ : Term), Val v₀ →
      getElem? (treeBodies t) pi =
        some (M₀.eval (.app (.send (.chan (Chan.var_Chan c)) .ex) v₀ .ex)) →
      getElem? (treeBodies t) pj =
        some (N₀.eval (.recv (.chan (Chan.var_Chan d)) .ex)) →
      ∃ t', Step t t' ∧
        treeBodiesM t' + ({M₀.eval (.app (.send (.chan (Chan.var_Chan c)) .ex) v₀ .ex)} +
          {N₀.eval (.recv (.chan (Chan.var_Chan d)) .ex)}) =
        treeBodiesM t + ({M₀.eval (.pure (.chan (Chan.var_Chan c)))} +
          {N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan d)) .ex .L))}) ∧
        treeEdgesM t' = treeEdgesM t ∧ treeChansM t' = treeChansM t ∧
        childChan t' = childChan t) ∧
    (∀ (M₀ N₀ : EvalCtx) (v₀ : Term), Val v₀ →
      getElem? (treeBodies t) pj =
        some (N₀.eval (.app (.send (.chan (Chan.var_Chan d)) .ex) v₀ .ex)) →
      getElem? (treeBodies t) pi =
        some (M₀.eval (.recv (.chan (Chan.var_Chan c)) .ex)) →
      ∃ t', Step t t' ∧
        treeBodiesM t' + ({M₀.eval (.recv (.chan (Chan.var_Chan c)) .ex)} +
          {N₀.eval (.app (.send (.chan (Chan.var_Chan d)) .ex) v₀ .ex)}) =
        treeBodiesM t + ({M₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan c)) .ex .L))} +
          {N₀.eval (.pure (.chan (Chan.var_Chan d)))}) ∧
        treeEdgesM t' = treeEdgesM t ∧ treeChansM t' = treeChansM t ∧
        childChan t' = childChan t) ∧
    (∀ (M₀ N₀ : EvalCtx) (b : Bool),
      getElem? (treeBodies t) pi =
        some (M₀.eval (.close b (.chan (Chan.var_Chan c)))) →
      getElem? (treeBodies t) pj =
        some (N₀.eval (.close (!b) (.chan (Chan.var_Chan d)))) →
      ∃ t', Step t t' ∧
        treeBodiesM t' + ({M₀.eval (.close b (.chan (Chan.var_Chan c)))} +
          {N₀.eval (.close (!b) (.chan (Chan.var_Chan d)))}) =
        treeBodiesM t + ({M₀.eval (.pure .one)} + {N₀.eval (.pure .one)}) ∧
        treeEdgesM t' + {sortPair (c, d)} = treeEdgesM t ∧
        treeChansM t' + ({c} + {d}) = treeChansM t ∧
        childChan t' = childChan t)

private lemma edge_replay_gen : ∀ (t : Tree),
    (Typed t ∨ ∃ r A, TypedAt r A t) → (treeChans t).Nodup →
    ∀ {e c d : Nat}, getElem? (treeEdges t) e = some (c, d) → EdgePkg t c d
  | .root m ms ns, hty, hnd, e, c, d, hedge => by
      have htyR : Typed (.root m ms ns) := by
        rcases hty with h | ⟨r0, A0, h⟩
        · exact h
        · cases h
      rw [treeEdges_root] at hedge
      rcases getElem?_append_split hedge with ⟨hlt, h'⟩ | ⟨hge, h'⟩
      · rcases childEdges_locate ms h' with ⟨l, ch, r, rfl, hd⟩ | ⟨l, c₀, ch, r, e', rfl, h'', hmeas⟩
        · -- the edge is a child edge of this node: fire here
          cases htyR with
          | @root Θ _ _ _ hsingle tym hch hsub =>
          have hchmem : (Chan.var_Chan c, ch) ∈ l ++ (Chan.var_Chan c, ch) :: r :=
            List.mem_append.mpr (.inr (List.mem_cons_self ..))
          obtain ⟨rc, Ac, htyAt⟩ := hch.typedAt_of_mem hchmem
          cases ch with
          | root _ _ _ => cases htyAt
          | node dch mc msc nsc =>
          cases dch with
          | var_Chan dx =>
          have hdx : d = dx := hd
          subst hdx
          rw [treeChans_root] at hnd
          obtain ⟨hndLI, hndS, hdisjS⟩ := List.nodup_append.mp hnd
          obtain ⟨hndL, hndI, hdisjLI⟩ := List.nodup_append.mp hndLI
          have hclabmem : c ∈ (l ++ (Chan.var_Chan c, Tree.node (Chan.var_Chan d) mc msc nsc)
              :: r).map (fun p => chanIndex p.1) :=
            List.mem_map.mpr ⟨(Chan.var_Chan c, _), hchmem, rfl⟩
          have hdint : d ∈ childInteriors (l ++ (Chan.var_Chan c,
              Tree.node (Chan.var_Chan d) mc msc nsc) :: r) := by
            rw [childInteriors_append, childInteriors_cons]
            refine List.mem_append.mpr (.inr (List.mem_append.mpr (.inl ?_)))
            rw [treeChans_node]
            exact List.mem_cons_self ..
          have hoccm : occurs c m = 1 :=
            tym.occurs1 (hch.pos_of_label (List.mem_map.mpr ⟨(Chan.var_Chan c, _), hchmem, rfl⟩))
          have hd0m : occurs d m = 0 := by
            by_contra hocc
            have hpc := TLLC.Process.dynOccursCount tym d
            have hmemd := hch.support d (by rw [← hpc]; exact hocc)
            exact (hdisjLI d hmemd d hdint) rfl
          cases htyAt with
          | @node Θc _ _ _ _ _ _ hsingleC hhasC tymC hchC hsubC =>
          have hoccmc : occurs d mc = 1 := tymC.occurs1 hhasC.pos_true
          have hc0mc : occurs c mc = 0 := by
            by_contra hocc
            have hpc := TLLC.Process.dynOccursCount tymC c
            rcases hchC.support c (by rw [← hpc]; exact hocc) with rfl | hmem
            · exact (hdisjLI c hclabmem c hdint) rfl
            · refine (hdisjLI c hclabmem c ?_) rfl
              rw [childInteriors_append, childInteriors_cons]
              refine List.mem_append.mpr (.inr (List.mem_append.mpr (.inl ?_)))
              rw [treeChans_node]
              refine List.mem_cons_of_mem _ ?_
              exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hmem)))
          refine ⟨0, 1 + (childBodies l).length, by omega, ⟨m, ?_, ?_, ?_⟩,
            ⟨mc, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
          · rw [treeBodies_root]
            exact List.getElem?_cons_zero
          · rw [hoccm]
            omega
          · exact hd0m
          · rw [treeBodies_root, childBodies_append, childBodies_cons]
            exact getElem?_cons_append_block (by
              rw [treeBodies_node]
              exact List.getElem?_cons_zero)
          · rw [hoccmc]
            omega
          · exact hc0mc
          · -- fire the parent-send rule
            intro M₀ N₀ o₀ hpiS hpjS
            rw [treeBodies_root, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_root, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            refine ⟨.root (M₀.eval (.pure (.chan (Chan.var_Chan c))))
              (l ++ (Chan.var_Chan c, .node (Chan.var_Chan d)
                (N₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan d)) .im .L))) msc nsc) :: r) ns,
              Step.rootSendIm, ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_root, treeBodies_root, childBodies_append, childBodies_append,
                childBodies_cons, childBodies_cons, treeBodies_node, treeBodies_node,
                List.set_cons_zero,
                show 1 + (childBodies l).length = (childBodies l).length + 1 from by omega,
                List.set_cons_succ,
                set_append_lt _ (by
                  simp [List.length_append, List.length_cons]) _,
                set_append_ge _ (Nat.le_refl _) _, Nat.sub_self,
                set_append_lt _ (by simp) _,
                List.set_cons_zero]
            · rw [treeEdges_root, treeEdges_root, childEdges_append, childEdges_append,
                childEdges_cons, childEdges_cons, treeEdges_node, treeEdges_node]
              rfl
            · rw [treeChans_root, treeChans_root, childInteriors_append, childInteriors_append,
                childInteriors_cons, childInteriors_cons, treeChans_node, treeChans_node,
                labels_surgery l r (Chan.var_Chan c)
                  (Tree.node (Chan.var_Chan d)
                    (N₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan d)) .im .L))) msc nsc)
                  (Tree.node (Chan.var_Chan d)
                    (N₀.eval (.recv (.chan (Chan.var_Chan d)) .im)) msc nsc)]
          · -- fire the parent-receive rule
            intro M₀ N₀ o₀ hpjS hpiS
            rw [treeBodies_root, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_root, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            refine ⟨.root (M₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan c)) .im .L)))
              (l ++ (Chan.var_Chan c, .node (Chan.var_Chan d)
                (N₀.eval (.pure (.chan (Chan.var_Chan d)))) msc nsc) :: r) ns,
              Step.rootRecvIm, ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_root, treeBodies_root, childBodies_append, childBodies_append,
                childBodies_cons, childBodies_cons, treeBodies_node, treeBodies_node,
                List.set_cons_zero,
                show 1 + (childBodies l).length = (childBodies l).length + 1 from by omega,
                List.set_cons_succ,
                set_append_lt _ (by
                  simp [List.length_append, List.length_cons]) _,
                set_append_ge _ (Nat.le_refl _) _, Nat.sub_self,
                set_append_lt _ (by simp) _,
                List.set_cons_zero]
            · rw [treeEdges_root, treeEdges_root, childEdges_append, childEdges_append,
                childEdges_cons, childEdges_cons, treeEdges_node, treeEdges_node]
              rfl
            · rw [treeChans_root, treeChans_root, childInteriors_append, childInteriors_append,
                childInteriors_cons, childInteriors_cons, treeChans_node, treeChans_node,
                labels_surgery l r (Chan.var_Chan c)
                  (Tree.node (Chan.var_Chan d)
                    (N₀.eval (.pure (.chan (Chan.var_Chan d)))) msc nsc)
                  (Tree.node (Chan.var_Chan d)
                    (N₀.eval (.app (.send (.chan (Chan.var_Chan d)) .im) o₀ .im)) msc nsc)]
          · -- fire the parent-send rule (explicit)
            intro M₀ N₀ v₀ hv₀ hpiS hpjS
            rw [treeBodies_root, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_root, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            refine ⟨.root (M₀.eval (.pure (.chan (Chan.var_Chan c))))
              (sendExChildren v₀ (Chan.var_Chan c) (Chan.var_Chan d) N₀ msc nsc (l ++ r)) ns,
              Step.rootSendEx hv₀, ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_root, treeBodiesM_node, sendExChildren,
                childBodiesM_insertChild, childBodiesM_mergeChildren, childBodiesM_middle]
              rw [← childBodiesM_split v₀ (l ++ r)]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeEdgesM_root, treeEdgesM_node, sendExChildren,
                childEdgesM_insertChild, childEdgesM_mergeChildren, childEdgesM_middle,
                childChan, chanIndex]
              rw [← childEdgesM_split v₀ (l ++ r)]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeChansM_root, treeChansM_node, sendExChildren,
                childChansM_insertChild, childChansM_mergeChildren, childChansM_middle,
                chanIndex]
              rw [← childChansM_split v₀ (l ++ r)]
              simp only [← Multiset.singleton_add]
              abel
          · -- fire the parent-receive rule (explicit)
            intro M₀ N₀ v₀ hv₀ hpjS hpiS
            rw [treeBodies_root, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_root, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            refine ⟨.root (M₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan c)) .ex .L)))
              (recvExChildren v₀ (Chan.var_Chan c) (Chan.var_Chan d) N₀ msc nsc (l ++ r)) ns,
              Step.rootRecvEx hv₀, ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_root, treeBodiesM_node, recvExChildren,
                childBodiesM_insertChild, childBodiesM_mergeChildren, childBodiesM_middle]
              rw [← childBodiesM_split v₀ msc]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeEdgesM_root, treeEdgesM_node, recvExChildren,
                childEdgesM_insertChild, childEdgesM_mergeChildren, childEdgesM_middle,
                childChan, chanIndex]
              rw [← childEdgesM_split v₀ msc]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeChansM_root, treeChansM_node, recvExChildren,
                childChansM_insertChild, childChansM_mergeChildren, childChansM_middle,
                chanIndex]
              rw [← childChansM_split v₀ msc]
              simp only [← Multiset.singleton_add]
              abel
          · -- fire the close rules
            intro M₀ N₀ b hpiS hpjS
            rw [treeBodies_root, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_root, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            refine ⟨.root (M₀.eval (.pure .one)) (l ++ r)
              (ns ++ [Tree.root (N₀.eval (.pure .one)) msc nsc]), ?_, ?_, ?_, ?_, rfl⟩
            · cases b
              · exact Step.rootWait
              · exact Step.rootClose
            · simp only [treeBodiesM_root, treeBodiesM_node, childBodiesM_middle,
                subBodiesM_append, subBodiesM_cons, subBodiesM_nil, ← Multiset.singleton_add]
              abel
            · simp only [treeEdgesM_root, treeEdgesM_node, childEdgesM_middle,
                subEdgesM_append, subEdgesM_cons, subEdgesM_nil, childChan, chanIndex,
                ← Multiset.singleton_add]
              abel
            · simp only [treeChansM_root, treeChansM_node, childChansM_middle,
                subChansM_append, subChansM_cons, subChansM_nil, chanIndex,
                ← Multiset.singleton_add]
              abel
        · -- the edge lies inside a child: recurse and wrap
          cases htyR with
          | @root Θ _ _ _ hsingle tym hch hsub =>
          have hchmem : (c₀, ch) ∈ l ++ (c₀, ch) :: r :=
            List.mem_append.mpr (.inr (List.mem_cons_self ..))
          obtain ⟨rc, Ac, htyAt⟩ := hch.typedAt_of_mem hchmem
          have hndch : (treeChans ch).Nodup := by
            rw [treeChans_root] at hnd
            obtain ⟨hndLI, _, _⟩ := List.nodup_append.mp hnd
            obtain ⟨_, hndI, _⟩ := List.nodup_append.mp hndLI
            exact (treeChans_sublist_childInteriors hchmem).nodup hndI
          obtain ⟨pi', pj', hpij', ⟨bpi, hpib, hpic, hpid0⟩, ⟨bpj, hpjb, hpjd, hpjc0⟩,
            contS', contR', contSEx', contREx', contClose'⟩ := edge_replay_gen ch (.inr ⟨rc, Ac, htyAt⟩) hndch h''
          have hpiLt : pi' < (treeBodies ch).length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hpib
            cases hpib
          have hpjLt : pj' < (treeBodies ch).length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hpjb
            cases hpjb
          refine ⟨1 + (childBodies l).length + pi', 1 + (childBodies l).length + pj',
            by omega, ⟨bpi, ?_, hpic, hpid0⟩, ⟨bpj, ?_, hpjd, hpjc0⟩, ?_, ?_, ?_, ?_, ?_⟩
          · rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt]
            exact hpib
          · rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt]
            exact hpjb
          · intro M₀ N₀ o₀ h1 h2
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h1
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contS' M₀ N₀ o₀ h1 h2
            refine ⟨.root m (l ++ (c₀, ch') :: r) ns,
              Step.rootChild stepch (fun x hx hnx => absurd (hchans' ▸ hx) hnx),
              ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_root, treeBodies_root, childBodies_append, childBodies_append,
                childBodies_cons, childBodies_cons, hbodies',
                set_block_eq hpiLt _,
                set_block_eq (by rw [List.length_set]; omega) _]
            · rw [treeEdges_root, treeEdges_root, childEdges_append, childEdges_append,
                childEdges_cons, childEdges_cons, hedges', hcc']
            · rw [treeChans_root, treeChans_root, childInteriors_append, childInteriors_append,
                childInteriors_cons, childInteriors_cons, hchans',
                labels_surgery l r c₀ ch' ch]
          · intro M₀ N₀ o₀ h1 h2
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h1
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contR' M₀ N₀ o₀ h1 h2
            refine ⟨.root m (l ++ (c₀, ch') :: r) ns,
              Step.rootChild stepch (fun x hx hnx => absurd (hchans' ▸ hx) hnx),
              ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_root, treeBodies_root, childBodies_append, childBodies_append,
                childBodies_cons, childBodies_cons, hbodies',
                set_block_eq hpiLt _,
                set_block_eq (by rw [List.length_set]; omega) _]
            · rw [treeEdges_root, treeEdges_root, childEdges_append, childEdges_append,
                childEdges_cons, childEdges_cons, hedges', hcc']
            · rw [treeChans_root, treeChans_root, childInteriors_append, childInteriors_append,
                childInteriors_cons, childInteriors_cons, hchans',
                labels_surgery l r c₀ ch' ch]
          · intro M₀ N₀ v₀ hv₀ h1 h2
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h1
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contSEx' M₀ N₀ v₀ hv₀ h1 h2
            refine ⟨.root m (l ++ (c₀, ch') :: r) ns,
              Step.rootChild stepch (stepAvoids_of_chansM_le (le_of_eq hchans')),
              ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_root]
              exact wrap_bodiesM_child hbodies' m l r c₀ ns
            · simp only [treeEdgesM_root, childEdgesM_middle, hedges', hcc']
            · simp only [treeChansM_root, childChansM_middle, hchans']
          · intro M₀ N₀ v₀ hv₀ h1 h2
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h1
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contREx' M₀ N₀ v₀ hv₀ h1 h2
            refine ⟨.root m (l ++ (c₀, ch') :: r) ns,
              Step.rootChild stepch (stepAvoids_of_chansM_le (le_of_eq hchans')),
              ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_root]
              exact wrap_bodiesM_child hbodies' m l r c₀ ns
            · simp only [treeEdgesM_root, childEdgesM_middle, hedges', hcc']
            · simp only [treeChansM_root, childChansM_middle, hchans']
          · intro M₀ N₀ b h1 h2
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h1
            rw [treeBodies_root, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contClose' M₀ N₀ b h1 h2
            refine ⟨.root m (l ++ (c₀, ch') :: r) ns,
              Step.rootChild stepch (stepAvoids_of_chansM_le
                (Multiset.le_iff_exists_add.mpr ⟨_, hchans'.symm⟩)),
              ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_root]
              exact wrap_bodiesM_child hbodies' m l r c₀ ns
            · simp only [treeEdgesM_root]
              exact wrap_edgesM_child hedges' hcc' l r c₀ ns
            · simp only [treeChansM_root]
              exact wrap_chansM_child hchans' l r c₀ ns
      · obtain ⟨l, n, r, e', rfl, h'', hmeas⟩ := subEdges_locate ns h'
        -- the edge lies inside a detached subtree: recurse and wrap
        cases htyR with
        | @root Θ _ _ _ hsingle tym hch hsub =>
        have hnmem : n ∈ l ++ n :: r := List.mem_append.mpr (.inr (List.mem_cons_self ..))
        have htyn := hsub.typed_of_mem hnmem
        have hndn : (treeChans n).Nodup := by
          rw [treeChans_root] at hnd
          obtain ⟨_, hndS, _⟩ := List.nodup_append.mp hnd
          exact (treeChans_sublist_subInteriors hnmem).nodup hndS
        obtain ⟨pi', pj', hpij', ⟨bpi, hpib, hpic, hpid0⟩, ⟨bpj, hpjb, hpjd, hpjc0⟩,
          contS', contR', contSEx', contREx', contClose'⟩ := edge_replay_gen n (.inl htyn) hndn h''
        have hpiLt : pi' < (treeBodies n).length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hpib
          cases hpib
        have hpjLt : pj' < (treeBodies n).length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hpjb
          cases hpjb
        refine ⟨1 + (childBodies ms).length + (subBodies l).length + pi',
          1 + (childBodies ms).length + (subBodies l).length + pj',
          by omega, ⟨bpi, ?_, hpic, hpid0⟩, ⟨bpj, ?_, hpjd, hpjc0⟩, ?_, ?_, ?_, ?_, ?_⟩
        · rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt]
          exact hpib
        · rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt]
          exact hpjb
        · intro M₀ N₀ o₀ h1 h2
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h1
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contS' M₀ N₀ o₀ h1 h2
          refine ⟨.root m ms (l ++ n' :: r),
            Step.rootSubtree stepn (fun x hx hnx => absurd (hchans' ▸ hx) hnx),
            ?_, ?_, ?_, rfl⟩
          · rw [treeBodies_root, treeBodies_root, subBodies_append, subBodies_append,
              subBodies_cons, subBodies_cons, hbodies',
              set_sub_block_eq hpiLt _,
              set_sub_block_eq (by rw [List.length_set]; omega) _]
          · rw [treeEdges_root, treeEdges_root, subEdges_append, subEdges_append,
              subEdges_cons, subEdges_cons, hedges']
          · rw [treeChans_root, treeChans_root, subInteriors_append, subInteriors_append,
              subInteriors_cons, subInteriors_cons, hchans']
        · intro M₀ N₀ o₀ h1 h2
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h1
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contR' M₀ N₀ o₀ h1 h2
          refine ⟨.root m ms (l ++ n' :: r),
            Step.rootSubtree stepn (fun x hx hnx => absurd (hchans' ▸ hx) hnx),
            ?_, ?_, ?_, rfl⟩
          · rw [treeBodies_root, treeBodies_root, subBodies_append, subBodies_append,
              subBodies_cons, subBodies_cons, hbodies',
              set_sub_block_eq hpiLt _,
              set_sub_block_eq (by rw [List.length_set]; omega) _]
          · rw [treeEdges_root, treeEdges_root, subEdges_append, subEdges_append,
              subEdges_cons, subEdges_cons, hedges']
          · rw [treeChans_root, treeChans_root, subInteriors_append, subInteriors_append,
              subInteriors_cons, subInteriors_cons, hchans']
        · intro M₀ N₀ v₀ hv₀ h1 h2
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h1
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contSEx' M₀ N₀ v₀ hv₀ h1 h2
          refine ⟨.root m ms (l ++ n' :: r),
            Step.rootSubtree stepn (stepAvoids_of_chansM_le (le_of_eq hchans')),
            ?_, ?_, ?_, rfl⟩
          · simp only [treeBodiesM_root]
            exact wrap_bodiesM_sub hbodies' m ms l r
          · simp only [treeEdgesM_root, subEdgesM_middle, hedges']
          · simp only [treeChansM_root, subChansM_middle, hchans']
        · intro M₀ N₀ v₀ hv₀ h1 h2
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h1
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contREx' M₀ N₀ v₀ hv₀ h1 h2
          refine ⟨.root m ms (l ++ n' :: r),
            Step.rootSubtree stepn (stepAvoids_of_chansM_le (le_of_eq hchans')),
            ?_, ?_, ?_, rfl⟩
          · simp only [treeBodiesM_root]
            exact wrap_bodiesM_sub hbodies' m ms l r
          · simp only [treeEdgesM_root, subEdgesM_middle, hedges']
          · simp only [treeChansM_root, subChansM_middle, hchans']
        · intro M₀ N₀ b h1 h2
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h1
          rw [treeBodies_root, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contClose' M₀ N₀ b h1 h2
          refine ⟨.root m ms (l ++ n' :: r),
            Step.rootSubtree stepn (stepAvoids_of_chansM_le
              (Multiset.le_iff_exists_add.mpr ⟨_, hchans'.symm⟩)),
            ?_, ?_, ?_, rfl⟩
          · simp only [treeBodiesM_root]
            exact wrap_bodiesM_sub hbodies' m ms l r
          · simp only [treeEdgesM_root]
            exact wrap_edgesM_sub hedges' ms l r
          · simp only [treeChansM_root]
            exact wrap_chansM_sub hchans' ms l r
  | .node dc m ms ns, hty, hnd, e, c, d, hedge => by
      have htyN : ∃ r0 A0, TypedAt r0 A0 (.node dc m ms ns) := by
        rcases hty with h | h
        · cases h
        · exact h
      rw [treeEdges_node] at hedge
      rcases getElem?_append_split hedge with ⟨hlt, h'⟩ | ⟨hge, h'⟩
      · rcases childEdges_locate ms h' with ⟨l, ch, r, rfl, hd⟩ | ⟨l, c₀, ch, r, e', rfl, h'', hmeas⟩
        · -- the edge is a child edge of this node: fire here
          obtain ⟨r0, A0, htyN'⟩ := htyN
          cases htyN' with
          | @node Θ xp rp Ap _ _ _ hsingle hhas tym hch hsub =>
          have hchmem : (Chan.var_Chan c, ch) ∈ l ++ (Chan.var_Chan c, ch) :: r :=
            List.mem_append.mpr (.inr (List.mem_cons_self ..))
          obtain ⟨rc, Ac, htyAt⟩ := hch.typedAt_of_mem hchmem
          cases ch with
          | root _ _ _ => cases htyAt
          | node dch mc msc nsc =>
          cases dch with
          | var_Chan dx =>
          have hdx : d = dx := hd
          subst hdx
          rw [treeChans_node, List.nodup_cons] at hnd
          obtain ⟨hhead, hnd'⟩ := hnd
          obtain ⟨hndLI, hndS, hdisjS⟩ := List.nodup_append.mp hnd'
          obtain ⟨hndL, hndI, hdisjLI⟩ := List.nodup_append.mp hndLI
          have hclabmem : c ∈ (l ++ (Chan.var_Chan c, Tree.node (Chan.var_Chan d) mc msc nsc)
              :: r).map (fun p => chanIndex p.1) :=
            List.mem_map.mpr ⟨(Chan.var_Chan c, _), hchmem, rfl⟩
          have hdint : d ∈ childInteriors (l ++ (Chan.var_Chan c,
              Tree.node (Chan.var_Chan d) mc msc nsc) :: r) := by
            rw [childInteriors_append, childInteriors_cons]
            refine List.mem_append.mpr (.inr (List.mem_append.mpr (.inl ?_)))
            rw [treeChans_node]
            exact List.mem_cons_self ..
          have hoccm : occurs c m = 1 :=
            tym.occurs1 (hch.pos_of_label (List.mem_map.mpr ⟨(Chan.var_Chan c, _), hchmem, rfl⟩))
          have hd0m : occurs d m = 0 := by
            by_contra hocc
            have hpc := TLLC.Process.dynOccursCount tym d
            rcases hch.support d (by rw [← hpc]; exact hocc) with rfl | hmemd
            · exact hhead (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hdint))))
            · exact (hdisjLI d hmemd d hdint) rfl
          cases htyAt with
          | @node Θc _ _ _ _ _ _ hsingleC hhasC tymC hchC hsubC =>
          have hoccmc : occurs d mc = 1 := tymC.occurs1 hhasC.pos_true
          have hc0mc : occurs c mc = 0 := by
            by_contra hocc
            have hpc := TLLC.Process.dynOccursCount tymC c
            rcases hchC.support c (by rw [← hpc]; exact hocc) with rfl | hmem
            · exact (hdisjLI c hclabmem c hdint) rfl
            · refine (hdisjLI c hclabmem c ?_) rfl
              rw [childInteriors_append, childInteriors_cons]
              refine List.mem_append.mpr (.inr (List.mem_append.mpr (.inl ?_)))
              rw [treeChans_node]
              refine List.mem_cons_of_mem _ ?_
              exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hmem)))
          refine ⟨0, 1 + (childBodies l).length, by omega, ⟨m, ?_, ?_, ?_⟩,
            ⟨mc, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
          · rw [treeBodies_node]
            exact List.getElem?_cons_zero
          · rw [hoccm]
            omega
          · exact hd0m
          · rw [treeBodies_node, childBodies_append, childBodies_cons]
            exact getElem?_cons_append_block (by
              rw [treeBodies_node]
              exact List.getElem?_cons_zero)
          · rw [hoccmc]
            omega
          · exact hc0mc
          · -- fire the parent-send rule
            intro M₀ N₀ o₀ hpiS hpjS
            rw [treeBodies_node, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_node, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            refine ⟨.node (Chan.var_Chan xp) (M₀.eval (.pure (.chan (Chan.var_Chan c))))
              (l ++ (Chan.var_Chan c, .node (Chan.var_Chan d)
                (N₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan d)) .im .L))) msc nsc) :: r) ns,
              Step.nodeSendIm, ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_node, treeBodies_node, childBodies_append, childBodies_append,
                childBodies_cons, childBodies_cons, treeBodies_node, treeBodies_node,
                List.set_cons_zero,
                show 1 + (childBodies l).length = (childBodies l).length + 1 from by omega,
                List.set_cons_succ,
                set_append_lt _ (by
                  simp [List.length_append, List.length_cons]) _,
                set_append_ge _ (Nat.le_refl _) _, Nat.sub_self,
                set_append_lt _ (by simp) _,
                List.set_cons_zero]
            · rw [treeEdges_node, treeEdges_node, childEdges_append, childEdges_append,
                childEdges_cons, childEdges_cons, treeEdges_node, treeEdges_node]
              rfl
            · rw [treeChans_node, treeChans_node, childInteriors_append, childInteriors_append,
                childInteriors_cons, childInteriors_cons, treeChans_node, treeChans_node,
                labels_surgery l r (Chan.var_Chan c)
                  (Tree.node (Chan.var_Chan d)
                    (N₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan d)) .im .L))) msc nsc)
                  (Tree.node (Chan.var_Chan d)
                    (N₀.eval (.recv (.chan (Chan.var_Chan d)) .im)) msc nsc)]
          · -- fire the parent-receive rule
            intro M₀ N₀ o₀ hpjS hpiS
            rw [treeBodies_node, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_node, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            refine ⟨.node (Chan.var_Chan xp) (M₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan c)) .im .L)))
              (l ++ (Chan.var_Chan c, .node (Chan.var_Chan d)
                (N₀.eval (.pure (.chan (Chan.var_Chan d)))) msc nsc) :: r) ns,
              Step.nodeRecvIm, ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_node, treeBodies_node, childBodies_append, childBodies_append,
                childBodies_cons, childBodies_cons, treeBodies_node, treeBodies_node,
                List.set_cons_zero,
                show 1 + (childBodies l).length = (childBodies l).length + 1 from by omega,
                List.set_cons_succ,
                set_append_lt _ (by
                  simp [List.length_append, List.length_cons]) _,
                set_append_ge _ (Nat.le_refl _) _, Nat.sub_self,
                set_append_lt _ (by simp) _,
                List.set_cons_zero]
            · rw [treeEdges_node, treeEdges_node, childEdges_append, childEdges_append,
                childEdges_cons, childEdges_cons, treeEdges_node, treeEdges_node]
              rfl
            · rw [treeChans_node, treeChans_node, childInteriors_append, childInteriors_append,
                childInteriors_cons, childInteriors_cons, treeChans_node, treeChans_node,
                labels_surgery l r (Chan.var_Chan c)
                  (Tree.node (Chan.var_Chan d)
                    (N₀.eval (.pure (.chan (Chan.var_Chan d)))) msc nsc)
                  (Tree.node (Chan.var_Chan d)
                    (N₀.eval (.app (.send (.chan (Chan.var_Chan d)) .im) o₀ .im)) msc nsc)]
          · -- fire the parent-send rule (explicit): dispatch on the parent endpoint
            intro M₀ N₀ v₀ hv₀ hpiS hpjS
            rw [treeBodies_node, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_node, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            by_cases hfree : Dynamic.occurs xp v₀ = 0
            · refine ⟨.node (Chan.var_Chan xp) (M₀.eval (.pure (.chan (Chan.var_Chan c))))
                (sendExChildren v₀ (Chan.var_Chan c) (Chan.var_Chan d) N₀ msc nsc (l ++ r)) ns,
                Step.nodeSendEx hv₀ hfree, ?_, ?_, ?_, rfl⟩
              · simp only [treeBodiesM_root, treeBodiesM_node, sendExChildren,
                  childBodiesM_insertChild, childBodiesM_mergeChildren, childBodiesM_middle]
                rw [← childBodiesM_split v₀ (l ++ r)]
                simp only [← Multiset.singleton_add]
                abel
              · simp only [treeEdgesM_root, treeEdgesM_node, sendExChildren,
                  childEdgesM_insertChild, childEdgesM_mergeChildren, childEdgesM_middle,
                  childChan, chanIndex]
                rw [← childEdgesM_split v₀ (l ++ r)]
                simp only [← Multiset.singleton_add]
                abel
              · simp only [treeChansM_root, treeChansM_node, sendExChildren,
                  childChansM_insertChild, childChansM_mergeChildren, childChansM_middle,
                  chanIndex]
                rw [← childChansM_split v₀ (l ++ r)]
                simp only [← Multiset.singleton_add]
                abel
            · refine ⟨.node (Chan.var_Chan xp)
                (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan d)) .ex .L)))
                (forwardChildren v₀ (Chan.var_Chan c) (Chan.var_Chan d) M₀ msc (l ++ r) ns) nsc,
                Step.nodeForward hv₀ hfree, ?_, ?_, ?_, rfl⟩
              · simp only [treeBodiesM_root, treeBodiesM_node, forwardChildren,
                  childBodiesM_insertChild, childBodiesM_mergeChildren, childBodiesM_middle]
                rw [← childBodiesM_split v₀ (l ++ r)]
                simp only [← Multiset.singleton_add]
                abel
              · simp only [treeEdgesM_root, treeEdgesM_node, forwardChildren,
                  childEdgesM_insertChild, childEdgesM_mergeChildren, childEdgesM_middle,
                  childChan, chanIndex]
                rw [sortPair_comm d c]
                rw [← childEdgesM_split v₀ (l ++ r)]
                simp only [← Multiset.singleton_add]
                abel
              · simp only [treeChansM_root, treeChansM_node, forwardChildren,
                  childChansM_insertChild, childChansM_mergeChildren, childChansM_middle,
                  chanIndex]
                rw [← childChansM_split v₀ (l ++ r)]
                simp only [← Multiset.singleton_add]
                abel
          · -- fire the parent-receive rule (explicit)
            intro M₀ N₀ v₀ hv₀ hpjS hpiS
            rw [treeBodies_node, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_node, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            refine ⟨.node (Chan.var_Chan xp) (M₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan c)) .ex .L)))
              (recvExChildren v₀ (Chan.var_Chan c) (Chan.var_Chan d) N₀ msc nsc (l ++ r)) ns,
              Step.nodeRecvEx hv₀, ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_root, treeBodiesM_node, recvExChildren,
                childBodiesM_insertChild, childBodiesM_mergeChildren, childBodiesM_middle]
              rw [← childBodiesM_split v₀ msc]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeEdgesM_root, treeEdgesM_node, recvExChildren,
                childEdgesM_insertChild, childEdgesM_mergeChildren, childEdgesM_middle,
                childChan, chanIndex]
              rw [← childEdgesM_split v₀ msc]
              simp only [← Multiset.singleton_add]
              abel
            · simp only [treeChansM_root, treeChansM_node, recvExChildren,
                childChansM_insertChild, childChansM_mergeChildren, childChansM_middle,
                chanIndex]
              rw [← childChansM_split v₀ msc]
              simp only [← Multiset.singleton_add]
              abel
          · -- fire the close rules
            intro M₀ N₀ b hpiS hpjS
            rw [treeBodies_node, List.getElem?_cons_zero] at hpiS
            obtain rfl := Option.some.inj hpiS
            rw [treeBodies_node, childBodies_append, childBodies_cons] at hpjS
            rw [getElem?_cons_append_block (L := childBodies l)
              (B := treeBodies (Tree.node (Chan.var_Chan d) mc msc nsc))
              (R := childBodies r) (S := subBodies ns)
              (by rw [treeBodies_node]; exact List.getElem?_cons_zero)] at hpjS
            obtain rfl := Option.some.inj hpjS
            refine ⟨.node (Chan.var_Chan xp) (M₀.eval (.pure .one)) (l ++ r)
              (ns ++ [Tree.root (N₀.eval (.pure .one)) msc nsc]), ?_, ?_, ?_, ?_, rfl⟩
            · cases b
              · exact Step.nodeWait
              · exact Step.nodeClose
            · simp only [treeBodiesM_root, treeBodiesM_node, childBodiesM_middle,
                subBodiesM_append, subBodiesM_cons, subBodiesM_nil, ← Multiset.singleton_add]
              abel
            · simp only [treeEdgesM_root, treeEdgesM_node, childEdgesM_middle,
                subEdgesM_append, subEdgesM_cons, subEdgesM_nil, childChan, chanIndex,
                ← Multiset.singleton_add]
              abel
            · simp only [treeChansM_root, treeChansM_node, childChansM_middle,
                subChansM_append, subChansM_cons, subChansM_nil, chanIndex,
                ← Multiset.singleton_add]
              abel
        · -- the edge lies inside a child: recurse and wrap
          obtain ⟨r0, A0, htyN'⟩ := htyN
          cases htyN' with
          | @node Θ xp rp Ap _ _ _ hsingle hhas tym hch hsub =>
          have hchmem : (c₀, ch) ∈ l ++ (c₀, ch) :: r :=
            List.mem_append.mpr (.inr (List.mem_cons_self ..))
          obtain ⟨rc, Ac, htyAt⟩ := hch.typedAt_of_mem hchmem
          have hndch : (treeChans ch).Nodup := by
            rw [treeChans_node, List.nodup_cons] at hnd
            obtain ⟨_, hnd'⟩ := hnd
            obtain ⟨hndLI, _, _⟩ := List.nodup_append.mp hnd'
            obtain ⟨_, hndI, _⟩ := List.nodup_append.mp hndLI
            exact (treeChans_sublist_childInteriors hchmem).nodup hndI
          obtain ⟨pi', pj', hpij', ⟨bpi, hpib, hpic, hpid0⟩, ⟨bpj, hpjb, hpjd, hpjc0⟩,
            contS', contR', contSEx', contREx', contClose'⟩ := edge_replay_gen ch (.inr ⟨rc, Ac, htyAt⟩) hndch h''
          have hpiLt : pi' < (treeBodies ch).length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hpib
            cases hpib
          have hpjLt : pj' < (treeBodies ch).length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hpjb
            cases hpjb
          refine ⟨1 + (childBodies l).length + pi', 1 + (childBodies l).length + pj',
            by omega, ⟨bpi, ?_, hpic, hpid0⟩, ⟨bpj, ?_, hpjd, hpjc0⟩, ?_, ?_, ?_, ?_, ?_⟩
          · rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt]
            exact hpib
          · rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt]
            exact hpjb
          · intro M₀ N₀ o₀ h1 h2
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h1
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contS' M₀ N₀ o₀ h1 h2
            refine ⟨.node (Chan.var_Chan xp) m (l ++ (c₀, ch') :: r) ns,
              Step.nodeChild stepch (fun x hx hnx => absurd (hchans' ▸ hx) hnx),
              ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_node, treeBodies_node, childBodies_append, childBodies_append,
                childBodies_cons, childBodies_cons, hbodies',
                set_block_eq hpiLt _,
                set_block_eq (by rw [List.length_set]; omega) _]
            · rw [treeEdges_node, treeEdges_node, childEdges_append, childEdges_append,
                childEdges_cons, childEdges_cons, hedges', hcc']
            · rw [treeChans_node, treeChans_node, childInteriors_append, childInteriors_append,
                childInteriors_cons, childInteriors_cons, hchans',
                labels_surgery l r c₀ ch' ch]
          · intro M₀ N₀ o₀ h1 h2
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h1
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contR' M₀ N₀ o₀ h1 h2
            refine ⟨.node (Chan.var_Chan xp) m (l ++ (c₀, ch') :: r) ns,
              Step.nodeChild stepch (fun x hx hnx => absurd (hchans' ▸ hx) hnx),
              ?_, ?_, ?_, rfl⟩
            · rw [treeBodies_node, treeBodies_node, childBodies_append, childBodies_append,
                childBodies_cons, childBodies_cons, hbodies',
                set_block_eq hpiLt _,
                set_block_eq (by rw [List.length_set]; omega) _]
            · rw [treeEdges_node, treeEdges_node, childEdges_append, childEdges_append,
                childEdges_cons, childEdges_cons, hedges', hcc']
            · rw [treeChans_node, treeChans_node, childInteriors_append, childInteriors_append,
                childInteriors_cons, childInteriors_cons, hchans',
                labels_surgery l r c₀ ch' ch]
          · intro M₀ N₀ v₀ hv₀ h1 h2
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h1
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contSEx' M₀ N₀ v₀ hv₀ h1 h2
            refine ⟨.node (Chan.var_Chan xp) m (l ++ (c₀, ch') :: r) ns,
              Step.nodeChild stepch (stepAvoids_of_chansM_le (le_of_eq hchans')),
              ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_node]
              exact wrap_bodiesM_child hbodies' m l r c₀ ns
            · simp only [treeEdgesM_node, childEdgesM_middle, hedges', hcc']
            · simp only [treeChansM_node, childChansM_middle, hchans']
          · intro M₀ N₀ v₀ hv₀ h1 h2
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h1
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contREx' M₀ N₀ v₀ hv₀ h1 h2
            refine ⟨.node (Chan.var_Chan xp) m (l ++ (c₀, ch') :: r) ns,
              Step.nodeChild stepch (stepAvoids_of_chansM_le (le_of_eq hchans')),
              ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_node]
              exact wrap_bodiesM_child hbodies' m l r c₀ ns
            · simp only [treeEdgesM_node, childEdgesM_middle, hedges', hcc']
            · simp only [treeChansM_node, childChansM_middle, hchans']
          · intro M₀ N₀ b h1 h2
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpiLt] at h1
            rw [treeBodies_node, childBodies_append, childBodies_cons,
              getElem?_block_eq hpjLt] at h2
            obtain ⟨ch', stepch, hbodies', hedges', hchans', hcc'⟩ := contClose' M₀ N₀ b h1 h2
            refine ⟨.node (Chan.var_Chan xp) m (l ++ (c₀, ch') :: r) ns,
              Step.nodeChild stepch (stepAvoids_of_chansM_le
                (Multiset.le_iff_exists_add.mpr ⟨_, hchans'.symm⟩)),
              ?_, ?_, ?_, rfl⟩
            · simp only [treeBodiesM_node]
              exact wrap_bodiesM_child hbodies' m l r c₀ ns
            · simp only [treeEdgesM_node]
              exact wrap_edgesM_child hedges' hcc' l r c₀ ns
            · simp only [treeChansM_node]
              exact wrap_chansM_child_cons hchans' l r c₀ ns
      · obtain ⟨l, n, r, e', rfl, h'', hmeas⟩ := subEdges_locate ns h'
        obtain ⟨r0, A0, htyN'⟩ := htyN
        cases htyN' with
        | @node Θ xp rp Ap _ _ _ hsingle hhas tym hch hsub =>
        have hnmem : n ∈ l ++ n :: r := List.mem_append.mpr (.inr (List.mem_cons_self ..))
        have htyn := hsub.typed_of_mem hnmem
        have hndn : (treeChans n).Nodup := by
          rw [treeChans_node, List.nodup_cons] at hnd
          obtain ⟨_, hnd'⟩ := hnd
          obtain ⟨_, hndS, _⟩ := List.nodup_append.mp hnd'
          exact (treeChans_sublist_subInteriors hnmem).nodup hndS
        obtain ⟨pi', pj', hpij', ⟨bpi, hpib, hpic, hpid0⟩, ⟨bpj, hpjb, hpjd, hpjc0⟩,
          contS', contR', contSEx', contREx', contClose'⟩ := edge_replay_gen n (.inl htyn) hndn h''
        have hpiLt : pi' < (treeBodies n).length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hpib
          cases hpib
        have hpjLt : pj' < (treeBodies n).length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hpjb
          cases hpjb
        refine ⟨1 + (childBodies ms).length + (subBodies l).length + pi',
          1 + (childBodies ms).length + (subBodies l).length + pj',
          by omega, ⟨bpi, ?_, hpic, hpid0⟩, ⟨bpj, ?_, hpjd, hpjc0⟩, ?_, ?_, ?_, ?_, ?_⟩
        · rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt]
          exact hpib
        · rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt]
          exact hpjb
        · intro M₀ N₀ o₀ h1 h2
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h1
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contS' M₀ N₀ o₀ h1 h2
          refine ⟨.node (Chan.var_Chan xp) m ms (l ++ n' :: r),
            Step.nodeSubtree stepn (fun x hx hnx => absurd (hchans' ▸ hx) hnx),
            ?_, ?_, ?_, rfl⟩
          · rw [treeBodies_node, treeBodies_node, subBodies_append, subBodies_append,
              subBodies_cons, subBodies_cons, hbodies',
              set_sub_block_eq hpiLt _,
              set_sub_block_eq (by rw [List.length_set]; omega) _]
          · rw [treeEdges_node, treeEdges_node, subEdges_append, subEdges_append,
              subEdges_cons, subEdges_cons, hedges']
          · rw [treeChans_node, treeChans_node, subInteriors_append, subInteriors_append,
              subInteriors_cons, subInteriors_cons, hchans']
        · intro M₀ N₀ o₀ h1 h2
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h1
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contR' M₀ N₀ o₀ h1 h2
          refine ⟨.node (Chan.var_Chan xp) m ms (l ++ n' :: r),
            Step.nodeSubtree stepn (fun x hx hnx => absurd (hchans' ▸ hx) hnx),
            ?_, ?_, ?_, rfl⟩
          · rw [treeBodies_node, treeBodies_node, subBodies_append, subBodies_append,
              subBodies_cons, subBodies_cons, hbodies',
              set_sub_block_eq hpiLt _,
              set_sub_block_eq (by rw [List.length_set]; omega) _]
          · rw [treeEdges_node, treeEdges_node, subEdges_append, subEdges_append,
              subEdges_cons, subEdges_cons, hedges']
          · rw [treeChans_node, treeChans_node, subInteriors_append, subInteriors_append,
              subInteriors_cons, subInteriors_cons, hchans']
        · intro M₀ N₀ v₀ hv₀ h1 h2
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h1
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contSEx' M₀ N₀ v₀ hv₀ h1 h2
          refine ⟨.node (Chan.var_Chan xp) m ms (l ++ n' :: r),
            Step.nodeSubtree stepn (stepAvoids_of_chansM_le (le_of_eq hchans')),
            ?_, ?_, ?_, rfl⟩
          · simp only [treeBodiesM_node]
            exact wrap_bodiesM_sub hbodies' m ms l r
          · simp only [treeEdgesM_node, subEdgesM_middle, hedges']
          · simp only [treeChansM_node, subChansM_middle, hchans']
        · intro M₀ N₀ v₀ hv₀ h1 h2
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h1
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contREx' M₀ N₀ v₀ hv₀ h1 h2
          refine ⟨.node (Chan.var_Chan xp) m ms (l ++ n' :: r),
            Step.nodeSubtree stepn (stepAvoids_of_chansM_le (le_of_eq hchans')),
            ?_, ?_, ?_, rfl⟩
          · simp only [treeBodiesM_node]
            exact wrap_bodiesM_sub hbodies' m ms l r
          · simp only [treeEdgesM_node, subEdgesM_middle, hedges']
          · simp only [treeChansM_node, subChansM_middle, hchans']
        · intro M₀ N₀ b h1 h2
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpiLt] at h1
          rw [treeBodies_node, subBodies_append, subBodies_cons,
            getElem?_sub_block_eq hpjLt] at h2
          obtain ⟨n', stepn, hbodies', hedges', hchans', hcc'⟩ := contClose' M₀ N₀ b h1 h2
          refine ⟨.node (Chan.var_Chan xp) m ms (l ++ n' :: r),
            Step.nodeSubtree stepn (stepAvoids_of_chansM_le
              (Multiset.le_iff_exists_add.mpr ⟨_, hchans'.symm⟩)),
            ?_, ?_, ?_, rfl⟩
          · simp only [treeBodiesM_node]
            exact wrap_bodiesM_sub hbodies' m ms l r
          · simp only [treeEdgesM_node]
            exact wrap_edgesM_sub hedges' ms l r
          · simp only [treeChansM_node]
            exact wrap_chansM_sub_cons hchans' ms l r
termination_by t => treeMeasure t
decreasing_by
  all_goals simp only [treeMeasure]
  all_goals omega

/-- Navigation to an edge of a valid distinct tree: the two names of the edge have holders
among the bodies with the opposite name excluded, and the implicit-communication rules can
fire at it, in either orientation, replacing exactly those two bodies. -/
lemma edge_replay {t : Tree} (typed : Typed t) (hnd : (treeChans t).Nodup)
    {e : Nat} {c d : Nat} (hedge : getElem? (treeEdges t) e = some (c, d)) :
    ∃ (pi pj : Nat), pi ≠ pj ∧
      (∃ bpi, getElem? (treeBodies t) pi = some bpi ∧
        occurs c bpi ≠ 0 ∧ occurs d bpi = 0) ∧
      (∃ bpj, getElem? (treeBodies t) pj = some bpj ∧
        occurs d bpj ≠ 0 ∧ occurs c bpj = 0) ∧
      (∀ (M₀ N₀ : EvalCtx) (o₀ : Term),
        getElem? (treeBodies t) pi =
          some (M₀.eval (.app (.send (.chan (Chan.var_Chan c)) .im) o₀ .im)) →
        getElem? (treeBodies t) pj =
          some (N₀.eval (.recv (.chan (Chan.var_Chan d)) .im)) →
        ∃ t', Step t t' ∧
          treeBodies t' = ((treeBodies t).set pi
            (M₀.eval (.pure (.chan (Chan.var_Chan c))))).set pj
            (N₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan d)) .im .L))) ∧
          treeEdges t' = treeEdges t ∧ treeChans t' = treeChans t ∧
          childChan t' = childChan t) ∧
      (∀ (M₀ N₀ : EvalCtx) (o₀ : Term),
        getElem? (treeBodies t) pj =
          some (N₀.eval (.app (.send (.chan (Chan.var_Chan d)) .im) o₀ .im)) →
        getElem? (treeBodies t) pi =
          some (M₀.eval (.recv (.chan (Chan.var_Chan c)) .im)) →
        ∃ t', Step t t' ∧
          treeBodies t' = ((treeBodies t).set pi
            (M₀.eval (.pure (.pair o₀ (.chan (Chan.var_Chan c)) .im .L)))).set pj
            (N₀.eval (.pure (.chan (Chan.var_Chan d)))) ∧
          treeEdges t' = treeEdges t ∧ treeChans t' = treeChans t ∧
          childChan t' = childChan t) ∧
      (∀ (M₀ N₀ : EvalCtx) (v₀ : Term), Val v₀ →
        getElem? (treeBodies t) pi =
          some (M₀.eval (.app (.send (.chan (Chan.var_Chan c)) .ex) v₀ .ex)) →
        getElem? (treeBodies t) pj =
          some (N₀.eval (.recv (.chan (Chan.var_Chan d)) .ex)) →
        ∃ t', Step t t' ∧
          treeBodiesM t' + ({M₀.eval (.app (.send (.chan (Chan.var_Chan c)) .ex) v₀ .ex)} +
            {N₀.eval (.recv (.chan (Chan.var_Chan d)) .ex)}) =
          treeBodiesM t + ({M₀.eval (.pure (.chan (Chan.var_Chan c)))} +
            {N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan d)) .ex .L))}) ∧
          treeEdgesM t' = treeEdgesM t ∧ treeChansM t' = treeChansM t ∧
          childChan t' = childChan t) ∧
      (∀ (M₀ N₀ : EvalCtx) (v₀ : Term), Val v₀ →
        getElem? (treeBodies t) pj =
          some (N₀.eval (.app (.send (.chan (Chan.var_Chan d)) .ex) v₀ .ex)) →
        getElem? (treeBodies t) pi =
          some (M₀.eval (.recv (.chan (Chan.var_Chan c)) .ex)) →
        ∃ t', Step t t' ∧
          treeBodiesM t' + ({M₀.eval (.recv (.chan (Chan.var_Chan c)) .ex)} +
            {N₀.eval (.app (.send (.chan (Chan.var_Chan d)) .ex) v₀ .ex)}) =
          treeBodiesM t + ({M₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan c)) .ex .L))} +
            {N₀.eval (.pure (.chan (Chan.var_Chan d)))}) ∧
          treeEdgesM t' = treeEdgesM t ∧ treeChansM t' = treeChansM t ∧
          childChan t' = childChan t) ∧
      (∀ (M₀ N₀ : EvalCtx) (b : Bool),
        getElem? (treeBodies t) pi =
          some (M₀.eval (.close b (.chan (Chan.var_Chan c)))) →
        getElem? (treeBodies t) pj =
          some (N₀.eval (.close (!b) (.chan (Chan.var_Chan d)))) →
        ∃ t', Step t t' ∧
          treeBodiesM t' + ({M₀.eval (.close b (.chan (Chan.var_Chan c)))} +
            {N₀.eval (.close (!b) (.chan (Chan.var_Chan d)))}) =
          treeBodiesM t + ({M₀.eval (.pure .one)} + {N₀.eval (.pure .one)}) ∧
          treeEdgesM t' + {sortPair (c, d)} = treeEdgesM t ∧
          treeChansM t' + ({c} + {d}) = treeChansM t ∧
          childChan t' = childChan t) :=
  edge_replay_gen t (.inl typed) hnd hedge

end TLLC.Spawning
