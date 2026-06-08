import Mathlib.Tactic
import TLLC.Process.CSubst
import TLLC.Spawning.Channel
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

/-! ## Process-context and substitution utilities -/

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

lemma nonePrefix_cons (n : Nat) (Θ : PCtx) :
    nonePrefix n (.none :: Θ) = nonePrefix (n + 1) Θ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nonePrefix_succ, ih]

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

lemma PHas.eraseExcept_shape {Θ x r L} (has : PHas Θ x r L) (wfΘ : ProcWf Θ) :
    ∃ tail B, [] ⊢ B : .proto ∧ L ≃ B ∧
      TLLC.Spawning.eraseExcept Θ x = nonePrefix x (.one r B :: erasePCtx tail) := by
  induction has with
  | zero =>
    cases wfΘ with
    | one wfTail tyB =>
      exact ⟨_, _, tyB, Static.cren_conv0 (m := _) .refl ((· + 1) : Nat → Nat), rfl⟩
  | succ hasTail ih =>
    cases wfΘ with
    | none wfTail =>
      obtain ⟨tail, B, tyB, eqB, hshape⟩ := ih wfTail
      exact ⟨tail, B, tyB,
        ARS.conv_trans (Static.cren_conv0 (m := _) .refl ((· + 1) : Nat → Nat)) eqB,
        by simp [hshape, nonePrefix_succ]⟩
    | one wfTail _ =>
      obtain ⟨tail, B, tyB, eqB, hshape⟩ := ih wfTail
      exact ⟨tail, B, tyB,
        ARS.conv_trans (Static.cren_conv0 (m := _) .refl ((· + 1) : Nat → Nat)) eqB,
        by simp [hshape, nonePrefix_succ]⟩
    | both wfTail _ =>
      obtain ⟨tail, B, tyB, eqB, hshape⟩ := ih wfTail
      exact ⟨tail, B, tyB,
        ARS.conv_trans (Static.cren_conv0 (m := _) .refl ((· + 1) : Nat → Nat)) eqB,
        by simp [hshape, nonePrefix_succ]⟩

lemma shiftN_agree {Θ : PCtx} (n : Nat) (wfΘ : ProcWf Θ) :
    AgreeCSubst (nonePrefix n Θ) (fun x => Chan.var_Chan (x + n)) Θ := by
  induction n with
  | zero =>
    simpa [nonePrefix] using (AgreeCSubst.nil wfΘ)
  | succ n ih =>
    have h := AgreeCSubst.pad ih
    simpa [nonePrefix_succ, funcomp, ren_Chan, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h

lemma bindEndpointAt_zero_reserve_tail_agree {tail r A} (k : Nat)
    (wfTail : ProcWf tail) (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: nonePrefix (k + 1) tail)
      (Chan.var_Chan 0 .: fun x => Chan.var_Chan (x + (k + 2)))
      (.one r A :: tail) := by
  have agr := AgreeCSubst.ty (r := r) (shiftN_agree (Θ := tail) (k + 1) wfTail) tyA
  simpa [up_Chan_Chan, funcomp, ren_Chan, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using agr

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

/-- The substitution produced while peeling an arbitrary prefix before the selected endpoint. The
parameter `reserve` counts how many prefix slots have already been turned into fresh all-empty slots
in the source context; `n` is the number of remaining prefix slots before the selected endpoint. -/
def prefixBindSubst (reserve n : Nat) : Nat → Chan :=
  fun i =>
    if i < n then Chan.var_Chan (reserve + 1 + i)
    else if i = n then Chan.var_Chan 0
    else Chan.var_Chan (i + reserve + 1)

lemma prefixBindSubst_succ (reserve n : Nat) :
    (Chan.var_Chan (reserve + 1) .: prefixBindSubst (reserve + 1) n) =
      prefixBindSubst reserve (n + 1) := by
  funext j
  cases j with
  | zero =>
    simp [prefixBindSubst]
  | succ i =>
    unfold prefixBindSubst
    by_cases hi : i < n
    · simp [hi, Nat.succ_lt_succ hi]
      omega
    · have hnotlt : ¬ i + 1 < n + 1 := by omega
      by_cases hieq : i = n
      · subst i
        simp
      · simp [hi, hieq, hnotlt]
        omega

lemma prefixBindSubst_self_zero (n : Nat) :
    prefixBindSubst 0 n = bindEndpointAt 0 (Chan.var_Chan n) := by
  funext i
  unfold prefixBindSubst bindEndpointAt
  simp
  by_cases hlt : i < n
  · have hne : i ≠ n := by omega
    simp [hlt, hne]
    omega
  · by_cases heq : i = n
    · simp [heq]
    · simp [hlt, heq]

lemma bindEndpointAt_zero_reserve_agree_conv {Θ r A B} (k : Nat)
    (tyA : [] ⊢ A : .proto) (tyB : [] ⊢ B : .proto) (eqAB : A ≃ B) :
    AgreeCSubst (.one r A :: nonePrefix (k + 1) (erasePCtx Θ))
      (Chan.var_Chan 0 .: fun x => Chan.var_Chan (x + (k + 2)))
      (.one r B :: erasePCtx Θ) := by
  have agr := bindEndpointAt_zero_reserve_tail_agree (tail := erasePCtx Θ)
    (r := r) (A := A) k (erasePCtx_empty Θ).procWf tyA
  exact AgreeCSubst.conv (r := r) eqAB tyB agr

lemma bindEndpointAt_nonePrefix_go_conv {Θ r A B} (n p : Nat) (hp : p ≤ n)
    (tyA : [] ⊢ A : .proto) (tyB : [] ⊢ B : .proto) (eqAB : A ≃ B) :
    AgreeCSubst (.one r A :: nonePrefix (n + 1) (erasePCtx Θ))
      (nonePrefixBindSubst n p) (nonePrefix p (.one r B :: erasePCtx Θ)) := by
  induction p with
  | zero =>
    have agr := bindEndpointAt_zero_reserve_agree_conv (Θ := Θ) (r := r)
      (A := A) (B := B) n tyA tyB eqAB
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

lemma bindEndpointAt_nonePrefix_agree_conv {Θ r A B} (n : Nat)
    (tyA : [] ⊢ A : .proto) (tyB : [] ⊢ B : .proto) (eqAB : A ≃ B) :
    AgreeCSubst (.one r A :: nonePrefix (n + 1) (erasePCtx Θ))
      (bindEndpointAt 0 (Chan.var_Chan n)) (nonePrefix n (.one r B :: erasePCtx Θ)) := by
  have agr := bindEndpointAt_nonePrefix_go_conv (Θ := Θ) (r := r) (A := A) (B := B)
    n n (Nat.le_refl n) tyA tyB eqAB
  rw [nonePrefixBindSubst_self n] at agr
  exact agr

lemma PHas_bindEndpointAt_eraseExcept_agree_conv {Θ x r L S}
    (has : PHas Θ x r L) (wfΘ : ProcWf Θ)
    (tyS : [] ⊢ S : .proto) (eqS : S ≃ L) :
    ∃ Θe, PEmpty Θe ∧ AgreeCSubst (.one r S :: Θe)
      (bindEndpointAt 0 (Chan.var_Chan x)) (eraseExcept Θ x) := by
  obtain ⟨tail, B, tyB, eqB, hshape⟩ := has.eraseExcept_shape wfΘ
  let Θe := nonePrefix (x + 1) (erasePCtx tail)
  refine ⟨Θe, nonePrefix_empty (erasePCtx_empty tail) (x + 1), ?_⟩
  have eqSB : S ≃ B := ARS.conv_trans eqS eqB
  have agr := bindEndpointAt_nonePrefix_agree_conv (Θ := tail) (r := r) (A := S) (B := B)
    x tyS tyB eqSB
  rw [hshape]
  simpa [Θe] using agr

lemma PHas_bindEndpointAt_eraseExcept_agree {Θ x r A}
    (has : PHas Θ x r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩))
    (wfΘ : ProcWf Θ) (tyA : [] ⊢ A : .proto) :
    ∃ Θe, PEmpty Θe ∧ AgreeCSubst (.one r A :: Θe)
      (bindEndpointAt 0 (Chan.var_Chan x)) (eraseExcept Θ x) := by
  exact PHas_bindEndpointAt_eraseExcept_agree_conv has wfΘ tyA
    (ARS.conv_sym (Static.cren_conv0 (m := A) .refl ((· + 1) : Nat → Nat)))

lemma chanAtN {Θe r A} (emp : PEmpty Θe) (tyA : [] ⊢ A : .proto) (n : Nat) :
    (nonePrefix n (.one r A :: Θe)) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
      .chan (Chan.var_Chan n) : .ch r A := by
  induction n with
  | zero =>
    simpa [nonePrefix] using TLLC.Process.chanAt0 emp tyA
  | succ n ih =>
    have h := TLLC.Dynamic.Typed.cweaken ih
    simpa [nonePrefix_succ] using h

lemma PMerge.erasePCtx_right (Θ : PCtx) : PMerge Θ (erasePCtx Θ) Θ := by
  induction Θ with
  | nil => exact PMerge.nil
  | cons slot Θ ih =>
    cases slot with
    | none => simpa using PMerge.none ih
    | one _ _ => simpa using PMerge.oneL ih
    | both _ => simpa using PMerge.bothL ih

lemma PMerge.nonePrefix_one_erase_right
    (reserve : Nat) (pre tail : PCtx) {r A} :
    PMerge (nonePrefix (reserve + 1) (pre ++ .none :: tail))
      (nonePrefix reserve (.one r A :: erasePCtx (pre ++ .none :: tail)))
      (nonePrefix reserve (.one r A :: pre ++ .none :: tail)) := by
  induction reserve with
  | zero =>
    simpa using PMerge.oneR (PMerge.erasePCtx_right (pre ++ .none :: tail))
  | succ reserve ih =>
    simpa [nonePrefix_succ] using PMerge.none ih

lemma bindEndpointAt_prefix_tail {tail r A} (pre : PCtx) (reserve : Nat)
    (singlePre : PCtxSingle pre) (wfpre : ProcWf pre) (wfTail : ProcWf tail)
    (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: nonePrefix reserve (pre ++ .none :: tail))
      (prefixBindSubst reserve pre.length) (pre ++ .one r A :: tail) := by
  induction pre generalizing reserve with
  | nil =>
    have agr := bindEndpointAt_zero_reserve_tail_agree (tail := tail) (r := r) (A := A)
      reserve wfTail tyA
    convert agr using 1
    · simp [nonePrefix_cons]
    · funext i
      cases i with
      | zero => simp [prefixBindSubst]
      | succ i => simp [prefixBindSubst, Nat.add_comm, Nat.add_left_comm]
  | cons slot pre ih =>
    cases slot with
    | none =>
      cases singlePre with
      | none singleTail =>
      cases wfpre with
      | none wfTailPre =>
        have agrTail := ih (reserve + 1) singleTail wfTailPre
        have agr := AgreeCSubst.wk0 (x := reserve + 1) agrTail
        rw [prefixBindSubst_succ reserve pre.length] at agr
        simpa [nonePrefix_cons, nonePrefix_succ] using agr
    | one r0 A0 =>
      cases singlePre with
      | one singleTail =>
      cases wfpre with
      | one wfTailPre tyA0 =>
        have agrTail := ih (reserve + 1) singleTail wfTailPre
        have empAfter : PEmpty (erasePCtx (pre ++ .none :: tail)) := erasePCtx_empty _
        have tyPrefix : (.none :: nonePrefix reserve
              (.one r0 A0 :: erasePCtx (pre ++ .none :: tail))) ⨾
            ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
              .chan (Chan.var_Chan (reserve + 1)) : .ch r0 A0 := by
          have h := chanAtN (Θe := erasePCtx (pre ++ .none :: tail))
            (r := r0) (A := A0) empAfter tyA0 reserve
          have hw := TLLC.Dynamic.Typed.cweaken h
          simpa [nonePrefix_succ] using hw
        have mrgAfterReserve : PMerge
            (nonePrefix (reserve + 1) (pre ++ .none :: tail))
            (nonePrefix reserve (.one r0 A0 :: erasePCtx (pre ++ .none :: tail)))
            (nonePrefix reserve (.one r0 A0 :: pre ++ .none :: tail)) :=
          PMerge.nonePrefix_one_erase_right reserve pre tail
        have mrg : PMerge
            (.one r A :: nonePrefix (reserve + 1) (pre ++ .none :: tail))
            (.none :: nonePrefix reserve (.one r0 A0 :: erasePCtx (pre ++ .none :: tail)))
            (.one r A :: nonePrefix reserve (.one r0 A0 :: pre ++ .none :: tail)) :=
          PMerge.oneL mrgAfterReserve
        have agr := AgreeCSubst.wk1 (x := reserve + 1) mrg agrTail tyPrefix
        rw [prefixBindSubst_succ reserve pre.length] at agr
        simpa [nonePrefix_cons, nonePrefix_succ] using agr
    | both _ =>
      cases singlePre

lemma bindEndpointAt_prefix_tail_agree {tail r A} (pre : PCtx)
    (singlePre : PCtxSingle pre) (wfpre : ProcWf pre) (wfTail : ProcWf tail)
    (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: pre ++ .none :: tail)
      (bindEndpointAt 0 (Chan.var_Chan pre.length)) (pre ++ .one r A :: tail) := by
  have agr := bindEndpointAt_prefix_tail (tail := tail) (r := r) (A := A)
    pre 0 singlePre wfpre wfTail tyA
  rw [prefixBindSubst_self_zero pre.length] at agr
  simpa [nonePrefix] using agr

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

/-! ## Flattening operation -/

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

/-- Shift every child-edge label by `n` channel binders. -/
def shiftChildrenN (n : Nat) : List (Chan × Tree) → List (Chan × Tree)
  | [] => []
  | (Chan.var_Chan x, child) :: children =>
      (Chan.var_Chan (x + n), child) :: shiftChildrenN n children

@[simp] lemma shiftChildrenN_nil (n : Nat) : shiftChildrenN n [] = [] := rfl

@[simp] lemma shiftChildrenN_cons (n x : Nat) (child : Tree)
    (children : List (Chan × Tree)) :
    shiftChildrenN n ((Chan.var_Chan x, child) :: children) =
      (Chan.var_Chan (x + n), child) :: shiftChildrenN n children := rfl

@[simp] lemma shiftChildrenN_zero (children : List (Chan × Tree)) :
    shiftChildrenN 0 children = children := by
  induction children with
  | nil => rfl
  | cons child children ih =>
    cases child with
    | mk c tree =>
      cases c
      simp [shiftChildrenN, ih]

lemma shiftChildrenN_shiftChildren (n : Nat) (children : List (Chan × Tree)) :
    shiftChildrenN n (shiftChildren children) = shiftChildrenN (n + 1) children := by
  induction children with
  | nil => rfl
  | cons child children ih =>
    cases child with
    | mk c tree =>
      cases c with
      | var_Chan x =>
        simp [shiftChildren, shiftChildrenN, ih]
        omega

lemma shiftChildrenN_one_cons (n : Nat) (child : Tree) (children : List (Chan × Tree)) :
    shiftChildrenN n ((Chan.var_Chan 0, child) :: shiftChildren children) =
      (Chan.var_Chan n, child) :: shiftChildrenN (n + 1) children := by
  simp [shiftChildrenN_shiftChildren]

/-! ## Typing support -/

lemma PCtxSingle.append {pre tail : PCtx}
    (singlePre : PCtxSingle pre) (singleTail : PCtxSingle tail) :
    PCtxSingle (pre ++ tail) := by
  induction singlePre with
  | nil => simpa using singleTail
  | none _ ih => simpa using PCtxSingle.none ih
  | one _ ih => simpa using PCtxSingle.one ih

lemma PCtxSingle.append_none {pre : PCtx} (singlePre : PCtxSingle pre) :
    PCtxSingle (pre ++ ([Slot.none] : PCtx)) :=
  PCtxSingle.append singlePre (PCtxSingle.none PCtxSingle.nil)

lemma PCtxSingle.append_one {pre : PCtx} {r A} (singlePre : PCtxSingle pre) :
    PCtxSingle (pre ++ ([Slot.one r A] : PCtx)) :=
  PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)

lemma procWf_append {pre tail : PCtx} (wfPre : ProcWf pre) (wfTail : ProcWf tail) :
    ProcWf (pre ++ tail) := by
  induction wfPre with
  | nil => simpa using wfTail
  | none _ ih => simpa using ProcWf.none ih
  | one _ tyA ih => simpa using ProcWf.one ih tyA
  | both _ tyA ih => simpa using ProcWf.both ih tyA

lemma ProcWf.append_none {pre : PCtx} (wfPre : ProcWf pre) :
    ProcWf (pre ++ ([Slot.none] : PCtx)) :=
  procWf_append wfPre (ProcWf.none ProcWf.nil)

lemma ProcWf.append_one {pre : PCtx} {r A} (wfPre : ProcWf pre)
    (tyA : [] ⊢ A : .proto) :
    ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
  procWf_append wfPre (ProcWf.one ProcWf.nil tyA)

lemma procWf_eraseExcept {Θ : PCtx} (wf : ProcWf Θ) (x : Nat) :
    ProcWf (eraseExcept Θ x) := by
  induction wf generalizing x with
  | nil =>
    cases x <;> simp [eraseExcept, ProcWf.nil]
  | none _ ih =>
    cases x with
    | zero => simpa using ProcWf.none (erasePCtx_empty _).procWf
    | succ x => simpa using ProcWf.none (ih x)
  | one _ tyA ih =>
    cases x with
    | zero => simpa using ProcWf.one (erasePCtx_empty _).procWf tyA
    | succ x => simpa using ProcWf.none (ih x)
  | both _ tyA ih =>
    cases x with
    | zero => simpa using ProcWf.both (erasePCtx_empty _).procWf tyA
    | succ x => simpa using ProcWf.none (ih x)

lemma flattenBody_typed {Θ m children subtrees}
    (tyChildren : TLLC.Process.Typed Θ (flattenChildren (.tm m) children))
    (tySubtrees : ∀ q, q ∈ flattenSubtrees subtrees → TLLC.Process.Typed [] q) :
    TLLC.Process.Typed Θ (flattenBody m children subtrees) := by
  simp [flattenBody]
  exact parAll_typed tyChildren tySubtrees

lemma flattenChildren_cons_prefix_tail_typed {tail r A body child children Θc pre}
    (singlePre : PCtxSingle pre) (wfPre : ProcWf pre) (wfTail : ProcWf tail)
    (tyA : [] ⊢ A : .proto)
    (tyTail : TLLC.Process.Typed (pre ++ .one r A :: tail)
      (flattenChildren body children))
    (tyChild : TLLC.Process.Typed (.one (!r) A :: Θc)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term]))
    (empC : PEmpty Θc) :
    TLLC.Process.Typed (pre ++ .none :: tail)
      (flattenChildren body ((Chan.var_Chan pre.length, child) :: children)) := by
  have tyParent : TLLC.Process.Typed (.one r A :: pre ++ .none :: tail)
      ((flattenChildren body children)[bindEndpointAt 0 (Chan.var_Chan pre.length);
        Term.var_Term]) :=
    tyTail.csubstitution (bindEndpointAt_prefix_tail_agree (tail := tail) (r := r) (A := A)
      pre singlePre wfPre wfTail tyA)
  have wfOuter : ProcWf (pre ++ .none :: tail) :=
    procWf_append wfPre (ProcWf.none wfTail)
  obtain ⟨Θe, empE, mrg⟩ := TLLC.Process.procWf_emptyR wfOuter
  have tyChild' : TLLC.Process.Typed (.one (!r) A :: Θe)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term]) :=
    one_empty_irrel tyChild empC empE
  cases h : child.flattenAt with
  | mk d p =>
    simp [flattenChildren, h]
    exact nu_par_typed tyA mrg tyParent (by simpa [h] using tyChild')

/-! ## Main theorems -/

/-- Lemma 5.85, root half: flattening a valid root spawning tree yields a well-typed process. -/
theorem Typed.flatten_typed {tree} (ty : Typed tree) :
    TLLC.Process.Typed [] tree.flatten := by
  refine Typed.rec
    (motive_1 := fun tree _ => TLLC.Process.Typed [] tree.flatten)
    (motive_2 := fun r Ashift tree _ =>
      ∀ {A}, [] ⊢ A : .proto →
        Ashift = A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ →
        TLLC.Process.Typed (.one r A :: [])
          ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term]))
    (motive_3 := fun Θ children _ =>
      ∀ {body pre}, PCtxSingle pre → ProcWf pre → ProcWf Θ →
        TLLC.Process.Typed (pre ++ Θ) body →
        TLLC.Process.Typed (pre ++ erasePCtx Θ)
          (flattenChildren body (shiftChildrenN pre.length children)))
    (motive_4 := fun Θ x _ _ children _ =>
      ∀ {body pre}, PCtxSingle pre → ProcWf pre → ProcWf Θ →
        TLLC.Process.Typed (pre ++ Θ) body →
        TLLC.Process.Typed (pre ++ eraseExcept Θ x)
          (flattenChildren body (shiftChildrenN pre.length children)))
    (motive_5 := fun trees _ =>
      ∀ q, q ∈ flattenSubtrees trees → TLLC.Process.Typed [] q)
    ?root ?node ?childrenNil ?childrenNone ?childrenOne ?atParent ?atNone ?atOne
    ?subsNil ?subsCons ty
  case root =>
    intro Θ m children subtrees _ tym _ _ ihChildren ihSubtrees
    have tyChildrenFlat : TLLC.Process.Typed (erasePCtx Θ)
        (flattenChildren (.tm m) children) := by
      simpa using ihChildren (body := .tm m) (pre := []) PCtxSingle.nil ProcWf.nil
        tym.procWf (TLLC.Process.Typed.exp tym)
    have tyBody : TLLC.Process.Typed (erasePCtx Θ) (flattenBody m children subtrees) :=
      flattenBody_typed tyChildrenFlat ihSubtrees
    simpa using tyBody.empty_irrel (erasePCtx_empty Θ) PEmpty.nil
  case node =>
    intro Θ x r _ m children subtrees _ has tym _ _ ihChildren ihSubtrees A tyA hEq
    subst hEq
    have tyChildrenFlat : TLLC.Process.Typed (eraseExcept Θ x)
        (flattenChildren (.tm m) children) := by
      simpa using ihChildren (body := .tm m) (pre := []) PCtxSingle.nil ProcWf.nil
        tym.procWf (TLLC.Process.Typed.exp tym)
    have tyBody : TLLC.Process.Typed (eraseExcept Θ x) (flattenBody m children subtrees) :=
      flattenBody_typed tyChildrenFlat ihSubtrees
    obtain ⟨Θe, empE, agr⟩ := PHas_bindEndpointAt_eraseExcept_agree has tym.procWf tyA
    have tySubst : TLLC.Process.Typed (.one r A :: Θe)
        ((flattenBody m children subtrees)[bindEndpointAt 0 (Chan.var_Chan x);
          Term.var_Term]) :=
      tyBody.csubstitution agr
    have tyFlat : TLLC.Process.Typed (.one r A :: [])
        ((flattenBody m children subtrees)[bindEndpointAt 0 (Chan.var_Chan x);
          Term.var_Term]) :=
      one_empty_irrel tySubst empE PEmpty.nil
    simpa [Tree.flattenAt] using tyFlat
  case childrenNil =>
    intro body pre _ _ _ tyBody
    simpa [shiftChildrenN] using tyBody
  case childrenNone =>
    intro Θ children _ ih body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | none wfTail =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.none] : PCtx)) :=
        PCtxSingle.append_none singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
        ProcWf.append_none wfPre
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.none] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have h := ih (body := body) (pre := pre ++ ([Slot.none] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      simpa [List.append_assoc, shiftChildrenN_shiftChildren] using h
  case childrenOne =>
    intro Θ r A child children _ _ ihChild ihTail body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | one wfTail tyA =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.one r A] : PCtx)) :=
        PCtxSingle.append_one singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
        ProcWf.append_one wfPre tyA
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.one r A] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have tyTail := ihTail (body := body) (pre := pre ++ ([Slot.one r A] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      have tyChildBase := ihChild tyA rfl
      have h := flattenChildren_cons_prefix_tail_typed (tail := erasePCtx Θ) (r := r) (A := A)
        (body := body) (child := child)
        (children := shiftChildrenN (pre.length + 1) children) (Θc := [])
        (pre := pre) singlePre wfPre (erasePCtx_empty Θ).procWf tyA (by
          simpa [List.append_assoc] using tyTail) tyChildBase PEmpty.nil
      simpa [shiftChildrenN_shiftChildren, shiftChildrenN_one_cons, List.append_assoc] using h
  case atParent =>
    intro Θ r A children _ ihChildren body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | one wfTail tyA =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.one r A] : PCtx)) :=
        PCtxSingle.append_one singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
        ProcWf.append_one wfPre tyA
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.one r A] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have h := ihChildren (body := body) (pre := pre ++ ([Slot.one r A] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      simpa [List.append_assoc, shiftChildrenN_shiftChildren] using h
  case atNone =>
    intro Θ x _ _ children _ ih body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | none wfTail =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.none] : PCtx)) :=
        PCtxSingle.append_none singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
        ProcWf.append_none wfPre
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.none] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have h := ih (body := body) (pre := pre ++ ([Slot.none] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      simpa [List.append_assoc, shiftChildrenN_shiftChildren] using h
  case atOne =>
    intro Θ x _ _ r0 A0 child children _ _ ihChild ihTail body pre singlePre wfPre
      wfΘ tyBody
    cases wfΘ with
    | one wfTail tyA0 =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.one r0 A0] : PCtx)) :=
        PCtxSingle.append_one singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.one r0 A0] : PCtx)) :=
        ProcWf.append_one wfPre tyA0
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.one r0 A0] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have tyTail := ihTail (body := body) (pre := pre ++ ([Slot.one r0 A0] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      have wfKeep : ProcWf (eraseExcept Θ x) := procWf_eraseExcept wfTail x
      have tyChildBase := ihChild tyA0 rfl
      have h := flattenChildren_cons_prefix_tail_typed (tail := eraseExcept Θ x)
        (r := r0) (A := A0) (body := body) (child := child)
        (children := shiftChildrenN (pre.length + 1) children) (Θc := []) (pre := pre)
        singlePre wfPre wfKeep tyA0 (by
          simpa [List.append_assoc] using tyTail) tyChildBase PEmpty.nil
      simpa [shiftChildrenN_shiftChildren, shiftChildrenN_one_cons, List.append_assoc] using h
  case subsNil =>
    intro q hq
    simp at hq
  case subsCons =>
    intro tree trees _ _ ihTree ihTrees q hq
    simp at hq
    rcases hq with hq | hq
    · subst hq
      exact ihTree
    · exact ihTrees q hq

/-- Lemma 5.85, node half: flattening a valid node yields a process typed by the exposed parent
endpoint. The statement exposes the raw protocol `A`; the `TypedAt` premise carries the one-step
lookup shift used by `PHas`. -/
theorem TypedAt.flattenAt_typed {r A tree} (tyA : [] ⊢ A : .proto)
    (ty : TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) tree) :
    TLLC.Process.Typed (.one r A :: [])
      ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term]) := by
  refine (TypedAt.rec
    (motive_1 := fun tree _ => TLLC.Process.Typed [] tree.flatten)
    (motive_2 := fun r Ashift tree _ =>
      ∀ {A}, [] ⊢ A : .proto →
        Ashift = A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ →
        TLLC.Process.Typed (.one r A :: [])
          ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term]))
    (motive_3 := fun Θ children _ =>
      ∀ {body pre}, PCtxSingle pre → ProcWf pre → ProcWf Θ →
        TLLC.Process.Typed (pre ++ Θ) body →
        TLLC.Process.Typed (pre ++ erasePCtx Θ)
          (flattenChildren body (shiftChildrenN pre.length children)))
    (motive_4 := fun Θ x _ _ children _ =>
      ∀ {body pre}, PCtxSingle pre → ProcWf pre → ProcWf Θ →
        TLLC.Process.Typed (pre ++ Θ) body →
        TLLC.Process.Typed (pre ++ eraseExcept Θ x)
          (flattenChildren body (shiftChildrenN pre.length children)))
    (motive_5 := fun trees _ =>
      ∀ q, q ∈ flattenSubtrees trees → TLLC.Process.Typed [] q)
    ?root ?node ?childrenNil ?childrenNone ?childrenOne ?atParent ?atNone ?atOne
    ?subsNil ?subsCons (t := ty)) tyA rfl
  case root =>
    intro Θ m children subtrees _ tym _ _ ihChildren ihSubtrees
    have tyChildrenFlat : TLLC.Process.Typed (erasePCtx Θ)
        (flattenChildren (.tm m) children) := by
      simpa using ihChildren (body := .tm m) (pre := []) PCtxSingle.nil ProcWf.nil
        tym.procWf (TLLC.Process.Typed.exp tym)
    have tyBody : TLLC.Process.Typed (erasePCtx Θ) (flattenBody m children subtrees) :=
      flattenBody_typed tyChildrenFlat ihSubtrees
    simpa using tyBody.empty_irrel (erasePCtx_empty Θ) PEmpty.nil
  case node =>
    intro Θ x r _ m children subtrees _ has tym _ _ ihChildren ihSubtrees A tyA hEq
    subst hEq
    have tyChildrenFlat : TLLC.Process.Typed (eraseExcept Θ x)
        (flattenChildren (.tm m) children) := by
      simpa using ihChildren (body := .tm m) (pre := []) PCtxSingle.nil ProcWf.nil
        tym.procWf (TLLC.Process.Typed.exp tym)
    have tyBody : TLLC.Process.Typed (eraseExcept Θ x) (flattenBody m children subtrees) :=
      flattenBody_typed tyChildrenFlat ihSubtrees
    obtain ⟨Θe, empE, agr⟩ := PHas_bindEndpointAt_eraseExcept_agree has tym.procWf tyA
    have tySubst : TLLC.Process.Typed (.one r A :: Θe)
        ((flattenBody m children subtrees)[bindEndpointAt 0 (Chan.var_Chan x);
          Term.var_Term]) :=
      tyBody.csubstitution agr
    have tyFlat : TLLC.Process.Typed (.one r A :: [])
        ((flattenBody m children subtrees)[bindEndpointAt 0 (Chan.var_Chan x);
          Term.var_Term]) :=
      one_empty_irrel tySubst empE PEmpty.nil
    simpa [Tree.flattenAt] using tyFlat
  case childrenNil =>
    intro body pre _ _ _ tyBody
    simpa [shiftChildrenN] using tyBody
  case childrenNone =>
    intro Θ children _ ih body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | none wfTail =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.none] : PCtx)) :=
        PCtxSingle.append_none singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
        ProcWf.append_none wfPre
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.none] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have h := ih (body := body) (pre := pre ++ ([Slot.none] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      simpa [List.append_assoc, shiftChildrenN_shiftChildren] using h
  case childrenOne =>
    intro Θ r A child children _ _ ihChild ihTail body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | one wfTail tyA =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.one r A] : PCtx)) :=
        PCtxSingle.append_one singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
        ProcWf.append_one wfPre tyA
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.one r A] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have tyTail := ihTail (body := body) (pre := pre ++ ([Slot.one r A] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      have tyChildBase := ihChild tyA rfl
      have h := flattenChildren_cons_prefix_tail_typed (tail := erasePCtx Θ) (r := r) (A := A)
        (body := body) (child := child)
        (children := shiftChildrenN (pre.length + 1) children) (Θc := [])
        (pre := pre) singlePre wfPre (erasePCtx_empty Θ).procWf tyA (by
          simpa [List.append_assoc] using tyTail) tyChildBase PEmpty.nil
      simpa [shiftChildrenN_shiftChildren, shiftChildrenN_one_cons, List.append_assoc] using h
  case atParent =>
    intro Θ r A children _ ihChildren body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | one wfTail tyA =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.one r A] : PCtx)) :=
        PCtxSingle.append_one singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
        ProcWf.append_one wfPre tyA
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.one r A] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have h := ihChildren (body := body) (pre := pre ++ ([Slot.one r A] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      simpa [List.append_assoc, shiftChildrenN_shiftChildren] using h
  case atNone =>
    intro Θ x _ _ children _ ih body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | none wfTail =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.none] : PCtx)) :=
        PCtxSingle.append_none singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
        ProcWf.append_none wfPre
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.none] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have h := ih (body := body) (pre := pre ++ ([Slot.none] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      simpa [List.append_assoc, shiftChildrenN_shiftChildren] using h
  case atOne =>
    intro Θ x _ _ r0 A0 child children _ _ ihChild ihTail body pre singlePre wfPre
      wfΘ tyBody
    cases wfΘ with
    | one wfTail tyA0 =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.one r0 A0] : PCtx)) :=
        PCtxSingle.append_one singlePre
      have wfPre' : ProcWf (pre ++ ([Slot.one r0 A0] : PCtx)) :=
        ProcWf.append_one wfPre tyA0
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.one r0 A0] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have tyTail := ihTail (body := body) (pre := pre ++ ([Slot.one r0 A0] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      have wfKeep : ProcWf (eraseExcept Θ x) := procWf_eraseExcept wfTail x
      have tyChildBase := ihChild tyA0 rfl
      have h := flattenChildren_cons_prefix_tail_typed (tail := eraseExcept Θ x)
        (r := r0) (A := A0) (body := body) (child := child)
        (children := shiftChildrenN (pre.length + 1) children) (Θc := []) (pre := pre)
        singlePre wfPre wfKeep tyA0 (by
          simpa [List.append_assoc] using tyTail) tyChildBase PEmpty.nil
      simpa [shiftChildrenN_shiftChildren, shiftChildrenN_one_cons, List.append_assoc] using h
  case subsNil =>
    intro q hq
    simp at hq
  case subsCons =>
    intro tree trees _ _ ihTree ihTrees q hq
    simp at hq
    rcases hq with hq | hq
    · subst hq
      exact ihTree
    · exact ihTrees q hq

end TLLC.Spawning
