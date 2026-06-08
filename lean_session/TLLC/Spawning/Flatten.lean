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

lemma erasePCtx_append_empty (pre : PCtx) {tail : PCtx} (emp : PEmpty tail) :
    PEmpty (erasePCtx pre ++ tail) := by
  induction pre with
  | nil => simpa using emp
  | cons _ pre ih => simpa using PEmpty.none ih

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

lemma PHas.proto {Θ x r A} (has : PHas Θ x r A) (wfΘ : ProcWf Θ) :
    [] ⊢ A : .proto := by
  induction has with
  | zero =>
    cases wfΘ with
    | one _ tyA => exact Static.Typed.crename tyA _
  | succ _ ih =>
    cases wfΘ with
    | none wfTail => exact Static.Typed.crename (ih wfTail) _
    | one wfTail _ => exact Static.Typed.crename (ih wfTail) _
    | both wfTail _ => exact Static.Typed.crename (ih wfTail) _

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

lemma bindEndpointAt_zero_agree_conv_source {Θ r A B}
    (tyA : [] ⊢ A : .proto) (tyB : [] ⊢ B : .proto) (eqAB : A ≃ B) :
    AgreeCSubst (.one r A :: .none :: erasePCtx Θ)
      (bindEndpointAt 0 (Chan.var_Chan 0)) (.one r B :: erasePCtx Θ) := by
  have agr := bindEndpointAt_zero_agree (Θ := Θ) (r := r) (A := A) tyA
  exact AgreeCSubst.conv (r := r) eqAB tyB agr

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

lemma shiftN_agree {Θ : PCtx} (n : Nat) (wfΘ : ProcWf Θ) :
    AgreeCSubst (nonePrefix n Θ) (fun x => Chan.var_Chan (x + n)) Θ := by
  induction n with
  | zero =>
    simpa [nonePrefix] using (AgreeCSubst.nil wfΘ)
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

lemma bindEndpointAt_zero_reserve_agree_conv {Θ r A B} (k : Nat)
    (tyA : [] ⊢ A : .proto) (tyB : [] ⊢ B : .proto) (eqAB : A ≃ B) :
    AgreeCSubst (.one r A :: nonePrefix (k + 1) (erasePCtx Θ))
      (Chan.var_Chan 0 .: fun x => Chan.var_Chan (x + (k + 2)))
      (.one r B :: erasePCtx Θ) := by
  have agr := bindEndpointAt_zero_reserve_agree (Θ := Θ) (r := r) (A := A) k tyA
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

lemma PMerge.erasePCtx_right_tail (pre : PCtx) {tail : PCtx} (emp : PEmpty tail) :
    PMerge (pre ++ tail) (erasePCtx pre ++ tail) (pre ++ tail) := by
  induction pre with
  | nil => simpa using emp.merge_self
  | cons slot pre ih =>
    cases slot with
    | none => simpa using PMerge.none ih
    | one _ _ => simpa using PMerge.oneL ih
    | both _ => simpa using PMerge.bothL ih

lemma PMerge.erasePCtx_right (Θ : PCtx) : PMerge Θ (erasePCtx Θ) Θ := by
  induction Θ with
  | nil => exact PMerge.nil
  | cons slot Θ ih =>
    cases slot with
    | none => simpa using PMerge.none ih
    | one _ _ => simpa using PMerge.oneL ih
    | both _ => simpa using PMerge.bothL ih

lemma PMerge.nonePrefix_one_erase_right_tail
    (reserve : Nat) (pre : PCtx) {tail : PCtx} (emp : PEmpty tail) {r A} :
    PMerge (nonePrefix (reserve + 1) (pre ++ tail))
      (nonePrefix reserve (.one r A :: erasePCtx pre ++ tail))
      (nonePrefix reserve (.one r A :: pre ++ tail)) := by
  induction reserve with
  | zero =>
    simpa using PMerge.oneR (PMerge.erasePCtx_right_tail pre emp)
  | succ reserve ih =>
    simpa [nonePrefix_succ] using PMerge.none ih

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

lemma bindEndpointAt_prefix_go {Θ r A} (pre : PCtx) (reserve : Nat)
    (singlePre : PCtxSingle pre) (wfpre : ProcWf pre) (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: nonePrefix reserve (pre ++ .none :: erasePCtx Θ))
      (prefixBindSubst reserve pre.length) (pre ++ .one r A :: erasePCtx Θ) := by
  induction pre generalizing reserve with
  | nil =>
    have agr := bindEndpointAt_zero_reserve_agree (Θ := Θ) (r := r) (A := A) reserve tyA
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
      | none wfTail =>
        have agrTail := ih (reserve + 1) singleTail wfTail
        have agr := AgreeCSubst.wk0 (x := reserve + 1) agrTail
        rw [prefixBindSubst_succ reserve pre.length] at agr
        simpa [nonePrefix_cons, nonePrefix_succ] using agr
    | one r0 A0 =>
      cases singlePre with
      | one singleTail =>
      cases wfpre with
      | one wfTail tyA0 =>
        have agrTail := ih (reserve + 1) singleTail wfTail
        have empAfter : PEmpty (erasePCtx pre ++ .none :: erasePCtx Θ) :=
          erasePCtx_append_empty pre (.none (erasePCtx_empty Θ))
        have tyPrefix : (.none :: nonePrefix reserve
              (.one r0 A0 :: erasePCtx pre ++ .none :: erasePCtx Θ)) ⨾
            ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
              .chan (Chan.var_Chan (reserve + 1)) : .ch r0 A0 := by
          have h := chanAtN (Θe := erasePCtx pre ++ .none :: erasePCtx Θ)
            (r := r0) (A := A0) empAfter tyA0 reserve
          have hw := TLLC.Dynamic.Typed.cweaken h
          simpa [nonePrefix_succ] using hw
        have mrgAfterReserve : PMerge
            (nonePrefix (reserve + 1) (pre ++ .none :: erasePCtx Θ))
            (nonePrefix reserve (.one r0 A0 :: erasePCtx pre ++ .none :: erasePCtx Θ))
            (nonePrefix reserve (.one r0 A0 :: pre ++ .none :: erasePCtx Θ)) :=
          PMerge.nonePrefix_one_erase_right_tail reserve pre (.none (erasePCtx_empty Θ))
        have mrg : PMerge
            (.one r A :: nonePrefix (reserve + 1) (pre ++ .none :: erasePCtx Θ))
            (.none :: nonePrefix reserve (.one r0 A0 :: erasePCtx pre ++ .none :: erasePCtx Θ))
            (.one r A :: nonePrefix reserve (.one r0 A0 :: pre ++ .none :: erasePCtx Θ)) :=
          PMerge.oneL mrgAfterReserve
        have agr := AgreeCSubst.wk1 (x := reserve + 1) mrg agrTail tyPrefix
        rw [prefixBindSubst_succ reserve pre.length] at agr
        simpa [nonePrefix_cons, nonePrefix_succ] using agr
    | both _ =>
      cases singlePre

lemma bindEndpointAt_prefix_agree {Θ r A} (pre : PCtx)
    (singlePre : PCtxSingle pre) (wfpre : ProcWf pre) (tyA : [] ⊢ A : .proto) :
    AgreeCSubst (.one r A :: pre ++ .none :: erasePCtx Θ)
      (bindEndpointAt 0 (Chan.var_Chan pre.length)) (pre ++ .one r A :: erasePCtx Θ) := by
  have agr := bindEndpointAt_prefix_go (Θ := Θ) (r := r) (A := A)
    pre 0 singlePre wfpre tyA
  rw [prefixBindSubst_self_zero pre.length] at agr
  simpa [nonePrefix] using agr

lemma bindEndpointAt_prefix_tail_go {tail r A} (pre : PCtx) (reserve : Nat)
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
  have agr := bindEndpointAt_prefix_tail_go (tail := tail) (r := r) (A := A)
    pre 0 singlePre wfpre wfTail tyA
  rw [prefixBindSubst_self_zero pre.length] at agr
  simpa [nonePrefix] using agr

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

lemma one_shift_proto_irrel {r A p} (tyA : [] ⊢ A : .proto)
    (ty : TLLC.Process.Typed
      (.one r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) :: []) p) :
    TLLC.Process.Typed (.one r A :: []) p := by
  let Ashift := A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
  have tyAshift : [] ⊢ Ashift : .proto := Static.Typed.crename tyA _
  have eqA : A ≃ Ashift :=
    ARS.conv_sym (Static.cren_conv0 (m := A) .refl ((· + 1) : Nat → Nat))
  have wfSource : ProcWf (.one r A :: []) := ProcWf.one ProcWf.nil tyA
  have agr0 : AgreeCSubst (.one r A :: []) Chan.var_Chan (.one r A :: []) :=
    AgreeCSubst.nil wfSource
  have agr : AgreeCSubst (.one r A :: []) Chan.var_Chan (.one r Ashift :: []) :=
    AgreeCSubst.conv (r := r) eqA tyAshift agr0
  have h := ty.csubstitution agr
  rw [show p[Chan.var_Chan; Term.var_Term] = p from by asimp] at h
  exact h

lemma procWf_append_empty_tail {pre tail : PCtx} (wfPre : ProcWf pre) (emp : PEmpty tail) :
    ProcWf (pre ++ tail) := by
  induction wfPre generalizing tail with
  | nil => simpa using emp.procWf
  | none _ ih => simpa using ProcWf.none (ih emp)
  | one _ tyA ih => simpa using ProcWf.one (ih emp) tyA
  | both _ tyA ih => simpa using ProcWf.both (ih emp) tyA

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

lemma PCtxSingle.append {pre tail : PCtx}
    (singlePre : PCtxSingle pre) (singleTail : PCtxSingle tail) :
    PCtxSingle (pre ++ tail) := by
  induction singlePre with
  | nil => simpa using singleTail
  | none _ ih => simpa using PCtxSingle.none ih
  | one _ ih => simpa using PCtxSingle.one ih

lemma procWf_append {pre tail : PCtx} (wfPre : ProcWf pre) (wfTail : ProcWf tail) :
    ProcWf (pre ++ tail) := by
  induction wfPre with
  | nil => simpa using wfTail
  | none _ ih => simpa using ProcWf.none ih
  | one _ tyA ih => simpa using ProcWf.one ih tyA
  | both _ tyA ih => simpa using ProcWf.both ih tyA

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

lemma flattenChildren_cons_prefix_typed {Θ r A body child children Θc pre}
    (singlePre : PCtxSingle pre) (wfPre : ProcWf pre) (tyA : [] ⊢ A : .proto)
    (tyTail : TLLC.Process.Typed (pre ++ .one r A :: erasePCtx Θ)
      (flattenChildren body children))
    (tyChild : TLLC.Process.Typed (.one (!r) A :: Θc)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term]))
    (empC : PEmpty Θc) :
    TLLC.Process.Typed (pre ++ .none :: erasePCtx Θ)
      (flattenChildren body ((Chan.var_Chan pre.length, child) :: children)) := by
  have tyParent : TLLC.Process.Typed (.one r A :: pre ++ .none :: erasePCtx Θ)
      ((flattenChildren body children)[bindEndpointAt 0 (Chan.var_Chan pre.length);
        Term.var_Term]) :=
    tyTail.csubstitution (bindEndpointAt_prefix_agree (Θ := Θ) (r := r) (A := A)
      pre singlePre wfPre tyA)
  have wfOuter : ProcWf (pre ++ .none :: erasePCtx Θ) :=
    procWf_append_empty_tail wfPre (.none (erasePCtx_empty Θ))
  obtain ⟨Θe, empE, mrg⟩ := TLLC.Process.procWf_emptyR wfOuter
  have tyChild' : TLLC.Process.Typed (.one (!r) A :: Θe)
      ((child.flattenAt).2[bindEndpointAt 0 (child.flattenAt).1; Term.var_Term]) :=
    one_empty_irrel tyChild empC empE
  cases h : child.flattenAt with
  | mk d p =>
    simp [flattenChildren, h]
    exact nu_par_typed tyA mrg tyParent (by simpa [h] using tyChild')

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

lemma ChildrenTyped.flattenChildren_typed_prefix {Θ children body pre}
    (tys : ChildrenTyped Θ children)
    (singlePre : PCtxSingle pre) (wfPre : ProcWf pre) (wfΘ : ProcWf Θ)
    (tyBody : TLLC.Process.Typed (pre ++ Θ) body)
    (validAt : ∀ {r A tree}, [] ⊢ A : .proto →
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) tree →
      TLLC.Process.Typed (.one r A :: [])
        ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term])) :
    TLLC.Process.Typed (pre ++ erasePCtx Θ)
      (flattenChildren body (shiftChildrenN pre.length children)) := by
  induction Θ generalizing children pre body with
  | nil =>
    cases tys
    simpa [shiftChildrenN] using tyBody
  | cons slot Θ ih =>
    cases slot with
    | none =>
      cases tys with
      | none tysTail =>
      cases wfΘ with
      | none wfTail =>
        have singlePre' : PCtxSingle (pre ++ ([Slot.none] : PCtx)) :=
          PCtxSingle.append singlePre (PCtxSingle.none PCtxSingle.nil)
        have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
          procWf_append wfPre (ProcWf.none ProcWf.nil)
        have tyBody' :
            TLLC.Process.Typed ((pre ++ ([Slot.none] : PCtx)) ++ Θ) body := by
          simpa [List.append_assoc] using tyBody
        have h := ih tysTail singlePre' wfPre' wfTail tyBody'
        simpa [List.append_assoc, shiftChildrenN_shiftChildren] using h
    | one r A =>
      cases tys with
      | @one _ _ _ child children tyChild tysTail =>
      cases wfΘ with
      | one wfTail tyA =>
        have singlePre' : PCtxSingle (pre ++ ([Slot.one r A] : PCtx)) :=
          PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)
        have wfPre' : ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
          procWf_append wfPre (ProcWf.one ProcWf.nil tyA)
        have tyBody' :
            TLLC.Process.Typed ((pre ++ ([Slot.one r A] : PCtx)) ++ Θ) body := by
          simpa [List.append_assoc] using tyBody
        have tyTail := ih tysTail singlePre' wfPre' wfTail tyBody'
        have tyChildBase := validAt tyA tyChild
        have h := flattenChildren_cons_prefix_typed (Θ := Θ) (r := r) (A := A)
          (body := body) (child := child)
          (children := shiftChildrenN (pre.length + 1) children) (Θc := [])
          (pre := pre) singlePre wfPre tyA (by
            simpa [List.append_assoc] using tyTail) tyChildBase PEmpty.nil
        simpa [shiftChildrenN_shiftChildren, shiftChildrenN_one_cons, List.append_assoc] using h
    | both _ =>
      cases tys

lemma ChildrenTyped.flattenChildren_typed {Θ children body}
    (tys : ChildrenTyped Θ children) (wfΘ : ProcWf Θ)
    (tyBody : TLLC.Process.Typed Θ body)
    (validAt : ∀ {r A tree}, [] ⊢ A : .proto →
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) tree →
      TLLC.Process.Typed (.one r A :: [])
        ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term])) :
    TLLC.Process.Typed (erasePCtx Θ) (flattenChildren body children) := by
  simpa using tys.flattenChildren_typed_prefix PCtxSingle.nil ProcWf.nil wfΘ tyBody validAt

lemma ChildrenTypedAt.flattenChildren_typed_prefix {Θ x r A children body pre}
    (tys : ChildrenTypedAt Θ x r A children)
    (singlePre : PCtxSingle pre) (wfPre : ProcWf pre) (wfΘ : ProcWf Θ)
    (tyBody : TLLC.Process.Typed (pre ++ Θ) body)
    (validAt : ∀ {r A tree}, [] ⊢ A : .proto →
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) tree →
      TLLC.Process.Typed (.one r A :: [])
        ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term])) :
    TLLC.Process.Typed (pre ++ eraseExcept Θ x)
      (flattenChildren body (shiftChildrenN pre.length children)) := by
  induction Θ generalizing x r A children pre body with
  | nil =>
    cases tys
  | cons slot Θ ih =>
    cases slot with
    | none =>
      cases tys with
      | none tysTail =>
      cases wfΘ with
      | none wfTail =>
        have singlePre' : PCtxSingle (pre ++ ([Slot.none] : PCtx)) :=
          PCtxSingle.append singlePre (PCtxSingle.none PCtxSingle.nil)
        have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
          procWf_append wfPre (ProcWf.none ProcWf.nil)
        have tyBody' :
            TLLC.Process.Typed ((pre ++ ([Slot.none] : PCtx)) ++ Θ) body := by
          simpa [List.append_assoc] using tyBody
        have h := ih tysTail singlePre' wfPre' wfTail tyBody'
        simpa [List.append_assoc, shiftChildrenN_shiftChildren] using h
    | one r0 A0 =>
      cases tys with
      | @parent Θp rp Ap childrenp tysChildren =>
        cases wfΘ with
        | one wfTail tyA0 =>
          have singlePre' : PCtxSingle (pre ++ ([Slot.one r A0] : PCtx)) :=
            PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)
          have wfPre' : ProcWf (pre ++ ([Slot.one r A0] : PCtx)) :=
            procWf_append wfPre (ProcWf.one ProcWf.nil tyA0)
          have tyBody' :
              TLLC.Process.Typed ((pre ++ ([Slot.one r A0] : PCtx)) ++ Θ) body := by
            simpa [List.append_assoc] using tyBody
          have h := tysChildren.flattenChildren_typed_prefix
            singlePre' wfPre' wfTail tyBody' validAt
          simpa [List.append_assoc, shiftChildrenN_shiftChildren] using h
      | @one _ xTail rPar APar rChild AChild child children tyChild tysTail =>
        cases wfΘ with
        | one wfTail tyA0 =>
          have singlePre' : PCtxSingle (pre ++ ([Slot.one r0 A0] : PCtx)) :=
            PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)
          have wfPre' : ProcWf (pre ++ ([Slot.one r0 A0] : PCtx)) :=
            procWf_append wfPre (ProcWf.one ProcWf.nil tyA0)
          have tyBody' :
              TLLC.Process.Typed ((pre ++ ([Slot.one r0 A0] : PCtx)) ++ Θ) body := by
            simpa [List.append_assoc] using tyBody
          have tyTail := ih tysTail singlePre' wfPre' wfTail tyBody'
          have wfKeep : ProcWf (eraseExcept Θ xTail) := procWf_eraseExcept wfTail xTail
          have tyChildBase := validAt tyA0 tyChild
          have h := flattenChildren_cons_prefix_tail_typed (tail := eraseExcept Θ xTail)
            (r := r0) (A := A0) (body := body) (child := child)
            (children := shiftChildrenN (pre.length + 1) children) (Θc := []) (pre := pre)
            singlePre wfPre wfKeep tyA0 (by
              simpa [List.append_assoc] using tyTail) tyChildBase PEmpty.nil
          simpa [shiftChildrenN_shiftChildren, shiftChildrenN_one_cons, List.append_assoc] using h
    | both _ =>
      cases tys

lemma ChildrenTypedAt.flattenChildren_typed {Θ x r A children body}
    (tys : ChildrenTypedAt Θ x r A children) (wfΘ : ProcWf Θ)
    (tyBody : TLLC.Process.Typed Θ body)
    (validAt : ∀ {r A tree}, [] ⊢ A : .proto →
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) tree →
      TLLC.Process.Typed (.one r A :: [])
        ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term])) :
    TLLC.Process.Typed (eraseExcept Θ x) (flattenChildren body children) := by
  simpa using tys.flattenChildren_typed_prefix PCtxSingle.nil ProcWf.nil wfΘ tyBody validAt

lemma Typed.flatten_typed_step {tree}
    (ty : Typed tree)
    (valid : ∀ {tree}, Typed tree → TLLC.Process.Typed [] tree.flatten)
    (validAt : ∀ {r A tree}, [] ⊢ A : .proto →
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) tree →
      TLLC.Process.Typed (.one r A :: [])
        ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term])) :
    TLLC.Process.Typed [] tree.flatten := by
  cases ty with
  | @root Θ m children subtrees singleΘ tym tyChildren tySubtrees =>
    have tyChildrenFlat : TLLC.Process.Typed (erasePCtx Θ)
        (flattenChildren (.tm m) children) :=
      tyChildren.flattenChildren_typed tym.procWf (TLLC.Process.Typed.exp tym) validAt
    have tySubtreesFlat : ∀ q, q ∈ flattenSubtrees subtrees → TLLC.Process.Typed [] q :=
      tySubtrees.flattenSubtrees_typed valid
    have tyBody : TLLC.Process.Typed (erasePCtx Θ) (flattenBody m children subtrees) :=
      flattenBody_typed tyChildrenFlat tySubtreesFlat
    simpa using tyBody.empty_irrel (erasePCtx_empty Θ) PEmpty.nil

lemma TypedAt.flattenAt_typed_step {r A tree} (tyA : [] ⊢ A : .proto)
    (ty : TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) tree)
    (valid : ∀ {tree}, Typed tree → TLLC.Process.Typed [] tree.flatten)
    (validAt : ∀ {r A tree}, [] ⊢ A : .proto →
      TypedAt r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) tree →
      TLLC.Process.Typed (.one r A :: [])
        ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term])) :
    TLLC.Process.Typed (.one r A :: [])
      ((tree.flattenAt).2[bindEndpointAt 0 (tree.flattenAt).1; Term.var_Term]) := by
  cases ty with
  | @node Θ x _ _ m children subtrees singleΘ has tym tyChildren tySubtrees =>
    have tyChildrenFlat : TLLC.Process.Typed (eraseExcept Θ x)
        (flattenChildren (.tm m) children) :=
      tyChildren.flattenChildren_typed tym.procWf (TLLC.Process.Typed.exp tym) validAt
    have tySubtreesFlat : ∀ q, q ∈ flattenSubtrees subtrees → TLLC.Process.Typed [] q :=
      tySubtrees.flattenSubtrees_typed valid
    have tyBody : TLLC.Process.Typed (eraseExcept Θ x) (flattenBody m children subtrees) :=
      flattenBody_typed tyChildrenFlat tySubtreesFlat
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
        PCtxSingle.append singlePre (PCtxSingle.none PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
        procWf_append wfPre (ProcWf.none ProcWf.nil)
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
        PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
        procWf_append wfPre (ProcWf.one ProcWf.nil tyA)
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.one r A] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have tyTail := ihTail (body := body) (pre := pre ++ ([Slot.one r A] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      have tyChildBase := ihChild tyA rfl
      have h := flattenChildren_cons_prefix_typed (Θ := Θ) (r := r) (A := A)
        (body := body) (child := child)
        (children := shiftChildrenN (pre.length + 1) children) (Θc := [])
        (pre := pre) singlePre wfPre tyA (by
          simpa [List.append_assoc] using tyTail) tyChildBase PEmpty.nil
      simpa [shiftChildrenN_shiftChildren, shiftChildrenN_one_cons, List.append_assoc] using h
  case atParent =>
    intro Θ r A children _ ihChildren body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | one wfTail tyA =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.one r A] : PCtx)) :=
        PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
        procWf_append wfPre (ProcWf.one ProcWf.nil tyA)
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
        PCtxSingle.append singlePre (PCtxSingle.none PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
        procWf_append wfPre (ProcWf.none ProcWf.nil)
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
        PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.one r0 A0] : PCtx)) :=
        procWf_append wfPre (ProcWf.one ProcWf.nil tyA0)
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
    intro _ _ _ _ singleΘ tym tyChildren tySubtrees _ _
    exact Typed.flatten_typed (.root singleΘ tym tyChildren tySubtrees)
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
        PCtxSingle.append singlePre (PCtxSingle.none PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
        procWf_append wfPre (ProcWf.none ProcWf.nil)
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
        PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
        procWf_append wfPre (ProcWf.one ProcWf.nil tyA)
      have tyBody' : TLLC.Process.Typed ((pre ++ ([Slot.one r A] : PCtx)) ++ Θ) body := by
        simpa [List.append_assoc] using tyBody
      have tyTail := ihTail (body := body) (pre := pre ++ ([Slot.one r A] : PCtx))
        singlePre' wfPre' wfTail tyBody'
      have tyChildBase := ihChild tyA rfl
      have h := flattenChildren_cons_prefix_typed (Θ := Θ) (r := r) (A := A)
        (body := body) (child := child)
        (children := shiftChildrenN (pre.length + 1) children) (Θc := [])
        (pre := pre) singlePre wfPre tyA (by
          simpa [List.append_assoc] using tyTail) tyChildBase PEmpty.nil
      simpa [shiftChildrenN_shiftChildren, shiftChildrenN_one_cons, List.append_assoc] using h
  case atParent =>
    intro Θ r A children _ ihChildren body pre singlePre wfPre wfΘ tyBody
    cases wfΘ with
    | one wfTail tyA =>
      have singlePre' : PCtxSingle (pre ++ ([Slot.one r A] : PCtx)) :=
        PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.one r A] : PCtx)) :=
        procWf_append wfPre (ProcWf.one ProcWf.nil tyA)
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
        PCtxSingle.append singlePre (PCtxSingle.none PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.none] : PCtx)) :=
        procWf_append wfPre (ProcWf.none ProcWf.nil)
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
        PCtxSingle.append singlePre (PCtxSingle.one PCtxSingle.nil)
      have wfPre' : ProcWf (pre ++ ([Slot.one r0 A0] : PCtx)) :=
        procWf_append wfPre (ProcWf.one ProcWf.nil tyA0)
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
