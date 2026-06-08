import TLLC.Dynamic.CSubst

/-!
# Channel occurrences and linearity

Port of `coq_session/dyn_occurs.v`: the channel-occurrence / linearity machinery used later by the
global-progress proof. This file ports:

* `CvarPos` (Coq `cvar_pos`): channel-occurrence *positivity* in the process context `Θ` — tracks
  whether the channel index `i` is present (`true`) or absent (`false`) in `Θ`.
* `occurs` (Coq `dyn_occurs`): the occurrence *count* of channel variable `i` in a term, by
  structural recursion. A channel variable `.chan (Chan.var_Chan x)` contributes `1` iff `x = i`;
  channels are bound by `res` at the `Proc` level (never by `Term` binders), so `i` is *not* lifted
  under any `Term` binder.
* The structural lemmas `CvarPos.merge_false`/`split_false`/`split_true`,
  `Empty.pos_true`/`pos_false`, `Just.pos_true`/`pos_false`.
* The linearity hearts `Typed.occurs0`/`occurs1` (Coq `dyn_type_occurs0`/`dyn_type_occurs1`).
* `Iren` (Coq `iren`, "`i` not in the range of `ξ`") and `Iren.zero`/`Iren.one`/`Iren.upren`, with
  the renaming corollary `Typed.occurs_iren` (Coq `dyn_occurs_iren`).

Coq `==`/`== false` (boolean eq) are rendered as Lean `=`/`≠` (Prop) throughout — the cleaner faithful
form. `upren` is the channel renaming lift `upRen_Chan_Chan`.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- Channel-occurrence positivity in the process context `Θ` (Coq `cvar_pos`): `CvarPos Θ i b` holds
    when channel index `i` is present (`b = true`) or absent (`b = false`) in `Θ`. -/
inductive CvarPos : Ctx → Nat → Bool → Prop where
  | nil {i} :
    CvarPos [] i false
  | ty {Θ A} :
    CvarPos (A :L Θ) 0 true
  | n {Θ} :
    CvarPos (none :: Θ) 0 false
  | cons {Θ x A b} :
    CvarPos Θ x b →
    CvarPos (A :: Θ) (x + 1) b

/-- The occurrence count of channel variable `i` in a term (Coq `dyn_occurs`). Channels are not bound
    by any `Term` binder, so `i` is never lifted under a binder. -/
def occurs (i : Nat) : Term → Nat
  | .var_Term _ => 0
  | .srt _ => 0
  | .pi _ _ _ _ => 0
  | .lam _ m _ _ => occurs i m
  | .app m _ .im => occurs i m
  | .app m n .ex => occurs i m + occurs i n
  | .sig _ _ _ _ => 0
  | .pair _ n .im _ => occurs i n
  | .pair m n .ex _ => occurs i m + occurs i n
  | .proj _ m n => occurs i m + occurs i n
  | .fix _ m => occurs i m
  | .unit => 0
  | .one => 0
  | .bool => 0
  | .tt => 0
  | .ff => 0
  | .ite _ m n1 n2 => occurs i m + max (occurs i n1) (occurs i n2)
  | .M _ => 0
  | .pure m => occurs i m
  | .mlet m n => occurs i m + occurs i n
  | .proto => 0
  | .stop => 0
  | .act _ _ _ _ => 0
  | .ch _ _ => 0
  | .chan (Chan.var_Chan x) => if x = i then 1 else 0
  | .fork _ m => occurs i m
  | .recv m _ => occurs i m
  | .send m _ => occurs i m
  | .close _ m => occurs i m
  | .box => 0

/-! ## Positivity / merge interaction. -/

/-- Absent on both merge components implies absent on the result (Coq `cvar_pos_merge_false`). -/
lemma CvarPos.merge_false {Θ1 Θ2 Θ i} (mrg : Merge Θ1 Θ2 Θ) :
    CvarPos Θ1 i false → CvarPos Θ2 i false → CvarPos Θ i false := by
  induction mrg generalizing i with
  | nil => intro p1 _; exact p1
  | left _ _ ih => intro p1 p2; cases p1 with
    | cons p1' => cases p2 with | cons p2' => exact .cons (ih p1' p2')
  | right1 _ _ ih => intro p1 p2; cases p1 with
    | cons p1' => cases p2 with | cons p2' => exact .cons (ih p1' p2')
  | right2 _ _ ih => intro p1 p2; cases p2 with
    | cons p2' => cases p1 with | cons p1' => exact .cons (ih p1' p2')
  | null _ ih => intro p1 p2; cases p1 with
    | n => exact .n
    | cons p1' => cases p2 with | cons p2' => exact .cons (ih p1' p2')

/-- Absent on a merge result splits into absent on both components (Coq `cvar_pos_split_false`). -/
lemma CvarPos.split_false {Θ1 Θ2 Θ i} (mrg : Merge Θ1 Θ2 Θ) :
    CvarPos Θ i false → CvarPos Θ1 i false ∧ CvarPos Θ2 i false := by
  induction mrg generalizing i with
  | nil => intro p; exact ⟨p, p⟩
  | left _ _ ih => intro p; cases p with
    | cons p' => obtain ⟨p1, p2⟩ := ih p'; exact ⟨.cons p1, .cons p2⟩
  | right1 _ _ ih => intro p; cases p with
    | cons p' => obtain ⟨p1, p2⟩ := ih p'; exact ⟨.cons p1, .cons p2⟩
  | right2 _ _ ih => intro p; cases p with
    | cons p' => obtain ⟨p1, p2⟩ := ih p'; exact ⟨.cons p1, .cons p2⟩
  | null _ ih => intro p; cases p with
    | n => exact ⟨.n, .n⟩
    | cons p' => obtain ⟨p1, p2⟩ := ih p'; exact ⟨.cons p1, .cons p2⟩

/-- Present on a merge result is present on exactly one component (Coq `cvar_pos_split_true`). -/
lemma CvarPos.split_true {Θ1 Θ2 Θ i} (mrg : Merge Θ1 Θ2 Θ) :
    CvarPos Θ i true →
    (CvarPos Θ1 i false ∧ CvarPos Θ2 i true) ∨ (CvarPos Θ1 i true ∧ CvarPos Θ2 i false) := by
  induction mrg generalizing i with
  | nil => intro p; cases p
  | left _ _ ih => intro p; cases p with
    | cons p' => rcases ih p' with ⟨p1, p2⟩ | ⟨p1, p2⟩
                 exacts [.inl ⟨.cons p1, .cons p2⟩, .inr ⟨.cons p1, .cons p2⟩]
  | right1 _ _ ih => intro p; cases p with
    | ty => exact .inr ⟨.ty, .n⟩
    | cons p' => rcases ih p' with ⟨p1, p2⟩ | ⟨p1, p2⟩
                 exacts [.inl ⟨.cons p1, .cons p2⟩, .inr ⟨.cons p1, .cons p2⟩]
  | right2 _ _ ih => intro p; cases p with
    | ty => exact .inl ⟨.n, .ty⟩
    | cons p' => rcases ih p' with ⟨p1, p2⟩ | ⟨p1, p2⟩
                 exacts [.inl ⟨.cons p1, .cons p2⟩, .inr ⟨.cons p1, .cons p2⟩]
  | null _ ih => intro p; cases p with
    | cons p' => rcases ih p' with ⟨p1, p2⟩ | ⟨p1, p2⟩
                 exacts [.inl ⟨.cons p1, .cons p2⟩, .inr ⟨.cons p1, .cons p2⟩]

/-! ## Empty / Just interaction. -/

/-- An empty process context has no present channel (Coq `dyn_empty_pos_true`). -/
lemma Empty.pos_true {Θ i} (emp : Empty Θ) : CvarPos Θ i true → False := by
  induction emp generalizing i with
  | nil => intro p; cases p
  | null _ ih => intro p; cases p with | cons p' => exact ih p'

/-- Every channel is absent in an empty process context (Coq `dyn_empty_pos_false`). -/
lemma Empty.pos_false {Θ i} (emp : Empty Θ) : CvarPos Θ i false := by
  induction emp generalizing i with
  | nil => exact .nil
  | null _ ih => cases i with
    | zero => exact .n
    | succ i => exact .cons ih

/-- A `Just` slot is present at `i` iff `x = i` (Coq `dyn_just_pos_true`). -/
lemma Just.pos_true {Θ x i A} (js : Just Θ x A) : CvarPos Θ i true ↔ x = i := by
  induction js generalizing i with
  | @zero Θ A emp =>
    refine ⟨fun p => ?_, fun e => ?_⟩
    · cases p with
      | ty => rfl
      | cons p' => exact absurd p' emp.pos_true
    · subst e; exact .ty
  | @null Θ A x js ih =>
    refine ⟨fun p => ?_, fun e => ?_⟩
    · cases p with | cons p' => rw [ih] at p'; rw [p']
    · subst e; exact .cons (ih.mpr rfl)

/-- A `Just` slot is absent at `i` iff `x ≠ i` (Coq `dyn_just_pos_false`). -/
lemma Just.pos_false {Θ x i A} (js : Just Θ x A) : CvarPos Θ i false ↔ x ≠ i := by
  induction js generalizing i with
  | @zero Θ A emp =>
    refine ⟨fun p => ?_, fun neq => ?_⟩
    · cases p with | cons p' => omega
    · cases i with
      | zero => exact absurd rfl neq
      | succ i => exact .cons emp.pos_false
  | @null Θ A x js ih =>
    refine ⟨fun p => ?_, fun neq => ?_⟩
    · cases p with
      | n => omega
      | cons p' => rw [ih] at p'; omega
    · cases i with
      | zero => exact .n
      | succ i => exact .cons (ih.mpr (by omega))

/-! ## Typing ↔ occurrence count. -/

/-- If `i` is absent in `Θ`, it does not occur in any well-typed term (Coq `dyn_type_occurs0`). -/
lemma Typed.occurs0 {Θ Γ Δ m A i} (ty : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    CvarPos Θ i false → occurs i m = 0 := by
  induction ty generalizing i with
  | var => intro _; rfl
  | lamIm _ _ _ ih => intro p; exact ih p
  | lamEx _ _ _ ih => intro p; exact ih p
  | appIm _ _ ihm => intro p; exact ihm p
  | appEx mrgΘ _ _ _ ihm ihn =>
    intro p
    obtain ⟨p1, p2⟩ := CvarPos.split_false mrgΘ p
    simp only [occurs, ihm p1, ihn p2]
  | pairIm _ _ _ ihn => intro p; exact ihn p
  | pairEx mrgΘ _ _ _ _ ihm ihn =>
    intro p
    obtain ⟨p1, p2⟩ := CvarPos.split_false mrgΘ p
    simp only [occurs, ihm p1, ihn p2]
  | projIm mrgΘ _ _ _ _ ihm ihn =>
    intro p
    obtain ⟨p1, p2⟩ := CvarPos.split_false mrgΘ p
    simp only [occurs, ihm p1, ihn p2]
  | projEx mrgΘ _ _ _ _ ihm ihn =>
    intro p
    obtain ⟨p1, p2⟩ := CvarPos.split_false mrgΘ p
    simp only [occurs, ihm p1, ihn p2]
  | one => intro _; rfl
  | tt => intro _; rfl
  | ff => intro _; rfl
  | ite mrgΘ _ _ _ _ _ ihm ihn1 ihn2 =>
    intro p
    obtain ⟨p1, p2⟩ := CvarPos.split_false mrgΘ p
    simp only [occurs, ihm p1, ihn1 p2, ihn2 p2, Nat.zero_add, Nat.max_self]
  | pure _ ihm => intro p; exact ihm p
  | mlet mrgΘ _ _ _ _ ihm ihn =>
    intro p
    obtain ⟨p1, p2⟩ := CvarPos.split_false mrgΘ p
    simp only [occurs, ihm p1, ihn p2]
  | chan js _ _ _ =>
    intro p
    show (if _ = i then 1 else 0) = 0
    rw [if_neg ((js.pos_false (i := i)).mp p)]
  | fork _ ihm => intro p; exact ihm p
  | recv _ _ ihm => intro p; exact ihm p
  | send _ _ ihm => intro p; exact ihm p
  | close _ ihm => intro p; exact ihm p
  | conv _ _ _ ihm => intro p; exact ihm p

/-- If `i` is present in `Θ`, it occurs exactly once in any well-typed term (Coq
    `dyn_type_occurs1`). -/
lemma Typed.occurs1 {Θ Γ Δ m A i} (ty : Θ ⨾ Γ ⨾ Δ ⊢ m : A) :
    CvarPos Θ i true → occurs i m = 1 := by
  induction ty generalizing i with
  | var emp _ _ _ => intro p; exact absurd p emp.pos_true
  | lamIm _ _ _ ih => intro p; exact ih p
  | lamEx _ _ _ ih => intro p; exact ih p
  | appIm _ _ ihm => intro p; exact ihm p
  | appEx mrgΘ _ tym tyn ihm ihn =>
    intro p
    rcases CvarPos.split_true mrgΘ p with ⟨p1, p2⟩ | ⟨p1, p2⟩
    · simp only [occurs, tym.occurs0 p1, ihn p2]
    · simp only [occurs, ihm p1, tyn.occurs0 p2]
  | pairIm _ _ _ ihn => intro p; exact ihn p
  | pairEx mrgΘ _ _ tym tyn ihm ihn =>
    intro p
    rcases CvarPos.split_true mrgΘ p with ⟨p1, p2⟩ | ⟨p1, p2⟩
    · simp only [occurs, tym.occurs0 p1, ihn p2]
    · simp only [occurs, ihm p1, tyn.occurs0 p2]
  | projIm mrgΘ _ _ tym tyn ihm ihn =>
    intro p
    rcases CvarPos.split_true mrgΘ p with ⟨p1, p2⟩ | ⟨p1, p2⟩
    · simp only [occurs, tym.occurs0 p1, ihn p2]
    · simp only [occurs, ihm p1, tyn.occurs0 p2]
  | projEx mrgΘ _ _ tym tyn ihm ihn =>
    intro p
    rcases CvarPos.split_true mrgΘ p with ⟨p1, p2⟩ | ⟨p1, p2⟩
    · simp only [occurs, tym.occurs0 p1, ihn p2]
    · simp only [occurs, ihm p1, tyn.occurs0 p2]
  | one emp _ _ => intro p; exact absurd p emp.pos_true
  | tt emp _ _ => intro p; exact absurd p emp.pos_true
  | ff emp _ _ => intro p; exact absurd p emp.pos_true
  | ite mrgΘ _ _ tym tyn1 tyn2 ihm ihn1 ihn2 =>
    intro p
    rcases CvarPos.split_true mrgΘ p with ⟨p1, p2⟩ | ⟨p1, p2⟩
    · simp only [occurs, tym.occurs0 p1, ihn1 p2, ihn2 p2, Nat.zero_add, Nat.max_self]
    · simp only [occurs, ihm p1, tyn1.occurs0 p2, tyn2.occurs0 p2, Nat.max_self, Nat.add_zero]
  | pure _ ihm => intro p; exact ihm p
  | mlet mrgΘ _ _ tym tyn ihm ihn =>
    intro p
    rcases CvarPos.split_true mrgΘ p with ⟨p1, p2⟩ | ⟨p1, p2⟩
    · simp only [occurs, tym.occurs0 p1, ihn p2]
    · simp only [occurs, ihm p1, tyn.occurs0 p2]
  | chan js _ _ _ =>
    intro p
    show (if _ = i then 1 else 0) = 1
    rw [if_pos ((js.pos_true (i := i)).mp p)]
  | fork _ ihm => intro p; exact ihm p
  | recv _ _ ihm => intro p; exact ihm p
  | send _ _ ihm => intro p; exact ihm p
  | close _ ihm => intro p; exact ihm p
  | conv _ _ _ ihm => intro p; exact ihm p

/-! ## Channel renaming with `i` out of range. -/

/-- `i` is not in the range of `ξ` (Coq `iren`). -/
def Iren (i : Nat) (ξ : Nat → Nat) : Prop := ∀ x, ξ x ≠ i

/-- `0` is out of range of `(· + 2)` (Coq `iren0`). -/
lemma Iren.zero : Iren 0 (· + 2) := by unfold Iren; intro x; show x + 2 ≠ 0; omega

/-- `1` is out of range of `(· + 2)` (Coq `iren1`). -/
lemma Iren.one : Iren 1 (· + 2) := by unfold Iren; intro x; show x + 2 ≠ 1; omega

/-- The channel-renaming lift preserves `Iren` shifted by one (Coq `iren_upren`). -/
lemma Iren.upren {i ξ} (ir : Iren i ξ) : Iren (i + 1) (upRen_Chan_Chan ξ) := by
  unfold Iren at ir ⊢
  intro x
  cases x with
  | zero =>
    show upRen_Chan_Chan ξ 0 ≠ i + 1
    intro h; asimp at h; simp only [var_zero] at h; omega
  | succ n =>
    show upRen_Chan_Chan ξ (n + 1) ≠ i + 1
    intro h; asimp at h
    simp only [funcomp, Nat.succ_eq_add_one] at h
    exact ir n (by omega)

/-- The occurrence count is `0` for any channel-renamed term whose renaming omits `i`. This is purely
    a fact about `occurs`/`cren` (the typing premise of the Coq `dyn_occurs_iren` is vestigial — under
    a `Term` binder a channel renaming keeps the same chan-map `ξ`, so the index `i` and the renaming
    are unchanged): proved by structural induction on `m`. -/
lemma occurs_cren {i : Nat} {ξ : Nat → Nat} (ir : Iren i ξ) :
    ∀ m : Term, occurs i (m⟨ξ; (id : Nat → Nat)⟩) = 0 := by
  intro m
  induction m with
  | var_Term _ => rfl
  | srt _ => rfl
  | pi _ _ _ _ _ _ => rfl
  | lam _ _ _ _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | app _ _ i0 ihm ihn => cases i0 <;> (asimp at ihm ihn ⊢; simp only [occurs, ihm, ihn])
  | sig _ _ _ _ _ _ => rfl
  | pair _ _ i0 _ ihm ihn => cases i0 <;> (asimp at ihm ihn ⊢; simp only [occurs, ihm, ihn])
  | proj _ _ _ _ ihm ihn => asimp at ihm ihn ⊢; simp only [occurs, ihm, ihn]
  | fix _ _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | unit => rfl
  | one => rfl
  | bool => rfl
  | tt => rfl
  | ff => rfl
  | ite _ _ _ _ _ ihm ihn1 ihn2 =>
    asimp at ihm ihn1 ihn2 ⊢; simp only [occurs, ihm, ihn1, ihn2, Nat.max_self]
  | M _ _ => rfl
  | pure _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | mlet _ _ ihm ihn => asimp at ihm ihn ⊢; simp only [occurs, ihm, ihn]
  | proto => rfl
  | stop => rfl
  | act _ _ _ _ _ _ => rfl
  | ch _ _ _ => rfl
  | chan c =>
    cases c with
    | var_Chan y =>
      asimp
      show (if ξ y = i then 1 else 0) = 0
      rw [if_neg (ir y)]
  | fork _ _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | recv _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | send _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | close _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | box => rfl

/-- If the term is the image of a channel renaming whose range omits `i`, then `i` does not occur
    in it (Coq `dyn_occurs_iren`). -/
lemma Typed.occurs_iren {Θ Γ Δ A i ξ} {m : Term}
    (_ : Θ ⨾ Γ ⨾ Δ ⊢ m⟨ξ; (id : Nat → Nat)⟩ : A) (ir : Iren i ξ) :
    occurs i (m⟨ξ; (id : Nat → Nat)⟩) = 0 :=
  occurs_cren ir m

end TLLC.Dynamic
