import Mathlib.Tactic

/-!
# Abstract Reduction Systems

Port of `coq_session/ARS.v`: reflexive-transitive (`Star`) and reflexive-symmetric-transitive
(`Conv`) closures of a relation, plus the diamond / confluence / Church-Rosser machinery used by
the static confluence development.

Omitted from the Coq file (verified unused anywhere downstream, and the `ComputationN` part relies
on `Prop → Type` elimination Lean restricts): the `<=2`-closure family (`star_closure`,
`star_monotone`, `eq_star`, `star_interpolation`, `confluent_stable`, `conv_closure`), the
`Termination` section (`sn`, `sn_preimage`, `normal`/`reducible`/`wn`/`nf`, …), the `CoFinal`
section (`triangle`, `cofinal`, `normalizing`, `cr_method`), and `ComputationN` (`accn`, `evaln`,
`evalnP`). They can be added back if a later phase needs them.
-/

namespace TLLC.ARS

variable {T : Type*} {e : T → T → Prop}

/-- Reflexive-transitive closure (snoc-style, as in Coq's `star`). -/
inductive Star (e : T → T → Prop) (x : T) : T → Prop
  | refl : Star e x x
  | tail {y z} : Star e x y → e y z → Star e x z

/-- Reflexive-symmetric-transitive closure (Coq's `conv`). -/
inductive Conv (e : T → T → Prop) (x : T) : T → Prop
  | refl : Conv e x x
  | tail  {y z} : Conv e x y → e y z → Conv e x z
  | taili {y z} : Conv e x y → e z y → Conv e x z

/-- `Com e1 e2`: commutation of `e1` over `e2`. -/
def Com (e1 e2 : T → T → Prop) : Prop :=
  ∀ x y z, e1 x y → e2 x z → ∃ u, e2 y u ∧ e1 z u

def Joinable (R : T → T → Prop) (x y : T) : Prop := ∃ z, R x z ∧ R y z
def Diamond (e : T → T → Prop) : Prop := ∀ x y z, e x y → e x z → ∃ u, e y u ∧ e z u
def Confluent (e : T → T → Prop) : Prop := ∀ x y z, Star e x y → Star e x z → Joinable (Star e) y z
def CR (e : T → T → Prop) : Prop := ∀ x y, Conv e x y → Joinable (Star e) x y

/-! ## Closure lemmas -/

lemma star1 {x y} (h : e x y) : Star e x y := .tail .refl h

lemma star_trans {x y z} (A : Star e x y) (B : Star e y z) : Star e x z := by
  induction B with
  | refl => exact A
  | tail _ s ih => exact .tail ih s

lemma starES {x y z} (h : e x y) (A : Star e y z) : Star e x z := star_trans (star1 h) A

lemma star_conv {x y} (A : Star e x y) : Conv e x y := by
  induction A with
  | refl => exact .refl
  | tail _ s ih => exact .tail ih s

lemma conv1 {x y} (h : e x y) : Conv e x y := .tail .refl h
lemma conv1i {x y} (h : e y x) : Conv e x y := .taili .refl h

lemma conv_trans {x y z} (A : Conv e x y) (B : Conv e y z) : Conv e x z := by
  induction B with
  | refl => exact A
  | tail _ s ih => exact .tail ih s
  | taili _ s ih => exact .taili ih s

lemma convES {x y z} (h : e x y) (A : Conv e y z) : Conv e x z := conv_trans (conv1 h) A
lemma convESi {x y z} (h : e y x) (A : Conv e y z) : Conv e x z := conv_trans (conv1i h) A

lemma conv_sym {x y} (A : Conv e x y) : Conv e y x := by
  induction A with
  | refl => exact .refl
  | tail _ s ih => exact convESi s ih
  | taili _ s ih => exact convES s ih

lemma join_conv {x y z} (A : Star e x y) (B : Star e z y) : Conv e x z :=
  conv_trans (star_conv A) (conv_sym (star_conv B))

lemma confluent_cr : Confluent e ↔ CR e := by
  constructor
  · intro h x y cxy
    induction cxy with
    | refl => exact ⟨x, .refl, .refl⟩
    | tail _ s ih =>
        obtain ⟨u, h1, h2⟩ := ih
        obtain ⟨v, hu, hz⟩ := h _ _ _ h2 (star1 s)
        exact ⟨v, star_trans h1 hu, hz⟩
    | taili _ s ih =>
        obtain ⟨u, h1, h2⟩ := ih
        exact ⟨u, h1, starES s h2⟩
  · intro h x y z sxy sxz
    exact h y z (conv_trans (conv_sym (star_conv sxy)) (star_conv sxz))

/-! ## Homomorphism / image lemmas -/

lemma star_img {T1 T2 : Type*} (f : T1 → T2) (e1 : T1 → T1 → Prop) {e2 : T2 → T2 → Prop}
    (A : ∀ x y, e1 x y → Star e2 (f x) (f y)) :
    ∀ x y, Star e1 x y → Star e2 (f x) (f y) := by
  intro x y h
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact star_trans ih (A _ _ s)

lemma star_hom {T1 T2 : Type*} (f : T1 → T2) (e1 : T1 → T1 → Prop) {e2 : T2 → T2 → Prop}
    (A : ∀ x y, e1 x y → e2 (f x) (f y)) :
    ∀ x y, Star e1 x y → Star e2 (f x) (f y) :=
  star_img f e1 (fun x y h => star1 (A x y h))

lemma conv_img {T1 T2 : Type*} (f : T1 → T2) (e1 : T1 → T1 → Prop) {e2 : T2 → T2 → Prop}
    (A : ∀ x y, e1 x y → Conv e2 (f x) (f y)) :
    ∀ x y, Conv e1 x y → Conv e2 (f x) (f y) := by
  intro x y h
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact conv_trans ih (A _ _ s)
  | taili _ s ih => exact conv_trans ih (conv_sym (A _ _ s))

lemma conv_hom {T1 T2 : Type*} (f : T1 → T2) (e1 : T1 → T1 → Prop) {e2 : T2 → T2 → Prop}
    (A : ∀ x y, e1 x y → e2 (f x) (f y)) :
    ∀ x y, Conv e1 x y → Conv e2 (f x) (f y) :=
  conv_img f e1 (fun x y h => conv1 (A x y h))

/-! ## Commutation: diamond ⟹ confluent -/

lemma com_strip {e1 e2 : T → T → Prop} (A : Com e1 e2) : Com (Star e2) e1 := by
  intro x y z Sxy
  induction Sxy with
  | refl => intro e1xz; exact ⟨z, e1xz, .refl⟩
  | tail _ eyw ih =>
      intro e1xz
      obtain ⟨u, eyu, s⟩ := ih e1xz
      obtain ⟨v, euv, ewv⟩ := A _ _ _ eyu eyw
      exact ⟨v, ewv, .tail s euv⟩

lemma com_lift {e1 e2 : T → T → Prop} (A : Com e1 e2) : Com (Star e1) (Star e2) :=
  com_strip (com_strip A)

lemma diamond_confluent {e : T → T → Prop} (h : Diamond e) : Confluent e :=
  com_lift h

end TLLC.ARS
