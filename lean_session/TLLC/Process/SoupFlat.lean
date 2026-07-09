import TLLC.Process.Soup
import TLLC.Process.CongrStep

/-!
# The flat normal form of the soup equivalence

`SoupEquiv` is a conversion closure; inverting it requires a normal form. `FlatEquiv` packages
one: equal binder counts, a single binder bijection, and — after discarding garbage threads —
a permutation with pointwise congruence through the bijection. `soupEquiv_flat` normalizes any
soup equivalence into this shape, and `flatEquiv_soupEquiv` plays it back, so the two coincide.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Garbage threads: the unit process `pure ()`. -/
def isGarbage : Term → Bool
  | .pure .one => true
  | _ => false

@[simp] lemma isGarbage_pure_one : isGarbage (.pure .one) = true := rfl

lemma isGarbage_eq_true {m : Term} (h : isGarbage m = true) : m = .pure .one := by
  cases m <;> simp [isGarbage] at h
  case pure v =>
    cases v <;> simp [isGarbage] at h ⊢

/-- Congruence preserves and reflects garbage. -/
lemma congrTerm_isGarbage {m m' : Term} (e : CongrTerm .ex m m') :
    isGarbage m = isGarbage m' := by
  cases hm : isGarbage m with
  | true =>
      rw [isGarbage_eq_true hm] at e
      cases e with
      | pure ev =>
          cases ev
          rfl
  | false =>
      cases hm' : isGarbage m' with
      | true =>
          rw [isGarbage_eq_true hm'] at e
          cases e with
          | pure ev =>
              cases ev
              simp [isGarbage] at hm
      | false => rfl

/-- Renaming preserves and reflects garbage. -/
lemma isGarbage_cren (m : Term) (ξ : Nat → Nat) :
    isGarbage (m⟨ξ; (id : Nat → Nat)⟩) = isGarbage m := by
  cases m <;> asimp <;> try rfl
  case pure v =>
    cases v <;> asimp <;> rfl

/-- The live (non-garbage) threads. -/
def live (ts : List Term) : List Term := ts.filter (fun m => !isGarbage m)

@[simp] lemma live_nil : live [] = [] := rfl

lemma live_cons_garbage {m ts} (h : isGarbage m = true) : live (m :: ts) = live ts := by
  simp [live, h]

lemma live_cons_live {m ts} (h : isGarbage m = false) : live (m :: ts) = m :: live ts := by
  simp [live, h]

/-- The pointwise relation of the flat form: congruent through the binder bijection. -/
def FlatRel (ξ : Nat → Nat) (m m' : Term) : Prop :=
  CongrTerm .ex (m⟨ξ; (id : Nat → Nat)⟩) m'

/-- Flat normal form of the soup equivalence. -/
def FlatEquiv (c c' : Config) : Prop :=
  c.1 = c'.1 ∧
  ∃ ξ ζ : Nat → Nat,
    (∀ x, ζ (ξ x) = x) ∧ (∀ x, ξ (ζ x) = x) ∧ (∀ x, c.1 ≤ x → ξ x = x) ∧
    ∃ l, (live c.2).Perm l ∧ List.Forall₂ (FlatRel ξ) l (live c'.2)

/-! ## Permutation transport along `Forall₂` -/

lemma forall₂_perm_left {R : Term → Term → Prop} {a b : List Term} :
    List.Forall₂ R a b → ∀ {a'}, a.Perm a' → ∃ b', b.Perm b' ∧ List.Forall₂ R a' b' := by
  intro h a' hp
  induction hp generalizing b with
  | nil =>
      cases h
      exact ⟨[], List.Perm.refl _, List.Forall₂.nil⟩
  | cons x _ ih =>
      cases h with
      | cons hx hrest =>
          obtain ⟨b', hb', hf⟩ := ih hrest
          exact ⟨_ :: b', List.Perm.cons _ hb', List.Forall₂.cons hx hf⟩
  | swap x y l =>
      cases h with
      | cons hy hrest =>
          cases hrest with
          | cons hx hrest' =>
              exact ⟨_, List.Perm.swap _ _ _, List.Forall₂.cons hx
                (List.Forall₂.cons hy hrest')⟩
  | trans _ _ ih1 ih2 =>
      obtain ⟨b1, hb1, hf1⟩ := ih1 h
      obtain ⟨b2, hb2, hf2⟩ := ih2 hf1
      exact ⟨b2, hb1.trans hb2, hf2⟩

lemma forall₂_imp {R S : Term → Term → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l₁ l₂ : List Term}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂ := by
  intro l₁ l₂ hf
  induction hf with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (h _ _ hab) ih

lemma forall₂_flip {R : Term → Term → Prop} {a b : List Term}
    (h : List.Forall₂ R a b) : List.Forall₂ (fun m m' => R m' m) b a := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

lemma forall₂_perm_right {R : Term → Term → Prop} {a b b' : List Term}
    (h : List.Forall₂ R a b) (hp : b.Perm b') :
    ∃ a', a.Perm a' ∧ List.Forall₂ R a' b' := by
  obtain ⟨a', ha', hf⟩ := forall₂_perm_left (forall₂_flip h) hp
  exact ⟨a', ha', forall₂_flip hf⟩

/-! ## `FlatEquiv` is an equivalence -/

lemma FlatEquiv.refl (c : Config) : FlatEquiv c c := by
  refine ⟨rfl, id, id, fun x => rfl, fun x => rfl, fun x _ => rfl, live c.2,
    List.Perm.refl _, ?_⟩
  induction live c.2 with
  | nil => exact List.Forall₂.nil
  | cons m ts ih =>
      refine List.Forall₂.cons ?_ ih
      show CongrTerm .ex (m⟨(id : Nat → Nat); (id : Nat → Nat)⟩) m
      rw [tren_id]
      exact CongrTerm.refl .ex m

lemma FlatRel.symm {ξ ζ : Nat → Nat} (hζξ : ∀ x, ζ (ξ x) = x) {m m' : Term}
    (h : FlatRel ξ m m') : FlatRel ζ m' m := by
  have h1 := (h.sym).crename ζ
  have e2 : (m⟨ξ; (id : Nat → Nat)⟩)⟨ζ; (id : Nat → Nat)⟩ = m := by
    rw [tren_comp,
      tren_ext m (ξ := fun x => ζ (ξ x)) (ζ := (id : Nat → Nat)) (fun x => hζξ x),
      tren_id]
  rw [e2] at h1
  exact h1

lemma forall₂_comp {R S T : Term → Term → Prop}
    (hcomp : ∀ a b c, R a b → S b c → T a c) :
    ∀ {a b c : List Term}, List.Forall₂ R a b → List.Forall₂ S b c →
      List.Forall₂ T a c := by
  intro a b c h1 h2
  induction h1 generalizing c with
  | nil => cases h2; exact .nil
  | cons hab _ ih =>
      cases h2 with
      | cons hbc hrest => exact .cons (hcomp _ _ _ hab hbc) (ih hrest)

lemma FlatEquiv.symm {c c' : Config} (h : FlatEquiv c c') : FlatEquiv c' c := by
  obtain ⟨hk, ξ, ζ, hζξ, hξζ, hfix, l, hp, hf⟩ := h
  refine ⟨hk.symm, ζ, ξ, hξζ, hζξ, ?_, ?_⟩
  · intro x hx
    rw [← hk] at hx
    conv_lhs => rw [show x = ξ x from (hfix x hx).symm]
    exact hζξ x
  · have hf' : List.Forall₂ (FlatRel ζ) (live c'.2) l :=
      forall₂_imp (fun _ _ hr => FlatRel.symm hζξ hr) (forall₂_flip hf)
    obtain ⟨l', hl', hff⟩ := forall₂_perm_right hf' hp.symm
    exact ⟨l', hl', hff⟩

lemma FlatEquiv.trans {c c' c'' : Config}
    (h1 : FlatEquiv c c') (h2 : FlatEquiv c' c'') : FlatEquiv c c'' := by
  obtain ⟨hk1, ξ1, ζ1, hζξ1, hξζ1, hfix1, l1, hp1, hf1⟩ := h1
  obtain ⟨hk2, ξ2, ζ2, hζξ2, hξζ2, hfix2, l2, hp2, hf2⟩ := h2
  refine ⟨hk1.trans hk2, fun x => ξ2 (ξ1 x), fun x => ζ1 (ζ2 x),
    fun x => by show ζ1 (ζ2 (ξ2 (ξ1 x))) = x; rw [hζξ2, hζξ1],
    fun x => by show ξ2 (ξ1 (ζ1 (ζ2 x))) = x; rw [hξζ1, hξζ2],
    fun x hx => by show ξ2 (ξ1 x) = x; rw [hfix1 x hx, hfix2 x (hk1 ▸ hx)], ?_⟩
  obtain ⟨l1', hp1', hf1'⟩ := forall₂_perm_right hf1 hp2
  refine ⟨l1', hp1.trans hp1', ?_⟩
  refine forall₂_comp ?_ hf1' hf2
  intro a b c hab hbc
  show CongrTerm .ex (a⟨fun x => ξ2 (ξ1 x); (id : Nat → Nat)⟩) c
  have h := hab.crename ξ2
  rw [tren_comp] at h
  exact h.trans hbc

/-! ## `live` bookkeeping -/

lemma live_perm {ts ts' : List Term} (h : ts.Perm ts') : (live ts).Perm (live ts') :=
  h.filter _

lemma live_congr {ts ts' : List Term} (h : List.Forall₂ (CongrTerm .ex) ts ts') :
    List.Forall₂ (CongrTerm .ex) (live ts) (live ts') := by
  induction h with
  | nil => exact .nil
  | cons hab hrest ih =>
      rename_i a b l₁ l₂
      cases hg : isGarbage a with
      | true =>
          rw [live_cons_garbage hg, live_cons_garbage ((congrTerm_isGarbage hab) ▸ hg)]
          exact ih
      | false =>
          rw [live_cons_live hg, live_cons_live ((congrTerm_isGarbage hab) ▸ hg)]
          exact .cons hab ih

lemma live_map_cren (ts : List Term) (ξ : Nat → Nat) :
    live (ts.map (fun m => m⟨ξ; (id : Nat → Nat)⟩)) =
      (live ts).map (fun m => m⟨ξ; (id : Nat → Nat)⟩) := by
  induction ts with
  | nil => rfl
  | cons m ts ih =>
      cases hg : isGarbage m with
      | true =>
          rw [List.map_cons, live_cons_garbage (by rw [isGarbage_cren]; exact hg),
            live_cons_garbage hg, ih]
      | false =>
          rw [List.map_cons, live_cons_live (by rw [isGarbage_cren]; exact hg),
            live_cons_live hg, List.map_cons, ih]

lemma flatRel_id_refl (ts : List Term) : List.Forall₂ (FlatRel id) ts ts := by
  induction ts with
  | nil => exact .nil
  | cons m ts ih =>
      refine List.Forall₂.cons ?_ ih
      show CongrTerm .ex (m⟨(id : Nat → Nat); (id : Nat → Nat)⟩) m
      rw [tren_id]
      exact CongrTerm.refl .ex m

lemma flatRel_map_refl (ts : List Term) (ξ : Nat → Nat) :
    List.Forall₂ (FlatRel ξ) ts (ts.map (fun m => m⟨ξ; (id : Nat → Nat)⟩)) := by
  induction ts with
  | nil => exact .nil
  | cons m ts ih =>
      exact List.Forall₂.cons (CongrTerm.refl .ex _) ih

/-! ## Normalization: soup equivalence to flat form -/

lemma soupG_flat {c c' : Config} (h : SoupG c c') : FlatEquiv c c' := by
  cases h with
  | @perm k ts ts' hperm =>
      exact ⟨rfl, id, id, fun x => rfl, fun x => rfl, fun x _ => rfl,
        live ts', live_perm hperm, flatRel_id_refl _⟩
  | @congr k ts ts' hcongr =>
      refine ⟨rfl, id, id, fun x => rfl, fun x => rfl, fun x _ => rfl,
        live ts, List.Perm.refl _, ?_⟩
      refine forall₂_imp (fun a b hr => ?_) (live_congr hcongr)
      show CongrTerm .ex (a⟨(id : Nat → Nat); (id : Nat → Nat)⟩) b
      rw [tren_id]
      exact hr
  | @garbage k ts =>
      refine ⟨rfl, id, id, fun x => rfl, fun x => rfl, fun x _ => rfl,
        live ts, List.Perm.refl _, ?_⟩
      rw [show live (Term.pure .one :: ts) = live ts from live_cons_garbage rfl]
      exact flatRel_id_refl _
  | @swap k ts i j hi hj =>
      refine ⟨rfl, cswap i j, cswap i j, cswap_invol i j, cswap_invol i j,
        fun x hx => cswap_ne (by omega) (by omega),
        live ts, List.Perm.refl _, ?_⟩
      rw [live_map_cren]
      exact flatRel_map_refl _ _

/-- Every soup equivalence normalizes to the flat form. -/
theorem soupEquiv_flat {c c' : Config} (h : SoupEquiv c c') : FlatEquiv c c' := by
  induction h with
  | refl => exact FlatEquiv.refl _
  | tail _ hg ih => exact ih.trans (soupG_flat hg)
  | taili _ hg ih => exact ih.trans (FlatEquiv.symm (soupG_flat hg))

/-! ## Playback: flat form to soup equivalence -/

private lemma soupEquiv_strip (k : Nat) :
    ∀ g : List Term, (∀ x ∈ g, isGarbage x = true) →
      ∀ us, SoupEquiv (k, g ++ us) (k, us) := by
  intro g
  induction g with
  | nil => intro _ us; exact ARS.Conv.refl
  | cons x g ih =>
      intro hg us
      have hx := isGarbage_eq_true (hg x (by simp))
      subst hx
      exact ARS.conv_trans (ARS.conv1i SoupG.garbage)
        (ih (fun y hy => hg y (by simp [hy])) us)

/-- A configuration is soup-equivalent to its live threads. -/
lemma soupEquiv_live (k : Nat) (ts : List Term) : SoupEquiv (k, ts) (k, live ts) := by
  have hperm : (ts.filter isGarbage ++ live ts).Perm ts :=
    List.filter_append_perm isGarbage ts
  refine ARS.conv_trans (SoupEquiv.perm hperm.symm) ?_
  exact soupEquiv_strip k _ (fun x hx => (List.mem_filter.mp hx).2) _

lemma forall₂_map_flatRel {ξ : Nat → Nat} :
    ∀ {l ts' : List Term}, List.Forall₂ (FlatRel ξ) l ts' →
      List.Forall₂ (CongrTerm .ex)
        (l.map (fun m => m⟨ξ; (id : Nat → Nat)⟩)) ts' := by
  intro l ts' hf
  induction hf with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

/-- The flat form plays back as a soup equivalence. -/
theorem flatEquiv_soupEquiv {c c' : Config} (h : FlatEquiv c c') : SoupEquiv c c' := by
  obtain ⟨hk, ξ, ζ, hζξ, hξζ, hfix, l, hp, hf⟩ := h
  obtain ⟨k, ts⟩ := c
  obtain ⟨k', ts'⟩ := c'
  simp only at hk
  subst hk
  refine ARS.conv_trans (soupEquiv_live k ts) ?_
  refine ARS.conv_trans (SoupEquiv.perm hp) ?_
  refine ARS.conv_trans (SoupEquiv.ren ξ ζ hζξ hξζ hfix) ?_
  refine ARS.conv_trans (SoupEquiv.congr ?_) (ARS.conv_sym (soupEquiv_live k ts'))
  exact forall₂_map_flatRel hf

end TLLC.Process
