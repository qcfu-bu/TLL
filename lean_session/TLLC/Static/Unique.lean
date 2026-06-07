import TLLC.Static.Inversion

/-!
# Static uniqueness

Port of `coq_session/sta_uniq.v`: type-uniqueness up to similarity. A *head similarity*
`HeadSim` (Coq `head_sim`) relates two terms with the same top-level constructor whose subterms
agree on the parts the typing rules constrain and are otherwise free (the indices of `sig`, `M`,
`ch`, `act`, … are left unconstrained). *Similarity* `Sim` (Coq `sim`) closes `HeadSim` under
conversion on both sides; `CtxSim` (Coq `sta_ctx_sim`) lifts it pointwise to contexts. The per-
constructor `*_unique` lemmas pin down a term's type up to `Sim`, culminating in `Typed.unique`
(Coq `sta_uniq`) and the type-uniqueness theorem `Typed.unicity` (Coq `sta_unicity`): a term has at
most one sort.

As elsewhere, Coq's implicit/explicit constructor pairs are merged via the `Rlv` tag and
`Close`/`Wait` via the `Bool` tag. Thus `head_sim_pi0`/`head_sim_pi1` collapse to `HeadSim.pi`,
`head_sim_sig0`/`head_sim_sig1` to `HeadSim.sig`, `head_sim_act0`/`head_sim_act1` to `HeadSim.act`,
`head_sim_io` to `HeadSim.M`, `head_sim_close`/`head_sim_wait` to `HeadSim.close`, and so on for the
remaining `*0`/`*1` pairs; correspondingly each pair of `sta_*0_unique`/`sta_*1_unique` lemmas (and the
injectivity lemmas `sim_pi0_inj`/`sim_pi1_inj`, `sim_act0_inj`) merges into a single lemma carrying
the tag. Coq's `solve_sim`/`solve_conv` scaffolding is replaced by `cases` on the `HeadSim` witness
followed by `false_conv` (impossible heads) or the `*_inj` lemmas of `Confluence` (matching heads).

The per-constructor `*_unique` proofs follow the Inversion idiom: the subject is generalized to a
fresh variable, induction runs over the typing derivation (`Typed.rec` with a trivial `Wf` motive),
all head-mismatch and well-formedness cases are discharged by `trivial`, the matching constructor
case reads off the similarity, and the `conv` case threads the conversion through `Sim.transL`.
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Head similarity (Coq `head_sim`): equal top-level constructors with the typing-relevant
    subterms aligned and the rest free. -/
inductive HeadSim : Term → Term → Prop where
  | var {x} :
    HeadSim (.var_Term x) (.var_Term x)
  | srt {s} :
    HeadSim (.srt s) (.srt s)
  | pi {A1 A2 B1 B2 i s} :
    HeadSim B1 B2 →
    HeadSim (.pi A1 B1 i s) (.pi A2 B2 i s)
  | lam {A m i s} :
    HeadSim (.lam A m i s) (.lam A m i s)
  | app {m n i} :
    HeadSim (.app m n i) (.app m n i)
  | sig {A1 A2 B1 B2 i s1 s2} :
    HeadSim (.sig A1 B1 i s1) (.sig A2 B2 i s2)
  | pair {m n i s} :
    HeadSim (.pair m n i s) (.pair m n i s)
  | proj {A m n} :
    HeadSim (.proj A m n) (.proj A m n)
  | fix {A m} :
    HeadSim (.fix A m) (.fix A m)
  | unit :
    HeadSim .unit .unit
  | one :
    HeadSim .one .one
  | bool :
    HeadSim .bool .bool
  | tt :
    HeadSim .tt .tt
  | ff :
    HeadSim .ff .ff
  | ite {A m n1 n2} :
    HeadSim (.ite A m n1 n2) (.ite A m n1 n2)
  | M {A B} :
    HeadSim (.M A) (.M B)
  | pure {m} :
    HeadSim (.pure m) (.pure m)
  | mlet {m n} :
    HeadSim (.mlet m n) (.mlet m n)
  | proto :
    HeadSim .proto .proto
  | stop :
    HeadSim .stop .stop
  | act {b A B i} :
    HeadSim (.act b A B i) (.act b A B i)
  | ch {b1 b2 A1 A2} :
    HeadSim (.ch b1 A1) (.ch b2 A2)
  | chan {c} :
    HeadSim (.chan c) (.chan c)
  | fork {A m} :
    HeadSim (.fork A m) (.fork A m)
  | recv {m i} :
    HeadSim (.recv m i) (.recv m i)
  | send {m i} :
    HeadSim (.send m i) (.send m i)
  | close {b m} :
    HeadSim (.close b m) (.close b m)
  | box :
    HeadSim .box .box

/-- Similarity (Coq `sim`): head similarity closed under conversion on both sides. -/
inductive Sim (m n : Term) : Prop where
  | intro {x y} : (m ≃ x) → HeadSim x y → (y ≃ n) → Sim m n

/-- Context similarity (Coq `sta_ctx_sim`): pointwise similarity. -/
inductive CtxSim : Ctx → Ctx → Prop where
  | nil : CtxSim ([] : Ctx) ([] : Ctx)
  | cons {A B Γ1 Γ2} :
    Sim A B →
    CtxSim Γ1 Γ2 →
    CtxSim (A :: Γ1) (B :: Γ2)

/-- Head similarity is reflexive (Coq `head_sim_reflexive`). -/
lemma HeadSim.refl : ∀ m, HeadSim m m := by
  intro m
  induction m with
  | pi _ _ _ _ _ ih => exact .pi ih
  | _ => first | exact .pi (by assumption) | constructor

/-- Head similarity is symmetric (Coq `head_sim_sym`). -/
lemma HeadSim.sym {m n} (h : HeadSim m n) : HeadSim n m := by
  induction h with
  | pi _ ih => exact .pi ih
  | _ => first | exact .pi (by assumption) | constructor

/-- Head similarity is closed under substitution (Coq `head_sim_subst`). -/
lemma HeadSim.subst {m1 m2} (h : HeadSim m1 m2) (σ : Nat → Term) :
    HeadSim (m1[Chan.var_Chan; σ]) (m2[Chan.var_Chan; σ]) := by
  induction h generalizing σ with
  | pi _ ih => exact .pi (ih (up_Term_Term σ))
  | _ => first | exact .pi (by assumption) | (asimp; first | exact HeadSim.refl _ | constructor)

/-- Similarity is reflexive (Coq `sim_reflexive`). -/
lemma Sim.refl (m : Term) : Sim m m := ⟨.refl, HeadSim.refl m, .refl⟩

/-- Similarity absorbs conversion on the right (Coq `sim_transL`). -/
lemma Sim.transL {x y z} (sm : Sim x y) (eq : y ≃ z) : Sim x z := by
  cases sm with | intro c1 hs c2 => exact ⟨c1, hs, ARS.conv_trans c2 eq⟩

/-- Similarity absorbs conversion on the left (Coq `sim_transR`). -/
lemma Sim.transR {x y z} (sm : Sim x y) (eq : z ≃ x) : Sim z y := by
  cases sm with | intro c1 hs c2 => exact ⟨ARS.conv_trans eq c1, hs, c2⟩

/-- Similarity is symmetric (Coq `sim_sym`). -/
lemma Sim.sym {x y} (sm : Sim x y) : Sim y x := by
  cases sm with | intro c1 hs c2 => exact ⟨ARS.conv_sym c2, hs.sym, ARS.conv_sym c1⟩

/-- Similarity is closed under substitution (Coq `sim_subst`). -/
lemma Sim.subst {x y} (sm : Sim x y) (σ : Nat → Term) :
    Sim (x[Chan.var_Chan; σ]) (y[Chan.var_Chan; σ]) := by
  cases sm with | intro c1 hs c2 => exact ⟨conv_subst σ c1, hs.subst σ, conv_subst σ c2⟩

/-- Similarity is closed under renaming (the renaming specialization of `Sim.subst`). -/
lemma Sim.ren {x y} (sm : Sim x y) (ξ : Nat → Nat) :
    Sim (x⟨(id : Nat → Nat); ξ⟩) (y⟨(id : Nat → Nat); ξ⟩) := by
  have h := sm.subst (funcomp Term.var_Term ξ)
  have e : ∀ X : Term, X[Chan.var_Chan; funcomp Term.var_Term ξ] = X⟨(id : Nat → Nat); ξ⟩ :=
    fun X => (rinst_inst_Term id ξ Chan.var_Chan (funcomp Term.var_Term ξ)
      (congrFun rfl) (congrFun rfl) X).symm
  rw [e, e] at h
  exact h

/-- Context similarity is symmetric (Coq `sta_ctx_sim_sym`). -/
lemma CtxSim.sym {Γ1 Γ2} (h : CtxSim Γ1 Γ2) : CtxSim Γ2 Γ1 := by
  induction h with
  | nil => exact .nil
  | cons sm _ ih => exact .cons sm.sym ih

/-- Context similarity is reflexive (Coq `sta_ctx_sim_reflexive`). -/
lemma CtxSim.refl : ∀ Γ, CtxSim Γ Γ
  | [] => .nil
  | A :: Γ => .cons (Sim.refl A) (CtxSim.refl Γ)

/-- Sort similarity forces sort equality (Coq `sim_sort`). -/
lemma sim_sort {s t} (sm : Sim (.srt s) (.srt t)) : s = t := by
  cases sm with | intro c1 hs c2 => ?_
  cases hs with
  | pi => false_conv
  | sig => false_conv
  | M => false_conv
  | ch => false_conv
  | act => false_conv
  | _ => exact sort_inj (ARS.conv_trans c1 c2)

/-- `pi`-similarity injectivity (Coq `sim_pi0_inj` / `sim_pi1_inj`, merged). -/
lemma sim_pi_inj {A1 A2 B1 B2 i1 i2 s1 s2}
    (sm : Sim (.pi A1 B1 i1 s1) (.pi A2 B2 i2 s2)) : Sim B1 B2 ∧ s1 = s2 := by
  cases sm with | intro c1 hs c2 => ?_
  cases hs with
  | @pi _ _ _ _ _ _ hB =>
    obtain ⟨_, eqB1, _, es1⟩ := pi_inj c1
    obtain ⟨_, eqB2, _, es2⟩ := pi_inj c2
    exact ⟨⟨eqB1, hB, eqB2⟩, es1.trans es2⟩
  | sig => false_conv
  | M => false_conv
  | ch => false_conv
  | act => false_conv
  | _ =>
    obtain ⟨_, eqB, _, es⟩ := pi_inj (ARS.conv_trans c1 c2)
    exact ⟨⟨.refl, HeadSim.refl _, eqB⟩, es⟩

/-- `act`-similarity injectivity (Coq `sim_act0_inj`, merged over the `Rlv`). -/
lemma sim_act_inj {b1 b2 A1 A2 B1 B2 i1 i2}
    (sm : Sim (.act b1 A1 B1 i1) (.act b2 A2 B2 i2)) :
    (A1 ≃ A2) ∧ (B1 ≃ B2) ∧ b1 = b2 := by
  cases sm with | intro c1 hs c2 => ?_
  cases hs with
  | pi => false_conv
  | sig => false_conv
  | M => false_conv
  | ch => false_conv
  | _ =>
    obtain ⟨eqA, eqB, eb, _⟩ := act_inj (ARS.conv_trans c1 c2)
    exact ⟨eqA, eqB, eb⟩

/-- The type of a sort is similar to `srt U` (Coq `sta_sort_uniq`). -/
lemma sort_unique {Γ s A} (ty : Γ ⊢ .srt s : A) : Sim (.srt .U) A := by
  generalize e : Term.srt s = n
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing s
  all_goals try trivial
  case srt => exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- Lookups in similar contexts yield similar types (Coq `sta_has_uniq`). -/
lemma has_unique {Γ1 Γ2 x A B}
    (hs1 : Has Γ1 x A) (hs2 : Has Γ2 x B) (csm : CtxSim Γ1 Γ2) : Sim A B := by
  induction hs1 generalizing Γ2 B with
  | zero =>
    cases hs2 with | zero => ?_
    cases csm with | cons sm _ => exact sm.ren _
  | succ _ ih =>
    cases hs2 with | succ hs2 => ?_
    cases csm with | cons _ csm => exact (ih hs2 csm).ren _

/-- The type of a variable is similar to its lookup in any similar context (Coq `sta_var_uniq`). -/
lemma var_unique {Γ1 Γ2 A B x}
    (ty : Γ1 ⊢ .var_Term x : B) (hs : Has Γ2 x A) (csm : CtxSim Γ1 Γ2) : Sim A B := by
  generalize e : Term.var_Term x = n
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A x Γ2
  all_goals try trivial
  case var hs1 _ => cases e; exact (has_unique hs1 hs csm).sym
  case conv eq _ _ ihm _ => exact (ihm hs csm e).transL eq

/-- The type of a `pi` is similar to its sort (Coq `sta_pi0_uniq` / `sta_pi1_uniq`, merged). -/
lemma pi_unique {Γ A B C i s} (ty : Γ ⊢ .pi A B i s : C) : Sim (.srt s) C := by
  generalize e : Term.pi A B i s = n
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B i s
  all_goals try trivial
  case pi => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of a `lam` is similar to its `pi` type (Coq `sta_lam0_uniq` / `sta_lam1_uniq`,
    merged). -/
lemma lam_unique {Γ1 Γ2 A B C m i s}
    (ty : Γ2 ⊢ .lam A m i s : C)
    (h : ∀ {Γ2 C}, Γ2 ⊢ m : C → CtxSim (A :: Γ1) Γ2 → Sim B C)
    (csm : CtxSim Γ1 Γ2) : Sim (.pi A B i s) C := by
  generalize e : Term.lam A m i s = n
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B m i s Γ1
  all_goals try trivial
  case lam Γ A B m i s tym _ =>
    cases e
    cases h tym (.cons (Sim.refl _) csm) with
    | intro c1 hsm c2 => exact ⟨conv_pi .refl c1, .pi hsm, conv_pi .refl c2⟩
  case conv eq _ _ ihm _ => exact (ihm h csm e).transL eq

/-- The type of an `app` is similar to the substituted codomain (Coq `sta_app0_uniq` /
    `sta_app1_uniq`, merged). -/
lemma app_unique {Γ A B C m n i s}
    (ty : Γ ⊢ .app m n i : C)
    (h : ∀ {C}, Γ ⊢ m : C → Sim (.pi A B i s) C) : Sim (B[Chan.var_Chan; n..]) C := by
  generalize e : Term.app m n i = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B m n i s
  all_goals try trivial
  case app Γ A B m n i s tym _ _ _ =>
    cases e
    obtain ⟨eq', _⟩ := sim_pi_inj (h tym)
    exact eq'.subst _
  case conv eq _ _ ihm _ => exact (ihm h e).transL eq

/-- The type of a `sig` is similar to its sort (Coq `sta_sig0_uniq` / `sta_sig1_uniq`, merged). -/
lemma sig_unique {Γ A B C i s} (ty : Γ ⊢ .sig A B i s : C) : Sim (.srt s) C := by
  generalize e : Term.sig A B i s = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B i s
  all_goals try trivial
  case sig => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of a `pair` is similar to its `sig` type (Coq `sta_pair0_uniq` / `sta_pair1_uniq`,
    merged). -/
lemma pair_unique {Γ A B C m n i s}
    (ty : Γ ⊢ .pair m n i s : C)
    (h : ∀ {X Y}, Γ ⊢ m : X → Γ ⊢ n : Y → Sim A X ∧ Sim (B[Chan.var_Chan; m..]) Y) :
    Sim (.sig A B i s) C := by
  generalize e : Term.pair m n i s = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B m n i s
  all_goals try trivial
  case pair => cases e; exact ⟨.refl, .sig, .refl⟩
  case conv eq _ _ ihm _ => exact (ihm h e).transL eq

/-- The type of a `proj` is similar to the substituted motive (Coq `sta_letin_uniq`). -/
lemma proj_unique {Γ A m n B} (ty : Γ ⊢ .proj A m n : B) : Sim (A[Chan.var_Chan; m..]) B := by
  generalize e : Term.proj A m n = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A m n
  all_goals try trivial
  case proj => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of a `fix` is similar to its annotation (Coq `sta_fix_uniq`). -/
lemma fix_unique {Γ A B m} (ty : Γ ⊢ .fix A m : B) : Sim A B := by
  generalize e : Term.fix A m = n
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A m
  all_goals try trivial
  case fix => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `unit` is similar to `srt U` (Coq `sta_unit_uniq`). -/
lemma unit_unique {Γ A} (ty : Γ ⊢ .unit : A) : Sim (.srt .U) A := by
  generalize e : Term.unit = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True)
  all_goals try trivial
  case unit => exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `one` is similar to `unit` (Coq `sta_ii_uniq`). -/
lemma one_unique {Γ A} (ty : Γ ⊢ .one : A) : Sim .unit A := by
  generalize e : Term.one = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True)
  all_goals try trivial
  case one => exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `bool` is similar to `srt U` (Coq `sta_bool_uniq`). -/
lemma bool_unique {Γ A} (ty : Γ ⊢ .bool : A) : Sim (.srt .U) A := by
  generalize e : Term.bool = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True)
  all_goals try trivial
  case bool => exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `tt` is similar to `bool` (Coq `sta_tt_uniq`). -/
lemma tt_unique {Γ A} (ty : Γ ⊢ .tt : A) : Sim .bool A := by
  generalize e : Term.tt = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True)
  all_goals try trivial
  case tt => exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `ff` is similar to `bool` (Coq `sta_ff_uniq`). -/
lemma ff_unique {Γ A} (ty : Γ ⊢ .ff : A) : Sim .bool A := by
  generalize e : Term.ff = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True)
  all_goals try trivial
  case ff => exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of an `ite` is similar to the substituted motive (Coq `sta_ifte_uniq`). -/
lemma ite_unique {Γ A m n1 n2 B} (ty : Γ ⊢ .ite A m n1 n2 : B) :
    Sim (A[Chan.var_Chan; m..]) B := by
  generalize e : Term.ite A m n1 n2 = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A m n1 n2
  all_goals try trivial
  case ite => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `M` is similar to `srt L` (Coq `sta_io_uniq`). -/
lemma M_unique {Γ A B} (ty : Γ ⊢ .M A : B) : Sim (.srt .L) B := by
  generalize e : Term.M A = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A
  all_goals try trivial
  case M => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `pure` is similar to a monadic type (Coq `sta_return_uniq`). -/
lemma pure_unique {Γ m A B} (ty : Γ ⊢ .pure m : B) : Sim (.M A) B := by
  generalize e : Term.pure m = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing m A
  all_goals try trivial
  case pure => cases e; exact ⟨.refl, .M, .refl⟩
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `mlet` is similar to a monadic type (Coq `sta_bind_uniq`). -/
lemma mlet_unique {Γ m n A B} (ty : Γ ⊢ .mlet m n : B) : Sim (.M A) B := by
  generalize e : Term.mlet m n = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing m n A
  all_goals try trivial
  case mlet => cases e; exact ⟨.refl, .M, .refl⟩
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `proto` is similar to `srt U` (Coq `sta_proto_uniq`). -/
lemma proto_unique {Γ B} (ty : Γ ⊢ .proto : B) : Sim (.srt .U) B := by
  generalize e : Term.proto = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True)
  all_goals try trivial
  case proto => exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `stop` is similar to `proto` (Coq `sta_stop_uniq`). -/
lemma stop_unique {Γ B} (ty : Γ ⊢ .stop : B) : Sim .proto B := by
  generalize e : Term.stop = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True)
  all_goals try trivial
  case stop => exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of an `act` is similar to `proto` (Coq `sta_act0_uniq` / `sta_act1_uniq`, merged). -/
lemma act_unique {Γ b A B C i} (ty : Γ ⊢ .act b A B i : C) : Sim .proto C := by
  generalize e : Term.act b A B i = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing b A B i
  all_goals try trivial
  case act => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of `ch` is similar to `srt L` (Coq `sta_ch_uniq`). -/
lemma ch_unique {Γ b A B} (ty : Γ ⊢ .ch b A : B) : Sim (.srt .L) B := by
  generalize e : Term.ch b A = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing b A
  all_goals try trivial
  case ch => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of a channel is similar to a channel type (Coq `sta_cvar_uniq`). -/
lemma chan_unique {Γ b x A B} (ty : Γ ⊢ .chan (Chan.var_Chan x) : B) : Sim (.ch b A) B := by
  generalize e : Term.chan (Chan.var_Chan x) = m
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing b x A
  all_goals try trivial
  case chan => cases e; exact ⟨.refl, .ch, .refl⟩
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of a `fork` is similar to its session type (Coq `sta_fork_uniq`). -/
lemma fork_unique {Γ m A B} (ty : Γ ⊢ .fork A m : B) : Sim (.M (.ch false A)) B := by
  generalize e : Term.fork A m = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A m
  all_goals try trivial
  case fork => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of a `recv` is similar to a monadic pair type (Coq `sta_recv0_uniq` /
    `sta_recv1_uniq`, merged). -/
lemma recv_unique {Γ m A B C i r} (ty : Γ ⊢ .recv m i : C) :
    Sim (.M (.sig A (.ch r B) i .L)) C := by
  generalize e : Term.recv m i = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B m i r
  all_goals try trivial
  case recv => cases e; exact ⟨.refl, .M, .refl⟩
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of a `send` is similar to a function type into the monad (Coq `sta_send0_uniq` /
    `sta_send1_uniq`, merged). -/
lemma send_unique {Γ m A B C i r} (ty : Γ ⊢ .send m i : C) :
    Sim (.pi A (.M (.ch r B)) i .L) C := by
  generalize e : Term.send m i = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing A B m i r
  all_goals try trivial
  case send => cases e; exact ⟨.refl, .pi .M, .refl⟩
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- The type of a `close` is similar to `M unit` (Coq `sta_wait_uniq` / `sta_close_uniq`,
    merged over the `Bool`). -/
lemma close_unique {Γ b m A} (ty : Γ ⊢ .close b m : A) : Sim (.M .unit) A := by
  generalize e : Term.close b m = x
  rw [e] at ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing b m
  all_goals try trivial
  case close => cases e; exact Sim.refl _
  case conv eq _ _ ihm _ => exact (ihm e).transL eq

/-- Type uniqueness up to similarity (Coq `sta_uniq`). -/
lemma Typed.unique {Γ1 Γ2 m A B}
    (ty : Γ1 ⊢ m : A) : Γ2 ⊢ m : B → CtxSim Γ1 Γ2 → Sim A B := by
  induction ty using Typed.rec (motive_2 := fun _ _ => True) generalizing Γ2 B
  all_goals try trivial
  case srt => intro ty2 _; exact sort_unique ty2
  case var hs _ => intro ty2 csm; exact var_unique ty2 hs csm.sym
  case pi => intro ty2 _; exact pi_unique ty2
  case lam ihm => intro ty2 csm; exact lam_unique ty2 (fun t c => ihm t c) csm
  case app ihm _ => intro ty2 csm; exact app_unique ty2 (fun t => ihm t csm)
  case sig => intro ty2 _; exact sig_unique ty2
  case pair ihS ihm ihn =>
    intro ty2 csm
    exact pair_unique ty2 (fun tx ty => ⟨ihm tx csm, ihn ty csm⟩)
  case proj => intro ty2 _; exact proj_unique ty2
  case fix => intro ty2 _; exact fix_unique ty2
  case unit => intro ty2 _; exact unit_unique ty2
  case one => intro ty2 _; exact one_unique ty2
  case bool => intro ty2 _; exact bool_unique ty2
  case tt => intro ty2 _; exact tt_unique ty2
  case ff => intro ty2 _; exact ff_unique ty2
  case ite => intro ty2 _; exact ite_unique ty2
  case M => intro ty2 _; exact M_unique ty2
  case pure => intro ty2 _; exact pure_unique ty2
  case mlet => intro ty2 _; exact mlet_unique ty2
  case proto => intro ty2 _; exact proto_unique ty2
  case stop => intro ty2 _; exact stop_unique ty2
  case act => intro ty2 _; exact act_unique ty2
  case ch => intro ty2 _; exact ch_unique ty2
  case chan => intro ty2 _; exact chan_unique ty2
  case fork => intro ty2 _; exact fork_unique ty2
  case recv => intro ty2 _; exact recv_unique ty2
  case send => intro ty2 _; exact send_unique ty2
  case close => intro ty2 _; exact close_unique ty2
  case conv eq _ _ ihm _ =>
    intro ty2 csm
    exact (ihm ty2 csm).transR (ARS.conv_sym eq)

/-- Type uniqueness: a term has at most one sort (Coq `sta_unicity`). -/
theorem Typed.unicity {Γ m s t}
    (ty1 : Γ ⊢ m : .srt s) (ty2 : Γ ⊢ m : .srt t) : s = t :=
  sim_sort (ty1.unique ty2 (CtxSim.refl _))

end TLLC.Static
