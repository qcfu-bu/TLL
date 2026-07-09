import TLLC.Process.SoupStep
import TLLC.Process.SoupFlat
import TLLC.Process.SR
import TLLC.Dynamic.StepReflect
import TLLC.Spawning.Fidelity
import TLLC.Spawning.Simulation

/-!
# Reflection: every standard reduction step corresponds to a spawning-tree step

The converse of the simulation theorem (Lemma 5.86, `TLLC/Spawning/Simulation.lean`). Simulation
maps every spawning-tree step to a standard process reduction of the flattenings; `reflection`
maps every standard reduction of a flattening back to a spawning-tree step whose flattening is
structurally congruent to the reduct. Together they exhibit flattening as a bisimulation up to
structural congruence: the spawning-tree semantics is a sound *and complete* implementation of the
standard semantics. This theorem is not in the companion report.

The proof pivots on the soup characterization of structural congruence
(`TLLC/Process/Soup.lean`): a standard step of `t.flatten` becomes a machine step of its prenex
configuration (`step_soup`), which `soup_inv` replays on the tree — the fired thread pulls back to
a node body, the fired binder to a tree edge, and typing dispatches which endpoint is the parent —
producing a tree step whose flattening has a soup-equivalent prenex configuration.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic
open TLLC.Process (Config parConfig nuConfig prenex shiftAbove cswap liftBinders
  shiftAbove_lt shiftAbove_ge tren_ext tren_comp tren_id tsmap_ext tsmap_comp tsmap_id
  tren_pure_one SoupG SoupEquiv SoupStep Prim cvar)

/-! ## Machine steps relocate over configuration composition -/

lemma evalctx_cren_ext (M : EvalCtx) {ξ ζ : Nat → Nat} (h : ∀ x, ξ x = ζ x) :
    M.cren ξ = M.cren ζ := by
  rw [funext h]

/-- Occurrence counts split at the hole of an evaluation context. -/
lemma occurs_evalctx (i : Nat) (M : EvalCtx) (m : Term) :
    occurs i (M.eval m) = occurs i (M.eval (.pure .one)) + occurs i m := by
  induction M with
  | hole =>
      show occurs i m = occurs i (Term.pure .one) + occurs i m
      simp [occurs]
  | bnd M' n ih =>
      show occurs i (.mlet (M'.eval m) n) =
        occurs i (.mlet (M'.eval (.pure .one)) n) + occurs i m
      simp only [occurs]
      omega

/-- Renamings that agree on every explicitly occurring channel produce congruent terms: the
disagreements are confined to erased implicit positions (`CongrTerm.chan_im`). -/
lemma congrTerm_cren_of_occurs {m : Term} {ξ ζ : Nat → Nat}
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

lemma forall₂_congr_cren {ξ ζ : Nat → Nat} : ∀ ts : List Term,
    (∀ t ∈ ts, ∀ x, occurs x t ≠ 0 → ξ x = ζ x) →
    List.Forall₂ (TLLC.Process.CongrTerm .ex)
      (ts.map (fun t => t⟨ξ; (id : Nat → Nat)⟩))
      (ts.map (fun t => t⟨ζ; (id : Nat → Nat)⟩)) := by
  intro ts
  induction ts with
  | nil => intro _; exact List.Forall₂.nil
  | cons t ts ih =>
      intro h
      exact List.Forall₂.cons
        (congrTerm_cren_of_occurs (h t (by simp)))
        (ih (fun t' ht' => h t' (by simp [ht'])))

private lemma prim_parConfig_left {c₁ c₂ : Config} (d : Config) (h : Prim c₁ c₂) :
    SoupStep (parConfig c₁ d) (parConfig c₂ d) := by
  cases h with
  | @exp k m m' ts hstep =>
      simp only [parConfig, List.map_cons, List.cons_append]
      exact TLLC.Process.SoupStep.of_prim
        (TLLC.Process.Prim.exp (dynamic_step_crename hstep (shiftAbove k d.1)))
  | @fork k N A m ts =>
      have h0 : shiftAbove (k + 1) d.1 0 = 0 := shiftAbove_lt (by omega)
      simp only [parConfig, List.map_cons, List.cons_append]
      simp only [evalctx_cren]
      asimp
      rw [h0, show k + 1 + d.1 = (k + d.1) + 1 from by omega]
      refine TLLC.Process.SoupStep.of_prim ?_
      convert TLLC.Process.Prim.fork using 3
      · congr 1
        rw [evalctx_cren_comp, evalctx_cren_comp]
        exact evalctx_cren_ext N (fun x => by
          simp only [funcomp, shiftAbove]
          split_ifs <;> omega)
      · congr 1
        · asimp
          congr 1
          funext x
          show Chan.var_Chan (shiftAbove (k + 1) d.1 (x + 1)) =
            Chan.var_Chan (shiftAbove k d.1 x + 1)
          congr 1
          simp only [shiftAbove]
          split_ifs <;> omega
        · rw [List.map_append]
          congr 1
          · rw [tsmap_comp, tsmap_comp]
            exact tsmap_ext ts (fun x => by
              simp only [shiftAbove]
              split_ifs <;> omega)
          · rw [tsmap_comp]
            exact tsmap_ext d.2 (fun x => by omega)
  | @comIm k M N o ts =>
      have h0 : shiftAbove (k + 1) d.1 0 = 0 := shiftAbove_lt (by omega)
      simp only [parConfig, List.map_cons, List.cons_append]
      simp only [evalctx_cren]
      asimp
      rw [h0, show k + 1 + d.1 = (k + d.1) + 1 from by omega]
      exact TLLC.Process.SoupStep.of_prim TLLC.Process.Prim.comIm
  | @comEx k M N v ts hv =>
      have h0 : shiftAbove (k + 1) d.1 0 = 0 := shiftAbove_lt (by omega)
      simp only [parConfig, List.map_cons, List.cons_append]
      simp only [evalctx_cren]
      asimp
      rw [h0, show k + 1 + d.1 = (k + d.1) + 1 from by omega]
      exact TLLC.Process.SoupStep.of_prim
        (TLLC.Process.Prim.comEx (dynamic_val_crename hv (shiftAbove (k + 1) d.1)))
  | @close k M N ts hM hN hocc =>
      have h0 : shiftAbove (k + 1) d.1 0 = 0 := shiftAbove_lt (by omega)
      have hpre : ∀ x, shiftAbove (k + 1) d.1 x = 0 → x = 0 := by
        intro x hx
        by_contra hne
        simp only [shiftAbove] at hx
        split_ifs at hx <;> omega
      have hthread : ∀ (M₀ : EvalCtx), occurs 0 (M₀.eval (.pure .one)) = 0 →
          occurs 0 ((EvalCtx.cren (shiftAbove (k + 1) d.1) M₀).eval (.pure .one)) = 0 := by
        intro M₀ h₀
        have e : (EvalCtx.cren (shiftAbove (k + 1) d.1) M₀).eval (.pure .one) =
            (M₀.eval (.pure .one))⟨shiftAbove (k + 1) d.1; (id : Nat → Nat)⟩ := by
          rw [evalctx_cren, tren_pure_one]
        rw [e]
        exact occurs_cren_zero (fun x hx => by rw [hpre x hx]; exact h₀)
      simp only [parConfig, List.map_cons, List.cons_append]
      simp only [evalctx_cren]
      asimp
      rw [h0, show k + 1 + d.1 = (k + d.1) + 1 from by omega]
      refine ⟨_, _, ARS.Conv.refl,
        TLLC.Process.Prim.close (k := k + d.1)
          (M := EvalCtx.cren (shiftAbove (k + 1) d.1) M)
          (N := EvalCtx.cren (shiftAbove (k + 1) d.1) N)
          (ts := ts.map (fun n => n⟨shiftAbove (k + 1) d.1; (id : Nat → Nat)⟩) ++
            d.2.map (fun n => n⟨(· + (k + 1)); (id : Nat → Nat)⟩))
          (hthread M hM) (hthread N hN) ?_, ?_⟩
      · intro n hn
        rcases List.mem_append.mp hn with hn | hn
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn
          exact occurs_cren_zero (fun x hx => by rw [hpre x hx]; exact hocc t ht)
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn
          exact occurs_cren (fun x => by show x + (k + 1) ≠ 0; omega) t
      · -- the two unshift orders agree except at the dead binder, which occurs only implicitly
        have hpoint : ∀ x, x ≠ 0 →
            shiftAbove (k + 1) d.1 x - 1 = shiftAbove k d.1 (x - 1) := by
          intro x hx
          simp only [shiftAbove]
          split_ifs <;> omega
        have hthreadCongr : ∀ (M₀ : EvalCtx), occurs 0 (M₀.eval (.pure .one)) = 0 →
            TLLC.Process.CongrTerm .ex
              ((EvalCtx.cren ((· - 1) : Nat → Nat)
                (EvalCtx.cren (shiftAbove (k + 1) d.1) M₀)).eval (.pure .one))
              ((EvalCtx.cren (shiftAbove k d.1)
                (EvalCtx.cren ((· - 1) : Nat → Nat) M₀)).eval (.pure .one)) := by
          intro M₀ h₀
          have e1 : (EvalCtx.cren ((· - 1) : Nat → Nat)
              (EvalCtx.cren (shiftAbove (k + 1) d.1) M₀)).eval (.pure .one) =
              (M₀.eval (.pure .one))⟨fun x => shiftAbove (k + 1) d.1 x - 1;
                (id : Nat → Nat)⟩ := by
            rw [evalctx_cren_comp, evalctx_cren, tren_pure_one]
          have e2 : (EvalCtx.cren (shiftAbove k d.1)
              (EvalCtx.cren ((· - 1) : Nat → Nat) M₀)).eval (.pure .one) =
              (M₀.eval (.pure .one))⟨fun x => shiftAbove k d.1 (x - 1);
                (id : Nat → Nat)⟩ := by
            rw [evalctx_cren_comp, evalctx_cren, tren_pure_one]
          rw [e1, e2]
          refine congrTerm_cren_of_occurs (fun x hx => ?_)
          have hxne : x ≠ 0 := fun heq => hx (heq ▸ h₀)
          exact hpoint x hxne
        refine ARS.conv1 (TLLC.Process.SoupG.congr ?_)
        refine List.Forall₂.cons (hthreadCongr M hM) ?_
        refine List.Forall₂.cons (hthreadCongr N hN) ?_
        rw [List.map_append, tsmap_comp, tsmap_comp, tsmap_comp]
        refine TLLC.Process.forall₂_append ?_ ?_
        · refine forall₂_congr_cren ts (fun t ht x hx => ?_)
          have hxne : x ≠ 0 := fun heq => hx (heq ▸ hocc t ht)
          exact hpoint x hxne
        · rw [tsmap_ext d.2 (ξ := fun x => x + (k + 1) - 1) (ζ := (· + k))
            (fun x => by show x + (k + 1) - 1 = x + k; omega)]
          exact TLLC.Process.forall₂_congr_refl _

lemma soupStep_parConfig_left {c c' : Config} (d : Config) (h : SoupStep c c') :
    SoupStep (parConfig c d) (parConfig c' d) := by
  obtain ⟨c₁, c₂, e1, prim, e2⟩ := h
  exact TLLC.Process.SoupStep.congr (TLLC.Process.SoupEquiv.parConfig_left d e1)
    (prim_parConfig_left d prim) (TLLC.Process.SoupEquiv.parConfig_left d e2)

lemma soupStep_parConfig_right (c : Config) {d d' : Config} (h : SoupStep d d') :
    SoupStep (parConfig c d) (parConfig c d') :=
  TLLC.Process.SoupStep.congr (TLLC.Process.parConfig_comm c d)
    (soupStep_parConfig_left c h) (TLLC.Process.parConfig_comm d' c)

/-! ## Step-to-soup -/

private lemma prenex_nu_par_tm_tm (a b : Term) :
    prenex (.nu (.par (.tm a) (.tm b))) = (1, [a, b]) := by
  simp only [TLLC.Process.prenex_nu, TLLC.Process.prenex_par, TLLC.Process.prenex_tm,
    TLLC.Process.parConfig, TLLC.Process.nuConfig, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [tren_ext a (ζ := (id : Nat → Nat)) (fun x => by
      simp only [shiftAbove, id_eq]
      split_ifs <;> omega),
    tren_ext b (ζ := (id : Nat → Nat)) (fun x => by simp), tren_id, tren_id]

private lemma prenex_par_tm_tm (a b : Term) :
    prenex (.par (.tm a) (.tm b)) = (0, [a, b]) := by
  simp only [TLLC.Process.prenex_par, TLLC.Process.prenex_tm,
    TLLC.Process.parConfig, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [tren_ext a (ζ := (id : Nat → Nat)) (fun x => by
      simp only [shiftAbove, id_eq]
      split_ifs <;> omega),
    tren_ext b (ζ := (id : Nat → Nat)) (fun x => by simp), tren_id, tren_id]

/-- Every reduction of a well-typed process is a soup step of the prenex forms. Typing supplies
the linearity facts that keep the `close` machine rule's side conditions available: the two
endpoints of the closed channel are its only explicit occurrences. -/
theorem step_soup {P Q : Proc} (st : TLLC.Process.Step P Q) :
    ∀ {Θ}, TLLC.Process.Typed Θ P → SoupStep (prenex P) (prenex Q) := by
  induction st with
  | exp h =>
      intro Θ _
      rw [TLLC.Process.prenex_tm, TLLC.Process.prenex_tm]
      exact TLLC.Process.SoupStep.of_prim (TLLC.Process.Prim.exp (ts := []) h)
  | @fork A m m' N N' em eN =>
      intro Θ _
      subst em
      subst eN
      rw [TLLC.Process.prenex_tm, prenex_nu_par_tm_tm]
      exact TLLC.Process.SoupStep.of_prim (TLLC.Process.Prim.fork (k := 0) (ts := []))
  | comIm =>
      intro Θ _
      rw [prenex_nu_par_tm_tm, prenex_nu_par_tm_tm]
      exact TLLC.Process.SoupStep.of_prim (TLLC.Process.Prim.comIm (k := 0) (ts := []))
  | comEx hv =>
      intro Θ _
      rw [prenex_nu_par_tm_tm, prenex_nu_par_tm_tm]
      exact TLLC.Process.SoupStep.of_prim (TLLC.Process.Prim.comEx (k := 0) (ts := []) hv)
  | @«end» M N M' N' eM eN =>
      intro Θ ty
      subst eM
      subst eN
      have hredex : ∀ b : Bool, occurs 0 (Term.close b (cvar 0)) = 1 := by
        intro b
        show occurs 0 (Term.chan (Chan.var_Chan 0)) = 1
        simp [occurs]
      cases ty with
      | res tyA typ =>
      cases typ with
      | par mrg ty1 ty2 =>
      cases ty1 with
      | exp tym =>
      cases ty2 with
      | exp tyn =>
      cases mrg with
      | split mrg' =>
          have h1 : occurs 0 (M.eval (.close true (cvar 0))) = 1 :=
            tym.occurs1 CvarPos.one
          have h2 : occurs 0 (N.eval (.close false (cvar 0))) = 1 :=
            tyn.occurs1 CvarPos.one
          rw [occurs_evalctx, hredex true] at h1
          rw [occurs_evalctx, hredex false] at h2
          rw [prenex_nu_par_tm_tm, prenex_par_tm_tm]
          exact TLLC.Process.SoupStep.of_prim
            (TLLC.Process.Prim.close (k := 0) (ts := []) (by omega) (by omega)
              (fun n hn => by cases hn))
      | bothL mrg' =>
          exfalso
          have h2 : occurs 0 (N.eval (.close false (cvar 0))) = 0 :=
            tyn.occurs0 CvarPos.none
          rw [occurs_evalctx, hredex false] at h2
          omega
      | bothR mrg' =>
          exfalso
          have h1 : occurs 0 (M.eval (.close true (cvar 0))) = 0 :=
            tym.occurs0 CvarPos.none
          rw [occurs_evalctx, hredex true] at h1
          omega
  | par _ ih =>
      intro Θ ty
      cases ty with
      | par mrg typ tyq =>
          rw [TLLC.Process.prenex_par, TLLC.Process.prenex_par]
          exact soupStep_parConfig_right _ (ih tyq)
  | res _ ih =>
      intro Θ ty
      cases ty with
      | res tyA typ =>
          rw [TLLC.Process.prenex_nu, TLLC.Process.prenex_nu]
          exact TLLC.Process.SoupStep.nuConfig (ih typ)
  | congr e1 _ e2 ih =>
      intro Θ ty
      exact TLLC.Process.SoupStep.congr (TLLC.Process.congruence_soup e1)
        (ih (TLLC.Process.Typed.congr ty e1)) (TLLC.Process.congruence_soup e2)

/-- Replaying a soup step of a valid tree's flattening on the tree itself. -/
theorem soup_inv {t : Tree} {c₂ : TLLC.Process.Config}
    (typed : Typed t) (distinct : Distinct t)
    (st : TLLC.Process.SoupStep (TLLC.Process.prenex t.flatten) c₂) :
    ∃ t', Step t t' ∧ TLLC.Process.SoupEquiv (TLLC.Process.prenex t'.flatten) c₂ := by
  sorry

/-- **Reflection.** Every standard reduction step of the flattening of a valid spawning tree
corresponds to a spawning-tree reduction step: the tree can take a step whose flattening is
structurally congruent to the reduct. Converse of Lemma 5.86. -/
theorem reflection {t : Tree} {P : Proc}
    (typed : Typed t) (distinct : Distinct t)
    (step : TLLC.Process.Step t.flatten P) :
    ∃ t', Step t t' ∧ TLLC.Process.Congruence P t'.flatten := by
  obtain ⟨t', tstep, se⟩ := soup_inv typed distinct (step_soup step typed.flatten_typed)
  refine ⟨t', tstep, ?_⟩
  exact ARS.conv_trans (TLLC.Process.prenex_sound P)
    (ARS.conv_trans (ARS.conv_sym (TLLC.Process.soupEquiv_congr se))
      (ARS.conv_sym (TLLC.Process.prenex_sound t'.flatten)))

/-- Reflection along multi-step reduction: fidelity carries validity and distinctness across the
replayed tree steps, and the built-in congruence saturation of `Process.Step` re-anchors each
standard step on the flattening of the current tree. -/
theorem reflection_red {t : Tree} {P : Proc}
    (typed : Typed t) (distinct : Distinct t)
    (red : TLLC.Process.Red t.flatten P) :
    ∃ t', Red t t' ∧ TLLC.Process.Congruence P t'.flatten := by
  induction red with
  | refl => exact ⟨t, ARS.Star.refl, ARS.Conv.refl⟩
  | @tail y z _ st ih =>
      obtain ⟨t₁, red₁, congr₁⟩ := ih
      have inv := typed.fidelity_red distinct red₁
      have st₁ : TLLC.Process.Step t₁.flatten z :=
        TLLC.Process.Step.congr (ARS.conv_sym congr₁) st ARS.Conv.refl
      obtain ⟨t₂, tstep, congr₂⟩ := reflection inv.1 inv.2 st₁
      exact ⟨t₂, ARS.Star.tail red₁ tstep, congr₂⟩

end TLLC.Spawning
