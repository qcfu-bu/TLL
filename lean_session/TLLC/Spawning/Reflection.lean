import TLLC.Process.SoupStep
import TLLC.Process.SoupFlat
import TLLC.Process.SR
import TLLC.Dynamic.StepReflect
import TLLC.Spawning.Fidelity
import TLLC.Spawning.Simulation
import TLLC.Spawning.TreeSoup
import TLLC.Spawning.Progress

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


/-! ## Typing transport along channel permutations -/

/-- The `j`-fold binder lift of the front channel exchange. -/
def upCexchN : Nat → (Nat → Chan)
  | 0 => Dynamic.cexch
  | j + 1 => up_Chan_Chan (upCexchN j)

private lemma csubst_ren_up (σ : Nat → Chan) :
    ∀ x, TLLC.Static.csubst_ren (up_Chan_Chan σ) x =
      upRen_Chan_Chan (TLLC.Static.csubst_ren σ) x := by
  intro x
  cases x with
  | zero => rfl
  | succ x =>
      cases hσ : σ x with
      | var_Chan y =>
          have e1 : up_Chan_Chan σ (x + 1) = Chan.var_Chan (y + 1) := by
            asimp
            simp only [funcomp]
            rw [hσ]
            asimp
          have e2 : TLLC.Static.csubst_ren σ x = y := by
            unfold TLLC.Static.csubst_ren
            rw [hσ]
          rw [TLLC.Process.upRen_CC_succ, e2]
          unfold TLLC.Static.csubst_ren
          rw [e1]

private lemma liftBinders_zero (ξ : Nat → Nat) :
    ∀ x, liftBinders 0 ξ x = ξ x := by
  intro x
  rw [TLLC.Process.liftBinders_ge _ (Nat.zero_le x), Nat.sub_zero, Nat.zero_add]

private lemma upCexchN_ren (j : Nat) :
    ∀ x, TLLC.Static.csubst_ren (upCexchN j) x = cswap j (j + 1) x := by
  induction j with
  | zero =>
      intro x
      show TLLC.Process.exch_ren x = cswap 0 1 x
      rw [← liftBinders_zero TLLC.Process.exch_ren x]
      exact TLLC.Process.liftBinders_exch_ren 0 x
  | succ j ih =>
      intro x
      rw [show upCexchN (j + 1) = up_Chan_Chan (upCexchN j) from rfl, csubst_ren_up]
      cases x with
      | zero =>
          rw [TLLC.Process.upRen_CC_zero, TLLC.Process.cswap_ne (by omega) (by omega)]
      | succ x =>
          rw [TLLC.Process.upRen_CC_succ, ih x]
          unfold TLLC.Process.cswap
          split_ifs <;> omega

private lemma procWf_swap_front {s0 s1 : Slot} {Θ : PCtx}
    (wf : ProcWf (s0 :: s1 :: Θ)) : ProcWf (s1 :: s0 :: Θ) := by
  cases wf with
  | one wf' ty0 =>
      cases wf' with
      | one wf'' ty1 => exact .one (.one wf'' ty0) ty1
      | both wf'' ty1 => exact .both (.one wf'' ty0) ty1
      | none wf'' => exact .none (.one wf'' ty0)
  | both wf' ty0 =>
      cases wf' with
      | one wf'' ty1 => exact .one (.both wf'' ty0) ty1
      | both wf'' ty1 => exact .both (.both wf'' ty0) ty1
      | none wf'' => exact .none (.both wf'' ty0)
  | none wf' =>
      cases wf' with
      | one wf'' ty1 => exact .one (.none wf'') ty1
      | both wf'' ty1 => exact .both (.none wf'') ty1
      | none wf'' => exact .none (.none wf'')

private lemma agree_swap_at : ∀ (j : Nat) (Θ : PCtx), ProcWf Θ → j + 1 < Θ.length →
    ∃ Θ', Θ'.length = Θ.length ∧
      TLLC.Dynamic.AgreeCSubst Θ' (upCexchN j) Θ := by
  intro j
  induction j with
  | zero =>
      intro Θ wf hlen
      match Θ, wf with
      | s0 :: s1 :: Θ', wf =>
          exact ⟨s1 :: s0 :: Θ', rfl, AgreeCSubst.swap wf⟩
  | succ j ih =>
      intro Θ wf hlen
      match Θ, wf with
      | .one r A :: Θ₀, ProcWf.one wf₀ tyA =>
          obtain ⟨Θ', hl, agr⟩ := ih Θ₀ wf₀ (by simpa using Nat.lt_of_succ_lt_succ hlen)
          exact ⟨.one r A :: Θ', by simp [hl], AgreeCSubst.ty agr tyA⟩
      | .both A :: Θ₀, ProcWf.both wf₀ tyA =>
          obtain ⟨Θ', hl, agr⟩ := ih Θ₀ wf₀ (by simpa using Nat.lt_of_succ_lt_succ hlen)
          exact ⟨.both A :: Θ', by simp [hl], AgreeCSubst.both agr tyA⟩
      | .none :: Θ₀, ProcWf.none wf₀ =>
          obtain ⟨Θ', hl, agr⟩ := ih Θ₀ wf₀ (by simpa using Nat.lt_of_succ_lt_succ hlen)
          exact ⟨.none :: Θ', by simp [hl], AgreeCSubst.n agr⟩

/-- Adjacent binder transpositions preserve typing (context transposed alongside). -/
private lemma typed_swap_adj {Θ : PCtx} {m A} (j : Nat)
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A)
    (hlen : j + 1 < Θ.length) :
    ∃ Θ' : PCtx, Θ'.length = Θ.length ∧
      Θ' ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
        m⟨cswap j (j + 1); (id : Nat → Nat)⟩ : A := by
  obtain ⟨Θ', hl, agr⟩ := agree_swap_at j Θ ty.procWf hlen
  refine ⟨Θ', hl, ?_⟩
  have h := ty.csubstitution agr
  have e : m[upCexchN j; Term.var_Term] =
      m⟨cswap j (j + 1); (id : Nat → Nat)⟩ := by
    rw [← TLLC.Static.csubst_cren]
    exact tren_ext m (upCexchN_ren j)
  rw [e] at h
  exact h

private lemma typed_cswap_id {Θ : PCtx} {m A} (i j : Nat) (hid : ∀ x, cswap i j x = x)
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) :
    Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m⟨cswap i j; (id : Nat → Nat)⟩ : A := by
  rw [tren_ext m (ζ := (id : Nat → Nat)) (fun x => by simp only [id_eq]; exact hid x),
    tren_id]
  exact ty

private lemma typed_swap_le {A : Term} :
    ∀ (fuel j : Nat), j ≤ fuel → ∀ (Θ : PCtx) (m : Term) (i : Nat), i ≤ j →
      j + 1 ≤ Θ.length →
      (Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) →
      ∃ Θ' : PCtx, Θ'.length = Θ.length ∧
        (Θ' ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          m⟨cswap i j; (id : Nat → Nat)⟩ : A) := by
  intro fuel
  induction fuel with
  | zero =>
      intro j hj Θ m i hij hlen ty
      refine ⟨Θ, rfl, typed_cswap_id i j (fun x => by
        unfold TLLC.Process.cswap
        split_ifs <;> omega) ty⟩
  | succ fuel ihf =>
      intro j hj Θ m i hij hlen ty
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · refine ⟨Θ, rfl, typed_cswap_id i i (fun x => by
          unfold TLLC.Process.cswap
          split_ifs <;> omega) ty⟩
      · rcases Nat.eq_or_lt_of_le hlt with heq1 | hlt'
        · obtain ⟨Θ', hl, ty'⟩ := typed_swap_adj i ty (by omega)
          refine ⟨Θ', hl, ?_⟩
          rw [tren_ext m (ξ := cswap i j) (ζ := cswap i (i + 1)) (fun x => by
            rw [← heq1])]
          exact ty'
        · obtain ⟨Θ1, hl1, ty1⟩ := typed_swap_adj (j - 1) ty (by omega)
          rw [tren_ext m (ξ := cswap (j - 1) (j - 1 + 1)) (ζ := cswap (j - 1) j)
            (fun x => by rw [show j - 1 + 1 = j from by omega])] at ty1
          obtain ⟨Θ2, hl2, ty2⟩ := ihf (j - 1) (by omega) Θ1 _ i (by omega)
            (by omega) ty1
          obtain ⟨Θ3, hl3, ty3⟩ := typed_swap_adj (j - 1) ty2 (by omega)
          refine ⟨Θ3, by omega, ?_⟩
          rw [tren_comp, tren_comp] at ty3
          rw [tren_ext m (ξ := cswap i j)
            (ζ := fun x => cswap (j - 1) (j - 1 + 1)
              (cswap i (j - 1) (cswap (j - 1) j x)))
            (fun x => by
              show cswap i j x =
                cswap (j - 1) (j - 1 + 1) (cswap i (j - 1) (cswap (j - 1) j x))
              rw [show j - 1 + 1 = j from by omega]
              unfold TLLC.Process.cswap
              split_ifs <;> omega)]
          exact ty3

/-- General binder transpositions preserve typing. -/
private lemma typed_swap {Θ : PCtx} {m A} (i j : Nat)
    (hi : i < Θ.length) (hj : j < Θ.length)
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) :
    ∃ Θ' : PCtx, Θ'.length = Θ.length ∧
      (Θ' ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
        m⟨cswap i j; (id : Nat → Nat)⟩ : A) := by
  rcases Nat.lt_or_ge i j with h | h
  · exact typed_swap_le j j (Nat.le_refl j) Θ m i (by omega) (by omega) ty
  · obtain ⟨Θ', hl, ty'⟩ := typed_swap_le i i (Nat.le_refl i) Θ m j (by omega)
      (by omega) ty
    refine ⟨Θ', hl, ?_⟩
    rw [tren_ext m (ξ := cswap i j) (ζ := cswap j i) (fun x => by
      unfold TLLC.Process.cswap
      split_ifs <;> omega)]
    exact ty'

private lemma pctxEmptyRel_pad (Θ : PCtx) (p : Nat) :
    TLLC.Process.PCtxEmptyRel Θ (Θ ++ List.replicate p Slot.none) := by
  induction Θ with
  | nil =>
      refine TLLC.Process.PCtxEmptyRel.empty PEmpty.nil ?_
      induction p with
      | zero => exact PEmpty.nil
      | succ p ih => exact PEmpty.none ih
  | cons s Θ ih =>
      cases s with
      | none => exact TLLC.Process.PCtxEmptyRel.none ih
      | one r A₀ => exact TLLC.Process.PCtxEmptyRel.one ih
      | both A₀ => exact TLLC.Process.PCtxEmptyRel.both ih

private lemma typed_cren_bounded {A : Term} :
    ∀ (n : Nat) (Θ : PCtx) (m : Term) (ξ ζ : Nat → Nat),
      (∀ x, ζ (ξ x) = x) → (∀ x, ξ (ζ x) = x) → (∀ x, n ≤ x → ξ x = x) →
      n ≤ Θ.length →
      (Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) →
      ∃ Θ' : PCtx, Θ'.length = Θ.length ∧
        (Θ' ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m⟨ξ; (id : Nat → Nat)⟩ : A) := by
  intro n
  induction n with
  | zero =>
      intro Θ m ξ ζ _ _ hfix _ ty
      rw [tren_ext m (ζ := (id : Nat → Nat)) (fun x => by
        simp only [id_eq]
        exact hfix x (Nat.zero_le x)), tren_id]
      exact ⟨Θ, rfl, ty⟩
  | succ n ihn =>
      intro Θ m ξ ζ hζξ hξζ hfix hlen ty
      by_cases hfixn : ξ n = n
      · refine ihn Θ m ξ ζ hζξ hξζ ?_ (by omega) ty
        intro x hx
        rcases Nat.eq_or_lt_of_le hx with rfl | h'
        · exact hfixn
        · exact hfix x h'
      · have hξa : ξ (ζ n) = n := hξζ n
        have haltn : ζ n < n := by
          rcases Nat.lt_or_ge (ζ n) n with h | h
          · exact h
          · exfalso
            rcases Nat.eq_or_lt_of_le h with heq | h'
            · rw [← heq] at hξa
              exact hfixn hξa
            · have := hfix (ζ n) h'
              omega
        obtain ⟨Θ1, hl1, ty1⟩ := typed_swap (ζ n) n (by omega) (by omega) ty
        obtain ⟨Θ2, hl2, ty2⟩ := ihn Θ1 _ (fun x => ξ (cswap (ζ n) n x))
          (fun x => cswap (ζ n) n (ζ x))
          (fun x => by
            show cswap (ζ n) n (ζ (ξ (cswap (ζ n) n x))) = x
            rw [hζξ (cswap (ζ n) n x), TLLC.Process.cswap_invol])
          (fun x => by
            show ξ (cswap (ζ n) n (cswap (ζ n) n (ζ x))) = x
            rw [TLLC.Process.cswap_invol, hξζ])
          (fun x hx => by
            rcases Nat.eq_or_lt_of_le hx with rfl | h'
            · show ξ (cswap (ζ n) n n) = n
              rw [TLLC.Process.cswap_right, hξa]
            · show ξ (cswap (ζ n) n x) = x
              rw [TLLC.Process.cswap_ne (by omega) (by omega), hfix x h'])
          (by omega) ty1
        refine ⟨Θ2, by omega, ?_⟩
        rw [tren_comp] at ty2
        rw [tren_ext m (ξ := ξ)
          (ζ := fun x => ξ (cswap (ζ n) n (cswap (ζ n) n x)))
          (fun x => by
            show ξ x = ξ (cswap (ζ n) n (cswap (ζ n) n x))
            rw [TLLC.Process.cswap_invol])]
        exact ty2

/-- Bounded channel bijections preserve typing of closed computations (up to relocating the
process context). -/
lemma typed_cren_perm {Θ : PCtx} {m A} (ξ ζ : Nat → Nat)
    (hζξ : ∀ x, ζ (ξ x) = x) (hξζ : ∀ x, ξ (ζ x) = x) (n : Nat)
    (hfix : ∀ x, n ≤ x → ξ x = x)
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) :
    ∃ Θ' : PCtx, Θ' ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
      m⟨ξ; (id : Nat → Nat)⟩ : A := by
  have typ := TLLC.Process.Dynamic.Typed.pctxEmptyRel ty
    (pctxEmptyRel_pad Θ (n - Θ.length))
  obtain ⟨Θ', _, ty'⟩ := typed_cren_bounded n _ m ξ ζ hζξ hξζ hfix
    (by simp [List.length_replicate]; omega) typ
  exact ⟨Θ', ty'⟩

/-! ## Replaying a soup step on the tree -/

private lemma nuN_typed_strip : ∀ (k : Nat) {Θ : PCtx} {p : Proc},
    TLLC.Process.Typed Θ (TLLC.Process.nuN k p) → ∃ Θ', TLLC.Process.Typed Θ' p := by
  intro k
  induction k with
  | zero =>
      intro Θ p ty
      exact ⟨Θ, ty⟩
  | succ k ih =>
      intro Θ p ty
      rw [TLLC.Process.nuN_succ] at ty
      cases ty with
      | res tyA typ => exact ih typ

private lemma parAllL_typed_inv : ∀ (ts : List Term) (acc : Proc) {Θ : PCtx},
    TLLC.Process.Typed Θ (TLLC.Process.parAllL acc ts) →
    (∃ Θa, TLLC.Process.Typed Θa acc) ∧
      ∀ m ∈ ts, ∃ Θ', Θ' ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M .unit := by
  intro ts
  induction ts with
  | nil =>
      intro acc Θ ty
      exact ⟨⟨Θ, ty⟩, by simp⟩
  | cons m ts ih =>
      intro acc Θ ty
      rw [TLLC.Process.parAllL_cons] at ty
      obtain ⟨⟨Θa, typar⟩, hts⟩ := ih _ ty
      cases typar with
      | par mrg tyacc tytm =>
          cases tytm with
          | exp tym =>
              refine ⟨⟨_, tyacc⟩, ?_⟩
              intro m' hm'
              rcases List.mem_cons.mp hm' with rfl | hm'
              · exact ⟨_, tym⟩
              · exact hts m' hm'

/-- Every thread of the prenex soup of a valid tree is a well-typed closed computation. -/
lemma flatten_threads_typed {t : Tree} (ty : Typed t) :
    ∀ m ∈ (prenex t.flatten).2,
      ∃ Θ, Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M .unit := by
  have h1 := TLLC.Process.Typed.congr ty.flatten_typed
    (TLLC.Process.prenex_sound t.flatten)
  obtain ⟨Θ', h2⟩ := nuN_typed_strip (prenex t.flatten).1
    (p := TLLC.Process.soupThreads (prenex t.flatten).2) h1
  rw [TLLC.Process.soupThreads_eq] at h2
  exact (parAllL_typed_inv _ _ h2).2

private lemma pure_one_no_step {n : Term} (h : (Term.pure .one) ~>> n) : False := by
  cases h with
  | pure h' => cases h'

/-- Split a list at a member position, tracking `set`. -/
private lemma list_split_set {ts : List Term} {i : Nat} {m n : Term}
    (h : getElem? ts i = some m) :
    ts = ts.take i ++ m :: ts.drop (i + 1) ∧
      ts.set i n = ts.take i ++ n :: ts.drop (i + 1) := by
  have hlt : i < ts.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  rw [List.getElem?_eq_getElem hlt] at h
  have hm := Option.some.inj h
  constructor
  · conv_lhs => rw [← List.take_append_drop i ts]
    rw [List.drop_eq_getElem_cons hlt, hm]
  · rw [List.set_eq_take_append_cons_drop, if_pos hlt]

/-! ## Shape reflection through congruence and renaming -/

/-- Explicit structural congruence preserves the channel-occurrence count: `occurs` counts
exactly the explicit positions, which `.ex`-congruence relates rigidly (`chan_ex`); the implicit
positions where `chan_im` may rewrite channels are skipped by `occurs`. -/
lemma congrTerm_occurs {r : Rlv} {m m' : Term}
    (e : TLLC.Process.CongrTerm r m m') :
    ∀ i, r = .ex → occurs i m = occurs i m' := by
  induction e with
  | var => intro i _; rfl
  | srt => intro i _; rfl
  | pi _ _ => intro i _; rfl
  | lam _ _ _ ihm => intro i h; simp only [occurs, ihm i h]
  | @app _ _ _ _ r1 r2 _ _ ihm ihn =>
      intro i h
      cases r2 with
      | im => simp only [occurs, ihm i h]
      | ex =>
          subst h
          simp only [occurs, ihm i rfl, ihn i rfl]
  | sig _ _ => intro i _; rfl
  | @pair _ _ _ _ r1 r2 _ _ _ ihm ihn =>
      intro i h
      cases r2 with
      | im => simp only [occurs, ihn i h]
      | ex =>
          subst h
          simp only [occurs, ihm i rfl, ihn i rfl]
  | proj _ _ _ _ ihm ihn => intro i h; simp only [occurs, ihm i h, ihn i h]
  | fix _ _ _ ihm => intro i h; simp only [occurs, ihm i h]
  | unit => intro i _; rfl
  | one => intro i _; rfl
  | bool => intro i _; rfl
  | tt => intro i _; rfl
  | ff => intro i _; rfl
  | ite _ _ _ _ _ ihm ihn1 ihn2 =>
      intro i h
      simp only [occurs, ihm i h, ihn1 i h, ihn2 i h]
  | M _ => intro i _; rfl
  | pure _ ihm => intro i h; simp only [occurs, ihm i h]
  | mlet _ _ ihm ihn => intro i h; simp only [occurs, ihm i h, ihn i h]
  | proto => intro i _; rfl
  | stop => intro i _; rfl
  | act _ _ => intro i _; rfl
  | ch _ => intro i _; rfl
  | chan_im => intro i h; simp at h
  | chan_ex => intro i _; rfl
  | fork _ _ _ ihm => intro i h; simp only [occurs, ihm i h]
  | recv _ ihm => intro i h; simp only [occurs, ihm i h]
  | send _ ihm => intro i h; simp only [occurs, ihm i h]
  | close _ ihm => intro i h; simp only [occurs, ihm i h]
  | box => intro i _; rfl

/-- Injective channel renamings translate occurrence counts exactly. -/
private lemma occurs_cren_inj {ξ : Nat → Nat} (inj : ∀ x y, ξ x = ξ y → x = y) (e : Nat) :
    ∀ m : Term, occurs (ξ e) (m⟨ξ; (id : Nat → Nat)⟩) = occurs e m := by
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
      asimp at ihm ihn1 ihn2 ⊢; simp only [occurs, ihm, ihn1, ihn2]
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
          show (if ξ y = ξ e then 1 else 0) = (if y = e then 1 else 0)
          split_ifs with h1 h2 <;> first | rfl | omega | (exact absurd (inj _ _ h1) h2) |
            (rename_i h3; exact absurd (congrArg ξ h3) h1)
  | fork _ _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | recv _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | send _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | close _ _ ihm => asimp at ihm ⊢; simp only [occurs, ihm]
  | box => rfl

/-- Pointwise explicit congruence of evaluation contexts. -/
inductive CongrCtx : EvalCtx → EvalCtx → Prop where
  | hole : CongrCtx .hole .hole
  | bnd {M M' : EvalCtx} {n n' : Term} :
    CongrCtx M M' →
    TLLC.Process.CongrTerm .ex n n' →
    CongrCtx (.bnd M n) (.bnd M' n')

lemma CongrCtx.eval {M M' : EvalCtx} (h : CongrCtx M M') :
    ∀ {n n' : Term}, TLLC.Process.CongrTerm .ex n n' →
      TLLC.Process.CongrTerm .ex (M.eval n) (M'.eval n') := by
  induction h with
  | hole => intro n n' e; exact e
  | bnd _ eb ih =>
      intro n n' e
      exact TLLC.Process.CongrTerm.mlet (ih e) eb

lemma CongrCtx.cren {M M' : EvalCtx} (h : CongrCtx M M') (ξ : Nat → Nat) :
    CongrCtx (EvalCtx.cren ξ M) (EvalCtx.cren ξ M') := by
  induction h with
  | hole => exact .hole
  | bnd _ eb ih => exact .bnd ih (eb.crename ξ)

/-- Invert an explicit congruence against an evaluation-context decomposition of the right side:
the left side decomposes with a congruent context and a congruent filler. -/
lemma congrTerm_eval_inv : ∀ (N : EvalCtx) {m r' : Term},
    TLLC.Process.CongrTerm .ex m (N.eval r') →
    ∃ (N₀ : EvalCtx) (r₀ : Term), m = N₀.eval r₀ ∧ CongrCtx N₀ N ∧
      TLLC.Process.CongrTerm .ex r₀ r' := by
  intro N
  induction N with
  | hole => intro m r' h; exact ⟨.hole, m, rfl, .hole, h⟩
  | bnd N' b ih =>
      intro m r' h
      simp only [EvalCtx.eval] at h
      cases h with
      | mlet em eb =>
          obtain ⟨N₀, r₀, rfl, hctx, hr⟩ := ih em
          exact ⟨.bnd N₀ _, r₀, rfl, .bnd hctx eb, hr⟩

/-- Reflect an evaluation-context decomposition through a channel renaming. -/
lemma eval_cren_reflect {ξ : Nat → Nat} : ∀ (N₁ : EvalCtx) {m r₁ : Term},
    m⟨ξ; (id : Nat → Nat)⟩ = N₁.eval r₁ →
    ∃ (N₀ : EvalCtx) (r₀ : Term), m = N₀.eval r₀ ∧ N₁ = EvalCtx.cren ξ N₀ ∧
      r₁ = r₀⟨ξ; (id : Nat → Nat)⟩ := by
  intro N₁
  induction N₁ with
  | hole =>
      intro m r₁ h
      exact ⟨.hole, m, rfl, rfl, h.symm⟩
  | bnd N' b ih =>
      intro m r₁ h
      simp only [EvalCtx.eval] at h
      cases m <;> asimp at h <;> try simp at h
      next m₀ n₀ =>
        obtain ⟨h1, h2⟩ := h
        obtain ⟨N₀, r₀, rfl, rfl, rfl⟩ := ih h1
        refine ⟨.bnd N₀ n₀, r₀, ?_, ?_, rfl⟩
        · show Term.mlet (N₀.eval r₀) n₀ = Term.mlet (N₀.eval r₀) n₀
          rfl
        · show EvalCtx.bnd (EvalCtx.cren ξ N₀) b =
            .bnd (EvalCtx.cren ξ N₀) (n₀⟨ξ; (id : Nat → Nat)⟩)
          rw [← h2]

/-- Pull a fork redex back through congruence and a channel renaming. -/
private lemma pull_fork {ξ : Nat → Nat} {m₀ : Term} {N : EvalCtx} {A m : Term}
    (h : TLLC.Process.CongrTerm .ex (m₀⟨ξ; (id : Nat → Nat)⟩) (N.eval (.fork A m))) :
    ∃ (N₀ : EvalCtx) (A₀ n₀ : Term),
      m₀ = N₀.eval (.fork A₀ n₀) ∧
      CongrCtx (EvalCtx.cren ξ N₀) N ∧
      TLLC.Process.CongrTerm .ex (n₀⟨ξ; (id : Nat → Nat)⟩) m := by
  obtain ⟨N₁, r₁, heq, hctx, hr⟩ := congrTerm_eval_inv N h
  cases hr with
  | fork eA em =>
      obtain ⟨N₀, r₀, rfl, rfl, hre⟩ := eval_cren_reflect N₁ heq
      cases r₀ <;> asimp at hre <;> try simp at hre
      next A₀ n₀ =>
        obtain ⟨hA, hn⟩ := hre
        refine ⟨N₀, A₀, n₀, rfl, hctx, ?_⟩
        rw [hn] at em
        exact em

/-- Pull a send redex on binder `0` back through congruence and a channel renaming. -/
private lemma pull_send {ξ : Nat → Nat} {m₀ : Term} {N : EvalCtx} {o : Term} {rv : Rlv}
    (h : TLLC.Process.CongrTerm .ex (m₀⟨ξ; (id : Nat → Nat)⟩)
      (N.eval (.app (.send (cvar 0) rv) o rv))) :
    ∃ (N₀ : EvalCtx) (e : Nat) (o₀ : Term),
      m₀ = N₀.eval (.app (.send (cvar e) rv) o₀ rv) ∧ ξ e = 0 ∧
      CongrCtx (EvalCtx.cren ξ N₀) N ∧
      TLLC.Process.CongrTerm (TLLC.Process.under .ex rv) (o₀⟨ξ; (id : Nat → Nat)⟩) o := by
  obtain ⟨N₁, r₁, heq, hctx, hr⟩ := congrTerm_eval_inv N h
  cases hr with
  | app es eo =>
      cases es with
      | send ec =>
          cases ec with
          | chan_ex =>
              obtain ⟨N₀, r₀, rfl, rfl, hre⟩ := eval_cren_reflect N₁ heq
              cases r₀ <;> asimp at hre <;> try simp at hre
              next u v rv₀ =>
                obtain ⟨hu, hv, hrv⟩ := hre
                subst hrv
                cases u <;> asimp at hu <;> try simp at hu
                next w rv₁ =>
                  obtain ⟨hw, hrv₁⟩ := hu
                  subst hrv₁
                  cases w <;> asimp at hw <;> try simp at hw
                  next ch =>
                    cases ch with
                    | var_Chan e =>
                        asimp at hw
                        simp at hw
                        refine ⟨N₀, e, v, rfl, hw.symm, hctx, ?_⟩
                        rw [hv] at eo
                        exact eo

/-- Pull a receive redex on binder `0` back through congruence and a channel renaming. -/
private lemma pull_recv {ξ : Nat → Nat} {m₀ : Term} {N : EvalCtx} {rv : Rlv}
    (h : TLLC.Process.CongrTerm .ex (m₀⟨ξ; (id : Nat → Nat)⟩)
      (N.eval (.recv (cvar 0) rv))) :
    ∃ (N₀ : EvalCtx) (e : Nat),
      m₀ = N₀.eval (.recv (cvar e) rv) ∧ ξ e = 0 ∧
      CongrCtx (EvalCtx.cren ξ N₀) N := by
  obtain ⟨N₁, r₁, heq, hctx, hr⟩ := congrTerm_eval_inv N h
  cases hr with
  | recv ec =>
      cases ec with
      | chan_ex =>
          obtain ⟨N₀, r₀, rfl, rfl, hre⟩ := eval_cren_reflect N₁ heq
          cases r₀ <;> asimp at hre <;> try simp at hre
          next w rv₁ =>
            obtain ⟨hw, hrv₁⟩ := hre
            subst hrv₁
            cases w <;> asimp at hw <;> try simp at hw
            next ch =>
              cases ch with
              | var_Chan e =>
                  asimp at hw
                  simp at hw
                  exact ⟨N₀, e, rfl, hw.symm, hctx⟩

/-- Pull a close redex on binder `0` back through congruence and a channel renaming. -/
private lemma pull_close {ξ : Nat → Nat} {m₀ : Term} {N : EvalCtx} {b : Bool}
    (h : TLLC.Process.CongrTerm .ex (m₀⟨ξ; (id : Nat → Nat)⟩)
      (N.eval (.close b (cvar 0)))) :
    ∃ (N₀ : EvalCtx) (e : Nat),
      m₀ = N₀.eval (.close b (cvar e)) ∧ ξ e = 0 ∧
      CongrCtx (EvalCtx.cren ξ N₀) N := by
  obtain ⟨N₁, r₁, heq, hctx, hr⟩ := congrTerm_eval_inv N h
  cases hr with
  | close ec =>
      cases ec with
      | chan_ex =>
          obtain ⟨N₀, r₀, rfl, rfl, hre⟩ := eval_cren_reflect N₁ heq
          cases r₀ <;> asimp at hre <;> try simp at hre
          next b₀ w =>
            obtain ⟨hb, hw⟩ := hre
            subst hb
            cases w <;> asimp at hw <;> try simp at hw
            next ch =>
              cases ch with
              | var_Chan e =>
                  asimp at hw
                  simp at hw
                  exact ⟨N₀, e, rfl, hw.symm, hctx⟩

/-- Plugging a non-garbage redex never produces garbage. -/
private lemma isGarbage_eval {N : EvalCtx} {r : Term}
    (h : TLLC.Process.isGarbage r = false) :
    TLLC.Process.isGarbage (N.eval r) = false := by
  cases N with
  | hole => exact h
  | bnd M n => rfl

/-! ## List surgery for the machine-step reconstruction -/

private lemma getElem?_set_ne {α : Type _} : ∀ (l : List α) (i j : Nat), i ≠ j → ∀ (a : α),
    getElem? (l.set i a) j = getElem? l j := by
  intro l
  induction l with
  | nil => intro i j _ a; rfl
  | cons x t ih =>
      intro i j hij a
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl hij
          | succ j => rfl
      | succ i =>
          cases j with
          | zero => rfl
          | succ j =>
              show getElem? (x :: t.set i a) (j + 1) = getElem? (x :: t) (j + 1)
              simp only [List.getElem?_cons_succ]
              exact ih i j (by omega) a

private lemma live_append (l r : List Term) :
    TLLC.Process.live (l ++ r) = TLLC.Process.live l ++ TLLC.Process.live r := by
  unfold TLLC.Process.live
  exact List.filter_append _ _

private lemma live_single_live {x : Term} (h : TLLC.Process.isGarbage x = false) :
    TLLC.Process.live [x] = [x] := by
  rw [TLLC.Process.live_cons_live h]
  rfl

private lemma live_single_garbage {x : Term} (h : TLLC.Process.isGarbage x = true) :
    TLLC.Process.live [x] = [] := by
  rw [TLLC.Process.live_cons_garbage h]
  rfl

private lemma live_cons_blocks (x : Term) (xs : List Term) :
    TLLC.Process.live (x :: xs) = TLLC.Process.live [x] ++ TLLC.Process.live xs := by
  cases h : TLLC.Process.isGarbage x with
  | false => rw [TLLC.Process.live_cons_live h, live_single_live h]; rfl
  | true => rw [TLLC.Process.live_cons_garbage h, live_single_garbage h]; rfl

/-- Replacing the thread at a located live position updates the live soup pointwise. -/
private lemma live_one_set {ts : List Term} {i : Nat} {a : Term} {l' : List Term} (a' : Term)
    (hi : getElem? ts i = some a) (hga : TLLC.Process.isGarbage a = false)
    (hperm : (TLLC.Process.live ts).Perm (a :: l')) :
    (TLLC.Process.live (ts.set i a')).Perm (TLLC.Process.live [a'] ++ l') := by
  obtain ⟨hsplit, hset⟩ := list_split_set (n := a') hi
  have h1 : TLLC.Process.live ts =
      TLLC.Process.live (ts.take i) ++ a :: TLLC.Process.live (ts.drop (i + 1)) := by
    conv_lhs => rw [hsplit]
    rw [live_append, TLLC.Process.live_cons_live hga]
  have hrest : (TLLC.Process.live (ts.take i) ++
      TLLC.Process.live (ts.drop (i + 1))).Perm l' := by
    refine List.Perm.cons_inv (a := a) ?_
    refine List.Perm.trans List.perm_middle.symm ?_
    rw [← h1]
    exact hperm
  have h2 : TLLC.Process.live (ts.set i a') =
      (TLLC.Process.live (ts.take i) ++ TLLC.Process.live [a']) ++
        TLLC.Process.live (ts.drop (i + 1)) := by
    rw [hset, show ts.take i ++ a' :: ts.drop (i + 1) =
      ts.take i ++ ([a'] ++ ts.drop (i + 1)) from rfl, live_append, live_append,
      List.append_assoc]
  rw [h2]
  refine List.Perm.trans (List.Perm.append_right _ List.perm_append_comm) ?_
  rw [List.append_assoc]
  exact List.Perm.append_left _ hrest

/-- Extract two distinct positions realizing the first two threads of a live permutation. -/
private lemma perm_two_pos {ts : List Term} {a b : Term} {l'' : List Term}
    (hperm : (TLLC.Process.live ts).Perm (a :: b :: l'')) :
    ∃ (i j : Nat), i ≠ j ∧ getElem? ts i = some a ∧ getElem? ts j = some b := by
  have hmema : a ∈ TLLC.Process.live ts := hperm.symm.subset (by simp)
  have hga : TLLC.Process.isGarbage a = false := by
    have := List.of_mem_filter hmema
    simpa using this
  obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.mem_of_mem_filter hmema)
  obtain ⟨hsplit, _⟩ := list_split_set (n := a) hi
  have h1 : TLLC.Process.live ts =
      TLLC.Process.live (ts.take i) ++ a :: TLLC.Process.live (ts.drop (i + 1)) := by
    conv_lhs => rw [hsplit]
    rw [live_append, TLLC.Process.live_cons_live hga]
  have h2 : (TLLC.Process.live (ts.take i) ++
      TLLC.Process.live (ts.drop (i + 1))).Perm (b :: l'') := by
    refine List.Perm.cons_inv (a := a) ?_
    refine List.Perm.trans List.perm_middle.symm ?_
    rw [← h1]
    exact hperm
  have hmemb : b ∈ TLLC.Process.live (ts.take i) ++ TLLC.Process.live (ts.drop (i + 1)) :=
    h2.symm.subset (by simp)
  rcases List.mem_append.mp hmemb with hb | hb
  · obtain ⟨p, hp⟩ := List.getElem?_of_mem (List.mem_of_mem_filter hb)
    have hplen : p < (ts.take i).length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hp
      cases hp
    have hplt : p < i := by
      rw [List.length_take] at hplen
      omega
    refine ⟨i, p, by omega, hi, ?_⟩
    rw [← List.getElem?_take_of_lt hplt]
    exact hp
  · obtain ⟨q, hq⟩ := List.getElem?_of_mem (List.mem_of_mem_filter hb)
    refine ⟨i, i + 1 + q, by omega, hi, ?_⟩
    rw [← List.getElem?_drop]
    exact hq

/-- Replacing two located live threads updates the live soup pointwise. -/
private lemma live_two_set {ts : List Term} {i j : Nat} {a b : Term} {l'' : List Term}
    (a' b' : Term) (hij : i ≠ j)
    (hi : getElem? ts i = some a) (hj : getElem? ts j = some b)
    (hga : TLLC.Process.isGarbage a = false) (hgb : TLLC.Process.isGarbage b = false)
    (hperm : (TLLC.Process.live ts).Perm (a :: b :: l'')) :
    (TLLC.Process.live ((ts.set i a').set j b')).Perm
      (TLLC.Process.live [a'] ++ TLLC.Process.live [b'] ++ l'') := by
  have h1 := live_one_set a' hi hga hperm
  have hj' : getElem? (ts.set i a') j = some b := by
    rw [getElem?_set_ne ts i j hij a']
    exact hj
  have h1' : (TLLC.Process.live (ts.set i a')).Perm
      (b :: (TLLC.Process.live [a'] ++ l'')) := h1.trans List.perm_middle
  have h2 := live_one_set b' hj' hgb h1'
  refine h2.trans ?_
  rw [← List.append_assoc]
  exact List.Perm.append_right _ List.perm_append_comm

private lemma forall₂_map_map_mem {R S : Term → Term → Prop} {f g : Term → Term} :
    ∀ {l l' : List Term}, List.Forall₂ R l l' →
      (∀ a b, b ∈ l' → R a b → S (f a) (g b)) →
      List.Forall₂ S (l.map f) (l'.map g) := by
  intro l l' h
  induction h with
  | nil => intro _; exact .nil
  | @cons a b l l' hab _ ih =>
      intro himp
      exact .cons (himp a b (by simp) hab)
        (ih (fun a b hb hr => himp a b (by simp [hb]) hr))

private lemma forall₂_live_single {R : Term → Term → Prop} {x y : Term}
    (hg : TLLC.Process.isGarbage x = TLLC.Process.isGarbage y) (hrel : R x y) :
    List.Forall₂ R (TLLC.Process.live [x]) (TLLC.Process.live [y]) := by
  cases hx : TLLC.Process.isGarbage x with
  | true =>
      rw [live_single_garbage hx, live_single_garbage (hg.symm.trans hx)]
      exact .nil
  | false =>
      rw [live_single_live hx, live_single_live (hg.symm.trans hx)]
      exact .cons hrel .nil

/-! ## Nat-list sum bounds for the linearity accounting -/

private lemma sum_ge_getElem : ∀ {l : List Nat} {i n : Nat},
    getElem? l i = some n → n ≤ l.sum := by
  intro l
  induction l with
  | nil => intro i n h; cases h
  | cons x t ih =>
      intro i n h
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at h
          obtain rfl := Option.some.inj h
          simp [List.sum_cons]
      | succ i =>
          rw [List.getElem?_cons_succ] at h
          have := ih h
          simp only [List.sum_cons]
          omega

private lemma sum_pair : ∀ {l : List Nat} {i j a b : Nat}, i ≠ j →
    getElem? l i = some a → getElem? l j = some b → a + b ≤ l.sum := by
  intro l
  induction l with
  | nil => intro i j a b _ hi _; cases hi
  | cons x t ih =>
      intro i j a b hij hi hj
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hi
          obtain rfl := Option.some.inj hi
          cases j with
          | zero => exact absurd rfl hij
          | succ j =>
              rw [List.getElem?_cons_succ] at hj
              have := sum_ge_getElem hj
              simp only [List.sum_cons]
              omega
      | succ i =>
          rw [List.getElem?_cons_succ] at hi
          cases j with
          | zero =>
              rw [List.getElem?_cons_zero] at hj
              obtain rfl := Option.some.inj hj
              have := sum_ge_getElem hi
              simp only [List.sum_cons]
              omega
          | succ j =>
              rw [List.getElem?_cons_succ] at hj
              have := ih (show i ≠ j by omega) hi hj
              simp only [List.sum_cons]
              omega

private lemma sum_three : ∀ {l : List Nat} {i j p a b n : Nat}, i ≠ j → p ≠ i → p ≠ j →
    getElem? l i = some a → getElem? l j = some b → getElem? l p = some n →
    a + b + n ≤ l.sum := by
  intro l
  induction l with
  | nil => intro i j p a b n _ _ _ hi _ _; cases hi
  | cons x t ih =>
      intro i j p a b n hij hpi hpj hi hj hp
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hi
          obtain rfl := Option.some.inj hi
          cases j with
          | zero => exact absurd rfl hij
          | succ j =>
              rw [List.getElem?_cons_succ] at hj
              cases p with
              | zero => exact absurd rfl hpi
              | succ p =>
                  rw [List.getElem?_cons_succ] at hp
                  have := sum_pair (show j ≠ p by omega) hj hp
                  simp only [List.sum_cons]
                  omega
      | succ i =>
          rw [List.getElem?_cons_succ] at hi
          cases j with
          | zero =>
              rw [List.getElem?_cons_zero] at hj
              obtain rfl := Option.some.inj hj
              cases p with
              | zero => exact absurd rfl hpj
              | succ p =>
                  rw [List.getElem?_cons_succ] at hp
                  have := sum_pair (show i ≠ p by omega) hi hp
                  simp only [List.sum_cons]
                  omega
          | succ j =>
              rw [List.getElem?_cons_succ] at hj
              cases p with
              | zero =>
                  rw [List.getElem?_cons_zero] at hp
                  obtain rfl := Option.some.inj hp
                  have := sum_pair (show i ≠ j by omega) hi hj
                  simp only [List.sum_cons]
                  omega
              | succ p =>
                  rw [List.getElem?_cons_succ] at hp
                  have := ih (show i ≠ j by omega) (show p ≠ i by omega)
                    (show p ≠ j by omega) hi hj hp
                  simp only [List.sum_cons]
                  omega

/-! ## Linearity accounting for the canonical soup -/

private lemma pcount_append : ∀ (Θb Θ : PCtx) (e : Nat),
    TLLC.Process.pcount (Θb ++ Θ) (Θb.length + e) = TLLC.Process.pcount Θ e := by
  intro Θb
  induction Θb with
  | nil => intro Θ e; simp
  | cons s Θb ih =>
      intro Θ e
      rw [show (s :: Θb).length + e = (Θb.length + e) + 1 from by
        simp [List.length_cons]; omega]
      cases s <;> exact ih Θ e

/-- Stripping the binder prefix of a soup form: every binder slot is a two-endpoint slot. -/
private lemma nuN_typed_strip2 : ∀ (k : Nat) {Θ : PCtx} {p : Proc},
    TLLC.Process.Typed Θ (TLLC.Process.nuN k p) →
    ∃ Θb : PCtx, Θb.length = k ∧
      (∀ e, e < k → TLLC.Process.pcount (Θb ++ Θ) e = 2) ∧
      TLLC.Process.Typed (Θb ++ Θ) p := by
  intro k
  induction k with
  | zero =>
      intro Θ p ty
      exact ⟨[], rfl, by omega, ty⟩
  | succ k ih =>
      intro Θ p ty
      rw [TLLC.Process.nuN_succ] at ty
      cases ty with
      | @res _ _ A tyA typ =>
          obtain ⟨Θb, hlen, hcount, typ'⟩ := ih typ
          refine ⟨Θb ++ [Slot.both A], by simp [hlen], ?_, ?_⟩
          · intro e he
            rw [List.append_assoc]
            show TLLC.Process.pcount (Θb ++ (Slot.both A :: Θ)) e = 2
            rcases Nat.lt_or_ge e k with he' | he'
            · exact hcount e he'
            · have hek : e = k := by omega
              subst hek
              have h0 := pcount_append Θb (Slot.both A :: Θ) 0
              rw [Nat.add_zero, hlen] at h0
              exact h0.trans rfl
          · rw [List.append_assoc]
            exact typ'

private lemma procOccurs_parAllL : ∀ (ts : List Term) (acc : Proc) (e : Nat),
    TLLC.Process.procOccurs e (TLLC.Process.parAllL acc ts) =
      TLLC.Process.procOccurs e acc + (ts.map (occurs e)).sum := by
  intro ts
  induction ts with
  | nil => intro acc e; simp [TLLC.Process.parAllL_nil]
  | cons m ts ih =>
      intro acc e
      rw [TLLC.Process.parAllL_cons, ih]
      show TLLC.Process.procOccurs e acc + occurs e m + _ = _
      simp only [List.map_cons, List.sum_cons]
      omega

/-- In a globally-typed soup, a bound channel has exactly two occurrences across the threads. -/
private lemma soup_occurs_two {Θ : PCtx} {k : Nat} {ts : List Term} {e : Nat}
    (hty : TLLC.Process.Typed Θ (TLLC.Process.soupForm (k, ts))) (he : e < k) :
    (ts.map (occurs e)).sum = 2 := by
  have hty' : TLLC.Process.Typed Θ
      (TLLC.Process.nuN k (TLLC.Process.soupThreads ts)) := hty
  obtain ⟨Θb, hlen, hcount, typ⟩ := nuN_typed_strip2 k hty'
  have h1 := typ.occursCount e
  rw [TLLC.Process.soupThreads_eq, procOccurs_parAllL, hcount e he] at h1
  have h2 : TLLC.Process.procOccurs e (Proc.tm (.pure .one)) = 0 := rfl
  omega

private lemma soup_threads_typed {Θ : PCtx} {k : Nat} {ts : List Term}
    (hty : TLLC.Process.Typed Θ (TLLC.Process.soupForm (k, ts))) :
    ∀ m ∈ ts, ∃ Θ', Θ' ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M .unit := by
  have hty' : TLLC.Process.Typed Θ
      (TLLC.Process.nuN k (TLLC.Process.soupThreads ts)) := hty
  obtain ⟨Θ', h2⟩ := nuN_typed_strip k hty'
  rw [TLLC.Process.soupThreads_eq] at h2
  exact (parAllL_typed_inv _ _ h2).2

/-! ## Binder-bijection extension and thread lifting for the fork rule -/

private lemma liftBinders_one_inv {f g : Nat → Nat} (hgf : ∀ x, g (f x) = x) :
    ∀ x, liftBinders 1 g (liftBinders 1 f x) = x := by
  intro x
  cases x with
  | zero =>
      rw [TLLC.Process.liftBinders_lt (k := 1) (x := 0) f (by omega),
        TLLC.Process.liftBinders_lt (k := 1) (x := 0) g (by omega)]
  | succ x =>
      rw [TLLC.Process.liftBinders_ge (k := 1) (x := x + 1) f (by omega),
        show x + 1 - 1 = x from by omega,
        TLLC.Process.liftBinders_ge (k := 1) (x := 1 + f x) g (by omega),
        show 1 + f x - 1 = f x from by omega, hgf x]
      omega

private lemma liftBinders_one_fix {f : Nat → Nat} {k : Nat} (hfix : ∀ x, k ≤ x → f x = x) :
    ∀ x, k + 1 ≤ x → liftBinders 1 f x = x := by
  intro x hx
  rw [TLLC.Process.liftBinders_ge _ (by omega), hfix (x - 1) (by omega)]
  omega

private lemma flatRel_lift {ξ ξp : Nat → Nat} (hs : ∀ x, ξp (x + 1) = ξ x + 1)
    {a b : Term} (h : TLLC.Process.FlatRel ξ a b) :
    TLLC.Process.FlatRel ξp
      (a⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
      (b⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) := by
  show TLLC.Process.CongrTerm .ex
    ((a⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨ξp; (id : Nat → Nat)⟩)
    (b⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
  have e1 : (a⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨ξp; (id : Nat → Nat)⟩ =
      (a⟨ξ; (id : Nat → Nat)⟩)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ := by
    rw [tren_comp, tren_comp]
    exact tren_ext a (fun x => by show ξp (x + 1) = ξ x + 1; exact hs x)
  rw [e1]
  exact TLLC.Process.CongrTerm.crename h _

/-- Renaming the spawned thread of a fork by the extended bijection is renaming its body by the
original bijection: the fresh binder `0` is fixed. -/
private lemma spawn_cren (n : Term) (ξ ξp : Nat → Nat) (h0 : ξp 0 = 0)
    (hs : ∀ x, ξp (x + 1) = ξ x + 1) :
    ((n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
      ((cvar 0 : Term))..])⟨ξp; (id : Nat → Nat)⟩ =
    ((n⟨ξ; (id : Nat → Nat)⟩)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
      ((cvar 0 : Term))..] := by
  asimp
  congr 1
  · funext x
    show Chan.var_Chan (ξp (x + 1)) = Chan.var_Chan (ξ x + 1)
    rw [hs x]
  · funext x
    cases x with
    | zero =>
        show (cvar 0 : Term)⟨ξp; (id : Nat → Nat)⟩ = cvar 0
        asimp
        show Term.chan (Chan.var_Chan (ξp 0)) = Term.chan (Chan.var_Chan 0)
        rw [h0]
    | succ x => rfl

private lemma forall₂_live_single_map {R : Term → Term → Prop} {f : Term → Term} {x y : Term}
    (hgf : TLLC.Process.isGarbage (f x) = TLLC.Process.isGarbage x)
    (hg : TLLC.Process.isGarbage (f x) = TLLC.Process.isGarbage y)
    (hrel : R (f x) y) :
    List.Forall₂ R ((TLLC.Process.live [x]).map f) (TLLC.Process.live [y]) := by
  cases hx : TLLC.Process.isGarbage x with
  | true =>
      rw [live_single_garbage hx, live_single_garbage (hg.symm.trans (hgf.trans hx))]
      exact .nil
  | false =>
      rw [live_single_live hx, live_single_live (hg.symm.trans (hgf.trans hx))]
      exact .cons hrel .nil

/-- Pull a machine step back through the soup equivalence to a positional machine step of the
canonical configuration. The soup must be globally typed: reflecting a term reduction through the
congruence slack of implicit positions is only sound for well-typed threads, and the close rule's
relocation needs the global linearity of the closed channel. -/
lemma prim_pullback {c c₁ c₂ : Config} {Θ : PCtx}
    (hty : TLLC.Process.Typed Θ (TLLC.Process.soupForm c))
    (he : SoupEquiv c c₁) (hp : Prim c₁ c₂) :
    ∃ c₂', TLLC.Process.PrimAt c c₂' ∧ SoupEquiv c₂' c₂ := by
  obtain ⟨hk, ξ, ζ, hζξ, hξζ, hfix, l, hperm, hforall⟩ := TLLC.Process.soupEquiv_flat he
  obtain ⟨k, ts⟩ := c
  have htyThreads := soup_threads_typed hty
  simp only at hk hfix hperm
  cases hp with
  | @exp k₁ m₁ m₁' ts₁ st =>
      subst hk
      -- the fired thread is live: garbage does not reduce
      cases hgar : TLLC.Process.isGarbage m₁ with
      | true =>
          rw [TLLC.Process.isGarbage_eq_true hgar] at st
          exact absurd st pure_one_no_step
      | false =>
      rw [TLLC.Process.live_cons_live hgar] at hforall
      cases hforall with
      | cons h₀ hforall' =>
      rename_i m₀ l'
      -- locate the source thread
      have hmem : m₀ ∈ ts := by
        have h1 : m₀ ∈ TLLC.Process.live ts := hperm.symm.subset (by simp)
        exact List.mem_of_mem_filter h1
      have hlive₀ : TLLC.Process.isGarbage m₀ = false := by
        have h1 : m₀ ∈ TLLC.Process.live ts := hperm.symm.subset (by simp)
        have := List.of_mem_filter h1
        simpa using this
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      -- reflect the step through the congruence and the binder bijection
      obtain ⟨Θ₀, tym₀⟩ := htyThreads m₀ hmem
      obtain ⟨Θ', tyξ⟩ := typed_cren_perm ξ ζ hζξ hξζ k hfix tym₀
      obtain ⟨n₁, st₁, e₁⟩ := TLLC.Process.congrTerm_step_reflect st tyξ h₀
      obtain ⟨n, stn, hn⟩ := TLLC.Dynamic.Step.cren_reflect st₁
      subst hn
      refine ⟨(k, ts.set i n), TLLC.Process.PrimAt.exp hi stn, ?_⟩
      -- reconstruct the soup equivalence for the updated configurations
      refine TLLC.Process.flatEquiv_soupEquiv ⟨rfl, ξ, ζ, hζξ, hξζ, hfix, ?_⟩
      obtain ⟨hsplit, hset⟩ := list_split_set (n := n) hi
      have hfa : TLLC.Process.live (ts.take i ++ m₀ :: ts.drop (i + 1)) =
          TLLC.Process.live (ts.take i) ++
            TLLC.Process.live (m₀ :: ts.drop (i + 1)) := by
        unfold TLLC.Process.live
        exact List.filter_append _ _
      have hliveSplit : TLLC.Process.live ts =
          TLLC.Process.live (ts.take i) ++ m₀ :: TLLC.Process.live (ts.drop (i + 1)) := by
        conv_lhs => rw [hsplit]
        rw [hfa, TLLC.Process.live_cons_live hlive₀]
      have hpermRest : (TLLC.Process.live (ts.take i) ++
          TLLC.Process.live (ts.drop (i + 1))).Perm l' := by
        have h1 : (m₀ :: (TLLC.Process.live (ts.take i) ++
            TLLC.Process.live (ts.drop (i + 1)))).Perm (m₀ :: l') := by
          refine List.Perm.trans ?_ (hliveSplit ▸ hperm)
          exact (List.perm_middle).symm
        exact List.Perm.cons_inv h1
      have hgarN : TLLC.Process.isGarbage n = TLLC.Process.isGarbage m₁' := by
        rw [← TLLC.Process.isGarbage_cren n ξ]
        exact TLLC.Process.congrTerm_isGarbage e₁
      have hliveSet : TLLC.Process.live (ts.set i n) =
          TLLC.Process.live (ts.take i) ++ TLLC.Process.live (n :: ts.drop (i + 1)) := by
        rw [hset]
        unfold TLLC.Process.live
        exact List.filter_append _ _
      cases hgn : TLLC.Process.isGarbage n with
      | false =>
          refine ⟨n :: l', ?_, ?_⟩
          · rw [hliveSet, TLLC.Process.live_cons_live hgn]
            exact List.Perm.trans List.perm_middle (List.Perm.cons _ hpermRest)
          · rw [TLLC.Process.live_cons_live (by rw [← hgarN]; exact hgn)]
            exact List.Forall₂.cons e₁ hforall'
      | true =>
          refine ⟨l', ?_, ?_⟩
          · rw [hliveSet, TLLC.Process.live_cons_garbage hgn]
            exact hpermRest
          · rw [TLLC.Process.live_cons_garbage (by rw [← hgarN]; exact hgn)]
            exact hforall'
  | @fork k₁ N A m ts₁ =>
      subst hk
      -- the forking thread is live
      have hgm : TLLC.Process.isGarbage (N.eval (.fork A m)) = false := isGarbage_eval rfl
      rw [TLLC.Process.live_cons_live hgm] at hforall
      cases hforall with
      | cons h₀ hforall' =>
      rename_i m₀ l'
      -- locate the source thread and reflect the redex shape
      have hmem : m₀ ∈ ts := by
        have h1 : m₀ ∈ TLLC.Process.live ts := hperm.symm.subset (by simp)
        exact List.mem_of_mem_filter h1
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      obtain ⟨N₀, A₀, n₀, rfl, hctx, hbody⟩ := pull_fork h₀
      refine ⟨_, TLLC.Process.PrimAt.fork hi, ?_⟩
      -- reconstruct the soup equivalence with the extended binder bijection
      have h0p : liftBinders 1 ξ 0 = 0 :=
        TLLC.Process.liftBinders_lt (k := 1) (x := 0) ξ (by omega)
      have hsp : ∀ x, liftBinders 1 ξ (x + 1) = ξ x + 1 := by
        intro x
        rw [TLLC.Process.liftBinders_ge (k := 1) (x := x + 1) ξ (by omega),
          show x + 1 - 1 = x from by omega]
        omega
      refine TLLC.Process.flatEquiv_soupEquiv ⟨rfl, liftBinders 1 ξ, liftBinders 1 ζ,
        liftBinders_one_inv hζξ, liftBinders_one_inv hξζ, liftBinders_one_fix hfix, ?_⟩
      -- live bookkeeping for the updated context thread and the fresh spawned thread
      have hts' : getElem? (ts.map (fun n => n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)) i =
          some ((N₀.eval (.fork A₀ n₀))⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) := by
        rw [List.getElem?_map, hi]
        rfl
      have hga' : TLLC.Process.isGarbage
          ((N₀.eval (.fork A₀ n₀))⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) = false := by
        rw [TLLC.Process.isGarbage_cren]
        exact isGarbage_eval rfl
      have hpermMap : (TLLC.Process.live
          (ts.map (fun n => n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩))).Perm
          ((N₀.eval (.fork A₀ n₀))⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ ::
            l'.map (fun n => n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)) := by
        rw [TLLC.Process.live_map_cren]
        exact hperm.map _
      have h1 := live_one_set
        ((EvalCtx.cren ((· + 1) : Nat → Nat) N₀).eval (.pure (cvar 0))) hts' hga' hpermMap
      have hgct : TLLC.Process.isGarbage
          ((EvalCtx.cren ((· + 1) : Nat → Nat) N₀).eval (.pure (cvar 0))) = false :=
        isGarbage_eval rfl
      have hgct₁ : TLLC.Process.isGarbage
          ((EvalCtx.cren ((· + 1) : Nat → Nat) N).eval (.pure (cvar 0))) = false :=
        isGarbage_eval rfl
      -- the spawned threads are congruent through the extended bijection
      have hrelSpawn : TLLC.Process.CongrTerm .ex
          ((((n₀⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
            ((cvar 0 : Term))..])⟨liftBinders 1 ξ; (id : Nat → Nat)⟩))
          ((m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
            ((cvar 0 : Term))..]) := by
        rw [spawn_cren n₀ ξ (liftBinders 1 ξ) h0p hsp]
        exact TLLC.Process.congrTerm_tsubst_of_occursEx
          (TLLC.Process.CongrTerm.crename hbody ((· + 1) : Nat → Nat)) _ _
          (fun x => TLLC.Process.CongrTerm.refl _ _)
          (fun _ x _ => TLLC.Process.CongrTerm.refl _ _)
      have hgSpawn : TLLC.Process.isGarbage
          ((n₀⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
            ((cvar 0 : Term))..]) =
          TLLC.Process.isGarbage
          ((m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
            ((cvar 0 : Term))..]) := by
        rw [← TLLC.Process.isGarbage_cren _ (liftBinders 1 ξ)]
        exact TLLC.Process.congrTerm_isGarbage hrelSpawn
      -- the context threads are congruent through the extended bijection
      have hrelCt : TLLC.Process.FlatRel (liftBinders 1 ξ)
          ((EvalCtx.cren ((· + 1) : Nat → Nat) N₀).eval (.pure (cvar 0)))
          ((EvalCtx.cren ((· + 1) : Nat → Nat) N).eval (.pure (cvar 0))) := by
        show TLLC.Process.CongrTerm .ex
          (((EvalCtx.cren ((· + 1) : Nat → Nat) N₀).eval
            (.pure (cvar 0)))⟨liftBinders 1 ξ; (id : Nat → Nat)⟩) _
        rw [evalctx_cren]
        have hfill : ((Term.pure (cvar 0))⟨liftBinders 1 ξ; (id : Nat → Nat)⟩) =
            .pure (cvar 0) := by
          asimp
          show Term.pure (.chan (Chan.var_Chan (liftBinders 1 ξ 0))) = _
          rw [h0p]
        rw [hfill, evalctx_cren_comp,
          evalctx_cren_ext N₀
            (ζ := funcomp ((· + 1) : Nat → Nat) ξ) (fun x => by
              show liftBinders 1 ξ (x + 1) = ξ x + 1
              exact hsp x),
          ← evalctx_cren_comp]
        exact CongrCtx.eval (CongrCtx.cren hctx ((· + 1) : Nat → Nat))
          (TLLC.Process.CongrTerm.refl _ _)
      refine ⟨(EvalCtx.cren ((· + 1) : Nat → Nat) N₀).eval (.pure (cvar 0)) ::
        (TLLC.Process.live [(n₀⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
          ((cvar 0 : Term))..]] ++
          l'.map (fun n => n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)), ?_, ?_⟩
      · -- permutation of the live successor threads
        rw [live_append]
        refine List.Perm.trans (List.Perm.append_right _ h1) ?_
        rw [live_single_live hgct]
        show ((EvalCtx.cren ((· + 1) : Nat → Nat) N₀).eval (.pure (cvar 0)) ::
          (l'.map (fun n => n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) ++
            TLLC.Process.live [(n₀⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
              ((cvar 0 : Term))..]])).Perm _
        exact List.Perm.cons _ List.perm_append_comm
      · -- pointwise congruence with the successor threads of the machine step
        have hEq : TLLC.Process.live
            ((EvalCtx.cren ((· + 1) : Nat → Nat) N).eval (.pure (cvar 0)) ::
              (m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
                ((cvar 0 : Term))..] ::
              ts₁.map (fun n => n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)) =
            (EvalCtx.cren ((· + 1) : Nat → Nat) N).eval (.pure (cvar 0)) ::
              (TLLC.Process.live [(m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
                ((cvar 0 : Term))..]] ++
                (TLLC.Process.live ts₁).map
                  (fun n => n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)) := by
          rw [TLLC.Process.live_cons_live hgct₁, live_cons_blocks,
            TLLC.Process.live_map_cren]
        rw [hEq]
        refine List.Forall₂.cons hrelCt ?_
        refine TLLC.Process.forall₂_append ?_ ?_
        · exact forall₂_live_single hgSpawn hrelSpawn
        · exact forall₂_map_map_mem hforall' (fun a b _ hr => flatRel_lift hsp hr)
  | @comIm k₁ M N o ts₁ =>
      subst hk
      -- both endpoint threads are live
      have hgM : TLLC.Process.isGarbage
          (M.eval (.app (.send (cvar 0) .im) o .im)) = false := isGarbage_eval rfl
      have hgN : TLLC.Process.isGarbage (N.eval (.recv (cvar 0) .im)) = false :=
        isGarbage_eval rfl
      rw [TLLC.Process.live_cons_live hgM, TLLC.Process.live_cons_live hgN] at hforall
      cases hforall with
      | cons h₀ hf1 =>
      cases hf1 with
      | cons h₁ hforall'' =>
      rename_i a b l''
      -- reflect the two redex shapes; both use the same binder
      obtain ⟨M₀, e, o₀, rfl, hxi0, hctxM, ho⟩ := pull_send h₀
      obtain ⟨N₀, e', rfl, hxi0', hctxN⟩ := pull_recv h₁
      have hee : e' = e := by
        have h1 := hζξ e'
        have h2 := hζξ e
        rw [hxi0'] at h1
        rw [hxi0] at h2
        omega
      subst hee
      have hek : e' < k₁ + 1 := by
        by_contra hge
        have := hfix e' (by omega)
        omega
      obtain ⟨i, j, hij, hi, hj⟩ := perm_two_pos hperm
      refine ⟨_, TLLC.Process.PrimAt.comIm hij hek hi hj, ?_⟩
      refine TLLC.Process.flatEquiv_soupEquiv ⟨rfl, ξ, ζ, hζξ, hξζ, hfix, ?_⟩
      have hgA' : TLLC.Process.isGarbage (M₀.eval (.pure (cvar e'))) = false :=
        isGarbage_eval rfl
      have hgB' : TLLC.Process.isGarbage
          (N₀.eval (.pure (.pair o₀ (cvar e') .im .L))) = false := isGarbage_eval rfl
      refine ⟨M₀.eval (.pure (cvar e')) ::
        N₀.eval (.pure (.pair o₀ (cvar e') .im .L)) :: l'', ?_, ?_⟩
      · have h2 := live_two_set (M₀.eval (.pure (cvar e')))
          (N₀.eval (.pure (.pair o₀ (cvar e') .im .L))) hij hi hj
          (isGarbage_eval rfl) (isGarbage_eval rfl) hperm
        rw [live_single_live hgA', live_single_live hgB'] at h2
        exact h2
      · have hgM₁ : TLLC.Process.isGarbage (M.eval (.pure (cvar 0))) = false :=
          isGarbage_eval rfl
        have hgN₁ : TLLC.Process.isGarbage
            (N.eval (.pure (.pair o (cvar 0) .im .L))) = false := isGarbage_eval rfl
        rw [TLLC.Process.live_cons_live hgM₁, TLLC.Process.live_cons_live hgN₁]
        refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ hforall'')
        · show TLLC.Process.CongrTerm .ex
            ((M₀.eval (.pure (cvar e')))⟨ξ; (id : Nat → Nat)⟩) _
          rw [evalctx_cren]
          have hfill : ((Term.pure (cvar e'))⟨ξ; (id : Nat → Nat)⟩) = .pure (cvar 0) := by
            asimp
            show Term.pure (.chan (Chan.var_Chan (ξ e'))) = _
            rw [hxi0]
          rw [hfill]
          exact CongrCtx.eval hctxM (TLLC.Process.CongrTerm.refl _ _)
        · show TLLC.Process.CongrTerm .ex
            ((N₀.eval (.pure (.pair o₀ (cvar e') .im .L)))⟨ξ; (id : Nat → Nat)⟩) _
          rw [evalctx_cren]
          have hfill : ((Term.pure (.pair o₀ (cvar e') .im .L))⟨ξ; (id : Nat → Nat)⟩) =
              .pure (.pair (o₀⟨ξ; (id : Nat → Nat)⟩) (cvar 0) .im .L) := by
            asimp
            show Term.pure (.pair (o₀⟨ξ; (id : Nat → Nat)⟩)
              (.chan (Chan.var_Chan (ξ e'))) .im .L) = _
            rw [hxi0]
          rw [hfill]
          exact CongrCtx.eval hctxN (TLLC.Process.CongrTerm.pure
            (TLLC.Process.CongrTerm.pair ho TLLC.Process.CongrTerm.chan_ex))
  | @comEx k₁ M N v ts₁ hv =>
      subst hk
      have hgM : TLLC.Process.isGarbage
          (M.eval (.app (.send (cvar 0) .ex) v .ex)) = false := isGarbage_eval rfl
      have hgN : TLLC.Process.isGarbage (N.eval (.recv (cvar 0) .ex)) = false :=
        isGarbage_eval rfl
      rw [TLLC.Process.live_cons_live hgM, TLLC.Process.live_cons_live hgN] at hforall
      cases hforall with
      | cons h₀ hf1 =>
      cases hf1 with
      | cons h₁ hforall'' =>
      rename_i a b l''
      obtain ⟨M₀, e, o₀, rfl, hxi0, hctxM, ho⟩ := pull_send h₀
      obtain ⟨N₀, e', rfl, hxi0', hctxN⟩ := pull_recv h₁
      have hee : e' = e := by
        have h1 := hζξ e'
        have h2 := hζξ e
        rw [hxi0'] at h1
        rw [hxi0] at h2
        omega
      subst hee
      have hek : e' < k₁ + 1 := by
        by_contra hge
        have := hfix e' (by omega)
        omega
      -- the payload is a value: reflect valuehood through congruence and the renaming
      have hval₀ : Val o₀ := TLLC.Dynamic.Val.cren_reflect
        (TLLC.Process.Val.congr_reflect ho hv)
      obtain ⟨i, j, hij, hi, hj⟩ := perm_two_pos hperm
      refine ⟨_, TLLC.Process.PrimAt.comEx hij hek hval₀ hi hj, ?_⟩
      refine TLLC.Process.flatEquiv_soupEquiv ⟨rfl, ξ, ζ, hζξ, hξζ, hfix, ?_⟩
      have hgA' : TLLC.Process.isGarbage (M₀.eval (.pure (cvar e'))) = false :=
        isGarbage_eval rfl
      have hgB' : TLLC.Process.isGarbage
          (N₀.eval (.pure (.pair o₀ (cvar e') .ex .L))) = false := isGarbage_eval rfl
      refine ⟨M₀.eval (.pure (cvar e')) ::
        N₀.eval (.pure (.pair o₀ (cvar e') .ex .L)) :: l'', ?_, ?_⟩
      · have h2 := live_two_set (M₀.eval (.pure (cvar e')))
          (N₀.eval (.pure (.pair o₀ (cvar e') .ex .L))) hij hi hj
          (isGarbage_eval rfl) (isGarbage_eval rfl) hperm
        rw [live_single_live hgA', live_single_live hgB'] at h2
        exact h2
      · have hgM₁ : TLLC.Process.isGarbage (M.eval (.pure (cvar 0))) = false :=
          isGarbage_eval rfl
        have hgN₁ : TLLC.Process.isGarbage
            (N.eval (.pure (.pair v (cvar 0) .ex .L))) = false := isGarbage_eval rfl
        rw [TLLC.Process.live_cons_live hgM₁, TLLC.Process.live_cons_live hgN₁]
        refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ hforall'')
        · show TLLC.Process.CongrTerm .ex
            ((M₀.eval (.pure (cvar e')))⟨ξ; (id : Nat → Nat)⟩) _
          rw [evalctx_cren]
          have hfill : ((Term.pure (cvar e'))⟨ξ; (id : Nat → Nat)⟩) = .pure (cvar 0) := by
            asimp
            show Term.pure (.chan (Chan.var_Chan (ξ e'))) = _
            rw [hxi0]
          rw [hfill]
          exact CongrCtx.eval hctxM (TLLC.Process.CongrTerm.refl _ _)
        · show TLLC.Process.CongrTerm .ex
            ((N₀.eval (.pure (.pair o₀ (cvar e') .ex .L)))⟨ξ; (id : Nat → Nat)⟩) _
          rw [evalctx_cren]
          have hfill : ((Term.pure (.pair o₀ (cvar e') .ex .L))⟨ξ; (id : Nat → Nat)⟩) =
              .pure (.pair (o₀⟨ξ; (id : Nat → Nat)⟩) (cvar 0) .ex .L) := by
            asimp
            show Term.pure (.pair (o₀⟨ξ; (id : Nat → Nat)⟩)
              (.chan (Chan.var_Chan (ξ e'))) .ex .L) = _
            rw [hxi0]
          rw [hfill]
          exact CongrCtx.eval hctxN (TLLC.Process.CongrTerm.pure
            (TLLC.Process.CongrTerm.pair ho TLLC.Process.CongrTerm.chan_ex))
  | @close k₁ M N ts₁ hM hN hocc =>
      subst hk
      -- both closing threads are live
      have hgM : TLLC.Process.isGarbage (M.eval (.close true (cvar 0))) = false :=
        isGarbage_eval rfl
      have hgN : TLLC.Process.isGarbage (N.eval (.close false (cvar 0))) = false :=
        isGarbage_eval rfl
      rw [TLLC.Process.live_cons_live hgM, TLLC.Process.live_cons_live hgN] at hforall
      cases hforall with
      | cons h₀ hf1 =>
      cases hf1 with
      | cons h₁ hforall'' =>
      rename_i a b l''
      -- reflect the two close redexes; both use the same binder
      obtain ⟨M₀, e, rfl, hxi0, hctxM⟩ := pull_close h₀
      obtain ⟨N₀, e', rfl, hxi0', hctxN⟩ := pull_close h₁
      have hee : e' = e := by
        have h1 := hζξ e'
        have h2 := hζξ e
        rw [hxi0'] at h1
        rw [hxi0] at h2
        omega
      subst hee
      have hek : e' < k₁ + 1 := by
        by_contra hge
        have := hfix e' (by omega)
        omega
      have hinj : ∀ x y, ξ x = ξ y → x = y := by
        intro x y hxy
        have h1 := hζξ x
        have h2 := hζξ y
        rw [hxy] at h1
        omega
      have hne0 : ∀ x, x ≠ e' → ξ x ≠ 0 := by
        intro x hx h0
        exact hx (hinj x e' (by rw [h0, hxi0]))
      obtain ⟨i, j, hij, hi, hj⟩ := perm_two_pos hperm
      -- global linearity: the closed binder occurs exactly at the two endpoints
      have hsum : (ts.map (occurs e')).sum = 2 := soup_occurs_two hty hek
      have hredex : ∀ b : Bool, occurs e' (Term.close b (cvar e')) = 1 := by
        intro b
        show occurs e' (Term.chan (Chan.var_Chan e')) = 1
        simp [occurs]
      have hgi : getElem? (ts.map (occurs e')) i =
          some (occurs e' (M₀.eval (.pure .one)) + 1) := by
        rw [List.getElem?_map, hi, Option.map_some, occurs_evalctx, hredex]
      have hgj : getElem? (ts.map (occurs e')) j =
          some (occurs e' (N₀.eval (.pure .one)) + 1) := by
        rw [List.getElem?_map, hj, Option.map_some, occurs_evalctx, hredex]
      have hctxM0 : occurs e' (M₀.eval (.pure .one)) = 0 := by
        have := sum_pair hij hgi hgj
        omega
      have hctxN0 : occurs e' (N₀.eval (.pure .one)) = 0 := by
        have := sum_pair hij hgi hgj
        omega
      have hrest : ∀ x m, getElem? ts x = some m → x ≠ i → x ≠ j → occurs e' m = 0 := by
        intro x m hx hxi hxj
        have hgx : getElem? (ts.map (occurs e')) x = some (occurs e' m) := by
          rw [List.getElem?_map, hx, Option.map_some]
        have := sum_three hij hxi hxj hgi hgj hgx
        omega
      refine ⟨_, TLLC.Process.PrimAt.close hij hek hi hj hctxM0 hctxN0 hrest, ?_⟩
      -- reconstruct with the bijection conjugated by the binder removal
      have hpoint : ∀ x, x ≠ e' →
          ξ (if TLLC.Process.unbind e' x < e' then TLLC.Process.unbind e' x
            else TLLC.Process.unbind e' x + 1) - 1 = ξ x - 1 := by
        intro x hx
        unfold TLLC.Process.unbind
        by_cases h : x < e'
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg (show ¬(x - 1 < e') from by omega),
            show x - 1 + 1 = x from by omega]
      have hrepair : ∀ (n₀ n₁ : Term), occurs e' n₀ = 0 →
          TLLC.Process.CongrTerm .ex (n₀⟨ξ; (id : Nat → Nat)⟩) n₁ →
          TLLC.Process.CongrTerm .ex
            ((n₀⟨TLLC.Process.unbind e'; (id : Nat → Nat)⟩)⟨(fun z =>
              ξ (if z < e' then z else z + 1) - 1); (id : Nat → Nat)⟩)
            (n₁⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩) := by
        intro n₀ n₁ hocc0 hrel
        rw [tren_comp]
        have hstep1 : TLLC.Process.CongrTerm .ex
            (n₀⟨(fun x => ξ (if TLLC.Process.unbind e' x < e' then TLLC.Process.unbind e' x
              else TLLC.Process.unbind e' x + 1) - 1); (id : Nat → Nat)⟩)
            (n₀⟨(fun x => ξ x - 1); (id : Nat → Nat)⟩) :=
          congrTerm_cren_of_occurs (fun x hx =>
            hpoint x (fun hxe => hx (by rw [hxe]; exact hocc0)))
        have hstep2 : TLLC.Process.CongrTerm .ex
            (n₀⟨(fun x => ξ x - 1); (id : Nat → Nat)⟩)
            (n₁⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩) := by
          have h2 := TLLC.Process.CongrTerm.crename hrel ((· - 1) : Nat → Nat)
          rw [tren_comp] at h2
          exact h2
        exact TLLC.Process.CongrTerm.trans hstep1 hstep2
      have hinv1 : ∀ x, (if ζ ((ξ (if x < e' then x else x + 1) - 1) + 1) < e'
          then ζ ((ξ (if x < e' then x else x + 1) - 1) + 1)
          else ζ ((ξ (if x < e' then x else x + 1) - 1) + 1) - 1) = x := by
        intro x
        by_cases hx : x < e'
        · rw [if_pos hx]
          have hr : ξ x ≠ 0 := hne0 x (by omega)
          rw [show ξ x - 1 + 1 = ξ x from by omega, hζξ x, if_pos hx]
        · rw [if_neg hx]
          have hr : ξ (x + 1) ≠ 0 := hne0 (x + 1) (by omega)
          rw [show ξ (x + 1) - 1 + 1 = ξ (x + 1) from by omega, hζξ (x + 1),
            if_neg (show ¬(x + 1 < e') from by omega)]
          omega
      have hζne : ∀ y, ζ (y + 1) ≠ e' := by
        intro y h
        have h1 := hξζ (y + 1)
        rw [h, hxi0] at h1
        omega
      have hinv2 : ∀ y, (ξ (if (if ζ (y + 1) < e' then ζ (y + 1) else ζ (y + 1) - 1) < e'
          then (if ζ (y + 1) < e' then ζ (y + 1) else ζ (y + 1) - 1)
          else (if ζ (y + 1) < e' then ζ (y + 1) else ζ (y + 1) - 1) + 1) - 1) = y := by
        intro y
        by_cases hz : ζ (y + 1) < e'
        · rw [if_pos hz, if_pos hz, hξζ (y + 1)]
          omega
        · have hz' : e' < ζ (y + 1) := by
            have := hζne y
            omega
          rw [if_neg hz, if_neg (show ¬(ζ (y + 1) - 1 < e') from by omega),
            show ζ (y + 1) - 1 + 1 = ζ (y + 1) from by omega, hξζ (y + 1)]
          omega
      have hfix' : ∀ x, k₁ + 1 - 1 ≤ x →
          ξ (if x < e' then x else x + 1) - 1 = x := by
        intro x hx
        rw [if_neg (show ¬(x < e') from by omega), hfix (x + 1) (by omega)]
        omega
      refine TLLC.Process.flatEquiv_soupEquiv ⟨by omega,
        (fun z => ξ (if z < e' then z else z + 1) - 1),
        (fun y => if ζ (y + 1) < e' then ζ (y + 1) else ζ (y + 1) - 1),
        hinv1, hinv2, hfix', ?_⟩
      -- live bookkeeping of the two rewritten endpoints and the unshifted rest
      have h2 := live_two_set (M₀.eval (.pure .one)) (N₀.eval (.pure .one)) hij hi hj
        (isGarbage_eval rfl) (isGarbage_eval rfl) hperm
      -- the pointwise relations for the two endpoint results
      have hM1 : TLLC.Process.CongrTerm .ex ((M₀.eval (.pure .one))⟨ξ; (id : Nat → Nat)⟩)
          (M.eval (.pure .one)) := by
        rw [evalctx_cren, tren_pure_one]
        exact CongrCtx.eval hctxM (TLLC.Process.CongrTerm.refl _ _)
      have hN1 : TLLC.Process.CongrTerm .ex ((N₀.eval (.pure .one))⟨ξ; (id : Nat → Nat)⟩)
          (N.eval (.pure .one)) := by
        rw [evalctx_cren, tren_pure_one]
        exact CongrCtx.eval hctxN (TLLC.Process.CongrTerm.refl _ _)
      have hrelM := hrepair (M₀.eval (.pure .one)) (M.eval (.pure .one)) hctxM0 hM1
      have hrelN := hrepair (N₀.eval (.pure .one)) (N.eval (.pure .one)) hctxN0 hN1
      rw [evalctx_cren ((· - 1) : Nat → Nat) M (.pure .one), tren_pure_one] at hrelM
      rw [evalctx_cren ((· - 1) : Nat → Nat) N (.pure .one), tren_pure_one] at hrelN
      refine ⟨(TLLC.Process.live [M₀.eval (.pure .one)]).map
          (fun n => n⟨TLLC.Process.unbind e'; (id : Nat → Nat)⟩) ++
        (TLLC.Process.live [N₀.eval (.pure .one)]).map
          (fun n => n⟨TLLC.Process.unbind e'; (id : Nat → Nat)⟩) ++
        l''.map (fun n => n⟨TLLC.Process.unbind e'; (id : Nat → Nat)⟩), ?_, ?_⟩
      · rw [TLLC.Process.live_map_cren]
        have h3 := List.Perm.map
          (fun n => n⟨TLLC.Process.unbind e'; (id : Nat → Nat)⟩) h2
        rw [List.map_append, List.map_append] at h3
        exact h3
      · have hEq : TLLC.Process.live
            ((EvalCtx.cren ((· - 1) : Nat → Nat) M).eval (.pure .one) ::
              (EvalCtx.cren ((· - 1) : Nat → Nat) N).eval (.pure .one) ::
              ts₁.map (fun n => n⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩)) =
            TLLC.Process.live [(EvalCtx.cren ((· - 1) : Nat → Nat) M).eval (.pure .one)] ++
              TLLC.Process.live [(EvalCtx.cren ((· - 1) : Nat → Nat) N).eval (.pure .one)] ++
              (TLLC.Process.live ts₁).map
                (fun n => n⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩) := by
          rw [live_cons_blocks ((EvalCtx.cren ((· - 1) : Nat → Nat) M).eval (.pure .one))
              ((EvalCtx.cren ((· - 1) : Nat → Nat) N).eval (.pure .one) ::
                ts₁.map (fun n => n⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩)),
            live_cons_blocks ((EvalCtx.cren ((· - 1) : Nat → Nat) N).eval (.pure .one))
              (ts₁.map (fun n => n⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩)),
            TLLC.Process.live_map_cren, List.append_assoc]
        rw [hEq]
        refine TLLC.Process.forall₂_append (TLLC.Process.forall₂_append ?_ ?_) ?_
        · refine forall₂_live_single_map (TLLC.Process.isGarbage_cren _ _) ?_ hrelM
          rw [← TLLC.Process.isGarbage_cren
            ((M₀.eval (.pure .one))⟨TLLC.Process.unbind e'; (id : Nat → Nat)⟩)
            (fun z => ξ (if z < e' then z else z + 1) - 1)]
          exact TLLC.Process.congrTerm_isGarbage hrelM
        · refine forall₂_live_single_map (TLLC.Process.isGarbage_cren _ _) ?_ hrelN
          rw [← TLLC.Process.isGarbage_cren
            ((N₀.eval (.pure .one))⟨TLLC.Process.unbind e'; (id : Nat → Nat)⟩)
            (fun z => ξ (if z < e' then z else z + 1) - 1)]
          exact TLLC.Process.congrTerm_isGarbage hrelN
        · refine forall₂_map_map_mem hforall'' (fun a b hb hr => ?_)
          refine hrepair a b ?_ hr
          have h1 := occurs_cren_inj hinj e' a
          rw [hxi0] at h1
          have h4 := congrTerm_occurs hr 0 rfl
          have h5 := hocc b (List.mem_of_mem_filter hb)
          omega

/-- **Tree-soup description.** The prenex soup of a valid distinct tree is, up to the soup
equivalence, the canonical tree soup: one binder per edge and one thread per node body, renamed
by a global name→binder map realizing the edges. -/
theorem tree_soup {t : Tree} (typed : Typed t) (distinct : Distinct t) :
    ∃ σ, TreeRen σ t ∧ SoupEquiv (prenex t.flatten) (treeSoup σ t) :=
  tree_soup' typed distinct

private lemma map_set_comm {f : Term → Term} : ∀ (l : List Term) (i : Nat) (a : Term),
    (l.set i a).map f = (l.map f).set i (f a) := by
  intro l
  induction l with
  | nil => intro i a; rfl
  | cons x t ih =>
      intro i a
      cases i with
      | zero => rfl
      | succ i =>
          show f x :: (t.set i a).map f = f x :: (t.map f).set i (f a)
          rw [ih]

/-- Pointwise congruence of a context under two renamings agreeing on its explicit names. -/
private lemma congrCtx_cren_of_occurs : ∀ (M₀ : EvalCtx) {ξ ζ : Nat → Nat},
    (∀ x, occurs x (M₀.eval (.pure .one)) ≠ 0 → ξ x = ζ x) →
    CongrCtx (EvalCtx.cren ξ M₀) (EvalCtx.cren ζ M₀)
  | .hole, ξ, ζ, _ => .hole
  | .bnd M' n, ξ, ζ, h => by
      show CongrCtx (.bnd (EvalCtx.cren ξ M') (n⟨ξ; (id : Nat → Nat)⟩))
        (.bnd (EvalCtx.cren ζ M') (n⟨ζ; (id : Nat → Nat)⟩))
      refine .bnd (congrCtx_cren_of_occurs M' (fun x hx => h x ?_))
        (congrTerm_cren_of_occurs (fun x hx => h x ?_))
      · show occurs x (M'.eval (.pure .one)) + occurs x n ≠ 0
        omega
      · show occurs x (M'.eval (.pure .one)) + occurs x n ≠ 0
        omega

/-- Renaming the endpoint-substituted fork body: the substituted endpoint maps to binder `0`. -/
private lemma spawnd_cren (n : Term) (ξ : Nat → Nat) (d : Nat) (hd : ξ d = 0) :
    (n[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..])⟨ξ; (id : Nat → Nat)⟩ =
      (n⟨ξ; (id : Nat → Nat)⟩)[Chan.var_Chan; ((cvar 0 : Term))..] := by
  asimp
  congr 1
  funext x
  cases x with
  | zero =>
      show (Term.chan (Chan.var_Chan d))⟨ξ; (id : Nat → Nat)⟩ = cvar 0
      asimp
      show Term.chan (Chan.var_Chan (ξ d)) = Term.chan (Chan.var_Chan 0)
      rw [hd]
  | succ x => rfl

private lemma forall₂_set {R : Term → Term → Prop} :
    ∀ {l l' : List Term}, List.Forall₂ R l l' → ∀ (i : Nat) {a b : Term}, R a b →
      List.Forall₂ R (l.set i a) (l'.set i b) := by
  intro l l' h
  induction h with
  | nil => intro i a b _; exact .nil
  | cons hR hrest ih =>
      intro i a b hab
      cases i with
      | zero => exact .cons hab hrest
      | succ i => exact .cons hR (ih i hab)

private lemma forall₂_append' {R : Term → Term → Prop} :
    ∀ {l l' : List Term}, List.Forall₂ R l l' → ∀ {r r' : List Term}, List.Forall₂ R r r' →
      List.Forall₂ R (l ++ r) (l' ++ r') := by
  intro l l' h
  induction h with
  | nil => intro r r' hr; exact hr
  | cons hR _ ih => intro r r' hr; exact .cons hR (ih hr)

/-- Two disjoint position updates, in the multiset view. -/
private lemma coe_set_set {ts : List Term} {p q : Nat} {op oq : Term}
    (hpq : p ≠ q)
    (hp : getElem? ts p = some op) (hq : getElem? ts q = some oq)
    (np nq : Term) :
    (↑((ts.set p np).set q nq) : Multiset Term) + ({op} + {oq}) =
      (↑ts : Multiset Term) + ({np} + {nq}) := by
  have h1 := coe_set_add (α := Term) hp np
  have hq' : getElem? (ts.set p np) q = some oq := by
    rw [getElem?_set_ne _ _ _ hpq _]
    exact hq
  have h2 := coe_set_add (α := Term) hq' nq
  calc (↑((ts.set p np).set q nq) : Multiset Term) + ({op} + {oq})
      = ((↑((ts.set p np).set q nq) : Multiset Term) + {oq}) + {op} := by abel
    _ = ((↑(ts.set p np) : Multiset Term) + {nq}) + {op} := by rw [h2]
    _ = ((↑(ts.set p np) : Multiset Term) + {op}) + {nq} := by abel
    _ = ((↑ts : Multiset Term) + {np}) + {nq} := by rw [h1]
    _ = (↑ts : Multiset Term) + ({np} + {nq}) := by abel

/-- A positional machine step of the canonical tree soup replays as a spawning-tree step. -/
theorem primAt_treeSoup {t : Tree} {c₂ : Config}
    (typed : Typed t) (distinct : Distinct t)
    (hp : TLLC.Process.PrimAt (treeSoup (edgeRen (treeEdges t)) t) c₂) :
    ∃ t', Step t t' ∧ SoupEquiv (prenex t'.flatten) c₂ := by
  cases hp with
  | @exp _ _ i m₁ m₁' hi st =>
      have hi' : ∃ b, getElem? (treeBodies t) i = some b ∧
          m₁ = b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ := by
        rw [List.getElem?_map] at hi
        cases hb : getElem? (treeBodies t) i with
        | none => rw [hb] at hi; cases hi
        | some b => rw [hb] at hi; exact ⟨b, rfl, (Option.some.inj hi).symm⟩
      obtain ⟨b, hib, rfl⟩ := hi'
      obtain ⟨n, stn, rfl⟩ := TLLC.Dynamic.Step.cren_reflect st
      obtain ⟨t', tstep, hbodies, hedges, hchans, _⟩ := bodyStep_tree t i b n hib stn
      have hinv := typed.fidelity distinct tstep
      refine ⟨t', tstep, ?_⟩
      refine ARS.conv_trans (tree_soup_desc hinv.1 hinv.2).1 ?_
      unfold treeSoup
      rw [hedges, hbodies, map_set_comm]
      exact ARS.Conv.refl
  | @fork _ _ i N A m hi =>
      have hct : treeChans t = treeChansTail t := by
        cases typed with
        | root _ _ _ _ => rw [treeChans_eq_tail_root]
      have hdesc := tree_soup_desc typed distinct
      -- pull the forking thread back through the renaming
      have hi' : ∃ b, getElem? (treeBodies t) i = some b ∧
          (N.eval (.fork A m)) = b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ := by
        rw [List.getElem?_map] at hi
        cases hb : getElem? (treeBodies t) i with
        | none => rw [hb] at hi; cases hi
        | some b => rw [hb] at hi; exact ⟨b, rfl, (Option.some.inj hi).symm⟩
      obtain ⟨bi, hib, hbi⟩ := hi'
      obtain ⟨M₀, r₀, hbieq, hMeq, hr₀⟩ := eval_cren_reflect N hbi.symm
      cases r₀ <;> asimp at hr₀ <;> try simp at hr₀
      next A₀ m₀ =>
      obtain ⟨hA₀, hm₀⟩ := hr₀
      -- mint globally fresh endpoints
      obtain ⟨c, d, hc, hd, hcd⟩ : ∃ c d, c ∉ treeChans t ∧ d ∉ treeChans t ∧ c ≠ d := by
        refine ⟨freshIndex (treeChans t),
          freshIndex (freshIndex (treeChans t) :: treeChans t),
          freshIndex_not_mem, ?_, ?_⟩
        · intro h
          exact freshIndex_not_mem (List.mem_cons_of_mem _ h)
        · intro h
          refine freshIndex_not_mem (l := freshIndex (treeChans t) :: treeChans t) ?_
          rw [← h]
          exact List.mem_cons_self ..
      have hib' : getElem? (treeBodies t) i = some (M₀.eval (.fork A₀ m₀)) := by
        rw [← hbieq]
        exact hib
      have hoc : occurs c (M₀.eval (.fork A₀ m₀)) = 0 := by
        by_contra h
        exact hc (hdesc.2.1 _ (List.mem_of_getElem? hib') c h)
      have hod : occurs d (M₀.eval (.fork A₀ m₀)) = 0 := by
        by_contra h
        exact hd (hdesc.2.1 _ (List.mem_of_getElem? hib') d h)
      -- replay the fork on the tree
      obtain ⟨t', tstep, hbodiesM, hedgesM, hchansM, _⟩ :=
        bodyFork_tree t hc hd hcd i M₀ A₀ m₀ hib' hoc hod
      have hinv := typed.fidelity distinct tstep
      refine ⟨t', tstep, ?_⟩
      refine ARS.conv_trans (tree_soup_desc hinv.1 hinv.2).1 ?_
      -- the updated thread list
      have h1 := coe_set_add (α := Term) hib'
        (M₀.eval (.pure (.chan (Chan.var_Chan c))))
      have hupd : (↑(((treeBodies t).set i (M₀.eval (.pure (.chan (Chan.var_Chan c))))) ++
            [m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]]) : Multiset Term) +
            {M₀.eval (.fork A₀ m₀)} =
          (↑(treeBodies t) : Multiset Term) +
            ({M₀.eval (.pure (.chan (Chan.var_Chan c)))} +
              {m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]}) := by
        calc (↑(((treeBodies t).set i (M₀.eval (.pure (.chan (Chan.var_Chan c))))) ++
              [m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]]) : Multiset Term) +
              {M₀.eval (.fork A₀ m₀)}
            = ((↑((treeBodies t).set i (M₀.eval (.pure (.chan (Chan.var_Chan c))))) :
                Multiset Term) + {M₀.eval (.fork A₀ m₀)}) +
                {m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]} := by
              rw [← Multiset.coe_add]
              simp only [← Multiset.singleton_add, ← Multiset.cons_coe, Multiset.coe_nil]
              abel
          _ = ((↑(treeBodies t) : Multiset Term) +
                {M₀.eval (.pure (.chan (Chan.var_Chan c)))}) +
                {m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]} := by
              rw [h1]
          _ = (↑(treeBodies t) : Multiset Term) +
                ({M₀.eval (.pure (.chan (Chan.var_Chan c)))} +
                  {m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]}) := by
              abel
      have hcoe : treeBodiesM t' =
          ↑(((treeBodies t).set i (M₀.eval (.pure (.chan (Chan.var_Chan c))))) ++
            [m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]]) :=
        add_right_cancel (hbodiesM.trans hupd.symm)
      have hperm : (treeBodies t').Perm
          (((treeBodies t).set i (M₀.eval (.pure (.chan (Chan.var_Chan c))))) ++
            [m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]]) :=
        Multiset.coe_eq_coe.mp hcoe
      unfold treeSoup
      refine ARS.conv_trans (TLLC.Process.SoupEquiv.perm
        (hperm.map (fun b => b⟨edgeRen (treeEdges t'); (id : Nat → Nat)⟩))) ?_
      -- reindex to the front-minted edge list
      have hM : (↑((treeEdges t').map sortPair) : Multiset (Nat × Nat)) =
          ↑(((c, d) :: treeEdges t).map sortPair) := by
        show treeEdgesM t' = _
        rw [hedgesM, List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add]
        show (↑((treeEdges t).map sortPair) : Multiset (Nat × Nat)) + {sortPair (c, d)} =
          {sortPair (c, d)} + ↑((treeEdges t).map sortPair)
        abel
      have hsubE : ∀ x ∈ edgeNames (treeEdges t), x ∈ treeChans t := by
        intro x hx
        have h := hdesc.2.2.1.subset hx
        rwa [← hct] at h
      have hnd₁ : (edgeNames ((c, d) :: treeEdges t)).Nodup := by
        rw [edgeNames_cons]
        refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr
          ⟨?_, edgeNames_nodup typed distinct⟩⟩
        · intro h
          rcases List.mem_cons.mp h with h | h
          · exact hcd h
          · exact hc (hsubE c h)
        · intro h
          exact hd (hsubE d h)
      have hchain := treeSoup_reindexM (es := treeEdges t') (es' := (c, d) :: treeEdges t)
        hM (edgeNames_nodup hinv.1 hinv.2) hnd₁
        (((treeBodies t).set i (M₀.eval (.pure (.chan (Chan.var_Chan c))))) ++
          [m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..]])
      refine ARS.conv_trans hchain ?_
      rw [List.length_cons]
      -- pointwise congruence with the machine result
      have hσ₁c : edgeRen ((c, d) :: treeEdges t) c = 0 := edgeRen_cons_hit (.inl rfl) _
      have hσ₁d : edgeRen ((c, d) :: treeEdges t) d = 0 := edgeRen_cons_hit (.inr rfl) _
      have hσ₁miss : ∀ x, x ≠ c → x ≠ d → edgeRen ((c, d) :: treeEdges t) x =
          edgeRen (treeEdges t) x + 1 := fun x hxc hxd =>
        edgeRen_cons_miss (Ne.symm hxc) (Ne.symm hxd) _
      have hbase : List.Forall₂ (TLLC.Process.CongrTerm .ex)
          ((treeBodies t).map
            (fun b => b⟨edgeRen ((c, d) :: treeEdges t); (id : Nat → Nat)⟩))
          ((treeBodies t).map
            (fun b => b⟨fun x => edgeRen (treeEdges t) x + 1; (id : Nat → Nat)⟩)) := by
        refine forall₂_congr_cren (treeBodies t) (fun b hb x hx => ?_)
        have hxT : x ∈ treeChans t := hdesc.2.1 b hb x hx
        exact hσ₁miss x (fun h => hc (h ▸ hxT)) (fun h => hd (h ▸ hxT))
      have hslot : TLLC.Process.CongrTerm .ex
          ((M₀.eval (.pure (.chan (Chan.var_Chan c))))⟨edgeRen ((c, d) :: treeEdges t);
            (id : Nat → Nat)⟩)
          ((N.cren ((· + 1) : Nat → Nat)).eval (.pure (cvar 0))) := by
        rw [evalctx_cren, hMeq, evalctx_cren_comp]
        have hpay : (Term.pure (.chan (Chan.var_Chan c)))⟨edgeRen ((c, d) :: treeEdges t);
            (id : Nat → Nat)⟩ = Term.pure (cvar 0) := by
          asimp
          show Term.pure (.chan (Chan.var_Chan (edgeRen ((c, d) :: treeEdges t) c))) = _
          rw [hσ₁c]
        rw [hpay]
        refine CongrCtx.eval ?_ (TLLC.Process.CongrTerm.refl _ _)
        refine congrCtx_cren_of_occurs M₀ (fun x hx => ?_)
        have hxbi : occurs x (M₀.eval (.fork A₀ m₀)) ≠ 0 := by
          rw [occurs_evalctx]
          omega
        have hxT : x ∈ treeChans t := hdesc.2.1 _ (List.mem_of_getElem? hib') x hxbi
        rw [hσ₁miss x (fun h => hc (h ▸ hxT)) (fun h => hd (h ▸ hxT))]
      have hspawn : TLLC.Process.CongrTerm .ex
          ((m₀[Chan.var_Chan; ((Term.chan (Chan.var_Chan d)))..])⟨
            edgeRen ((c, d) :: treeEdges t); (id : Nat → Nat)⟩)
          ((m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan;
            ((cvar 0 : Term))..]) := by
        rw [spawnd_cren m₀ _ d hσ₁d, hm₀, TLLC.Process.tren_comp]
        refine TLLC.Process.congrTerm_tsubst_of_occursEx ?_ _ _
          (fun x => TLLC.Process.CongrTerm.refl _ _)
          (fun _ x _ => TLLC.Process.CongrTerm.refl _ _)
        refine congrTerm_cren_of_occurs (fun x hx => ?_)
        have hxbi : occurs x (M₀.eval (.fork A₀ m₀)) ≠ 0 := by
          rw [occurs_evalctx]
          have hfx : occurs x (Term.fork A₀ m₀) = occurs x m₀ := rfl
          omega
        have hxT : x ∈ treeChans t := hdesc.2.1 _ (List.mem_of_getElem? hib') x hxbi
        exact hσ₁miss x (fun h => hc (h ▸ hxT)) (fun h => hd (h ▸ hxT))
      rw [List.map_append, map_set_comm, TLLC.Process.tsmap_comp]
      refine ARS.conv1 (TLLC.Process.SoupG.congr
        (forall₂_append' (forall₂_set hbase i hslot) (.cons hspawn .nil)))
  | @comIm _ _ i j e M N o hij hek hi hj =>
      -- expose the root shape and the edge
      have hct : treeChans t = treeChansTail t := by
        cases typed with
        | root _ _ _ _ => rw [treeChans_eq_tail_root]
      have hlt : e < (treeEdges t).length := hek
      obtain ⟨⟨c, d⟩, hedge⟩ : ∃ ed, getElem? (treeEdges t) e = some ed :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      -- name→edge dispatch
      have hnameEdge : ∀ (a : Nat), a ∈ treeChans t →
          edgeRen (treeEdges t) a = e → a = c ∨ a = d := by
        intro a hmem hae
        have hD := (tree_soup_desc typed distinct).2.2.2 a (hct ▸ hmem)
        obtain ⟨p, ed, hp, hed⟩ := mem_edgeNames_getElem hD
        have hplt : p < (treeEdges t).length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hp
          cases hp
        have hed_eq : ed = (treeEdges t).get ⟨p, hplt⟩ := by
          rw [List.getElem?_eq_getElem hplt] at hp
          exact (Option.some.inj hp).symm
        have hreal := (treeRen_edgeRen typed distinct).realizes p hplt
        have hpe : p = e := by
          rcases hed with h | h
          · rw [← hae, ← h, hed_eq]
            exact hreal.1.symm
          · rw [← hae, ← h, hed_eq]
            exact hreal.2.symm
        subst hpe
        have hcd : ed = (c, d) := by
          rw [List.getElem?_eq_getElem hplt] at hp
          rw [List.getElem?_eq_getElem hplt] at hedge
          exact (Option.some.inj hp).symm.trans (Option.some.inj hedge)
        rw [hcd] at hed
        rcases hed with h | h
        · exact .inl h.symm
        · exact .inr h.symm
      -- pull the two threads back through the renaming
      have hi' : ∃ b, getElem? (treeBodies t) i = some b ∧
          (M.eval (.app (.send (cvar e) .im) o .im)) =
            b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ := by
        rw [List.getElem?_map] at hi
        cases hb : getElem? (treeBodies t) i with
        | none => rw [hb] at hi; cases hi
        | some b => rw [hb] at hi; exact ⟨b, rfl, (Option.some.inj hi).symm⟩
      obtain ⟨bi, hib, hbi⟩ := hi'
      obtain ⟨M₀, r₀, hbieq, hMeq, hr₀⟩ := eval_cren_reflect M hbi.symm
      cases r₀ <;> asimp at hr₀ <;> try simp at hr₀
      next u v rv =>
      obtain ⟨hu, hv, hrv⟩ := hr₀
      cases u <;> asimp at hu <;> try simp at hu
      next w rv₁ =>
      obtain ⟨hw, hrv₁⟩ := hu
      cases w <;> asimp at hw <;> try simp at hw
      next ch =>
      cases ch with
      | var_Chan a =>
      asimp at hw
      simp at hw
      subst hrv
      subst hrv₁
      -- the redex holds the name explicitly
      have hocca : occurs a bi ≠ 0 := by
        rw [hbieq, occurs_evalctx]
        have h1 : occurs a (Term.app (.send (.chan (Chan.var_Chan a)) .im) v .im) = 1 := by
          show occurs a (Term.chan (Chan.var_Chan a)) = 1
          simp [occurs]
        omega
      have hmema : a ∈ treeChans t :=
        (tree_soup_desc typed distinct).2.1 bi (List.mem_of_getElem? hib) a hocca
      -- pull the receiving thread back
      have hj' : ∃ b, getElem? (treeBodies t) j = some b ∧
          (N.eval (.recv (cvar e) .im)) = b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ := by
        rw [List.getElem?_map] at hj
        cases hb : getElem? (treeBodies t) j with
        | none => rw [hb] at hj; cases hj
        | some b => rw [hb] at hj; exact ⟨b, rfl, (Option.some.inj hj).symm⟩
      obtain ⟨bj, hjb, hbj⟩ := hj'
      obtain ⟨N₀, r₀', hbjeq, hNeq, hr₀'⟩ := eval_cren_reflect N hbj.symm
      cases r₀' <;> asimp at hr₀' <;> try simp at hr₀'
      next w' rv' =>
      obtain ⟨hw', hrv'⟩ := hr₀'
      subst hrv'
      cases w' <;> asimp at hw' <;> try simp at hw'
      next ch' =>
      cases ch' with
      | var_Chan a' =>
      asimp at hw'
      simp at hw'
      have hocca' : occurs a' bj ≠ 0 := by
        rw [hbjeq, occurs_evalctx]
        have h1 : occurs a' (Term.recv (.chan (Chan.var_Chan a')) .im) = 1 := by
          show occurs a' (Term.chan (Chan.var_Chan a')) = 1
          simp [occurs]
        omega
      have hmema' : a' ∈ treeChans t :=
        (tree_soup_desc typed distinct).2.1 bj (List.mem_of_getElem? hjb) a' hocca'
      -- the canonical renaming of the edge names
      have hget_e : (treeEdges t).get ⟨e, hlt⟩ = (c, d) := by
        rw [List.getElem?_eq_getElem hlt] at hedge
        exact Option.some.inj hedge
      have hreal_e := (treeRen_edgeRen typed distinct).realizes e hlt
      have hσc : edgeRen (treeEdges t) c = e := by
        have h1 := hreal_e.1
        rw [hget_e] at h1
        exact h1
      have hσd : edgeRen (treeEdges t) d = e := by
        have h1 := hreal_e.2
        rw [hget_e] at h1
        exact h1
      -- navigate to the edge and pin the fired positions by linearity
      obtain ⟨pi, pj, hpij, ⟨bpi, hpib, hpic, hpid0⟩, ⟨bpj, hpjb, hpjd, hpjc0⟩,
        contS, contR, _, _, _⟩ := edge_replay typed distinct hedge
      have htysoup : TLLC.Process.Typed []
          (TLLC.Process.soupForm (treeSoup (edgeRen (treeEdges t)) t)) :=
        TLLC.Process.Typed.congr
          (TLLC.Process.Typed.congr typed.flatten_typed
            (TLLC.Process.prenex_sound t.flatten))
          (TLLC.Process.soupEquiv_congr (tree_soup_desc typed distinct).1)
      have hsum : (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)).sum = 2 :=
        soup_occurs_two htysoup hek
      have hcnt_i : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) i =
          some (occurs e (M.eval (.app (.send (cvar e) .im) o .im))) := by
        rw [List.getElem?_map, hi]
        rfl
      have hge_i : 1 ≤ occurs e (M.eval (.app (.send (cvar e) .im) o .im)) := by
        rw [occurs_evalctx]
        have h1 : occurs e (Term.app (.send (cvar e) .im) o .im) = 1 := by
          show occurs e (Term.chan (Chan.var_Chan e)) = 1
          simp [occurs]
        omega
      have hcnt_j : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) j =
          some (occurs e (N.eval (.recv (cvar e) .im))) := by
        rw [List.getElem?_map, hj]
        rfl
      have hge_j : 1 ≤ occurs e (N.eval (.recv (cvar e) .im)) := by
        rw [occurs_evalctx]
        have h1 : occurs e (Term.recv (cvar e) .im) = 1 := by
          show occurs e (Term.chan (Chan.var_Chan e)) = 1
          simp [occurs]
        omega
      have hcnt_pi : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) pi =
          some (occurs e (bpi⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)) := by
        rw [List.getElem?_map, List.getElem?_map, hpib]
        rfl
      have hge_pi : 1 ≤ occurs e (bpi⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) := by
        have h1 := occurs_cren_ge (f := edgeRen (treeEdges t)) c bpi
        rw [hσc] at h1
        omega
      have hcnt_pj : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) pj =
          some (occurs e (bpj⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)) := by
        rw [List.getElem?_map, List.getElem?_map, hpjb]
        rfl
      have hge_pj : 1 ≤ occurs e (bpj⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) := by
        have h1 := occurs_cren_ge (f := edgeRen (treeEdges t)) d bpj
        rw [hσd] at h1
        omega
      have hpi_in : pi = i ∨ pi = j := by
        by_contra hcon
        push Not at hcon
        have := sum_three hij hcon.1 hcon.2 hcnt_i hcnt_j hcnt_pi
        omega
      have hpj_in : pj = i ∨ pj = j := by
        by_contra hcon
        push Not at hcon
        have := sum_three hij hcon.1 hcon.2 hcnt_i hcnt_j hcnt_pj
        omega
      rcases hnameEdge a hmema hw.symm with rfl | rfl
      · -- the sender holds the label: the parent sends
        have hipj : i ≠ pj := by
          intro h
          rw [h, hpjb] at hib
          exact ((Option.some.inj hib).symm ▸ hocca) hpjc0
        have hpin_i : pi = i := by
          rcases hpi_in with h | h
          · exact h
          · rcases hpj_in with h' | h'
            · exact absurd h'.symm hipj
            · exact absurd (h.trans h'.symm) hpij
        have hpin_j : j = pj := by
          rcases hpj_in with h' | h'
          · exact absurd h'.symm hipj
          · exact h'.symm
        rcases hnameEdge a' hmema' hw'.symm with rfl | rfl
        · exfalso
          rw [hpin_j, hpjb] at hjb
          exact ((Option.some.inj hjb).symm ▸ hocca') hpjc0
        · subst hpin_i
          subst hpin_j
          obtain ⟨t', tstep, hbodies, hedges, hchans⟩ := contS M₀ N₀ v
            (by rw [← hbieq]; exact hib) (by rw [← hbjeq]; exact hjb)
          have hinv := typed.fidelity distinct tstep
          refine ⟨t', tstep, ?_⟩
          refine ARS.conv_trans (tree_soup_desc hinv.1 hinv.2).1 ?_
          unfold treeSoup
          rw [hedges, hbodies, map_set_comm, map_set_comm]
          have hv1 : (M₀.eval (.pure (.chan (Chan.var_Chan a))))⟨edgeRen (treeEdges t);
              (id : Nat → Nat)⟩ = M.eval (.pure (cvar e)) := by
            rw [evalctx_cren, hMeq]
            congr 1
            asimp
            show Term.pure (.chan (Chan.var_Chan (edgeRen (treeEdges t) a))) = _
            rw [hσc]
          have hv2 : (N₀.eval (.pure (.pair v (.chan (Chan.var_Chan a')) .im .L)))⟨
              edgeRen (treeEdges t); (id : Nat → Nat)⟩ =
              N.eval (.pure (.pair o (cvar e) .im .L)) := by
            rw [evalctx_cren, hNeq]
            congr 1
            asimp
            show Term.pure (.pair (v⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)
              (.chan (Chan.var_Chan (edgeRen (treeEdges t) a'))) .im .L) = _
            rw [hσd, ← hv]
          rw [hv1, hv2]
          exact ARS.Conv.refl
      · -- the sender holds the child-side name: the parent receives
        have hipi : i ≠ pi := by
          intro h
          rw [h, hpib] at hib
          exact ((Option.some.inj hib).symm ▸ hocca) hpid0
        have hpin_i : pi = j := by
          rcases hpi_in with h | h
          · exact absurd h.symm hipi
          · exact h
        have hpin_j : pj = i := by
          rcases hpj_in with h | h
          · exact h
          · exact absurd (hpin_i.trans h.symm) hpij
        rcases hnameEdge a' hmema' hw'.symm with rfl | rfl
        · subst hpin_i
          subst hpin_j
          obtain ⟨t', tstep, hbodies, hedges, hchans⟩ := contR N₀ M₀ v
            (by rw [← hbieq]; exact hib) (by rw [← hbjeq]; exact hjb)
          have hinv := typed.fidelity distinct tstep
          refine ⟨t', tstep, ?_⟩
          refine ARS.conv_trans (tree_soup_desc hinv.1 hinv.2).1 ?_
          unfold treeSoup
          rw [hedges, hbodies, map_set_comm, map_set_comm,
            List.set_comm _ _ (Ne.symm hpij)]
          have hv1 : (M₀.eval (.pure (.chan (Chan.var_Chan a))))⟨edgeRen (treeEdges t);
              (id : Nat → Nat)⟩ = M.eval (.pure (cvar e)) := by
            rw [evalctx_cren, hMeq]
            congr 1
            asimp
            show Term.pure (.chan (Chan.var_Chan (edgeRen (treeEdges t) a))) = _
            rw [hσd]
          have hv2 : (N₀.eval (.pure (.pair v (.chan (Chan.var_Chan a')) .im .L)))⟨
              edgeRen (treeEdges t); (id : Nat → Nat)⟩ =
              N.eval (.pure (.pair o (cvar e) .im .L)) := by
            rw [evalctx_cren, hNeq]
            congr 1
            asimp
            show Term.pure (.pair (v⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)
              (.chan (Chan.var_Chan (edgeRen (treeEdges t) a'))) .im .L) = _
            rw [hσc, ← hv]
          rw [hv1, hv2]
          exact ARS.Conv.refl
        · exfalso
          rw [hpin_i] at hpib
          rw [hpib] at hjb
          exact ((Option.some.inj hjb).symm ▸ hocca') hpid0
  | @comEx _ _ i j e M N v hij hek hv hi hj =>
      -- expose the root shape and the edge
      have hct : treeChans t = treeChansTail t := by
        cases typed with
        | root _ _ _ _ => rw [treeChans_eq_tail_root]
      have hlt : e < (treeEdges t).length := hek
      obtain ⟨⟨c, d⟩, hedge⟩ : ∃ ed, getElem? (treeEdges t) e = some ed :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      -- name→edge dispatch
      have hnameEdge : ∀ (a : Nat), a ∈ treeChans t →
          edgeRen (treeEdges t) a = e → a = c ∨ a = d := by
        intro a hmem hae
        have hD := (tree_soup_desc typed distinct).2.2.2 a (hct ▸ hmem)
        obtain ⟨p, ed, hp, hed⟩ := mem_edgeNames_getElem hD
        have hplt : p < (treeEdges t).length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hp
          cases hp
        have hed_eq : ed = (treeEdges t).get ⟨p, hplt⟩ := by
          rw [List.getElem?_eq_getElem hplt] at hp
          exact (Option.some.inj hp).symm
        have hreal := (treeRen_edgeRen typed distinct).realizes p hplt
        have hpe : p = e := by
          rcases hed with h | h
          · rw [← hae, ← h, hed_eq]
            exact hreal.1.symm
          · rw [← hae, ← h, hed_eq]
            exact hreal.2.symm
        subst hpe
        have hcd : ed = (c, d) := by
          rw [List.getElem?_eq_getElem hplt] at hp
          rw [List.getElem?_eq_getElem hplt] at hedge
          exact (Option.some.inj hp).symm.trans (Option.some.inj hedge)
        rw [hcd] at hed
        rcases hed with h | h
        · exact .inl h.symm
        · exact .inr h.symm
      -- pull the two threads back through the renaming
      have hi' : ∃ b, getElem? (treeBodies t) i = some b ∧
          (M.eval (.app (.send (cvar e) .ex) v .ex)) =
            b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ := by
        rw [List.getElem?_map] at hi
        cases hb : getElem? (treeBodies t) i with
        | none => rw [hb] at hi; cases hi
        | some b => rw [hb] at hi; exact ⟨b, rfl, (Option.some.inj hi).symm⟩
      obtain ⟨bi, hib, hbi⟩ := hi'
      obtain ⟨M₀, r₀, hbieq, hMeq, hr₀⟩ := eval_cren_reflect M hbi.symm
      cases r₀ <;> asimp at hr₀ <;> try simp at hr₀
      next u v₀ rv =>
      obtain ⟨hu, hv₀, hrv⟩ := hr₀
      cases u <;> asimp at hu <;> try simp at hu
      next w rv₁ =>
      obtain ⟨hw, hrv₁⟩ := hu
      cases w <;> asimp at hw <;> try simp at hw
      next ch =>
      cases ch with
      | var_Chan a =>
      asimp at hw
      simp at hw
      subst hrv
      subst hrv₁
      -- the redex holds the name explicitly
      have hocca : occurs a bi ≠ 0 := by
        rw [hbieq, occurs_evalctx]
        have h1 : occurs a (Term.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex) =
            1 + occurs a v₀ := by
          show occurs a (Term.chan (Chan.var_Chan a)) + occurs a v₀ = 1 + occurs a v₀
          simp [occurs]
        omega
      have hmema : a ∈ treeChans t :=
        (tree_soup_desc typed distinct).2.1 bi (List.mem_of_getElem? hib) a hocca
      -- pull the receiving thread back
      have hj' : ∃ b, getElem? (treeBodies t) j = some b ∧
          (N.eval (.recv (cvar e) .ex)) = b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ := by
        rw [List.getElem?_map] at hj
        cases hb : getElem? (treeBodies t) j with
        | none => rw [hb] at hj; cases hj
        | some b => rw [hb] at hj; exact ⟨b, rfl, (Option.some.inj hj).symm⟩
      obtain ⟨bj, hjb, hbj⟩ := hj'
      obtain ⟨N₀, r₀', hbjeq, hNeq, hr₀'⟩ := eval_cren_reflect N hbj.symm
      cases r₀' <;> asimp at hr₀' <;> try simp at hr₀'
      next w' rv' =>
      obtain ⟨hw', hrv'⟩ := hr₀'
      subst hrv'
      cases w' <;> asimp at hw' <;> try simp at hw'
      next ch' =>
      cases ch' with
      | var_Chan a' =>
      asimp at hw'
      simp at hw'
      have hocca' : occurs a' bj ≠ 0 := by
        rw [hbjeq, occurs_evalctx]
        have h1 : occurs a' (Term.recv (.chan (Chan.var_Chan a')) .ex) = 1 := by
          show occurs a' (Term.chan (Chan.var_Chan a')) = 1
          simp [occurs]
        omega
      have hmema' : a' ∈ treeChans t :=
        (tree_soup_desc typed distinct).2.1 bj (List.mem_of_getElem? hjb) a' hocca'
      -- the canonical renaming of the edge names
      have hget_e : (treeEdges t).get ⟨e, hlt⟩ = (c, d) := by
        rw [List.getElem?_eq_getElem hlt] at hedge
        exact Option.some.inj hedge
      have hreal_e := (treeRen_edgeRen typed distinct).realizes e hlt
      have hσc : edgeRen (treeEdges t) c = e := by
        have h1 := hreal_e.1
        rw [hget_e] at h1
        exact h1
      have hσd : edgeRen (treeEdges t) d = e := by
        have h1 := hreal_e.2
        rw [hget_e] at h1
        exact h1
      -- navigate to the edge and pin the fired positions by linearity
      obtain ⟨pi, pj, hpij, ⟨bpi, hpib, hpic, hpid0⟩, ⟨bpj, hpjb, hpjd, hpjc0⟩,
        _, _, contSEx, contREx, _⟩ := edge_replay typed distinct hedge
      have htysoup : TLLC.Process.Typed []
          (TLLC.Process.soupForm (treeSoup (edgeRen (treeEdges t)) t)) :=
        TLLC.Process.Typed.congr
          (TLLC.Process.Typed.congr typed.flatten_typed
            (TLLC.Process.prenex_sound t.flatten))
          (TLLC.Process.soupEquiv_congr (tree_soup_desc typed distinct).1)
      have hsum : (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)).sum = 2 :=
        soup_occurs_two htysoup hek
      have hcnt_i : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) i =
          some (occurs e (M.eval (.app (.send (cvar e) .ex) v .ex))) := by
        rw [List.getElem?_map, hi]
        rfl
      have hge_i : 1 ≤ occurs e (M.eval (.app (.send (cvar e) .ex) v .ex)) := by
        rw [occurs_evalctx]
        have h1 : occurs e (Term.app (.send (cvar e) .ex) v .ex) = 1 + occurs e v := by
          show occurs e (Term.chan (Chan.var_Chan e)) + occurs e v = 1 + occurs e v
          simp [occurs]
        omega
      have hcnt_j : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) j =
          some (occurs e (N.eval (.recv (cvar e) .ex))) := by
        rw [List.getElem?_map, hj]
        rfl
      have hge_j : 1 ≤ occurs e (N.eval (.recv (cvar e) .ex)) := by
        rw [occurs_evalctx]
        have h1 : occurs e (Term.recv (cvar e) .ex) = 1 := by
          show occurs e (Term.chan (Chan.var_Chan e)) = 1
          simp [occurs]
        omega
      have hcnt_pi : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) pi =
          some (occurs e (bpi⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)) := by
        rw [List.getElem?_map, List.getElem?_map, hpib]
        rfl
      have hge_pi : 1 ≤ occurs e (bpi⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) := by
        have h1 := occurs_cren_ge (f := edgeRen (treeEdges t)) c bpi
        rw [hσc] at h1
        omega
      have hcnt_pj : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) pj =
          some (occurs e (bpj⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)) := by
        rw [List.getElem?_map, List.getElem?_map, hpjb]
        rfl
      have hge_pj : 1 ≤ occurs e (bpj⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) := by
        have h1 := occurs_cren_ge (f := edgeRen (treeEdges t)) d bpj
        rw [hσd] at h1
        omega
      have hpi_in : pi = i ∨ pi = j := by
        by_contra hcon
        push Not at hcon
        have := sum_three hij hcon.1 hcon.2 hcnt_i hcnt_j hcnt_pi
        omega
      have hpj_in : pj = i ∨ pj = j := by
        by_contra hcon
        push Not at hcon
        have := sum_three hij hcon.1 hcon.2 hcnt_i hcnt_j hcnt_pj
        omega
      have hvv : Val v₀ := Val.cren_reflect (ξ := edgeRen (treeEdges t)) (hv₀.symm ▸ hv)
      rcases hnameEdge a hmema hw.symm with rfl | rfl
      · -- the sender holds the label: the parent sends
        have hipj : i ≠ pj := by
          intro h
          rw [h, hpjb] at hib
          exact ((Option.some.inj hib).symm ▸ hocca) hpjc0
        have hpin_i : pi = i := by
          rcases hpi_in with h | h
          · exact h
          · rcases hpj_in with h' | h'
            · exact absurd h'.symm hipj
            · exact absurd (h.trans h'.symm) hpij
        have hpin_j : j = pj := by
          rcases hpj_in with h' | h'
          · exact absurd h'.symm hipj
          · exact h'.symm
        rcases hnameEdge a' hmema' hw'.symm with rfl | rfl
        · exfalso
          rw [hpin_j, hpjb] at hjb
          exact ((Option.some.inj hjb).symm ▸ hocca') hpjc0
        · subst hpin_i
          subst hpin_j
          obtain ⟨t', tstep, hbodiesM, hedgesM, hchansM, _⟩ := contSEx M₀ N₀ v₀ hvv
            (by rw [← hbieq]; exact hib) (by rw [← hbjeq]; exact hjb)
          have hinv := typed.fidelity distinct tstep
          refine ⟨t', tstep, ?_⟩
          refine ARS.conv_trans (tree_soup_desc hinv.1 hinv.2).1 ?_
          -- the updated tree-side body list
          have hset_pj : getElem? ((treeBodies t).set pi
              (M₀.eval (.pure (.chan (Chan.var_Chan a))))) j =
              some (N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)) := by
            rw [getElem?_set_ne _ _ _ hij _, ← hbjeq]
            exact hjb
          have hib' : getElem? (treeBodies t) pi =
              some (M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)) := by
            rw [← hbieq]
            exact hib
          have h1 := coe_set_add (α := Term) hib'
            (M₀.eval (.pure (.chan (Chan.var_Chan a))))
          have h2 := coe_set_add (α := Term) hset_pj
            (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))
          have hupd : (↑(((treeBodies t).set pi (M₀.eval (.pure (.chan (Chan.var_Chan a))))).set j
                (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))) : Multiset Term) +
                ({M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)} +
                  {N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)}) =
              (↑(treeBodies t) : Multiset Term) +
                ({M₀.eval (.pure (.chan (Chan.var_Chan a)))} +
                  {N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L))}) := by
            calc (↑(((treeBodies t).set pi (M₀.eval (.pure (.chan (Chan.var_Chan a))))).set j
                  (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))) : Multiset Term) +
                  ({M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)} +
                    {N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)})
                = ((↑(((treeBodies t).set pi (M₀.eval (.pure (.chan (Chan.var_Chan a))))).set j
                    (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))) : Multiset Term) +
                    {N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)}) +
                    {M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)} := by
                  abel
              _ = ((↑((treeBodies t).set pi (M₀.eval (.pure (.chan (Chan.var_Chan a))))) : Multiset Term) +
                    {N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L))}) +
                    {M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)} := by
                  rw [h2]
              _ = ((↑((treeBodies t).set pi (M₀.eval (.pure (.chan (Chan.var_Chan a))))) : Multiset Term) +
                    {M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)}) +
                    {N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L))} := by
                  abel
              _ = ((↑(treeBodies t) : Multiset Term) +
                    {M₀.eval (.pure (.chan (Chan.var_Chan a)))}) +
                    {N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L))} := by
                  rw [h1]
              _ = (↑(treeBodies t) : Multiset Term) +
                    ({M₀.eval (.pure (.chan (Chan.var_Chan a)))} +
                      {N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L))}) := by
                  abel
          have hcoe : treeBodiesM t' =
              ↑(((treeBodies t).set pi (M₀.eval (.pure (.chan (Chan.var_Chan a))))).set j
                (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))) :=
            add_right_cancel (hbodiesM.trans hupd.symm)
          have hperm : (treeBodies t').Perm
              (((treeBodies t).set pi (M₀.eval (.pure (.chan (Chan.var_Chan a))))).set j
                (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))) :=
            Multiset.coe_eq_coe.mp hcoe
          unfold treeSoup
          refine ARS.conv_trans (TLLC.Process.SoupEquiv.perm
            (hperm.map (fun b => b⟨edgeRen (treeEdges t'); (id : Nat → Nat)⟩))) ?_
          have hv1 : (M₀.eval (.pure (.chan (Chan.var_Chan a))))⟨edgeRen (treeEdges t);
              (id : Nat → Nat)⟩ = M.eval (.pure (cvar e)) := by
            rw [evalctx_cren, hMeq]
            congr 1
            asimp
            show Term.pure (.chan (Chan.var_Chan (edgeRen (treeEdges t) a))) = _
            rw [hσc]
          have hv2 : (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))⟨
              edgeRen (treeEdges t); (id : Nat → Nat)⟩ =
              N.eval (.pure (.pair v (cvar e) .ex .L)) := by
            rw [evalctx_cren, hNeq]
            congr 1
            asimp
            show Term.pure (.pair (v₀⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)
              (.chan (Chan.var_Chan (edgeRen (treeEdges t) a'))) .ex .L) = _
            rw [hσd, hv₀]
          have hchain := treeSoup_reindexM (es := treeEdges t') (es' := treeEdges t)
            hedgesM (edgeNames_nodup hinv.1 hinv.2) (edgeNames_nodup typed distinct)
            (((treeBodies t).set pi (M₀.eval (.pure (.chan (Chan.var_Chan a))))).set j
              (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L))))
          have hc₂ : (((treeBodies t).set pi (M₀.eval (.pure (.chan (Chan.var_Chan a))))).set j
              (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))).map
                (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) =
              (((treeBodies t).map (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).set pi
                (M.eval (.pure (cvar e)))).set j (N.eval (.pure (.pair v (cvar e) .ex .L))) := by
            rw [map_set_comm, map_set_comm, hv1, hv2]
          rw [hc₂] at hchain
          exact hchain
      · -- the sender holds the child-side name: the parent receives
        have hipi : i ≠ pi := by
          intro h
          rw [h, hpib] at hib
          exact ((Option.some.inj hib).symm ▸ hocca) hpid0
        have hpin_i : pi = j := by
          rcases hpi_in with h | h
          · exact absurd h.symm hipi
          · exact h
        have hpin_j : pj = i := by
          rcases hpj_in with h | h
          · exact h
          · exact absurd (hpin_i.trans h.symm) hpij
        rcases hnameEdge a' hmema' hw'.symm with rfl | rfl
        · subst hpin_i
          subst hpin_j
          obtain ⟨t', tstep, hbodiesM, hedgesM, hchansM, _⟩ := contREx N₀ M₀ v₀ hvv
            (by rw [← hbieq]; exact hib) (by rw [← hbjeq]; exact hjb)
          have hinv := typed.fidelity distinct tstep
          refine ⟨t', tstep, ?_⟩
          refine ARS.conv_trans (tree_soup_desc hinv.1 hinv.2).1 ?_
          have hset_pj : getElem? ((treeBodies t).set pi
              (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))) pj =
              some (M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)) := by
            rw [getElem?_set_ne _ _ _ (Ne.symm hij) _, ← hbieq]
            exact hib
          have hjb' : getElem? (treeBodies t) pi =
              some (N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)) := by
            rw [← hbjeq]
            exact hjb
          have h1 := coe_set_add (α := Term) hjb'
            (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))
          have h2 := coe_set_add (α := Term) hset_pj
            (M₀.eval (.pure (.chan (Chan.var_Chan a))))
          have hupd : (↑(((treeBodies t).set pi
                (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))).set pj
                (M₀.eval (.pure (.chan (Chan.var_Chan a))))) : Multiset Term) +
                ({N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)} +
                  {M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)}) =
              (↑(treeBodies t) : Multiset Term) +
                ({N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L))} +
                  {M₀.eval (.pure (.chan (Chan.var_Chan a)))}) := by
            calc (↑(((treeBodies t).set pi
                  (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))).set pj
                  (M₀.eval (.pure (.chan (Chan.var_Chan a))))) : Multiset Term) +
                  ({N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)} +
                    {M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)})
                = ((↑(((treeBodies t).set pi
                    (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))).set pj
                    (M₀.eval (.pure (.chan (Chan.var_Chan a))))) : Multiset Term) +
                    {M₀.eval (.app (.send (.chan (Chan.var_Chan a)) .ex) v₀ .ex)}) +
                    {N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)} := by
                  abel
              _ = ((↑((treeBodies t).set pi
                    (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))) : Multiset Term) +
                    {M₀.eval (.pure (.chan (Chan.var_Chan a)))}) +
                    {N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)} := by
                  rw [h2]
              _ = ((↑((treeBodies t).set pi
                    (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))) : Multiset Term) +
                    {N₀.eval (.recv (.chan (Chan.var_Chan a')) .ex)}) +
                    {M₀.eval (.pure (.chan (Chan.var_Chan a)))} := by
                  abel
              _ = ((↑(treeBodies t) : Multiset Term) +
                    {N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L))}) +
                    {M₀.eval (.pure (.chan (Chan.var_Chan a)))} := by
                  rw [h1]
              _ = (↑(treeBodies t) : Multiset Term) +
                    ({N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L))} +
                      {M₀.eval (.pure (.chan (Chan.var_Chan a)))}) := by
                  abel
          have hcoe : treeBodiesM t' =
              ↑(((treeBodies t).set pi
                (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))).set pj
                (M₀.eval (.pure (.chan (Chan.var_Chan a))))) :=
            add_right_cancel (hbodiesM.trans hupd.symm)
          have hperm : (treeBodies t').Perm
              (((treeBodies t).set pi
                (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))).set pj
                (M₀.eval (.pure (.chan (Chan.var_Chan a))))) :=
            Multiset.coe_eq_coe.mp hcoe
          unfold treeSoup
          refine ARS.conv_trans (TLLC.Process.SoupEquiv.perm
            (hperm.map (fun b => b⟨edgeRen (treeEdges t'); (id : Nat → Nat)⟩))) ?_
          have hv1 : (M₀.eval (.pure (.chan (Chan.var_Chan a))))⟨edgeRen (treeEdges t);
              (id : Nat → Nat)⟩ = M.eval (.pure (cvar e)) := by
            rw [evalctx_cren, hMeq]
            congr 1
            asimp
            show Term.pure (.chan (Chan.var_Chan (edgeRen (treeEdges t) a))) = _
            rw [hσd]
          have hv2 : (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))⟨
              edgeRen (treeEdges t); (id : Nat → Nat)⟩ =
              N.eval (.pure (.pair v (cvar e) .ex .L)) := by
            rw [evalctx_cren, hNeq]
            congr 1
            asimp
            show Term.pure (.pair (v₀⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)
              (.chan (Chan.var_Chan (edgeRen (treeEdges t) a'))) .ex .L) = _
            rw [hσc, hv₀]
          have hchain := treeSoup_reindexM (es := treeEdges t') (es' := treeEdges t)
            hedgesM (edgeNames_nodup hinv.1 hinv.2) (edgeNames_nodup typed distinct)
            (((treeBodies t).set pi
              (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))).set pj
              (M₀.eval (.pure (.chan (Chan.var_Chan a)))))
          have hc₂ : (((treeBodies t).set pi
              (N₀.eval (.pure (.pair v₀ (.chan (Chan.var_Chan a')) .ex .L)))).set pj
              (M₀.eval (.pure (.chan (Chan.var_Chan a))))).map
                (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) =
              (((treeBodies t).map (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).set pj
                (M.eval (.pure (cvar e)))).set pi (N.eval (.pure (.pair v (cvar e) .ex .L))) := by
            rw [map_set_comm, map_set_comm, hv1, hv2, List.set_comm _ _ (Ne.symm hij)]
          rw [hc₂] at hchain
          exact hchain
        · exfalso
          rw [hpin_i] at hpib
          rw [hpib] at hjb
          exact ((Option.some.inj hjb).symm ▸ hocca') hpid0
  | @close _ _ i j e M N hij hek hi hj hMocc hNocc hothers =>
      -- expose the root shape and the edge
      have hct : treeChans t = treeChansTail t := by
        cases typed with
        | root _ _ _ _ => rw [treeChans_eq_tail_root]
      have hlt : e < (treeEdges t).length := hek
      obtain ⟨⟨c, d⟩, hedge⟩ : ∃ ed, getElem? (treeEdges t) e = some ed :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      -- name→edge dispatch
      have hnameEdge : ∀ (a : Nat), a ∈ treeChans t →
          edgeRen (treeEdges t) a = e → a = c ∨ a = d := by
        intro a hmem hae
        have hD := (tree_soup_desc typed distinct).2.2.2 a (hct ▸ hmem)
        obtain ⟨p, ed, hp, hed⟩ := mem_edgeNames_getElem hD
        have hplt : p < (treeEdges t).length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hp
          cases hp
        have hed_eq : ed = (treeEdges t).get ⟨p, hplt⟩ := by
          rw [List.getElem?_eq_getElem hplt] at hp
          exact (Option.some.inj hp).symm
        have hreal := (treeRen_edgeRen typed distinct).realizes p hplt
        have hpe : p = e := by
          rcases hed with h | h
          · rw [← hae, ← h, hed_eq]
            exact hreal.1.symm
          · rw [← hae, ← h, hed_eq]
            exact hreal.2.symm
        subst hpe
        have hcd : ed = (c, d) := by
          rw [List.getElem?_eq_getElem hplt] at hp
          rw [List.getElem?_eq_getElem hplt] at hedge
          exact (Option.some.inj hp).symm.trans (Option.some.inj hedge)
        rw [hcd] at hed
        rcases hed with h | h
        · exact .inl h.symm
        · exact .inr h.symm
      -- pull the two threads back through the renaming
      have hi' : ∃ b, getElem? (treeBodies t) i = some b ∧
          (M.eval (.close true (cvar e))) = b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ := by
        rw [List.getElem?_map] at hi
        cases hb : getElem? (treeBodies t) i with
        | none => rw [hb] at hi; cases hi
        | some b => rw [hb] at hi; exact ⟨b, rfl, (Option.some.inj hi).symm⟩
      obtain ⟨bi, hib, hbi⟩ := hi'
      obtain ⟨M₀, r₀, hbieq, hMeq, hr₀⟩ := eval_cren_reflect M hbi.symm
      cases r₀ <;> asimp at hr₀ <;> try simp at hr₀
      next b₀ w =>
      obtain ⟨hb₀, hw⟩ := hr₀
      subst hb₀
      cases w <;> asimp at hw <;> try simp at hw
      next ch =>
      cases ch with
      | var_Chan a =>
      asimp at hw
      simp at hw
      have hocca : occurs a bi ≠ 0 := by
        rw [hbieq, occurs_evalctx]
        have h1 : occurs a (Term.close true (.chan (Chan.var_Chan a))) = 1 := by
          show occurs a (Term.chan (Chan.var_Chan a)) = 1
          simp [occurs]
        omega
      have hmema : a ∈ treeChans t :=
        (tree_soup_desc typed distinct).2.1 bi (List.mem_of_getElem? hib) a hocca
      have hj' : ∃ b, getElem? (treeBodies t) j = some b ∧
          (N.eval (.close false (cvar e))) = b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ := by
        rw [List.getElem?_map] at hj
        cases hb : getElem? (treeBodies t) j with
        | none => rw [hb] at hj; cases hj
        | some b => rw [hb] at hj; exact ⟨b, rfl, (Option.some.inj hj).symm⟩
      obtain ⟨bj, hjb, hbj⟩ := hj'
      obtain ⟨N₀, r₀', hbjeq, hNeq, hr₀'⟩ := eval_cren_reflect N hbj.symm
      cases r₀' <;> asimp at hr₀' <;> try simp at hr₀'
      next b₀' w' =>
      obtain ⟨hb₀', hw'⟩ := hr₀'
      subst hb₀'
      cases w' <;> asimp at hw' <;> try simp at hw'
      next ch' =>
      cases ch' with
      | var_Chan a' =>
      asimp at hw'
      simp at hw'
      have hocca' : occurs a' bj ≠ 0 := by
        rw [hbjeq, occurs_evalctx]
        have h1 : occurs a' (Term.close false (.chan (Chan.var_Chan a'))) = 1 := by
          show occurs a' (Term.chan (Chan.var_Chan a')) = 1
          simp [occurs]
        omega
      have hmema' : a' ∈ treeChans t :=
        (tree_soup_desc typed distinct).2.1 bj (List.mem_of_getElem? hjb) a' hocca'
      -- the canonical renaming of the edge names
      have hget_e : (treeEdges t).get ⟨e, hlt⟩ = (c, d) := by
        rw [List.getElem?_eq_getElem hlt] at hedge
        exact Option.some.inj hedge
      have hreal_e := (treeRen_edgeRen typed distinct).realizes e hlt
      have hσc : edgeRen (treeEdges t) c = e := by
        have h1 := hreal_e.1
        rw [hget_e] at h1
        exact h1
      have hσd : edgeRen (treeEdges t) d = e := by
        have h1 := hreal_e.2
        rw [hget_e] at h1
        exact h1
      -- navigate to the edge and pin the fired positions by linearity
      obtain ⟨pi, pj, hpij, ⟨bpi, hpib, hpic, hpid0⟩, ⟨bpj, hpjb, hpjd, hpjc0⟩,
        _, _, _, _, contClose⟩ := edge_replay typed distinct hedge
      have htysoup : TLLC.Process.Typed []
          (TLLC.Process.soupForm (treeSoup (edgeRen (treeEdges t)) t)) :=
        TLLC.Process.Typed.congr
          (TLLC.Process.Typed.congr typed.flatten_typed
            (TLLC.Process.prenex_sound t.flatten))
          (TLLC.Process.soupEquiv_congr (tree_soup_desc typed distinct).1)
      have hsum : (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)).sum = 2 :=
        soup_occurs_two htysoup hek
      have hcnt_i : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) i =
          some (occurs e (M.eval (.close true (cvar e)))) := by
        rw [List.getElem?_map, hi]
        rfl
      have hge_i : 1 ≤ occurs e (M.eval (.close true (cvar e))) := by
        rw [occurs_evalctx]
        have h1 : occurs e (Term.close true (cvar e)) = 1 := by
          show occurs e (Term.chan (Chan.var_Chan e)) = 1
          simp [occurs]
        omega
      have hcnt_j : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) j =
          some (occurs e (N.eval (.close false (cvar e)))) := by
        rw [List.getElem?_map, hj]
        rfl
      have hge_j : 1 ≤ occurs e (N.eval (.close false (cvar e))) := by
        rw [occurs_evalctx]
        have h1 : occurs e (Term.close false (cvar e)) = 1 := by
          show occurs e (Term.chan (Chan.var_Chan e)) = 1
          simp [occurs]
        omega
      have hcnt_pi : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) pi =
          some (occurs e (bpi⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)) := by
        rw [List.getElem?_map, List.getElem?_map, hpib]
        rfl
      have hge_pi : 1 ≤ occurs e (bpi⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) := by
        have h1 := occurs_cren_ge (f := edgeRen (treeEdges t)) c bpi
        rw [hσc] at h1
        omega
      have hcnt_pj : getElem? (((treeBodies t).map
          (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map (occurs e)) pj =
          some (occurs e (bpj⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)) := by
        rw [List.getElem?_map, List.getElem?_map, hpjb]
        rfl
      have hge_pj : 1 ≤ occurs e (bpj⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) := by
        have h1 := occurs_cren_ge (f := edgeRen (treeEdges t)) d bpj
        rw [hσd] at h1
        omega
      have hpi_in : pi = i ∨ pi = j := by
        by_contra hcon
        push Not at hcon
        have := sum_three hij hcon.1 hcon.2 hcnt_i hcnt_j hcnt_pi
        omega
      have hpj_in : pj = i ∨ pj = j := by
        by_contra hcon
        push Not at hcon
        have := sum_three hij hcon.1 hcon.2 hcnt_i hcnt_j hcnt_pj
        omega
      rcases hnameEdge a hmema hw.symm with rfl | rfl
      · -- the closing thread holds the label: the parent closes (rule Close)
        have hipj : i ≠ pj := by
          intro h
          rw [h, hpjb] at hib
          exact ((Option.some.inj hib).symm ▸ hocca) hpjc0
        have hpin_i : pi = i := by
          rcases hpi_in with h | h
          · exact h
          · rcases hpj_in with h' | h'
            · exact absurd h'.symm hipj
            · exact absurd (h.trans h'.symm) hpij
        have hpin_j : j = pj := by
          rcases hpj_in with h' | h'
          · exact absurd h'.symm hipj
          · exact h'.symm
        rcases hnameEdge a' hmema' hw'.symm with rfl | rfl
        · exfalso
          rw [hpin_j, hpjb] at hjb
          exact ((Option.some.inj hjb).symm ▸ hocca') hpjc0
        · subst hpin_i
          subst hpin_j
          have hpiLt : pi < (treeBodies t).length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hib
            cases hib
          have hjLt : j < (treeBodies t).length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hjb
            cases hjb
          have hib' : getElem? (treeBodies t) pi =
              some (M₀.eval (.close true (.chan (Chan.var_Chan a)))) := by
            rw [← hbieq]
            exact hib
          have hjb' : getElem? (treeBodies t) j =
              some (N₀.eval (.close (!true) (.chan (Chan.var_Chan a')))) := by
            rw [show (!true) = false from rfl, ← hbjeq]
            exact hjb
          obtain ⟨t', tstep, hbodiesM, hedgesM, hchansM, _⟩ := contClose M₀ N₀ true hib' hjb'
          have hinv := typed.fidelity distinct tstep
          refine ⟨t', tstep, ?_⟩
          refine ARS.conv_trans (tree_soup_desc hinv.1 hinv.2).1 ?_
          have hcoe : treeBodiesM t' =
              ↑(((treeBodies t).set pi (M₀.eval (.pure .one))).set j
                (N₀.eval (.pure .one))) :=
            add_right_cancel (hbodiesM.trans
              (coe_set_set hij hib' hjb' (M₀.eval (.pure .one)) (N₀.eval (.pure .one))).symm)
          have hperm : (treeBodies t').Perm
              (((treeBodies t).set pi (M₀.eval (.pure .one))).set j
                (N₀.eval (.pure .one))) :=
            Multiset.coe_eq_coe.mp hcoe
          unfold treeSoup
          refine ARS.conv_trans (TLLC.Process.SoupEquiv.perm
            (hperm.map (fun b => b⟨edgeRen (treeEdges t'); (id : Nat → Nat)⟩))) ?_
          have heqM : (M₀.eval (.pure .one))⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ =
              M.eval (.pure .one) := by
            rw [evalctx_cren, hMeq, tren_pure_one]
          have heqN : (N₀.eval (.pure .one))⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ =
              N.eval (.pure .one) := by
            rw [evalctx_cren, hNeq, tren_pure_one]
          have hPa : occurs a (M₀.eval (.pure .one)) = 0 ∧
              occurs a' (M₀.eval (.pure .one)) = 0 := by
            constructor
            · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a (M₀.eval (.pure .one))
              rw [hσc, heqM] at hle
              omega
            · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a' (M₀.eval (.pure .one))
              rw [hσd, heqM] at hle
              omega
          have hQa : occurs a (N₀.eval (.pure .one)) = 0 ∧
              occurs a' (N₀.eval (.pure .one)) = 0 := by
            constructor
            · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a (N₀.eval (.pure .one))
              rw [hσc, heqN] at hle
              omega
            · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a' (N₀.eval (.pure .one))
              rw [hσd, heqN] at hle
              omega
          have hoccupd : ∀ b ∈ ((treeBodies t).set pi (M₀.eval (.pure .one))).set j
              (N₀.eval (.pure .one)), occurs a b = 0 ∧ occurs a' b = 0 := by
            intro b hb
            obtain ⟨x, hx⟩ := List.getElem?_of_mem hb
            by_cases hxj : x = j
            · subst hxj
              rw [List.getElem?_set_self (by rw [List.length_set]; exact hjLt)] at hx
              obtain rfl := Option.some.inj hx
              exact hQa
            · rw [getElem?_set_ne _ _ _ (Ne.symm hxj) _] at hx
              by_cases hxpi : x = pi
              · subst hxpi
                rw [List.getElem?_set_self hpiLt] at hx
                obtain rfl := Option.some.inj hx
                exact hPa
              · rw [getElem?_set_ne _ _ _ (Ne.symm hxpi) _] at hx
                have hproc : occurs e (b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) = 0 := by
                  refine hothers x _ ?_ hxpi hxj
                  rw [List.getElem?_map, hx]
                  rfl
                constructor
                · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a b
                  rw [hσc, hproc] at hle
                  omega
                · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a' b
                  rw [hσd, hproc] at hle
                  omega
          have hchain := treeSoup_remove (es := treeEdges t) (es' := treeEdges t')
            hedge hedgesM (edgeNames_nodup typed distinct) (edgeNames_nodup hinv.1 hinv.2)
            (((treeBodies t).set pi (M₀.eval (.pure .one))).set j (N₀.eval (.pure .one)))
            hoccupd
          have hfuse : ((treeBodies t).map
              (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map
              (fun n => n⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩) =
              (treeBodies t).map (fun b =>
                b⟨fun x => TLLC.Process.unbind e (edgeRen (treeEdges t) x);
                  (id : Nat → Nat)⟩) :=
            TLLC.Process.tsmap_comp (treeBodies t) (edgeRen (treeEdges t))
              (TLLC.Process.unbind e)
          have hv1 : (M₀.eval (.pure .one))⟨fun x =>
              TLLC.Process.unbind e (edgeRen (treeEdges t) x); (id : Nat → Nat)⟩ =
              (M.eval (.pure .one))⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩ :=
            (TLLC.Process.tren_comp (M₀.eval (.pure .one)) (edgeRen (treeEdges t))
              (TLLC.Process.unbind e)).symm.trans
              (congrArg (fun m => m⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩) heqM)
          have hv2 : (N₀.eval (.pure .one))⟨fun x =>
              TLLC.Process.unbind e (edgeRen (treeEdges t) x); (id : Nat → Nat)⟩ =
              (N.eval (.pure .one))⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩ :=
            (TLLC.Process.tren_comp (N₀.eval (.pure .one)) (edgeRen (treeEdges t))
              (TLLC.Process.unbind e)).symm.trans
              (congrArg (fun m => m⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩) heqN)
          have hc₂ : (((treeBodies t).set pi (M₀.eval (.pure .one))).set j
              (N₀.eval (.pure .one))).map (fun b =>
                b⟨fun x => TLLC.Process.unbind e (edgeRen (treeEdges t) x);
                  (id : Nat → Nat)⟩) =
              ((((treeBodies t).map (fun b => b⟨edgeRen (treeEdges t);
                  (id : Nat → Nat)⟩)).set pi
                (M.eval (.pure .one))).set j (N.eval (.pure .one))).map
                (fun n => n⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩) := by
            rw [map_set_comm, map_set_comm, map_set_comm, map_set_comm, hfuse, hv1, hv2]
          rw [hc₂] at hchain
          exact hchain
      · -- the closing thread holds the child-side name: the parent waits (rule Wait)
        have hipi : i ≠ pi := by
          intro h
          rw [h, hpib] at hib
          exact ((Option.some.inj hib).symm ▸ hocca) hpid0
        have hpin_i : pi = j := by
          rcases hpi_in with h | h
          · exact absurd h.symm hipi
          · exact h
        have hpin_j : pj = i := by
          rcases hpj_in with h | h
          · exact h
          · exact absurd (hpin_i.trans h.symm) hpij
        rcases hnameEdge a' hmema' hw'.symm with rfl | rfl
        · subst hpin_i
          subst hpin_j
          have hpiLt : pi < (treeBodies t).length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hjb
            cases hjb
          have hpjLt : pj < (treeBodies t).length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hib
            cases hib
          have hjb' : getElem? (treeBodies t) pi =
              some (N₀.eval (.close false (.chan (Chan.var_Chan a')))) := by
            rw [← hbjeq]
            exact hjb
          have hib' : getElem? (treeBodies t) pj =
              some (M₀.eval (.close (!false) (.chan (Chan.var_Chan a)))) := by
            rw [show (!false) = true from rfl, ← hbieq]
            exact hib
          obtain ⟨t', tstep, hbodiesM, hedgesM, hchansM, _⟩ := contClose N₀ M₀ false hjb' hib'
          have hinv := typed.fidelity distinct tstep
          refine ⟨t', tstep, ?_⟩
          refine ARS.conv_trans (tree_soup_desc hinv.1 hinv.2).1 ?_
          have hcoe : treeBodiesM t' =
              ↑(((treeBodies t).set pi (N₀.eval (.pure .one))).set pj
                (M₀.eval (.pure .one))) :=
            add_right_cancel (hbodiesM.trans
              (coe_set_set hpij hjb' hib' (N₀.eval (.pure .one)) (M₀.eval (.pure .one))).symm)
          have hperm : (treeBodies t').Perm
              (((treeBodies t).set pi (N₀.eval (.pure .one))).set pj
                (M₀.eval (.pure .one))) :=
            Multiset.coe_eq_coe.mp hcoe
          unfold treeSoup
          refine ARS.conv_trans (TLLC.Process.SoupEquiv.perm
            (hperm.map (fun b => b⟨edgeRen (treeEdges t'); (id : Nat → Nat)⟩))) ?_
          have heqM : (M₀.eval (.pure .one))⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ =
              M.eval (.pure .one) := by
            rw [evalctx_cren, hMeq, tren_pure_one]
          have heqN : (N₀.eval (.pure .one))⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩ =
              N.eval (.pure .one) := by
            rw [evalctx_cren, hNeq, tren_pure_one]
          have hPa : occurs a (M₀.eval (.pure .one)) = 0 ∧
              occurs a' (M₀.eval (.pure .one)) = 0 := by
            constructor
            · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a (M₀.eval (.pure .one))
              rw [hσd, heqM] at hle
              omega
            · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a' (M₀.eval (.pure .one))
              rw [hσc, heqM] at hle
              omega
          have hQa : occurs a (N₀.eval (.pure .one)) = 0 ∧
              occurs a' (N₀.eval (.pure .one)) = 0 := by
            constructor
            · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a (N₀.eval (.pure .one))
              rw [hσd, heqN] at hle
              omega
            · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a' (N₀.eval (.pure .one))
              rw [hσc, heqN] at hle
              omega
          have hoccupd : ∀ b ∈ ((treeBodies t).set pi (N₀.eval (.pure .one))).set pj
              (M₀.eval (.pure .one)), occurs a' b = 0 ∧ occurs a b = 0 := by
            intro b hb
            obtain ⟨x, hx⟩ := List.getElem?_of_mem hb
            by_cases hxpj : x = pj
            · subst hxpj
              rw [List.getElem?_set_self (by rw [List.length_set]; exact hpjLt)] at hx
              obtain rfl := Option.some.inj hx
              exact ⟨hPa.2, hPa.1⟩
            · rw [getElem?_set_ne _ _ _ (Ne.symm hxpj) _] at hx
              by_cases hxpi : x = pi
              · subst hxpi
                rw [List.getElem?_set_self hpiLt] at hx
                obtain rfl := Option.some.inj hx
                exact ⟨hQa.2, hQa.1⟩
              · rw [getElem?_set_ne _ _ _ (Ne.symm hxpi) _] at hx
                have hproc : occurs e (b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩) = 0 := by
                  refine hothers x _ ?_ hxpj hxpi
                  rw [List.getElem?_map, hx]
                  rfl
                constructor
                · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a' b
                  rw [hσc, hproc] at hle
                  omega
                · have hle := occurs_cren_ge (f := edgeRen (treeEdges t)) a b
                  rw [hσd, hproc] at hle
                  omega
          have hchain := treeSoup_remove (es := treeEdges t) (es' := treeEdges t')
            hedge hedgesM (edgeNames_nodup typed distinct) (edgeNames_nodup hinv.1 hinv.2)
            (((treeBodies t).set pi (N₀.eval (.pure .one))).set pj (M₀.eval (.pure .one)))
            hoccupd
          have hfuse : ((treeBodies t).map
              (fun b => b⟨edgeRen (treeEdges t); (id : Nat → Nat)⟩)).map
              (fun n => n⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩) =
              (treeBodies t).map (fun b =>
                b⟨fun x => TLLC.Process.unbind e (edgeRen (treeEdges t) x);
                  (id : Nat → Nat)⟩) :=
            TLLC.Process.tsmap_comp (treeBodies t) (edgeRen (treeEdges t))
              (TLLC.Process.unbind e)
          have hv1 : (M₀.eval (.pure .one))⟨fun x =>
              TLLC.Process.unbind e (edgeRen (treeEdges t) x); (id : Nat → Nat)⟩ =
              (M.eval (.pure .one))⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩ :=
            (TLLC.Process.tren_comp (M₀.eval (.pure .one)) (edgeRen (treeEdges t))
              (TLLC.Process.unbind e)).symm.trans
              (congrArg (fun m => m⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩) heqM)
          have hv2 : (N₀.eval (.pure .one))⟨fun x =>
              TLLC.Process.unbind e (edgeRen (treeEdges t) x); (id : Nat → Nat)⟩ =
              (N.eval (.pure .one))⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩ :=
            (TLLC.Process.tren_comp (N₀.eval (.pure .one)) (edgeRen (treeEdges t))
              (TLLC.Process.unbind e)).symm.trans
              (congrArg (fun m => m⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩) heqN)
          have hc₂ : (((treeBodies t).set pi (N₀.eval (.pure .one))).set pj
              (M₀.eval (.pure .one))).map (fun b =>
                b⟨fun x => TLLC.Process.unbind e (edgeRen (treeEdges t) x);
                  (id : Nat → Nat)⟩) =
              ((((treeBodies t).map (fun b => b⟨edgeRen (treeEdges t);
                  (id : Nat → Nat)⟩)).set pj
                (M.eval (.pure .one))).set pi (N.eval (.pure .one))).map
                (fun n => n⟨TLLC.Process.unbind e; (id : Nat → Nat)⟩) := by
            rw [map_set_comm, map_set_comm, map_set_comm, map_set_comm, hfuse, hv1, hv2,
              List.set_comm _ _ (Ne.symm hij)]
          rw [hc₂] at hchain
          exact hchain
        · exfalso
          rw [hpin_i] at hpib
          rw [hpib] at hjb
          exact ((Option.some.inj hjb).symm ▸ hocca') hpid0

/-- Replaying a soup step of a valid tree's flattening on the tree itself: normalize the soup to
the canonical tree soup, pull the machine step back onto it positionally, and replay. -/
theorem soup_inv {t : Tree} {c₂ : TLLC.Process.Config}
    (typed : Typed t) (distinct : Distinct t)
    (st : TLLC.Process.SoupStep (TLLC.Process.prenex t.flatten) c₂) :
    ∃ t', Step t t' ∧ TLLC.Process.SoupEquiv (TLLC.Process.prenex t'.flatten) c₂ := by
  have hd := (tree_soup_desc typed distinct).1
  obtain ⟨c₁', c₂', e1, prim, e2⟩ := st
  have hty : TLLC.Process.Typed []
      (TLLC.Process.soupForm (treeSoup (edgeRen (treeEdges t)) t)) :=
    TLLC.Process.Typed.congr
      (TLLC.Process.Typed.congr typed.flatten_typed (TLLC.Process.prenex_sound t.flatten))
      (TLLC.Process.soupEquiv_congr hd)
  obtain ⟨c₂'', pa, se⟩ := prim_pullback hty
    (ARS.conv_trans (ARS.conv_sym hd) e1) prim
  obtain ⟨t', tstep, se'⟩ := primAt_treeSoup typed distinct pa
  exact ⟨t', tstep, ARS.conv_trans se' (ARS.conv_trans se e2)⟩

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
