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

/-- Pull a machine step back through the soup equivalence to a positional machine step of the
canonical configuration. The threads must be typed: reflecting a term reduction through the
congruence slack of implicit positions is only sound for well-typed threads. -/
lemma prim_pullback {c c₁ c₂ : Config}
    (hty : ∀ m ∈ c.2, ∃ Θ, Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M .unit)
    (he : SoupEquiv c c₁) (hp : Prim c₁ c₂) :
    ∃ c₂', TLLC.Process.PrimAt c c₂' ∧ SoupEquiv c₂' c₂ := by
  obtain ⟨hk, ξ, ζ, hζξ, hξζ, hfix, l, hperm, hforall⟩ := TLLC.Process.soupEquiv_flat he
  obtain ⟨k, ts⟩ := c
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
      obtain ⟨Θ, tym₀⟩ := hty m₀ hmem
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
      sorry
  | @comIm k₁ M N o ts₁ =>
      sorry
  | @comEx k₁ M N v ts₁ hv =>
      sorry
  | @close k₁ M N ts₁ hM hN hocc =>
      sorry

/-- A positional machine step of the prenex soup of a valid distinct tree replays as a
spawning-tree step with soup-equivalent result. -/
theorem primAt_tree {t : Tree} {c₂ : Config} (typed : Typed t) (distinct : Distinct t)
    (hp : TLLC.Process.PrimAt (prenex t.flatten) c₂) :
    ∃ t', Step t t' ∧ SoupEquiv (prenex t'.flatten) c₂ := by
  sorry

/-- Replaying a soup step of a valid tree's flattening on the tree itself. -/
theorem soup_inv {t : Tree} {c₂ : TLLC.Process.Config}
    (typed : Typed t) (distinct : Distinct t)
    (st : TLLC.Process.SoupStep (TLLC.Process.prenex t.flatten) c₂) :
    ∃ t', Step t t' ∧ TLLC.Process.SoupEquiv (TLLC.Process.prenex t'.flatten) c₂ := by
  obtain ⟨c₁', c₂', e1, prim, e2⟩ := st
  obtain ⟨c₂'', pa, se⟩ := prim_pullback (flatten_threads_typed typed) e1 prim
  obtain ⟨t', tstep, se'⟩ := primAt_tree typed distinct pa
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
