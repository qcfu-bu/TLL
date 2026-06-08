import TLLC.Process.CSubst
import TLLC.Process.Occurs

/-!
# Process subject reduction (self-dual single-channel encoding)

Port of `coq_session/proc_sr.v`: structural congruence preserves typing (`proc_congr0_type`,
`proc_congr_type`) and process reduction preserves typing (`proc_sr`). Adapted to the self-dual
single-channel encoding (see [[tllc-process-channel-encoding]]); the prerequisites
`Typed.exch`/`cweaken`/`cstrengthen`/`occursCount`/`procOccurs_cren` are the channel-machinery
lemmas of the Process layer.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- The empty process types the trivial returning thread `⟨return ()⟩`. -/
lemma PEmpty.return {Θ} (emp : PEmpty Θ) : Θ ⊩ Proc.tm (.pure .one) := by
  obtain ⟨Θd, rea, e⟩ := emp.realize
  exact .exp rea (.pure (.one e .nil .nil))

/-! ## Exchange involution and the `0`-channel non-occurrence. -/

/-- `exch_ren` is an involution. -/
lemma exch_ren_invol : funcomp exch_ren exch_ren = (id : Nat → Nat) := by
  funext x
  match x with
  | 0 => rfl
  | 1 => rfl
  | (_ + 2) => rfl

/-- `0` is out of range of the `+1` channel shift. -/
lemma iren0_succ : Iren 0 ((· + 1) : Nat → Nat) := fun x => Nat.succ_ne_zero x

/-! ## Structural congruence preserves typing. -/

/-- One-step structural congruence preserves typing in both directions (Coq `proc_congr0_type`). -/
lemma Typed.congr0 {p q} (cgr : Congr p q) : ∀ {Θ}, (Θ ⊩ p) ↔ (Θ ⊩ q) := by
  induction cgr with
  | @par_sym p q =>
    intro Θ
    constructor <;>
    · intro ty; cases ty with | par mrg t1 t2 => exact .par mrg.sym t2 t1
  | @assoc o p q =>
    intro Θ
    constructor
    · intro ty
      cases ty with
      | par mrg1 ho tpq =>
        cases tpq with
        | par mrg2 tp tq =>
          obtain ⟨Θc, mc1, mc2⟩ := mrg1.sym.splitL mrg2
          exact .par mc2 (.par mc1.sym ho tp) tq
    · intro ty
      cases ty with
      | par mrg1 top tq =>
        cases top with
        | par mrg2 ho tp =>
          obtain ⟨Θc, mc1, mc2⟩ := mrg1.splitR mrg2
          exact .par mc2.sym ho (.par mc1 tp tq)
  | @scope p q =>
    intro Θ
    constructor
    · intro ty
      cases ty with
      | par mrg t1 t2 =>
        cases t1 with
        | res tyA tp => exact .res tyA (.par (.bothL mrg) tp t2.cweaken)
    · intro ty
      cases ty with
      | res tyA tpar =>
        cases tpar with
        | par mrg tp tq =>
          cases mrg with
          | bothL mrg' => exact .par mrg' (.res tyA tp) tq.cstrengthen
          | bothR mrg' =>
            have h1 := tq.occursCount 0
            rw [procOccurs_cren iren0_succ q] at h1
            exact absurd h1 (by simp [pcount])
          | split mrg' =>
            have h1 := tq.occursCount 0
            rw [procOccurs_cren iren0_succ q] at h1
            exact absurd h1 (by simp [pcount])
  | @exch p =>
    intro Θ
    constructor
    · intro ty
      rw [csubst_exch]
      exact ty.exch
    · intro ty
      have h := ty.exch
      rw [show (p[Process.exch; Term.var_Term])⟨exch_ren; (id : Nat → Nat)⟩ = p from by
            rw [csubst_exch]; asimp; rw [exch_ren_invol]; asimp] at h
      exact h
  | @par p p' q q' _ _ ihp ihq =>
    intro Θ
    constructor
    · intro ty; cases ty with | par mrg t1 t2 => exact .par mrg (ihp.mp t1) (ihq.mp t2)
    · intro ty; cases ty with | par mrg t1 t2 => exact .par mrg (ihp.mpr t1) (ihq.mpr t2)
  | @res p p' _ ih =>
    intro Θ
    constructor
    · intro ty; cases ty with | res tyA tp => exact .res tyA (ih.mp tp)
    · intro ty; cases ty with | res tyA tp => exact .res tyA (ih.mpr tp)
  | @«end» p =>
    intro Θ
    constructor
    · intro ty
      cases ty with
      | par mrg t1 t2 =>
        cases t2 with
        | exp rea tym =>
          obtain ⟨B, ty1, _⟩ := pure_invX tym
          have emp := one_inv ty1
          have e := mrg.emptyR (rea.pempty emp)
          rw [e] at t1; exact t1
    · intro ty
      obtain ⟨Θe, emp, mrg⟩ := PMerge.refl_emptyR Θ
      exact .par mrg ty emp.return

/-- Structural congruence preserves typing (Coq `proc_congr_type`). -/
lemma Typed.congr {Θ p q} (ty : Θ ⊩ p) (e : p ≡ₚ q) : Θ ⊩ q := by
  induction e generalizing Θ with
  | refl => exact ty
  | tail _ c ih => exact (Typed.congr0 c).mp (ih ty)
  | taili _ c ih => exact (Typed.congr0 c).mpr (ih ty)

end TLLC.Process
