import TLLC.Spawning.Progress
import TLLC.Spawning.Reflection

/-!
# Deadlock freedom for standard process reduction

The fully assembled deadlock-freedom theorem: every standard multi-step reduct of the
flattening of a valid, distinct spawning tree either is the finished process up to structural
congruence, or can take another standard reduction step. No reachable process is ever stuck.

The proof composes the four pillars:

- **Reflection** (converse of Lemma 5.86, `TLLC/Spawning/Reflection.lean`): the standard
  reduction sequence is replayed on the spawning tree, landing on a tree `t'` whose flattening
  is structurally congruent to the reduct.
- **Fidelity** (`Typed.fidelity_red`, `TLLC/Spawning/Fidelity.lean`): validity and channel
  distinctness persist along the replayed tree reduction.
- **Spawning-tree progress** (Lemma 5.92, `Typed.progress` in `TLLC/Spawning/Progress.lean`):
  the tree `t'` is terminal or takes a tree step.
- **Terminal characterization** (Lemma 5.89, `Terminal.flatten_congr`) and **simulation**
  (Lemma 5.86, `TLLC/Spawning/Simulation.lean`): a terminal tree flattens to the finished
  process, and a tree step maps to a standard step of the flattening, re-anchored on the
  reduct by the congruence rule of `⇛`.

`deadlock_free_tm` instantiates the theorem to a closed well-typed program launched as a
single thread: the singleton spawning tree `.root m [] []` flattens to `.tm m`.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- **Deadlock freedom** for standard reduction: every standard reduct of the flattening of a
valid distinct spawning tree is finished up to structural congruence, or reduces further. -/
theorem deadlock_free {t : Tree} (typed : Typed t) (distinct : Distinct t) {P : Proc}
    (red : TLLC.Process.Red t.flatten P) :
    TLLC.Process.Congruence P (.tm (.pure .one)) ∨ ∃ P', TLLC.Process.Step P P' := by
  obtain ⟨t', tred, congr⟩ := reflection_red typed distinct red
  have inv := typed.fidelity_red distinct tred
  rcases inv.1.progress with hterm | ⟨t'', tstep⟩
  · exact .inl (ARS.conv_trans congr hterm.flatten_congr)
  · exact .inr ⟨t''.flatten,
      TLLC.Process.Step.congr congr (simulation (.inl inv.1) inv.2 tstep) ARS.Conv.refl⟩

/-- Deadlock freedom for a closed well-typed program run as a single thread. -/
theorem deadlock_free_tm {m : Term}
    (ty : ([] : PCtx) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : .M .unit) {P : Proc}
    (red : TLLC.Process.Red (.tm m) P) :
    TLLC.Process.Congruence P (.tm (.pure .one)) ∨ ∃ P', TLLC.Process.Step P P' := by
  have typed : Typed (.root m [] []) := .root .nil ty .nil .nil
  have distinct : Distinct (.root m [] []) := by
    show (treeChans (.root m [] [])).Nodup
    rw [treeChans_root]
    simp
  have hf : (Tree.root m [] []).flatten = .tm m := by
    rw [Tree.flatten_root]
    simp [flattenBody]
  exact deadlock_free typed distinct (hf.symm ▸ red)

end TLLC.Spawning
