import TLLC.Spawning.Simulation

/-!
# Terminal spawning trees

The `Terminal` judgment from the report characterizes spawning trees with no further reductions:
the root computation has finished with `return ()`, all children have been cleaned up, and every
detached subtree is itself terminal. Lemma 5.89 shows that such trees flatten, up to process
structural congruence, to the single finished thread `⟨return ()⟩` — this is where the report's
Root-Unit/Node-Unit cleanup (deliberately absent from `Step`) is discharged.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- A spawning tree with no further reductions (report rule Terminal-Root): the root computation
has returned unit, the children set is empty, and every detached subtree is terminal. Nodes are
never terminal — they still owe communication on their parent endpoint. -/
inductive Terminal : Tree → Prop where
  | root {qs : List Tree} :
      (∀ q ∈ qs, Terminal q) →
      Terminal (.root (.pure .one) [] qs)

/-- Folding finished threads in parallel yields, up to structural congruence, one finished
thread. -/
lemma process_congr_parAll_end (ps : List Proc)
    (h : ∀ p ∈ ps, TLLC.Process.Congruence p (.tm (.pure .one))) :
    TLLC.Process.Congruence (parAll (.tm (.pure .one)) ps) (.tm (.pure .one)) := by
  induction ps with
  | nil => exact ARS.Conv.refl
  | cons q ps ih =>
      rw [parAll_cons]
      exact ARS.conv_trans
        (process_congr_parAll_accumulator ps
          (ARS.conv_trans (process_congr_parallel_right (h q (by simp)))
            (ARS.conv1 TLLC.Process.CongrProc.end)))
        (ih (fun p hp => h p (by simp [hp])))

/-- Lemma 5.89 (Terminal): a terminal spawning tree flattens to the finished process, up to
structural congruence. -/
theorem Terminal.flatten_congr {t : Tree} (term : Terminal t) :
    TLLC.Process.Congruence t.flatten (.tm (.pure .one)) := by
  induction term with
  | root sub ih =>
      rename_i qs
      rw [Tree.flatten_root]
      have e : flattenBody (.pure .one) [] qs
          = parAll (.tm (.pure .one)) (flattenSubtrees qs) := by
        simp [flattenBody]
      rw [e]
      refine process_congr_parAll_end _ ?_
      intro p hp
      rw [flattenSubtrees_eq_map] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih q hq

end TLLC.Spawning
