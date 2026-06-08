import TLLC.Process.Step
import TLLC.Spawning.Flatten
import TLLC.Spawning.Step

/-!
# Spawning-tree simulation

Lemma 5.86 for the productive spawning-tree step relation. Finished-subtree cleanup is not part of
`Step`; terminality and process structural congruence handle it separately.
-/

namespace TLLC.Spawning

lemma process_step_parallel_left {p q r : Proc}
    (step : TLLC.Process.Step p q) :
    TLLC.Process.Step (.par p r) (.par q r) := by
  exact TLLC.Process.Step.congr
    (ARS.conv1 TLLC.Process.Congr.par_sym)
    (TLLC.Process.Step.par (o := r) step)
    (ARS.conv1 TLLC.Process.Congr.par_sym)

lemma process_step_parAll_accumulator {p q : Proc} (processes : List Proc)
    (step : TLLC.Process.Step p q) :
    TLLC.Process.Step (parAll p processes) (parAll q processes) := by
  induction processes generalizing p q with
  | nil =>
      simpa using step
  | cons process processes ih =>
      simpa [parAll] using
        ih (p := .par p process) (q := .par q process)
          (process_step_parallel_left (r := process) step)

lemma process_step_parAll_list {body old new : Proc} (before after : List Proc)
    (step : TLLC.Process.Step old new) :
    TLLC.Process.Step
      (parAll body (before ++ old :: after))
      (parAll body (before ++ new :: after)) := by
  induction before generalizing body with
  | nil =>
      simpa [parAll] using
        process_step_parAll_accumulator after
          (TLLC.Process.Step.par (o := body) step)
  | cons process before ih =>
      simpa [parAll, List.cons_append] using
        ih (body := .par body process)

lemma process_step_flattenSubtrees_list {body : Proc} {subtree subtree' : Tree}
    (before after : List Tree)
    (step : TLLC.Process.Step subtree.flatten subtree'.flatten) :
    TLLC.Process.Step
      (parAll body (flattenSubtrees (before ++ subtree :: after)))
      (parAll body (flattenSubtrees (before ++ subtree' :: after))) := by
  simpa [flattenSubtrees_eq_map, List.map_append] using
    process_step_parAll_list (body := body)
      (before.map Tree.flatten) (after.map Tree.flatten) step

/-- Lemma 5.86 for productive spawning-tree steps. -/
theorem simulation {p q : Tree}
    (typed : Typed p ∨ ∃ r A, TypedAt r A p)
    (step : Step p q) :
    TLLC.Process.Step p.flatten q.flatten := by
  induction step with
  | rootFork => sorry
  | nodeFork => sorry
  | rootWait => sorry
  | nodeWait => sorry
  | rootClose => sorry
  | nodeClose => sorry
  | rootSendEx => sorry
  | nodeSendEx => sorry
  | rootRecvEx => sorry
  | nodeRecvEx => sorry
  | rootSendIm => sorry
  | nodeSendIm => sorry
  | rootRecvIm => sorry
  | nodeRecvIm => sorry
  | nodeForward => sorry
  | rootChild => sorry
  | nodeChild => sorry
  | rootSubtree => sorry
  | nodeSubtree => sorry
  | rootExpr => sorry
  | nodeExpr => sorry

end TLLC.Spawning
