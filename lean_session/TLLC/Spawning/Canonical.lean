import TLLC.Spawning.Simulation

/-!
# Canonical forms of spawning trees

The auxiliary judgments and canonical-forms lemmas that characterize the state of a spawning tree
for the progress theorem (Lemma 5.92): `Terminal` with Lemma 5.89, and the thunk/poised
decomposition lemmas (Lemmas 5.90 and 5.91).

The `Terminal` judgment characterizes spawning trees with no further reductions: the root
computation has finished with `return ()`, all children have been cleaned up, and every detached
subtree is itself terminal. Lemma 5.89 shows that such trees flatten, up to process structural
congruence, to the single finished thread `⟨return ()⟩` — this is where the report's
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

/-! ## Thunk decomposition -/

/-- Lemma 5.90 (Thunk Evaluation Context): a thunk is a partial session redex — fork, receive,
send, close, or wait — inside an evaluation context. -/
theorem _root_.TLLC.Dynamic.Thunk.evalctx {τ : Term} (thunk : Thunk τ) :
    ∃ (M : EvalCtx) (m : Term), τ = M.eval m ∧ Dynamic.Partial m := by
  induction thunk using @TLLC.Dynamic.Thunk.rec (motive_2 := fun _ _ => True) with
  | mlet _ ih =>
      obtain ⟨M, m, rfl, part⟩ := ih
      exact ⟨.bnd M _, m, rfl, part⟩
  | fork => exact ⟨.hole, _, rfl, .fork⟩
  | recv => exact ⟨.hole, _, rfl, .recv⟩
  | appSendIm => exact ⟨.hole, _, rfl, .appSendIm⟩
  | appSendEx value _ => exact ⟨.hole, _, rfl, .appSendEx value⟩
  | close => exact ⟨.hole, _, rfl, .close⟩
  | _ => trivial

/-! ## Poised terms and trees -/

/-- A communication primitive blocked on channel `d` (report rules Poised-Explicit/Implicit-Recv,
Poised-Explicit/Implicit-Send, Poised-Close, and Poised-Wait): `Dynamic.Partial` restricted to one
channel, with the fork excluded because it relies on no channel. -/
inductive PoisedRedex (d : Chan) : Term → Prop where
  | recvEx :
      PoisedRedex d (.recv (.chan d) .ex)
  | recvIm :
      PoisedRedex d (.recv (.chan d) .im)
  | sendEx {v} :
      Dynamic.Val v →
      PoisedRedex d (.app (.send (.chan d) .ex) v .ex)
  | sendIm {o} :
      PoisedRedex d (.app (.send (.chan d) .im) o .im)
  | close :
      PoisedRedex d (.close true (.chan d))
  | wait :
      PoisedRedex d (.close false (.chan d))

/-- A term poised to communicate on channel `d` (report judgment `m Poised(d)`): a communication
primitive on `d` under a chain of monadic binds (report rule Poised-Bind). -/
inductive Poised (d : Chan) : Term → Prop where
  | redex {m} :
      PoisedRedex d m →
      Poised d m
  | mlet {m n} :
      Poised d m →
      Poised d (.mlet m n)

/-- Poisedness is preserved by plugging into an evaluation context (converse of Lemma 5.91). -/
lemma Poised.plug {d : Chan} {m : Term} (M : EvalCtx) (poised : Poised d m) :
    Poised d (M.eval m) := by
  induction M with
  | hole => exact poised
  | bnd M n ih => exact ih.mlet

/-- Lemma 5.91 (Poised Evaluation Context): a poised term is a communication primitive on its
channel inside an evaluation context. -/
theorem Poised.evalctx {d : Chan} {m : Term} (poised : Poised d m) :
    ∃ (M : EvalCtx) (m' : Term), m = M.eval m' ∧ PoisedRedex d m' := by
  induction poised with
  | redex h => exact ⟨.hole, _, rfl, h⟩
  | mlet _ ih =>
      obtain ⟨M, m', rfl, h⟩ := ih
      exact ⟨.bnd M _, m', rfl, h⟩

/-- A spawning tree poised to communicate on the channel `d` connected to its parent (report rule
Poised-Node). -/
inductive PoisedAt (d : Chan) : Tree → Prop where
  | node {m ms qs} :
      Poised d m →
      PoisedAt d (.node d m ms qs)

end TLLC.Spawning
