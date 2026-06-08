import TLLC.Syntax

/-!
# Spawning trees

The spawning-tree formalism from the companion report records the parent/child topology of a
reachable process configuration. Each node carries the term currently running at that process, a
finite collection of child processes labelled by the channel used to communicate with that child,
and a finite collection of detached subtrees. Internal nodes additionally remember the channel used
to communicate with their parent.

The report presents child and subtree collections as finite sets. Here they are represented as
lists; the no-duplicate/freshness invariants belong to later validity judgments rather than to the
raw syntax.
-/

namespace TLLC.Spawning

/-- Spawning trees from the report's global-progress formalism. -/
inductive Tree where
  /-- A root process has no parent channel. -/
  | root (m : Term) (ms : List (Prod Chan Tree)) (ns : List Tree)
  /-- An internal process additionally carries the channel connecting it to its parent. -/
  | node (p : Chan) (m : Term) (ms : List (Chan × Tree)) (ns : List Tree)



end TLLC.Spawning
