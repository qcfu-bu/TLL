import TLLC.Syntax

/-!
# Spawning-tree channel utilities

Small channel helpers shared by spawning-tree flattening and the raw step relation.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation

/-! ## Endpoint binding -/

/-- Extract the de Bruijn index from a channel variable. -/
def chanIndex : Chan → Nat
  | .var_Chan x => x

@[simp] theorem chanIndex_var (x : Nat) : chanIndex (.var_Chan x) = x := rfl

/-- Channel substitution for moving under one fresh binder and tying one named endpoint to it. The
selected endpoint becomes the freshly bound channel `0`; all other free channels are weakened. -/
def bindEndpointAt (depth : Nat) (c : Chan) (x : Nat) : Chan :=
  if x = chanIndex c + depth then .var_Chan 0 else .var_Chan (x + 1)

end TLLC.Spawning
