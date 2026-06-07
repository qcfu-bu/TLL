import TLLC.Dynamic.Context
import TLLC.Static.Typing

/-!
# Process-context well-formedness

The `ProcWf` predicate (Coq `proc_wf`) characterizes a well-formed *process* context `Θ`: every live
slot holds a channel typing `Ch r A :L` with `A` a closed protocol (`[] ⊢ A : .proto`), and every
other slot is null.

In the Coq development this is declared in `proc_type.v` (the Process layer), but `dyn_csubst.v`
(Dynamic layer) already depends on it, so we lift the *inductive* here to keep the dependency order
clean. Its metatheory lemmas (`dyn_empty_proc_wf`, `dyn_just_proc_wf`, `proc_wf_merge`,
`dyn_type_proc_wf`) are ported in the Process layer, which reuses this `ProcWf` rather than
redefining it.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- Well-formed process context (Coq `proc_wf`). -/
inductive ProcWf : Ctx → Prop where
  | nil :
    ProcWf []
  | ty {Θ r A} :
    ProcWf Θ →
    [] ⊢ A : .proto →
    ProcWf (.ch r A :L Θ)
  | null {Θ} :
    ProcWf Θ →
    ProcWf (□: Θ)

end TLLC.Dynamic
