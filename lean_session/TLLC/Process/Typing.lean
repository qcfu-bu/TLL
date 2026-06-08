import TLLC.Process.Context
import TLLC.Dynamic.SR
import TLLC.Dynamic.ProcWf

/-!
# Process typing (self-dual single-channel encoding)

Port of `coq_session/proc_type.v` (process typing `Θ ⊢ p`, here `Typed Θ p`, notation `Θ ⊩ p`),
adapted to the Lean **self-dual single-channel** scope restriction. The channel context `PCtx`, its
trinary `Slot`, the count-conserving merge `PMerge`, the leaf lowering `Realize`, and the empty
process context `PEmpty` all live in `Process.Context`. See [[tllc-process-channel-encoding]].

A leaf (`exp`) types a runtime term `m` in the dynamic context `Realize`d from a `both`-free process
context; `par` routes resources through `PMerge`; `scope` (`res p`) introduces one fresh self-dual
channel as a `both` slot.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Process typing (Coq `proc_type`, report `Θ ⊩ P`). -/
inductive Typed : PCtx → Proc → Prop where
  | exp {Θ Θ' m} :
    Realize Θ Θ' →
    Θ' ⨾ [] ⨾ [] ⊢ m : .M .unit →
    Typed Θ (.tm m)
  | par {Θ1 Θ2 Θ p q} :
    PMerge Θ1 Θ2 Θ →
    Typed Θ1 p →
    Typed Θ2 q →
    Typed Θ (.par p q)
  | res {Θ p A} :
    [] ⊢ A : .proto →
    Typed (.both A :: Θ) p →
    Typed Θ (.nu p)

@[inherit_doc] scoped notation:50 Θ:50 " ⊩ " p:51 => Typed Θ p

end TLLC.Process
