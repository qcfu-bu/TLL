import TLLC.Process.CRename
import TLLC.Dynamic.Occurs

/-!
# Process channel occurrences (self-dual single-channel encoding)

Port of `coq_session/proc_occurs.v`: the channel-occurrence count `proc_occurs` on processes and its
typing characterisation, adapted to the self-dual encoding (see [[tllc-process-channel-encoding]]).

Because each `nu` binds ONE self-dual channel (not Coq's two endpoints), the `res` case shifts the
index by `+1` (Coq used `i.+2`). The typing characterisation generalises Coq's boolean pair
`proc_type_occurs0`/`proc_type_occurs1`: in the trinary context a `both A` slot carries *two* live
endpoints, so a channel can occur `0`, `1`, or `2` times. The unified statement
`Typed.occursCount` (`Θ ⊩ p → proc_occurs i p = pcount Θ i`) counts endpoints via `pcount`
(`none ↦ 0`, `one ↦ 1`, `both ↦ 2`); the Coq `occurs0`/`occurs1` are recovered as the corollaries
`Typed.procOccurs0`/`procOccurs1`. The renaming corollary `procOccurs_cren` (Coq `proc_occurs_iren`)
is, as in the dynamic file, a pure fact about `proc_occurs`/`cren` (the typing premise is vestigial).
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- The occurrence count of channel `i` in a process (Coq `proc_occurs`; `res` shifts by `+1`). -/
def procOccurs (i : Nat) : Proc → Nat
  | .tm m => occurs i m
  | .par p q => procOccurs i p + procOccurs i q
  | .nu p => procOccurs (i + 1) p

/-- The number of live endpoints of channel `i` in a process context (`none ↦ 0`, `one ↦ 1`,
    `both ↦ 2`). The self-dual analogue of Coq's boolean `cvar_pos`. -/
def pcount : PCtx → Nat → Nat
  | [], _ => 0
  | .none :: _, 0 => 0
  | .one _ _ :: _, 0 => 1
  | .both _ :: _, 0 => 2
  | _ :: Θ, i + 1 => pcount Θ i

/-- Endpoint counts are additive over the process-context merge (the count-conserving heart: `split`
    realises `2 = 1 + 1`). -/
lemma PMerge.pcount {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ i, pcount Θ i = pcount Θ1 i + pcount Θ2 i := by
  induction mrg with
  | nil => intro i; rfl
  | none _ ih => intro i; cases i with | zero => rfl | succ i => exact ih i
  | oneL _ ih => intro i; cases i with | zero => rfl | succ i => exact ih i
  | oneR _ ih => intro i; cases i with | zero => rfl | succ i => exact ih i
  | bothL _ ih => intro i; cases i with | zero => rfl | succ i => exact ih i
  | bothR _ ih => intro i; cases i with | zero => rfl | succ i => exact ih i
  | split _ ih => intro i; cases i with | zero => rfl | succ i => exact ih i

/-- A leaf lowering identifies the endpoint count (`0` or `1`, since a realised context has no
    `both`) with the dynamic channel positivity. -/
lemma PCtxSingle.cvarPos {Θ} (rea : PCtxSingle Θ) :
    ∀ i, (pcount Θ i = 0 ∧ CvarPos Θ i false) ∨ (pcount Θ i = 1 ∧ CvarPos Θ i true) := by
  induction rea with
  | nil => intro i; exact .inl ⟨rfl, .nil⟩
  | none _ ih =>
    intro i
    cases i with
    | zero => exact .inl ⟨rfl, .none⟩
    | succ i => rcases ih i with ⟨e, pos⟩ | ⟨e, pos⟩
                exacts [.inl ⟨e, .cons pos⟩, .inr ⟨e, .cons pos⟩]
  | one _ ih =>
    intro i
    cases i with
    | zero => exact .inr ⟨rfl, .one⟩
    | succ i => rcases ih i with ⟨e, pos⟩ | ⟨e, pos⟩
                exacts [.inl ⟨e, .cons pos⟩, .inr ⟨e, .cons pos⟩]

/-- The occurrence count of a channel equals its endpoint count in the process context (the
    self-dual generalisation of Coq `proc_type_occurs0`/`proc_type_occurs1`). -/
lemma Typed.occursCount {Θ p} (ty : Θ ⊩ p) : ∀ i, procOccurs i p = pcount Θ i := by
  induction ty with
  | @exp Θ m rea tym =>
    intro i
    show occurs i m = pcount Θ i
    rcases TLLC.Process.PCtxSingle.cvarPos rea i with ⟨e, pos⟩ | ⟨e, pos⟩
    · rw [e]; exact tym.occurs0 pos
    · rw [e]; exact tym.occurs1 pos
  | @par Θ1 Θ2 Θ p q mrg _ _ ihp ihq =>
    intro i
    show procOccurs i p + procOccurs i q = pcount Θ i
    rw [ihp i, ihq i, TLLC.Process.PMerge.pcount mrg i]
  | @res Θ p A _ _ ih =>
    intro i
    show procOccurs (i + 1) p = pcount Θ i
    rw [ih (i + 1)]; rfl

/-- If channel `i` has no endpoint in `Θ`, it does not occur in `p` (Coq `proc_type_occurs0`). -/
lemma Typed.procOccurs0 {Θ p i} (ty : Θ ⊩ p) (h : pcount Θ i = 0) : procOccurs i p = 0 := by
  rw [ty.occursCount i, h]

/-- If channel `i` has exactly one endpoint in `Θ`, it occurs once in `p` (Coq
    `proc_type_occurs1`). -/
lemma Typed.procOccurs1 {Θ p i} (ty : Θ ⊩ p) (h : pcount Θ i = 1) : procOccurs i p = 1 := by
  rw [ty.occursCount i, h]

/-! ## Channel renaming with `i` out of range. -/

/-- A channel-renamed process whose renaming omits `i` has `i`-occurrence `0` (the self-dual analogue
    of `Dynamic.occurs_cren`; `proc_occurs_iren`'s typing premise is vestigial). -/
lemma procOccurs_cren {i : Nat} {ξ : Nat → Nat} (ir : Iren i ξ) (p : Proc) :
    procOccurs i (p⟨ξ; (id : Nat → Nat)⟩) = 0 := by
  induction p generalizing i ξ with
  | tm m =>
    show occurs i (m⟨ξ; (id : Nat → Nat)⟩) = 0
    exact occurs_cren ir m
  | par p q ihp ihq =>
    show procOccurs i (p⟨ξ; (id : Nat → Nat)⟩) + procOccurs i (q⟨ξ; (id : Nat → Nat)⟩) = 0
    rw [ihp ir, ihq ir]
  | nu p ih =>
    show procOccurs (i + 1) (p⟨upRen_Chan_Chan ξ; (id : Nat → Nat)⟩) = 0
    exact ih ir.upren

/-- If a process is the image of a channel renaming whose range omits `i`, then `i` does not occur in
    it (Coq `proc_occurs_iren`). -/
lemma Typed.procOccurs_iren {Θ i ξ} {p : Proc}
    (_ : Θ ⊩ p⟨ξ; (id : Nat → Nat)⟩) (ir : Iren i ξ) :
    procOccurs i (p⟨ξ; (id : Nat → Nat)⟩) = 0 :=
  procOccurs_cren ir p

end TLLC.Process
