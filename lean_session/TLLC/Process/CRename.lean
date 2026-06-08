import TLLC.Process.Typing
import TLLC.Dynamic.CRename

/-!
# Process channel renaming (self-dual single-channel encoding)

Port of `coq_session/proc_cren.v`: channel renaming preserves process typing
(`proc_crename` — here `Typed.crename`), with the strengthening/weakening corollaries
(`proc_cstrengthen`/`proc_cweaken`). Adapted to the **self-dual** encoding (see
[[tllc-process-channel-encoding]]): the process context is the trinary `PCtx`, so the Coq's
`dyn_ctx_cren` agreement is replaced by `PCtxCRen`, a channel-renaming agreement over `PCtx`.

The headline lemma reuses the dynamic `Dynamic.Typed.crename` at each leaf through
`PCtxCRen.toDynamic`; `PCtxCRen.pctxSingle` only preserves the leaf-safe `PCtxSingle` predicate. The `par`
case routes through `PCtxCRen.merge` (the count-conserving analogue of `dyn_ctx_cren_merge`), and the
`scope` case renames the `both A` slot using the protocol typing `[] ⊢ A : .proto` carried directly by
`Process.Typed.res`.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Channel-renaming agreement on the process context `Θ` (the self-dual analogue of
    `Dynamic.CtxCRen`, Coq `dyn_ctx_cren`). -/
inductive PCtxCRen : (Nat → Nat) → PCtx → PCtx → Prop where
  | O {Θ} :
    PCtxCRen (id : Nat → Nat) Θ Θ
  | one {ξ r A Θ Θ'} :
    [] ⊢ A : .proto →
    PCtxCRen ξ Θ Θ' →
    PCtxCRen (upRen_Chan_Chan ξ) (.one r A :: Θ) (.one r (A⟨ξ; (id : Nat → Nat)⟩) :: Θ')
  | both {ξ A Θ Θ'} :
    [] ⊢ A : .proto →
    PCtxCRen ξ Θ Θ' →
    PCtxCRen (upRen_Chan_Chan ξ) (.both A :: Θ) (.both (A⟨ξ; (id : Nat → Nat)⟩) :: Θ')
  | n {ξ Θ Θ'} :
    PCtxCRen ξ Θ Θ' →
    PCtxCRen (upRen_Chan_Chan ξ) (.none :: Θ) (.none :: Θ')
  | plus {ξ Θ Θ'} :
    PCtxCRen ξ Θ Θ' →
    PCtxCRen (funcomp Nat.succ ξ) Θ (.none :: Θ')
  | minus {ξ Θ Θ'} :
    PCtxCRen ξ Θ Θ' →
    PCtxCRen (funcomp ξ (· - 1)) (.none :: Θ) Θ'

/-! ## Bridge to the dynamic channel renaming. -/

/-- A process-context channel renaming is the dynamic PCtx channel-renaming agreement. -/
lemma PCtxCRen.toDynamic {ξ Θ Θ'} (agr : PCtxCRen ξ Θ Θ') : Dynamic.CtxCRen ξ Θ Θ' := by
  induction agr with
  | O => exact .O
  | one tyA _ ih => exact .one tyA ih
  | both tyA _ ih => exact .both tyA ih
  | n _ ih => exact .n ih
  | plus _ ih => exact .plus ih
  | minus _ ih => exact .minus ih

/-- A process-context channel renaming preserves leaf-safety. -/
lemma PCtxCRen.pctxSingle {ξ Θ Θ'} (agr : PCtxCRen ξ Θ Θ') :
    PCtxSingle Θ → PCtxSingle Θ' := by
  induction agr with
  | O => intro rea; exact rea
  | one tyA _ ih =>
    intro rea
    cases rea with
    | one rea0 =>
      exact .one (ih rea0)
  | both _ _ _ =>
    intro rea; cases rea
  | n _ ih =>
    intro rea
    cases rea with
    | none rea0 =>
      exact .none (ih rea0)
  | plus _ ih =>
    intro rea
    exact .none (ih rea)
  | minus _ ih =>
    intro rea
    cases rea with
    | none rea0 =>
      exact ih rea0

/-! ## Compatibility with merge. -/

/-- Channel renaming is compatible with the process-context merge (the count-conserving analogue of
    `dyn_ctx_cren_merge`). -/
lemma PCtxCRen.merge {ξ Θ Θ'} (agr : PCtxCRen ξ Θ Θ') :
    ∀ {Θ1 Θ2}, PMerge Θ1 Θ2 Θ →
    ∃ Θ1' Θ2', PMerge Θ1' Θ2' Θ' ∧ PCtxCRen ξ Θ1 Θ1' ∧ PCtxCRen ξ Θ2 Θ2' := by
  induction agr with
  | O => intro Θ1 Θ2 mrg; exact ⟨Θ1, Θ2, mrg, .O, .O⟩
  | one tyA _ ih =>
    intro Θ1 Θ2 mrg
    cases mrg with
    | oneL mrg0 =>
      obtain ⟨Δ1', Δ2', mrg', a1, a2⟩ := ih mrg0
      exact ⟨_, _, .oneL mrg', .one tyA a1, .n a2⟩
    | oneR mrg0 =>
      obtain ⟨Δ1', Δ2', mrg', a1, a2⟩ := ih mrg0
      exact ⟨_, _, .oneR mrg', .n a1, .one tyA a2⟩
  | both tyA _ ih =>
    intro Θ1 Θ2 mrg
    cases mrg with
    | bothL mrg0 =>
      obtain ⟨Δ1', Δ2', mrg', a1, a2⟩ := ih mrg0
      exact ⟨_, _, .bothL mrg', .both tyA a1, .n a2⟩
    | bothR mrg0 =>
      obtain ⟨Δ1', Δ2', mrg', a1, a2⟩ := ih mrg0
      exact ⟨_, _, .bothR mrg', .n a1, .both tyA a2⟩
    | split mrg0 =>
      obtain ⟨Δ1', Δ2', mrg', a1, a2⟩ := ih mrg0
      exact ⟨_, _, .split mrg', .one tyA a1, .one tyA a2⟩
  | n _ ih =>
    intro Θ1 Θ2 mrg
    cases mrg with
    | none mrg0 =>
      obtain ⟨Δ1', Δ2', mrg', a1, a2⟩ := ih mrg0
      exact ⟨_, _, .none mrg', .n a1, .n a2⟩
  | plus _ ih =>
    intro Θ1 Θ2 mrg
    obtain ⟨Θ1', Θ2', mrg', a1, a2⟩ := ih mrg
    exact ⟨.none :: Θ1', .none :: Θ2', .none mrg', .plus a1, .plus a2⟩
  | minus _ ih =>
    intro Θ1 Θ2 mrg
    cases mrg with
    | none mrg0 =>
      obtain ⟨Δ1', Δ2', mrg', a1, a2⟩ := ih mrg0
      exact ⟨Δ1', Δ2', mrg', .minus a1, .minus a2⟩

/-! ## Channel renaming preserves process typing. -/

/-- Channel renaming preserves process typing (Coq `proc_crename`). -/
lemma Typed.crename {Θ p} (ty : Θ ⊩ p) :
    ∀ {Θ' ξ}, PCtxCRen ξ Θ Θ' → Θ' ⊩ p⟨ξ; (id : Nat → Nat)⟩ := by
  induction ty with
  | @exp Θ m rea tym =>
    intro Θ' ξ agr
    asimp
    exact .exp (agr.pctxSingle rea) (tym.crename agr.toDynamic)
  | @par Θ1 Θ2 Θ p q mrg _ _ ihp ihq =>
    intro Θ' ξ agr
    obtain ⟨Θ1', Θ2', mrg', agr1, agr2⟩ := agr.merge mrg
    asimp
    exact .par mrg' (ihp agr1) (ihq agr2)
  | @res Θ p A tyA _ ih =>
    intro Θ' ξ agr
    asimp
    exact .res (Static.Typed.crename tyA ξ) (ih (.both tyA agr))

/-- Channel strengthening (Coq `proc_cstrengthen`). -/
lemma Typed.cstrengthen {Θ p}
    (ty : (Slot.none :: Θ) ⊩ p⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) : Θ ⊩ p := by
  have h := ty.crename (Θ' := Θ) (ξ := funcomp (id : Nat → Nat) (· - 1)) (.minus .O)
  have hmap : funcomp ((· - 1) : Nat → Nat) ((· + 1) : Nat → Nat) = (id : Nat → Nat) := by
    funext x; simp only [funcomp, id]; omega
  rw [show (p⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨funcomp (id : Nat → Nat) (· - 1);
        (id : Nat → Nat)⟩ = p from by
        asimp; rw [hmap]; asimp] at h
  exact h

/-- Channel weakening (Coq `proc_cweaken`). -/
lemma Typed.cweaken {Θ p} (ty : Θ ⊩ p) :
    (Slot.none :: Θ) ⊩ p⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ := by
  have h := ty.crename (.plus .O)
  rw [show p⟨funcomp Nat.succ (id : Nat → Nat); (id : Nat → Nat)⟩
        = p⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ from by asimp] at h
  exact h

end TLLC.Process
