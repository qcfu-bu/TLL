import TLLC.Process.Congr

/-!
# Process reduction (self-dual single-channel encoding)

Port of `rocq_formal/proc_step.v`: structural congruence `≡` (`proc_congr0` + its `conv` closure)
and process reduction `⇛` (`proc_step`), adapted to the self-dual single-channel encoding (see
[[tllc-process-channel-encoding]]).

Following rocq_formal, the session redexes sit inside an **evaluation context** `N.eval (redex)`
(`Dynamic.EvalCtx`) rather than at the head of a single `Bind`. Because each `res` binds ONE self-dual
channel (both communicating threads reference `CVar 0`, with polarity supplied by typing), the Coq's
symmetric rule pairs collapse: `proc_step_com0`/`com0i`, `com1`/`com1i`, and `end`/`endi` each become
ONE rule, the `exch` congruence swaps just channels `0 ↔ 1`, and the channel shifts are `±1` (Coq used
`±2`; eval contexts are renamed by `EvalCtx.cren`).
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Process reduction (Coq `proc_step`, `p ⇛ q`). -/
inductive Step : Proc → Proc → Prop where
  -- monadic
  | exp {m m'} :
    m ~>> m' →
    Step (.tm m) (.tm m')
  -- session
  | fork {A m m'} {N N' : EvalCtx} :
    m' = m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ →
    N' = N.cren ((· + 1) : Nat → Nat) →
    Step (.tm (N.eval (.fork A m)))
      (.nu (.par (.tm (N'.eval (.pure (cvar 0)))) (.tm (m'[Chan.var_Chan; (cvar 0)..]))))
  | comIm {M N : EvalCtx} {m} :
    Step (.nu (.par (.tm (M.eval (.app (.send (cvar 0) .im) m .im))) (.tm (N.eval (.recv (cvar 0) .im)))))
      (.nu (.par (.tm (M.eval (.pure (cvar 0)))) (.tm (N.eval (.pure (.pair m (cvar 0) .im .L))))))
  | comEx {M N : EvalCtx} {v} :
    Val v →
    Step (.nu (.par (.tm (M.eval (.app (.send (cvar 0) .ex) v .ex))) (.tm (N.eval (.recv (cvar 0) .ex)))))
      (.nu (.par (.tm (M.eval (.pure (cvar 0)))) (.tm (N.eval (.pure (.pair v (cvar 0) .ex .L))))))
  | «end» {M N M' N' : EvalCtx} :
    M' = M.cren ((· - 1) : Nat → Nat) →
    N' = N.cren ((· - 1) : Nat → Nat) →
    Step (.nu (.par (.tm (M.eval (.close true (cvar 0)))) (.tm (N.eval (.close false (cvar 0))))))
      (.par (.tm (M'.eval (.pure .one))) (.tm (N'.eval (.pure .one))))
  -- congruence
  | par {o p q} :
    Step p q →
    Step (.par o p) (.par o q)
  | res {p q} :
    Step p q →
    Step (.nu p) (.nu q)
  | congr {p p' q q'} :
    p ≡ₚ p' →
    Step p' q' →
    q' ≡ₚ q →
    Step p q

@[inherit_doc] scoped infix:50 " ⇛ " => Step

/-- Multi-step process reduction. -/
abbrev Red : Proc → Proc → Prop := ARS.Star Process.Step

@[inherit_doc] scoped infix:50 " ⇛* " => Red

end TLLC.Process
