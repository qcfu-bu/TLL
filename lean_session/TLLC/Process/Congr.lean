import TLLC.Dynamic.Step
import TLLC.Dynamic.EvalCtx
import TLLC.Process.Typing

/-!
# Process reduction (self-dual single-channel encoding)

Port of `rocq_formal/proc_step.v`: structural congruence `≡` (`proc_CongrTerm` + its `conv` closure)
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

/-- The channel `CVar 0` as a m. -/
abbrev cvar (n : Nat) : Term := .chan (Chan.var_Chan n)

/-- Channel exchange substitution swapping the two innermost channels `0 ↔ 1` (Coq `exch`, here over
one channel per `res` instead of two endpoints). -/
abbrev exch : Nat → Chan := Dynamic.cexch

def under : Rlv → Rlv → Rlv
  | .im, _ => .im
  | .ex, r => r

inductive CongrTerm : Rlv → Term → Term → Prop where
  -- core
  | var {x r} :
    CongrTerm r (.var_Term x) (.var_Term x)
  | srt {s r} :
    CongrTerm r (.srt s) (.srt s)
  | pi {A A' B B' r1 r2 s} :
    CongrTerm .im A A' →
    CongrTerm .im B B' →
    CongrTerm r1 (.pi A B r2 s) (.pi A' B' r2 s)
  | lam {A A' m m' r1 r2 s} :
    CongrTerm .im A A' →
    CongrTerm r1 m m' →
    CongrTerm r1 (.lam A m r2 s) (.lam A' m' r2 s)
  | app {m m' n n' r1 r2} :
    CongrTerm r1 m m' →
    CongrTerm (under r1 r2) n n' →
    CongrTerm r1 (.app m n r2) (.app m' n' r2)
  | sig {A A' B B' r1 r2 s} :
    CongrTerm .im A A' →
    CongrTerm .im B B' →
    CongrTerm r1 (.sig A B r2 s) (.sig A' B' r2 s)
  | pair {m m' n n' r1 r2 s} :
    CongrTerm (under r1 r2) m m' →
    CongrTerm r1 n n' →
    CongrTerm r1 (.pair m n r2 s) (.pair m' n' r2 s)
  | proj {C C' m m' n n' r} :
    CongrTerm .im C C' →
    CongrTerm r m m' →
    CongrTerm r n n' →
    CongrTerm r (.proj C m n) (.proj C' m' n')
  | fix {A A' m m' r} :
    CongrTerm .im A A' →
    CongrTerm r m m' →
    CongrTerm r (.fix A m) (.fix A' m')
  -- data
  | unit {r} :
    CongrTerm r .unit .unit
  | one {r} :
    CongrTerm r .one .one
  | bool {r} :
    CongrTerm r .bool .bool
  | tt {r} :
    CongrTerm r .tt .tt
  | ff {r} :
    CongrTerm r .ff .ff
  | ite {A A' m m' n1 n1' n2 n2' r} :
    CongrTerm .im A A' →
    CongrTerm r m m' →
    CongrTerm r n1 n1' →
    CongrTerm r n2 n2' →
    CongrTerm r (.ite A m n1 n2) (.ite A' m' n1' n2')
  -- monadic
  | M {A A' r} :
    CongrTerm .im A A' →
    CongrTerm r (.M A) (.M A')
  | pure {m m' r} :
    CongrTerm r m m' →
    CongrTerm r (.pure m) (.pure m')
  | mlet {m m' n n' r} :
    CongrTerm r m m' →
    CongrTerm r n n' →
    CongrTerm r (.mlet m n) (.mlet m' n')
  -- session
  | proto {r} :
    CongrTerm r .proto .proto
  | stop {r} :
    CongrTerm r .stop .stop
  | act {b A A' B B' r1 r2} :
    CongrTerm .im A A' →
    CongrTerm .im B B' →
    CongrTerm r1 (.act b A B r2) (.act b A' B' r2)
  | ch {b A A' r} :
    CongrTerm .im A A' →
    CongrTerm r (.ch b A) (.ch b A')
  | chan_im {x y} :
    CongrTerm .im (.chan x) (.chan y)
  | chan_ex {x} :
    CongrTerm .ex (.chan x) (.chan x)
  | fork {A A' m m' r} :
    CongrTerm .im A A' →
    CongrTerm r m m' →
    CongrTerm r (.fork A m) (.fork A' m')
  | recv {m m' r1 r2} :
    CongrTerm r1 m m' →
    CongrTerm r1 (.recv m r2) (.recv m' r2)
  | send {m m' r1 r2} :
    CongrTerm r1 m m' →
    CongrTerm r1 (.send m r2) (.send m' r2)
  | close {b m m' r} :
    CongrTerm r m m' →
    CongrTerm r (.close b m) (.close b m')
  -- erasure
  | box {r} :
    CongrTerm r .box .box

lemma CongrTerm.refl (r : Rlv) (m : Term) : CongrTerm r m m := by
  induction m generalizing r with
  | var_Term x =>
      exact .var
  | srt s =>
      exact .srt
  | pi A B r2 s ihA ihB =>
      exact .pi (ihA .im) (ihB .im)
  | lam A m r2 s ihA ihm =>
      exact .lam (ihA .im) (ihm r)
  | app m n r2 ihm ihn =>
      exact .app (ihm r) (ihn (under r r2))
  | sig A B r2 s ihA ihB =>
      exact .sig (ihA .im) (ihB .im)
  | pair m n r2 s ihm ihn =>
      exact .pair (ihm (under r r2)) (ihn r)
  | proj A m n ihA ihm ihn =>
      exact .proj (ihA .im) (ihm r) (ihn r)
  | fix A m ihA ihm =>
      exact .fix (ihA .im) (ihm r)
  | unit =>
      exact .unit
  | one =>
      exact .one
  | bool =>
      exact .bool
  | tt =>
      exact .tt
  | ff =>
      exact .ff
  | ite A m n1 n2 ihA ihm ihn1 ihn2 =>
      exact .ite (ihA .im) (ihm r) (ihn1 r) (ihn2 r)
  | M A ihA =>
      exact .M (ihA .im)
  | pure m ihm =>
      exact .pure (ihm r)
  | mlet m n ihm ihn =>
      exact .mlet (ihm r) (ihn r)
  | proto =>
      exact .proto
  | stop =>
      exact .stop
  | act b A B r2 ihA ihB =>
      exact .act (ihA .im) (ihB .im)
  | ch b A ihA =>
      exact .ch (ihA .im)
  | chan c =>
      cases r
      · exact .chan_im
      · exact .chan_ex
  | fork A m ihA ihm =>
      exact .fork (ihA .im) (ihm r)
  | recv m r2 ihm =>
      exact .recv (ihm r)
  | send m r2 ihm =>
      exact .send (ihm r)
  | close b m ihm =>
      exact .close (ihm r)
  | box =>
      exact .box

lemma CongrTerm.crename {r : Rlv} {m m' : Term} (e : CongrTerm r m m') :
    ∀ ξ : Nat → Nat,
      CongrTerm r (m⟨ξ; (id : Nat → Nat)⟩) (m'⟨ξ; (id : Nat → Nat)⟩) := by
  induction e with
  | var =>
      intro ξ
      simpa using CongrTerm.var
  | srt =>
      intro ξ
      simpa using CongrTerm.srt
  | pi eA eB ihA ihB =>
      rename_i A A' B B' r1 r2 s
      intro ξ
      convert CongrTerm.pi (r1 := r1) (r2 := r2) (s := s) (ihA ξ) (ihB ξ) using 1
      all_goals try asimp
  | lam eA em ihA ihm =>
      rename_i A A' m m' r1 r2 s
      intro ξ
      convert CongrTerm.lam (r1 := r1) (r2 := r2) (s := s) (ihA ξ) (ihm ξ) using 1
      all_goals try asimp
  | app em en ihm ihn =>
      intro ξ
      convert CongrTerm.app (ihm ξ) (ihn ξ) using 1
  | sig eA eB ihA ihB =>
      rename_i A A' B B' r1 r2 s
      intro ξ
      convert CongrTerm.sig (r1 := r1) (r2 := r2) (s := s) (ihA ξ) (ihB ξ) using 1
      all_goals try asimp
  | pair em en ihm ihn =>
      intro ξ
      convert CongrTerm.pair (ihm ξ) (ihn ξ) using 1
  | proj eC em en ihC ihm ihn =>
      intro ξ
      convert CongrTerm.proj (ihC ξ) (ihm ξ) (ihn ξ) using 1
      all_goals try asimp
  | fix eA em ihA ihm =>
      intro ξ
      convert CongrTerm.fix (ihA ξ) (ihm ξ) using 1
      all_goals try asimp
  | unit =>
      intro ξ
      simpa using CongrTerm.unit
  | one =>
      intro ξ
      simpa using CongrTerm.one
  | bool =>
      intro ξ
      simpa using CongrTerm.bool
  | tt =>
      intro ξ
      simpa using CongrTerm.tt
  | ff =>
      intro ξ
      simpa using CongrTerm.ff
  | ite eA em en1 en2 ihA ihm ihn1 ihn2 =>
      intro ξ
      convert CongrTerm.ite (ihA ξ) (ihm ξ) (ihn1 ξ) (ihn2 ξ) using 1
      all_goals try asimp
  | M eA ihA =>
      intro ξ
      convert CongrTerm.M (ihA ξ) using 1
  | pure em ihm =>
      intro ξ
      convert CongrTerm.pure (ihm ξ) using 1
  | mlet em en ihm ihn =>
      intro ξ
      convert CongrTerm.mlet (ihm ξ) (ihn ξ) using 1
      all_goals try asimp
  | proto =>
      intro ξ
      simpa using CongrTerm.proto
  | stop =>
      intro ξ
      simpa using CongrTerm.stop
  | act eA eB ihA ihB =>
      rename_i b A A' B B' r1 r2
      intro ξ
      convert CongrTerm.act (b := b) (r1 := r1) (r2 := r2) (ihA ξ) (ihB ξ) using 1
      all_goals try asimp
  | ch eA ihA =>
      intro ξ
      convert CongrTerm.ch (ihA ξ) using 1
  | chan_im =>
      intro ξ
      simpa using CongrTerm.chan_im
  | chan_ex =>
      intro ξ
      simpa using CongrTerm.chan_ex
  | fork eA em ihA ihm =>
      intro ξ
      convert CongrTerm.fork (ihA ξ) (ihm ξ) using 1
      all_goals try asimp
  | recv em ihm =>
      intro ξ
      convert CongrTerm.recv (ihm ξ) using 1
  | send em ihm =>
      intro ξ
      convert CongrTerm.send (ihm ξ) using 1
  | close em ihm =>
      intro ξ
      convert CongrTerm.close (ihm ξ) using 1
  | box =>
      intro ξ
      simpa using CongrTerm.box

/-- One-step structural congruence (Coq `proc_CongrTerm`). -/
inductive CongrProc : Proc → Proc → Prop where
  | tm {m m'} :
    CongrTerm .ex m m' →
    CongrProc (.tm m) (.tm m')
  | par_sym {p q} :
    CongrProc (.par p q) (.par q p)
  | assoc {o p q} :
    CongrProc (.par o (.par p q)) (.par (.par o p) q)
  | scope {p q} :
    CongrProc (.par (.nu p) q) (.nu (.par p (q⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)))
  | exch {p} :
    CongrProc (.nu (.nu p)) (.nu (.nu (p[exch; Term.var_Term])))
  | par {p p' q q'} :
    CongrProc p p' →
    CongrProc q q' →
    CongrProc (.par p q) (.par p' q')
  | res {p p'} :
    CongrProc p p' →
    CongrProc (.nu p) (.nu p')
  | «end» {p} :
    CongrProc (.par p (.tm (.pure .one))) p

/-- Structural congruence (the conversion closure of `CongrProc`, Coq `≡`). -/
abbrev Congruence : Proc → Proc → Prop := ARS.Conv CongrProc

@[inherit_doc] scoped infix:50 " ≡ₚ " => Congruence
