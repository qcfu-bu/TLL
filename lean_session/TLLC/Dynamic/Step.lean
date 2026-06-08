import TLLC.Syntax
import TLLC.ARS

/-!
# Dynamic reduction

Port of `coq_session/dyn_step.v`: the call-by-value value/thunk predicates (`dyn_val`/`dyn_thunk`,
here the mutual `Val`/`Thunk`) and the dynamic single-step reduction `dyn_step` (`m ~>> n`, here
`Step`) with `dyn_red := star dyn_step` (`m ~>>* n`).

As elsewhere the unified AST collapses Coq's implicit/explicit constructor pairs via the `Rlv`/`Bool`
tag, but ONLY where the two rules are identical modulo the tag. Several CBV rules are genuinely
asymmetric (the explicit applications/betas/pairs carry a value premise the implicit ones lack, and
`App0`/`Pair0` reduce fewer subterms), so those stay split with an `Im`/`Ex` suffix:
* `appL` merges Coq `app0L`+`app1L`; `appR` is `app1R` (explicit only).
* `betaIm`/`betaEx` are `beta0`/`beta1` (the latter requires the argument to be a value).
* `pairR` merges `pair0R`+`pair1R`; `pairL` is `pair1L` (explicit only).
* `pairIm`/`pairEx` values are `pair0`/`pair1` (`pair1` requires both components to be values).
* `recv`/`send`/`close` merge the Coq `*0`/`*1` and `close`/`wait` pairs.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation

/-! ## Values and thunks (Coq `dyn_thunk` / `dyn_val`). -/

mutual
/-- Suspended monadic computations (Coq `dyn_thunk`). -/
inductive Thunk : Term → Prop where
  | mlet {m n} :
    Thunk m →
    Thunk (.mlet m n)
  | fork {A m} :
    Thunk (.fork A m)
  | recv {c i} :
    Thunk (.recv (.chan (Chan.var_Chan c)) i)
  | appSendIm {c m} :
    Thunk (.app (.send (.chan (Chan.var_Chan c)) .im) m .im)
  | appSendEx {c v} :
    Val v →
    Thunk (.app (.send (.chan (Chan.var_Chan c)) .ex) v .ex)
  | close {b c} :
    Thunk (.close b (.chan (Chan.var_Chan c)))

/-- Runtime values (Coq `dyn_val`). -/
inductive Val : Term → Prop where
  | var {x} :
    Val (.var_Term x)
  | lam {A m i s} :
    Val (.lam A m i s)
  | pairIm {m1 m2 s} :
    Val m2 →
    Val (.pair m1 m2 .im s)
  | pairEx {m1 m2 s} :
    Val m1 →
    Val m2 →
    Val (.pair m1 m2 .ex s)
  | one :
    Val .one
  | tt :
    Val .tt
  | ff :
    Val .ff
  | pure {v} :
    Val v →
    Val (.pure v)
  | chan {x} :
    Val (.chan (Chan.var_Chan x))
  | send {c i} :
    Val (.send (.chan (Chan.var_Chan c)) i)
  | thunk {m} :
    Thunk m →
    Val m
end

/-- Partial session redexes (Coq `dyn_partial`): a session operation blocked on a channel variable.
    These are exactly the non-`mlet` `Thunk` shapes — a `Thunk` is one of these inside an evaluation
    context (`Thunk.evalctx`). -/
inductive Partial : Term → Prop where
  | fork {A m} :
    Partial (.fork A m)
  | recv {c i} :
    Partial (.recv (.chan (Chan.var_Chan c)) i)
  | appSendIm {c m} :
    Partial (.app (.send (.chan (Chan.var_Chan c)) .im) m .im)
  | appSendEx {c v} :
    Val v →
    Partial (.app (.send (.chan (Chan.var_Chan c)) .ex) v .ex)
  | close {b c} :
    Partial (.close b (.chan (Chan.var_Chan c)))

/-! ## Single-step reduction (Coq `dyn_step`, `m ~>> n`). -/

/-- Dynamic call-by-value single-step reduction (Coq `dyn_step`). -/
inductive Step : Term → Term → Prop where
  -- core
  | appL {m m' n i} :
    Step m m' →
    Step (.app m n i) (.app m' n i)
  | appR {m n n'} :
    Step n n' →
    Step (.app m n .ex) (.app m n' .ex)
  | betaIm {A m n s} :
    Step (.app (.lam A m .im s) n .im) (m[Chan.var_Chan; n..])
  | betaEx {A m v s} :
    Val v →
    Step (.app (.lam A m .ex s) v .ex) (m[Chan.var_Chan; v..])
  | pairL {m m' n s} :
    Step m m' →
    Step (.pair m n .ex s) (.pair m' n .ex s)
  | pairR {m n n' i s} :
    Step n n' →
    Step (.pair m n i s) (.pair m n' i s)
  | projM {A m m' n} :
    Step m m' →
    Step (.proj A m n) (.proj A m' n)
  | projE {A m1 m2 n i s} :
    Val (.pair m1 m2 i s) →
    Step (.proj A (.pair m1 m2 i s) n) (n[Chan.var_Chan; m2 .: m1 .: Term.var_Term])
  | fixE {A m} :
    Step (.fix A m) (m[Chan.var_Chan; (Term.fix A m)..])
  -- data
  | iteM {A m m' n1 n2} :
    Step m m' →
    Step (.ite A m n1 n2) (.ite A m' n1 n2)
  | iteT {A n1 n2} :
    Step (.ite A .tt n1 n2) n1
  | iteF {A n1 n2} :
    Step (.ite A .ff n1 n2) n2
  -- monadic
  | pure {m m'} :
    Step m m' →
    Step (.pure m) (.pure m')
  | mletL {m m' n} :
    Step m m' →
    Step (.mlet m n) (.mlet m' n)
  | mletE {v n} :
    Val v →
    Step (.mlet (.pure v) n) (n[Chan.var_Chan; v..])
  -- session
  | recv {m m' i} :
    Step m m' →
    Step (.recv m i) (.recv m' i)
  | send {m m' i} :
    Step m m' →
    Step (.send m i) (.send m' i)
  | close {b m m'} :
    Step m m' →
    Step (.close b m) (.close b m')

@[inherit_doc] scoped infix:50 " ~>> " => Step

/-- Dynamic multi-step reduction (Coq `dyn_red`, `m ~>>* n`). -/
abbrev Red : Term → Term → Prop := ARS.Star Step

@[inherit_doc] scoped infix:50 " ~>>* " => Red

end TLLC.Dynamic
