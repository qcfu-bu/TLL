import TLLC.Syntax
import TLLC.ARS

/-!
# Static reduction

Port of `coq_session/sta_step.v` (`sta_step`, notation `m ~> n`, and `sta_red := star sta_step`).

Because the Lean AST unifies Coq's implicit/explicit constructor pairs (`Pi0`/`Pi1` → `pi · · r ·`)
and `Close`/`Wait` (→ `close b ·`), each Coq rule pair collapses to one rule parameterized by the
`Rlv`/`Bool` tag (e.g. Coq `sta_step_pi0L` + `sta_step_pi1L` ↔ Lean `Step.piL`).
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Static single-step reduction (Coq `sta_step`, `m ~> n`). -/
inductive Step : Term → Term → Prop where
  -- core
  | piL {A A' B r s} :
    Step A A' →
    Step (.pi A B r s) (.pi A' B r s)
  | piR {A B B' r s} :
    Step B B' →
    Step (.pi A B r s) (.pi A B' r s)
  | lamL {A A' m r s} :
    Step A A' →
    Step (.lam A m r s) (.lam A' m r s)
  | lamR {A m m' r s} :
    Step m m' →
    Step (.lam A m r s) (.lam A m' r s)
  | appL {m m' n r} :
    Step m m' →
    Step (.app m n r) (.app m' n r)
  | appR {m n n' r} :
    Step n n' →
    Step (.app m n r) (.app m n' r)
  | beta {A m n r s} :
    Step (.app (.lam A m r s) n r) (m[Chan.var_Chan; n..])
  | sigL {A A' B r s} :
    Step A A' →
    Step (.sig A B r s) (.sig A' B r s)
  | sigR {A B B' r s} :
    Step B B' →
    Step (.sig A B r s) (.sig A B' r s)
  | pairL {m m' n r s} :
    Step m m' →
    Step (.pair m n r s) (.pair m' n r s)
  | pairR {m n n' r s} :
    Step n n' →
    Step (.pair m n r s) (.pair m n' r s)
  | projA {A A' m n} :
    Step A A' →
    Step (.proj A m n) (.proj A' m n)
  | projM {A m m' n} :
    Step m m' →
    Step (.proj A m n) (.proj A m' n)
  | projN {A m n n'} :
    Step n n' →
    Step (.proj A m n) (.proj A m n')
  | projE {A m1 m2 n r s} :
    Step (.proj A (.pair m1 m2 r s) n) (n[Chan.var_Chan; m2 .: m1 .: Term.var_Term])
  | fixL {A A' m} :
    Step A A' →
    Step (.fix A m) (.fix A' m)
  | fixR {A m m'} :
    Step m m' →
    Step (.fix A m) (.fix A m')
  | fixE {A m} :
    Step (.fix A m) (m[Chan.var_Chan; (Term.fix A m)..])
  -- data
  | iteA {A A' m n1 n2} :
    Step A A' →
    Step (.ite A m n1 n2) (.ite A' m n1 n2)
  | iteM {A m m' n1 n2} :
    Step m m' →
    Step (.ite A m n1 n2) (.ite A m' n1 n2)
  | iteN1 {A m n1 n1' n2} :
    Step n1 n1' →
    Step (.ite A m n1 n2) (.ite A m n1' n2)
  | iteN2 {A m n1 n2 n2'} :
    Step n2 n2' →
    Step (.ite A m n1 n2) (.ite A m n1 n2')
  | iteT {A n1 n2} :
    Step (.ite A .tt n1 n2) n1
  | iteF {A n1 n2} :
    Step (.ite A .ff n1 n2) n2
  -- monadic
  | M {A A'} :
    Step A A' →
    Step (.M A) (.M A')
  | pure {m m'} :
    Step m m' →
    Step (.pure m) (.pure m')
  | mletL {m m' n} :
    Step m m' →
    Step (.mlet m n) (.mlet m' n)
  | mletR {m n n'} :
    Step n n' →
    Step (.mlet m n) (.mlet m n')
  | mletE {m n} :
    Step (.mlet (.pure m) n) (n[Chan.var_Chan; m..])
  -- session
  | actL {b A A' B r} :
    Step A A' →
    Step (.act b A B r) (.act b A' B r)
  | actR {b A B B' r} :
    Step B B' →
    Step (.act b A B r) (.act b A B' r)
  | ch {b A A'} :
    Step A A' →
    Step (.ch b A) (.ch b A')
  | forkL {A A' m} :
    Step A A' →
    Step (.fork A m) (.fork A' m)
  | forkR {A m m'} :
    Step m m' →
    Step (.fork A m) (.fork A m')
  | recv {m m' r} :
    Step m m' →
    Step (.recv m r) (.recv m' r)
  | send {m m' r} :
    Step m m' →
    Step (.send m r) (.send m' r)
  | close {b m m'} :
    Step m m' →
    Step (.close b m) (.close b m')

@[inherit_doc] scoped infix:50 " ~> " => Step

/-- Static multi-step reduction (Coq `sta_red`, `m ~>* n`). -/
abbrev Red : Term → Term → Prop := ARS.Star Step

@[inherit_doc] scoped infix:50 " ~>* " => Red

end TLLC.Static
