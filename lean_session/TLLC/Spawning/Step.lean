import TLLC.Dynamic.EvalCtx
import TLLC.Dynamic.Occurs
import TLLC.Dynamic.Step
import TLLC.Spawning.Channel
import TLLC.Spawning.Tree

/-!
# Spawning-tree reduction

This file formalizes the spawning-tree operational semantics from report pages 28--31. The report
presents children and detached subtrees as finite sets. The raw Lean syntax uses lists, so rules
select an entry by decomposing a list as `l ++ selected :: r`, and set comprehensions such as
`{i | cᵢ ∈ FC(v)}` are represented by deterministic list partitions.

The self-dual process encoding uses one channel variable together with endpoint polarity supplied by
typing. At the spawning-tree level we still keep the report's two names for an edge: the channel used
by the parent (`c`) and the channel carried by the child node (`d`). Flattening ties these two names
together under one `Proc.nu`.

The report's Root-Unit and Node-Unit cleanup rules are deliberately left out of `Step`. They remove
finished detached subtrees, which corresponds to structural congruence after flattening rather than
a concrete process reduction. Terminality and process congruence handle that cleanup separately.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation

/-! ## Child-transfer helpers -/

/-- `c ∈ FC(m)` from the report, phrased with the existing occurrence counter. -/
def chanOccursIn : Chan → Term → Prop
  | .var_Chan x, m => Dynamic.occurs x m ≠ 0

/-- `c ∉ FC(m)` from the report. -/
def chanFreshIn : Chan → Term → Prop
  | .var_Chan x, m => Dynamic.occurs x m = 0

/-- A term that does not observe channel substitutions. This is stronger than the edge-local implicit
payload premise, but is often easier to provide directly. -/
def chanSubstInvariant (payload : Term) : Prop :=
  ∀ σ τ : Nat → Chan,
    payload[σ; Term.var_Term] = payload[τ; Term.var_Term]

/-- An implicit payload is untied from a parent/child edge when flattening may bind either endpoint
without changing the payload. This is the local replacement for the report's separation between
static channels and process endpoints. -/
def implicitPayload (c d : Chan) (payload : Term) : Prop :=
  ∀ σ : Nat → Chan,
    payload[bindEndpointAt 0 c; Term.var_Term][up_Chan_Chan σ; Term.var_Term] =
      payload[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ; Term.var_Term]

theorem chanSubstInvariant_implicitPayload {c d : Chan} {payload : Term}
    (invariant : chanSubstInvariant payload) :
    implicitPayload c d payload := by
  intro σ
  convert invariant
    (fun x => (bindEndpointAt 0 c x)[up_Chan_Chan σ])
    (fun x => (bindEndpointAt 0 d x)[up_Chan_Chan σ]) using 1 <;> asimp

theorem implicitPayload_symm {c d : Chan} {payload : Term}
    (implicit : implicitPayload c d payload) :
    implicitPayload d c payload := by
  intro σ
  exact (implicit σ).symm

/-- Split a child list into the children whose parent edge occurs in `m` and those whose edge does
not occur in `m`. The first component is the report's `I'`; the second is the complement. -/
def splitChildrenByTerm (m : Term) :
    List (Chan × Tree) → List (Chan × Tree) × List (Chan × Tree)
  | [] => ([], [])
  | p :: ps =>
      let rest := splitChildrenByTerm m ps
      match p.1 with
      | .var_Chan x =>
          if Dynamic.occurs x m = 0 then
            (rest.1, p :: rest.2)
          else
            (p :: rest.1, rest.2)

/-- Children after a fork: keep the children not mentioned by the fork body at the parent, and move
the mentioned children under the freshly spawned node. -/
def forkChildren (m : Term) (c d : Chan) (ms : List (Chan × Tree)) :
    List (Chan × Tree) :=
  let split := splitChildrenByTerm m ms
  split.2 ++ [(c, .node d (m[Chan.var_Chan; (Term.chan d)..]) split.1 [])]

/-- Children after an explicit send from the current node to a selected child. -/
def sendExChildren (v : Term) (c d : Chan) (N : Dynamic.EvalCtx)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (ms : List (Chan × Tree)) : List (Chan × Tree) :=
  let split := splitChildrenByTerm v ms
  let child' := Tree.node d (N.eval (.pure (.pair v (Term.chan d) .ex .L)))
    (ms' ++ split.1) qs'
  split.2 ++ [(c, child')]

/-- Children after an explicit receive by the current node from a selected child. -/
def recvExChildren (v : Term) (c d : Chan) (N : Dynamic.EvalCtx)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (ms : List (Chan × Tree)) : List (Chan × Tree) :=
  let split := splitChildrenByTerm v ms'
  let child' := Tree.node d (N.eval (.pure (Term.chan d))) split.2 qs'
  ms ++ split.1 ++ [(c, child')]

/-- Children after an implicit send from the current node to a selected child. Implicit payloads do not
carry channels, so no child subtrees move. -/
def sendImChildren (o : Term) (c d : Chan) (N : Dynamic.EvalCtx)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (ms : List (Chan × Tree)) : List (Chan × Tree) :=
  ms ++ [(c, .node d (N.eval (.pure (.pair o (Term.chan d) .im .L))) ms' qs')]

/-- Children after an implicit receive by the current node from a selected child. -/
def recvImChildren (_o : Term) (c d : Chan) (N : Dynamic.EvalCtx)
    (ms' : List (Chan × Tree)) (qs' : List Tree)
    (ms : List (Chan × Tree)) : List (Chan × Tree) :=
  ms ++ [(c, .node d (N.eval (.pure (Term.chan d))) ms' qs')]

/-- Children after forwarding the current node's parent channel through a selected child. The
selected child becomes the new node at this position, and the old current node becomes its child. -/
def forwardChildren (v : Term) (c d : Chan) (M : Dynamic.EvalCtx)
    (ms' : List (Chan × Tree)) (ms : List (Chan × Tree))
    (qs : List Tree) : List (Chan × Tree) :=
  let split := splitChildrenByTerm v ms
  let oldParent := Tree.node c (M.eval (.pure (Term.chan c))) split.2 qs
  ms' ++ split.1 ++ [(d, oldParent)]

/-! ## Spawning-tree single-step reduction -/

/-- Spawning-tree reduction from the companion report. -/
inductive Step : Tree → Tree → Prop where
  | rootFork {M : Dynamic.EvalCtx} {A m c d ms qs} :
      chanFreshIn c (M.eval (.fork A m)) →
      chanFreshIn d (M.eval (.fork A m)) →
      Step
        (.root (M.eval (.fork A m)) ms qs)
        (.root (M.eval (.pure (Term.chan c))) (forkChildren m c d ms) qs)
  | nodeFork {M : Dynamic.EvalCtx} {p A m c d ms qs} :
      chanFreshIn c (M.eval (.fork A m)) →
      chanFreshIn d (M.eval (.fork A m)) →
      Step
        (.node p (M.eval (.fork A m)) ms qs)
        (.node p (M.eval (.pure (Term.chan c))) (forkChildren m c d ms) qs)

  | rootWait {M N : Dynamic.EvalCtx} {c d l r ms' qs qs'} :
      Step
        (.root (M.eval (.close false (Term.chan c)))
          (l ++ (c, .node d (N.eval (.close true (Term.chan d))) ms' qs') :: r)
          qs)
        (.root (M.eval (.pure .one)) (l ++ r)
          (qs ++ [Tree.root (N.eval (.pure .one)) ms' qs']))
  | nodeWait {M N : Dynamic.EvalCtx} {p c d l r ms' qs qs'} :
      Step
        (.node p (M.eval (.close false (Term.chan c)))
          (l ++ (c, .node d (N.eval (.close true (Term.chan d))) ms' qs') :: r)
          qs)
        (.node p (M.eval (.pure .one)) (l ++ r)
          (qs ++ [Tree.root (N.eval (.pure .one)) ms' qs']))
  | rootClose {M N : Dynamic.EvalCtx} {c d l r ms' qs qs'} :
      Step
        (.root (M.eval (.close true (Term.chan c)))
          (l ++ (c, .node d (N.eval (.close false (Term.chan d))) ms' qs') :: r)
          qs)
        (.root (M.eval (.pure .one)) (l ++ r)
          (qs ++ [Tree.root (N.eval (.pure .one)) ms' qs']))
  | nodeClose {M N : Dynamic.EvalCtx} {p c d l r ms' qs qs'} :
      Step
        (.node p (M.eval (.close true (Term.chan c)))
          (l ++ (c, .node d (N.eval (.close false (Term.chan d))) ms' qs') :: r)
          qs)
        (.node p (M.eval (.pure .one)) (l ++ r)
          (qs ++ [Tree.root (N.eval (.pure .one)) ms' qs']))

  | rootSendEx {M N : Dynamic.EvalCtx}
      {v c d l r ms' qs qs'} :
      Dynamic.Val v →
      Step
        (.root (M.eval (.app (.send (Term.chan c) .ex) v .ex))
          (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r)
          qs)
        (.root (M.eval (.pure (Term.chan c)))
          (sendExChildren v c d N ms' qs' (l ++ r))
          qs)
  | nodeSendEx {M N : Dynamic.EvalCtx}
      {p v c d l r ms' qs qs'} :
      Dynamic.Val v →
      chanFreshIn p v →
      Step
        (.node p (M.eval (.app (.send (Term.chan c) .ex) v .ex))
          (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r)
          qs)
        (.node p (M.eval (.pure (Term.chan c)))
          (sendExChildren v c d N ms' qs' (l ++ r))
          qs)
  | rootRecvEx {M N : Dynamic.EvalCtx}
      {v c d l r ms' qs qs'} :
      Dynamic.Val v →
      Step
        (.root (M.eval (.recv (Term.chan c) .ex))
          (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .ex) v .ex)) ms' qs') :: r)
          qs)
        (.root (M.eval (.pure (.pair v (Term.chan c) .ex .L)))
          (recvExChildren v c d N ms' qs' (l ++ r))
          qs)
  | nodeRecvEx {M N : Dynamic.EvalCtx}
      {p v c d l r ms' qs qs'} :
      Dynamic.Val v →
      Step
        (.node p (M.eval (.recv (Term.chan c) .ex))
          (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .ex) v .ex)) ms' qs') :: r)
          qs)
        (.node p (M.eval (.pure (.pair v (Term.chan c) .ex .L)))
          (recvExChildren v c d N ms' qs' (l ++ r))
          qs)

  | rootSendIm {M N : Dynamic.EvalCtx}
      {o c d l r ms' qs qs'} :
      implicitPayload c d o →
      Step
        (.root (M.eval (.app (.send (Term.chan c) .im) o .im))
          (l ++ (c, .node d (N.eval (.recv (Term.chan d) .im)) ms' qs') :: r)
          qs)
        (.root (M.eval (.pure (Term.chan c)))
          (sendImChildren o c d N ms' qs' (l ++ r))
          qs)
  | nodeSendIm {M N : Dynamic.EvalCtx}
      {p o c d l r ms' qs qs'} :
      implicitPayload c d o →
      Step
        (.node p (M.eval (.app (.send (Term.chan c) .im) o .im))
          (l ++ (c, .node d (N.eval (.recv (Term.chan d) .im)) ms' qs') :: r)
          qs)
        (.node p (M.eval (.pure (Term.chan c)))
          (sendImChildren o c d N ms' qs' (l ++ r))
          qs)
  | rootRecvIm {M N : Dynamic.EvalCtx}
      {o c d l r ms' qs qs'} :
      implicitPayload c d o →
      Step
        (.root (M.eval (.recv (Term.chan c) .im))
          (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .im) o .im)) ms' qs') :: r)
          qs)
        (.root (M.eval (.pure (.pair o (Term.chan c) .im .L)))
          (recvImChildren o c d N ms' qs' (l ++ r))
          qs)
  | nodeRecvIm {M N : Dynamic.EvalCtx}
      {p o c d l r ms' qs qs'} :
      implicitPayload c d o →
      Step
        (.node p (M.eval (.recv (Term.chan c) .im))
          (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .im) o .im)) ms' qs') :: r)
          qs)
        (.node p (M.eval (.pure (.pair o (Term.chan c) .im .L)))
          (recvImChildren o c d N ms' qs' (l ++ r))
          qs)

  | nodeForward {M N : Dynamic.EvalCtx}
      {p v c d l r ms' qs qs'} :
      Dynamic.Val v →
      chanOccursIn p v →
      Step
        (.node p (M.eval (.app (.send (Term.chan c) .ex) v .ex))
          (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r)
          qs)
        (.node p (N.eval (.pure (.pair v (Term.chan d) .ex .L)))
          (forwardChildren v c d M ms' (l ++ r) qs)
          qs')

  | rootChild {m c child child' l r qs} :
      Step child child' →
      Step
        (.root m (l ++ (c, child) :: r) qs)
        (.root m (l ++ (c, child') :: r) qs)
  | nodeChild {p m c child child' l r qs} :
      Step child child' →
      Step
        (.node p m (l ++ (c, child) :: r) qs)
        (.node p m (l ++ (c, child') :: r) qs)
  | rootSubtree {m ms subtree subtree' l r} :
      Step subtree subtree' →
      Step
        (.root m ms (l ++ subtree :: r))
        (.root m ms (l ++ subtree' :: r))
  | nodeSubtree {p m ms subtree subtree' l r} :
      Step subtree subtree' →
      Step
        (.node p m ms (l ++ subtree :: r))
        (.node p m ms (l ++ subtree' :: r))

  | rootExpr {m m' ms qs} :
      Dynamic.Step m m' →
      Step (.root m ms qs) (.root m' ms qs)
  | nodeExpr {p m m' ms qs} :
      Dynamic.Step m m' →
      Step (.node p m ms qs) (.node p m' ms qs)

@[inherit_doc] scoped infix:50 " ⇛ₛ " => Step

/-- Multi-step spawning-tree reduction. -/
abbrev Red : Tree → Tree → Prop := ARS.Star Step

@[inherit_doc] scoped infix:50 " ⇛ₛ* " => Red

end TLLC.Spawning
