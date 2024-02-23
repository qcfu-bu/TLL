From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_cren sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint term_csubst (m : term) (σ : cvar -> term) :=
  match m with
  (* core *)
  | Var x => Var x
  | Sort s => Sort s
  | Pi0 A B s => Pi0 (term_csubst A σ) (term_csubst B σ) s
  | Pi1 A B s => Pi1 (term_csubst A σ) (term_csubst B σ) s
  | Lam0 A m s => Lam0 (term_csubst A σ) (term_csubst m σ) s
  | Lam1 A m s => Lam1 (term_csubst A σ) (term_csubst m σ) s
  | App0 m n => App0 (term_csubst m σ) (term_csubst n σ)
  | App1 m n => App1 (term_csubst m σ) (term_csubst n σ)
  | Sig0 A B s => Sig0 (term_csubst A σ) (term_csubst B σ) s
  | Sig1 A B s => Sig1 (term_csubst A σ) (term_csubst B σ) s
  | Pair0 m n s => Pair0 (term_csubst m σ) (term_csubst n σ) s
  | Pair1 m n s => Pair1 (term_csubst m σ) (term_csubst n σ) s
  | LetIn A m n => LetIn (term_csubst A σ) (term_csubst m σ) (term_csubst n σ)
  | Fix A m => Fix (term_csubst A σ) (term_csubst m σ)
  (* data *)
  | Unit => Unit
  | II => II
  | Bool => Bool
  | TT => TT
  | FF => FF
  | Ifte A m n1 n2 => 
    Ifte 
      (term_csubst A σ) 
      (term_csubst m σ) 
      (term_csubst n1 σ) 
      (term_csubst n2 σ)
  (* monadic *)
  | IO A => IO (term_csubst A σ)
  | Return m => Return (term_csubst m σ)
  | Bind m n => Bind (term_csubst m σ) (term_csubst n σ)
  (* session *)
  | Proto => Proto
  | Stop => Stop
  | Act0 r A B => Act0 r (term_csubst A σ) (term_csubst B σ)
  | Act1 r A B => Act1 r (term_csubst A σ) (term_csubst B σ)
  | Ch r A => Ch r (term_csubst A σ)
  | CVar x => σ x
  | Fork A m => Fork (term_csubst A σ) (term_csubst m σ)
  | Recv0 m => Recv0 (term_csubst m σ)
  | Recv1 m => Recv1 (term_csubst m σ)
  | Send0 m => Send0 (term_csubst m σ)
  | Send1 m => Send1 (term_csubst m σ)
  | Close m => Close (term_csubst m σ)
  | Wait m => Wait (term_csubst m σ)
  (* erasure *)
  | Box => Box
  end.

Definition cids x := CVar x.
Definition upp (σ : cvar -> term) := cids 0 .: σ >>> term_cren^~ (+1).

Lemma upp_cids : upp cids = cids.
Proof. f_ext. elim=>//. Qed.

Lemma term_csubst_cids m : term_csubst m cids = m. 
Proof with eauto.
  elim: m=>//=...
  all: solve[intros; autorew; eauto].
Qed.
  
Lemma term_csubst_cren_comp0 m σ ξ :
  term_cren (term_csubst m σ) ξ = term_csubst m (σ >>> term_cren^~ ξ).
Proof with eauto.
  elim: m σ ξ.
  all: try solve[intros; asimpl; autorew; eauto].
Qed.

Lemma term_csubst_cren_comp1 m σ :
  term_cren (term_csubst m σ) (+1) = term_csubst (term_cren m (+1)) (upp σ).
Proof with eauto.
  elim: m σ. all: try solve[intros; asimpl; autorew; eauto].
Qed.

Lemma term_csubst_cren_comp2 m x σ :
  term_csubst (term_cren m (+1)) (CVar x .: σ) = term_csubst m σ.
Proof with eauto.
  elim: m σ. all: try solve[intros; asimpl; autorew; eauto].
Qed.
