From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_cren sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[global] Instance CSubst_term : CSubst term :=
  fix dummy (σ : cvar -> term) (m : term) : term :=
    let term_csubst := @csubst term dummy in
    match m with
    (* core *)
    | Var x => Var x
    | Sort s => Sort s
    | Pi0 A B s => Pi0 (term_csubst σ A) (term_csubst σ B) s
    | Pi1 A B s => Pi1 (term_csubst σ A) (term_csubst σ B) s
    | Lam0 A m s => Lam0 (term_csubst σ A) (term_csubst σ m) s
    | Lam1 A m s => Lam1 (term_csubst σ A) (term_csubst σ m) s
    | App0 m n => App0 (term_csubst σ m) (term_csubst σ n)
    | App1 m n => App1 (term_csubst σ m) (term_csubst σ n)
    | Sig0 A B s => Sig0 (term_csubst σ A) (term_csubst σ B) s
    | Sig1 A B s => Sig1 (term_csubst σ A) (term_csubst σ B) s
    | Pair0 m n s => Pair0 (term_csubst σ m) (term_csubst σ n) s
    | Pair1 m n s => Pair1 (term_csubst σ m) (term_csubst σ n) s
    | LetIn A m n => LetIn (term_csubst σ A) (term_csubst σ m) (term_csubst σ n)
    | Fix A m => Fix (term_csubst σ A) (term_csubst σ m)
    (* data *)
    | Unit => Unit | II => II | Bool => Bool | TT => TT | FF => FF
    | Ifte A m n1 n2 => 
      Ifte (term_csubst σ A) (term_csubst σ m) (term_csubst σ n1) (term_csubst σ n2)
    (* monadic *)
    | IO A => IO (term_csubst σ A)
    | Return m => Return (term_csubst σ m)
    | Bind m n => Bind (term_csubst σ m) (term_csubst σ n)
    (* session *)
    | Proto => Proto
    | Stop => Stop
    | Act0 r A B => Act0 r (term_csubst σ A) (term_csubst σ B)
    | Act1 r A B => Act1 r (term_csubst σ A) (term_csubst σ B)
    | Ch r A => Ch r (term_csubst σ A)
    | CVar x => σ x
    | Fork A m => Fork (term_csubst σ A) (term_csubst σ m)
    | Recv0 m => Recv0 (term_csubst σ m)
    | Recv1 m => Recv1 (term_csubst σ m)
    | Send0 m => Send0 (term_csubst σ m)
    | Send1 m => Send1 (term_csubst σ m)
    | Close m => Close (term_csubst σ m)
    | Wait m => Wait (term_csubst σ m)
    (* erasure *)
    | Box => Box
    end.

Definition cids x := CVar x.
Definition cup (σ : cvar -> term) := cids 0 .: σ >>> cren (+1).
Fixpoint cupn n σ := 
  match n with
  | O => σ
  | S n => cup (cupn n σ)
  end.

Lemma cupn_unfold n σ : cupn n.+1 σ = cup (cupn n σ).
Proof. eauto. Qed.

Lemma cup_cids : cup cids = cids.
Proof. f_ext. elim=>//. Qed.

Lemma term_csubst_cids m : csubst cids m = m. 
Proof with eauto.
  elim: m=>//=...
  all: solve[intros; autorew; eauto].
Qed.
  
Lemma term_csubst_cren_comp0 m σ ξ :
  cren ξ (csubst σ m) = csubst (σ >>> cren ξ) m.
Proof with eauto.
  elim: m σ ξ.
  all: try solve[intros; asimpl; autorew; eauto].
Qed.

Lemma term_csubst_cren_comp1 m σ :
  cren (+1) (csubst σ m) = csubst (cup σ) (cren (+1) m).
Proof with eauto.
  elim: m σ. all: try solve[intros; asimpl; autorew; eauto].
Qed.

Lemma term_csubst_cren_comp2 m x σ :
  csubst (CVar x .: σ) (cren (+1) m) = csubst σ m.
Proof with eauto.
  elim: m σ. all: try solve[intros; asimpl; autorew; eauto].
Qed.

Lemma term_cup_comp σ1 σ2 :
  cup σ1 >>> csubst (cup σ2) = cup (σ1 >>> csubst σ2).
Proof. 
  f_ext. move=>[|x]. by simpl. simpl.
  by rewrite term_csubst_cren_comp1.
Qed.

Lemma term_cupn_comp σ1 σ2 n :
  cupn n σ1 >>> csubst (cupn n σ2) = cupn n (σ1 >>> csubst σ2).
Proof with eauto.
  elim: n σ1 σ2... 
  move=>n ih σ1 σ2//=. rewrite term_cup_comp. f_equal...
Qed.

Lemma term_csubst_comp m σ1 σ2 :
  csubst σ2 (csubst σ1 m) = csubst (σ1 >>> csubst σ2) m.
Proof with eauto.
  elim: m σ1 σ2. all: try solve[intros; asimpl; autorew; eauto].
Qed.
