From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "( - n )" := (subn^~ n).

Fixpoint term_cren (m : term) (ξ : cvar -> cvar) : term :=
  match m with
  (* core *)
  | Var x => Var x
  | Sort s => Sort s
  | Pi0 A B s => Pi0 (term_cren A ξ) (term_cren B ξ) s
  | Pi1 A B s => Pi1 (term_cren A ξ) (term_cren B ξ) s
  | Lam0 A m s => Lam0 (term_cren A ξ) (term_cren m ξ) s
  | Lam1 A m s => Lam1 (term_cren A ξ) (term_cren m ξ) s
  | App m n => App (term_cren m ξ) (term_cren n ξ)
  | Sig0 A B s => Sig0 (term_cren A ξ) (term_cren B ξ) s
  | Sig1 A B s => Sig1 (term_cren A ξ) (term_cren B ξ) s
  | Pair0 m n s => Pair0 (term_cren m ξ) (term_cren n ξ) s
  | Pair1 m n s => Pair1 (term_cren m ξ) (term_cren n ξ) s
  | LetIn A m n =>
      LetIn
        (term_cren A ξ)
        (term_cren m ξ)
        (term_cren n ξ)
  | Fix A m => Fix (term_cren A ξ) (term_cren m ξ)
  (* data *)
  | Unit => Unit
  | II => II
  | Bool => Bool
  | TT => TT
  | FF => FF
  | Ifte A m n1 n2 =>
      Ifte
        (term_cren A ξ)
        (term_cren m ξ)
        (term_cren n1 ξ)
        (term_cren n2 ξ)
  (* monadic *)
  | IO A => IO (term_cren A ξ)
  | Return m => Return (term_cren m ξ)
  | Bind m n => Bind (term_cren m ξ) (term_cren n ξ)
  (* session *)
  | Proto => Proto
  | Stop r => Stop r
  | Act0 r A B => Act0 r (term_cren A ξ) (term_cren B ξ)
  | Act1 r A B => Act1 r (term_cren A ξ) (term_cren B ξ)
  | Ch r A => Ch r (term_cren A ξ)
  | CVar x => CVar (ξ x)
  | Fork A m => Fork (term_cren A ξ) (term_cren m ξ)
  | Recv0 m => Recv0 (term_cren m ξ)
  | Recv1 m => Recv1 (term_cren m ξ)
  | Send0 m => Send0 (term_cren m ξ)
  | Send1 m => Send1 (term_cren m ξ)
  | Close m => Close (term_cren m ξ)
  | Wait m => Wait (term_cren m ξ)
  end.

Lemma term_cren_ren m ξ ξ' :
  term_cren m.[ren ξ] ξ' = (term_cren m ξ').[ren ξ].
Proof with eauto.
  elim: m ξ ξ'...
  { move=>A ihA B ihB s ξ ξ'. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>A ihA B ihB s ξ ξ'. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>A ihA m ihm s ξ ξ'. asimpl.
    rewrite ihA. rewrite ihm... }
  { move=>A ihA m ihm s ξ ξ'. asimpl.
    rewrite ihA. rewrite ihm... }
  { move=>m ihm n ihn ξ ξ'. asimpl.
    rewrite ihm. rewrite ihn... }
  { move=>A ihA B ihB s ξ ξ'. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>A ihA B ihB s ξ ξ'. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>m ihm n ihn s ξ ξ'. asimpl.
    rewrite ihm. rewrite ihn... }
  { move=>m ihm n ihn s ξ ξ'. asimpl.
    rewrite ihm. rewrite ihn... }
  { move=>A ihA m ihm n ihn ξ ξ'. asimpl.
    rewrite ihA. rewrite ihm. rewrite ihn... }
  { move=>A ihA m ihm ξ ξ'. asimpl.
    rewrite ihA. rewrite ihm... }
  { move=>A ihA m ihm n1 ihn1 n2 ihn2 ξ ξ'. asimpl.
    rewrite ihA. rewrite ihm.
    rewrite ihn1. rewrite ihn2... }
  { move=>A ihA ξ ξ'. asimpl. rewrite ihA... }
  { move=>m ihm ξ ξ'. asimpl. rewrite ihm... }
  { move=>m ihm n ihn ξ ξ'. asimpl.
    rewrite ihm. rewrite ihn... }  
  { move=>r A ihA B ihB ξ ξ'. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>r A ihA B ihB ξ ξ'. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>r A ihA ξ ξ'. asimpl.
    rewrite ihA... }
  { move=>A ihA m ihm ξ ξ'. asimpl.
    rewrite ihA. rewrite ihm... }
  { move=>m ihm ξ ξ'. asimpl. rewrite ihm... }
  { move=>m ihm ξ ξ'. asimpl. rewrite ihm... }
  { move=>m ihm ξ ξ'. asimpl. rewrite ihm... }
  { move=>m ihm ξ ξ'. asimpl. rewrite ihm... }
  { move=>m ihm ξ ξ'. asimpl. rewrite ihm... }
  { move=>m ihm ξ ξ'. asimpl. rewrite ihm... }
Qed.

Lemma term_cren_id m : term_cren m id = m.
Proof with eauto.
  elim: m=>//=...
  { move=>A ihA B ihB s. rewrite ihA. by rewrite ihB. }
  { move=>A ihA B ihB s. rewrite ihA. by rewrite ihB. }
  { move=>A ihA m ihm s. rewrite ihA. by rewrite ihm. }
  { move=>A ihA m ihm s. rewrite ihA. by rewrite ihm. }
  { move=>m ihm n ihn. rewrite ihm. by rewrite ihn. }
  { move=>m ihm n ihn. rewrite ihm. by rewrite ihn. }
  { move=>A ihA B ihB s. rewrite ihA. by rewrite ihB. }
  { move=>A ihA B ihB s. rewrite ihA. by rewrite ihB. }
  { move=>m ihm n ihn s. rewrite ihm. by rewrite ihn. }
  { move=>A ihA m ihm n ihn. rewrite ihA. rewrite ihm. by rewrite ihn. }
  { move=>A ihA m ihm. rewrite ihA. by rewrite ihm. }
  { move=>A ihA m ihm n1 ihn1 n2 ihn2.
    rewrite ihA. rewrite ihm. rewrite ihn1. by rewrite ihn2. }
  { move=>A ihA. by rewrite ihA. }
  { move=>m ihm. by rewrite ihm. }
  { move=>m ihm n ihn. rewrite ihm. by rewrite ihn. }
  { move=>r A ihA B ihB. rewrite ihA. by rewrite ihB. }
  { move=>r A ihA B ihB. rewrite ihA. by rewrite ihB. }
  { move=>r A ihA. by rewrite ihA. }
  { move=>A ihA m ihm. rewrite ihA. by rewrite ihm. }
  { move=>m ihm. by rewrite ihm. }
  { move=>m ihm. by rewrite ihm. }
  { move=>m ihm. by rewrite ihm. }
  { move=>m ihm. by rewrite ihm. }
  { move=>m ihm. by rewrite ihm. }
  { move=>m ihm. by rewrite ihm. }
Qed.

Lemma term_cren_comp ξ1 ξ2 m :
  term_cren m (ξ1 >>> ξ2) = term_cren (term_cren m ξ1) ξ2.
Proof with eauto.
  elim: m ξ1 ξ2=>//=.
  { move=>A ihA B ihB s ξ1 ξ2. rewrite ihA. by rewrite ihB. }
  { move=>A ihA B ihB s ξ1 ξ2. rewrite ihA. by rewrite ihB. }
  { move=>A ihA m ihm s ξ1 ξ2. rewrite ihA. by rewrite ihm. }
  { move=>A ihA m ihm s ξ1 ξ2. rewrite ihA. by rewrite ihm. }
  { move=>m ihm n ihn ξ1 ξ2. rewrite ihm. by rewrite ihn. }
  { move=>A ihA B ihB s ξ1 ξ2. rewrite ihA. by rewrite ihB. }
  { move=>A ihA B ihB s ξ1 ξ2. rewrite ihA. by rewrite ihB. }
  { move=>m ihm n ihn s ξ1 ξ2. rewrite ihm. by rewrite ihn. }
  { move=>m ihm n ihn s ξ1 ξ2. rewrite ihm. by rewrite ihn. }
  { move=>A ihA m ihm n ihn ξ1 ξ2. rewrite ihA. rewrite ihm. by rewrite ihn. }
  { move=>A ihA m ihm ξ1 ξ2. rewrite ihA. by rewrite ihm. }
  { move=>A ihA m ihm n1 ihn1 n2 ihn2 ξ1 ξ2.
    rewrite ihA. rewrite ihm. rewrite ihn1. by rewrite ihn2. }
  { move=>A ihA ξ1 ξ2. by rewrite ihA. }
  { move=>m ihm ξ1 ξ2. by rewrite ihm. }
  { move=>m ihm n ihn ξ1 ξ2. rewrite ihm. by rewrite ihn. }
  { move=>r A ihA B ihB ξ1 ξ2. rewrite ihA. by rewrite ihB. }
  { move=>r A ihA B ihB ξ1 ξ2. rewrite ihA. by rewrite ihB. }
  { move=>r A ihA ξ1 ξ2. by rewrite ihA. }
  { move=>A ihA m ihm ξ1 ξ2. rewrite ihA. by rewrite ihm. }
  { move=>m ihm ξ1 ξ2. by rewrite ihm. }
  { move=>m ihm ξ1 ξ2. by rewrite ihm. }
  { move=>m ihm ξ1 ξ2. by rewrite ihm. }
  { move=>m ihm ξ1 ξ2. by rewrite ihm. }
  { move=>m ihm ξ1 ξ2. by rewrite ihm. }
  { move=>m ihm ξ1 ξ2. by rewrite ihm. }
Qed.

Definition term_csubst (σ σ' : var -> term) ξ :=
  forall x, σ' x = term_cren (σ x) ξ.

Lemma term_csubst1 n ξ :
  term_csubst (n .: ids) (term_cren n ξ .: ids) ξ.
Proof with eauto.
  move=>x.
  elim: x n ξ.
  { move=>n ξ. asimpl... }
  { move=>n ihn n0 ξ. by asimpl. }
Qed.

Lemma term_csubst2 n1 n2 ξ :
  term_csubst (n1 .: n2 .: ids) (term_cren n1 ξ .: term_cren n2 ξ .: ids) ξ.
Proof with eauto.
  move=>x.
  elim: x n1 n2 ξ.
  { move=>n1 n2 ξ. asimpl... }
  { move=>n ihn n1 n2 ξ. asimpl.
    rewrite term_csubst1... }
Qed.

Lemma term_csubst_pair0 ξ t :
  term_csubst
    (Pair0 (Var 1) (Var 0) t .: ren (+2))
    (Pair0 (Var 1) (Var 0) t .: ren (+2)) ξ.
Proof. move=>x. elim: x ξ t=>//. Qed.

Lemma term_csubst_pair1 ξ t :
  term_csubst
    (Pair1 (Var 1) (Var 0) t .: ren (+2))
    (Pair1 (Var 1) (Var 0) t .: ren (+2)) ξ.
Proof. move=>x. elim: x ξ t=>//. Qed.

Lemma term_csubst_up σ σ' ξ :
  term_csubst σ σ' ξ -> term_csubst (up σ) (up σ') ξ.
Proof.
  move=>h x.
  elim: x σ σ' ξ h.
  { move=>σ σ' ξ h. asimpl. by simpl. }
  { move=>n ih σ σ' ξ h. asimpl.
    rewrite h. by rewrite term_cren_ren. }
Qed.

Lemma term_cren_subst m σ σ' ξ :
  term_csubst σ σ' ξ -> term_cren m.[σ] ξ = (term_cren m ξ).[σ'].
Proof.
  elim: m σ σ' ξ.
  all: solve[intros; asimpl; f_equal; eauto using term_csubst_up].
Qed.

Lemma term_cren_beta1 m n ξ :
  term_cren m.[n/] ξ = (term_cren m ξ).[term_cren n ξ/].
Proof.
  apply: term_cren_subst.
  apply: term_csubst1.
Qed.

Lemma term_cren_beta2 m n1 n2 ξ :
  term_cren m.[n1,n2/] ξ = (term_cren m ξ).[term_cren n1 ξ,term_cren n2 ξ/].
Proof.
  apply: term_cren_subst.
  apply: term_csubst2.
Qed.
