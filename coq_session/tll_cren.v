From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_classes sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "( - n )" := (subn^~ n).

#[global] Instance CRename_term : CRename term :=
  fix dummy (ξ : cvar -> cvar) (m : term) : term :=
    let term_cren := @cren term dummy in
    match m with
    (* core *)
    | Var x => Var x
    | Sort s => Sort s
    | Pi0 A B s => Pi0 (term_cren ξ A) (term_cren ξ B) s
    | Pi1 A B s => Pi1 (term_cren ξ A) (term_cren ξ B) s
    | Lam0 A m s => Lam0 (term_cren ξ A) (term_cren ξ m) s
    | Lam1 A m s => Lam1 (term_cren ξ A) (term_cren ξ m) s
    | App0 m n => App0 (term_cren ξ m) (term_cren ξ n)
    | App1 m n => App1 (term_cren ξ m) (term_cren ξ n)
    | Sig0 A B s => Sig0 (term_cren ξ A) (term_cren ξ B) s
    | Sig1 A B s => Sig1 (term_cren ξ A) (term_cren ξ B) s
    | Pair0 m n s => Pair0 (term_cren ξ m) (term_cren ξ n) s
    | Pair1 m n s => Pair1 (term_cren ξ m) (term_cren ξ n) s
    | LetIn A m n => LetIn (term_cren ξ A) (term_cren ξ m) (term_cren ξ n)
    | Fix A m => Fix (term_cren ξ A) (term_cren ξ m)
    (* data *)
    | Unit => Unit | II => II | Bool => Bool | TT => TT | FF => FF
    | Ifte A m n1 n2 =>
      Ifte (term_cren ξ A) (term_cren ξ m) (term_cren ξ n1) (term_cren ξ n2)
    (* monadic *)
    | IO A => IO (term_cren ξ A)
    | Return m => Return (term_cren ξ m)
    | Bind m n => Bind (term_cren ξ m) (term_cren ξ n)
    (* session *)
    | Proto => Proto
    | Stop => Stop
    | Act0 r A B => Act0 r (term_cren ξ A) (term_cren ξ B)
    | Act1 r A B => Act1 r (term_cren ξ A) (term_cren ξ B)
    | Ch r A => Ch r (term_cren ξ A)
    | CVar x => (fun x => CVar (ξ x)) x
    | Fork A m => Fork (term_cren ξ A) (term_cren ξ m)
    | Recv0 m => Recv0 (term_cren ξ m)
    | Recv1 m => Recv1 (term_cren ξ m)
    | Send0 m => Send0 (term_cren ξ m)
    | Send1 m => Send1 (term_cren ξ m)
    | Close m => Close (term_cren ξ m)
    | Wait m => Wait (term_cren ξ m)
    | Box => Box
    end.

Lemma term_cren_ren m ξ ξ' :
  cren ξ' m.[ren ξ] = (cren ξ' m).[ren ξ].
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

Lemma term_cren_id m : cren id m = m.
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
  cren (ξ1 >>> ξ2) m = cren ξ2 (cren ξ1 m).
Proof with eauto.
  elim: m ξ1 ξ2=>//=.
  { move=>A ihA B ihB s ξ1 ξ2. rewrite ihA. by rewrite ihB. }
  { move=>A ihA B ihB s ξ1 ξ2. rewrite ihA. by rewrite ihB. }
  { move=>A ihA m ihm s ξ1 ξ2. rewrite ihA. by rewrite ihm. }
  { move=>A ihA m ihm s ξ1 ξ2. rewrite ihA. by rewrite ihm. }
  { move=>m ihm n ihn ξ1 ξ2. rewrite ihm. by rewrite ihn. }
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

Definition cren_subst_agree (σ σ' : var -> term) ξ :=
  forall x, σ' x = cren ξ (σ x).

Lemma term_cren_subst1 n ξ :
  cren_subst_agree (n .: ids) (cren ξ n .: ids) ξ.
Proof with eauto.
  move=>x.
  elim: x n ξ.
  { move=>n ξ. asimpl... }
  { move=>n ihn n0 ξ. by asimpl. }
Qed.

Lemma term_cren_subst2 n1 n2 ξ :
  cren_subst_agree (n1 .: n2 .: ids) (cren ξ n1 .: cren ξ n2 .: ids) ξ.
Proof with eauto.
  move=>x.
  elim: x n1 n2 ξ.
  { move=>n1 n2 ξ. asimpl... }
  { move=>n ihn n1 n2 ξ. asimpl.
    rewrite term_cren_subst1... }
Qed.

Lemma term_cren_subst_pair0 ξ t :
  cren_subst_agree
    (Pair0 (Var 1) (Var 0) t .: ren (+2))
    (Pair0 (Var 1) (Var 0) t .: ren (+2)) ξ.
Proof. move=>x. elim: x ξ t=>//. Qed.

Lemma term_cren_subst_pair1 ξ t :
  cren_subst_agree
    (Pair1 (Var 1) (Var 0) t .: ren (+2))
    (Pair1 (Var 1) (Var 0) t .: ren (+2)) ξ.
Proof. move=>x. elim: x ξ t=>//. Qed.

Lemma term_cren_subst_up σ σ' ξ :
  cren_subst_agree σ σ' ξ -> cren_subst_agree (up σ) (up σ') ξ.
Proof.
  move=>h x.
  elim: x σ σ' ξ h.
  { move=>σ σ' ξ h. asimpl. by simpl. }
  { move=>n ih σ σ' ξ h. asimpl.
    rewrite h. by rewrite term_cren_ren. }
Qed.

Lemma term_cren_subst m σ σ' ξ :
  cren_subst_agree σ σ' ξ -> cren ξ m.[σ] = (cren ξ m).[σ'].
Proof.
  elim: m σ σ' ξ.
  all: solve[intros; asimpl; f_equal; eauto using term_cren_subst_up].
Qed.

Lemma term_cren_beta1 m n ξ :
  cren ξ m.[n/] = (cren ξ m).[cren ξ n/].
Proof. apply: term_cren_subst. apply: term_cren_subst1. Qed.

Lemma term_cren_beta2 m n1 n2 ξ :
  cren ξ m.[n1,n2/] = (cren ξ m).[cren ξ n1,cren ξ n2/].
Proof. apply: term_cren_subst. apply: term_cren_subst2. Qed.
