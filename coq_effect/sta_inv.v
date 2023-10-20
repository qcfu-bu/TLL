From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sta_forall_inv Γ A B C :
  Γ ⊢ Forall A B : C ->
  (A :: Γ) ⊢ B : Ty /\ C === Ty.
Proof with eauto.
  move e:(Forall A B)=>m ty.
  elim: ty A B e=>//{Γ C m}.
  { move=>Γ A B tyA ihA tyB ihB A0 B0 [e1 e2]; subst... }
  { move=>Γ A B m eq1 tym ihm tyB ihB A0 B0 e; subst.
    have[tyB0 eq2]:=ihm _ _ erefl.
    split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_arrow_inv Γ A B C :
  Γ ⊢ Arrow A B : C ->
  (A :: Γ) ⊢ B.[ren (+1)] : Ty /\ C === Ty.
Proof with eauto.
  move e:(Arrow A B)=>m ty.
  elim: ty A B e=>//{Γ C m}.
  { move=>Γ A B tyA ihA tyB ihB A0 B0 [e1 e2]; subst... }
  { move=>Γ A B m eq1 tym ihm tyB ihB A0 B0 e; subst.
    have[tyB0 eq2]:=ihm _ _ erefl.
    split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.
