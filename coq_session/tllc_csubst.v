From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_csubst tllc_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[global] Instance CSubst_proc : CSubst proc :=
  fix dummy (σ : cvar -> term) (p : proc) : proc :=
    let proc_csubst := @csubst proc dummy in
    match p with
    | Exp m => Exp (csubst σ m)
    | Par p q => Par (proc_csubst σ p) (proc_csubst σ q)
    | Nu p => Nu (proc_csubst (cup (cup σ)) p)
    end.

Lemma proc_csubst_cids p : csubst cids p = p. 
Proof with eauto.
  elim: p=>//=...
  { move=>m. rewrite term_csubst_cids... }
  { move=>p ihp q ihq. autorew... }
  { move=>p e. rewrite! cup_cids. rewrite e... }
Qed.

Lemma proc_csubst_comp p σ1 σ2 :
  csubst σ2 (csubst σ1 p) = csubst (σ1 >>> csubst σ2) p.
Proof.
  elim: p σ1 σ2=>//=.
  { move=>m σ1 σ2. by rewrite term_csubst_comp. }
  { move=>p ihp q ihq σ1 σ2. by autorew. }
  { move=>p ihp σ1 σ2. f_equal.
    rewrite ihp. f_equal.
    apply: (term_cupn_comp σ1 σ2 2). }
Qed.
