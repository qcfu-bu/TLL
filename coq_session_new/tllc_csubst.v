From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_csubst tllc_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint proc_csubst (p : proc) (σ : cvar -> term) :=
  match p with
  | Exp m => Exp (term_csubst m σ)
  | Par p q => Par (proc_csubst p σ) (proc_csubst q σ)
  | Nu p => Nu (proc_csubst p (upp (upp σ)))
  end.

Lemma proc_csubst_cids p : proc_csubst p cids = p. 
Proof with eauto.
  elim: p=>//=...
  { move=>m. rewrite term_csubst_cids... }
  { move=>p ihp q ihq. autorew... }
  { move=>p e. rewrite! upp_cids. rewrite e... }
Qed.

Lemma proc_csubst_comp p σ1 σ2 :
  proc_csubst (proc_csubst p σ1) σ2 = proc_csubst p (σ1 >>> term_csubst^~ σ2).
Proof.
  elim: p σ1 σ2=>//=.
  { move=>m σ1 σ2. by rewrite term_csubst_comp. }
  { move=>p ihp q ihq σ1 σ2. by autorew. }
  { move=>p ihp σ1 σ2. f_equal.
    rewrite ihp. f_equal.
    apply: (term_uppn_comp σ1 σ2 2). }
Qed.
