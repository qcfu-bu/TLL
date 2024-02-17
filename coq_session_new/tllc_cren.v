From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tllc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint proc_cren (p : proc) (ξ : cvar -> cvar) : proc :=
  match p with
  | ⟨ m ⟩ => ⟨ term_cren m ξ ⟩
  | p ∣ q => (proc_cren p ξ) ∣ (proc_cren q ξ)
  | ν.p => ν.(proc_cren p (upren (upren ξ)))
  end.

Lemma proc_cren_id p : proc_cren p id = p.
Proof with eauto.
  elim: p=>//=.
  { move=>m. by rewrite term_cren_id. }
  { move=>p ihp q ihq. rewrite ihp. by rewrite ihq. }
  { move=>p ihp. asimpl. by rewrite ihp. }
Qed.

Lemma proc_cren_comp ξ1 ξ2 p :
  proc_cren p (ξ1 >>> ξ2) = proc_cren (proc_cren p ξ1) ξ2.
Proof with eauto.
  elim: p ξ1 ξ2=>/=.
  { move=>m ξ1 ξ2. by rewrite term_cren_comp. }
  { move=>p ihp q ihq ξ1 ξ2. rewrite ihp. rewrite ihq... }
  { move=>p ihp ξ1 ξ2. rewrite<-ihp. by asimpl. }
Qed.

