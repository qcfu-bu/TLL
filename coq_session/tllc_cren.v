From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tllc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[global] Instance CRename_proc : CRename proc :=
  fix dummy (ξ : cvar -> cvar) (p : proc) : proc :=
    let proc_cren := @cren proc dummy in
    match p with
    | ⟨ m ⟩ => ⟨ cren ξ m ⟩
    | p ∣ q => (proc_cren ξ p) ∣ (proc_cren ξ q)
    | ν.p => ν.(proc_cren (upren (upren ξ)) p)
    end.

Lemma proc_cren_id p : cren id p = p.
Proof with eauto.
  elim: p=>//=.
  { move=>m. by rewrite term_cren_id. }
  { move=>p ihp q ihq. rewrite ihp. by rewrite ihq. }
  { move=>p ihp. asimpl. by rewrite ihp. }
Qed.

Lemma proc_cren_comp ξ1 ξ2 p :
  cren (ξ1 >>> ξ2) p = cren ξ2 (cren ξ1 p).
Proof with eauto.
  elim: p ξ1 ξ2=>/=.
  { move=>m ξ1 ξ2. by rewrite term_cren_comp. }
  { move=>p ihp q ihq ξ1 ξ2. rewrite ihp. rewrite ihq... }
  { move=>p ihp ξ1 ξ2. rewrite<-ihp. by asimpl. }
Qed.

