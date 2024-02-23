From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tllc_csubst dyn_csubst proc_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma proc_csubstitution Θ2 Θ1 p σ :
  Θ2 ⊢ p -> Θ1 ⊩ σ ⫣ Θ2 -> Θ1 ⊢ proc_csubst p σ. 
Proof with eauto.
  move=>ty. elim: ty Θ1 σ=>{Θ2 p}.
  { move=>Θ m tym Θ1 σ agr. constructor.
    apply: dyn_csubstitution... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq Θ0 σ agr. simpl.
    have[Θa[Θb[mrgx[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg.
    have{}ihp:=ihp _ _ agr1.
    have{}ihq:=ihq _ _ agr2.
    econstructor... }
  { move=>Θ p r1 r2 A xor typ ihp Θ1 σ agr. simpl.
    have wf:=proc_type_wf typ. inv wf. inv H1.
    econstructor... apply: ihp.
    repeat constructor... }
Qed.
