From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS proc_csubst era_csubst eproc_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma eproc_csubstitution Θ2 Θ1 p p' σ :
  Θ2 ⊢ p ~ p' -> Θ1 ⊩ σ ⫣ Θ2 -> Θ1 ⊢ proc_csubst p σ ~ proc_csubst p' σ. 
Proof with eauto.
  move=>ty. elim: ty Θ1 σ=>{Θ2 p p'}.
  { move=>Θ m m' tym Θ1 σ agr. constructor.
    apply: era_csubstitution... }
  { move=>Θ1 Θ2 Θ p p' q q' mrg typ ihp tyq ihq Θ0 σ agr. simpl.
    have[Θa[Θb[mrgx[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg.
    have{}ihp:=ihp _ _ agr1.
    have{}ihq:=ihq _ _ agr2.
    econstructor... }
  { move=>Θ p p' r1 r2 A xor typ ihp Θ1 σ agr. simpl.
    have wf:=eproc_type_wf typ. inv wf. inv H1.
    econstructor... apply: ihp.
    repeat constructor... }
Qed.
