From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tllc_cren proc_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma proc_crename Θ Θ' p ξ :
  Θ ⊢ p -> dyn_ctx_cren ξ Θ Θ' -> Θ' ⊢ proc_cren p ξ.
Proof with eauto.
  move=>ty. elim: ty Θ' ξ=>{Θ p}.
  { move=>Θ m tym Θ' ξ agr/=.
    constructor.
    replace (IO Unit) with (term_cren (IO Unit) ξ) by eauto.
    apply: dyn_crename... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq Θ' ξ agr/=.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg.
    econstructor... }
  { move=>Θ p r1 r2 A xor typ ihp Θ' ξ agr/=.
    have wf:=proc_type_wf typ. inv wf. inv H1.
    econstructor...
    apply: ihp.
    have agr0:=dyn_ctx_cren_ty r2 H5 agr.
    have{}agr0:=dyn_ctx_cren_ty (~~r2) H3 agr0.
    rewrite<-term_cren_comp in agr0.
    have e:((+1) >>> upren ξ) = (ξ >>> (+1)) by autosubst.
    rewrite e in agr0.
    have{}e:(term_cren A (ξ >>> (+1)))= term_cren (term_cren A ξ) (+1).
    by rewrite<-term_cren_comp.
    rewrite e in agr0.
    apply: agr0. }
Qed.

Lemma proc_cstrengthen Θ p : _: Θ ⊢ proc_cren p (+1) -> Θ ⊢ p.
Proof.
  move=>ty.
  have e:((+1) >>> (-1)) = id.
  { f_ext. move=>x. asimpl. fold subn. lia. }
  replace p with (proc_cren (proc_cren p (+1)) ((-1) >>> id)).
  apply: proc_crename.
  apply: ty.
  constructor.
  constructor.
  rewrite<-proc_cren_comp.
  asimpl.
  rewrite e.
  by rewrite proc_cren_id.
Qed.

Lemma proc_cweaken Θ p : Θ ⊢ p -> _: Θ ⊢ proc_cren p (+1). 
Proof with eauto.
  move=>ty.
  apply: proc_crename...
  constructor.
  constructor.
Qed.
