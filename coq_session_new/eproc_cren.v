From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_cren proc_cren eproc_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma eproc_crename Θ Θ' p p' ξ :
  Θ ⊢ p ~ p' -> dyn_ctx_cren ξ Θ Θ' -> Θ' ⊢ proc_cren p ξ ~ proc_cren p' ξ.
Proof with eauto.
  move=>er. elim: er Θ' ξ=>{Θ p p'}.
  { move=>Θ m m' tym Θ' ξ agr/=.
    constructor.
    replace (IO Unit) with (term_cren (IO Unit) ξ) by eauto.
    apply: era_crename... }
  { move=>Θ1 Θ2 Θ p p' q q' mrg typ ihp tyq ihq Θ' ξ agr/=.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg.
    econstructor... }
  { move=>Θ p p' r1 r2 A xor typ ihp Θ' ξ agr/=.
    have wf:=eproc_type_wf typ. inv wf. inv H1.
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

Lemma eproc_cstrengthen Θ p p' : _: Θ ⊢ proc_cren p (+1) ~ proc_cren p' (+1) -> Θ ⊢ p ~ p'.
Proof.
  move=>ty.
  have e:((+1) >>> (-1)) = id.
  { f_ext. move=>x. asimpl. fold subn. lia. }
  replace p with (proc_cren (proc_cren p (+1)) ((-1) >>> id)).
  replace p' with (proc_cren (proc_cren p' (+1)) ((-1) >>> id)).
  apply: eproc_crename.
  apply: ty.
  repeat constructor.
  rewrite<-proc_cren_comp.
  asimpl. rewrite e.
  by rewrite proc_cren_id.
  rewrite<-proc_cren_comp.
  asimpl. rewrite e.
  by rewrite proc_cren_id.
Qed.

Lemma eproc_cweaken Θ p p' : Θ ⊢ p ~ p' -> _: Θ ⊢ proc_cren p (+1) ~ proc_cren p' (+1). 
Proof with eauto.
  move=>ty.
  apply: eproc_crename...
  constructor.
  constructor.
Qed.

Lemma eproc_cren_inv Θ p x ξ :
  Θ ⊢ proc_cren p ξ ~ x -> exists p', x = proc_cren p' ξ. 
Proof with eauto.
  move e:(proc_cren p ξ)=>n er. elim: er p ξ e=>{Θ x n}.
  { move=>Θ m m' erm p ξ e. destruct p; inv e.
    have[m1 e]:=era_cren_inv erm. subst. by exists ⟨ m1 ⟩. }
  { move=>Θ1 Θ2 Θ p p' q q' mrg erp ihp erq ihq p0 ξ e.
    destruct p0; inv e.
    have[p1 e1]:=ihp _ _ erefl.
    have[q1 e2]:=ihq _ _ erefl.
    subst. by exists (p1 ∣ q1). }
  { move=>Θ p p' r1 r2 A _ erp ihp p0 ξ e. destruct p0; inv e.
    have[p1 e1]:=ihp _ _ erefl. subst. by exists (ν.p1). }
Qed.
