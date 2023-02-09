From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS proc_step dyn_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Θ ⊢ p" (at level 50, p at next level).

Inductive proc_type : dyn_ctx -> proc -> Prop :=
| proc_exp Θ m :
  Θ ; nil ; nil ⊢ m : IO Unit ->
  Θ ⊢ ⟨ m ⟩
| proc_par Θ1 Θ2 Θ p q :
  Θ1 ∘ Θ2 => Θ ->
  Θ1 ⊢ p ->
  Θ2 ⊢ q ->
  Θ ⊢ p ∣ q
| proc_scope Θ p r1 r2 A :
  r1 = ~~r2 ->
  Ch r1 (term_cren A (+1)) :L Ch r2 A :L Θ ⊢ p ->
  Θ ⊢ ν.p
where "Θ ⊢ p" := (proc_type Θ p).

Lemma proc_congr0_sym p q : proc_congr0 p q -> proc_congr0 q p.
Proof. elim; move=>*; eauto using proc_congr0. Qed.

Lemma proc_crename Θ Θ' p ξ :
  Θ ⊢ p -> dyn_ctx_cren ξ Θ Θ' -> Θ' ⊢ proc_cren p ξ.
Proof with eauto.
  move=>ty. elim: ty Θ' ξ=>{Θ p}.
  { move=>Θ m tym Θ' ξ agr/=.
    constructor.
    replace (IO Unit) with (term_cren (IO Unit) ξ) by eauto.
    apply: dyn_crename.
    apply: tym.
    constructor... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq Θ' ξ agr/=.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg.
    econstructor... }
  { move=>Θ p r1 r2 A xor typ ihp Θ' ξ agr/=.
    econstructor...
    apply: ihp.
    have tyA:nil ⊢ A : Proto by admit.
    have tyA':nil ⊢ term_cren A (+1) : Proto by admit.
    have agr0:=dyn_ctx_cren_ty r2 tyA agr.
    have{}agr0:=dyn_ctx_cren_ty r1 tyA' agr0.
    rewrite<-term_cren_comp in agr0.
    have e:((+1) >>> upren ξ) = (ξ >>> (+1)) by autosubst.
    rewrite e in agr0.
    have{}e:(term_cren A (ξ >>> (+1)))= term_cren (term_cren A ξ) (+1).
    by rewrite<-term_cren_comp.
    rewrite e in agr0.
    apply: agr0. }
  {
  }

Lemma proc_congr0_type Θ p q : Θ ⊢ p -> proc_congr0 p q -> Θ ⊢ q.
Proof with eauto using proc_type, proc_congr0.
  move=>ty. elim: ty q=>{Θ p}.
  { move=>Θ m tym q cgr. inv cgr. }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq q0 cgr. inv cgr.
    { econstructor. apply: merge_sym. all: eauto. }
    { inv tyq.
      have[Θ4[mrg1 mrg2]]:=merge_splitL (merge_sym mrg) H1.
      econstructor. apply: mrg2.
      econstructor. apply: merge_sym mrg1.
      all: eauto. }
    { admit. }
    { admit. }
    { admit. }
    { admit. } }
  { move=>Θ p r1 r2 A d typ ihp q cgr. inv cgr.
    { inv typ. inv H1; inv H5.
      { econstructor. apply: H2.
        econstructor...
      }
    }
  }
