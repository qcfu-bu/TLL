From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS proc_type proc_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma proc_congr0_sym p q : proc_congr0 p q -> proc_congr0 q p.
Proof. elim; move=>*; eauto using proc_congr0. Qed.

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
    { inv typ.
      have[Θ4[mrg1 mrg2]]:=merge_splitR mrg H1.
      econstructor. apply: (merge_sym mrg2). apply: H3.
      econstructor... }
    { inv typ.
      have wf:=proc_type_wf H2. inv wf. inv H1.
      have mrg': 
        Ch (~~r2) (term_cren A (+1)) :L Ch r2 A :L Θ1 ∘ _: _: Θ2 =>
        Ch (~~r2) (term_cren A (+1)) :L Ch r2 A :L Θ.
      repeat econstructor; eauto.
      econstructor...
      econstructor...
      replace (proc_cren q (+2)) with (proc_cren (proc_cren q (+1)) (+1)).
      apply: proc_cweaken.
      apply: proc_cweaken...
      rewrite<-proc_cren_comp.
      by asimpl. }
    { econstructor... }
    { econstructor.
      apply: mrg.
      apply: ihp. apply: proc_congr0_sym...
      apply: ihq. apply: proc_congr0_sym... } }
  { move=>Θ p r1 r2 A d typ ihp q cgr. inv cgr.
    { inv typ. inv H1; inv H5.
      { econstructor. apply: H2.
        econstructor...
        apply: proc_cstrengthen.
        apply: proc_cstrengthen.
        rewrite<-proc_cren_comp.
        by asimpl. }
      { have:=dyn_occurs_iren.
      }
    }
  }
