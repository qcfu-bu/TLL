From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_inv proc_sr eproc_occurs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma eproc_congr0_type Θ p p' q :
  proc_congr0 p q -> Θ ⊢ p ~ p' -> exists2 q', proc_congr0 p' q' & Θ ⊢ q ~ q'.
Proof with eauto using era_type, eproc_type, proc_congr0.
  move=>cgr. elim: cgr Θ p'=>{p q}.
  { move=>p q Θ p' er. inv er.
    exists (q' ∣ p'0)...
    econstructor.
    apply: merge_sym...
    all: eauto. }
  { move=>o p q Θ p' er. inv er. inv H5.
    have[Θ4[mrg1 mrg2]]:=merge_splitL (merge_sym H1) H2.
    exists ((p'0 ∣ p') ∣ q'0)...
    econstructor. apply: mrg2.
    econstructor. apply: merge_sym.
    all: eauto. }
  { move=>p q Θ p' er. inv er. inv H3.
    exists (ν.(p' ∣ proc_cren q' (+2))).
    constructor.
    move: H4. move e:(~~r2)=>r1 erp.
    econstructor. apply: (esym e).
    econstructor.
    2:{ apply: erp. }
    2:{ replace (proc_cren q (+2)) with (proc_cren (proc_cren q (+1)) (+1)).
        replace (proc_cren q' (+2)) with (proc_cren (proc_cren q' (+1)) (+1)).
        apply: eproc_cweaken.
        apply: eproc_cweaken.
        apply: H5.
        rewrite<-proc_cren_comp. by asimpl.
        rewrite<-proc_cren_comp. by asimpl. }
    repeat constructor... }
  { move=>p p' q q' cgr1 ih1 cgr2 ih2 Θ p0 er. inv er.
    have[p1 cgr3 erp]:=ih1 _ _ H3.
    have[q1 cgr4 erq]:=ih2 _ _ H5.
    exists (p1 ∣ q1)... }
  { move=>p p' cgr ih Θ p0 er. inv er.
    have[p1 cgr1 erp]:=ih _ _ H2.
    exists (ν.p1)... }
  { move=>p Θ p' er. inv er. inv H5.
    have[n e]:=era_return_form H2. subst.
    have er:=era_return_inv H2.
    have e:=era_ii_form er. subst.
    have emp:=era_ii_inv er.
    have e:=merge_emptyR H1 emp. subst... }
Qed.

Lemma eproc_congr0_typei Θ p q q' :
  proc_congr0 p q -> Θ ⊢ q ~ q' -> exists2 p', proc_congr0 p' q' & Θ ⊢ p ~ p'.
Proof with eauto using era_type, eproc_type, proc_congr0.
  move=>cgr. elim: cgr Θ q'=>{p q}.
  { move=>p q Θ q' er. inv er.
    exists (q'0 ∣ p'). constructor.
    econstructor.
    apply: merge_sym...
    all: eauto. }
  { move=>o p q Θ q' er. inv er. inv H3.
    have[Θ4[mrg1 mrg2]]:=merge_splitR H1 H2.
    exists (p'0 ∣ (q' ∣ q'0)). apply: proc_congr0_assoc.
    econstructor.
    apply: merge_sym.
    apply: mrg2.
    eauto.
    econstructor... }
  { move=>p q Θ q' er. inv er. inv H2. inv H1; inv H3.
    { have[q0 e]:=eproc_cren_inv H6. subst.
      replace (proc_cren q (+2))
        with (proc_cren (proc_cren q (+1)) (+1)) in H6.
      replace (proc_cren q0 (+2))
        with (proc_cren (proc_cren q0 (+1)) (+1)) in H6.
      have erq:=eproc_cstrengthen (eproc_cstrengthen H6).
      exists (ν.p'0 ∣ q0).
      constructor.
      econstructor...
      rewrite<-proc_cren_comp. by asimpl.
      rewrite<-proc_cren_comp. by asimpl. }
    { have[q0 e]:=eproc_cren_inv H6. subst.
      have:=eproc_occurs_iren H6 iren1.
      have[->_]:proc_occurs 1 (proc_cren q (+2)) = 1 ∧
               proc_occurs 1 (proc_cren q0 (+2)) = 1.
      apply: eproc_type_occurs1...
      repeat constructor.
      by move=>[]. }
    { have[q0 e]:=eproc_cren_inv H6. subst.
      have:=eproc_occurs_iren H6 iren0.
      have[->_]:proc_occurs 0 (proc_cren q (+2)) = 1 ∧
               proc_occurs 0 (proc_cren q0 (+2)) = 1.
      apply: eproc_type_occurs1...
      repeat constructor.
      by move=>[]. }
    { have[q0 e]:=eproc_cren_inv H6. subst.
      have:=eproc_occurs_iren H6 iren0.
      have[->_]:proc_occurs 0 (proc_cren q (+2)) = 1 ∧
               proc_occurs 0 (proc_cren q0 (+2)) = 1.
      apply: eproc_type_occurs1...
      repeat constructor.
      by move=>[]. } }
  { move=>p p' q q' cgr1 ih1 crg2 ih2 Θ q0 er. inv er.
    have[p2 cgr3 erp]:=ih1 _ _ H3.
    have[q2 cgr4 erq]:=ih2 _ _ H5.
    exists (p2 ∣ q2)... }
  { move=>p p' cgr ih Θ q' er. inv er.
    have[p1 cgr1 erp]:=ih _ _ H2.
    exists (ν.p1)... }
  { move=>p Θ q' er.
    have wf:=eproc_type_wf er.
    have[Θ0[emp mrg]]:=proc_wf_empty wf.
    exists (q' ∣ ⟨ Return II ⟩)...
    econstructor.
    apply: merge_sym.
    all: eauto.
    repeat constructor... }
Qed.

Lemma eproc_congr_type Θ p p' q :
  p ≡ q -> Θ ⊢ p ~ p' -> exists2 q', p' ≡ q' & Θ ⊢ q ~ q'.
Proof with eauto.
  move=>eq. elim: eq Θ p'=>{q}...
  { move=>y z eq1 ih cr1 Θ p' erp.
    have[q' eq2 ery]:=ih _ _ erp.
    have[z' cr2 erz]:=eproc_congr0_type cr1 ery.
    exists z'... apply: conv_trans. apply: eq2. by apply: conv1. }
  { move=>y z eq1 ih cr1 Θ p' erp.
    have[q' eq2 ery]:=ih _ _ erp.
    have[z' cr2 erz]:=eproc_congr0_typei cr1 ery.
    exists z'... apply: conv_trans. apply: eq2. apply: conv_sym. by apply: conv1. }
Qed.

Theorem eproc_sr Θ p p' q :
  Θ ⊢ p ~ p' -> p ≈>> q -> exists2 q', Θ ⊢ q ~ q' & p' ≈>> q'.
Proof with eauto using merge, merge_sym, sta_type, dyn_type.
  move=>er st. elim: st Θ p' er=>{p q}.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { move=>p x q y eq1 st ih eq2 Θ p' erp.
    have[x' eq3 erx]:=eproc_congr_type eq1 erp.
    have[y' eqy st']:=ih _ _ erx.
    have[z' eqz erz]:=eproc_congr_type eq2 eqy.
    exists z'...
    apply: proc_congr.
    apply: eq3.
    apply: st'.
    apply: eqz. }
Admitted.
