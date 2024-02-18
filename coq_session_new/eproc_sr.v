From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS proc_sr eproc_occurs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma eproc_congr0_type Θ p p' q :
  proc_congr0 p q -> Θ ⊢ p ~ p' -> exists2 q', proc_congr0 p' q' & Θ ⊢ q ~ q'.
Proof with eauto using proc_type, proc_congr0.
Admitted.

Lemma eproc_congr0_typei Θ p q q' :
  proc_congr0 p q -> Θ ⊢ q ~ q' -> exists2 p', proc_congr0 p' q' & Θ ⊢ p ~ p'.
Proof with eauto using proc_type, proc_congr0.
Admitted.

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
