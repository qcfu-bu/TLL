From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_weak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive proc :=
| Exp (m : term)
| Par (p q : proc)
| Nu (p : proc).

Notation "⟨ m ⟩" := (Exp m).
Notation "p ∣ q" := (Par p q) (at level 50).
Notation "'ν.' p" := (Nu p) (at level 50).


Lemma dyn_crename Θ Θ' Γ Γ' Δ Δ' m A ξ :
  Θ ; Γ ; Δ ⊢ m : A -> dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' ->
  Θ' ; Γ' ; Δ' ⊢ term_cren m ξ : term_cren A ξ.
Proof with eauto using dyn_empty, dyn_type.
  move=>ty. elim: ty Θ' Γ' Δ' ξ=>/={Θ Γ Δ m A}.
  { intros.
    econstructor.
    admit.
    admit.
    admit.
    admit. }
  { intros.
    econstructor.
    admit.
    admit.
    apply: H2.
    econstructor.
    eauto.
    admit.
    eauto. }
  { intros.
    econstructor.
    admit.
    admit.
    apply: H2.
    constructor.
    eauto.
    admit.
    eauto. }
  { intros.
    rewrite term_cren_beta.
    apply: dyn_app0...
    admit. }
  { intros.
    rewrite term_cren_beta.
    apply: dyn_app1...
    admit.
    admit.
    apply: H2.
    admit.
    apply: H4.
    admit. }

Lemma dyn_strengthen Θ m A :
  _: Θ ; nil ; nil ⊢ term_cren m (+1) : term_cren A (+1) ->
  Θ ; nil ; nil ⊢ m : A.
Proof with eauto using dyn_empty, dyn_type.
  intros.
  replace m with (term_cren (term_cren m (+1)) (subn^~ 1)).
  replace A with (term_cren (term_cren A (+1)) (subn^~ 1)).
  apply: dyn_crename.
  apply: H.
  constructor.
  replace (subn^~ 1) with (id >>> subn^~ 1) by autosubst.
  constructor.
  constructor.


  move=>ty. elim: ty Γ' Δ'=>//={Θ Γ Δ m A}...
  admit.
  { intros.
    constructor...
    admit.
    admit.
    apply: H2.
    econstructor...
    admit. }
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  { intros.
    replace (term_cren A.[ren (+size Γ)] (+1))
      with (term_cren A (+1)).[ren (+size Γ')].
    apply: dyn_cvar.
    admit.
    admit.
    admit.
    admit.
    admit. }
  { intros.
    econstructor...
    constructor... }
  { intros.
    econstructor...
    constructor... }
  { intros.
  }
Admitted.

Lemma dyn_cweaken0 Θ m A :
  Θ ; nil ; nil ⊢ m : A ->
  _: Θ ; nil ; nil ⊢ term_cren m (+1) : term_cren A (+1).
Proof with eauto using dyn_empty, dyn_type.
  intros.
  apply: dyn_cweaken...
  constructor.

  move=>ty. elim: ty Γ' Δ'=>//={Θ Γ Δ m A}...
  { intros.
    econstructor...

    
    constructor... }
  { intros.
    econstructor...
    constructor... }
  { intros.
  }
