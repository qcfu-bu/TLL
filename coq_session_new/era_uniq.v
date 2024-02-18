From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint erase (m : term) : term :=
  match m with
  | Var x => Var x
  | Lam0 _ m s => Lam0 Box (erase m) s
  | Lam1 _ m s => Lam1 Box (erase m) s
  | App0 m _ => App0 (erase m) Box
  | App1 m n => App1 (erase m) (erase n)
  | Pair0 _ n s => Pair0 Box (erase n) s
  | Pair1 m n s => Pair1 (erase m) (erase n) s
  | LetIn _ m n => LetIn Box (erase m) (erase n)
  | Fix _ m => Fix Box (erase m)
  | II => II
  | TT => TT
  | FF => FF
  | Ifte _ m n1 n2 => Ifte Box (erase m) (erase n1) (erase n2)
  | IO _ => Box
  | Return m => Return (erase m)
  | Bind m n => Bind (erase m) (erase n)
  | CVar x => CVar x
  | Fork _ m => Fork Box (erase m)
  | Recv0 m => Recv0 (erase m)
  | Recv1 m => Recv1 (erase m)
  | Send0 m => Send0 (erase m)
  | Send1 m => Send1 (erase m)
  | Close m => Close (erase m)
  | Wait m => Wait (erase m)
  | _ => Box
  end.

Lemma era_type_erase Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> m' = erase m.
Proof with eauto.
  elim=>//={Θ Γ Δ m m' A}...
  { move=>Θ Γ Δ A B m m' s k1 k2 erm->//. }
  { move=>Θ Γ Δ A B m m' s t k1 k2 erm->//. }
  { move=>Θ Γ Δ A B m m' n s erm->//. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 erm->ern->//. }
  { move=>Θ Γ Δ A B m n n' t tyS tym ern->//. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS erm->ern->//. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2 tyS erm->ern->//. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2 tyS erm->ern->//. }
  { move=>Θ Γ Δ A m m' k1 k2 erm->//. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2 tyA erm->ern1->ern2->//. }
  { move=>Θ Γ Δ m m' A erm->//. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB erm->ern->//. }
  { move=>Θ Γ Δ m m' A erm->//. }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm->//. }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm->//. }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm->//. }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm->//. }
  { move=>Θ Γ Δ m m' erm->//. }
  { move=>Θ Γ Δ m m' erm->//. }
Qed.

Lemma era_unicity Θ Γ Δ m m1 m2 A :
  Θ ; Γ ; Δ ⊢ m ~ m1 : A -> 
  Θ ; Γ ; Δ ⊢ m ~ m2 : A -> 
  m1 = m2.
Proof with eauto.
  move=>er1 er2.
  have->:=era_type_erase er1.
  have->:=era_type_erase er2.
  by [].
Qed.
