From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_era_type Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ m : A -> exists m', Θ ; Γ ; Δ ⊢ m ~ m' : A. 
Proof with eauto using era_type.
  elim=>{Θ Γ Δ m A}.
  { move=>Θ Γ Δ x s A chs wf shs dhs. exists (Var x)... }
  { move=>Θ Γ Δ A B m s k1 k2 tym [m' erm'].
    exists (Lam0 Box m' s)... }
  { move=>Θ Γ Δ A B m s t k1 k2 tym [m' erm'].
    exists (Lam1 Box m' s)... }
  { move=>Θ Γ Δ A B m n s tym [m' erm'] tyn.
    exists (App0 m' Box)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym [m' erm'] tyn [n' ern'].
    exists (App1 m' n')... }
  { move=>Θ Γ Δ A B m n t tyS tym tyn [n' ern'].
    exists (Pair0 Box n' t)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym [m' erm'] tyn [n' ern'].
    exists (Pair1 m' n' t)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
      tyC tym [m' erm'] tyn [n' ern'].
    exists (LetIn Box m' n')... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
      tyC tym [m' erm'] tyn [n' ern'].
    exists (LetIn Box m' n')... }
  { move=>Θ Γ Δ A m k1 k2 tym [m' erm'].
    exists (Fix Box m')... }
  { move=>Θ Γ Δ chs wf k. exists II... }
  { move=>Θ Γ Δ chs wf k. exists TT... }
  { move=>Θ Γ Δ chs wf k. exists FF... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
      tyA tym[m' erm'] tyn1[n1' ern1'] tyn2[n2' ern2'].
    exists (Ifte Box m' n1' n2')... }
  { move=>Θ Γ Δ m A tym[m' erm']. exists (Return m')... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
      tyB tym[m' erm'] tyn[n' ern'].
    exists (Bind m' n')... }
  { move=>Θ Γ Δ r x A chs wf k tyA. exists (CVar x)... }
  { move=>Θ Γ Δ m A tym[m' erm']. exists (Fork Box m')... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym[m' erm']. exists (Recv0 m')... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym[m' erm']. exists (Recv1 m')... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym[m' erm']. exists (Send0 m')... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym[m' erm']. exists (Send1 m')... }
  { move=>Θ Γ Δ m tym[m' erm']. exists (Wait m')... }
  { move=>Θ Γ Δ m tym[m' erm']. exists (Close m')... }
  { move=>Θ Γ Δ A B m s eq tym[m' erm']tyB. exists m'... }
Qed.

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
