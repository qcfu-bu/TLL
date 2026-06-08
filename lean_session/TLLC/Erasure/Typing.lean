import TLLC.Dynamic.SR

/-!
# Erasure typing

Port of `coq_session/era_type.v`: the erasure relation `era_type`
(`Θ ; Γ ; Δ ⊢ m ~ m' : A`, here `Erased Θ Γ Δ m m' A`, notation `Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A`). It reads
"the source term `m` erases to the runtime term `m'` at type `A`", where erasure replaces irrelevant
subterms (implicit-`Pi`/`Sig` annotations, the implicit argument/component, the `LetIn`/`Ifte`/`Fork`
motive/type) with `Box` (`.box`).

The judgment is structurally parallel to the dynamic typing `Dynamic.Typed` (it reuses the entire
Dynamic context machinery — `Wf`/`Merge`/`Key`/`Empty`/`Has`/`Just`), threading a second (erased)
term. As in the dynamic layer, Coq's implicit/explicit constructor pairs merge via the `Rlv`/`Bool`
tag only where identical; CBV/linearity asymmetries stay split (`lamIm`/`lamEx`, `appIm`/`appEx`,
`pairIm`/`pairEx`, `projIm`/`projEx`); merged: `ite`, `mlet` (Coq `Bind`), `recv`/`send`,
`close` (`Close`/`Wait`).
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- The erasure relation (Coq `era_type`): `m` erases to `m'` at type `A`. -/
inductive Erased : Ctx → Static.Ctx → Ctx → Term → Term → Term → Prop where
  -- core
  | var {Θ Γ Δ x s A} :
    Empty Θ →
    Wf Γ Δ →
    Static.Has Γ x A →
    Has Δ x s A →
    Erased Θ Γ Δ (.var_Term x) (.var_Term x) A
  | lamIm {Θ Γ Δ A B m m' s} :
    Θ ▷ s →
    Δ ▷ s →
    Erased Θ (A :: Γ) (none :: Δ) m m' B →
    Erased Θ Γ Δ (.lam A m .im s) (.lam .box m' .im s) (.pi A B .im s)
  | lamEx {Θ Γ Δ A B m m' s t} :
    Θ ▷ s →
    Δ ▷ s →
    Erased Θ (A :: Γ) (A :⟨t⟩ Δ) m m' B →
    Erased Θ Γ Δ (.lam A m .ex s) (.lam .box m' .ex s) (.pi A B .ex s)
  | appIm {Θ Γ Δ A B m m' n s} :
    Erased Θ Γ Δ m m' (.pi A B .im s) →
    Γ ⊢ n : A →
    Erased Θ Γ Δ (.app m n .im) (.app m' .box .im) (B[Chan.var_Chan; n..])
  | appEx {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    Erased Θ1 Γ Δ1 m m' (.pi A B .ex s) →
    Erased Θ2 Γ Δ2 n n' A →
    Erased Θ Γ Δ (.app m n .ex) (.app m' n' .ex) (B[Chan.var_Chan; n..])
  | pairIm {Θ Γ Δ A B m n n' t} :
    Γ ⊢ .sig A B .im t : .srt t →
    Γ ⊢ m : A →
    Erased Θ Γ Δ n n' (B[Chan.var_Chan; m..]) →
    Erased Θ Γ Δ (.pair m n .im t) (.pair .box n' .im t) (.sig A B .im t)
  | pairEx {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    Γ ⊢ .sig A B .ex t : .srt t →
    Erased Θ1 Γ Δ1 m m' A →
    Erased Θ2 Γ Δ2 n n' (B[Chan.var_Chan; m..]) →
    Erased Θ Γ Δ (.pair m n .ex t) (.pair m' n' .ex t) (.sig A B .ex t)
  | projIm {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    .sig A B .im t :: Γ ⊢ C : .srt s →
    Erased Θ1 Γ Δ1 m m' (.sig A B .im t) →
    Erased Θ2 (B :: A :: Γ) (B :⟨r⟩ none :: Δ2) n n'
      (C[Chan.var_Chan; (Term.pair (.var_Term 1) (.var_Term 0) .im t) .: funcomp Term.var_Term (· + 2)]) →
    Erased Θ Γ Δ (.proj C m n) (.proj .box m' n') (C[Chan.var_Chan; m..])
  | projEx {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    .sig A B .ex t :: Γ ⊢ C : .srt s →
    Erased Θ1 Γ Δ1 m m' (.sig A B .ex t) →
    Erased Θ2 (B :: A :: Γ) (B :⟨r2⟩ A :⟨r1⟩ Δ2) n n'
      (C[Chan.var_Chan; (Term.pair (.var_Term 1) (.var_Term 0) .ex t) .: funcomp Term.var_Term (· + 2)]) →
    Erased Θ Γ Δ (.proj C m n) (.proj .box m' n') (C[Chan.var_Chan; m..])
  -- data
  | one {Θ Γ Δ} :
    Empty Θ →
    Wf Γ Δ →
    Δ ▷ Srt.U →
    Erased Θ Γ Δ .one .one .unit
  | tt {Θ Γ Δ} :
    Empty Θ →
    Wf Γ Δ →
    Δ ▷ Srt.U →
    Erased Θ Γ Δ .tt .tt .bool
  | ff {Θ Γ Δ} :
    Empty Θ →
    Wf Γ Δ →
    Δ ▷ Srt.U →
    Erased Θ Γ Δ .ff .ff .bool
  | ite {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    .bool :: Γ ⊢ A : .srt s →
    Erased Θ1 Γ Δ1 m m' .bool →
    Erased Θ2 Γ Δ2 n1 n1' (A[Chan.var_Chan; Term.tt..]) →
    Erased Θ2 Γ Δ2 n2 n2' (A[Chan.var_Chan; Term.ff..]) →
    Erased Θ Γ Δ (.ite A m n1 n2) (.ite .box m' n1' n2') (A[Chan.var_Chan; m..])
  -- monadic
  | pure {Θ Γ Δ m m' A} :
    Erased Θ Γ Δ m m' A →
    Erased Θ Γ Δ (.pure m) (.pure m') (.M A)
  | mlet {Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t} :
    Merge Θ1 Θ2 Θ →
    Merge Δ1 Δ2 Δ →
    Γ ⊢ B : .srt t →
    Erased Θ1 Γ Δ1 m m' (.M A) →
    Erased Θ2 (A :: Γ) (A :⟨s⟩ Δ2) n n' (.M (B⟨(id : Nat → Nat); ↑⟩)) →
    Erased Θ Γ Δ (.mlet m n) (.mlet m' n') (.M B)
  -- session
  | chan {Θ Γ Δ r x A} :
    Just Θ x (.ch r A) →
    Wf Γ Δ →
    Δ ▷ Srt.U →
    [] ⊢ A : .proto →
    Erased Θ Γ Δ (.chan (Chan.var_Chan x)) (.chan (Chan.var_Chan x)) (.ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩))
  | fork {Θ Γ Δ A m m'} :
    Erased Θ (.ch true A :: Γ) (.ch true A :L Δ) m m' (.M .unit) →
    Erased Θ Γ Δ (.fork A m) (.fork .box m') (.M (.ch false A))
  | recv {Θ Γ Δ r1 r2 A B m m' i} :
    xor r1 r2 = false →
    Erased Θ Γ Δ m m' (.ch r1 (.act r2 A B i)) →
    Erased Θ Γ Δ (.recv m i) (.recv m' i) (.M (.sig A (.ch r1 B) i .L))
  | send {Θ Γ Δ r1 r2 A B m m' i} :
    xor r1 r2 = true →
    Erased Θ Γ Δ m m' (.ch r1 (.act r2 A B i)) →
    Erased Θ Γ Δ (.send m i) (.send m' i) (.pi A (.M (.ch r1 B)) i .L)
  | close {Θ Γ Δ b m m'} :
    Erased Θ Γ Δ m m' (.ch b .stop) →
    Erased Θ Γ Δ (.close b m) (.close b m') (.M .unit)
  -- conversion
  | conv {Θ Γ Δ A B m m' s} :
    A ≃ B →
    Erased Θ Γ Δ m m' A →
    Γ ⊢ B : .srt s →
    Erased Θ Γ Δ m m' B

@[inherit_doc]
scoped notation:50 Θ:50 " ⨾ " Γ:51 " ⨾ " Δ:51 " ⊢ " m:51 " ~ " m':51 " : " A:51 =>
  Erased Θ Γ Δ m m' A

end TLLC.Erasure
