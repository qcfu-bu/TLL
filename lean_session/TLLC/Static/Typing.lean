import TLLC.Static.Context
import TLLC.Static.Confluence

/-!
# Static typing

Port of `coq_session/sta_type.v`: the proof-irrelevant arity/guardedness predicates
(`arity_proto`, `guarded`), the sort order `s ⊑ t` (Coq `sort_leq` from `tll_ast.v`), the
"level-0" typing judgment `Typed0`/`Wf0` (Coq `sta0_type`/`sta0_wf`), the main typing judgment
`Typed`/`Wf` with notation `Γ ⊢ m : A` (Coq `sta_type`/`sta_wf`), and the bridge lemmas between
them.

As elsewhere, Coq's implicit/explicit constructor pairs are merged via the `Rlv` tag (`.im`/`.ex`)
and `Close`/`Wait` via the `Bool` tag. The lone case where the `0`/`1` rules genuinely differ is
`sig`: Coq `sta_sig1` carries an extra premise `s ⊑ t` absent from `sta_sig0`; the merged rule
gates it with `r = .ex → s ⊑ t`.
-/

namespace TLLC.Static
open Autosubst Autosubst.Notation

/-- Protocol arity (Coq `arity_proto`). -/
def ArityProto : Term → Prop
  | .proto => True
  | .pi _ B _ _ => ArityProto B
  | _ => False

/-- Guardedness of variable `x` in a term (Coq `guarded`). -/
def Guarded (x : Nat) : Term → Prop
  | .var_Term y => x ≠ y
  | .srt _ => True
  | .pi A B _ _ => Guarded x A ∧ Guarded (x + 1) B
  | .lam A m _ _ => Guarded x A ∧ Guarded (x + 1) m
  | .app m n _ => Guarded x m ∧ Guarded x n
  | .sig A B _ _ => Guarded x A ∧ Guarded (x + 1) B
  | .pair m n _ _ => Guarded x m ∧ Guarded x n
  | .proj A m n => Guarded (x + 1) A ∧ Guarded x m ∧ Guarded (x + 2) n
  | .fix A m => Guarded x A ∧ Guarded (x + 1) m
  | .unit => True
  | .one => True
  | .bool => True
  | .tt => True
  | .ff => True
  | .ite A m n1 n2 => Guarded (x + 1) A ∧ Guarded x m ∧ Guarded x n1 ∧ Guarded x n2
  | .M A => Guarded x A
  | .pure m => Guarded x m
  | .mlet m n => Guarded x m ∧ Guarded (x + 1) n
  | .proto => True
  | .stop => True
  | .act _ A _ _ => Guarded x A
  | .ch _ A => Guarded x A
  | .chan _ => True
  | .fork A m => Guarded x A ∧ Guarded (x + 1) m
  | .recv m _ => Guarded x m
  | .send m _ => Guarded x m
  | .close _ m => Guarded x m
  | .box => True

/-- Sort order (Coq `sort_leq`, `s ⊑ t`): `U ⊑ s` for all `s`, and `L ⊑ L`. -/
inductive Srt.Leq : Srt → Srt → Prop where
  | U {s} : Srt.Leq .U s
  | L : Srt.Leq .L .L

@[inherit_doc] scoped infix:30 " ⊑ " => Srt.Leq

/-- Every sort is below `L` (Coq `sort_leq_Lgt`). -/
lemma sort_leq_Lgt {s} : s ⊑ Srt.L := by cases s <;> constructor

/-! ## Level-0 typing and well-formedness (Coq `sta0_type` / `sta0_wf`). -/

mutual
/-- Level-0 typing (Coq `sta0_type`). -/
inductive Typed0 : Ctx → Term → Term → Prop where
  -- core
  | srt {Γ s} :
    Wf0 Γ →
    Typed0 Γ (.srt s) (.srt .U)
  | var {Γ x A} :
    Wf0 Γ →
    Has Γ x A →
    Typed0 Γ (.var_Term x) A
  | pi {Γ A B i s r t} :
    Typed0 Γ A (.srt r) →
    Typed0 (A :: Γ) B (.srt t) →
    Typed0 Γ (.pi A B i s) (.srt s)
  | lam {Γ A B m i s r} :
    Typed0 Γ A (.srt r) →
    Typed0 (A :: Γ) m B →
    Typed0 Γ (.lam A m i s) (.pi A B i s)
  | app {Γ A B m n i s} :
    Typed0 Γ m (.pi A B i s) →
    Typed0 Γ n A →
    Typed0 Γ (.app m n i) (B[Chan.var_Chan; n..])
  | sig {Γ A B i s r t} :
    (i = .ex → s ⊑ t) →
    r ⊑ t →
    Typed0 Γ A (.srt s) →
    Typed0 (A :: Γ) B (.srt r) →
    Typed0 Γ (.sig A B i t) (.srt t)
  | pair {Γ A B m n i t} :
    Typed0 Γ (.sig A B i t) (.srt t) →
    Typed0 Γ m A →
    Typed0 Γ n (B[Chan.var_Chan; m..]) →
    Typed0 Γ (.pair m n i t) (.sig A B i t)
  | proj {Γ A B C m n i s t} :
    Typed0 (.sig A B i t :: Γ) C (.srt s) →
    Typed0 Γ m (.sig A B i t) →
    Typed0 (B :: A :: Γ) n
      (C[Chan.var_Chan; (Term.pair (.var_Term 1) (.var_Term 0) i t) .: funcomp Term.var_Term (· + 2)]) →
    Typed0 Γ (.proj C m n) (C[Chan.var_Chan; m..])
  | fix {Γ A m s} :
    ArityProto A →
    Guarded 0 m →
    Typed0 Γ A (.srt s) →
    Typed0 (A :: Γ) m (A⟨(id : Nat → Nat); ↑⟩) →
    Typed0 Γ (.fix A m) A
  -- data
  | unit {Γ} :
    Wf0 Γ →
    Typed0 Γ .unit (.srt .U)
  | one {Γ} :
    Wf0 Γ →
    Typed0 Γ .one .unit
  | bool {Γ} :
    Wf0 Γ →
    Typed0 Γ .bool (.srt .U)
  | tt {Γ} :
    Wf0 Γ →
    Typed0 Γ .tt .bool
  | ff {Γ} :
    Wf0 Γ →
    Typed0 Γ .ff .bool
  | ite {Γ A m n1 n2 s} :
    Typed0 (.bool :: Γ) A (.srt s) →
    Typed0 Γ m .bool →
    Typed0 Γ n1 (A[Chan.var_Chan; Term.tt..]) →
    Typed0 Γ n2 (A[Chan.var_Chan; Term.ff..]) →
    Typed0 Γ (.ite A m n1 n2) (A[Chan.var_Chan; m..])
  -- monadic
  | M {Γ A s} :
    Typed0 Γ A (.srt s) →
    Typed0 Γ (.M A) (.srt .L)
  | pure {Γ m A} :
    Typed0 Γ m A →
    Typed0 Γ (.pure m) (.M A)
  | mlet {Γ m n A B s} :
    Typed0 Γ B (.srt s) →
    Typed0 Γ m (.M A) →
    Typed0 (A :: Γ) n (.M (B⟨(id : Nat → Nat); ↑⟩)) →
    Typed0 Γ (.mlet m n) (.M B)
  -- session
  | proto {Γ} :
    Wf0 Γ →
    Typed0 Γ .proto (.srt .U)
  | stop {Γ} :
    Wf0 Γ →
    Typed0 Γ .stop .proto
  | act {Γ b A B i s} :
    Typed0 Γ A (.srt s) →
    Typed0 (A :: Γ) B .proto →
    Typed0 Γ (.act b A B i) .proto
  | ch {Γ b A} :
    Typed0 Γ A .proto →
    Typed0 Γ (.ch b A) (.srt .L)
  | chan {Γ b x A} :
    Wf0 Γ →
    Typed0 [] A .proto →
    Typed0 Γ (.chan (Chan.var_Chan x)) (.ch b (A⟨(id : Nat → Nat); (· + Γ.length)⟩))
  | fork {Γ A m s} :
    Typed0 Γ (.ch true A) (.srt s) →
    Typed0 (.ch true A :: Γ) m (.M .unit) →
    Typed0 Γ (.fork A m) (.M (.ch false A))
  | recv {Γ r1 r2 A B m i} :
    xor r1 r2 = false →
    Typed0 Γ m (.ch r1 (.act r2 A B i)) →
    Typed0 Γ (.recv m i) (.M (.sig A (.ch r1 B) i .L))
  | send {Γ r1 r2 A B m i} :
    xor r1 r2 = true →
    Typed0 Γ m (.ch r1 (.act r2 A B i)) →
    Typed0 Γ (.send m i) (.pi A (.M (.ch r1 B)) i .L)
  | close {Γ b m} :
    Typed0 Γ m (.ch b .stop) →
    Typed0 Γ (.close b m) (.M .unit)
  -- conversion
  | conv {Γ A B m s} :
    A ≃ B →
    Typed0 Γ m A →
    Typed0 Γ B (.srt s) →
    Typed0 Γ m B

/-- Level-0 well-formedness (Coq `sta0_wf`). -/
inductive Wf0 : Ctx → Prop where
  | nil : Wf0 []
  | cons {Γ A s} :
    Wf0 Γ →
    Typed0 Γ A (.srt s) →
    Wf0 (A :: Γ)
end

/-- Level-0 typing implies the context is well-formed (Coq `sta0_type_wf`). -/
lemma Typed0.wf {Γ m A} (h : Typed0 Γ m A) : Wf0 Γ := by
  induction h using Typed0.rec (motive_2 := fun Γ _ => Wf0 Γ) with
  | srt wf _ => exact wf
  | var wf _ _ => exact wf
  | pi _ _ ih _ => exact ih
  | lam _ _ ih _ => exact ih
  | app _ _ ih _ => exact ih
  | sig _ _ _ _ ih _ => exact ih
  | pair _ _ _ ih _ _ => exact ih
  | proj _ _ _ _ ih _ => exact ih
  | fix _ _ _ _ ih _ => exact ih
  | unit wf _ => exact wf
  | one wf _ => exact wf
  | bool wf _ => exact wf
  | tt wf _ => exact wf
  | ff wf _ => exact wf
  | ite _ _ _ _ _ ih _ _ => exact ih
  | M _ ih => exact ih
  | pure _ ih => exact ih
  | mlet _ _ _ ih _ _ => exact ih
  | proto wf _ => exact wf
  | stop wf _ => exact wf
  | act _ _ ih _ => exact ih
  | ch _ ih => exact ih
  | chan wf _ _ _ => exact wf
  | fork _ _ ih _ => exact ih
  | recv _ _ ih => exact ih
  | send _ _ ih => exact ih
  | close _ ih => exact ih
  | conv _ _ _ ihm _ => exact ihm
  | nil => exact .nil
  | cons _ ty ih _ => exact .cons ih ty

/-! ## Main typing and well-formedness (Coq `sta_type` / `sta_wf`). -/

mutual
/-- Main typing judgment (Coq `sta_type`, notation `Γ ⊢ m : A`). -/
inductive Typed : Ctx → Term → Term → Prop where
  -- core
  | srt {Γ s} :
    Wf Γ →
    Typed Γ (.srt s) (.srt .U)
  | var {Γ x A} :
    Wf Γ →
    Has Γ x A →
    Typed Γ (.var_Term x) A
  | pi {Γ A B i s r t} :
    Typed Γ A (.srt r) →
    Typed (A :: Γ) B (.srt t) →
    Typed Γ (.pi A B i s) (.srt s)
  | lam {Γ A B m i s} :
    Typed (A :: Γ) m B →
    Typed Γ (.lam A m i s) (.pi A B i s)
  | app {Γ A B m n i s} :
    Typed Γ m (.pi A B i s) →
    Typed Γ n A →
    Typed Γ (.app m n i) (B[Chan.var_Chan; n..])
  | sig {Γ A B i s r t} :
    (i = .ex → s ⊑ t) →
    r ⊑ t →
    Typed Γ A (.srt s) →
    Typed (A :: Γ) B (.srt r) →
    Typed Γ (.sig A B i t) (.srt t)
  | pair {Γ A B m n i t} :
    Typed Γ (.sig A B i t) (.srt t) →
    Typed Γ m A →
    Typed Γ n (B[Chan.var_Chan; m..]) →
    Typed Γ (.pair m n i t) (.sig A B i t)
  | proj {Γ A B C m n i s t} :
    Typed (.sig A B i t :: Γ) C (.srt s) →
    Typed Γ m (.sig A B i t) →
    Typed (B :: A :: Γ) n
      (C[Chan.var_Chan; (Term.pair (.var_Term 1) (.var_Term 0) i t) .: funcomp Term.var_Term (· + 2)]) →
    Typed Γ (.proj C m n) (C[Chan.var_Chan; m..])
  | fix {Γ A m} :
    ArityProto A →
    Guarded 0 m →
    Typed (A :: Γ) m (A⟨(id : Nat → Nat); ↑⟩) →
    Typed Γ (.fix A m) A
  -- data
  | unit {Γ} :
    Wf Γ →
    Typed Γ .unit (.srt .U)
  | one {Γ} :
    Wf Γ →
    Typed Γ .one .unit
  | bool {Γ} :
    Wf Γ →
    Typed Γ .bool (.srt .U)
  | tt {Γ} :
    Wf Γ →
    Typed Γ .tt .bool
  | ff {Γ} :
    Wf Γ →
    Typed Γ .ff .bool
  | ite {Γ A m n1 n2 s} :
    Typed (.bool :: Γ) A (.srt s) →
    Typed Γ m .bool →
    Typed Γ n1 (A[Chan.var_Chan; Term.tt..]) →
    Typed Γ n2 (A[Chan.var_Chan; Term.ff..]) →
    Typed Γ (.ite A m n1 n2) (A[Chan.var_Chan; m..])
  -- monadic
  | M {Γ A s} :
    Typed Γ A (.srt s) →
    Typed Γ (.M A) (.srt .L)
  | pure {Γ m A} :
    Typed Γ m A →
    Typed Γ (.pure m) (.M A)
  | mlet {Γ m n A B s} :
    Typed Γ B (.srt s) →
    Typed Γ m (.M A) →
    Typed (A :: Γ) n (.M (B⟨(id : Nat → Nat); ↑⟩)) →
    Typed Γ (.mlet m n) (.M B)
  -- session
  | proto {Γ} :
    Wf Γ →
    Typed Γ .proto (.srt .U)
  | stop {Γ} :
    Wf Γ →
    Typed Γ .stop .proto
  | act {Γ b A B i} :
    Typed (A :: Γ) B .proto →
    Typed Γ (.act b A B i) .proto
  | ch {Γ b A} :
    Typed Γ A .proto →
    Typed Γ (.ch b A) (.srt .L)
  | chan {Γ b x A} :
    Wf Γ →
    Typed [] A .proto →
    Typed Γ (.chan (Chan.var_Chan x)) (.ch b (A⟨(id : Nat → Nat); (· + Γ.length)⟩))
  | fork {Γ m A} :
    Typed (.ch true A :: Γ) m (.M .unit) →
    Typed Γ (.fork A m) (.M (.ch false A))
  | recv {Γ r1 r2 A B m i} :
    xor r1 r2 = false →
    Typed Γ m (.ch r1 (.act r2 A B i)) →
    Typed Γ (.recv m i) (.M (.sig A (.ch r1 B) i .L))
  | send {Γ r1 r2 A B m i} :
    xor r1 r2 = true →
    Typed Γ m (.ch r1 (.act r2 A B i)) →
    Typed Γ (.send m i) (.pi A (.M (.ch r1 B)) i .L)
  | close {Γ b m} :
    Typed Γ m (.ch b .stop) →
    Typed Γ (.close b m) (.M .unit)
  -- conversion
  | conv {Γ A B m s} :
    A ≃ B →
    Typed Γ m A →
    Typed Γ B (.srt s) →
    Typed Γ m B

/-- Main well-formedness (Coq `sta_wf`). -/
inductive Wf : Ctx → Prop where
  | nil : Wf []
  | cons {Γ A s} :
    Wf Γ →
    Typed Γ A (.srt s) →
    Wf (A :: Γ)
end

@[inherit_doc] scoped notation:50 Γ:50 " ⊢ " m:51 " : " A:51 => Typed Γ m A

/-- Typing implies the context is well-formed (Coq `sta_type_wf`). -/
lemma Typed.wf {Γ m A} (h : Γ ⊢ m : A) : Wf Γ := by
  induction h using Typed.rec (motive_2 := fun Γ _ => Wf Γ) with
  | srt wf _ => exact wf
  | var wf _ _ => exact wf
  | pi _ _ ih _ => exact ih
  | lam _ ih => cases ih with | cons wf _ => exact wf
  | app _ _ ih _ => exact ih
  | sig _ _ _ _ ih _ => exact ih
  | pair _ _ _ ih _ _ => exact ih
  | proj _ _ _ _ ih _ => exact ih
  | fix _ _ _ ih => cases ih with | cons wf _ => exact wf
  | unit wf _ => exact wf
  | one wf _ => exact wf
  | bool wf _ => exact wf
  | tt wf _ => exact wf
  | ff wf _ => exact wf
  | ite _ _ _ _ _ ih _ _ => exact ih
  | M _ ih => exact ih
  | pure _ ih => exact ih
  | mlet _ _ _ ih _ _ => exact ih
  | proto wf _ => exact wf
  | stop wf _ => exact wf
  | act _ ih => cases ih with | cons wf _ => exact wf
  | ch _ ih => exact ih
  | chan wf _ _ _ => exact wf
  | fork _ ih => cases ih with | cons wf _ => exact wf
  | recv _ _ ih => exact ih
  | send _ _ ih => exact ih
  | close _ ih => exact ih
  | conv _ _ _ ihm _ => exact ihm
  | nil => exact .nil
  | cons _ ty ih _ => exact .cons ih ty

/-- The main judgment implies its level-0 counterpart (Coq `Typed.toTyped0`). -/
lemma Typed.toTyped0 {Γ m A} (h : Γ ⊢ m : A) : Typed0 Γ m A := by
  induction h using Typed.rec (motive_2 := fun Γ _ => Wf0 Γ) with
  | srt _ ih => exact .srt ih
  | var _ hs ih => exact .var ih hs
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ ihm =>
      have wf0 := Typed0.wf ihm
      cases wf0 with | cons _ hA => exact .lam hA ihm
  | app _ _ ihm ihn => exact .app ihm ihn
  | sig h1 h2 _ _ ihA ihB => exact .sig h1 h2 ihA ihB
  | pair _ _ _ ihS ihm ihn => exact .pair ihS ihm ihn
  | proj _ _ _ ihC ihm ihn => exact .proj ihC ihm ihn
  | fix ar gr _ ihm =>
      have wf0 := Typed0.wf ihm
      cases wf0 with | cons _ hA => exact .fix ar gr hA ihm
  | unit _ ih => exact .unit ih
  | one _ ih => exact .one ih
  | bool _ ih => exact .bool ih
  | tt _ ih => exact .tt ih
  | ff _ ih => exact .ff ih
  | ite _ _ _ _ ihA ihm ihn1 ihn2 => exact .ite ihA ihm ihn1 ihn2
  | M _ ihA => exact .M ihA
  | pure _ ihm => exact .pure ihm
  | mlet _ _ _ ihB ihm ihn => exact .mlet ihB ihm ihn
  | proto _ ih => exact .proto ih
  | stop _ ih => exact .stop ih
  | act _ ihB =>
      have wf0 := Typed0.wf ihB
      cases wf0 with | cons _ hA => exact .act hA ihB
  | ch _ ihA => exact .ch ihA
  | chan _ _ ih ihA => exact .chan ih ihA
  | fork _ ihm =>
      have wf0 := Typed0.wf ihm
      cases wf0 with | cons _ hA => exact .fork hA ihm
  | recv h _ ihm => exact .recv h ihm
  | send h _ ihm => exact .send h ihm
  | close _ ihm => exact .close ihm
  | conv c _ _ ihm ihB => exact .conv c ihm ihB
  | nil => exact .nil
  | cons _ _ ihwf ihty => exact .cons ihwf ihty

/-- The level-0 judgment implies the main one (Coq `Typed0.toTyped`). -/
lemma Typed0.toTyped {Γ m A} (h : Typed0 Γ m A) : Γ ⊢ m : A := by
  induction h using Typed0.rec (motive_2 := fun Γ _ => Wf Γ) with
  | srt _ ih => exact .srt ih
  | var _ hs ih => exact .var ih hs
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ _ ihm => exact .lam ihm
  | app _ _ ihm ihn => exact .app ihm ihn
  | sig h1 h2 _ _ ihA ihB => exact .sig h1 h2 ihA ihB
  | pair _ _ _ ihS ihm ihn => exact .pair ihS ihm ihn
  | proj _ _ _ ihC ihm ihn => exact .proj ihC ihm ihn
  | fix ar gr _ _ _ ihm => exact .fix ar gr ihm
  | unit _ ih => exact .unit ih
  | one _ ih => exact .one ih
  | bool _ ih => exact .bool ih
  | tt _ ih => exact .tt ih
  | ff _ ih => exact .ff ih
  | ite _ _ _ _ ihA ihm ihn1 ihn2 => exact .ite ihA ihm ihn1 ihn2
  | M _ ihA => exact .M ihA
  | pure _ ihm => exact .pure ihm
  | mlet _ _ _ ihB ihm ihn => exact .mlet ihB ihm ihn
  | proto _ ih => exact .proto ih
  | stop _ ih => exact .stop ih
  | act _ _ _ ihB => exact .act ihB
  | ch _ ihA => exact .ch ihA
  | chan _ _ ih ihA => exact .chan ih ihA
  | fork _ _ _ ihm => exact .fork ihm
  | recv h _ ihm => exact .recv h ihm
  | send h _ ihm => exact .send h ihm
  | close _ ihm => exact .close ihm
  | conv c _ _ ihm ihB => exact .conv c ihm ihB
  | nil => exact .nil
  | cons _ _ ihwf ihty => exact .cons ihwf ihty

/-- The level-0 well-formedness implies the main one (Coq `Wf0.toWf`). -/
lemma Wf0.toWf : ∀ {Γ}, Wf0 Γ → Wf Γ
  | _, .nil => .nil
  | _, .cons wf ty => .cons (Wf0.toWf wf) (Typed0.toTyped ty)

end TLLC.Static
