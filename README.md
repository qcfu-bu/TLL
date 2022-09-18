## Static Fragment
```
——————————
Γ ⊢ U : U

——————————
Γ ⊢ L : U

—————————————————
Γ, x : A ⊢ x : A

Γ ⊢ A : s   Γ, x : A ⊢ B : r
—————————————————————————————
Γ ⊢ Πt (x :s A).B : t

Γ ⊢ A : s   Γ, x : A ⊢ B : r
—————————————————————————————
Γ ⊢ Πt {x :s A}.B : t

Γ ⊢ Πt (x :s A).B : t    Γ, x : A ⊢ m : B
——————————————————————————————————————————
Γ ⊢ λt (x :s A).m : Πt (x :s A).B

Γ ⊢ Πt {x :s A}.B : t    Γ, x : A ⊢ m : B
——————————————————————————————————————————
Γ ⊢ λt {x :s A}.m : Πt {x :s A}.B

Γ ⊢ m : Πt (x :s A).B    Γ ⊢ n : A
———————————————————————————————————
Γ ⊢ m n : B[n/x]

Γ ⊢ m : Πt {x :s A}.B    Γ ⊢ n : A
———————————————————————————————————
Γ ⊢ m n : B[n/x]

Γ ⊢ B : s    Γ ⊢ m : A    A = B
————————————————————————————————
Γ ⊢ m : B
```

## Dynamic Fragment
```
Δ ▹ U
————————————————————————————
Γ, x : A; Δ, x :s A ⊨ x : A

Γ ⊢ Πt (x :s A).B : t    Γ, x : A; Δ, x :s A ⊨ m : B    Δ ▹ t
———————————————————————————————————————————————————————————————
Γ; Δ ⊨ λt (x :s A).m : Πt (x :s A).B

Γ ⊢ Πt {x :s A}.B : t    Γ, x : A; Δ ⊨ m : B    Δ ▹ t
———————————————————————————————————————————————————————
Γ; Δ ⊨ λt {x :s A}.m : Πt {x :s A}.B

(compatible with non-deterministic reduction)
Γ; Δ1 ⊨ m : Πt (x :s A).B    Γ; Δ2 ⊨ n : A     Δ2 ▹ s
———————————————————————————————————————————————————————
Γ; Δ1 ⊍ Δ2 ⊨ m n : B[n/x]

(only compatible with call-by-value reduction)
Γ; Δ1 ⊨ m : Πt (x :s A).B    Γ; Δ2 ⊨ n : A
———————————————————————————————————————————
Γ; Δ1 ⊍ Δ2 ⊨ m n : B[n/x]

Γ; Δ ⊨ m : Πt {x :s A}.B    Γ ⊢ n : A
——————————————————————————————————————
Γ; Δ ⊨ m n : B[n/x]

Γ ⊢ B : s    Γ; Δ ⊨ m : A     A = B
————————————————————————————————————
Γ; Δ ⊨ m : B
```

## Arity
```
——————————
arity(s,s)

arity(s,B)
———————————————————————
arity(s, ΠU {x :r A}.B)
```

## Constructor
```
X ∉ FV(m̄)
—————————————————
constr(X, s, X m̄)

t ⊑ s    positive(X, A)    x ∉ FV(B)    constr(X, s, B)
———————————————————————————————————————————————————————
constr(X, s, Πs (x :t A).B)

positive(X, A)    x ∉ FV(B)    constr(X, s, B)
——————————————————————————————————————————————
constr(X, s, Πs {x :t A}.B)

t ⊑ s    x ∉ FV(A)    constr(X, s, B)
—————————————————————————————————————
constr(X, s, Πs (x :t A).B)

x ∉ FV(A)    constr(X, s, B)
————————————————————————————
constr(X, s, Πs {x :t A}.B)
```

## Motive
```
motive(ΠU {x :r A}.B, t, I) = ΠU {x :r A}.motive(B, t, I)
motive(s, t, I) = ΠU {x :s I}.t
```

## Branch
```
br(Πs (x :t A).B, X, Q, c) = ΠL (x :t A).br(B, X, Q, c x)
br(Πs {x :t A}.B, X, Q, c) = ΠL {x :t A}.br(B, X, Q, c x)
br(X m̄, X, Q, c) = Q m̄ c

branch(A, I, Q, c) = (br(A, X, Q, c))[I/X]
```

## Static Inductive
```
arity(s, A)     constr(X, s, Cᵢ)
Γ ⊢ A : U     Γ, x : A ⊢ Cᵢ : s
————————————————————————————————
Γ ⊢ Indₛ(X : A){C̄} : A

I := Indₛ(X : A){C̄}    Γ ⊢ I : A
—————————————————————————————————
Γ ⊢ Constrₛ(i, I) : Cᵢ[I/X]

I := Indₛ(X : A){C̄}     arity(s, A)
Γ ⊢ n : I m̄      Γ ⊢ Q : motive(A, t, I)
Γ ⊢ fᵢ : branch(Cᵢ, I, Q, Constrₛ(i, I))
—————————————————————————————————————————
Γ ⊢ Case(n, Q){f̄} : Q m̄ n

Γ ⊢ A : U     Γ, x : A ⊢ m : A
———————————————————————————————
Γ ⊢ Fix(x : A).m : A
```

## Dynamic Inductive
```
I := Indₛ(X : A){C̄}     Γ ⊢ I : A
——————————————————————————————————
Γ; ⋅ ⊢ Constrₛ(i, I) : Cᵢ[I/X]

I := Indₛ(X : A){C̄}     arity(s, A)
Γ; Δ1 ⊨ n : I m̄      Γ ⊢ Q : motive(A, t, I)
Γ; Δ2 ⊨ fᵢ : branch(Cᵢ, I, Q, Constrₛ(i, I))
—————————————————————————————————————————————
Γ; Δ1 ⊍ Δ2 ⊨ Case(n, Q){f̄} : Q m̄ n

Γ ⊢ A : U     Γ, x : A; Δ, x : A ⊨ m : A     Δ ▹ U
———————————————————————————————————————————————————
Γ; Δ ⊨ Fix(x : A).m : A
```

## Theorems
- **Translation**  
  For dynamic typing `Γ; Δ ⊨ m : A` then static typing `Γ ⊢ m : A` is well-typed.
- **Validity**  
  For dynamic typing `Γ; Δ ⊨ m : A`, there exists sort `s` such that static typing `Γ ⊢ A : s` is well-typed.
- **Subject Reduction**  
  For dynamic typing `Γ; Δ ⊨ m : A`, if there is reduction `m ~> n` then `Γ; Δ ⊨ n : A` is well-typed.
