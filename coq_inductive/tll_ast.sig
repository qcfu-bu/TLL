-- builtin
name : Type
list : Functor

-- types
sort : Type
term : Type
tele : Type

-- constructors of sort
U : sort
L : sort

-- constructors of term
Sort  : sort -> term
Const : name -> term
Pi0 : term -> (term -> term) -> sort -> term
Pi1 : term -> (term -> term) -> sort -> term
Lam0 : term -> (term -> term) -> sort -> term
Lam1 : term -> (term -> term) -> sort -> term
App0 : term -> term -> term
App1 : term -> term -> term
Ind0 : name -> "list" (term) -> term
Ind1 : name -> "list" (term) -> term
Cons0 : name -> "list" (term) -> term
Cons1 : name -> "list" (term) -> term
Case0 : term -> tele -> "list" (tele) -> term
Case1 : term -> tele -> "list" (tele) -> term
Fix : term -> (term -> term) -> term

-- constructors of tele
Base : term -> tele
Bind0 : term -> (term -> tele) -> term
Bind1 : term -> (term -> tele) -> term

