Require Import AutosubstSsr ARS tll_ast.

Class CRename (A : Type) := cren : (cvar -> cvar) -> A -> A.
Class CSubst (A : Type)  := csubst : (cvar -> term) -> A -> A.

Arguments cren {_ _} xi !m /.
Arguments csubst {_ _} sigma !m /.

