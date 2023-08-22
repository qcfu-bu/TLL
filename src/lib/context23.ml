open Fmt
open Bindlib
open Names
open Syntax2
open Pprint2

module Ctx = struct
  (* Constructors can be unboxed in the following scenarios:

     1. All constructors carry no relevant information.
        Constructors unbox to a single c_tag.

        Example:
        inductive bool : U where
        | true  : bool
        | false : bool

     2. An inductive has only a single constructor contain a
        single piece of relevant information. A constructor of
        this inductive type unboxes to expose its relevant payload.

        Examples:
        inductive sing (A : Type) : Type where
        | just (m : A) : sing A

        inductive exists (A : Type) (B : A -> Type) : Type where
        | ex (m : A) {n : B m} : exists A B

     Other inductive declarations must remain boxed. *)
  type entry =
    { layout : relv list
    ; unbox : bool
    }

  type t = entry Constr.Map.t

  let empty = Constr.Map.empty
  let add_constr c entry (ctx : t) = Constr.Map.add c entry ctx
  let find_constr c (ctx : t) = Constr.Map.find c ctx
end
