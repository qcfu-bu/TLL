open Fmt
open Bindlib
open TLL
open Names
open Syntax0

let test0 = Lam (R, U, Binder ("x", Id "x"))

let test1 =
  Lam (R, U, Binder ("x", Lam (N, L, Binder ("y", App [ Id "x"; Id "y" ]))))

let test2 =
  DTm
    ( R,
      "identity",
      ABind
        ( N,
          Type U,
          Binder
            ("A", ABind (R, Id "A", Binder ("x", ABase (Id "identity", Id "A"))))
        ) )

let _, test3 = Trans01.trans_dcls [] [ test2; test2 ]
let test3 = unbox test3
let _ = pr "%a@." Pprint1.pp_dcls test3
