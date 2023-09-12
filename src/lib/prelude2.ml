open Names
open Trans12

let find_ex1 () =
  let ex1U_constr = State.find_constr Prelude1.ex1_constr [U;L] in
  let ex1L_constr = State.find_constr Prelude1.ex1_constr [L;L] in
  (ex1U_constr, ex1L_constr)
