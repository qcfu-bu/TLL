(* 
Mergesort in OCaml 

reference benchmark for GC sequential msort in OCaml
0.51 real         0.50 user         0.01 sys
243.18 MB maximum resident set size
*)

let rec split xs =
  match xs with
  | [] -> ([], [])
  | [ x ] -> ([ x ], [])
  | x :: y :: zs ->
    let xs, ys = split zs in
    (x :: xs, y :: ys)

let rec merge xs ys =
  match (xs, ys) with
  | [], _ -> ys
  | _, [] -> xs
  | x :: xs', y :: ys' ->
    if x <= y then
      x :: merge xs' ys
    else
      y :: merge xs ys'

let rec msort zs =
  match zs with
  | [] -> []
  | [ x ] -> [ x ]
  | _ ->
    let xs, ys = split zs in
    merge (msort xs) (msort ys)

let rec mk_list (n : int) =
  if n <= 0 then
    []
  else
    n :: mk_list (n - 1)

let rec list_len xs =
  match xs with
  | [] -> 0
  | _ :: xs -> 1 + list_len xs

let _ =
  let test = mk_list (1000 * 1000) in
  let sorted = msort test in
  let len = list_len sorted in
  print_endline (string_of_int len)
