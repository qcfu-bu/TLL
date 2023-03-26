let bits_of_char c =
  let rec loop n sz acc =
    if sz <= 0 then
      acc
    else
      let b = n land 1 = 1 in
      let n = n lsr 1 in
      loop n (sz - 1) (b :: acc)
  in
  loop (Char.code c) 8 []

let char_of_bits bs =
  let n =
    List.fold_left
      (fun n -> function
        | true -> (n lsl 1) lor 1
        | false -> n lsl 1)
      0 bs
  in
  Char.chr n
