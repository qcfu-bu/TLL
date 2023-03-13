
datavtype llist (A : vt@ype) =
  | Nil
  | Cons of (A, llist A)
  
val ls : llist(int) = Nil
val ls : llist(int) = Cons (1, ls)

fun free_llist {A :vt@ype}(xs : llist A, f : A -> void) : void =
  case xs of
  | ~Nil() => ()
  | ~Cons (x, ls) => (f x; free_llist(ls, f))

  
fun free_int (x : int) : void = ()
  
val p : (int, int) =
  case ls of
  | ~Nil() => (0, 0)
  | ~Cons (x, ls) => (free_llist(ls, free_int); (x, x))
