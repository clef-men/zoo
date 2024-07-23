type[@unboxed] 'a t =
  T of 'a

let test1 x =
  T x

let test2 x =
  match x with
  | T x ->
      x

let test3 x =
  let T x = x in
  x
