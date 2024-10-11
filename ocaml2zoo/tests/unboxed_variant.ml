type[@unboxed] 'a t =
  T of 'a

let test1 x =
  T x

let test2 t =
  match t with
  | T x ->
      x

let test3 t =
  let T x = t in
  x
