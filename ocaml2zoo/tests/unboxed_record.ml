type[@unboxed] 'a t =
  { f: 'a;
  }

let test1 x =
  { f= x }

let test2 t =
  match t with
  | { f= x } ->
      x

let test3 t =
  let { f= x } = t in
  x
