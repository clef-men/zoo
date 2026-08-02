type 'a t =
  | Nil
  | Cons of 'a * 'a t [@generative]

let rec rev_app t1 t2 =
  match t1 with
  | Nil ->
      t2
  | Cons (v, t1) ->
      rev_app t1 (Cons (v, t2))

let rev t =
  rev_app t Nil
