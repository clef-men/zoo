type 'a t =
  | Closed
  | Open
  | Cons of 'a * 'a t [@generative]

let rec app t1 t2 =
  match t1 with
  | Closed ->
      assert false
  | Open ->
      t2
  | Cons (v, t1) ->
      Cons (v, app t1 t2)
[@@tail_mod_cons]

let rec rev_app t1 t2 =
  match t1 with
  | Closed ->
      assert false
  | Open ->
      t2
  | Cons (v, t1) ->
      rev_app t1 (Cons (v, t2))

let rec iter fn = function
  | Closed ->
      assert false
  | Open ->
      ()
  | Cons (v, t) ->
      fn v ;
      iter fn t
