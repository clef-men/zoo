type 'a t =
  | ClistClosed
  | ClistOpen
  | ClistCons of 'a * 'a t [@generative]

let[@tail_mod_cons] rec app t1 t2 =
  match t1 with
  | ClistClosed ->
      assert false
  | ClistOpen ->
      t2
  | ClistCons (v, t1) ->
      ClistCons (v, app t1 t2)

let rec rev_app t1 t2 =
  match t1 with
  | ClistClosed ->
      assert false
  | ClistOpen ->
      t2
  | ClistCons (v, t1) ->
      rev_app t1 (ClistCons (v, t2))

let rec iter fn = function
  | ClistClosed ->
      assert false
  | ClistOpen ->
      ()
  | ClistCons (v, t) ->
      fn v ;
      iter fn t
