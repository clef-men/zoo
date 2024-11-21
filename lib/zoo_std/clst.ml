type 'a t =
  | ClstClosed
  | ClstOpen
  | ClstCons of 'a * 'a t

let[@tail_mod_cons] rec app t1 t2 =
  match t1 with
  | ClstClosed ->
      assert false
  | ClstOpen ->
      t2
  | ClstCons (v, t1) ->
      ClstCons (v, app t1 t2)

let rec rev_app t1 t2 =
  match t1 with
  | ClstClosed ->
      assert false
  | ClstOpen ->
      t2
  | ClstCons (v, t1) ->
      rev_app t1 (ClstCons (v, t2))

let rec iter fn t =
  match t with
  | ClstClosed ->
      assert false
  | ClstOpen ->
      ()
  | ClstCons (v, t) ->
      fn v ;
      iter fn t
