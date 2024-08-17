type 'a t =
  | ClstClosed
  | ClstOpen
  | ClstCons of 'a * 'a t

let rec app t1 t2 =
  match t1 with
  | ClstOpen ->
      t2
  | ClstCons (v, t1) ->
      ClstCons (v, app t1 t2)

let rec rev_app t1 t2 =
  match t1 with
  | ClstOpen ->
      t2
  | ClstCons (v, t1) ->
      rev_app t1 (ClstCons (v, t2))

let rec iter t fn =
  match t with
  | ClstOpen ->
      ()
  | ClstCons (v, t) ->
      fn v ;
      iter t fn
