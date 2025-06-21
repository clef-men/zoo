type 'a t

[@@@zoo{|
predicate inv
  (t : val)
  (ι : namespace)
persistent inv

predicate model
  (t : val)
  (vs : list val)
|}]

val create :
  unit -> 'a t
[@@zoo{|
  returns
    ?t
  ensures
    inv ?t ι
  , model ?t []
|}]

val push :
  'a t -> 'a -> unit
[@@zoo{|
  arguments
    t
  , v
  atomically
    ι
  requires
    inv t ι
  arequires
    model t ?vs
  aensures
    model t (v :: ?vs)
|}]

val pop :
  'a t -> 'a option
[@@zoo{|
  arguments
    t
  atomically
    ι
  requires
    inv t ι
  arequires
    model t ?vs
  aensures
    model t (tail ?vs)
  returns
    head ?vs
|}]

val snapshot :
  'a t -> 'a Glst.t
[@@zoo{|
  arguments
    t
  atomically
    ι
  requires
    inv t ι
  arequires
    model t ?vs
  aensures
    model t ?vs
  returns
    ?l
  ensures
    Glst.model ?l ?vs
|}]
