type 'a t

[@@@zoo{|
predicate inv
  (t : val)
  (ι : namespace)
persistent inv

predicate model
  (t : val)
  (vs : multiset val)
|}]

val create :
  int -> 'a t
[@@zoo{|
  arguments
    sz
  requires
    0 < sz
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
    model t ({v} ⊎ ?vs)
|}]

val pop :
  'a t -> 'a
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
    ?vs = {?v} ⊎ ?vs'
  , model t ?vs'
  returns
    ?v
|}]
