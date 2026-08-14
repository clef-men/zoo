type 'a t

[@@@zoo{|
predicate inv
  (t : val)
  (ι : namespace)
persistent inv

predicate model
  (t : val)
  (vs : list val)

predicate consumer
  (t : val)
|}]

val create :
  unit -> 'a t
[@@zoo{|
  returns
    ?t
  ensures
    inv ?t ι
  , model ?t []
  , consumer ?t
|}]

val is_empty :
  'a t -> bool
[@@zoo{|
  arguments
    t
  atomically
    ι
  requires
    inv t ι
  , consumer t
  arequires
    model t ?vs
  aensures
    model t ?vs
  decides
    ?vs = []
  ensures
    consumer t
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
    model t (?vs ++ [v])
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
  , consumer t
  arequires
    model t ?vs
  aensures
    model t (tail ?vs)
  returns
    head ?vs
  ensures
    consumer t
|}]
