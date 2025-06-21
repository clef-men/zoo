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

val size :
  'a t -> int
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
    ?sz
  ensures
    length ?vs ≤ ?sz
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
  arequires
    model t ?vs
  aensures
    model t ?vs
  returns
    ?b
  ensures
    if ?b then ?vs = [] else True
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
    ?vs = ?v :: ?vs'
  , model t ?vs'
  returns
    ?v
|}]
