type 'a t

[@@@zoo{|
predicate inv
  (t : val)
  (ι : namespace)
  (cap : nat)
persistent inv

predicate model
  (t : val)
  (vs : list val)
|}]

val create :
  int -> 'a t
[@@zoo{|
  arguments
    cap
  requires
    0 < cap
  returns
    ?t
  ensures
    inv ?t ι ₊cap
  , model ?t []
|}]

val capacity :
  'a t -> int
[@@zoo{|
  arguments
    t
  requires
    inv t ι cap
  returns
    cap
|}]

val size :
  'a t -> int
[@@zoo{|
  arguments
    t
  atomically
    ι
  requires
    inv t ι cap
  arequires
    model t ?vs
  aensures
    model t ?vs
  returns
    length ?vs
|}]

val is_empty :
  'a t -> bool
[@@zoo{|
  arguments
    t
  atomically
    ι
  requires
    inv t ι cap
  arequires
    model t ?vs
  aensures
    model t ?vs
  decides
    ?vs = []
|}]

val push :
  'a t -> 'a -> bool
[@@zoo{|
  arguments
    t
  , v
  atomically
    ι
  requires
    inv t ι cap
  arequires
    model t ?vs
  aensures
    ?b = decide (length ?vs < cap)
  , model t (if ?b then ?vs ++ [v] else ?vs)
  returns
    ?b
|}]

val pop :
  'a t -> 'a option
[@@zoo{|
  arguments
    t
  atomically
    ι
  requires
    inv t ι cap
  arequires
    model t ?vs
  aensures
    model t (tail ?vs)
  returns
    head ?vs
|}]
