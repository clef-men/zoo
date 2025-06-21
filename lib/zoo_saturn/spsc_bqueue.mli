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

predicate producer
  (t : val)
  (ws : list val)

predicate consumer
  (t : val)
|}]

val create :
  int -> 'a t
[@@zoo{|
  arguments
    cap
  requires
    0 ≤ cap
  returns
    ?t
  ensures
    inv ?t ι ₊cap
  , model ?t []
  , producer ?t []
  , consumer ?t
|}]

val size :
  'a t -> int
[@@zoo{|
  specification
    producer
  arguments
    t
  atomically
    ι
  requires
    inv t ι cap
  , producer t ws
  arequires
    model t ?vs
  aensures
    model t ?vs
  returns
    length ?vs
  ensures
    producer t ws
|}]
[@@zoo{|
  specification
    consumer
  arguments
    t
  atomically
    ι
  requires
    inv t ι cap
  , consumer t
  arequires
    model t ?vs
  aensures
    model t ?vs
  returns
    length ?vs
  ensures
    consumer t
|}]

val is_empty :
  'a t -> bool
[@@zoo{|
  specification
    producer
  arguments
    t
  atomically
    ι
  requires
    inv t ι cap
  , producer t ws
  arequires
    model t ?vs
  aensures
    model t ?vs
  decides
    ?vs = []
  ensures
    producer t ws
|}]
[@@zoo{|
  specification
    consumer
  arguments
    t
  atomically
    ι
  requires
    inv t ι cap
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
  'a t -> 'a -> bool
[@@zoo{|
  arguments
    t
  , v
  atomically
    ι
  requires
    inv t ι cap
  , producer t ws
  arequires
    model t ?vs
  aensures
    ?b = decide (length ?vs = cap)
  , model t (if ?b then ?vs else ?vs ++ [v])
  returns
    ?b
  ensures
    producer t (if ?b then ws else ?vs ++ [v])
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
  , consumer t
  arequires
    model t ?vs
  aensures
    model t (tail ?vs)
  returns
    head vs
  ensures
    consumer t
|}]
