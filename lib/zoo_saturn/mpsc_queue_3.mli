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
  (vs : option (list val))

predicate closed
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
  , consumer ?t None
|}]

val is_empty :
  'a t -> bool
[@@zoo{|
  specification
    open
  arguments
    t
  atomically
    ι
  requires
    inv t ι
  , consumer t None
  arequires
    model t ?vs
  aensures
    model t ?vs
  decides
    ?vs = []
  ensures
    consumer t None
|}]
[@@zoo{|
  specification
    closed
  arguments
    t
  requires
    inv t ι
  , consumer t (Some vs)
  decides
    vs = []
  ensures
    consumer t (Some vs)
|}]

val push_front :
  'a t -> 'a -> bool
[@@zoo{|
  specification
    open
  arguments
    t
  , v
  atomically
    ι
  requires
    inv t ι
  , consumer t None
  arequires
    model t ?vs
  aensures
    model t (v :: ?vs)
  returns
    false
  ensures
    consumer t None
|}]
[@@zoo{|
  specification
    closed
  arguments
    t
  , v
  atomically
    ι
  requires
    inv t ι
  , consumer t (Some vs)
  arequires
    model t ?vs'
  aensures
    ?b = decide (vs = [])
  , ?vs' = vs
  , model t (if ?b then [] else v :: vs)
  returns
    b
  ensures
    consumer t (Some (if ?b then [] else v :: vs))
|}]

val push_back :
  'a t -> 'a -> bool
[@@zoo{|
  specification
    open
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
    if ?closed then
      model t ?vs
    else
      model t (?vs ++ [v])
  returns
    ?closed
  ensures
    if ?closed then
      closed t
    else
      True
|}]
[@@zoo{|
  specification
    closed
  arguments
    t
  , v
  requires
    inv t ι
  , closed t
  returns
    true
|}]

val pop :
  'a t -> 'a option
[@@zoo{|
  specification
    open
  arguments
    t
  atomically
    ι
  requires
    inv t ι
  , consumer t None
  arequires
    model t ?vs
  aensures
    model t (tail ?vs)
  returns
    head ?vs
  ensures
    consumer t None
|}]
[@@zoo{|
  specification
    closed
  arguments
    t
  atomically
    ι
  requires
    inv t ι
  , consumer t (Some vs)
  arequires
    model t ?vs'
  aensures
    ?vs' = vs
  , model t (tail vs)
  returns
    head vs
  ensures
    consumer t (Some (tail vs))
|}]

val close :
  'a t -> bool
[@@zoo{|
  specification
    open
  arguments
    t
  atomically
    ι
  requires
    inv t ι
  , consumer t None
  arequires
    model t ?vs
  aensures
    model t ?vs
  returns
    false
  ensures
    consumer t (Some ?vs)
|}]
[@@zoo{|
  specification
    closed
  arguments
    t
  requires
    inv t ι
  , consumer t (Some vs)
  returns
    true
  ensures
    consumer t (Some vs)
|}]
