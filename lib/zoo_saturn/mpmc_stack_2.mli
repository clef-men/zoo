type 'a t

[@@@zoo{|
predicate inv
  (t : val)
  (ι : namespace)
persistent inv

predicate model
  (t : val)
  (vs : option (list val))
|}]

val create :
  unit -> 'a t
[@@zoo{|
  returns
    ?t
  ensures
    inv ?t ι
  , model ?t (Some [])
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
    inv t ι
  arequires
    model t ?vs
  aensures
    model t (Option.map (cons v) ?vs)
  decides
    ?vs = None
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
  'a t -> 'a Optional.t
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
    model t (Option.map tail ?vs)
  returns
    Option.value Optional.Anything (Option.map (Optional.of_option ∘ head) ?vs)
|}]
[@@zoo{|
  specification
    closed
  arguments
    t
  requires
    inv t ι
  , closed t
  returns
    Optional.Anything
|}]

val is_closed :
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
  decides
    ?vs = None
|}]
[@@zoo{|
  specification
    closed
  arguments
    t
  requires
    inv t ι
  , closed t
  returns
    true
|}]

val close :
  'a t -> 'a Clst.t
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
    model t None
  returns
    Option.fold Clst.Closed Clst.of_lst_open ?vs
|}]
[@@zoo{|
  specification
    closed
  arguments
    t
  requires
    inv t ι
  , closed t
  returns
    Clst.Closed
|}]
