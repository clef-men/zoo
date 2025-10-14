type 'a t

[@@@zoo{|
predicate inv
  (t : val)
  (ι : namespace)
persistent inv

predicate model
  (t : val)
  (vs : list val)

predicate owner
  (t : val)
  (ws : list val)
|}]

val create :
  unit -> 'a t
[@@zoo{|
  returns
    ?t
  ensures
    inv ?t ι
  , model ?t []
  , owner ?t []
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
  , owner t ws
  arequires
    model t ?vs
  aensures
    suffix ?vs ws
  , model t ?vs
  returns
    length ?vs
  ensures
    owner t ?vs
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
  , owner t ws
  arequires
    model t ?vs
  aensures
    suffix ?vs ws
  , model t ?vs
  decides
    ?vs = []
  ensures
    owner t ?vs
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
  , owner t ws
  arequires
    model t ?vs
  aensures
    suffix ?vs ws
  , model t (?vs ++ [v])
  ensures
    owner t (?vs ++ [v])
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
  , owner t ws
  arequires
    model t ?vs
  aensures
    suffix ?vs ws
  , match ?o with
    | None ->
        ?vs = [] ∗
        ?ws' = [] ∗
        model t []
    | Some v ->
        ∃ vs'.
        ?vs = vs' ++ [v] ∗
        ?ws' = vs' ∗
        model t vs'
    end
  returns
    ?o
  ensures
    owner t ?ws'
|}]

val steal :
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
