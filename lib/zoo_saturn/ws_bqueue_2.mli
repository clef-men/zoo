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

predicate owner
  (t : val)
  (ws : list val)
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
  , owner ?t []
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
  , owner t ws
  arequires
    model t ?vs
  aensures
    ?b = decide (length ?vs < cap)
  , model t (if ?b then ?vs ++ [v] else ?vs)
  returns
    ?b
  ensures
    owner t (if ?b then ?vs ++ [v] else ws)
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
  , owner t ws
  arequires
    model t ?vs
  aensures
    match ?o with
    | None ->
        ?vs = [] ∗
        ws = [] ∗
        model t []
    | Some v ->
        ∃ vs'.
        ?vs = vs' ++ [v] ∗
        ws = vs' ∗
        model t vs'
    end
  returns
    ?o
  ensures
    owner t ws
|}]

val steal :
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
