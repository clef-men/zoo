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
|}]

val create :
  unit -> 'a t
[@@zoo{|
  returns
    ?t
  ensures
    inv ?t ι
  , model ?t []
  , owner ?t
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
  , owner t
  arequires
    model t ?vs
  aensures
    model t (?vs ++ [v])
  ensures
    owner t
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
  , owner t
  arequires
    model t ?vs
  aensures
    match ?o with
    | None ->
        ?vs = [] ∗
        model t []
    | Some v ->
        ∃ vs'.
        ?vs = vs' ++ [v] ∗
        model t vs'
    end
  returns
    ?o
  ensures
    owner t
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
  ensures
    head ?vs
|}]
