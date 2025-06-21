type 'a t

type 'a producer

type 'a consumer

[@@@zoo{|
predicate inv
  (t : val)
  (ι : namespace)
persistent inv

predicate model
  (t : val)
  (vss : map val (list val))

predicate producer
  (t : val)
  (producer : val)
  (ws : list val)

predicate consumer
  (t : val)
  (consumer : val)
|}]

val create :
  unit -> 'a t
[@@zoo{|
  returns
    ?t
  ensures
    inv ?t ι
  , model ?t ∅
|}]

val create_producer :
  'a t -> 'a producer
[@@zoo{|
  arguments
    t
  atomically
    ι
  requires
    inv t ι
  arequires
    model t ?vss
  aensures
    model t (?vss [?producer := []])
  returns
    ?producer
  ensures
    producer t ?producer []
|}]

val close_producer :
  'a producer -> unit
[@@zoo{|
  arguments
    producer
  requires
    inv t ι
  , producer t producer ws
  ensures
    producer t producer ws
|}]

val create_consumer :
  'a t -> 'a consumer
[@@zoo{|
  arguments
    t
  requires
    inv t ι
  returns
    ?consumer
  ensures
    consumer t ?consumer
|}]

val push :
  'a producer -> 'a -> unit
[@@zoo{|
  arguments
    producer
  , v
  atomically
    ι
  requires
    inv t ι
  , producer t producer ws
  arequires
    model t ?vss
  aensures
    vss [producer] = Some ?vs
  , model t (?vss [producer := ?vs ++ [v]])
  ensures
    producer t producer (?vs ++ [v])
|}]

val pop :
  'a t -> 'a consumer -> 'a option
[@@zoo{|
  arguments
    t
  , consumer
  atomically
    ι
  requires
    inv t ι
  , consumer t consumer
  arequires
    model t ?vss
  aensures
    match ?o with
    | None ->
        model t ?vss
    | Some v ->
        ∃ producer vs.
        ?vss [producer] = Some (v :: vs) ∗
        model t (?vss [producer := vs])
    end
  returns
    ?o
  ensures
    consumer t consumer
|}]
