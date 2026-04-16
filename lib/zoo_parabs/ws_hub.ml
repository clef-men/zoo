[@@@zoo.ignore]

module type S = sig
  type 'a t

  val create :
    int -> 'a t

  val size :
    'a t -> int

  val block :
    'a t -> int -> unit
  val unblock :
    'a t -> int -> unit

  val push :
    'a t -> int -> 'a -> unit
  val pop :
    'a t -> int -> 'a option

  val steal_until :
    'a t ->
    int ->
    max_round_noyield:int ->
    max_round_yield:int ->
    notification:((unit -> unit) -> unit) ->
    pred:(unit -> bool) ->
    'a option
  val steal :
    'a t ->
    int ->
    max_round_noyield:int ->
    max_round_yield:int ->
    'a option

  val closed :
    'a t -> bool
  val close :
    'a t -> unit

  val pop_steal_until :
    'a t ->
    int ->
    max_round_noyield:int ->
    max_round_yield:int ->
    notification:((unit -> unit) -> unit) ->
    pred:(unit -> bool) ->
    'a option
  val pop_steal :
    'a t ->
    int ->
    max_round_noyield:int ->
    max_round_yield:int ->
    'a option
end
