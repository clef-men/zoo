[@@@zoo.exclude]

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
    'a t -> int -> int -> (unit -> bool) -> 'a option
  val steal :
    'a t -> int -> int -> int -> 'a option

  val killed :
    'a t -> bool
  val kill :
    'a t -> unit

  val pop_steal_until :
    'a t -> int -> int -> (unit -> bool) -> 'a option
  val pop_steal :
    'a t -> int -> int -> int -> 'a option
end
