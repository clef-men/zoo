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

  val steal_to :
    'a t -> int -> int -> 'a option
  val steal_as :
    'a t -> int -> Random_round.t -> 'a option
end
