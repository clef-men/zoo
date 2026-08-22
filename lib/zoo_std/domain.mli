type !'a t

val spawn :
  (unit -> 'a) -> 'a t

val join :
  'a t -> 'a

val yield :
  unit -> unit

val self_index  :
  unit -> int

val recommended_domain_count  :
  unit -> int

module Dls : sig
  type 'a key

  val new_key :
    (unit -> 'a) -> 'a key

  val get :
    'a key -> 'a

  val set :
    'a key -> 'a -> unit
end
