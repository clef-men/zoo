type 'a node =
  { mutable xdeque_prev: 'a t;
    mutable xdeque_next: 'a t;
    mutable xdeque_data: 'a;
  }

and 'a t

val create :
  unit -> 'a t

val is_empty :
  'a t -> bool

val push_front :
  'a t -> 'a node -> unit
val push_back :
  'a t -> 'a node -> unit

val pop_front :
  'a t -> 'a node option
val pop_back :
  'a t -> 'a node option

val remove :
  'a node -> unit

val iter :
  'a t -> ('a node -> unit) -> unit
