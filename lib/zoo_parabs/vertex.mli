type t

val create :
  bool Pool.task option -> t

val get_task :
  t -> bool Pool.task
val set_task :
  t -> bool Pool.task -> unit

val precede :
  t -> t -> unit

val release :
  Pool.context -> t -> unit
