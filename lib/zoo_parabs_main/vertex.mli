type t

type task =
  bool Pool.task

val create :
  task option -> t
val create' :
  unit Pool.task -> t

val task :
  t -> task
val set_task :
  t -> task -> unit

val precede :
  t -> t -> unit

val release :
  Pool.context -> t -> unit

val yield :
  t -> task -> bool
