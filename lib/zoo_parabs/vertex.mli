type t

type task =
  unit Pool.task

val create :
  task option -> t

val task :
  t -> task
val set_task :
  t -> task -> unit

val precede :
  t -> t -> unit

val release :
  Pool.context -> t -> unit

val yield :
  Pool.context -> t -> task -> unit
