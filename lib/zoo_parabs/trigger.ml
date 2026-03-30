type t = (unit, (unit -> unit) Pool.task) Ivar_3.t

let create () =
  Ivar_3.create ()

let notify ctx t =
  let wakeups = Ivar_3.set t () in
  List.iter (fun wakeup -> wakeup ctx ()) wakeups
