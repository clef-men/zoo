(* Based on:
   https://inria.hal.science/hal-01409022v1
*)

type t =
  { mutable task: unit Pool.task;
    mutable preds: int [@atomic];
    succs: t Mpmc_stack_2.t;
  }

type task =
  unit Pool.task

let create task =
  let task =
    match task with
    | Some task ->
        task
    | None ->
        fun _ -> ()
  in
  { task;
    preds= 1;
    succs= Mpmc_stack_2.create ();
  }

let task t =
  t.task

let set_task t task =
  t.task <- task

let precede t1 t2 =
  let succs1 = t1.succs in
  if not @@ Mpmc_stack_2.is_closed succs1 then (
    Atomic.Loc.fetch_and_add [%atomic.loc t2.preds] 1 |> ignore ;
    if Mpmc_stack_2.push succs1 t2 then
      Atomic.Loc.fetch_and_add [%atomic.loc t2.preds] (-1) |> ignore
  )

let rec release ctx t =
  if Atomic.Loc.fetch_and_add [%atomic.loc t.preds] (-1) == 1 then
    run ctx t
and run ctx t =
  Pool.async ctx @@ fun ctx ->
    t.preds <- 1 ;
    t.task ctx ;
    let succs = Mpmc_stack_2.close t.succs in
    Clst.iter (fun succ -> release ctx succ) succs

let yield ctx t task =
  set_task t task ;
  release ctx t
