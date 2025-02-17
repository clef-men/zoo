(* Based on:
   https://inria.hal.science/hal-01409022v1
*)

type t =
  { task: unit Pool.task;
    mutable preds: int [@atomic];
    succs: t Mpmc_stack_2.t;
  }

let create task =
  { task;
    preds= 1;
    succs= Mpmc_stack_2.create ();
  }

let precede t1 t2 =
  let succs1 = t1.succs in
  if not @@ Mpmc_stack_2.is_closed succs1 then (
    Atomic.Loc.fetch_and_add [%atomic.loc t2.preds] 1 |> ignore ;
    if Mpmc_stack_2.push succs1 t2 then (
      Atomic.Loc.fetch_and_add [%atomic.loc t2.preds] (-1) |> ignore ;
      ()
    )
  )

let propagate ctx t run =
  if Atomic.Loc.fetch_and_add [%atomic.loc t.preds] (-1) == 1 then
    Pool.silent_async ctx (fun ctx -> run ctx t)
let rec run ctx t =
  t.task ctx ;
  let succs = Mpmc_stack_2.close t.succs in
  Clst.iter (fun t' -> propagate ctx t' run) succs
let release ctx t =
  propagate ctx t run
