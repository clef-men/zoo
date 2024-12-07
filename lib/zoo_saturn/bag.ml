(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/65211c5176b632bd9ed268c0c608ac483f88a992/src_lockfree/mpmc_relaxed_queue.ml
*)

type 'a t =
  { data: 'a option Atomic.t array;
    mutable front: int [@atomic];
    mutable back: int [@atomic];
  }

let create sz =
  { data= Array.unsafe_init sz (fun () -> Atomic.make None);
    front= 0;
    back= 0;
  }

let rec push slot o =
  if not @@ Atomic.compare_and_set slot None o then (
    Domain.cpu_relax () ;
    push slot o
  )
let push t v =
  let data = t.data in
  let i = (Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1) mod Array.size data in
  push (Array.unsafe_get data i) (Some v)

let rec pop slot =
  match Atomic.get slot with
  | None ->
      pop slot
  | Some v as o ->
      if Atomic.compare_and_set slot o None then (
        v
      ) else (
        Domain.cpu_relax () ;
        pop slot
      )
let pop t =
  let data = t.data in
  let i = (Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1) mod Array.size data in
  pop (Array.unsafe_get data i)
