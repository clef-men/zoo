type 'a t =
  { data: 'a option array;
    mutable front: int [@atomic];
    mutable back: int [@atomic];
  }

let create sz =
  { data= Array.initi sz (fun () -> ref None);
    front= 0;
    back= 0;
  }

let rec push_aux slot o =
  if not @@ Atomic.compare_and_set slot None o then (
    Domain.cpu_relax () ;
    push_aux slot o
  )
let push t v =
  let data = t.data in
  let i = (Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1) mod Array.size data in
  push_aux (Array.unsafe_get data i) (Some v)

let rec pop_aux slot =
  match Atomic.get slot with
  | None ->
      pop_aux slot
  | Some v as o ->
      if Atomic.compare_and_set slot o None then (
        v
      ) else (
        Domain.cpu_relax () ;
        pop_aux slot
      )
let pop t =
  let data = t.data in
  let i = (Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1) mod Array.size data in
  pop_aux (Array.unsafe_get data i)
