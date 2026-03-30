type t =
  { mutable cond : (Mutex.t * Condition.t) option [@atomic]
  ; predicate: unit -> bool
  }

let create pred =
  { cond = None
  ; predicate= pred
  }

let[@inline] probe t =
  t.predicate ()

let notify t =
  match t.cond with
  | None -> ()
  | Some (mutex, condition) ->
     Mutex.protect mutex @@ fun () ->
     Condition.notify condition

let notify_weak t =
  notify t; true

let rec init_cond t =
  match t.cond with
  | Some cond -> cond
  | None ->
    let cond = (Mutex.create (), Condition.create ()) in
    if Atomic.Loc.compare_and_set [%atomic.loc t.cond] None (Some cond) then cond
    else init_cond t

let wait t =
  let (mutex, condition) = init_cond t in
  Mutex.protect mutex @@ fun () ->
    if probe t then (
      true
    ) else (
      Condition.wait condition mutex ;
      false
    )
