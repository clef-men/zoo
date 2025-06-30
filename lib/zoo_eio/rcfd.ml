(* Based on:
   https://github.com/ocaml-multicore/eio/blob/964ed2730593339219a03636bbefa443d310c8c9/lib_eio/unix/rcfd.ml
*)

type state =
  | Open of Unix.file_descr [@generative] [@zoo.reveal]
  | Closing of (unit -> unit) [@generative]

type t =
  { mutable ops: int [@atomic];
    mutable state: state [@atomic];
  }

let make fd =
  { ops= 0; state= Open fd }

let closed =
  Closing (fun () -> ())

let[@inline] finish t close state =
  if t.ops == 0
  && Atomic.Loc.compare_and_set [%atomic.loc t.state] state closed
  then
    close ()

let put t =
  let old = Atomic.Loc.fetch_and_add [%atomic.loc t.ops] (-1) in
  if old == 1 then
    match t.state with
    | Open _ ->
        ()
    | Closing close as state ->
        finish t close state

let get t =
  Atomic.Loc.incr [%atomic.loc t.ops] ;
  match t.state with
  | Open fd ->
      Some fd
  | Closing _ ->
      put t ;
      None

let use t closed open_ =
  match get t with
  | None ->
      closed ()
  | Some fd ->
      let res = open_ fd in
      put t ;
      res

let close t =
  match t.state with
  | Closing _ ->
      false
  | Open fd as state ->
      let close () = Unix.close fd in
      let new_state = Closing close in
      if Atomic.Loc.compare_and_set [%atomic.loc t.state] state new_state then (
        finish t close new_state ;
        true
      ) else (
        false
      )

let remove t =
  match t.state with
  | Closing _ ->
      None
  | Open fd as state ->
      let waiter = Spsc_waiter.create () in
      let new_state = Closing (fun () -> Spsc_waiter.notify waiter) in
      if Atomic.Loc.compare_and_set [%atomic.loc t.state] state new_state then (
        Spsc_waiter.wait waiter ;
        Some fd
      ) else (
        None
      )

let is_open t =
  match t.state with
  | Open _ ->
      true
  | Closing _ ->
      false

let peek t =
  match t.state with
  | Open fd ->
      Some fd
  | Closing _ ->
      None
