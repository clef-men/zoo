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

let put t =
  let old = Atomic.Loc.fetch_and_add [%atomic.loc t.ops] (-1) in
  if old == 1 then
    match t.state with
    | Open _ ->
        ()
    | Closing no_users as prev ->
        if t.ops <= 0
        && Atomic.Loc.compare_and_set [%atomic.loc t.state] prev closed
        then
          no_users ()

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
  | Open fd as prev ->
      let close () = Unix.close fd in
      let next = Closing close in
      if Atomic.Loc.compare_and_set [%atomic.loc t.state] prev next then (
        if t.ops == 0
        && Atomic.Loc.compare_and_set [%atomic.loc t.state] next closed
        then
          close () ;
        true
      ) else (
        false
      )

let remove t =
  match t.state with
  | Closing _ ->
      None
  | Open fd as prev ->
      let waiter = Spsc_waiter.create () in
      let next = Closing (fun () -> Spsc_waiter.notify waiter) in
      if Atomic.Loc.compare_and_set [%atomic.loc t.state] prev next then (
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
