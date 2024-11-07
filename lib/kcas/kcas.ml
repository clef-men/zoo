(* Based on:
   https://github.com/ocaml-multicore/kcas/blob/44c732c83585f662abda0ef0984fdd2fe8990f4a/doc/gkmz-with-read-only-cmp-ops.md
*)

type 'a loc =
  'a state Atomic.t

and[@zoo.reveal] 'a state =
  { casn: 'a casn;
    before: 'a;
    after: 'a;
  }

and 'a cas =
  { loc: 'a loc;
    state: 'a state;
  }

and 'a casn =
  { mutable status: 'a status [@atomic];
    proph: (Zoo.id * bool) Zoo.proph;
  }

and 'a status =
  | Undetermined of 'a cas list [@zoo.reveal]
  | Before
  | After

let status_to_bool = function
  | Undetermined _ ->
      assert false
  | Before ->
      false
  | After ->
      true

let finish gid casn status =
  match casn.status with
  | Before ->
      false
  | After ->
      true
  | Undetermined _ as old_status ->
      Zoo.resolve (
        Atomic.Loc.compare_and_set [%atomic.loc casn.status] old_status status
      ) casn.proph (gid, status_to_bool status) |> ignore ;
      casn.status == After

let rec determine_as casn cass =
  let gid = Zoo.id in
  match cass with
  | [] ->
      finish gid casn After
  | cas :: cass' ->
      let { loc; state } = cas in
      let state' = Atomic.get loc in
      if state == state' then
        determine_as casn cass'
      else
        if state.before != get_as state' then
          finish gid casn Before
        else
          match casn.status with
          | Before ->
              false
          | After ->
              true
          | Undetermined _ ->
              if Atomic.compare_and_set loc state' state then
                determine_as casn cass'
              else
                determine_as casn cass
and get_as state =
  if determine state.casn then
    state.after
  else
    state.before
and determine casn =
  match casn.status with
  | Before ->
      false
  | After ->
      true
  | Undetermined cass ->
      determine_as casn cass

let make v =
  let _gid = Zoo.id in
  let casn = { status= After; proph= Zoo.proph } in
  let state = { casn; before= v; after= v } in
  Atomic.make state

let get loc =
  get_as (Atomic.get loc)

let cas cass =
  let casn = { status= After; proph= Zoo.proph } in
  let cass =
    Lst.map cass (fun cas ->
      let loc, before, after = cas in
      let state = { casn; before; after } in
      { loc; state }
    )
  in
  casn.status <- Undetermined cass ;
  determine_as casn cass
