(* Based on:
   https://github.com/ocaml-multicore/kcas/blob/44c732c83585f662abda0ef0984fdd2fe8990f4a/doc/gkmz-with-read-only-cmp-ops.md
*)

type 'a loc =
  'a state Atomic.t

and 'a state =
  { casn: 'a casn;
    mutable before: 'a;
    mutable after: 'a;
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
  | Undetermined of { cass: 'a cas list } [@generative] [@zoo.reveal]
  | Before
  | After

let clear cass is_after =
  if is_after then
    Lst.iter (fun cas -> cas.state.before <- cas.state.after) cass
  else
    Lst.iter (fun cas -> cas.state.after <- cas.state.before) cass

let[@inline] status_to_bool status =
  status == After
let finish gid casn status =
  match casn.status with
  | Before ->
      false
  | After ->
      true
  | Undetermined undet_r as old_status ->
      let is_after = status_to_bool status in
      if
        Zoo.resolve (
          Atomic.Loc.compare_and_set [%atomic.loc casn.status] old_status status
        ) casn.proph (gid, is_after)
      then
        clear undet_r.cass is_after ;
      status_to_bool casn.status

let rec determine_as casn cass =
  let gid = Zoo.id () in
  match cass with
  | [] ->
      finish gid casn After
  | cas :: continue as retry ->
      let { loc; state } = cas in
      let proph = Zoo.proph () in
      let old_state = Atomic.get loc in
      if state == old_state then
        determine_as casn continue
      else
        if Zoo.resolve (state.before == eval old_state) proph () then
          lock casn loc old_state state retry continue
        else
          finish gid casn Before
and[@inline] lock casn loc old_state state retry continue =
  match casn.status with
  | Before ->
      false
  | After ->
      true
  | Undetermined _ ->
      if Atomic.compare_and_set loc old_state state then
        determine_as casn continue
      else
        determine_as casn retry
and eval state =
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
  | Undetermined undet_r ->
      determine_as casn undet_r.cass

let make v =
  let _gid = Zoo.id () in
  let casn = { status= After; proph= Zoo.proph () } in
  let state = { casn; before= v; after= v } in
  Atomic.make state

let get loc =
  eval (Atomic.get loc)

let cas cass =
  let casn = { status= After; proph= Zoo.proph () } in
  let cass =
    Lst.map (fun cas ->
      let loc, before, after = cas in
      let state = { casn; before; after } in
      { loc; state }
    ) cass
  in
  casn.status <- Undetermined { cass } ;
  determine_as casn cass
