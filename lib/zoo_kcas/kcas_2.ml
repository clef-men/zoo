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
    proph: (bool, Zoo.id * bool) Zoo.proph;
  }

and 'a status =
  | Undetermined of
    { cmps: 'a cas list;
      cass: 'a cas list;
    }
    [@generative] [@zoo.reveal]
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
  | Undetermined { cmps; cass } as old_status ->
      let status =
        if status == Before then
          Before
        else if Lst.forall (fun cmp -> Atomic.get cmp.loc == cmp.state) cmps then
          After
        else
          Before
      in
      let is_after = status_to_bool status in
      if
        Zoo.resolve_with (
          Atomic.Loc.compare_and_set [%atomic.loc casn.status] old_status status
        ) casn.proph (gid, is_after)
      then
        clear cass is_after ;
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
      else if Zoo.resolve proph (state.before == eval old_state) then
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
  | Undetermined { cmps= _; cass }  ->
      determine_as casn cass

let make v =
  let _gid = Zoo.id () in
  let casn = { status= After; proph= Zoo.proph () } in
  let state = { casn; before= v; after= v } in
  Atomic.make state

let get loc =
  eval (Atomic.get loc)

let cas_2 cmps cass =
  let casn = { status= After; proph= Zoo.proph () } in
  let cass =
    cass |> Lst.map @@ fun cas ->
      let loc, before, after = cas in
      let state = { casn; before; after } in
      { loc; state }
  in
  casn.status <- Undetermined { cmps; cass } ;
  determine_as casn cass
let rec cas_1 acc cmps cass =
  match cmps with
  | [] ->
      cas_2 (Lst.rev acc) cass
  | cmp :: cmps ->
      let loc, expected = cmp in
      let state = Atomic.get loc in
      if eval state == expected then
        cas_1 ({ loc; state } :: acc) cmps cass
      else
        false
let cas cmps cass =
  cas_1 [] cmps cass
