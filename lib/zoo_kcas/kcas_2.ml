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
  { cmps: 'a cas list;
    mutable status: 'a status [@atomic];
    proph: (Zoo.id * bool) Zoo.proph;
  }

and 'a status =
  | Undetermined of 'a cas list [@zoo.reveal]
  | Before
  | After

let[@inline] status_to_bool status =
  status == After
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
      status_to_bool casn.status

let rec determine_as casn cass =
  let gid = Zoo.id in
  match cass with
  | [] ->
      let status =
        if Lst.forall (fun cas -> Atomic.get cas.loc == cas.state) casn.cmps then
          After
        else
          Before
      in
      finish gid casn status
  | cas :: cass' ->
      let { loc; state } = cas in
      let proph = Zoo.proph in
      let state' = Atomic.get loc in
      if state == state' then
        determine_as casn cass'
      else
        if Zoo.resolve (state.before != get_as state') proph () then
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
  let casn = { cmps= []; status= After; proph= Zoo.proph } in
  let state = { casn; before= v; after= v } in
  Atomic.make state

let get loc =
  get_as (Atomic.get loc)

let cas_2 cmps cass =
  let casn = { cmps; status= After; proph= Zoo.proph } in
  let cass =
    Lst.map (fun cas ->
      let loc, before, after = cas in
      let state = { casn; before; after } in
      { loc; state }
    ) cass
  in
  casn.status <- Undetermined cass ;
  determine_as casn cass
let rec cas_1 acc cmps cass =
  match cmps with
  | [] ->
      cas_2 (Lst.rev acc) cass
  | cmp :: cmps ->
      let loc, expected = cmp in
      let state = Atomic.get loc in
      if get_as state == expected then
        cas_1 ({ loc; state } :: acc) cmps cass
      else
        false
let cas cmps cass =
  cas_1 [] cmps cass
