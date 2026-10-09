(* Based on:
   https://github.com/ocaml-multicore/kcas/blob/44c732c83585f662abda0ef0984fdd2fe8990f4a/doc/gkmz-with-read-only-cmp-ops.md
*)

type 'a loc =
  'a state Atomic.t

and 'a state =
  { casn: casn
  ; mutable before: 'a
  ; mutable after: 'a
  }

and cas =
  Cas :
  { loc: 'a loc
  ; state: 'a state
  } ->
  cas

and casn =
  { mutable status: status [@atomic]
  ; proph: (Zoo.id * bool) Zoo.proph
  }

and status =
  | Undetermined of
    { cmps: cas list
    ; cass: cas list
    }
    [@generative] [@zoo.generative_strong]
  | Before
  | After

let verify cmps =
  cmps |> List.forall (function Cas cmp_r -> Atomic.get cmp_r.loc == cmp_r.state)

let clear cass is_after =
  if is_after then
    cass |> List.iter (function Cas cas_r -> cas_r.state.before <- cas_r.state.after)
  else
    cass |> List.iter (function Cas cas_r -> cas_r.state.after <- cas_r.state.before)

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
        else if verify cmps then
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
      let Cas { loc; state } = cas in
      let proph = Zoo.proph () in
      let old_state = Atomic.get loc in
      if state == old_state then
        determine_as casn continue
      else if Zoo.resolve proph (state.before == eval old_state) then
        lock casn loc old_state state retry continue
      else
        finish gid casn Before
and[@inline] lock : type a. casn -> a loc -> a state -> a state -> cas list -> cas list -> bool =
  fun casn loc old_state state retry continue ->
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
and eval : type a. a state -> a =
  fun state ->
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

let mcas_2 cmps cass =
  let casn = { status= After; proph= Zoo.proph () } in
  let cass =
    cass |> List.map @@ fun cas ->
      let loc, before, after = cas in
      let state = { casn; before; after } in
      Cas { loc; state }
  in
  casn.status <- Undetermined { cmps; cass } ;
  determine_as casn cass
let rec mcas_1 acc cmps cass =
  match cmps with
  | [] ->
      mcas_2 (List.rev acc) cass
  | cmp :: cmps ->
      let loc, expected = cmp in
      let state = Atomic.get loc in
      if eval state == expected then
        mcas_1 (Cas { loc; state } :: acc) cmps cass
      else
        false
let mcas cmps cass =
  mcas_1 [] cmps cass
