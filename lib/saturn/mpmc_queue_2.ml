(* Based on:
   https://github.com/ocaml-multicore/saturn/pull/112
   https://github.com/ocaml-multicore/picos/blob/0c8d97df54b319ed4a7857d66f801b18a9e76f38/lib/picos_aux.mpmcq/picos_aux_mpmcq.ml
*)

type ('a, _) front =
  | Front :
    int ->
    ('a, [> `Front]) front
  | Cons :
    int * 'a * ('a, [`Front | `Cons]) front ->
    ('a, [> `Cons]) front

type ('a, _) back =
  | Back :
    { index: int;
      mutable move: ('a, [`Snoc | `Used]) back;
    } ->
    ('a, [> `Back]) back
  | Snoc :
    int * 'a * ('a, [`Back | `Snoc]) back ->
    ('a, [> `Snoc]) back
  | Used :
    ('a, [> `Used]) back

type 'a t =
  { mutable front: ('a, [`Front | `Cons]) front [@atomic];
    mutable back: ('a, [`Back | `Snoc]) back [@atomic];
  }

let rec rev (suffix : (_, [`Cons]) front) prefix =
  let Cons _ as suffix = suffix in
  match prefix with
  | Back _ ->
      suffix
  | Snoc (i, v, prefix) ->
      rev (Cons (i, v, suffix)) prefix
let rev (back : (_, [`Snoc]) back) =
  let Snoc (i, v, prefix) = back in
  rev (Cons (i, v, Front (i + 1))) prefix

let create () =
  { front= Front 1;
    back= Back { index= 0; move= Used };
  }

let rec push_aux t v i back =
  if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back (Snoc (i + 1, v, back)) then (
    Domain.cpu_relax () ;
    push t v
  )
and push t v =
  let back = t.back in
  match back with
  | Snoc (i, _, _) ->
      push_aux t v i back
  | Back back_r ->
      let i_back = back_r.index in
      match back_r.move with
      | Used ->
          push_aux t v i_back back
      | Snoc (i_move, _, _) as move ->
          begin match t.front with
          | Front i_front as front ->
              if i_front < i_move
              && Atomic.Loc.compare_and_set [%atomic.loc t.front] front (rev move) then
                back_r.move <- Used
          | _ ->
              ()
          end ;
          push_aux t v i_back back

let rec pop_1 t front =
  match front with
  | Cons (_, v, suffix) ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.front] front suffix then (
        Some v
      ) else (
        Domain.cpu_relax () ;
        pop t
      )
  | Front i_front as front ->
      match t.back with
      | Snoc (i_move, v, move_prefix) as move ->
          if i_front == i_move then (
            if Atomic.Loc.compare_and_set [%atomic.loc t.back] move move_prefix then (
              Some v
            ) else (
              pop t
            )
          ) else (
            let (Back _ as back : (_, [`Back]) back) = Back { index= i_move; move } in
            if Atomic.Loc.compare_and_set [%atomic.loc t.back] move back then
              pop_2 t front move back
            else
              pop t
          )
      | Back back_r as back ->
          match back_r.move with
          | Used ->
              pop_3 t front
          | Snoc _ as move ->
              pop_2 t front move back
and pop_2 t (front : (_, [`Front]) front) (move : (_, [`Snoc]) back) (back : (_, [`Back]) back) =
  let Front i_front as front = front in
  let Snoc (i_move, _, _) = move in
  let Back back_r = back in
  if i_front < i_move then (
    let (Cons (_, v, suffix) : (_, [`Cons]) front) = rev move in
    if Atomic.Loc.compare_and_set [%atomic.loc t.front] front suffix then (
      back_r.move <- Used ;
      Some v
    ) else (
      Domain.cpu_relax () ;
      pop t
    )
  ) else (
    pop_3 t front
  )
and pop_3 t front =
  let front' = t.front in
  if front' == front then
    None
  else
    pop_1 t front'
and pop t =
  pop_1 t t.front
