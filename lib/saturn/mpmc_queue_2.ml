(* Based on:
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

let rec rev (suffix : (_, [< `Cons]) front) prefix =
  let Cons _ as suffix = suffix in
  match prefix with
  | Back _ ->
      suffix
  | Snoc (i, v, prefix) ->
      rev (Cons (i, v, suffix)) prefix
let rev (back : (_, [< `Snoc]) back) =
  let Snoc (i, v, prefix) = back in
  rev (Cons (i, v, Front (i + 1))) prefix

let create () =
  { front= Front 1;
    back= Back { index= 0; move= Used };
  }

let rec size t =
  let front = t.front in
  let back = t.back in
  if front != t.front then
    size t
  else
    let i_front =
      match front with
      | Front i ->
          i
      | Cons (i, _, _) ->
          i
    in
    let i_back =
      match back with
      | Back back_r ->
          back_r.index
      | Snoc (i, _, _) ->
          i
    in
    i_back - i_front + 1

let is_empty t =
  size t == 0

let rec push_back_aux t v i back =
  let new_back = Snoc (i + 1, v, back) in
  if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back then (
    Domain.cpu_relax () ;
    push_back t v
  )
and push_back t v =
  let back = t.back in
  match back with
  | Snoc (i, _, _) ->
      push_back_aux t v i back
  | Back back_r ->
      match back_r.move with
      | Used ->
          push_back_aux t v back_r.index back
      | Snoc (i_move, _, _) as move ->
          begin match t.front with
          | Front i_front as front ->
              if i_move <= i_front
              || Atomic.Loc.compare_and_set [%atomic.loc t.front] front (rev move) then
                back_r.move <- Used
          | _ ->
              back_r.move <- Used
          end ;
          push_back t v

let rec push_front t v =
  match t.front with
  | Cons (i, _, _) as front ->
      let new_front = Cons (i - 1, v, front) in
      if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then (
        Domain.cpu_relax () ;
        push_front t v
      )
  | Front i_front as front ->
      match t.back with
      | Snoc (i_back, v_back, prefix) as back ->
          if i_front == i_back then (
            let prefix = Snoc (i_back, v, prefix) in
            let new_back = Snoc (i_back + 1, v_back, prefix) in
            if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back then (
              Domain.cpu_relax () ;
              push_front t v
            )
          ) else (
            let new_back = Back { index= i_back; move= back } in
            if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back then
              Domain.cpu_relax () ;
            push_front t v
          )
      | Back back_r as back ->
          match back_r.move with
          | Used ->
              if t.front == front then (
                let new_back = Snoc (back_r.index + 1, v, back) in
                if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back then (
                  Domain.cpu_relax () ;
                  push_front t v
                )
              ) else (
                push_front t v
              )
          | Snoc (i_move, _, _) as move ->
              begin match t.front with
              | Front i_front as front ->
                  if i_move <= i_front
                  || Atomic.Loc.compare_and_set [%atomic.loc t.front] front (rev move) then
                    back_r.move <- Used
              | _ ->
                  back_r.move <- Used
              end ;
              push_front t v

let rec pop_1 t front =
  match front with
  | Cons (_, v, new_front) ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then (
        Some v
      ) else (
        Domain.cpu_relax () ;
        pop t
      )
  | Front i_front as front ->
      match t.back with
      | Snoc (i_move, v, move_prefix) as move ->
          if i_front == i_move then (
            if Atomic.Loc.compare_and_set [%atomic.loc t.back] move move_prefix then
              Some v
            else
              pop t
          ) else (
            let (Back back_r as back : (_, [`Back]) back) = Back { index= i_move; move } in
            if Atomic.Loc.compare_and_set [%atomic.loc t.back] move back then
              let (Cons (_, v, new_front) : (_, [`Cons]) front) = rev move in
              if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then (
                back_r.move <- Used ;
                Some v
              ) else (
                Domain.cpu_relax () ;
                pop t
              )
            else
              pop t
          )
      | Back back_r ->
          match back_r.move with
          | Used ->
              pop_2 t front
          | Snoc (i_move, _, _) as move ->
              if i_front < i_move then
                let (Cons (_, v, new_front) : (_, [`Cons]) front) = rev move in
                if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then (
                  back_r.move <- Used ;
                  Some v
                ) else (
                  Domain.cpu_relax () ;
                  pop t
                )
              else
                pop_2 t front
and pop_2 t front =
  let front' = t.front in
  if front' == front then
    None
  else
    pop_1 t front'
and pop t =
  pop_1 t t.front
