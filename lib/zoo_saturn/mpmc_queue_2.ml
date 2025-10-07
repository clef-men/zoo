(* Based on:
   https://github.com/ocaml-multicore/picos/blob/0c8d97df54b319ed4a7857d66f801b18a9e76f38/lib/picos_aux.mpmcq/picos_aux_mpmcq.ml
*)

type ('a, _) suffix =
  | Front :
    int ->
    ('a, [> `Front]) suffix
    [@generative]
  | Cons :
    int * 'a * ('a, [`Front | `Cons]) suffix ->
    ('a, [> `Cons]) suffix
    [@generative]

type ('a, _) prefix =
  | Back :
    { index: int;
      mutable move: ('a, [`Snoc | `Used]) prefix;
    } ->
    ('a, [> `Back]) prefix
  | Snoc :
    int * 'a * ('a, [`Back | `Snoc]) prefix ->
    ('a, [> `Snoc]) prefix
    [@generative]
  | Used :
    ('a, [> `Used]) prefix

type 'a t =
  { mutable front: ('a, [`Front | `Cons]) suffix [@atomic];
    mutable back: ('a, [`Back | `Snoc]) prefix [@atomic];
  }

let suffix_index suff =
  match suff with
  | Front i ->
      i
  | Cons (i, _, _) ->
      i

let prefix_index (pref : (_, [`Back | `Snoc]) prefix) =
  match pref with
  | Back back_r ->
      back_r.index
  | Snoc (i, _, _) ->
      i

let rec rev (suff : (_, [< `Cons]) suffix) pref =
  let Cons _ as suff = suff in
  match pref with
  | Back _ ->
      suff
  | Snoc (i, v, pref) ->
      rev (Cons (i, v, suff)) pref
let rev (back : (_, [< `Snoc]) prefix) =
  let Snoc (i, v, pref) = back in
  rev (Cons (i, v, Front (i + 1))) pref

let create () =
  { front= Front 1;
    back= Back { index= 0; move= Used };
  }

let rec size t =
  let front = t.front in
  let proph = Zoo.proph () in
  let back = t.back in
  if Zoo.resolve proph (t.front == front) then
    prefix_index back - suffix_index front + 1
  else
    size t

let is_empty t =
  size t == 0

let finish (back : (_, [< `Back]) prefix) =
  let Back back_r = back in
  back_r.move <- Used

let help t back i_move move =
  match t.front with
  | Front i_front as front ->
      if i_move < i_front
      || Atomic.Loc.compare_and_set [%atomic.loc t.front] front (rev move)
      then
        finish back
  | _ ->
      finish back

let rec push_aux t v i back =
  let new_back = Snoc (i + 1, v, back) in
  if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back then (
    Domain.yield () ;
    push t v
  )
and push t v =
  match t.back with
  | Snoc (i, _, _) as back ->
      push_aux t v i back
  | Back back_r as back ->
      match back_r.move with
      | Used ->
          push_aux t v back_r.index back
      | Snoc (i_move, _, _) as move ->
          help t back i_move move ;
          push t v

let rec pop_1 t front =
  match front with
  | Cons (_, v, new_front) ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then (
        Some v
      ) else (
        Domain.yield () ;
        pop t
      )
  | Front i_front as front ->
      (* let proph = Zoo.proph () in *)
      match t.back with
      | Snoc (i_move, v, move_pref) as move ->
          if i_front == i_move then (
            if Atomic.Loc.compare_and_set [%atomic.loc t.back] move move_pref then
              Some v
            else
              pop t
          ) else (
            let (Back _ as back : (_, [`Back]) prefix) = Back { index= i_move; move } in
            let front' = t.front in
            if front' != front then
              pop_1 t front'
            else if Atomic.Loc.compare_and_set [%atomic.loc t.back] move back then
              pop_2 t front back move
            else
              pop t
          )
      (* | Back back_r as back -> *)
      (*     match back_r.move with *)
      (*     | Used -> *)
      (*         pop_3 t proph front *)
      (*     | Snoc (i_move, _, _) as move -> *)
      (*         if i_front < i_move then ( *)
      (*           Zoo.resolve_silent proph false ; *)
      (*           pop_2 t front back move *)
      (*         ) else ( *)
      (*           pop_3 t proph front *)
      (*         ) *)
      | Back _ ->
          pop_3 t front
and pop_2 t front back move =
  let (Cons (_, v, new_front) : (_, [`Cons]) suffix) = rev move in
  if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then (
    finish back ;
    Some v
  ) else (
    Domain.yield () ;
    pop t
  )
(* and pop_3 t proph front = *)
and pop_3 t front =
  let front' = t.front in
  (* if Zoo.resolve proph (front' == front) then *)
  if front' == front then
    None
  else
    pop_1 t front'
and pop t =
  pop_1 t t.front
