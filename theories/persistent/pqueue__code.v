From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Import
  lst.
From zoo.persistent Require Import
  pqueue__types.
From zoo Require Import
  options.

Definition pqueue_empty : val :=
  (§Nil, §Nil).

Definition pqueue_is_empty : val :=
  fun: "t" =>
    lst_is_empty "t".<front> and lst_is_empty "t".<back>.

Definition pqueue_push : val :=
  fun: "t" "v" =>
    ("t".<front>, ‘Cons( "v", "t".<back> )).

Definition pqueue_pop : val :=
  fun: "t" =>
    match: "t".<front> with
    | Cons "v" "front" =>
        ‘Some( ("v", ("front", "t".<back>)) )
    | Nil =>
        match: lst_rev "t".<back> with
        | Nil =>
            §None
        | Cons "v" "front" =>
            ‘Some( ("v", ("front", §Nil)) )
        end
    end.
