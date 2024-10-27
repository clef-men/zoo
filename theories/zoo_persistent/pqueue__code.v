From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst.
From zoo_persistent Require Import
  pqueue__types.
From zoo Require Import
  options.

Definition pqueue_empty : val :=
  ([], []).

Definition pqueue_is_empty : val :=
  fun: "t" =>
    lst_is_empty "t".<front> and lst_is_empty "t".<back>.

Definition pqueue_push : val :=
  fun: "t" "v" =>
    ("t".<front>, "v" :: "t".<back>).

Definition pqueue_pop : val :=
  fun: "t" =>
    match: "t".<front> with
    | "v" :: "front" =>
        ‘Some( ("v", ("front", "t".<back>)) )
    | [] =>
        match: lst_rev "t".<back> with
        | [] =>
            §None
        | "v" :: "front" =>
            ‘Some( ("v", ("front", [])) )
        end
    end.
