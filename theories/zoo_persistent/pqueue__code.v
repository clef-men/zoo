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

Definition pqueue٠empty : val :=
  ([], []).

Definition pqueue٠is_empty : val :=
  fun: "t" =>
    lst٠is_empty "t".<front> and lst٠is_empty "t".<back>.

Definition pqueue٠push : val :=
  fun: "t" "v" =>
    ("t".<front>, "v" :: "t".<back>).

Definition pqueue٠pop : val :=
  fun: "t" =>
    match: "t".<front> with
    | "v" :: "front" =>
        ‘Some( ("v", ("front", "t".<back>)) )
    | [] =>
        match: lst٠rev "t".<back> with
        | [] =>
            §None
        | "v" :: "front" =>
            ‘Some( ("v", ("front", [])) )
        end
    end.
