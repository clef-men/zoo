Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.list.
Require Import zoo_persistent.pqueue__types.
Require Import zoo.options.

Definition pqueue٠empty : val :=
  ([], []).

Definition pqueue٠is_empty : val :=
  fun: "t" =>
    list٠is_empty "t".<front> and list٠is_empty "t".<back>.

Definition pqueue٠push : val :=
  fun: "t" "v" =>
    ("t".<front>, "v" :: "t".<back>).

Definition pqueue٠pop : val :=
  fun: "t" =>
    match: "t".<front> with
    | "v" :: "front" =>
        ‘Some( ("v", ("front", "t".<back>)) )
    | [] =>
        match: list٠rev "t".<back> with
        | [] =>
            §None
        | "v" :: "front" =>
            ‘Some( ("v", ("front", [])) )
        end
    end.
