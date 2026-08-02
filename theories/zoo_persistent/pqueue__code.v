Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.list.
Require Import zoo.options.

Notation "'pqueue٠front'" := (
  in_type "zoo_persistent.pqueue.t" 0
)(in custom zoo_proj
).
Notation "'pqueue٠back'" := (
  in_type "zoo_persistent.pqueue.t" 1
)(in custom zoo_proj
).

Definition pqueue٠empty : val :=
  ([], []).

Definition pqueue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    list٠is_empty "t".<pqueue٠front>
    𝗮𝗻𝗱
    list٠is_empty "t".<pqueue٠back>.

Definition pqueue٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    ("t".<pqueue٠front>, "v" :: "t".<pqueue٠back>).

Definition pqueue٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".<pqueue٠front> 𝘄𝗶𝘁𝗵
    | "v" :: "front" ->
        ‘Some( ("v", ("front", "t".<pqueue٠back>)) )
    | [] ->
        𝗺𝗮𝘁𝗰𝗵 list٠rev "t".<pqueue٠back> 𝘄𝗶𝘁𝗵
        | [] ->
            §None
        | "v" :: "front" ->
            ‘Some( ("v", ("front", [])) )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
