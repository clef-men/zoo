Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.list.
Require Import zoo_persistent.pqueue__types.
Require Import zoo.options.

Definition pqueue٠empty : val :=
  ([], []).

Definition pqueue٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    list٠is_empty "t".<front> 𝗮𝗻𝗱 list٠is_empty "t".<back>.

Definition pqueue٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    ("t".<front>, "v" :: "t".<back>).

Definition pqueue٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t".<front> 𝘄𝗶𝘁𝗵
    | "v" :: "front" ->
        ‘Some( ("v", ("front", "t".<back>)) )
    | [] ->
        𝗺𝗮𝘁𝗰𝗵 list٠rev "t".<back> 𝘄𝗶𝘁𝗵
        | [] ->
            §None
        | "v" :: "front" ->
            ‘Some( ("v", ("front", [])) )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
