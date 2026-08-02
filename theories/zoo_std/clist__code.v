Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'clist٠Closed'" := (
  in_type "zoo_std.clist.t" 0
)(in custom zoo_tag
).
Notation "'clist٠Open'" := (
  in_type "zoo_std.clist.t" 1
)(in custom zoo_tag
).
Notation "'clist٠Cons'" := (
  in_type "zoo_std.clist.t" 2
)(in custom zoo_tag
).

Definition clist٠app : val :=
  𝗿𝗲𝗰 "app" "t1" "t2" ->
    𝗺𝗮𝘁𝗰𝗵 "t1" 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        𝗳𝗮𝗶𝗹
    | clist٠Open ->
        "t2"
    | clist٠Cons "v" "t1" ->
        ‘clist٠Cons[ "v", "app" "t1" "t2" ]
    𝗲𝗻𝗱.

Definition clist٠rev_app : val :=
  𝗿𝗲𝗰 "rev_app" "t1" "t2" ->
    𝗺𝗮𝘁𝗰𝗵 "t1" 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        𝗳𝗮𝗶𝗹
    | clist٠Open ->
        "t2"
    | clist٠Cons "v" "t1" ->
        "rev_app" "t1" ‘clist٠Cons[ "v", "t2" ]
    𝗲𝗻𝗱.

Definition clist٠iter : val :=
  𝗿𝗲𝗰 "iter" "fn" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        𝗳𝗮𝗶𝗹
    | clist٠Open ->
        ()
    | clist٠Cons "v" "t" ->
        "fn" "v" ⍮
        "iter" "fn" "t"
    𝗲𝗻𝗱.
