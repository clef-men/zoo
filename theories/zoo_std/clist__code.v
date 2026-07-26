Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.clist__types.
Require Import zoo.options.

Definition clist٠app : val :=
  𝗿𝗲𝗰 "app" "t1" "t2" ->
    𝗺𝗮𝘁𝗰𝗵 "t1" 𝘄𝗶𝘁𝗵
    | ClistClosed ->
        𝗳𝗮𝗶𝗹
    | ClistOpen ->
        "t2"
    | ClistCons "v" "t1" ->
        ‘ClistCons[ "v", "app" "t1" "t2" ]
    𝗲𝗻𝗱.

Definition clist٠rev_app : val :=
  𝗿𝗲𝗰 "rev_app" "t1" "t2" ->
    𝗺𝗮𝘁𝗰𝗵 "t1" 𝘄𝗶𝘁𝗵
    | ClistClosed ->
        𝗳𝗮𝗶𝗹
    | ClistOpen ->
        "t2"
    | ClistCons "v" "t1" ->
        "rev_app" "t1" ‘ClistCons[ "v", "t2" ]
    𝗲𝗻𝗱.

Definition clist٠iter : val :=
  𝗿𝗲𝗰 "iter" "fn" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | ClistClosed ->
        𝗳𝗮𝗶𝗹
    | ClistOpen ->
        ()
    | ClistCons "v" "t" ->
        "fn" "v" ⍮
        "iter" "fn" "t"
    𝗲𝗻𝗱.
