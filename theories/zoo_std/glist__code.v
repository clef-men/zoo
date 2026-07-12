Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.glist__types.
Require Import zoo.options.

Definition glist٠rev_app : val :=
  rec: "rev_app" "t1" "t2" =>
    match: "t1" with
    | Gnil =>
        "t2"
    | Gcons "v" "t1" =>
        "rev_app" "t1" ‘Gcons[ "v", "t2" ]
    end.

Definition glist٠rev : val :=
  fun: "t" =>
    glist٠rev_app "t" §Gnil.
