From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  glst__types.
From zoo Require Import
  options.

Definition glst_rev_app : val :=
  rec: "rev_app" "t1" "t2" =>
    match: "t1" with
    | Gnil =>
        "t2"
    | Gcons "v" "t1" =>
        "rev_app" "t1" ‘Gcons[ "v", "t2" ]
    end.

Definition glst_rev : val :=
  fun: "t" =>
    glst_rev_app "t" §Gnil.
