From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Import
  lst.
From zoo.persistent Require Import
  pstack__types.
From zoo Require Import
  options.

Definition pstack_empty : val :=
  §Nil.

Definition pstack_is_empty : val :=
  lst_is_empty.

Definition pstack_push : val :=
  fun: "t" "v" =>
    ‘Cons( "v", "t" ).

Definition pstack_pop : val :=
  fun: "param" =>
    match: "param" with
    | Nil =>
        §None
    | Cons "v" "t" =>
        ‘Some( ("v", "t") )
    end.
