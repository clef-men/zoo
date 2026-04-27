From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  clst__types.
From zoo Require Import
  options.

Definition clst٠app : val :=
  rec: "app" "t1" "t2" =>
    match: "t1" with
    | ClstClosed =>
        Fail
    | ClstOpen =>
        "t2"
    | ClstCons "v" "t1" =>
        ‘ClstCons[ "v", "app" "t1" "t2" ]
    end.

Definition clst٠rev_app : val :=
  rec: "rev_app" "t1" "t2" =>
    match: "t1" with
    | ClstClosed =>
        Fail
    | ClstOpen =>
        "t2"
    | ClstCons "v" "t1" =>
        "rev_app" "t1" ‘ClstCons[ "v", "t2" ]
    end.

Definition clst٠iter : val :=
  rec: "iter" "fn" "param" =>
    match: "param" with
    | ClstClosed =>
        Fail
    | ClstOpen =>
        ()
    | ClstCons "v" "t" =>
        "fn" "v" ;;
        "iter" "fn" "t"
    end.
