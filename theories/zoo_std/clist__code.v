Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.clist__types.
Require Import zoo.options.

Definition clist٠app : val :=
  rec: "app" "t1" "t2" =>
    match: "t1" with
    | ClistClosed =>
        Fail
    | ClistOpen =>
        "t2"
    | ClistCons "v" "t1" =>
        ‘ClistCons[ "v", "app" "t1" "t2" ]
    end.

Definition clist٠rev_app : val :=
  rec: "rev_app" "t1" "t2" =>
    match: "t1" with
    | ClistClosed =>
        Fail
    | ClistOpen =>
        "t2"
    | ClistCons "v" "t1" =>
        "rev_app" "t1" ‘ClistCons[ "v", "t2" ]
    end.

Definition clist٠iter : val :=
  rec: "iter" "fn" "param" =>
    match: "param" with
    | ClistClosed =>
        Fail
    | ClistOpen =>
        ()
    | ClistCons "v" "t" =>
        "fn" "v" ;;
        "iter" "fn" "t"
    end.
