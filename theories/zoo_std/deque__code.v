Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.xdeque.
Require Import zoo_std.deque__types.
Require Import zoo.options.

Definition deque٠create : val :=
  xdeque٠create.

Definition deque٠is_empty : val :=
  xdeque٠is_empty.

Definition deque٠push_front : val :=
  fun: "t" "v" =>
    xdeque٠push_front "t" { "t", "t", "v" }.

Definition deque٠push_back : val :=
  fun: "t" "v" =>
    xdeque٠push_back "t" { "t", "t", "v" }.

Definition deque٠pop_front : val :=
  fun: "t" =>
    match: xdeque٠pop_front "t" with
    | None =>
        §None
    | Some "node" =>
        ‘Some( "node".{xdeque_data} )
    end.

Definition deque٠pop_back : val :=
  fun: "t" =>
    match: xdeque٠pop_back "t" with
    | None =>
        §None
    | Some "node" =>
        ‘Some( "node".{xdeque_data} )
    end.

Definition deque٠iter : val :=
  fun: "fn" =>
    xdeque٠iter (fun: "node" => "fn" "node".{xdeque_data}).
