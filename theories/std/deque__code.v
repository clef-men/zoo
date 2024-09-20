From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  xdeque.
From zoo.std Require Import
  deque__types.
From zoo Require Import
  options.

Definition deque_create : val :=
  xdeque_create.

Definition deque_is_empty : val :=
  xdeque_is_empty.

Definition deque_push_front : val :=
  fun: "t" "v" =>
    xdeque_push_front "t" { "t", "t", "v" }.

Definition deque_push_back : val :=
  fun: "t" "v" =>
    xdeque_push_back "t" { "t", "t", "v" }.

Definition deque_pop_front : val :=
  fun: "t" =>
    match: xdeque_pop_front "t" with
    | None =>
        §None
    | Some "node" =>
        ‘Some( "node".{xdeque_data} )
    end.

Definition deque_pop_back : val :=
  fun: "t" =>
    match: xdeque_pop_back "t" with
    | None =>
        §None
    | Some "node" =>
        ‘Some( "node".{xdeque_data} )
    end.

Definition deque_iter : val :=
  fun: "t" "fn" =>
    xdeque_iter "t" (fun: "node" => "fn" "node".{xdeque_data}).
