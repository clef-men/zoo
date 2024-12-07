From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  queue_2__types.
From zoo Require Import
  options.

Definition queue_2_create : val :=
  fun: <> =>
    let: "sent" := ‘Node{ (), §Null } in
    { "sent", "sent" }.

Definition queue_2_is_empty : val :=
  fun: "t" =>
    "t".{front} == "t".{sentinel}.

Definition queue_2_push : val :=
  fun: "t" "v" =>
    match: ‘Node{ (), §Null } with
    | Node <> <> as "new_sent" =>
        match: "t".{sentinel} with
        | Node <> <> as "sent_r" =>
            "sent_r" <-{head} "v" ;;
            "sent_r" <-{tail} "new_sent" ;;
            "t" <-{sentinel} "new_sent"
        end
    end.

Definition queue_2_pop : val :=
  fun: "t" =>
    match: "t".{front} with
    | Node <> <> as "front_r" =>
        match: "front_r".{tail} with
        | Null =>
            §None
        | Node <> <> as "tail" =>
            "t" <-{front} "tail" ;;
            ‘Some( "front_r".{head} )
        end
    end.
