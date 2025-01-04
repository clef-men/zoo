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
    let: "front" := ‘Node{ §Null, () } in
    { "front", "front" }.

Definition queue_2_is_empty : val :=
  fun: "t" =>
    "t".{front} == "t".{back}.

Definition queue_2_push : val :=
  fun: "t" "v" =>
    match: ‘Node{ §Null, () } with
    | Node <> <> as "new_back" =>
        match: "t".{back} with
        | Node <> <> as "back_r" =>
            "back_r" <-{next} "new_back" ;;
            "back_r" <-{data} "v" ;;
            "t" <-{back} "new_back"
        end
    end.

Definition queue_2_pop : val :=
  fun: "t" =>
    match: "t".{front} with
    | Node <> <> as "front_r" =>
        match: "front_r".{next} with
        | Null =>
            §None
        | Node <> <> as "next" =>
            "t" <-{front} "next" ;;
            ‘Some( "front_r".{data} )
        end
    end.
