From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  atomic_array
  queue_3
  array
  random_round
  domain.
From zoo_parabs Require Import
  ws_deques_private__types.
From zoo Require Import
  options.

Definition ws_deques_private_create : val :=
  fun: "sz" =>
    { "sz",
      array_unsafe_init "sz" queue_3_create,
      array_unsafe_make "sz" §Nonblocked,
      atomic_array_make "sz" §RequestNone,
      array_unsafe_make "sz" §ResponseWaiting,
      ()
    }.

Definition ws_deques_private_size : val :=
  fun: "t" =>
    "t".{size}.

Definition ws_deques_private_block : val :=
  fun: "t" "i" =>
    array_unsafe_set "t".{statuses} "i" §Blocked ;;
    match: atomic_array_unsafe_xchg "t".{requests} "i" §RequestBlocked with
    | RequestSome "j" =>
        array_unsafe_set "t".{responses} "j" §ResponseNone
    |_ =>
        ()
    end.

Definition ws_deques_private_unblock : val :=
  fun: "t" "i" =>
    atomic_array_unsafe_set "t".{requests} "i" §RequestNone ;;
    array_unsafe_set "t".{statuses} "i" §Nonblocked.

Definition ws_deques_private_respond : val :=
  fun: "t" "i" =>
    match: atomic_array_unsafe_get "t".{requests} "i" with
    | RequestSome "j" =>
        let: "response" :=
          match: queue_3_pop_front (array_unsafe_get "t".{queues} "i") with
          | Some "v" =>
              ‘ResponseSome( "v" )
          |_ =>
              §ResponseNone
          end
        in
        array_unsafe_set "t".{responses} "j" "response" ;;
        atomic_array_unsafe_set "t".{requests} "i" §RequestNone
    |_ =>
        ()
    end.

Definition ws_deques_private_push : val :=
  fun: "t" "i" "v" =>
    queue_3_push (array_unsafe_get "t".{queues} "i") "v" ;;
    ws_deques_private_respond "t" "i".

Definition ws_deques_private_pop : val :=
  fun: "t" "i" =>
    let: "res" := queue_3_pop_back (array_unsafe_get "t".{queues} "i") in
    ws_deques_private_respond "t" "i" ;;
    "res".

Definition ws_deques_private_steal_to_0 : val :=
  rec: "steal_to" "t" "i" =>
    match: array_unsafe_get "t".{responses} "i" with
    | ResponseWaiting =>
        domain_yield () ;;
        "steal_to" "t" "i"
    | ResponseNone =>
        array_unsafe_set "t".{responses} "i" §ResponseWaiting ;;
        §None
    | ResponseSome "v" =>
        array_unsafe_set "t".{responses} "i" §ResponseWaiting ;;
        ‘Some( "v" )
    end.

Definition ws_deques_private_steal_to : val :=
  fun: "t" "i" "j" =>
    if:
      array_unsafe_get "t".{statuses} "j" == §Nonblocked
      and
      atomic_array_unsafe_cas
        "t".{requests}
        "j"
        §RequestNone
        ‘RequestSome( "i" )
    then (
      ws_deques_private_steal_to_0 "t" "i"
    ) else (
      §None
    ).

Definition ws_deques_private_steal_as_0 : val :=
  rec: "steal_as" "t" "sz" "i" "round" "n" =>
    if: "n" ≤ 0 then (
      §None
    ) else (
      let: "j" := ("i" + 1 + random_round_next "round") `rem` "sz" in
      match: ws_deques_private_steal_to "t" "i" "j" with
      | None =>
          "steal_as" "t" "sz" "i" "round" ("n" - 1)
      |_ as "res" =>
          "res"
      end
    ).

Definition ws_deques_private_steal_as : val :=
  fun: "t" "i" "round" =>
    let: "sz" := ws_deques_private_size "t" in
    ws_deques_private_steal_as_0 "t" "sz" "i" "round" ("sz" - 1).
