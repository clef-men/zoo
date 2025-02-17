From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  deque
  atomic_array
  array
  random_round
  domain.
From zoo_parabs Require Import
  ws_deques_private__types.
From zoo Require Import
  options.

Definition ws_deques_private_create : val :=
  fun: "sz" =>
    (array_unsafe_init "sz" deque_create,
     array_unsafe_make "sz" #false,
     atomic_array_make "sz" §Blocked,
     array_unsafe_make "sz" §No_response
    ).

Definition ws_deques_private_size : val :=
  fun: "t" =>
    array_size "t".<deques>.

Definition ws_deques_private_block_0 : val :=
  fun: "t" "i" "j" =>
    array_unsafe_set "t".<responses> "j" §No ;;
    atomic_array_unsafe_set "t".<requests> "i" §Blocked.

Definition ws_deques_private_block : val :=
  fun: "t" "i" =>
    array_unsafe_set "t".<flags> "i" #false ;;
    let: "requests" := "t".<requests> in
    match: atomic_array_unsafe_get "requests" "i" with
    | Blocked =>
        ()
    | No_request =>
        if:
          ~ atomic_array_unsafe_cas "requests" "i" §No_request §Blocked
        then (
          match: atomic_array_unsafe_get "requests" "i" with
          | Request "j" =>
              ws_deques_private_block_0 "t" "i" "j"
          |_ =>
              Fail
          end
        )
    | Request "j" =>
        ws_deques_private_block_0 "t" "i" "j"
    end.

Definition ws_deques_private_unblock : val :=
  fun: "t" "i" =>
    atomic_array_unsafe_set "t".<requests> "i" §No_request ;;
    array_unsafe_set "t".<flags> "i" #true.

Definition ws_deques_private_respond : val :=
  fun: "t" "i" =>
    let: "deque" := array_unsafe_get "t".<deques> "i" in
    let: "requests" := "t".<requests> in
    match: atomic_array_unsafe_get "requests" "i" with
    | Request "j" =>
        let: "v" :=
          match: deque_pop_front "deque" with
          | Some "v" =>
              "v"
          |_ =>
              Fail
          end
        in
        array_unsafe_set "t".<responses> "j" ‘Yes( "v" ) ;;
        atomic_array_unsafe_set
          "requests"
          "i"
          if: deque_is_empty "deque" then (
            §Blocked
          ) else (
            §No_request
          )
    |_ =>
        ()
    end.

Definition ws_deques_private_push : val :=
  fun: "t" "i" "v" =>
    let: "deque" := array_unsafe_get "t".<deques> "i" in
    deque_push_back "deque" "v" ;;
    if: array_unsafe_get "t".<flags> "i" then (
      ws_deques_private_respond "t" "i"
    ) else (
      ws_deques_private_unblock "t" "i"
    ).

Definition ws_deques_private_pop : val :=
  fun: "t" "i" =>
    let: "deque" := array_unsafe_get "t".<deques> "i" in
    let: "res" := deque_pop_back "deque" in
    match: "res" with
    | None =>
        ()
    | Some <> =>
        if: deque_is_empty "deque" then (
          ws_deques_private_block "t" "i"
        ) else (
          ws_deques_private_respond "t" "i"
        )
    end ;;
    "res".

Definition ws_deques_private_steal_to_0 : val :=
  rec: "steal_to" "t" "i" =>
    match: array_unsafe_get "t".<responses> "i" with
    | No_response =>
        domain_yield () ;;
        "steal_to" "t" "i"
    | No =>
        §None
    | Yes "v" =>
        array_unsafe_set "t".<responses> "i" §No_response ;;
        ‘Some( "v" )
    end.

Definition ws_deques_private_steal_to : val :=
  fun: "t" "i" "j" =>
    if:
      array_unsafe_get "t".<flags> "j" and
      atomic_array_unsafe_cas
        "t".<requests>
        "j"
        §No_request
        ‘Request( "i" )
    then (
      ws_deques_private_steal_to_0 "t" "i"
    ) else (
      §None
    ).

Definition ws_deques_private_steal_as_0 : val :=
  rec: "steal_as" "t" "sz" "i" "round" "n" =>
    if: "n" ≤ #0 then (
      §None
    ) else (
      let: "j" := ("i" + #1 + random_round_next "round") `rem` "sz" in
      match: ws_deques_private_steal_to "t" "i" "j" with
      | None =>
          "steal_as" "t" "sz" "i" "round" ("n" - #1)
      |_ as "res" =>
          "res"
      end
    ).

Definition ws_deques_private_steal_as : val :=
  fun: "t" "i" "round" =>
    let: "sz" := ws_deques_private_size "t" in
    ws_deques_private_steal_as_0 "t" "sz" "i" "round" ("sz" - #1).
