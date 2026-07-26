Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.atomic_array.
Require Import zoo_std.queue_3.
Require Import zoo_std.array.
Require Import zoo_std.random_round.
Require Import zoo_std.domain.
Require Import zoo_parabs.ws_deques_private__types.
Require Import zoo.options.

Definition ws_deques_private٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    { "sz",
      array٠unsafe_init "sz" queue_3٠create,
      array٠unsafe_make "sz" §Nonblocked,
      atomic_array٠make "sz" §RequestNone,
      array٠unsafe_make "sz" §ResponseWaiting,
      ()
    }.

Definition ws_deques_private٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{size}.

Definition ws_deques_private٠block : val :=
  𝗳𝘂𝗻 "t" "i" ->
    array٠unsafe_set "t".{statuses} "i" §Blocked ⍮
    𝗺𝗮𝘁𝗰𝗵
      atomic_array٠unsafe_xchg "t".{requests} "i" §RequestBlocked
    𝘄𝗶𝘁𝗵
    | RequestSome "j" ->
        array٠unsafe_set "t".{responses} "j" §ResponseNone
    | ⎽ ->
        ()
    𝗲𝗻𝗱.

Definition ws_deques_private٠unblock : val :=
  𝗳𝘂𝗻 "t" "i" ->
    atomic_array٠unsafe_set "t".{requests} "i" §RequestNone ⍮
    array٠unsafe_set "t".{statuses} "i" §Nonblocked.

Definition ws_deques_private٠respond : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗺𝗮𝘁𝗰𝗵
      atomic_array٠unsafe_get "t".{requests} "i"
    𝘄𝗶𝘁𝗵
    | RequestSome "j" ->
        𝗹𝗲𝘁 "response" =
          𝗺𝗮𝘁𝗰𝗵
            queue_3٠pop_front (array٠unsafe_get "t".{queues} "i")
          𝘄𝗶𝘁𝗵
          | Some "v" ->
              ‘ResponseSome( "v" )
          | ⎽ ->
              §ResponseNone
          𝗲𝗻𝗱
        𝗶𝗻
        array٠unsafe_set "t".{responses} "j" "response" ⍮
        atomic_array٠unsafe_set "t".{requests} "i" §RequestNone
    | ⎽ ->
        ()
    𝗲𝗻𝗱.

Definition ws_deques_private٠push : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    queue_3٠push (array٠unsafe_get "t".{queues} "i") "v" ⍮
    ws_deques_private٠respond "t" "i".

Definition ws_deques_private٠pop : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗹𝗲𝘁 "res" =
      queue_3٠pop_back (array٠unsafe_get "t".{queues} "i")
    𝗶𝗻
    ws_deques_private٠respond "t" "i" ⍮
    "res".

Definition ws_deques_private٠steal_to₀ : val :=
  𝗿𝗲𝗰 "steal_to" "t" "i" ->
    𝗺𝗮𝘁𝗰𝗵
      array٠unsafe_get "t".{responses} "i"
    𝘄𝗶𝘁𝗵
    | ResponseWaiting ->
        domain٠yield () ⍮
        "steal_to" "t" "i"
    | ResponseNone ->
        array٠unsafe_set "t".{responses} "i" §ResponseWaiting ⍮
        §None
    | ResponseSome "v" ->
        array٠unsafe_set "t".{responses} "i" §ResponseWaiting ⍮
        ‘Some( "v" )
    𝗲𝗻𝗱.

Definition ws_deques_private٠steal_to : val :=
  𝗳𝘂𝗻 "t" "i" "j" ->
    𝗶𝗳
      array٠unsafe_get "t".{statuses} "j" == §Nonblocked
      𝗮𝗻𝗱
      atomic_array٠unsafe_cas
        "t".{requests}
        "j"
        §RequestNone
        ‘RequestSome( "i" )
    𝘁𝗵𝗲𝗻 (
      ws_deques_private٠steal_to₀ "t" "i"
    ) 𝗲𝗹𝘀𝗲 (
      §None
    ).

Definition ws_deques_private٠steal_as₀ : val :=
  𝗿𝗲𝗰 "steal_as" "t" "sz" "i" "round" "n" ->
    𝗶𝗳 "n" ≤ 0 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "j" =
        ("i" + 1 + random_round٠next "round") 𝗿𝗲𝗺 "sz"
      𝗶𝗻
      𝗺𝗮𝘁𝗰𝗵
        ws_deques_private٠steal_to "t" "i" "j"
      𝘄𝗶𝘁𝗵
      | None ->
          "steal_as" "t" "sz" "i" "round" ("n" - 1)
      | ⎽ 𝗮𝘀 "res" ->
          "res"
      𝗲𝗻𝗱
    ).

Definition ws_deques_private٠steal_as : val :=
  𝗳𝘂𝗻 "t" "i" "round" ->
    𝗹𝗲𝘁 "sz" = ws_deques_private٠size "t" 𝗶𝗻
    ws_deques_private٠steal_as₀ "t" "sz" "i" "round" ("sz" - 1).
