Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.program_logic.identifier.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo_saturn.ws_deque_1__types.
Require Import zoo.options.

Definition ws_deque_1٠min_capacity : val :=
  16.

Definition ws_deque_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { 1,
      1,
      array٠unsafe_make ws_deque_1٠min_capacity (),
      𝗽𝗿𝗼𝗽𝗵
    }.

Definition ws_deque_1٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{back} - "t".{front}.

Definition ws_deque_1٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    ws_deque_1٠size "t" == 0.

Definition ws_deque_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
    𝗹𝗲𝘁 "cap" = array٠size "data" 𝗶𝗻
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗶𝗳 "back" < "front" + "cap" 𝘁𝗵𝗲𝗻 (
      array٠unsafe_cset "data" "back" "v"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "new_cap" = "cap" 𝗹𝘀𝗹 1 𝗶𝗻
      𝗹𝗲𝘁 "new_data" =
        array٠unsafe_cgrow "data" "front" "new_cap" ()
      𝗶𝗻
      array٠unsafe_cset "new_data" "back" "v" ⍮
      "t" <-{data} "new_data"
    ) ⍮
    "t" <-{back} "back" + 1.

Definition ws_deque_1٠steal : val :=
  𝗿𝗲𝗰 "steal" "t" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} 𝗶𝗻
    𝗶𝗳 "back" ≤ "front" 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
      𝗹𝗲𝘁 "v" = array٠unsafe_cget "data" "front" 𝗶𝗻
      𝗶𝗳
        𝗿𝗲𝘀𝗼𝗹𝘃𝗲
          (𝗰𝗮𝘀 "t".[front] "front" ("front" + 1))
          "t".{proph}
          ("front", "id")
      𝘁𝗵𝗲𝗻 (
        ‘Some( "v" )
      ) 𝗲𝗹𝘀𝗲 (
        domain٠yield () ⍮
        "steal" "t"
      )
    ).

Definition ws_deque_1٠pop₀ : val :=
  𝗳𝘂𝗻 "t" "id" "back" ->
    𝗹𝗲𝘁 "front" = "t".{front} 𝗶𝗻
    𝗶𝗳 "back" < "front" 𝘁𝗵𝗲𝗻 (
      "t" <-{back} "front" ⍮
      §None
    ) 𝗲𝗹𝘀𝗲 𝗶𝗳 "front" < "back" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
      𝗹𝗲𝘁 "cap" = array٠size "data" 𝗶𝗻
      𝗶𝗳
        ws_deque_1٠min_capacity + 3 * ("back" - "front") ≤ "cap"
      𝘁𝗵𝗲𝗻 (
        𝗹𝗲𝘁 "new_cap" = "cap" 𝗹𝘀𝗿 1 𝗶𝗻
        𝗹𝗲𝘁 "new_data" =
          array٠unsafe_cshrink_slice "data" "front" "new_cap"
        𝗶𝗻
        "t" <-{data} "new_data"
      ) 𝗲𝗹𝘀𝗲 (
        ()
      ) ⍮
      ‘Some( array٠unsafe_cget "data" "back" )
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "won" =
        𝗿𝗲𝘀𝗼𝗹𝘃𝗲
          (𝗰𝗮𝘀 "t".[front] "front" ("front" + 1))
          "t".{proph}
          ("front", "id")
      𝗶𝗻
      "t" <-{back} "front" + 1 ⍮
      𝗶𝗳 "won" 𝘁𝗵𝗲𝗻 (
        ‘Some( array٠unsafe_cget "t".{data} "front" )
      ) 𝗲𝗹𝘀𝗲 (
        §None
      )
    ).

Definition ws_deque_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "back" = "t".{back} - 1 𝗶𝗻
    "t" <-{back} "back" ⍮
    ws_deque_1٠pop₀ "t" "id" "back".
