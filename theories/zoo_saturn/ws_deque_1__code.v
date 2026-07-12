Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo.program_logic.identifier.
Require Import zoo_saturn.ws_deque_1__types.
Require Import zoo.options.

Definition ws_deque_1٠min_capacity : val :=
  16.

Definition ws_deque_1٠create : val :=
  fun: <> =>
    { 1, 1, array٠unsafe_make ws_deque_1٠min_capacity (), Proph }.

Definition ws_deque_1٠size : val :=
  fun: "t" =>
    "t".{back} - "t".{front}.

Definition ws_deque_1٠is_empty : val :=
  fun: "t" =>
    ws_deque_1٠size "t" == 0.

Definition ws_deque_1٠push : val :=
  fun: "t" "v" =>
    let: "back" := "t".{back} in
    let: "data" := "t".{data} in
    let: "cap" := array٠size "data" in
    let: "front" := "t".{front} in
    if: "back" < "front" + "cap" then (
      array٠unsafe_cset "data" "back" "v"
    ) else (
      let: "new_cap" := "cap" `lsl` 1 in
      let: "new_data" := array٠unsafe_cgrow "data" "front" "new_cap" () in
      array٠unsafe_cset "new_data" "back" "v" ;;
      "t" <-{data} "new_data"
    ) ;;
    "t" <-{back} "back" + 1.

Definition ws_deque_1٠steal : val :=
  rec: "steal" "t" =>
    let: "id" := Id in
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "back" ≤ "front" then (
      §None
    ) else (
      let: "data" := "t".{data} in
      let: "v" := array٠unsafe_cget "data" "front" in
      if:
        Resolve
          (CAS "t".[front] "front" ("front" + 1))
          "t".{proph}
          ("front", "id")
      then (
        ‘Some( "v" )
      ) else (
        domain٠yield () ;;
        "steal" "t"
      )
    ).

Definition ws_deque_1٠pop₀ : val :=
  fun: "t" "id" "back" =>
    let: "front" := "t".{front} in
    if: "back" < "front" then (
      "t" <-{back} "front" ;;
      §None
    ) else if: "front" < "back" then (
      let: "data" := "t".{data} in
      let: "cap" := array٠size "data" in
      if: ws_deque_1٠min_capacity + 3 * ("back" - "front") ≤ "cap" then (
        let: "new_cap" := "cap" `lsr` 1 in
        let: "new_data" :=
          array٠unsafe_cshrink_slice "data" "front" "new_cap"
        in
        "t" <-{data} "new_data"
      ) else (
        ()
      ) ;;
      ‘Some( array٠unsafe_cget "data" "back" )
    ) else (
      let: "won" :=
        Resolve
          (CAS "t".[front] "front" ("front" + 1))
          "t".{proph}
          ("front", "id")
      in
      "t" <-{back} "front" + 1 ;;
      if: "won" then (
        ‘Some( array٠unsafe_cget "t".{data} "front" )
      ) else (
        §None
      )
    ).

Definition ws_deque_1٠pop : val :=
  fun: "t" =>
    let: "id" := Id in
    let: "back" := "t".{back} - 1 in
    "t" <-{back} "back" ;;
    ws_deque_1٠pop₀ "t" "id" "back".
