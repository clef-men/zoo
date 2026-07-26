Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.diverge.
Require Import zoo_std.array.
Require Import zoo_std.assume.
Require Import zoo_std.int.
Require Import zoo_std.dynarray_2__types.
Require Import zoo.options.

Definition dynarray_2٠element : val :=
  𝗳𝘂𝗻 "v" ->
    ‘Element{ "v" }.

Definition dynarray_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { 0, array٠create () }.

Definition dynarray_2٠make : val :=
  𝗳𝘂𝗻 "sz" "v" ->
    { "sz", array٠init "sz" (𝗳𝘂𝗻 ⎽ -> dynarray_2٠element "v") }.

Definition dynarray_2٠initi : val :=
  𝗳𝘂𝗻 "sz" "fn" ->
    { "sz",
      array٠initi "sz" (𝗳𝘂𝗻 "i" -> dynarray_2٠element ("fn" "i"))
    }.

Definition dynarray_2٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{size}.

Definition dynarray_2٠data : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{data}.

Definition dynarray_2٠capacity : val :=
  𝗳𝘂𝗻 "t" ->
    array٠size (dynarray_2٠data "t").

Definition dynarray_2٠set_size : val :=
  𝗳𝘂𝗻 "t" "sz" ->
    "t" <-{size} "sz".

Definition dynarray_2٠set_data : val :=
  𝗳𝘂𝗻 "t" "data" ->
    "t" <-{data} "data".

Definition dynarray_2٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    dynarray_2٠size "t" == 0.

Definition dynarray_2٠get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗺𝗮𝘁𝗰𝗵
      array٠get (dynarray_2٠data "t") "i"
    𝘄𝗶𝘁𝗵
    | Empty ->
        𝗱𝗶𝘃𝗲𝗿𝗴𝗲 ()
    | Element ⎽ 𝗮𝘀 "slot_r" ->
        "slot_r".{value}
    𝗲𝗻𝗱.

Definition dynarray_2٠set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    𝗺𝗮𝘁𝗰𝗵
      array٠get (dynarray_2٠data "t") "i"
    𝘄𝗶𝘁𝗵
    | Empty ->
        𝗱𝗶𝘃𝗲𝗿𝗴𝗲 ()
    | Element ⎽ 𝗮𝘀 "slot_r" ->
        "slot_r" <-{value} "v"
    𝗲𝗻𝗱.

Definition dynarray_2٠next_capacity : val :=
  𝗳𝘂𝗻 "n" ->
    int٠max
      8
      𝗶𝗳 "n" ≤ 512 𝘁𝗵𝗲𝗻 (
        2 * "n"
      ) 𝗲𝗹𝘀𝗲 (
        "n" + "n" 𝗾𝘂𝗼𝘁 2
      ).

Definition dynarray_2٠reserve : val :=
  𝗳𝘂𝗻 "t" "n" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    𝗹𝗲𝘁 "data" = dynarray_2٠data "t" 𝗶𝗻
    𝗹𝗲𝘁 "cap" = array٠size "data" 𝗶𝗻
    𝗶𝗳 "cap" < "n" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "cap" =
        int٠max "n" (dynarray_2٠next_capacity "cap")
      𝗶𝗻
      𝗹𝗲𝘁 "data" = array٠unsafe_grow "data" "cap" §Empty 𝗶𝗻
      dynarray_2٠set_data "t" "data"
    ).

Definition dynarray_2٠reserve_extra : val :=
  𝗳𝘂𝗻 "t" "n" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    dynarray_2٠reserve "t" (dynarray_2٠size "t" + "n").

Definition dynarray_2٠try_grow : val :=
  𝗳𝘂𝗻 "t" "sz" "v" ->
    𝗹𝗲𝘁 "old_sz" = dynarray_2٠size "t" 𝗶𝗻
    𝗶𝗳 "sz" ≤ "old_sz" 𝘁𝗵𝗲𝗻 (
      true
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "data" = dynarray_2٠data "t" 𝗶𝗻
      𝗶𝗳 array٠size "data" < "sz" 𝘁𝗵𝗲𝗻 (
        false
      ) 𝗲𝗹𝘀𝗲 (
        dynarray_2٠set_size "t" "sz" ⍮
        array٠unsafe_apply_slice
          (𝗳𝘂𝗻 ⎽ -> dynarray_2٠element "v")
          "data"
          "old_sz"
          ("sz" - "old_sz") ⍮
        true
      )
    ).

Definition dynarray_2٠grow₀ : val :=
  𝗿𝗲𝗰 "grow" "t" "sz" "v" ->
    dynarray_2٠reserve "t" "sz" ⍮
    𝗶𝗳 ~ dynarray_2٠try_grow "t" "sz" "v" 𝘁𝗵𝗲𝗻 (
      "grow" "t" "sz" "v"
    ).

Definition dynarray_2٠grow : val :=
  𝗳𝘂𝗻 "t" "sz" "v" ->
    𝗶𝗳 ~ dynarray_2٠try_grow "t" "sz" "v" 𝘁𝗵𝗲𝗻 (
      dynarray_2٠grow₀ "t" "sz" "v"
    ).

Definition dynarray_2٠try_push : val :=
  𝗳𝘂𝗻 "t" "slot" ->
    𝗹𝗲𝘁 "sz" = dynarray_2٠size "t" 𝗶𝗻
    𝗹𝗲𝘁 "data" = dynarray_2٠data "t" 𝗶𝗻
    𝗶𝗳 array٠size "data" ≤ "sz" 𝘁𝗵𝗲𝗻 (
      false
    ) 𝗲𝗹𝘀𝗲 (
      dynarray_2٠set_size "t" ("sz" + 1) ⍮
      array٠unsafe_set "data" "sz" "slot" ⍮
      true
    ).

Definition dynarray_2٠push₀ : val :=
  𝗿𝗲𝗰 "push" "t" "slot" ->
    dynarray_2٠reserve_extra "t" 1 ⍮
    𝗶𝗳 ~ dynarray_2٠try_push "t" "slot" 𝘁𝗵𝗲𝗻 (
      "push" "t" "slot"
    ).

Definition dynarray_2٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "slot" = dynarray_2٠element "v" 𝗶𝗻
    𝗶𝗳 ~ dynarray_2٠try_push "t" "slot" 𝘁𝗵𝗲𝗻 (
      dynarray_2٠push₀ "t" "slot"
    ).

Definition dynarray_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "sz" = dynarray_2٠size "t" 𝗶𝗻
    𝗹𝗲𝘁 "data" = dynarray_2٠data "t" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 ("sz" ≤ array٠size "data") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 < "sz") ⍮
    𝗹𝗲𝘁 "sz" = "sz" - 1 𝗶𝗻
    𝗺𝗮𝘁𝗰𝗵 array٠unsafe_get "data" "sz" 𝘄𝗶𝘁𝗵
    | Empty ->
        𝗱𝗶𝘃𝗲𝗿𝗴𝗲 ()
    | Element ⎽ 𝗮𝘀 "slot_r" ->
        array٠unsafe_set "data" "sz" §Empty ⍮
        dynarray_2٠set_size "t" "sz" ⍮
        "slot_r".{value}
    𝗲𝗻𝗱.

Definition dynarray_2٠fit_capacity : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "sz" = dynarray_2٠size "t" 𝗶𝗻
    𝗹𝗲𝘁 "data" = dynarray_2٠data "t" 𝗶𝗻
    𝗶𝗳 array٠size "data" != "sz" 𝘁𝗵𝗲𝗻 (
      dynarray_2٠set_data "t" (array٠shrink "data" "sz")
    ).

Definition dynarray_2٠reset : val :=
  𝗳𝘂𝗻 "t" ->
    dynarray_2٠set_size "t" 0 ⍮
    dynarray_2٠set_data "t" (array٠create ()).

Definition dynarray_2٠iteri : val :=
  𝗳𝘂𝗻 "fn" "t" ->
    𝗹𝗲𝘁 "sz" = dynarray_2٠size "t" 𝗶𝗻
    𝗹𝗲𝘁 "data" = dynarray_2٠data "t" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 ("sz" ≤ array٠size "data") ⍮
    array٠unsafe_iteri_slice
      (𝗳𝘂𝗻 "i" "slot" ->
         𝗺𝗮𝘁𝗰𝗵 "slot" 𝘄𝗶𝘁𝗵
         | Empty ->
             𝗱𝗶𝘃𝗲𝗿𝗴𝗲 ()
         | Element ⎽ 𝗮𝘀 "slot_r" ->
             "fn" "i" "slot_r".{value}
         𝗲𝗻𝗱)
      "data"
      0
      "sz".

Definition dynarray_2٠iter : val :=
  𝗳𝘂𝗻 "fn" ->
    dynarray_2٠iteri (𝗳𝘂𝗻 "_i" -> "fn").
