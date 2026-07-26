Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.int.
Require Import zoo_std.dynarray_1__types.
Require Import zoo.options.

Definition dynarray_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { 0, array٠create () }.

Definition dynarray_1٠make : val :=
  𝗳𝘂𝗻 "sz" "v" ->
    { "sz", array٠unsafe_make "sz" "v" }.

Definition dynarray_1٠initi : val :=
  𝗳𝘂𝗻 "sz" "fn" ->
    { "sz", array٠unsafe_initi "sz" "fn" }.

Definition dynarray_1٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{size}.

Definition dynarray_1٠capacity : val :=
  𝗳𝘂𝗻 "t" ->
    array٠size "t".{data}.

Definition dynarray_1٠is_empty : val :=
  𝗳𝘂𝗻 "t" ->
    dynarray_1٠size "t" == 0.

Definition dynarray_1٠get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    array٠unsafe_get "t".{data} "i".

Definition dynarray_1٠set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    array٠unsafe_set "t".{data} "i" "v".

Definition dynarray_1٠next_capacity : val :=
  𝗳𝘂𝗻 "n" ->
    int٠max
      8
      𝗶𝗳 "n" ≤ 512 𝘁𝗵𝗲𝗻 (
        2 * "n"
      ) 𝗲𝗹𝘀𝗲 (
        "n" + "n" 𝗾𝘂𝗼𝘁 2
      ).

Definition dynarray_1٠reserve : val :=
  𝗳𝘂𝗻 "t" "n" ->
    𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
    𝗹𝗲𝘁 "cap" = array٠size "data" 𝗶𝗻
    𝗶𝗳 "cap" < "n" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "new_cap" =
        int٠max "n" (dynarray_1٠next_capacity "cap")
      𝗶𝗻
      𝗹𝗲𝘁 "new_data" = array٠unsafe_alloc "new_cap" 𝗶𝗻
      array٠unsafe_copy_slice "data" 0 "new_data" 0 "t".{size} ⍮
      "t" <-{data} "new_data"
    ).

Definition dynarray_1٠reserve_extra : val :=
  𝗳𝘂𝗻 "t" "n" ->
    dynarray_1٠reserve "t" ("t".{size} + "n").

Definition dynarray_1٠grow : val :=
  𝗳𝘂𝗻 "t" "sz" "v" ->
    𝗹𝗲𝘁 "old_sz" = "t".{size} 𝗶𝗻
    𝗶𝗳 "old_sz" < "sz" 𝘁𝗵𝗲𝗻 (
      dynarray_1٠reserve "t" "sz" ⍮
      array٠unsafe_fill_slice "t".{data} "old_sz" ("sz" - "old_sz") "v" ⍮
      "t" <-{size} "sz"
    ).

Definition dynarray_1٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    dynarray_1٠reserve_extra "t" 1 ⍮
    𝗹𝗲𝘁 "sz" = "t".{size} 𝗶𝗻
    "t" <-{size} "sz" + 1 ⍮
    array٠unsafe_set "t".{data} "sz" "v".

Definition dynarray_1٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "sz" = "t".{size} - 1 𝗶𝗻
    "t" <-{size} "sz" ⍮
    𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
    𝗹𝗲𝘁 "v" = array٠unsafe_get "data" "sz" 𝗶𝗻
    array٠unsafe_set "data" "sz" () ⍮
    "v".

Definition dynarray_1٠fit_capacity : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "sz" = "t".{size} 𝗶𝗻
    𝗹𝗲𝘁 "data" = "t".{data} 𝗶𝗻
    𝗶𝗳 "sz" != array٠size "data" 𝘁𝗵𝗲𝗻 (
      "t" <-{data} array٠unsafe_shrink "data" "sz"
    ).

Definition dynarray_1٠reset : val :=
  𝗳𝘂𝗻 "t" ->
    "t" <-{size} 0 ⍮
    "t" <-{data} array٠create ().

Definition dynarray_1٠iteri : val :=
  𝗳𝘂𝗻 "fn" "t" ->
    array٠unsafe_iteri_slice "fn" "t".{data} 0 "t".{size}.

Definition dynarray_1٠iter : val :=
  𝗳𝘂𝗻 "fn" ->
    dynarray_1٠iteri (𝗳𝘂𝗻 "_i" -> "fn").
