Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.int.
Require Import zoo_std.mutex.
Require Import zoo.options.

Notation "'inf_array٠data'" := (
  in_type "zoo_std.inf_array.t" 0
)(in custom zoo_field
).
Notation "'inf_array٠default'" := (
  in_type "zoo_std.inf_array.t" 1
)(in custom zoo_field
).
Notation "'inf_array٠mutex'" := (
  in_type "zoo_std.inf_array.t" 2
)(in custom zoo_field
).

Definition inf_array٠create : val :=
  𝗳𝘂𝗻 "default" ->
    𝗹𝗲𝘁 "data" = array٠create () 𝗶𝗻
    𝗹𝗲𝘁 "mutex" = mutex٠create () 𝗶𝗻
    { "data", "default", "mutex" }.

Definition inf_array٠next_capacity : val :=
  𝗳𝘂𝗻 "n" ->
    int٠max
      8
      𝗶𝗳 "n" ≤ 512 𝘁𝗵𝗲𝗻 (
        2 * "n"
      ) 𝗲𝗹𝘀𝗲 (
        "n" + "n" 𝗾𝘂𝗼𝘁 2
      ).

Definition inf_array٠reserve : val :=
  𝗳𝘂𝗻 "t" "n" ->
    𝗹𝗲𝘁 "data" = "t".{inf_array٠data} 𝗶𝗻
    𝗹𝗲𝘁 "cap" = array٠size "data" 𝗶𝗻
    𝗶𝗳 "cap" < "n" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "cap" =
        int٠max "n" (inf_array٠next_capacity "cap")
      𝗶𝗻
      𝗹𝗲𝘁 "data" =
        array٠unsafe_grow "data" "cap" "t".{inf_array٠default}
      𝗶𝗻
      "t" <-{inf_array٠data} "data"
    ).

Definition inf_array٠get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    mutex٠protect "t".{inf_array٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         𝗹𝗲𝘁 "data" = "t".{inf_array٠data} 𝗶𝗻
         𝗶𝗳 "i" < array٠size "data" 𝘁𝗵𝗲𝗻 (
           array٠unsafe_get "data" "i"
         ) 𝗲𝗹𝘀𝗲 (
           "t".{inf_array٠default}
         )).

Definition inf_array٠update : val :=
  𝗳𝘂𝗻 "t" "i" "fn" ->
    mutex٠protect "t".{inf_array٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         inf_array٠reserve "t" ("i" + 1) ⍮
         𝗹𝗲𝘁 "v" =
           array٠unsafe_get "t".{inf_array٠data} "i"
         𝗶𝗻
         array٠unsafe_set "t".{inf_array٠data} "i" ("fn" "v") ⍮
         "v").

Definition inf_array٠xchg : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    inf_array٠update "t" "i" (𝗳𝘂𝗻 ⎽ -> "v").

Definition inf_array٠xchg_resolve : val :=
  𝗳𝘂𝗻 "t" "i" "v" "proph" "v_resolve" ->
    mutex٠protect "t".{inf_array٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         inf_array٠reserve "t" ("i" + 1) ⍮
         𝗹𝗲𝘁 "old_v" =
           array٠unsafe_get "t".{inf_array٠data} "i"
         𝗶𝗻
         array٠unsafe_set "t".{inf_array٠data} "i" "v" ⍮
         𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "proph" "v_resolve" ⍮
         "old_v").

Definition inf_array٠set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    inf_array٠xchg "t" "i" "v" ⍮
    ().

Definition inf_array٠cas : val :=
  𝗳𝘂𝗻 "t" "i" "v1" "v2" ->
    mutex٠protect "t".{inf_array٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         inf_array٠reserve "t" ("i" + 1) ⍮
         𝗹𝗲𝘁 "res" =
           array٠unsafe_get "t".{inf_array٠data} "i" == "v1"
         𝗶𝗻
         𝗶𝗳 "res" 𝘁𝗵𝗲𝗻 (
           array٠unsafe_set "t".{inf_array٠data} "i" "v2"
         ) 𝗲𝗹𝘀𝗲 (
           ()
         ) ⍮
         "res").

Definition inf_array٠cas_resolve : val :=
  𝗳𝘂𝗻 "t" "i" "v1" "v2" "proph" "v_resolve" ->
    mutex٠protect "t".{inf_array٠mutex}
      (𝗳𝘂𝗻 ⎽ ->
         inf_array٠reserve "t" ("i" + 1) ⍮
         𝗹𝗲𝘁 "res" =
           array٠unsafe_get "t".{inf_array٠data} "i" == "v1"
         𝗶𝗻
         𝗶𝗳 "res" 𝘁𝗵𝗲𝗻 (
           array٠unsafe_set "t".{inf_array٠data} "i" "v2"
         ) 𝗲𝗹𝘀𝗲 (
           ()
         ) ⍮
         𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "proph" "v_resolve" ⍮
         "res").

Definition inf_array٠faa : val :=
  𝗳𝘂𝗻 "t" "i" "incr" ->
    inf_array٠update "t" "i" (𝗳𝘂𝗻 "n" -> "n" + "incr").
