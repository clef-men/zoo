Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_persistent.sstore_2.
Require Import zoo_persistent.suf__types.
Require Import zoo.options.

Definition suf٠create : val :=
  sstore_2٠create.

Definition suf٠make : val :=
  𝗳𝘂𝗻 "t" ->
    sstore_2٠ref "t" ‘Root( 0 ).

Definition suf٠repr : val :=
  𝗿𝗲𝗰 "repr" "t" "elt" ->
    𝗺𝗮𝘁𝗰𝗵 sstore_2٠get "t" "elt" 𝘄𝗶𝘁𝗵
    | Root ⎽ ->
        "elt"
    | Link "parent" ->
        𝗹𝗲𝘁 "repr" = "repr" "t" "parent" 𝗶𝗻
        sstore_2٠set "t" "elt" ‘Link( "repr" ) ⍮
        "repr"
    𝗲𝗻𝗱.

Definition suf٠equiv : val :=
  𝗳𝘂𝗻 "t" "elt1" "elt2" ->
    suf٠repr "t" "elt1" == suf٠repr "t" "elt2".

Definition suf٠rank : val :=
  𝗳𝘂𝗻 "t" "elt" ->
    𝗺𝗮𝘁𝗰𝗵 sstore_2٠get "t" "elt" 𝘄𝗶𝘁𝗵
    | Root "rank" ->
        "rank"
    | Link ⎽ ->
        𝗳𝗮𝗶𝗹
    𝗲𝗻𝗱.

Definition suf٠union : val :=
  𝗳𝘂𝗻 "t" "elt1" "elt2" ->
    𝗹𝗲𝘁 "repr1" = suf٠repr "t" "elt1" 𝗶𝗻
    𝗹𝗲𝘁 "rank1" = suf٠rank "t" "repr1" 𝗶𝗻
    𝗹𝗲𝘁 "repr2" = suf٠repr "t" "elt2" 𝗶𝗻
    𝗹𝗲𝘁 "rank2" = suf٠rank "t" "repr2" 𝗶𝗻
    𝗶𝗳 "repr1" != "repr2" 𝘁𝗵𝗲𝗻 (
      𝗶𝗳 "rank1" < "rank2" 𝘁𝗵𝗲𝗻 (
        sstore_2٠set "t" "repr1" ‘Link( "repr2" )
      ) 𝗲𝗹𝘀𝗲 (
        sstore_2٠set "t" "repr2" ‘Link( "repr1" ) ⍮
        𝗶𝗳 "rank1" == "rank2" 𝘁𝗵𝗲𝗻 (
          sstore_2٠set "t" "repr1" ‘Root( "rank1" + 1 )
        )
      )
    ).

Definition suf٠capture : val :=
  sstore_2٠capture.

Definition suf٠restore : val :=
  sstore_2٠restore.
