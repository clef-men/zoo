Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Definition list٠singleton : val :=
  𝗳𝘂𝗻 "v" ->
    "v" :: [].

Definition list٠head : val :=
  𝗳𝘂𝗻 "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        𝗳𝗮𝗶𝗹
    | "v" :: ⎽ ->
        "v"
    𝗲𝗻𝗱.

Definition list٠tail : val :=
  𝗳𝘂𝗻 "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        𝗳𝗮𝗶𝗹
    | ⎽ :: "t" ->
        "t"
    𝗲𝗻𝗱.

Definition list٠is_empty : val :=
  𝗳𝘂𝗻 "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        true
    | ⎽ :: ⎽ ->
        false
    𝗲𝗻𝗱.

Definition list٠get : val :=
  𝗿𝗲𝗰 "get" "t" "i" ->
    𝗶𝗳 "i" ≤ 0 𝘁𝗵𝗲𝗻 (
      list٠head "t"
    ) 𝗲𝗹𝘀𝗲 (
      "get" (list٠tail "t") ("i" - 1)
    ).

Definition list٠initi₁ : val :=
  𝗿𝗲𝗰 "initi" "sz" "fn" "i" ->
    𝗶𝗳 "sz" ≤ "i" 𝘁𝗵𝗲𝗻 (
      []
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "v" = "fn" "i" 𝗶𝗻
      "v" :: "initi" "sz" "fn" ("i" + 1)
    ).

Definition list٠initi : val :=
  𝗳𝘂𝗻 "sz" "fn" ->
    list٠initi₁ "sz" "fn" 0.

Definition list٠init : val :=
  𝗳𝘂𝗻 "sz" "fn" ->
    list٠initi "sz" (𝗳𝘂𝗻 "_i" -> "fn" ()).

Definition list٠foldli₁ : val :=
  𝗿𝗲𝗰 "foldli" "fn" "i" "acc" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t" 𝘄𝗶𝘁𝗵
    | [] ->
        "acc"
    | "v" :: "t" ->
        "foldli" "fn" ("i" + 1) ("fn" "i" "acc" "v") "t"
    𝗲𝗻𝗱.

Definition list٠foldli : val :=
  𝗳𝘂𝗻 "fn" ->
    list٠foldli₁ "fn" 0.

Definition list٠foldl : val :=
  𝗳𝘂𝗻 "fn" ->
    list٠foldli (𝗳𝘂𝗻 "_i" -> "fn").

Definition list٠foldri₁ : val :=
  𝗿𝗲𝗰 "foldri" "fn" "i" "t" "acc" ->
    𝗺𝗮𝘁𝗰𝗵 "t" 𝘄𝗶𝘁𝗵
    | [] ->
        "acc"
    | "v" :: "t" ->
        "fn" "i" "v" ("foldri" "fn" ("i" + 1) "t" "acc")
    𝗲𝗻𝗱.

Definition list٠foldri : val :=
  𝗳𝘂𝗻 "fn" ->
    list٠foldri₁ "fn" 0.

Definition list٠foldr : val :=
  𝗳𝘂𝗻 "fn" ->
    list٠foldri (𝗳𝘂𝗻 "_i" -> "fn").

Definition list٠size : val :=
  𝗳𝘂𝗻 "t" ->
    list٠foldl (𝗳𝘂𝗻 "acc" ⎽ -> "acc" + 1) 0 "t".

Definition list٠rev_app : val :=
  𝗳𝘂𝗻 "t1" "t2" ->
    list٠foldl (𝗳𝘂𝗻 "acc" "v" -> "v" :: "acc") "t2" "t1".

Definition list٠rev : val :=
  𝗳𝘂𝗻 "t" ->
    list٠rev_app "t" [].

Definition list٠app : val :=
  𝗳𝘂𝗻 "t1" "t2" ->
    list٠foldr (𝗳𝘂𝗻 "v" "acc" -> "v" :: "acc") "t1" "t2".

Definition list٠snoc : val :=
  𝗳𝘂𝗻 "t" "v" ->
    list٠app "t" (list٠singleton "v").

Definition list٠iteri : val :=
  𝗳𝘂𝗻 "fn" ->
    list٠foldli (𝗳𝘂𝗻 "i" ⎽ -> "fn" "i") ().

Definition list٠iter : val :=
  𝗳𝘂𝗻 "fn" ->
    list٠iteri (𝗳𝘂𝗻 "_i" -> "fn").

Definition list٠mapi₁ : val :=
  𝗿𝗲𝗰 "mapi" "fn" "i" "t" ->
    𝗺𝗮𝘁𝗰𝗵 "t" 𝘄𝗶𝘁𝗵
    | [] ->
        []
    | "v" :: "t" ->
        𝗹𝗲𝘁 "v" = "fn" "i" "v" 𝗶𝗻
        "v" :: "mapi" "fn" ("i" + 1) "t"
    𝗲𝗻𝗱.

Definition list٠mapi : val :=
  𝗳𝘂𝗻 "fn" ->
    list٠mapi₁ "fn" 0.

Definition list٠map : val :=
  𝗳𝘂𝗻 "fn" ->
    list٠mapi (𝗳𝘂𝗻 "_i" -> "fn").

Definition list٠forall : val :=
  𝗿𝗲𝗰 "forall" "pred" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        true
    | "v" :: "t" ->
        "pred" "v" 𝗮𝗻𝗱 "forall" "pred" "t"
    𝗲𝗻𝗱.

Definition list٠exists : val :=
  𝗿𝗲𝗰 "exists" "pred" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        false
    | "v" :: "t" ->
        "pred" "v" 𝗼𝗿 "exists" "pred" "t"
    𝗲𝗻𝗱.
