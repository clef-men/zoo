Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_persistent.sarray__types.
Require Import zoo.options.

Definition sarray٠make : val :=
  𝗳𝘂𝗻 "equal" "sz" "v" ->
    𝗹𝗲𝘁 "data" = array٠unsafe_make "sz" "v" 𝗶𝗻
    𝗹𝗲𝘁 "root" = 𝗿𝗲𝗳 §Root 𝗶𝗻
    { "equal", "data", "root" }.

Definition sarray٠get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    array٠unsafe_get "t".{data} "i".

Definition sarray٠set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    𝗹𝗲𝘁 "v'" = array٠unsafe_get "t".{data} "i" 𝗶𝗻
    𝗶𝗳 ~ "t".{equal} "v" "v'" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "root" = 𝗿𝗲𝗳 §Root 𝗶𝗻
      "t".{root} <- ‘Diff( "i", "v'", "root" ) ⍮
      "t" <-{root} "root" ⍮
      array٠unsafe_set "t".{data} "i" "v"
    ).

Definition sarray٠capture : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{root}.

Definition sarray٠restore₁ : val :=
  𝗿𝗲𝗰 "restore" "data" "node" ->
    𝗺𝗮𝘁𝗰𝗵 !"node" 𝘄𝗶𝘁𝗵
    | Root ->
        ()
    | Diff "i" "v" "node'" ->
        "restore" "data" "node'" ⍮
        "node'" <- ‘Diff( "i", array٠unsafe_get "data" "i", "node" ) ⍮
        array٠unsafe_set "data" "i" "v"
    𝗲𝗻𝗱.

Definition sarray٠restore : val :=
  𝗳𝘂𝗻 "t" "s" ->
    𝗺𝗮𝘁𝗰𝗵 !"s" 𝘄𝗶𝘁𝗵
    | Root ->
        ()
    | Diff ⎽ ⎽ ⎽ ->
        sarray٠restore₁ "t".{data} "s" ⍮
        "s" <- §Root ⍮
        "t" <-{root} "s"
    𝗲𝗻𝗱.
