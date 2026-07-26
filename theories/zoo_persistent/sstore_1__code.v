Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.assert.
Require Import zoo_persistent.sstore_1__types.
Require Import zoo.options.

Definition sstore_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 (𝗿𝗲𝗳 §Root).

Definition sstore_1٠ref : val :=
  𝗳𝘂𝗻 "_t" "v" ->
    𝗿𝗲𝗳 "v".

Definition sstore_1٠get : val :=
  𝗳𝘂𝗻 "_t" "r" ->
    !"r".

Definition sstore_1٠set : val :=
  𝗳𝘂𝗻 "t" "r" "v" ->
    𝗹𝗲𝘁 "root" = 𝗿𝗲𝗳 §Root 𝗶𝗻
    !"t" <- ‘Diff( "r", !"r", "root" ) ⍮
    "r" <- "v" ⍮
    "t" <- "root".

Definition sstore_1٠capture : val :=
  𝗳𝘂𝗻 "t" ->
    ("t", !"t").

Definition sstore_1٠collect : val :=
  𝗿𝗲𝗰 "collect" "node" "acc" ->
    𝗺𝗮𝘁𝗰𝗵 !"node" 𝘄𝗶𝘁𝗵
    | Root ->
        ("node", "acc")
    | Diff ⎽ ⎽ "node'" ->
        "collect" "node'" ("node" :: "acc")
    𝗲𝗻𝗱.

Definition sstore_1٠revert : val :=
  𝗿𝗲𝗰 "revert" "node" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        "node" <- §Root
    | "node'" :: "path" ->
        𝗺𝗮𝘁𝗰𝗵 !"node'" 𝘄𝗶𝘁𝗵
        | Root ->
            𝗳𝗮𝗶𝗹
        | Diff "r" "v" "node_" ->
            𝗮𝘀𝘀𝗲𝗿𝘁 ("node_" == "node") ⍮
            "node" <- ‘Diff( "r", !"r", "node'" ) ⍮
            "r" <- "v" ⍮
            "revert" "node'" "path"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition sstore_1٠reroot : val :=
  𝗳𝘂𝗻 "node" ->
    𝗹𝗲𝘁 "root", "nodes" = sstore_1٠collect "node" [] 𝗶𝗻
    sstore_1٠revert "root" "nodes".

Definition sstore_1٠restore : val :=
  𝗳𝘂𝗻 "t" "s" ->
    𝗶𝗳 "t" != "s".<snapshot_store> 𝘁𝗵𝗲𝗻 (
      𝗳𝗮𝗶𝗹
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "root" = "s".<snapshot_root> 𝗶𝗻
      𝗺𝗮𝘁𝗰𝗵 !"root" 𝘄𝗶𝘁𝗵
      | Root ->
          ()
      | Diff ⎽ ⎽ ⎽ ->
          sstore_1٠reroot "root" ⍮
          "t" <- "root"
      𝗲𝗻𝗱
    ).
