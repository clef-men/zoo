Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.program_logic.assert.
Require Import zoo.options.

Notation "'sstore_1٠Root'" := (
  in_type "zoo_persistent.sstore_1.descr" 0
)(in custom zoo_tag
).
Notation "'sstore_1٠Diff'" := (
  in_type "zoo_persistent.sstore_1.descr" 1
)(in custom zoo_tag
).

Notation "'sstore_1٠snapshot_store'" := (
  in_type "zoo_persistent.sstore_1.snapshot" 0
)(in custom zoo_proj
).
Notation "'sstore_1٠snapshot_root'" := (
  in_type "zoo_persistent.sstore_1.snapshot" 1
)(in custom zoo_proj
).

Definition sstore_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 (𝗿𝗲𝗳 §sstore_1٠Root).

Definition sstore_1٠ref : val :=
  𝗳𝘂𝗻 "_t" "v" ->
    𝗿𝗲𝗳 "v".

Definition sstore_1٠get : val :=
  𝗳𝘂𝗻 "_t" "r" ->
    !"r".

Definition sstore_1٠set : val :=
  𝗳𝘂𝗻 "t" "r" "v" ->
    𝗹𝗲𝘁 "root" = 𝗿𝗲𝗳 §sstore_1٠Root 𝗶𝗻
    !"t" <- ‘sstore_1٠Diff( "r", !"r", "root" ) ⍮
    "r" <- "v" ⍮
    "t" <- "root".

Definition sstore_1٠capture : val :=
  𝗳𝘂𝗻 "t" ->
    ("t", !"t").

Definition sstore_1٠collect : val :=
  𝗿𝗲𝗰 "collect" "node" "acc" ->
    𝗺𝗮𝘁𝗰𝗵 !"node" 𝘄𝗶𝘁𝗵
    | sstore_1٠Root ->
        ("node", "acc")
    | sstore_1٠Diff ⎽ ⎽ "node'" ->
        "collect" "node'" ("node" :: "acc")
    𝗲𝗻𝗱.

Definition sstore_1٠revert : val :=
  𝗿𝗲𝗰 "revert" "node" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        "node" <- §sstore_1٠Root
    | "node'" :: "path" ->
        𝗺𝗮𝘁𝗰𝗵 !"node'" 𝘄𝗶𝘁𝗵
        | sstore_1٠Root ->
            𝗳𝗮𝗶𝗹
        | sstore_1٠Diff "r" "v" "node_" ->
            𝗮𝘀𝘀𝗲𝗿𝘁 ("node_" == "node") ⍮
            "node" <- ‘sstore_1٠Diff( "r", !"r", "node'" ) ⍮
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
    𝗶𝗳 "t" != "s".<sstore_1٠snapshot_store> 𝘁𝗵𝗲𝗻 (
      𝗳𝗮𝗶𝗹
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "root" = "s".<sstore_1٠snapshot_root> 𝗶𝗻
      𝗺𝗮𝘁𝗰𝗵 !"root" 𝘄𝗶𝘁𝗵
      | sstore_1٠Root ->
          ()
      | sstore_1٠Diff ⎽ ⎽ ⎽ ->
          sstore_1٠reroot "root" ⍮
          "t" <- "root"
      𝗲𝗻𝗱
    ).
