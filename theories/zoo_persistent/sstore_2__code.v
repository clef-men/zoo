Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.assert.
Require Import zoo_persistent.sstore_2__types.
Require Import zoo.options.

Definition sstore_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { 0, 𝗿𝗲𝗳 §Root }.

Definition sstore_2٠ref : val :=
  𝗳𝘂𝗻 "_t" "v" ->
    { 0, "v" }.

Definition sstore_2٠get : val :=
  𝗳𝘂𝗻 "_t" "r" ->
    "r".{ref_value}.

Definition sstore_2٠set : val :=
  𝗳𝘂𝗻 "t" "r" "v" ->
    𝗹𝗲𝘁 "g_t" = "t".{gen} 𝗶𝗻
    𝗹𝗲𝘁 "g_r" = "r".{ref_gen} 𝗶𝗻
    𝗶𝗳 "g_t" == "g_r" 𝘁𝗵𝗲𝗻 (
      "r" <-{ref_value} "v"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "root" = 𝗿𝗲𝗳 §Root 𝗶𝗻
      "t".{root} <- ‘Diff( "r", "g_r", "r".{ref_value}, "root" ) ⍮
      "r" <-{ref_gen} "g_t" ⍮
      "r" <-{ref_value} "v" ⍮
      "t" <-{root} "root"
    ).

Definition sstore_2٠capture : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "g" = "t".{gen} 𝗶𝗻
    "t" <-{gen} "g" + 1 ⍮
    ("t", "g", "t".{root}).

Definition sstore_2٠collect : val :=
  𝗿𝗲𝗰 "collect" "node" "path" ->
    𝗺𝗮𝘁𝗰𝗵 !"node" 𝘄𝗶𝘁𝗵
    | Root ->
        ("node", "path")
    | Diff ⎽ ⎽ ⎽ "node'" ->
        "collect" "node'" ("node" :: "path")
    𝗲𝗻𝗱.

Definition sstore_2٠revert : val :=
  𝗿𝗲𝗰 "revert" "node" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        "node" <- §Root
    | "node'" :: "path" ->
        𝗺𝗮𝘁𝗰𝗵 !"node'" 𝘄𝗶𝘁𝗵
        | Root ->
            𝗳𝗮𝗶𝗹
        | Diff "r" "g" "v" "node_" ->
            𝗮𝘀𝘀𝗲𝗿𝘁 ("node_" == "node") ⍮
            "node" <- ‘Diff( "r", "r".{ref_gen}, "r".{ref_value}, "node'" ) ⍮
            "r" <-{ref_gen} "g" ⍮
            "r" <-{ref_value} "v" ⍮
            "revert" "node'" "path"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition sstore_2٠reroot : val :=
  𝗳𝘂𝗻 "node" ->
    𝗹𝗲𝘁 "root", "path" = sstore_2٠collect "node" [] 𝗶𝗻
    sstore_2٠revert "root" "path".

Definition sstore_2٠restore : val :=
  𝗳𝘂𝗻 "t" "s" ->
    𝗶𝗳 "t" != "s".<snapshot_store> 𝘁𝗵𝗲𝗻 (
      𝗳𝗮𝗶𝗹
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "root" = "s".<snapshot_root> 𝗶𝗻
      𝗺𝗮𝘁𝗰𝗵 !"root" 𝘄𝗶𝘁𝗵
      | Root ->
          ()
      | Diff ⎽ ⎽ ⎽ ⎽ ->
          sstore_2٠reroot "root" ⍮
          "t" <-{gen} "s".<snapshot_gen> + 1 ⍮
          "t" <-{root} "root"
      𝗲𝗻𝗱
    ).
