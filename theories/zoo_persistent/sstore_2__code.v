Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.assert.
Require Import zoo.options.

Notation "'sstore_2٠ref_gen'" := (
  in_type "zoo_persistent.sstore_2.ref" 0
)(in custom zoo_field
).
Notation "'sstore_2٠ref_value'" := (
  in_type "zoo_persistent.sstore_2.ref" 1
)(in custom zoo_field
).

Notation "'sstore_2٠Root'" := (
  in_type "zoo_persistent.sstore_2.descr" 0
)(in custom zoo_tag
).
Notation "'sstore_2٠Diff'" := (
  in_type "zoo_persistent.sstore_2.descr" 1
)(in custom zoo_tag
).

Notation "'sstore_2٠gen'" := (
  in_type "zoo_persistent.sstore_2.t" 0
)(in custom zoo_field
).
Notation "'sstore_2٠root'" := (
  in_type "zoo_persistent.sstore_2.t" 1
)(in custom zoo_field
).

Notation "'sstore_2٠snapshot_store'" := (
  in_type "zoo_persistent.sstore_2.snapshot" 0
)(in custom zoo_proj
).
Notation "'sstore_2٠snapshot_gen'" := (
  in_type "zoo_persistent.sstore_2.snapshot" 1
)(in custom zoo_proj
).
Notation "'sstore_2٠snapshot_root'" := (
  in_type "zoo_persistent.sstore_2.snapshot" 2
)(in custom zoo_proj
).

Definition sstore_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { 0, 𝗿𝗲𝗳 §sstore_2٠Root }.

Definition sstore_2٠ref : val :=
  𝗳𝘂𝗻 "_t" "v" ->
    { 0, "v" }.

Definition sstore_2٠get : val :=
  𝗳𝘂𝗻 "_t" "r" ->
    "r".{sstore_2٠ref_value}.

Definition sstore_2٠set : val :=
  𝗳𝘂𝗻 "t" "r" "v" ->
    𝗹𝗲𝘁 "g_t" = "t".{sstore_2٠gen} 𝗶𝗻
    𝗹𝗲𝘁 "g_r" = "r".{sstore_2٠ref_gen} 𝗶𝗻
    𝗶𝗳 "g_t" == "g_r" 𝘁𝗵𝗲𝗻 (
      "r" <-{sstore_2٠ref_value} "v"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "root" = 𝗿𝗲𝗳 §sstore_2٠Root 𝗶𝗻
      "t".{sstore_2٠root} <-
        ‘sstore_2٠Diff( "r", "g_r", "r".{sstore_2٠ref_value}, "root" ) ⍮
      "r" <-{sstore_2٠ref_gen} "g_t" ⍮
      "r" <-{sstore_2٠ref_value} "v" ⍮
      "t" <-{sstore_2٠root} "root"
    ).

Definition sstore_2٠capture : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "g" = "t".{sstore_2٠gen} 𝗶𝗻
    "t" <-{sstore_2٠gen} "g" + 1 ⍮
    ("t", "g", "t".{sstore_2٠root}).

Definition sstore_2٠collect : val :=
  𝗿𝗲𝗰 "collect" "node" "path" ->
    𝗺𝗮𝘁𝗰𝗵 !"node" 𝘄𝗶𝘁𝗵
    | sstore_2٠Root ->
        ("node", "path")
    | sstore_2٠Diff ⎽ ⎽ ⎽ "node'" ->
        "collect" "node'" ("node" :: "path")
    𝗲𝗻𝗱.

Definition sstore_2٠revert : val :=
  𝗿𝗲𝗰 "revert" "node" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        "node" <- §sstore_2٠Root
    | "node'" :: "path" ->
        𝗺𝗮𝘁𝗰𝗵 !"node'" 𝘄𝗶𝘁𝗵
        | sstore_2٠Root ->
            𝗳𝗮𝗶𝗹
        | sstore_2٠Diff "r" "g" "v" "node_" ->
            𝗮𝘀𝘀𝗲𝗿𝘁 ("node_" == "node") ⍮
            "node" <-
              ‘sstore_2٠Diff( "r",
                "r".{sstore_2٠ref_gen},
                "r".{sstore_2٠ref_value},
                "node'"
              ) ⍮
            "r" <-{sstore_2٠ref_gen} "g" ⍮
            "r" <-{sstore_2٠ref_value} "v" ⍮
            "revert" "node'" "path"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition sstore_2٠reroot : val :=
  𝗳𝘂𝗻 "node" ->
    𝗹𝗲𝘁 "root", "path" = sstore_2٠collect "node" [] 𝗶𝗻
    sstore_2٠revert "root" "path".

Definition sstore_2٠restore : val :=
  𝗳𝘂𝗻 "t" "s" ->
    𝗶𝗳 "t" != "s".<sstore_2٠snapshot_store> 𝘁𝗵𝗲𝗻 (
      𝗳𝗮𝗶𝗹
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "root" = "s".<sstore_2٠snapshot_root> 𝗶𝗻
      𝗺𝗮𝘁𝗰𝗵 !"root" 𝘄𝗶𝘁𝗵
      | sstore_2٠Root ->
          ()
      | sstore_2٠Diff ⎽ ⎽ ⎽ ⎽ ->
          sstore_2٠reroot "root" ⍮
          "t" <-{sstore_2٠gen} "s".<sstore_2٠snapshot_gen> + 1 ⍮
          "t" <-{sstore_2٠root} "root"
      𝗲𝗻𝗱
    ).
