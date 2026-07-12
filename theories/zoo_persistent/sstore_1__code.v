Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.assert.
Require Import zoo_persistent.sstore_1__types.
Require Import zoo.options.

Definition sstore_1٠create : val :=
  fun: <> =>
    ref (ref §Root).

Definition sstore_1٠ref : val :=
  fun: "_t" "v" =>
    ref "v".

Definition sstore_1٠get : val :=
  fun: "_t" "r" =>
    !"r".

Definition sstore_1٠set : val :=
  fun: "t" "r" "v" =>
    let: "root" := ref §Root in
    !"t" <- ‘Diff( "r", !"r", "root" ) ;;
    "r" <- "v" ;;
    "t" <- "root".

Definition sstore_1٠capture : val :=
  fun: "t" =>
    ("t", !"t").

Definition sstore_1٠collect : val :=
  rec: "collect" "node" "acc" =>
    match: !"node" with
    | Root =>
        ("node", "acc")
    | Diff <> <> "node'" =>
        "collect" "node'" ("node" :: "acc")
    end.

Definition sstore_1٠revert : val :=
  rec: "revert" "node" "param" =>
    match: "param" with
    | [] =>
        "node" <- §Root
    | "node'" :: "path" =>
        match: !"node'" with
        | Root =>
            Fail
        | Diff "r" "v" "node_" =>
            assert ("node_" == "node") ;;
            "node" <- ‘Diff( "r", !"r", "node'" ) ;;
            "r" <- "v" ;;
            "revert" "node'" "path"
        end
    end.

Definition sstore_1٠reroot : val :=
  fun: "node" =>
    let: "root", "nodes" := sstore_1٠collect "node" [] in
    sstore_1٠revert "root" "nodes".

Definition sstore_1٠restore : val :=
  fun: "t" "s" =>
    if: "t" != "s".<snapshot_store> then (
      Fail
    ) else (
      let: "root" := "s".<snapshot_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> =>
          sstore_1٠reroot "root" ;;
          "t" <- "root"
      end
    ).
