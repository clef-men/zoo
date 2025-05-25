From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  assert.
From zoo_persistent Require Import
  pstore_1__types.
From zoo Require Import
  options.

Definition pstore_create : val :=
  fun: <> =>
    ref (ref §Root).

Definition pstore_ref : val :=
  fun: "_t" "v" =>
    ref "v".

Definition pstore_get : val :=
  fun: "_t" "r" =>
    !"r".

Definition pstore_set : val :=
  fun: "t" "r" "v" =>
    let: "root" := ref §Root in
    !"t" <- ‘Diff( "r", !"r", "root" ) ;;
    "r" <- "v" ;;
    "t" <- "root".

Definition pstore_capture : val :=
  fun: "t" =>
    ("t", !"t").

Definition pstore_collect : val :=
  rec: "collect" "node" "acc" =>
    match: !"node" with
    | Root =>
        ("node", "acc")
    | Diff <> <> "node'" =>
        "collect" "node'" ("node" :: "acc")
    end.

Definition pstore_revert : val :=
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

Definition pstore_reroot : val :=
  fun: "node" =>
    let: "root", "nodes" := pstore_collect "node" [] in
    pstore_revert "root" "nodes".

Definition pstore_restore : val :=
  fun: "t" "s" =>
    if: "t" != "s".<snapshot_store> then (
      Fail
    ) else (
      let: "root" := "s".<snapshot_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> =>
          pstore_reroot "root" ;;
          "t" <- "root"
      end
    ).
