From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  assert.
From zoo_persistent Require Import
  pstore_2__types.
From zoo Require Import
  options.

Definition pstore_create : val :=
  fun: <> =>
    { #0, ref §Root }.

Definition pstore_ref : val :=
  fun: "_t" "v" =>
    { #0, "v" }.

Definition pstore_get : val :=
  fun: "_t" "r" =>
    "r".{ref_value}.

Definition pstore_set : val :=
  fun: "t" "r" "v" =>
    let: "g_t" := "t".{gen} in
    let: "g_r" := "r".{ref_gen} in
    if: "g_t" == "g_r" then (
      "r" <-{ref_value} "v"
    ) else (
      let: "root" := ref §Root in
      "t".{root} <- ‘Diff( "r", "g_r", "r".{ref_value}, "root" ) ;;
      "r" <-{ref_gen} "g_t" ;;
      "r" <-{ref_value} "v" ;;
      "t" <-{root} "root"
    ).

Definition pstore_capture : val :=
  fun: "t" =>
    let: "g" := "t".{gen} in
    "t" <-{gen} "g" + #1 ;;
    ("t", "g", "t".{root}).

Definition pstore_collect : val :=
  rec: "collect" "node" "acc" =>
    match: !"node" with
    | Root =>
        ("node", "acc")
    | Diff <> <> <> "node'" =>
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
        | Diff "r" "g" "v" "node_" =>
            assert ("node_" == "node") ;;
            "node" <- ‘Diff( "r", "r".{ref_gen}, "r".{ref_value}, "node'" ) ;;
            "r" <-{ref_gen} "g" ;;
            "r" <-{ref_value} "v" ;;
            "revert" "node'" "path"
        end
    end.

Definition pstore_reroot : val :=
  fun: "node" =>
    let: "root", "path" := pstore_collect "node" [] in
    pstore_revert "root" "path".

Definition pstore_restore : val :=
  fun: "t" "s" =>
    if: "t" != "s".<snap_store> then (
      Fail
    ) else (
      let: "root" := "s".<snap_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> <> =>
          pstore_reroot "root" ;;
          "t" <-{gen} "s".<snap_gen> + #1 ;;
          "t" <-{root} "root"
      end
    ).
