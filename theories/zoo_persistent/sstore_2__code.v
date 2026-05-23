From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  assert.
From zoo_persistent Require Import
  sstore_2__types.
From zoo Require Import
  options.

Definition sstore_2٠create : val :=
  fun: <> =>
    { 0, ref §Root }.

Definition sstore_2٠ref : val :=
  fun: "_t" "v" =>
    { 0, "v" }.

Definition sstore_2٠get : val :=
  fun: "_t" "r" =>
    "r".{ref_value}.

Definition sstore_2٠set : val :=
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

Definition sstore_2٠capture : val :=
  fun: "t" =>
    let: "g" := "t".{gen} in
    "t" <-{gen} "g" + 1 ;;
    ("t", "g", "t".{root}).

Definition sstore_2٠collect : val :=
  rec: "collect" "node" "path" =>
    match: !"node" with
    | Root =>
        ("node", "path")
    | Diff <> <> <> "node'" =>
        "collect" "node'" ("node" :: "path")
    end.

Definition sstore_2٠revert : val :=
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

Definition sstore_2٠reroot : val :=
  fun: "node" =>
    let: "root", "path" := sstore_2٠collect "node" [] in
    sstore_2٠revert "root" "path".

Definition sstore_2٠restore : val :=
  fun: "t" "s" =>
    if: "t" != "s".<snapshot_store> then (
      Fail
    ) else (
      let: "root" := "s".<snapshot_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> <> =>
          sstore_2٠reroot "root" ;;
          "t" <-{gen} "s".<snapshot_gen> + 1 ;;
          "t" <-{root} "root"
      end
    ).
