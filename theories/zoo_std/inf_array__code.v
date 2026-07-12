Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.mutex.
Require Import zoo_std.array.
Require Import zoo_std.int.
Require Import zoo_std.inf_array__types.
Require Import zoo.options.

Definition inf_array٠create : val :=
  fun: "default" =>
    let: "data" := array٠create () in
    let: "mutex" := mutex٠create () in
    { "data", "default", "mutex" }.

Definition inf_array٠next_capacity : val :=
  fun: "n" =>
    int٠max 8 if: "n" ≤ 512 then (
                 2 * "n"
               ) else (
                 "n" + "n" `quot` 2
               ).

Definition inf_array٠reserve : val :=
  fun: "t" "n" =>
    let: "data" := "t".{data} in
    let: "cap" := array٠size "data" in
    if: "cap" < "n" then (
      let: "cap" := int٠max "n" (inf_array٠next_capacity "cap") in
      let: "data" := array٠unsafe_grow "data" "cap" "t".{default} in
      "t" <-{data} "data"
    ).

Definition inf_array٠get : val :=
  fun: "t" "i" =>
    mutex٠protect "t".{mutex}
      (fun: <> =>
         let: "data" := "t".{data} in
         if: "i" < array٠size "data" then (
           array٠unsafe_get "data" "i"
         ) else (
           "t".{default}
         )).

Definition inf_array٠update : val :=
  fun: "t" "i" "fn" =>
    mutex٠protect "t".{mutex}
      (fun: <> =>
         inf_array٠reserve "t" ("i" + 1) ;;
         let: "v" := array٠unsafe_get "t".{data} "i" in
         array٠unsafe_set "t".{data} "i" ("fn" "v") ;;
         "v").

Definition inf_array٠xchg : val :=
  fun: "t" "i" "v" =>
    inf_array٠update "t" "i" (fun: <> => "v").

Definition inf_array٠xchg_resolve : val :=
  fun: "t" "i" "v" "proph" "v_resolve" =>
    mutex٠protect "t".{mutex}
      (fun: <> =>
         inf_array٠reserve "t" ("i" + 1) ;;
         let: "old_v" := array٠unsafe_get "t".{data} "i" in
         array٠unsafe_set "t".{data} "i" "v" ;;
         Resolve Skip "proph" "v_resolve" ;;
         "old_v").

Definition inf_array٠set : val :=
  fun: "t" "i" "v" =>
    inf_array٠xchg "t" "i" "v" ;;
    ().

Definition inf_array٠cas : val :=
  fun: "t" "i" "v1" "v2" =>
    mutex٠protect "t".{mutex}
      (fun: <> =>
         inf_array٠reserve "t" ("i" + 1) ;;
         let: "res" := array٠unsafe_get "t".{data} "i" == "v1" in
         if: "res" then (
           array٠unsafe_set "t".{data} "i" "v2"
         ) else (
           ()
         ) ;;
         "res").

Definition inf_array٠cas_resolve : val :=
  fun: "t" "i" "v1" "v2" "proph" "v_resolve" =>
    mutex٠protect "t".{mutex}
      (fun: <> =>
         inf_array٠reserve "t" ("i" + 1) ;;
         let: "res" := array٠unsafe_get "t".{data} "i" == "v1" in
         if: "res" then (
           array٠unsafe_set "t".{data} "i" "v2"
         ) else (
           ()
         ) ;;
         Resolve Skip "proph" "v_resolve" ;;
         "res").

Definition inf_array٠faa : val :=
  fun: "t" "i" "incr" =>
    inf_array٠update "t" "i" (fun: "n" => "n" + "incr").
