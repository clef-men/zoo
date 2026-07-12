Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_saturn.spmc_queue__types.
Require Import zoo.options.

Definition spmc_queue٠create : val :=
  fun: <> =>
    let: "front" := ‘Node{ §Null, () } in
    { "front", "front" }.

Definition spmc_queue٠is_empty : val :=
  fun: "t" =>
    match: "t".{front} with
    | Node <> <> as "front_r" =>
        "front_r".{next} == §Null
    end.

Definition spmc_queue٠push : val :=
  fun: "t" "v" =>
    match: ‘Node{ §Null, "v" } with
    | Node <> <> as "new_back" =>
        match: "t".{back} with
        | Node <> <> as "back_r" =>
            "back_r" <-{next} "new_back" ;;
            "t" <-{back} "new_back"
        end
    end.

Definition spmc_queue٠pop : val :=
  rec: "pop" "t" =>
    match: "t".{front} with
    | Node <> <> as "front" =>
        let: "front_r" := "front" in
        match: "front_r".{next} with
        | Null =>
            §None
        | Node <> <> as "new_front" =>
            let: "new_front_r" := "new_front" in
            if: CAS "t".[front] "front" "new_front" then (
              let: "v" := "new_front_r".{data} in
              "new_front_r" <-{data} () ;;
              ‘Some( "v" )
            ) else (
              domain٠yield () ;;
              "pop" "t"
            )
        end
    end.
