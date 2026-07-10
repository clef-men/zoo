From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  list.
From zoo Require Import
  identifier.
From zoo_mcas Require Import
  mcas__types.
From zoo Require Import
  options.

Definition mcas٠clear : val :=
  fun: "cass" "is_after" =>
    if: "is_after" then (
      list٠iter
        (fun: "cas" => "cas".<state> <-{before} "cas".<state>.{after})
        "cass"
    ) else (
      list٠iter
        (fun: "cas" => "cas".<state> <-{after} "cas".<state>.{before})
        "cass"
    ).

Definition mcas٠status_to_bool : val :=
  fun: "status" =>
    "status" == §After.

Definition mcas٠finish : val :=
  fun: "gid" "casn" "status" =>
    match: "casn".{status} with
    | Before =>
        false
    | After =>
        true
    | Undetermined "cass" as "old_status" =>
        let: "is_after" := mcas٠status_to_bool "status" in
        if:
          Resolve
            (CAS "casn".[status] "old_status" "status")
            "casn".{proph}
            ("gid", "is_after")
        then (
          mcas٠clear "cass" "is_after"
        ) else (
          ()
        ) ;;
        mcas٠status_to_bool "casn".{status}
    end.

#[local] Definition __zoo_recs_0 :=
  ( recs: "determine_as" "casn" "cass" =>
      let: "gid" := Id in
      match: "cass" with
      | [] =>
          mcas٠finish "gid" "casn" §After
      | "cas" :: "continue" as "retry" =>
          let: "loc", "state" := "cas" in
          let: "proph" := Proph in
          let: "old_state" := !"loc" in
          if: "state" == "old_state" then (
            "determine_as" "casn" "continue"
          ) else if:
             let: "@tmp" := "state".{before} == "eval" "old_state" in
             Resolve Skip "proph" "@tmp" ;;
             "@tmp"
           then (
            "lock" "casn" "loc" "old_state" "state" "retry" "continue"
          ) else (
            mcas٠finish "gid" "casn" §Before
          )
      end
    and: "lock" "casn" "loc" "old_state" "state" "retry" "continue" =>
      match: "casn".{status} with
      | Before =>
          false
      | After =>
          true
      | Undetermined <> =>
          if: CAS "loc".[contents] "old_state" "state" then (
            "determine_as" "casn" "continue"
          ) else (
            "determine_as" "casn" "retry"
          )
      end
    and: "eval" "state" =>
      if: "determine" "state".{casn} then (
        "state".{after}
      ) else (
        "state".{before}
      )
    and: "determine" "casn" =>
      match: "casn".{status} with
      | Before =>
          false
      | After =>
          true
      | Undetermined "cass" =>
          "determine_as" "casn" "cass"
      end
  )%zoo_recs.
Definition mcas٠determine_as :=
  ValRecs 0 __zoo_recs_0.
Definition mcas٠lock :=
  ValRecs 1 __zoo_recs_0.
Definition mcas٠eval :=
  ValRecs 2 __zoo_recs_0.
Definition mcas٠determine :=
  ValRecs 3 __zoo_recs_0.
#[global] Instance :
  AsValRecs' mcas٠determine_as 0 __zoo_recs_0 [
    mcas٠determine_as ;
    mcas٠lock ;
    mcas٠eval ;
    mcas٠determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mcas٠lock 1 __zoo_recs_0 [
    mcas٠determine_as ;
    mcas٠lock ;
    mcas٠eval ;
    mcas٠determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mcas٠eval 2 __zoo_recs_0 [
    mcas٠determine_as ;
    mcas٠lock ;
    mcas٠eval ;
    mcas٠determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mcas٠determine 3 __zoo_recs_0 [
    mcas٠determine_as ;
    mcas٠lock ;
    mcas٠eval ;
    mcas٠determine
  ].
Proof.
  done.
Qed.

Definition mcas٠make : val :=
  fun: "v" =>
    let: "_gid" := Id in
    let: "casn" := { §After, Proph } in
    let: "state" := { "casn", "v", "v" } in
    ref "state".

Definition mcas٠get : val :=
  fun: "loc" =>
    mcas٠eval !"loc".

Definition mcas٠mcas : val :=
  fun: "cass" =>
    let: "casn" := { §After, Proph } in
    let: "cass" :=
      list٠map
        (fun: "cas" =>
           let: "loc", "before", "after" := "cas" in
           let: "state" := { "casn", "before", "after" } in
           ("loc", "state"))
        "cass"
    in
    "casn" <-{status} ‘Undetermined@[ "cass" ] ;;
    mcas٠determine_as "casn" "cass".
