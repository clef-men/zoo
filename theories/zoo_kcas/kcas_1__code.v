From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  identifier.
From zoo_std Require Import
  lst.
From zoo_kcas Require Import
  kcas_1__types.
From zoo Require Import
  options.

Definition kcas_1_clear : val :=
  fun: "cass" "is_after" =>
    if: "is_after" then (
      lst_iter
        (fun: "cas" => "cas".<state> <-{before} "cas".<state>.{after})
        "cass"
    ) else (
      lst_iter
        (fun: "cas" => "cas".<state> <-{after} "cas".<state>.{before})
        "cass"
    ).

Definition kcas_1_status_to_bool : val :=
  fun: "status" =>
    "status" == §After.

Definition kcas_1_finish : val :=
  fun: "gid" "casn" "status" =>
    match: "casn".{status} with
    | Before =>
        #false
    | After =>
        #true
    | Undetermined "cass" as "old_status" =>
        let: "is_after" := kcas_1_status_to_bool "status" in
        if:
          Resolve
            (CAS "casn".[status] "old_status" "status")
            "casn".{proph}
            ("gid", "is_after")
        then (
          kcas_1_clear "cass" "is_after"
        ) else (
          ()
        ) ;;
        kcas_1_status_to_bool "casn".{status}
    end.

#[local] Definition __zoo_recs_0 := (
  recs: "determine_as" "casn" "cass" =>
    let: "gid" := Id in
    match: "cass" with
    | [] =>
        kcas_1_finish "gid" "casn" §After
    | "cas" :: "continue" as "retry" =>
        let: "loc", "state" := "cas" in
        let: "proph" := Proph in
        let: "old_state" := !"loc" in
        if: "state" == "old_state" then (
          "determine_as" "casn" "continue"
        ) else if:
           Resolve ("state".{before} == "eval" "old_state") "proph" ()
         then (
          "lock" "casn" "loc" "old_state" "state" "retry" "continue"
        ) else (
          kcas_1_finish "gid" "casn" §Before
        )
    end
  and: "lock" "casn" "loc" "old_state" "state" "retry" "continue" =>
    match: "casn".{status} with
    | Before =>
        #false
    | After =>
        #true
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
        #false
    | After =>
        #true
    | Undetermined "cass" =>
        "determine_as" "casn" "cass"
    end
)%zoo_recs.
Definition kcas_1_determine_as :=
  ValRecs 0 __zoo_recs_0.
Definition kcas_1_lock :=
  ValRecs 1 __zoo_recs_0.
Definition kcas_1_eval :=
  ValRecs 2 __zoo_recs_0.
Definition kcas_1_determine :=
  ValRecs 3 __zoo_recs_0.
#[global] Instance :
  AsValRecs' kcas_1_determine_as 0 __zoo_recs_0 [
    kcas_1_determine_as ;
    kcas_1_lock ;
    kcas_1_eval ;
    kcas_1_determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' kcas_1_lock 1 __zoo_recs_0 [
    kcas_1_determine_as ;
    kcas_1_lock ;
    kcas_1_eval ;
    kcas_1_determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' kcas_1_eval 2 __zoo_recs_0 [
    kcas_1_determine_as ;
    kcas_1_lock ;
    kcas_1_eval ;
    kcas_1_determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' kcas_1_determine 3 __zoo_recs_0 [
    kcas_1_determine_as ;
    kcas_1_lock ;
    kcas_1_eval ;
    kcas_1_determine
  ].
Proof.
  done.
Qed.

Definition kcas_1_make : val :=
  fun: "v" =>
    let: "_gid" := Id in
    let: "casn" := { §After, Proph } in
    let: "state" := { "casn", "v", "v" } in
    ref "state".

Definition kcas_1_get : val :=
  fun: "loc" =>
    kcas_1_eval !"loc".

Definition kcas_1_cas : val :=
  fun: "cass" =>
    let: "casn" := { §After, Proph } in
    let: "cass" :=
      lst_map
        (fun: "cas" =>
           let: "loc", "before", "after" := "cas" in
           let: "state" := { "casn", "before", "after" } in
           ("loc", "state"))
        "cass"
    in
    "casn" <-{status} ‘Undetermined@[ "cass" ] ;;
    kcas_1_determine_as "casn" "cass".
