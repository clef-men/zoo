From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclass_instances
  notations.
From zoo Require Import
  identifier
  lst.
From zoo.kcas Require Import
  kcas__types.
From zoo Require Import
  options.

Definition kcas_status_to_bool : val :=
  fun: "param" =>
    match: "param" with
    | Undetermined <> =>
        Fail
    | Before =>
        #false
    | After =>
        #true
    end.

Definition kcas_finish : val :=
  fun: "id" "casn" "status" =>
    match: "casn".{status} with
    | Before =>
        #false
    | After =>
        #true
    | Undetermined <> as "old_status" =>
        Resolve
          (CAS "casn".[status] "old_status" "status")
          "casn".{proph}
          ("id", kcas_status_to_bool "status") ;;
        "casn".{status} == §After
    end.

#[local] Definition __zoo_recs_0 := (
  recs: "determine_aux" "casn" "cass" =>
    let: "id" := Id in
    match: "cass" with
    | [] =>
        kcas_finish "id" "casn" §After
    | "cas" :: "cass'" =>
        let: "loc", "state" := "cas" in
        let: "state'" := !"loc" in
        if: "state" == "state'" then (
          "determine_aux" "casn" "cass'"
        ) else (
          let: "v" :=
            if: "determine" "state'".<casn> then (
              "state'".<after>
            ) else (
              "state'".<before>
            )
          in
          if: "v" != "state".<before> then (
            kcas_finish "id" "casn" §Before
          ) else (
            match: "casn".{status} with
            | Before =>
                #false
            | After =>
                #true
            | Undetermined <> =>
                if: CAS "loc".[contents] "state'" "state" then (
                  "determine_aux" "casn" "cass'"
                ) else (
                  "determine_aux" "casn" "cass"
                )
            end
          )
        )
    end
  and: "determine" "casn" =>
    match: "casn".{status} with
    | Before =>
        #false
    | After =>
        #true
    | Undetermined "cass" =>
        "determine_aux" "casn" "cass"
    end
)%zoo_recs.
Definition kcas_determine_aux :=
  ValRecs 0 __zoo_recs_0.
Definition kcas_determine :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' kcas_determine_aux 0 __zoo_recs_0 [
    kcas_determine_aux ;
    kcas_determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' kcas_determine 1 __zoo_recs_0 [
    kcas_determine_aux ;
    kcas_determine
  ].
Proof.
  done.
Qed.

Definition kcas_get : val :=
  fun: "loc" =>
    let: "state" := !"loc" in
    if: kcas_determine "state".<casn> then (
      "state".<after>
    ) else (
      "state".<before>
    ).

Definition kcas_cas : val :=
  fun: "cass" =>
    let: "casn" := { §After, Proph } in
    let: "cass" :=
      lst_map
        "cass"
        (fun: "cas" =>
           let: "loc", "before", "after" := "cas" in
           let: "state" := ("casn", "before", "after") in
           ("loc", "state"))
    in
    "casn" <-{status} Reveal ‘Undetermined( "cass" ) ;;
    kcas_determine_aux "casn" "cass".
