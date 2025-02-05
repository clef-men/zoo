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
  kcas_2__types.
From zoo Require Import
  options.

Definition kcas_2_status_to_bool : val :=
  fun: "status" =>
    "status" == §After.

Definition kcas_2_finish : val :=
  fun: "gid" "casn" "status" =>
    match: "casn".{status} with
    | Before =>
        #false
    | After =>
        #true
    | Undetermined <> as "old_status" =>
        Resolve
          (CAS "casn".[status] "old_status" "status")
          "casn".{proph}
          ("gid", kcas_2_status_to_bool "status") ;;
        kcas_2_status_to_bool "casn".{status}
    end.

#[local] Definition __zoo_recs_0 := (
  recs: "determine_as" "casn" "cass" =>
    let: "gid" := Id in
    match: "cass" with
    | [] =>
        let: "status" :=
          if:
            lst_forall
              (fun: "cas" => !"cas".<loc> == "cas".<state>)
              "casn".{cmps}
          then (
            §After
          ) else (
            §Before
          )
        in
        kcas_2_finish "gid" "casn" "status"
    | "cas" :: "cass'" =>
        let: "loc", "state" := "cas" in
        let: "proph" := Proph in
        let: "state'" := !"loc" in
        if: "state" == "state'" then (
          "determine_as" "casn" "cass'"
        ) else if:
           Resolve ("state".<before> != "get_as" "state'") "proph" ()
         then (
          kcas_2_finish "gid" "casn" §Before
        ) else (
          match: "casn".{status} with
          | Before =>
              #false
          | After =>
              #true
          | Undetermined <> =>
              if: CAS "loc".[contents] "state'" "state" then (
                "determine_as" "casn" "cass'"
              ) else (
                "determine_as" "casn" "cass"
              )
          end
        )
    end
  and: "get_as" "state" =>
    if: "determine" "state".<casn> then (
      "state".<after>
    ) else (
      "state".<before>
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
Definition kcas_2_determine_as :=
  ValRecs 0 __zoo_recs_0.
Definition kcas_2_get_as :=
  ValRecs 1 __zoo_recs_0.
Definition kcas_2_determine :=
  ValRecs 2 __zoo_recs_0.
#[global] Instance :
  AsValRecs' kcas_2_determine_as 0 __zoo_recs_0 [
    kcas_2_determine_as ;
    kcas_2_get_as ;
    kcas_2_determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' kcas_2_get_as 1 __zoo_recs_0 [
    kcas_2_determine_as ;
    kcas_2_get_as ;
    kcas_2_determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' kcas_2_determine 2 __zoo_recs_0 [
    kcas_2_determine_as ;
    kcas_2_get_as ;
    kcas_2_determine
  ].
Proof.
  done.
Qed.

Definition kcas_2_make : val :=
  fun: "v" =>
    let: "_gid" := Id in
    let: "casn" := { [], §After, Proph } in
    let: "state" := Reveal ("casn", "v", "v") in
    ref "state".

Definition kcas_2_get : val :=
  fun: "loc" =>
    kcas_2_get_as !"loc".

Definition kcas_2_cas_2 : val :=
  fun: "cmps" "cass" =>
    let: "casn" := { "cmps", §After, Proph } in
    let: "cass" :=
      lst_map
        (fun: "cas" =>
           let: "loc", "before", "after" := "cas" in
           let: "state" := Reveal ("casn", "before", "after") in
           ("loc", "state"))
        "cass"
    in
    "casn" <-{status} Reveal ‘Undetermined( "cass" ) ;;
    kcas_2_determine_as "casn" "cass".

Definition kcas_2_cas_1 : val :=
  rec: "cas_1" "acc" "cmps" "cass" =>
    match: "cmps" with
    | [] =>
        kcas_2_cas_2 (lst_rev "acc") "cass"
    | "cmp" :: "cmps" =>
        let: "loc", "expected" := "cmp" in
        let: "state" := !"loc" in
        if: kcas_2_get_as "state" == "expected" then (
          "cas_1" (("loc", "state") :: "acc") "cmps" "cass"
        ) else (
          #false
        )
    end.

Definition kcas_2_cas : val :=
  fun: "cmps" "cass" =>
    kcas_2_cas_1 [] "cmps" "cass".
