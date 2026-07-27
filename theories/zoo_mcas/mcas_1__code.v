Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.program_logic.identifier.
Require Import zoo_std.list.
Require Import zoo_mcas.mcas_1__types.
Require Import zoo.options.

Definition mcas_1٠clear : val :=
  𝗳𝘂𝗻 "cass" "is_after" ->
    𝗶𝗳 "is_after" 𝘁𝗵𝗲𝗻 (
      list٠iter
        (𝗳𝘂𝗻 "cas" -> "cas".<state> <-{before} "cas".<state>.{after})
        "cass"
    ) 𝗲𝗹𝘀𝗲 (
      list٠iter
        (𝗳𝘂𝗻 "cas" -> "cas".<state> <-{after} "cas".<state>.{before})
        "cass"
    ).

Definition mcas_1٠status_to_bool : val :=
  𝗳𝘂𝗻 "status" ->
    "status" == §After.

Definition mcas_1٠finish : val :=
  𝗳𝘂𝗻 "gid" "casn" "status" ->
    𝗺𝗮𝘁𝗰𝗵 "casn".{status} 𝘄𝗶𝘁𝗵
    | Before ->
        false
    | After ->
        true
    | Undetermined "cass" 𝗮𝘀 "old_status" ->
        𝗹𝗲𝘁 "is_after" = mcas_1٠status_to_bool "status" 𝗶𝗻
        𝗶𝗳
          𝗿𝗲𝘀𝗼𝗹𝘃𝗲
            (𝗰𝗮𝘀 "casn".[status] "old_status" "status")
            "casn".{proph}
            ("gid", "is_after")
        𝘁𝗵𝗲𝗻 (
          mcas_1٠clear "cass" "is_after"
        ) 𝗲𝗹𝘀𝗲 (
          ()
        ) ⍮
        mcas_1٠status_to_bool "casn".{status}
    𝗲𝗻𝗱.

#[local] Definition __zoo_recs_0 :=
  ( 𝗿𝗲𝗰𝘀 "determine_as" "casn" "cass" ->
      𝗹𝗲𝘁 "gid" = 𝗶𝗱 𝗶𝗻
      𝗺𝗮𝘁𝗰𝗵 "cass" 𝘄𝗶𝘁𝗵
      | [] ->
          mcas_1٠finish "gid" "casn" §After
      | "cas" :: "continue" 𝗮𝘀 "retry" ->
          𝗹𝗲𝘁 "loc", "state" = "cas" 𝗶𝗻
          𝗹𝗲𝘁 "proph" = 𝗽𝗿𝗼𝗽𝗵 𝗶𝗻
          𝗹𝗲𝘁 "old_state" = !"loc" 𝗶𝗻
          𝗶𝗳 "state" == "old_state" 𝘁𝗵𝗲𝗻 (
            "determine_as" "casn" "continue"
          ) 𝗲𝗹𝘀𝗲 𝗶𝗳
             𝗹𝗲𝘁 "@tmp" =
               "state".{before} == "eval" "old_state"
             𝗶𝗻
             𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "proph" "@tmp" ⍮
             "@tmp"
           𝘁𝗵𝗲𝗻 (
            "lock" "casn" "loc" "old_state" "state" "retry" "continue"
          ) 𝗲𝗹𝘀𝗲 (
            mcas_1٠finish "gid" "casn" §Before
          )
      𝗲𝗻𝗱
    𝘄𝗶𝘁𝗵 "lock" "casn" "loc" "old_state" "state" "retry" "continue" ->
      𝗺𝗮𝘁𝗰𝗵 "casn".{status} 𝘄𝗶𝘁𝗵
      | Before ->
          false
      | After ->
          true
      | Undetermined ⎽ ->
          𝗶𝗳
            𝗰𝗮𝘀 "loc".[contents] "old_state" "state"
          𝘁𝗵𝗲𝗻 (
            "determine_as" "casn" "continue"
          ) 𝗲𝗹𝘀𝗲 (
            "determine_as" "casn" "retry"
          )
      𝗲𝗻𝗱
    𝘄𝗶𝘁𝗵 "eval" "state" ->
      𝗶𝗳 "determine" "state".{casn} 𝘁𝗵𝗲𝗻 (
        "state".{after}
      ) 𝗲𝗹𝘀𝗲 (
        "state".{before}
      )
    𝘄𝗶𝘁𝗵 "determine" "casn" ->
      𝗺𝗮𝘁𝗰𝗵 "casn".{status} 𝘄𝗶𝘁𝗵
      | Before ->
          false
      | After ->
          true
      | Undetermined "cass" ->
          "determine_as" "casn" "cass"
      𝗲𝗻𝗱
  )%zoo_recs.
Definition mcas_1٠determine_as :=
  ValRecs 0 __zoo_recs_0.
Definition mcas_1٠lock :=
  ValRecs 1 __zoo_recs_0.
Definition mcas_1٠eval :=
  ValRecs 2 __zoo_recs_0.
Definition mcas_1٠determine :=
  ValRecs 3 __zoo_recs_0.
#[global] Instance :
  AsValRecs' mcas_1٠determine_as 0 __zoo_recs_0 [
    mcas_1٠determine_as ;
    mcas_1٠lock ;
    mcas_1٠eval ;
    mcas_1٠determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mcas_1٠lock 1 __zoo_recs_0 [
    mcas_1٠determine_as ;
    mcas_1٠lock ;
    mcas_1٠eval ;
    mcas_1٠determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mcas_1٠eval 2 __zoo_recs_0 [
    mcas_1٠determine_as ;
    mcas_1٠lock ;
    mcas_1٠eval ;
    mcas_1٠determine
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mcas_1٠determine 3 __zoo_recs_0 [
    mcas_1٠determine_as ;
    mcas_1٠lock ;
    mcas_1٠eval ;
    mcas_1٠determine
  ].
Proof.
  done.
Qed.

Definition mcas_1٠make : val :=
  𝗳𝘂𝗻 "v" ->
    𝗹𝗲𝘁 "_gid" = 𝗶𝗱 𝗶𝗻
    𝗹𝗲𝘁 "casn" = { §After, 𝗽𝗿𝗼𝗽𝗵 } 𝗶𝗻
    𝗹𝗲𝘁 "state" = { "casn", "v", "v" } 𝗶𝗻
    𝗿𝗲𝗳 "state".

Definition mcas_1٠get : val :=
  𝗳𝘂𝗻 "loc" ->
    mcas_1٠eval !"loc".

Definition mcas_1٠mcas : val :=
  𝗳𝘂𝗻 "cass" ->
    𝗹𝗲𝘁 "casn" = { §After, 𝗽𝗿𝗼𝗽𝗵 } 𝗶𝗻
    𝗹𝗲𝘁 "cass" =
      list٠map
        (𝗳𝘂𝗻 "cas" ->
           𝗹𝗲𝘁 "loc", "before", "after" = "cas" 𝗶𝗻
           𝗹𝗲𝘁 "state" = { "casn", "before", "after" } 𝗶𝗻
           ("loc", "state"))
        "cass"
    𝗶𝗻
    "casn" <-{status} ‘Undetermined@[ "cass" ] ⍮
    mcas_1٠determine_as "casn" "cass".
