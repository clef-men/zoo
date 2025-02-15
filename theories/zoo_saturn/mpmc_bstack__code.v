From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo_saturn Require Import
  mpmc_bstack__types.
From zoo Require Import
  options.

Definition mpmc_bstack_create : val :=
  fun: "cap" =>
    { "cap", §Nil }.

Definition mpmc_bstack_size : val :=
  fun: "t" =>
    match: "t".{front} with
    | Nil =>
        #0
    | Cons "sz" <> <> =>
        "sz"
    end.

Definition mpmc_bstack_is_empty : val :=
  fun: "t" =>
    "t".{front} == §Nil.

#[local] Definition __zoo_recs_0 := (
  recs: "push_aux" "t" "sz" "v" "front" =>
    let: "new_front" := ‘Cons[ "sz" + #1, "v", "front" ] in
    if: CAS "t".[front] "front" "new_front" then (
      #true
    ) else (
      domain_yield () ;;
      "push" "t" "v"
    )
  and: "push" "t" "v" =>
    match: "t".{front} with
    | Nil =>
        "push_aux" "t" #0 "v" §Nil
    | Cons "sz" <> <> as "front" =>
        if: "t".{capacity} ≤ "sz" then (
          #false
        ) else (
          "push_aux" "t" "sz" "v" "front"
        )
    end
)%zoo_recs.
Definition mpmc_bstack_push_aux :=
  ValRecs 0 __zoo_recs_0.
Definition mpmc_bstack_push :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' mpmc_bstack_push_aux 0 __zoo_recs_0 [
    mpmc_bstack_push_aux ;
    mpmc_bstack_push
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_bstack_push 1 __zoo_recs_0 [
    mpmc_bstack_push_aux ;
    mpmc_bstack_push
  ].
Proof.
  done.
Qed.

Definition mpmc_bstack_pop : val :=
  rec: "pop" "t" =>
    match: "t".{front} with
    | Nil =>
        §None
    | Cons <> "v" "new_front" as "front" =>
        if: CAS "t".[front] "front" "new_front" then (
          ‘Some( "v" )
        ) else (
          domain_yield () ;;
          "pop" "t"
        )
    end.
