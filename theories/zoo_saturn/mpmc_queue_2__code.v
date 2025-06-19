From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo_saturn Require Import
  mpmc_queue_2__types.
From zoo Require Import
  options.

Definition mpmc_queue_2_suffix_index : val :=
  fun: "suff" =>
    match: "suff" with
    | Front "i" =>
        "i"
    | Cons "i" <> <> =>
        "i"
    end.

Definition mpmc_queue_2_prefix_index : val :=
  fun: "pref" =>
    match: "pref" with
    | Back <> <> as "back_r" =>
        "back_r".{index}
    | Snoc "i" <> <> =>
        "i"
    end.

Definition mpmc_queue_2_rev_0 : val :=
  rec: "rev" "suff" "pref" =>
    match: "suff" with
    | Cons <> <> <> as "suff" =>
        match: "pref" with
        | Back <> <> =>
            "suff"
        | Snoc "i" "v" "pref" =>
            "rev" ‘Cons[ "i", "v", "suff" ] "pref"
        end
    end.

Definition mpmc_queue_2_rev : val :=
  fun: "back" =>
    match: "back" with
    | Snoc "i" "v" "pref" =>
        mpmc_queue_2_rev_0 ‘Cons[ "i", "v", ‘Front[ "i" + #1 ] ] "pref"
    end.

Definition mpmc_queue_2_create : val :=
  fun: <> =>
    { ‘Front[ #1 ], ‘Back{ #0, §Used } }.

Definition mpmc_queue_2_size : val :=
  rec: "size" "t" =>
    let: "front" := "t".{front} in
    let: "proph" := Proph in
    let: "back" := "t".{back} in
    if:
      let: "__tmp__" := "t".{front} == "front" in
      Resolve Skip "proph" "__tmp__" ;;
      "__tmp__"
    then (
      mpmc_queue_2_prefix_index "back" - mpmc_queue_2_suffix_index "front"
      +
      #1
    ) else (
      "size" "t"
    ).

Definition mpmc_queue_2_is_empty : val :=
  fun: "t" =>
    mpmc_queue_2_size "t" == #0.

Definition mpmc_queue_2_finish : val :=
  fun: "back" =>
    match: "back" with
    | Back <> <> as "back_r" =>
        "back_r" <-{move} §Used
    end.

Definition mpmc_queue_2_help : val :=
  fun: "t" "back" "i_move" "move" =>
    match: "t".{front} with
    | Front "i_front" as "front" =>
        if:
          "i_move" < "i_front"
          or
          CAS "t".[front] "front" (mpmc_queue_2_rev "move")
        then (
          mpmc_queue_2_finish "back"
        )
    |_ =>
        mpmc_queue_2_finish "back"
    end.

#[local] Definition __zoo_recs_0 := (
  recs: "push_aux" "t" "v" "i" "back" =>
    let: "new_back" := ‘Snoc[ "i" + #1, "v", "back" ] in
    if: ~ CAS "t".[back] "back" "new_back" then (
      domain_yield () ;;
      "push" "t" "v"
    )
  and: "push" "t" "v" =>
    match: "t".{back} with
    | Snoc "i" <> <> as "back" =>
        "push_aux" "t" "v" "i" "back"
    | Back <> <> as "back" =>
        let: "back_r" := "back" in
        match: "back_r".{move} with
        | Used =>
            "push_aux" "t" "v" "back_r".{index} "back"
        | Snoc "i_move" <> <> as "move" =>
            mpmc_queue_2_help "t" "back" "i_move" "move" ;;
            "push" "t" "v"
        end
    end
)%zoo_recs.
Definition mpmc_queue_2_push_aux :=
  ValRecs 0 __zoo_recs_0.
Definition mpmc_queue_2_push :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' mpmc_queue_2_push_aux 0 __zoo_recs_0 [
    mpmc_queue_2_push_aux ;
    mpmc_queue_2_push
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2_push 1 __zoo_recs_0 [
    mpmc_queue_2_push_aux ;
    mpmc_queue_2_push
  ].
Proof.
  done.
Qed.

#[local] Definition __zoo_recs_1 := (
  recs: "pop_1" "t" "front" =>
    match: "front" with
    | Cons <> "v" "new_front" =>
        if: CAS "t".[front] "front" "new_front" then (
          ‘Some( "v" )
        ) else (
          domain_yield () ;;
          "pop" "t"
        )
    | Front "i_front" as "front" =>
        match: "t".{back} with
        | Snoc "i_move" "v" "move_pref" as "move" =>
            if: "i_front" == "i_move" then (
              if: CAS "t".[back] "move" "move_pref" then (
                ‘Some( "v" )
              ) else (
                "pop" "t"
              )
            ) else (
              match: ‘Back{ "i_move", "move" } with
              | Back <> <> as "back" =>
                  let: "front'" := "t".{front} in
                  if: "front'" != "front" then (
                    "pop_1" "t" "front'"
                  ) else if: CAS "t".[back] "move" "back" then (
                    "pop_2" "t" "front" "back" "move"
                  ) else (
                    "pop" "t"
                  )
              end
            )
        | Back <> <> as "back" =>
            let: "back_r" := "back" in
            let: "proph" := Proph in
            match: "back_r".{move} with
            | Used =>
                "pop_3" "t" "proph" "front"
            | Snoc "i_move" <> <> as "move" =>
                if: "i_front" < "i_move" then (
                  "pop_2" "t" "front" "back" "move"
                ) else (
                  "pop_3" "t" "proph" "front"
                )
            end
        end
    end
  and: "pop_2" "t" "front" "back" "move" =>
    match: mpmc_queue_2_rev "move" with
    | Cons <> "v" "new_front" =>
        if: CAS "t".[front] "front" "new_front" then (
          mpmc_queue_2_finish "back" ;;
          ‘Some( "v" )
        ) else (
          domain_yield () ;;
          "pop" "t"
        )
    end
  and: "pop_3" "t" "proph" "front" =>
    let: "front'" :=
      let: "__tmp__" := "t".{front} in
      Resolve Skip "proph" "__tmp__" ;;
      "__tmp__"
    in
    if: "front'" != "front" then (
      "pop_1" "t" "front'"
    ) else (
      §None
    )
  and: "pop" "t" =>
    "pop_1" "t" "t".{front}
)%zoo_recs.
Definition mpmc_queue_2_pop_1 :=
  ValRecs 0 __zoo_recs_1.
Definition mpmc_queue_2_pop_2 :=
  ValRecs 1 __zoo_recs_1.
Definition mpmc_queue_2_pop_3 :=
  ValRecs 2 __zoo_recs_1.
Definition mpmc_queue_2_pop :=
  ValRecs 3 __zoo_recs_1.
#[global] Instance :
  AsValRecs' mpmc_queue_2_pop_1 0 __zoo_recs_1 [
    mpmc_queue_2_pop_1 ;
    mpmc_queue_2_pop_2 ;
    mpmc_queue_2_pop_3 ;
    mpmc_queue_2_pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2_pop_2 1 __zoo_recs_1 [
    mpmc_queue_2_pop_1 ;
    mpmc_queue_2_pop_2 ;
    mpmc_queue_2_pop_3 ;
    mpmc_queue_2_pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2_pop_3 2 __zoo_recs_1 [
    mpmc_queue_2_pop_1 ;
    mpmc_queue_2_pop_2 ;
    mpmc_queue_2_pop_3 ;
    mpmc_queue_2_pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2_pop 3 __zoo_recs_1 [
    mpmc_queue_2_pop_1 ;
    mpmc_queue_2_pop_2 ;
    mpmc_queue_2_pop_3 ;
    mpmc_queue_2_pop
  ].
Proof.
  done.
Qed.
