Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpmc_queue_2__types.
Require Import zoo.options.

Definition mpmc_queue_2٠suffix_index : val :=
  fun: "suff" =>
    match: "suff" with
    | Front "i" =>
        "i"
    | Cons "i" <> <> =>
        "i"
    end.

Definition mpmc_queue_2٠prefix_index : val :=
  fun: "pref" =>
    match: "pref" with
    | Back <> <> as "back_r" =>
        "back_r".{index}
    | Snoc "i" <> <> =>
        "i"
    end.

Definition mpmc_queue_2٠rev₀ : val :=
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

Definition mpmc_queue_2٠rev : val :=
  fun: "back" =>
    match: "back" with
    | Snoc "i" "v" "pref" =>
        mpmc_queue_2٠rev₀ ‘Cons[ "i", "v", ‘Front[ "i" + 1 ] ] "pref"
    end.

Definition mpmc_queue_2٠create : val :=
  fun: <> =>
    { ‘Front[ 1 ], ‘Back{ 0, §Used } }.

Definition mpmc_queue_2٠size : val :=
  rec: "size" "t" =>
    let: "front" := "t".{front} in
    let: "proph" := Proph in
    let: "back" := "t".{back} in
    if:
      let: "@tmp" := "t".{front} == "front" in
      Resolve Skip "proph" "@tmp" ;;
      "@tmp"
    then (
      mpmc_queue_2٠prefix_index "back" - mpmc_queue_2٠suffix_index "front"
      +
      1
    ) else (
      "size" "t"
    ).

Definition mpmc_queue_2٠is_empty : val :=
  fun: "t" =>
    mpmc_queue_2٠size "t" == 0.

Definition mpmc_queue_2٠finish : val :=
  fun: "back" =>
    match: "back" with
    | Back <> <> as "back_r" =>
        "back_r" <-{move} §Used
    end.

Definition mpmc_queue_2٠help : val :=
  fun: "t" "back" "i_move" "move" =>
    match: "t".{front} with
    | Front "i_front" as "front" =>
        if:
          "i_move" < "i_front"
          or
          CAS "t".[front] "front" (mpmc_queue_2٠rev "move")
        then (
          mpmc_queue_2٠finish "back"
        )
    |_ =>
        mpmc_queue_2٠finish "back"
    end.

#[local] Definition __zoo_recs_0 :=
  ( recs: "push_aux" "t" "v" "i" "back" =>
      let: "new_back" := ‘Snoc[ "i" + 1, "v", "back" ] in
      if: ~ CAS "t".[back] "back" "new_back" then (
        domain٠yield () ;;
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
              mpmc_queue_2٠help "t" "back" "i_move" "move" ;;
              "push" "t" "v"
          end
      end
  )%zoo_recs.
Definition mpmc_queue_2٠push_aux :=
  ValRecs 0 __zoo_recs_0.
Definition mpmc_queue_2٠push :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠push_aux 0 __zoo_recs_0 [
    mpmc_queue_2٠push_aux ;
    mpmc_queue_2٠push
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠push 1 __zoo_recs_0 [
    mpmc_queue_2٠push_aux ;
    mpmc_queue_2٠push
  ].
Proof.
  done.
Qed.

#[local] Definition __zoo_recs_1 :=
  ( recs: "pop_1" "t" "front" =>
      match: "front" with
      | Cons <> "v" "new_front" =>
          if: CAS "t".[front] "front" "new_front" then (
            ‘Some( "v" )
          ) else (
            domain٠yield () ;;
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
          | Back <> <> =>
              "pop_3" "t" "front"
          end
      end
    and: "pop_2" "t" "front" "back" "move" =>
      match: mpmc_queue_2٠rev "move" with
      | Cons <> "v" "new_front" =>
          if: CAS "t".[front] "front" "new_front" then (
            mpmc_queue_2٠finish "back" ;;
            ‘Some( "v" )
          ) else (
            domain٠yield () ;;
            "pop" "t"
          )
      end
    and: "pop_3" "t" "front" =>
      let: "front'" := "t".{front} in
      if: "front'" == "front" then (
        §None
      ) else (
        "pop_1" "t" "front'"
      )
    and: "pop" "t" =>
      "pop_1" "t" "t".{front}
  )%zoo_recs.
Definition mpmc_queue_2٠pop_1 :=
  ValRecs 0 __zoo_recs_1.
Definition mpmc_queue_2٠pop_2 :=
  ValRecs 1 __zoo_recs_1.
Definition mpmc_queue_2٠pop_3 :=
  ValRecs 2 __zoo_recs_1.
Definition mpmc_queue_2٠pop :=
  ValRecs 3 __zoo_recs_1.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠pop_1 0 __zoo_recs_1 [
    mpmc_queue_2٠pop_1 ;
    mpmc_queue_2٠pop_2 ;
    mpmc_queue_2٠pop_3 ;
    mpmc_queue_2٠pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠pop_2 1 __zoo_recs_1 [
    mpmc_queue_2٠pop_1 ;
    mpmc_queue_2٠pop_2 ;
    mpmc_queue_2٠pop_3 ;
    mpmc_queue_2٠pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠pop_3 2 __zoo_recs_1 [
    mpmc_queue_2٠pop_1 ;
    mpmc_queue_2٠pop_2 ;
    mpmc_queue_2٠pop_3 ;
    mpmc_queue_2٠pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2٠pop 3 __zoo_recs_1 [
    mpmc_queue_2٠pop_1 ;
    mpmc_queue_2٠pop_2 ;
    mpmc_queue_2٠pop_3 ;
    mpmc_queue_2٠pop
  ].
Proof.
  done.
Qed.
