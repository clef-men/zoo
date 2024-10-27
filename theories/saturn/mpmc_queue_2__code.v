From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From saturn Require Import
  mpmc_queue_2__types.
From zoo Require Import
  options.

Definition mpmc_queue_2_rev_0 : val :=
  rec: "rev" "suffix" "prefix" =>
    match: "suffix" with
    | Cons <> <> <> as "suffix" =>
        match: "prefix" with
        | Back <> <> =>
            "suffix"
        | Snoc "i" "v" "prefix" =>
            "rev" ‘Cons( "i", "v", "suffix" ) "prefix"
        end
    end.

Definition mpmc_queue_2_rev : val :=
  fun: "back" =>
    match: "back" with
    | Snoc "i" "v" "prefix" =>
        mpmc_queue_2_rev_0 ‘Cons( "i", "v", ‘Front( "i" + #1 ) ) "prefix"
    end.

Definition mpmc_queue_2_create : val :=
  fun: <> =>
    { ‘Front( #1 ), ‘Back{ #0, §Used } }.

#[local] Definition __zoo_recs_0 := (
  recs: "push_aux" "t" "v" "i" "back" =>
    ifnot: CAS "t".[back] "back" ‘Snoc( "i" + #1, "v", "back" ) then (
      Yield ;;
      "push" "t" "v"
    )
  and: "push" "t" "v" =>
    let: "back" := "t".{back} in
    match: "back" with
    | Snoc "i" <> <> =>
        "push_aux" "t" "v" "i" "back"
    | Back <> <> as "back_r" =>
        let: "i_back" := "back_r".{index} in
        match: "back_r".{move} with
        | Used =>
            "push_aux" "t" "v" "i_back" "back"
        | Snoc "i_move" <> <> as "move" =>
            match: "t".{front} with
            | Front "i_front" as "front" =>
                if:
                  "i_front" < "i_move" and
                  CAS "t".[front] "front" (mpmc_queue_2_rev "move")
                then (
                  "back_r" <-{move} §Used
                )
            |_ =>
                ()
            end ;;
            "push_aux" "t" "v" "i_back" "back"
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
    | Cons <> "v" "suffix" =>
        if: CAS "t".[front] "front" "suffix" then (
          ‘Some( "v" )
        ) else (
          Yield ;;
          "pop" "t"
        )
    | Front "i_front" as "front" =>
        match: "t".{back} with
        | Snoc "i_move" "v" "move_prefix" as "move" =>
            if: "i_front" == "i_move" then (
              if: CAS "t".[back] "move" "move_prefix" then (
                ‘Some( "v" )
              ) else (
                "pop" "t"
              )
            ) else (
              match: ‘Back{ "i_move", "move" } with
              | Back <> <> as "back" =>
                  if: CAS "t".[back] "move" "back" then (
                    "pop_2" "t" "front" "move" "back"
                  ) else (
                    "pop" "t"
                  )
              end
            )
        | Back <> <> as "back" =>
            let: "back_r" := "back" in
            match: "back_r".{move} with
            | Used =>
                "pop_3" "t" "front"
            | Snoc <> <> <> as "move" =>
                "pop_2" "t" "front" "move" "back"
            end
        end
    end
  and: "pop_2" "t" "front" "move" "back" =>
    match: "front" with
    | Front "i_front" as "front" =>
        match: "move" with
        | Snoc "i_move" <> <> =>
            match: "back" with
            | Back <> <> as "back_r" =>
                if: "i_front" < "i_move" then (
                  match: mpmc_queue_2_rev "move" with
                  | Cons <> "v" "suffix" =>
                      if: CAS "t".[front] "front" "suffix" then (
                        "back_r" <-{move} §Used ;;
                        ‘Some( "v" )
                      ) else (
                        Yield ;;
                        "pop" "t"
                      )
                  end
                ) else (
                  "pop_3" "t" "front"
                )
            end
        end
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
