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

Definition mpmc_queue_2_size : val :=
  rec: "size" "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" != "t".{front} then (
      "size" "t"
    ) else (
      let: "i_front" :=
        match: "front" with
        | Front "i" =>
            "i"
        | Cons "i" <> <> =>
            "i"
        end
      in
      let: "i_back" :=
        match: "back" with
        | Back <> <> as "back_r" =>
            "back_r".{index}
        | Snoc "i" <> <> =>
            "i"
        end
      in
      "i_back" - "i_front" + #1
    ).

Definition mpmc_queue_2_is_empty : val :=
  fun: "t" =>
    mpmc_queue_2_size "t" == #0.

Definition mpmc_queue_2_help : val :=
  fun: "t" "back" "i_move" "move" =>
    match: "back" with
    | Back <> <> as "back_r" =>
        match: "t".{front} with
        | Front "i_front" as "front" =>
            if:
              "i_move" ≤ "i_front" or
              CAS "t".[front] "front" (mpmc_queue_2_rev "move")
            then (
              "back_r" <-{move} §Used
            )
        |_ =>
            "back_r" <-{move} §Used
        end
    end.

#[local] Definition __zoo_recs_0 := (
  recs: "push_back_aux" "t" "v" "i" "back" =>
    let: "new_back" := ‘Snoc( "i" + #1, "v", "back" ) in
    if: ~ CAS "t".[back] "back" "new_back" then (
      domain_yield () ;;
      "push_back" "t" "v"
    )
  and: "push_back" "t" "v" =>
    match: "t".{back} with
    | Snoc "i" <> <> as "back" =>
        "push_back_aux" "t" "v" "i" "back"
    | Back <> <> as "back" =>
        let: "back_r" := "back" in
        match: "back_r".{move} with
        | Used =>
            "push_back_aux" "t" "v" "back_r".{index} "back"
        | Snoc "i_move" <> <> as "move" =>
            mpmc_queue_2_help "t" "back" "i_move" "move" ;;
            "push_back" "t" "v"
        end
    end
)%zoo_recs.
Definition mpmc_queue_2_push_back_aux :=
  ValRecs 0 __zoo_recs_0.
Definition mpmc_queue_2_push_back :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' mpmc_queue_2_push_back_aux 0 __zoo_recs_0 [
    mpmc_queue_2_push_back_aux ;
    mpmc_queue_2_push_back
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2_push_back 1 __zoo_recs_0 [
    mpmc_queue_2_push_back_aux ;
    mpmc_queue_2_push_back
  ].
Proof.
  done.
Qed.

Definition mpmc_queue_2_push_front : val :=
  rec: "push_front" "t" "v" =>
    match: "t".{front} with
    | Cons "i" <> <> as "front" =>
        let: "new_front" := ‘Cons( "i" - #1, "v", "front" ) in
        if: ~ CAS "t".[front] "front" "new_front" then (
          domain_yield () ;;
          "push_front" "t" "v"
        )
    | Front "i_front" as "front" =>
        match: "t".{back} with
        | Snoc "i_back" "v_back" "prefix" as "back" =>
            if: "i_front" == "i_back" then (
              let: "new_back" :=
                ‘Snoc( "i_back" + #1,
                  "v_back",
                  ‘Snoc( "i_back", "v", "prefix" )
                )
              in
              if: ~ CAS "t".[back] "back" "new_back" then (
                domain_yield () ;;
                "push_front" "t" "v"
              )
            ) else (
              let: "new_back" := ‘Back{ "i_back", "back" } in
              if: ~ CAS "t".[back] "back" "new_back" then (
                domain_yield ()
              ) else (
                ()
              ) ;;
              "push_front" "t" "v"
            )
        | Back <> <> as "back" =>
            let: "back_r" := "back" in
            match: "back_r".{move} with
            | Used =>
                if: "t".{front} == "front" then (
                  let: "new_back" :=
                    ‘Snoc( "back_r".{index} + #1, "v", "back" )
                  in
                  if: ~ CAS "t".[back] "back" "new_back" then (
                    domain_yield () ;;
                    "push_front" "t" "v"
                  )
                ) else (
                  "push_front" "t" "v"
                )
            | Snoc "i_move" <> <> as "move" =>
                mpmc_queue_2_help "t" "back" "i_move" "move" ;;
                "push_front" "t" "v"
            end
        end
    end.

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
                  let: "back_r" := "back" in
                  if: CAS "t".[back] "move" "back" then (
                    match: mpmc_queue_2_rev "move" with
                    | Cons <> "v" "new_front" =>
                        if: CAS "t".[front] "front" "new_front" then (
                          "back_r" <-{move} §Used ;;
                          ‘Some( "v" )
                        ) else (
                          domain_yield () ;;
                          "pop" "t"
                        )
                    end
                  ) else (
                    "pop" "t"
                  )
              end
            )
        | Back <> <> as "back_r" =>
            match: "back_r".{move} with
            | Used =>
                "pop_2" "t" "front"
            | Snoc "i_move" <> <> as "move" =>
                if: "i_front" < "i_move" then (
                  match: mpmc_queue_2_rev "move" with
                  | Cons <> "v" "new_front" =>
                      if: CAS "t".[front] "front" "new_front" then (
                        "back_r" <-{move} §Used ;;
                        ‘Some( "v" )
                      ) else (
                        domain_yield () ;;
                        "pop" "t"
                      )
                  end
                ) else (
                  "pop_2" "t" "front"
                )
            end
        end
    end
  and: "pop_2" "t" "front" =>
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
Definition mpmc_queue_2_pop :=
  ValRecs 2 __zoo_recs_1.
#[global] Instance :
  AsValRecs' mpmc_queue_2_pop_1 0 __zoo_recs_1 [
    mpmc_queue_2_pop_1 ;
    mpmc_queue_2_pop_2 ;
    mpmc_queue_2_pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2_pop_2 1 __zoo_recs_1 [
    mpmc_queue_2_pop_1 ;
    mpmc_queue_2_pop_2 ;
    mpmc_queue_2_pop
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' mpmc_queue_2_pop 2 __zoo_recs_1 [
    mpmc_queue_2_pop_1 ;
    mpmc_queue_2_pop_2 ;
    mpmc_queue_2_pop
  ].
Proof.
  done.
Qed.
