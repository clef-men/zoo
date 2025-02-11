From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  structeq.
From zoo_std Require Import
  domain.
From zoo_saturn Require Import
  mpmc_bqueue__types.
From zoo Require Import
  options.

Definition mpmc_bqueue_create : val :=
  fun: "cap" =>
    let: "front" := ‘Node{ (), (), #0, "cap" } in
    { "cap", "front", "front" }.

Definition mpmc_bqueue_capacity : val :=
  fun: "t" =>
    "t".{capacity}.

Definition mpmc_bqueue_size : val :=
  rec: "size" "t" =>
    match: "t".{front} with
    | Node <> <> <> <> as "front" =>
        let: "front_r" := "front" in
        let: "proph" := Proph in
        match: "t".{back} with
        | Node <> <> <> <> as "back" =>
            let: "back_r" := "back" in
            match: "back_r".{next} with
            | Node <> <> <> <> as "node" =>
                CAS "t".[back] "back" "node" ;;
                "size" "t"
            | Null =>
                if: Resolve "t".{front} "proph" () != "front" then (
                  "size" "t"
                ) else (
                  "back_r".{index} - "front_r".{index}
                )
            end
        end
    end.

Definition mpmc_bqueue_is_empty : val :=
  fun: "t" =>
    match: "t".{front} with
    | Node <> <> <> <> as "front_r" =>
        "front_r".{next} == §Null
    end.

Definition mpmc_bqueue_fix_back : val :=
  rec: "fix_back" "t" "back" "new_back" =>
    match: "new_back" with
    | Node <> <> <> <> as "new_back_r" =>
        if:
          "new_back_r".{next} == §Null and
          ~ CAS "t".[back] "back" "new_back"
        then (
          domain_yield () ;;
          "fix_back" "t" "t".{back} "new_back"
        )
    end.

Definition mpmc_bqueue_push_0 : val :=
  rec: "push" "t" "back" "new_back" "cap" =>
    match: "back" with
    | Node <> <> <> <> as "back_r" =>
        match: "new_back" with
        | Node <> <> <> <> as "new_back" =>
            let: "new_back_r" := "new_back" in
            if: "cap" = #0 then (
              match: "t".{front} with
              | Node <> <> <> <> as "front_r" =>
                  let: "cap" :=
                    "t".{capacity} - ("back_r".{index} - "front_r".{index})
                  in
                  if: "cap" ≤ #0 then (
                    #false
                  ) else (
                    "back_r" <-{estimated_capacity} "cap" ;;
                    "push" "t" "back" "new_back" "cap"
                  )
              end
            ) else (
              "new_back_r" <-{index} "back_r".{index} + #1 ;;
              "new_back_r" <-{estimated_capacity} "cap" - #1 ;;
              if: CAS "back_r".[next] §Null "new_back" then (
                mpmc_bqueue_fix_back "t" "back" "new_back" ;;
                #true
              ) else (
                match: "back_r".{next} with
                | Null =>
                    Fail
                | Node <> <> <> <> as "back" =>
                    let: "back_r" := "back" in
                    "push"
                      "t"
                      "back"
                      "new_back"
                      "back_r".{estimated_capacity}
                end
              )
            )
        end
    end.

Definition mpmc_bqueue_push : val :=
  fun: "t" "v" =>
    let: "new_back" := ‘Node{ §Null, "v", #0, #0 } in
    match: "t".{back} with
    | Node <> <> <> <> as "back" =>
        let: "back_r" := "back" in
        mpmc_bqueue_push_0
          "t"
          "back"
          "new_back"
          "back_r".{estimated_capacity}
    end.

Definition mpmc_bqueue_pop : val :=
  rec: "pop" "t" =>
    match: "t".{front} with
    | Node <> <> <> <> as "front" =>
        let: "front_r" := "front" in
        match: "front_r".{next} with
        | Null =>
            §None
        | Node <> <> <> <> as "new_front" =>
            let: "new_front_r" := "new_front" in
            if: CAS "t".[front] "front" "new_front" then (
              let: "v" := "new_front_r".{data} in
              "new_front_r" <-{data} () ;;
              ‘Some( "v" )
            ) else (
              domain_yield () ;;
              "pop" "t"
            )
        end
    end.
