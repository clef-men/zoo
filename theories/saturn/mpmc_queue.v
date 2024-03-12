(* Based on:
   https://github.com/ocaml-multicore/saturn/pull/112
*)

From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt.
From zebre.saturn Require Export
  base.
From zebre Require Import
  options.

Implicit Types v t : val.
Implicit Types vs : list val.

#[local] Notation "'Front'" := (
  in_type "truc" 0
)(in custom zebre_tag
).
#[local] Notation "'Cons'" := (
  in_type "truc" 1
)(in custom zebre_tag
).
#[local] Notation "'Back'" := (
  in_type "truc" 2
)(in custom zebre_tag
).
#[local] Notation "'Snoc'" := (
  in_type "truc" 3
)(in custom zebre_tag
).

#[local] Notation "'front'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'back'" := (
  in_type "t" 1
)(in custom zebre_field
).

#[local] Definition truc_rev_aux : val :=
  rec: "truc_rev_aux" "suffix" "truc" :=
    match: "truc" with
    | Snoc "cnt" "prefix" "v" =>
        "truc_rev_aux" ‘Cons{ "cnt", "v", "suffix" } "prefix"
    | Back <> =>
        "suffix"
    end.
#[local] Definition truc_rev : val :=
  λ: "truc",
    let: ‘Snoc "cnt" "prefix" "v" := "truc" in
    truc_rev_aux ‘Cons{ "cnt", "v", #1 + ‘Front{ "cnt" } } "prefix".

Definition mpmc_queue_create : val :=
  λ: <>,
    { ‘Front{ #1 }; ‘Back{ #0, ref () } }.

#[local] Definition mpmc_queue_push_aux : val :=
  λ: "mpmc_queue_push" "t" "v" "cnt" "back",
    ifnot: Cas "t".[back] "back" ‘Snoc{ #1 + "cnt", "back", "v" } then (
      "mpmc_queue_push" "t" "v"
    ).
Definition mpmc_queue_push : val :=
  rec: "mpmc_queue_push" "t" "v" :=
    let: "back" := "t".{back} in
    match: "back" with
    | Snoc "cnt" <> <> =>
        mpmc_queue_push_aux "mpmc_queue_push" "t" "v" "cnt" "back"
    | Back "back_cnt" "↦move" =>
        let: "move" := !"↦move" in
        if: "move" = () then (
          mpmc_queue_push_aux "mpmc_queue_push" "t" "v" "back_cnt" "back"
        ) else (
          let: ‘Snoc "move_cnt" <> <> := "move" in
          match: "t".{front} with
          | Front "front_cnt" as "front" =>
              if: "front_cnt" < "move_cnt" && Cas "t".[front] "front" (truc_rev "move") then (
                "↦move" <- ()
              )
          | _ =>
              ()
          end ;;
          mpmc_queue_push_aux "mpmc_queue_push" "t" "v" "back_cnt" "back"
        )
    end.

#[local] Definition mpmc_queue_pop_aux1 : val :=
  rec: "aux1" "aux2" "aux3" "t" "front" :=
    match: "front" with
    | Cons <> "v" "suffix" =>
        if: Cas "t".[front] "front" "suffix" then (
          ‘Some{ "v" }
        ) else (
          "aux1" "aux2" "aux3" "t" "t".{front}
        )
    | Front "front_cnt" =>
        match: "t".{back} with
        | Snoc "move_cnt" "v" "move_prefix" as "move" =>
            if: "front_cnt" = "move_cnt" then (
              if: Cas "t".[back] "move" "move_prefix" then (
                ‘Some{ "v" }
              ) else (
                "aux1" "aux2" "aux3" "t" "t".{front}
              )
            ) else (
              let: "back" := ‘Back{ "move_cnt", "move" } in
              if: Cas "t".[back] "move" "back" then (
                "aux2" "aux1" "aux3" "t" "front" "move" "back"
              ) else (
                "aux1" "aux2" "aux3" "t" "t".{front}
              )
            )
        | Back <> "↦move" as "back" =>
            let: "move" := !"↦move" in
            if: "move" = () then (
              "aux3" "aux1" "aux2" "t" "front"
            ) else (
              "aux2" "aux1" "aux3" "t" "front" "move" "back"
            )
        end
    end.
#[local] Definition mpmc_queue_pop_aux2 : val :=
  rec: "aux2" "aux1" "aux3" "t" "front" "move" "back" :=
    let: ‘Front "front_cnt" := "front" in
    let: ‘Snoc "move_cnt" <> <> := "move" in
    let: ‘Back <> "↦move" := "back" in
    if: "front_cnt" < "move_cnt" then (
      let: ‘Cons <> "v" "suffix" := truc_rev "move" in
      if: Cas "t".[front] "front" "suffix" then (
        "↦move" <- () ;;
        ‘Some{ "v" }
      ) else (
        "aux1" "aux2" "aux3" "t" "t".{front}
      )
    ) else (
      "aux3" "aux1" "aux2" "t" "front"
    ).
#[local] Definition mpmc_queue_pop_aux3 : val :=
  rec: "aux3" "aux1" "aux2" "t" "front" :=
    let: "front'" := "t".{front} in
    if: "front'" = "front" then (
      §None
    ) else (
      "aux1" "aux2" "aux3" "t" "front'"
    ).
Definition mpmc_queue_pop : val :=
  λ: "t",
    mpmc_queue_pop_aux1 mpmc_queue_pop_aux2 mpmc_queue_pop_aux3 "t" "t".{front}.

Class MpmcQueueG Σ `{zebre_G : !ZebreG Σ} := {
}.

Definition mpmc_queue_Σ := #[
].
#[global] Instance subG_mpmc_queue_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG mpmc_queue_Σ Σ →
  MpmcQueueG Σ.
Proof.
Qed.

Section mpmc_queue_G.
  Context `{mpmc_queue_G : MpmcQueueG Σ}.

  Definition mpmc_queue_inv t (ι : namespace) : iProp Σ.
  Proof. Admitted.

  Definition mpmc_queue_model t vs : iProp Σ.
  Proof. Admitted.

  #[global] Instance mpmc_queue_model_timeless t vs :
    Timeless (mpmc_queue_model t vs).
  Proof.
  Admitted.
  #[global] Instance mpmc_queue_inv_persistent t ι :
    Persistent (mpmc_queue_inv t ι).
  Proof.
  Admitted.

  Lemma mpmc_queue_create_spec ι :
    {{{ True }}}
      mpmc_queue_create ()
    {{{ t,
      RET t;
      mpmc_queue_inv t ι ∗
      mpmc_queue_model t []
    }}}.
  Proof.
  Admitted.

  Lemma mpmc_queue_push_spec t ι v :
    <<<
      mpmc_queue_inv t ι
    | ∀∀ vs,
      mpmc_queue_model t vs
    >>>
      mpmc_queue_push t v @ ↑ι
    <<<
      mpmc_queue_model t (vs ++ [v])
    | RET (); True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_queue_pop_spec t ι :
    <<<
      mpmc_queue_inv t ι
    | ∀∀ vs,
      mpmc_queue_model t vs
    >>>
      mpmc_queue_pop t @ ↑ι
    <<<
      mpmc_queue_model t (tail vs)
    | RET head vs; True
    >>>.
  Proof.
  Admitted.
End mpmc_queue_G.

#[global] Opaque mpmc_queue_create.
#[global] Opaque mpmc_queue_push.
#[global] Opaque mpmc_queue_pop.

#[global] Opaque mpmc_queue_inv.
#[global] Opaque mpmc_queue_model.
