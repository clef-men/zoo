(* Based on:
   https://github.com/ocaml-multicore/saturn/pull/83
*)

From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From saturn Require Export
  base.
From zoo Require Import
  options.

Implicit Types v t : val.
Implicit Types vs : list val.

#[local] Notation "'node_next'" := (
  in_type "node" 0
)(in custom zoo_field
).
#[local] Notation "'node_data'" := (
  in_type "node" 1
)(in custom zoo_field
).
#[local] Notation "'node_capacity'" := (
  in_type "node" 2
)(in custom zoo_field
).
#[local] Notation "'node_count'" := (
  in_type "node" 3
)(in custom zoo_field
).

#[local] Notation "'capacity'" := (
  in_type "t" 0
)(in custom zoo_field
).
#[local] Notation "'front'" := (
  in_type "t" 1
)(in custom zoo_field
).
#[local] Notation "'back'" := (
  in_type "t" 2
)(in custom zoo_field
).

#[local] Definition node_create : val :=
  fun: "v1" "v2" "v3" "v4" =>
    { "v1", "v2", "v3", "v4" }.

Definition mpmc_bqueue_create : val :=
  fun: "cap" =>
    let: "front" := node_create () () "cap" #0 in
    { "cap", "front", "front" }.

Definition mpmc_bqueue_capacity : val :=
  fun: "t" =>
    "t".{capacity}.

Definition mpmc_bqueue_is_empty : val :=
  fun: "t" =>
    "t".{front}.{node_next} == ().

#[local] Definition mpmc_bqueue_fix_back : val :=
  rec: "mpmc_bqueue_fix_back" "t" "back" "new_back" =>
    if: "new_back".{node_next} == () and ~ CAS "t".[back] "back" "new_back" then
      "mpmc_bqueue_fix_back" "t" "t".{back} "new_back".
#[local] Definition mpmc_bqueue_push_aux : val :=
  rec: "mpmc_bqueue_push_aux" "t" "back" "new_back" "cap" =>
    if: "cap" == #0 then (
      let: "cap" := "t".{capacity} - ("back".{node_count} - "t".{front}.{node_count}) in
      if: "cap" ≤ #0 then (
        #false
      ) else (
        "back" <-{node_capacity} "cap" ;;
        "mpmc_bqueue_push_aux" "t" "back" "new_back" "cap"
      )
    ) else (
      "new_back" <-{node_capacity} "cap" - #1 ;;
      "new_back" <-{node_count} "back".{node_count} + #1 ;;
      if: CAS "back".[node_next] () "new_back" then (
        mpmc_bqueue_fix_back "t" "back" "new_back" ;;
        #true
      ) else (
        let: "back" := "back".{node_next} in
        "mpmc_bqueue_push_aux" "t" "back" "new_back" "back".{node_capacity}
      )
    ).
Definition mpmc_bqueue_push : val :=
  fun: "t" "v" =>
    let: "new_back" := node_create () "v" #0 #0 in
    let: "back" := "t".{back} in
    mpmc_bqueue_push_aux "t" "back" "new_back" "back".{node_capacity}.

#[local] Definition mpmc_queue_do_push : val :=
  rec: "mpmc_queue_do_push" "node" "new_back" =>
    let: "node'" := "node".{node_next} in
    if: "node'" != () or ~ CAS "node".[node_next] () "new_back" then
      "mpmc_queue_do_push" "node'" "new_back".

Definition mpmc_bqueue_pop : val :=
  rec: "mpmc_bqueue_pop" "t" =>
    let: "old_front" := "t".{front} in
    let: "front" := "old_front".{node_next} in
    if: "front" == () then (
      §None
    ) else (
      if: CAS "t".[front] "old_front" "front" then (
        let: "v" := "front".{node_data} in
        "front" <-{node_data} () ;;
        ‘Some{ "v" }
      ) else (
        Yield ;;
        "mpmc_bqueue_pop" "t"
      )
    ).

Class MpmcBqueueG Σ `{zoo_G : !ZooG Σ} := {
}.

Definition mpmc_bqueue_Σ := #[
].
#[global] Instance subG_mpmc_bqueue_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_bqueue_Σ Σ →
  MpmcBqueueG Σ.
Proof.
Qed.

Section mpmc_bqueue_G.
  Context `{mpmc_bqueue_G : MpmcBqueueG Σ}.

  Definition mpmc_bqueue_inv t (ι : namespace) (cap : nat) : iProp Σ.
  Proof. Admitted.

  Definition mpmc_bqueue_model t vs : iProp Σ.
  Proof. Admitted.

  #[global] Instance mpmc_bqueue_model_timeless t vs :
    Timeless (mpmc_bqueue_model t vs).
  Proof.
  Admitted.
  #[global] Instance mpmc_bqueue_inv_persistent t ι cap :
    Persistent (mpmc_bqueue_inv t ι cap).
  Proof.
  Admitted.

  Lemma mpmc_bqueue_create_spec ι cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      mpmc_bqueue_create #cap
    {{{ t,
      RET t;
      mpmc_bqueue_inv t ι (Z.to_nat cap) ∗
      mpmc_bqueue_model t []
    }}}.
  Proof.
  Admitted.

  Lemma mpmc_bqueue_is_empty_spec t ι cap :
    <<<
      mpmc_bqueue_inv t ι cap
    | ∀∀ vs,
      mpmc_bqueue_model t vs
    >>>
      mpmc_bqueue_is_empty t
    <<<
      mpmc_bqueue_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_bqueue_push_spec t ι cap v :
    <<<
      mpmc_bqueue_inv t ι cap
    | ∀∀ vs,
      mpmc_bqueue_model t vs
    >>>
      mpmc_bqueue_push t v @ ↑ι
    <<<
      mpmc_bqueue_model t (if decide (length vs = cap) then vs else vs ++ [v])
    | RET #(bool_decide (length vs = cap));
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_bqueue_pop_spec t ι cap :
    <<<
      mpmc_bqueue_inv t ι cap
    | ∀∀ vs,
      mpmc_bqueue_model t vs
    >>>
      mpmc_bqueue_pop t @ ↑ι
    <<<
      mpmc_bqueue_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
  Admitted.
End mpmc_bqueue_G.

#[global] Opaque mpmc_bqueue_create.
#[global] Opaque mpmc_bqueue_capacity.
#[global] Opaque mpmc_bqueue_is_empty.
#[global] Opaque mpmc_bqueue_push.
#[global] Opaque mpmc_bqueue_pop.
