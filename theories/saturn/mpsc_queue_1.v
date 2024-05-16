From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  opt
  node2_chain.
From zoo.saturn Require Export
  base.
From zoo Require Import
  options.

Implicit Types v t : val.
Implicit Types vs : list val.

#[local] Notation "'front'" := (
  in_type "t" 0
)(in custom zoo_field
).
#[local] Notation "'back'" := (
  in_type "t" 1
)(in custom zoo_field
).

Definition mpsc_queue_create : val :=
  λ: <>,
    let: "front" := node2_create () () in
    { "front"; "front" }.

Definition mpsc_queue_is_empty : val :=
  λ: "t",
    "t".{front}.{node2_next} = ().

#[local] Definition mpsc_queue_do_push : val :=
  rec: "mpsc_queue_do_push" "node" "new_back" :=
    let: "node'" := "node".{node2_next} in
    if: "node'" = () then (
      ifnot: Cas "node".[node2_next] () "new_back" then (
        Yield ;;
        "mpsc_queue_do_push" "node'" "new_back"
      )
    ) else (
      "mpsc_queue_do_push" "node'" "new_back"
    ).
#[local] Definition mpsc_queue_fix_back : val :=
  rec: "mpsc_queue_fix_back" "t" "new_back" :=
    let: "back" := "t".{back} in
    if: "new_back".{node2_next} = () and ~ Cas "t".[back] "back" "new_back" then (
      Yield ;;
      "mpsc_queue_fix_back" "t" "new_back"
    ).
Definition mpsc_queue_push : val :=
  λ: "t" "v",
    let: "new_back" := node2_create "v" () in
    mpsc_queue_do_push "t".{back} "new_back" ;;
    mpsc_queue_fix_back "t" "new_back".

Definition mpsc_queue_pop : val :=
  λ: "t",
    let: "front" := "t".{front}.{node2_next} in
    if: "front" = () then (
      §None
    ) else (
      "t" <-{front} "front" ;;
      let: "v" := "front".{node2_data} in
      "front" <-{node2_data} () ;;
      ‘Some{ "v" }
    ).

Class MpscQueueG Σ `{zoo_G : !ZooG Σ} := {
}.

Definition mpsc_queue_Σ := #[
].
#[global] Instance subG_mpsc_queue_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpsc_queue_Σ Σ →
  MpscQueueG Σ.
Proof.
Qed.

Section mpsc_queue_G.
  Context `{mpsc_queue_G : MpscQueueG Σ}.

  Definition mpsc_queue_inv t (ι : namespace) : iProp Σ.
  Proof. Admitted.

  Definition mpsc_queue_model t vs : iProp Σ.
  Proof. Admitted.

  Definition mpsc_queue_consumer t : iProp Σ.
  Proof. Admitted.

  #[global] Instance mpsc_queue_model_timeless t vs :
    Timeless (mpsc_queue_model t vs).
  Proof.
  Admitted.
  #[global] Instance mpsc_queue_consumer_timeless t :
    Timeless (mpsc_queue_consumer t ).
  Proof.
  Admitted.
  #[global] Instance mpsc_queue_inv_persistent t ι :
    Persistent (mpsc_queue_inv t ι).
  Proof.
  Admitted.

  Lemma mpsc_queue_consumer_exclusive t :
    mpsc_queue_consumer t -∗
    mpsc_queue_consumer t -∗
    False.
  Proof.
  Admitted.

  Lemma mpsc_queue_create_spec ι :
    {{{ True }}}
      mpsc_queue_create ()
    {{{ t,
      RET t;
      mpsc_queue_inv t ι ∗
      mpsc_queue_model t [] ∗
      mpsc_queue_consumer t
    }}}.
  Proof.
  Admitted.

  Lemma mpsc_queue_push_spec t ι v :
    <<<
      mpsc_queue_inv t ι
    | ∀∀ vs,
      mpsc_queue_model t vs
    >>>
      mpsc_queue_push t v @ ↑ι
    <<<
      mpsc_queue_model t (vs ++ [v])
    | RET (); True
    >>>.
  Proof.
  Admitted.

  Lemma mpsc_queue_pop_spec t ι :
    <<<
      mpsc_queue_inv t ι ∗
      mpsc_queue_consumer t
    | ∀∀ vs,
      mpsc_queue_model t vs
    >>>
      mpsc_queue_pop t @ ↑ι
    <<<
      mpsc_queue_model t (tail vs)
    | RET head vs;
      mpsc_queue_consumer t
    >>>.
  Proof.
  Admitted.
End mpsc_queue_G.

#[global] Opaque mpsc_queue_create.
#[global] Opaque mpsc_queue_is_empty.
#[global] Opaque mpsc_queue_push.
#[global] Opaque mpsc_queue_pop.

#[global] Opaque mpsc_queue_inv.
#[global] Opaque mpsc_queue_model.
#[global] Opaque mpsc_queue_consumer.
