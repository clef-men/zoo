From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From zoo_saturn Require Export
  base
  bag_2__code.
From zoo_saturn Require Import
  bag_2__types.
From zoo Require Import
  options.

Implicit Types v t producer consumer : val.

Class Bag2G Σ `{zoo_G : !ZooG Σ} := {
}.

Definition bag_2_Σ := #[
].
#[global] Instance subG_bag_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG bag_2_Σ Σ →
  Bag2G Σ.
Proof.
  (* solve_inG. *)
Qed.

Section bag_2_G.
  Context `{bag_2_G : Bag2G Σ}.

  Parameter bag_2_inv : val → namespace → iProp Σ.

  Parameter bag_2_model : val → list (list val) → iProp Σ.

  Parameter bag_2_producer : val → val → nat → list val → iProp Σ.

  Parameter bag_2_consumer : val → val → iProp Σ.

  #[global] Instance bag_2_model_timeless t vs :
    Timeless (bag_2_model t vs).
  Proof.
  Admitted.
  #[global] Instance bag_2_producer_timeless t producer i ws :
    Timeless (bag_2_producer t producer i ws).
  Proof.
  Admitted.
  #[global] Instance bag_2_consumer_timeless t consumer :
    Timeless (bag_2_consumer t consumer).
  Proof.
  Admitted.
  #[global] Instance bag_2_inv_persistent t ι :
    Persistent (bag_2_inv t ι).
  Proof.
  Admitted.

  Lemma bag_2_producer_valid t vss producer i ws :
    bag_2_model t vss -∗
    bag_2_producer t producer i ws -∗
      ∃ vs,
      ⌜vss !! i = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝.
  Proof.
  Admitted.

  Lemma bag_2_create_spec ι :
    {{{
      True
    }}}
      bag_2_create  ()
    {{{ t,
      RET t;
      bag_2_inv t ι ∗
      bag_2_model t []
    }}}.
  Proof.
  Admitted.

  Lemma bag_2_create_producer_spec t ι :
    <<<
      bag_2_inv t ι
    | ∀∀ vss,
      bag_2_model t vss
    >>>
      bag_2_create_producer t
    <<<
      bag_2_model t (vss ++ [[]])
    | prod,
      RET prod;
      bag_2_producer t prod (length vss) []
    >>>.
  Proof.
  Admitted.

  Lemma bag_2_close_producer_spec t ι producer i ws :
    {{{
      bag_2_inv t ι ∗
      bag_2_producer t producer i ws
    }}}
      bag_2_close_producer producer
    {{{
      RET ();
      bag_2_producer t producer i ws
    }}}.
  Proof.
  Admitted.

  Lemma bag_2_create_consumer_spec t ι :
    {{{
      bag_2_inv t ι
    }}}
      bag_2_create_consumer t
    {{{ consumer,
      RET consumer;
      bag_2_consumer t consumer
    }}}.
  Proof.
  Admitted.

  Lemma bag_2_push_spec t ι producer i ws v :
    <<<
      bag_2_inv t ι ∗
      bag_2_producer t producer i ws
    | ∀∀ vss,
      bag_2_model t vss
    >>>
      bag_2_push producer v
    <<<
      ∃∃ vs,
      ⌜vss !! i = Some vs⌝ ∗
      bag_2_model t (<[i := vs ++ [v]]> vss)
    | RET ();
      bag_2_producer t producer i (ws ++ [v])
    >>>.
  Proof.
  Admitted.

  Lemma bag_2_pop_spec t ι consumer :
    <<<
      bag_2_inv t ι ∗
      bag_2_consumer t consumer
    | ∀∀ vss,
      bag_2_model t vss
    >>>
      bag_2_pop consumer
    <<<
      ∃∃ o,
      match o with
      | None =>
          bag_2_model t vss
      | Some v =>
          ∃ i v vs,
          ⌜vss !! i = Some (v :: vs)⌝ ∗
          bag_2_model t (<[i := vs]> vss)
      end
    | RET o;
      bag_2_consumer t consumer
    >>>.
  Proof.
  Admitted.
End bag_2_G.

#[global] Opaque bag_2_inv.
#[global] Opaque bag_2_model.
#[global] Opaque bag_2_producer.
#[global] Opaque bag_2_consumer.

#[global] Opaque bag_2_create.
#[global] Opaque bag_2_create_producer.
#[global] Opaque bag_2_close_producer.
#[global] Opaque bag_2_create_consumer.
#[global] Opaque bag_2_push.
#[global] Opaque bag_2_pop.
