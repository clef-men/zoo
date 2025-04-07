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
  spmc_queue__code.
From zoo_saturn Require Import
  spmc_queue__types.
From zoo Require Import
  options.

Implicit Types v t : val.

Class SpmcQueueG Σ `{zoo_G : !ZooG Σ} := {
}.

Definition spmc_queue_Σ := #[
].
#[global] Instance subG_spmc_queue_Σ Σ `{zoo_G : !ZooG Σ} :
  subG spmc_queue_Σ Σ →
  SpmcQueueG Σ.
Proof.
  (* solve_inG. *)
Qed.

Section spmc_queue_G.
  Context `{spmc_queue_G : SpmcQueueG Σ}.

  Parameter spmc_queue_inv : val → namespace → iProp Σ.

  Parameter spmc_queue_model : val → list val → iProp Σ.

  Parameter spmc_queue_producer : val → list val → iProp Σ.

  #[global] Instance spmc_queue_model_timeless t vs :
    Timeless (spmc_queue_model t vs).
  Proof.
  Admitted.
  #[global] Instance spmc_queue_producer_timeless t ws :
    Timeless (spmc_queue_producer t ws).
  Proof.
  Admitted.
  #[global] Instance spmc_queue_inv_persistent t ι :
    Persistent (spmc_queue_inv t ι).
  Proof.
  Admitted.

  Lemma spmc_queue_producer_valid t vs ws :
    spmc_queue_model t vs -∗
    spmc_queue_producer t ws -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
  Admitted.

  Lemma spmc_queue_create_spec ι :
    {{{
      True
    }}}
      spmc_queue_create ()
    {{{ t,
      RET t;
      spmc_queue_inv t ι ∗
      spmc_queue_model t [] ∗
      spmc_queue_producer t []
    }}}.
  Proof.
  Admitted.

  Lemma spmc_queue_is_empty_spec t ι :
    <<<
      spmc_queue_inv t ι
    | ∀∀ vs,
      spmc_queue_model t vs
    >>>
      spmc_queue_is_empty t @ ↑ι
    <<<
      spmc_queue_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
  Admitted.

  Lemma spmc_queue_push_spec t ι ws v :
    <<<
      spmc_queue_inv t ι ∗
      spmc_queue_producer t ws
    | ∀∀ vs,
      spmc_queue_model t vs
    >>>
      spmc_queue_push t v @ ↑ι
    <<<
      spmc_queue_model t (vs ++ [v])
    | RET ();
      spmc_queue_producer t (vs ++ [v])
    >>>.
  Proof.
  Admitted.

  Lemma spmc_queue_pop_spec t ι :
    <<<
      spmc_queue_inv t ι
    | ∀∀ vs,
      spmc_queue_model t vs
    >>>
      spmc_queue_pop t @ ↑ι
    <<<
      spmc_queue_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
  Admitted.
End spmc_queue_G.

#[global] Opaque spmc_queue_inv.
#[global] Opaque spmc_queue_model.
#[global] Opaque spmc_queue_producer.

#[global] Opaque spmc_queue_create.
#[global] Opaque spmc_queue_is_empty.
#[global] Opaque spmc_queue_push.
#[global] Opaque spmc_queue_pop.
