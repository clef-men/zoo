From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From saturn Require Export
  base
  mpmc_queue_2__code.
From saturn Require Import
  mpmc_queue_2__types.
From zoo Require Import
  options.

Implicit Types v t : val.
Implicit Types vs : list val.

Class MpmcQueue2G Σ `{zoo_G : !ZooG Σ} := {
}.

Definition mpmc_queue_2_Σ := #[
].
#[global] Instance subG_mpmc_queue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_queue_2_Σ Σ →
  MpmcQueue2G Σ.
Proof.
Qed.

Section mpmc_queue_2_G.
  Context `{mpmc_queue_2_G : MpmcQueue2G Σ}.

  Definition mpmc_queue_2_inv t (ι : namespace) : iProp Σ.
  Proof. Admitted.

  Definition mpmc_queue_2_model t vs : iProp Σ.
  Proof. Admitted.

  #[global] Instance mpmc_queue_2_model_timeless t vs :
    Timeless (mpmc_queue_2_model t vs).
  Proof.
  Admitted.
  #[global] Instance mpmc_queue_2_inv_persistent t ι :
    Persistent (mpmc_queue_2_inv t ι).
  Proof.
  Admitted.

  Lemma mpmc_queue_2_create_spec ι :
    {{{
      True
    }}}
      mpmc_queue_2_create ()
    {{{ t,
      RET t;
      mpmc_queue_2_inv t ι ∗
      mpmc_queue_2_model t []
    }}}.
  Proof.
  Admitted.

  Lemma mpmc_queue_2_size_spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_size t
    <<<
      mpmc_queue_2_model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_queue_2_is_empty_spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_is_empty t
    <<<
      mpmc_queue_2_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_queue_2_push_back_spec t ι v :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_push_back t v @ ↑ι
    <<<
      mpmc_queue_2_model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_queue_2_push_front_spec t ι v :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_push_front t v @ ↑ι
    <<<
      mpmc_queue_2_model t (v :: vs)
    | RET ();
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_queue_2_pop_spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_pop t @ ↑ι
    <<<
      mpmc_queue_2_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
  Admitted.
End mpmc_queue_2_G.

#[global] Opaque mpmc_queue_2_create.
#[global] Opaque mpmc_queue_2_push_back.
#[global] Opaque mpmc_queue_2_pop.

#[global] Opaque mpmc_queue_2_inv.
#[global] Opaque mpmc_queue_2_model.
