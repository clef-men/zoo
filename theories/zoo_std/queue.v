From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  queue__code.
From zoo_std Require Import
  option
  chain
  queue__types.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types t v front sent : val.
Implicit Types vs : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition queue_model t vs : iProp Σ :=
    ∃ l front sent,
    ⌜t = #l⌝ ∗
    l.[front] ↦ front ∗
    l.[sentinel] ↦ sent ∗
    chain_model front vs sent ∗
    chain_model sent [()%V] ().

  #[global] Instance queue_model_timeless t vs :
    Timeless (queue_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma queue_create_spec :
    {{{
      True
    }}}
      queue_create ()
    {{{ t,
      RET t;
      queue_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply chain_cons_spec as (sent) "Hsent_model".
    { iApply chain_model_nil. iSteps. }
    wp_block l as "(Hfront & Hsent & _)".
    iApply "HΦ". iExists l, sent, sent. iFrame. iSteps.
    iApply chain_model_nil. iSteps.
  Qed.

  Lemma queue_is_empty_spec t vs :
    {{{
      queue_model t vs
    }}}
      queue_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      queue_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%l & %front & %sent & -> & Hfront & Hsent & Hfront_model & Hsent_model) HΦ".
    wp_rec. do 2 wp_load.
    destruct vs as [| v vs].
    - iDestruct (chain_model_nil with "Hfront_model") as %->.
      iDestruct (chain_physical with "Hsent_model") as %Hphysical; first naive_solver.
      wp_equal as ? | _.
      { iDestruct (chain_physically_distinct' with "Hsent_model") as %[]; naive_solver. }
      iSteps.
    - wp_apply (wp_equal_chain with "Hfront_model Hsent_model") as "Hfront_model Hsent_model"; [naive_solver lia.. |].
      iSplit; first iSteps. iIntros "->".
      iDestruct (chain_model_exclusive with "Hsent_model Hfront_model") as %[]; naive_solver lia.
  Qed.

  Lemma queue_push_spec t vs v :
    {{{
      queue_model t vs
    }}}
      queue_push t v
    {{{
      RET ();
      queue_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (%l & %front & %sent & -> & Hfront & Hsent & Hfront_model & Hsent_model) HΦ".
    wp_rec.
    wp_smart_apply chain_cons_spec as (sent') "Hsent'_model".
    { iApply chain_model_nil. iSteps. }
    wp_load.
    wp_apply (chain_set_head_spec with "Hsent_model") as "Hsent_model".
    wp_load.
    wp_apply (chain_set_tail_spec with "Hsent_model") as (?) "(Hsent_model & _)".
    iDestruct (chain_model_app_2 with "Hfront_model Hsent_model") as "Hfront_model".
    iSteps.
  Qed.

  Lemma queue_pop_spec t vs :
    {{{
      queue_model t vs
    }}}
      queue_pop t
    {{{
      RET (head vs : val);
      queue_model t (tail vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply (queue_is_empty_spec with "Hmodel") as "(%l & %front & %sent & -> & Hfront & Hsent & Hfront_model & Hsent_model)".
    destruct vs as [| v vs]; first iSteps.
    wp_load.
    wp_apply (chain_head_spec with "Hfront_model") as "Hfront_model".
    wp_load.
    wp_apply (chain_tail_spec with "Hfront_model") as (front') "(Hfront_model & Hfront'_model)".
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque queue_create.
#[global] Opaque queue_is_empty.
#[global] Opaque queue_push.
#[global] Opaque queue_pop.

#[global] Opaque queue_model.
