From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  opt.
From zebre.std Require Import
  chain.
From zebre Require Import
  options.

Implicit Types l : location.
Implicit Types t v front sent : val.
Implicit Types vs : list val.

#[local] Notation "'front'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'sentinel'" := (
  in_type "t" 1
)(in custom zebre_field
).

Definition queue_create : val :=
  λ: <>,
    let: "sent" := chain_cons () () in
    { "sent"; "sent" }.

Definition queue_is_empty : val :=
  λ: "t",
    "t".{front} = "t".{sentinel}.

Definition queue_push : val :=
  λ: "t" "v",
    let: "sent" := chain_cons () () in
    chain_set_head "t".{sentinel} "v" ;;
    chain_set_tail "t".{sentinel} "sent" ;;
    "t" <-{sentinel} "sent".

Definition queue_pop : val :=
  λ: "t",
    if: queue_is_empty "t" then (
      §None
    ) else (
      let: "v" := chain_head "t".{front} in
      "t" <-{front} chain_tail "t".{front} ;;
      ‘Some{ "v" }
    ).

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

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
    {{{ True }}}
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
    wp_record l as "(Hfront & Hsent & _)".
    iApply "HΦ". iExists l, sent, sent. iFrame. iSteps.
    iApply chain_model_nil. iSteps.
  Qed.

  Lemma queue_is_empty_spec t vs :
    {{{
      queue_model t vs
    }}}
      queue_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      queue_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%l & %front & %sent & -> & Hfront & Hsent & Hfront_model & Hsent_model) HΦ".
    wp_rec. do 2 wp_load.
    destruct vs as [| v vs].
    - iDestruct (chain_model_nil with "Hfront_model") as %->.
      iDestruct (chain_physical with "Hsent_model") as %Hphysical; first naive_solver.
      wp_equal as ? | _ _.
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
End zebre_G.

#[global] Opaque queue_create.
#[global] Opaque queue_is_empty.
#[global] Opaque queue_push.
#[global] Opaque queue_pop.

#[global] Opaque queue_model.
