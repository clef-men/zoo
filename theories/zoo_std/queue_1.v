From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  queue_1__code.
From zoo_std Require Import
  option
  chain
  queue_1__types.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types t v front back : val.
Implicit Types vs : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition queue_1_model t vs : iProp Σ :=
    ∃ l front back,
    ⌜t = #l⌝ ∗
    l.[front] ↦ front ∗
    l.[back] ↦ back ∗
    chain_model None front vs back ∗
    chain_model None back [()%V] ().
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l &
      %front &
      %back &
      -> &
      Hl_front &
      Hl_back &
      Hfront &
      Hback
    )".

  #[global] Instance queue_1_model_timeless t vs :
    Timeless (queue_1_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma queue_1_create_spec :
    {{{
      True
    }}}
      queue_1_create ()
    {{{ t,
      RET t;
      queue_1_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (chain_block_spec None) as (back) "Hback_model".
    { iApply chain_model_nil. iSteps. }
    wp_block l as "(Hfront & Hback & _)".
    iApply "HΦ". iExists l, back, back. iFrameSteps.
    iApply chain_model_nil. iSteps.
  Qed.

  Lemma queue_1_is_empty_spec t vs :
    {{{
      queue_1_model t vs
    }}}
      queue_1_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      queue_1_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. do 2 wp_load.
    destruct vs as [| v vs].
    - iDestruct (chain_model_nil with "Hfront") as %->.
      iDestruct (chain_physical with "Hback") as %Hphysical; first naive_solver.
      wp_equal as ? | _.
      { iDestruct (chain_physically_distinct' with "Hback") as %[]; naive_solver. }
      iSteps.
    - wp_apply (wp_equal_chain with "Hfront Hback") as "Hfront Hback"; [naive_solver lia.. |].
      iSplit; first iSteps. iIntros "->".
      iDestruct (chain_model_exclusive with "Hback Hfront") as %[]; naive_solver lia.
  Qed.

  Lemma queue_1_push_spec t vs v :
    {{{
      queue_1_model t vs
    }}}
      queue_1_push t v
    {{{
      RET ();
      queue_1_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec.
    wp_load.
    wp_smart_apply (chain_block_spec None) as (back') "Hback'".
    { iApply chain_model_nil. iSteps. }
    wp_smart_apply (chain_set_next_spec with "Hback") as (?) "(Hback & _)".
    wp_smart_apply (chain_set_data_spec with "Hback") as "Hback".
    iDestruct (chain_model_app_2 with "Hfront Hback") as "Hfront".
    iSteps.
  Qed.

  Lemma queue_1_pop_spec t vs :
    {{{
      queue_1_model t vs
    }}}
      queue_1_pop t
    {{{
      RET (head vs : val);
      queue_1_model t (tail vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply (queue_1_is_empty_spec with "Hmodel") as "(:model)".
    destruct vs as [| v vs]; first iSteps.
    wp_load.
    wp_smart_apply (chain_next_spec with "Hfront") as (front') "(Hfront & Hfront')".
    wp_store.
    wp_smart_apply (chain_data_spec with "Hfront") as "Hfront".
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque queue_1_create.
#[global] Opaque queue_1_is_empty.
#[global] Opaque queue_1_push.
#[global] Opaque queue_1_pop.

#[global] Opaque queue_1_model.
