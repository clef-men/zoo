From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  array.
From zoo_parabs Require Import
  pool.
From examples Require Export
  pool_quicksort__code.
From zoo Require Import
  options.

Section pool_G.
  Context `{pool_G : PoolG}.

  #[local] Lemma pool_quicksort_partition_spec arr i i_ ns sz :
    (0 ≤ i)%Z →
    i_ = ₊i →
    (1 < sz)%Z →
    length ns = ₊sz →
    {{{
      array_slice arr i_ (DfracOwn 1) (#*@{Z} ns)
    }}}
      pool_quicksort_partition arr #i #sz
    {{{
      ns1 p pivot ns2
    , RET #p;
      ⌜p = (i_ + length ns1)%nat⌝ ∗
      ⌜ns ≡ₚ ns1 ++ pivot :: ns2⌝ ∗
      ⌜Forall ((≥)%Z pivot) ns1⌝ ∗
      ⌜Forall ((≤)%Z pivot) ns2⌝ ∗
      array_slice arr i_ (DfracOwn 1) (#*@{Z} ns1 ++ #@{Z} pivot :: #*@{Z} ns2)
    }}}.
  Proof.
  Admitted.

  #[local] Lemma pool_quicksort_main_0_spec pool ctx scope arr i i_ ns sz :
    (0 ≤ i)%Z →
    i_ = ₊i →
    length ns = ₊sz →
    {{{
      pool_context pool ctx scope ∗
      array_slice arr i_ (DfracOwn 1) (#*@{Z} ns)
    }}}
      pool_quicksort_main_0 ctx arr #i #sz
    {{{
      RET ();
      pool_context pool ctx scope ∗
      pool_consumer pool (
        ∃ ns',
        ⌜ns ≡ₚ ns'⌝ ∗
        ⌜StronglySorted (≤)%Z ns'⌝ ∗
        array_slice arr i_ (DfracOwn 1) (#*@{Z} ns')
      )
    }}}.
  Proof.
    iIntros "%Hi %Hi_ %Hsz %Φ (Hctx & Harr) HΦ".

    iLöb as "HLöb" forall (ctx scope i i_ ns sz Hi Hi_ Hsz Φ).

    wp_rec. wp_pures.
    case_bool_decide; wp_pures.

    - wp_apply (pool_quicksort_partition_spec with "Harr") as (ns1 p pivot ns2) "(%Hp & %Hns & %Hns1 & %Hns2 & Harr)". 1-4: done.
      iDestruct (array_slice_app3 _ [_] with "Harr") as "(Harr_1 & Harr_2 & Harr_3)".

      wp_smart_apply (pool_async_spec
        True
        ( pool_consumer pool (
            ∃ ns1',
            ⌜ns1 ≡ₚ ns1'⌝ ∗
            ⌜StronglySorted (≤)%Z ns1'⌝ ∗
            array_slice arr i_ (DfracOwn 1) (#*@{Z} ns1')
          )
        )
      with "[$Hctx Harr_1]") as "(Hctx & _ & Hpool_consumer_1)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp_smart_apply ("HLöb" with "[//] [//] [%] Hctx Harr_1") as "($ & $) //". 1: lia.
      }
      iDestruct (pool_consumer_join with "Hpool_consumer_1") as "Hpool_consumer_1".

      wp_smart_apply (pool_async_spec
        True
        ( pool_consumer pool (
            ∃ ns2',
            ⌜ns2 ≡ₚ ns2'⌝ ∗
            ⌜StronglySorted (≤)%Z ns2'⌝ ∗
            array_slice arr (S p) (DfracOwn 1) (#*@{Z} ns2')
          )
        )
      with "[$Hctx Harr_3]") as "(Hctx & _ & Hpool_consumer_2)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp_smart_apply ("HLöb" with "[%] [%] [%] Hctx Harr_3") as "($ & Hpool_consumer)".
        { lia. }
        { simpl_length/=. lia. }
        { apply Permutation_length in Hns. simpl_length/= in Hns. lia. }
        iEval (simpl_length/=) in "Hpool_consumer".
        iEval (rewrite -Hp Nat.add_1_r) in "Hpool_consumer".
        iFrameSteps.
      }
      iDestruct (pool_consumer_join with "Hpool_consumer_2") as "Hpool_consumer_2".

      iApply "HΦ".
      iFrame.
      iApply pool_consumer_intro. iIntros "#Hpool_finished".
      iMod (pool_consumer_finished with "Hpool_consumer_1 Hpool_finished") as "(%ns1' & %Hns1'_permutation & %Hns1'_sorted & Harr_1)".
      iMod (pool_consumer_finished with "Hpool_consumer_2 Hpool_finished") as "(%ns2' & %Hns2'_permutation & %Hns2'_sorted & Harr_3)".
      iDestruct (array_slice_app3_1 with "Harr_1 Harr_2 Harr_3") as "Harr".
      { simpl_length. apply Permutation_length in Hns1'_permutation. lia. }
      { simpl_length/=. apply Permutation_length in Hns1'_permutation. lia. }
      iEval (rewrite -(fmap_app _ [_]) -fmap_app) in "Harr".
      iFrame. iPureIntro. split.
      { rewrite -Hns1'_permutation -Hns2'_permutation //. }
      { apply: StronglySorted_app_cons. 1,4: done.
        - rewrite -Hns1'_permutation.
          eapply Forall_impl => //=. lia.
        - rewrite -Hns2'_permutation //.
      }

    - iDestruct (pool_consumer_intro with "[Harr]") as "Hpool_consumer". 2: iSteps.
      iIntros "_ !>".
      iExists ns. iSteps. iPureIntro.
      apply StronglySorted_trivial. lia.
  Qed.
  #[local] Lemma pool_quicksort_main_1_spec pool ctx scope arr ns :
    {{{
      pool_context pool ctx scope ∗
      array_model arr (DfracOwn 1) (#*@{Z} ns)
    }}}
      pool_quicksort_main_1 ctx arr
    {{{
      RET ();
      pool_context pool ctx scope ∗
      pool_consumer pool (
        ∃ ns',
        ⌜ns ≡ₚ ns'⌝ ∗
        ⌜StronglySorted (≤)%Z ns'⌝ ∗
        array_model arr (DfracOwn 1) (#*@{Z} ns')
      )
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Harr_model) HΦ".

    wp_rec.

    wp_smart_apply (array_size_spec with "Harr_model") as "Harr_model".
    iEval (simpl_length).

    iDestruct (array_model_to_slice' with "Harr_model") as "(Harr_slice & #Harr_model)".
    wp_smart_apply (pool_quicksort_main_0_spec with "[$]") as "(Hctx & Hpool_consumer)". 1-3: lia.

    iSteps.
    iApply (pool_consumer_wand with "Hpool_consumer").
    iSteps. iPureIntro.
    simpl_length. apply Permutation_length. done.
  Qed.

  Lemma pool_quicksort_main_spec (num_dom : nat) arr ns :
    {{{
      array_model arr (DfracOwn 1) (#*@{Z} ns)
    }}}
      pool_quicksort_main #num_dom arr
    {{{
      ns'
    , RET ();
      ⌜ns ≡ₚ ns'⌝ ∗
      ⌜StronglySorted (≤)%Z ns'⌝ ∗
      array_model arr (DfracOwn 1) (#*@{Z} ns')
    }}}.
  Proof.
    iIntros "%Φ Harr HΦ".

    wp_rec.
    wp_smart_apply (pool_create_spec with "[//]") as (pool) "(_ & Hpool_model)". 1: lia.

    wp_smart_apply (pool_run_spec (λ _,
      pool_consumer pool (
        ∃ ns',
        ⌜ns ≡ₚ ns'⌝ ∗
        ⌜StronglySorted (≤)%Z ns'⌝ ∗
        array_model arr (DfracOwn 1) (#*@{Z} ns')
      )
    )%I with "[$Hpool_model Harr]") as (?) "(Hpool_model & Hpool_consumer)".
    { iIntros "%ctx %scope Hctx".
      wp_smart_apply (pool_quicksort_main_1_spec with "[$]") as "$".
    }

    iApply wp_fupd.
    wp_smart_apply (pool_kill_spec with "[$Hpool_model]") as "#Hpool_finished".
    iMod (pool_consumer_finished with "Hpool_consumer Hpool_finished") as "(%ns' & % & % & Harr)".
    iSteps.
  Qed.
End pool_G.

From examples Require
  pool_quicksort__opaque.
