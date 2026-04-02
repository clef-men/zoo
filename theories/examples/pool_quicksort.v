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
From zoo_std Require Import
  for_.
From zoo_parabs Require Import
  pool.
From examples Require Export
  pool_quicksort__code.
From zoo Require Import
  options.

Section pool_G.
  Context `{pool_G : PoolG}.

  #[local] Lemma pool_quicksort_partition_spec arr i i_ xs sz :
    (0 ≤ i)%Z →
    i_ = ₊i →
    (1 < sz)%Z →
    length xs = ₊sz →
    {{{
      array_slice arr i_ (DfracOwn 1) (#*@{Z} xs)
    }}}
      pool_quicksort_partition arr #i #sz
    {{{
      xs1 p pivot xs2
    , RET #p;
      ⌜p = (i_ + length xs1)%nat⌝ ∗
      ⌜xs ≡ₚ xs1 ++ pivot :: xs2⌝ ∗
      ⌜Forall ((≥)%Z pivot) xs1⌝ ∗
      ⌜Forall ((≤)%Z pivot) xs2⌝ ∗
      array_slice arr i_ (DfracOwn 1) (#*@{Z} xs1 ++ #@{Z} pivot :: #*@{Z} xs2)
    }}}.
  Proof.
    iIntros (Hi -> Hsz Hxs) "%Φ Harr HΦ".

    destruct xs as [| pivot xs]; simpl in Hxs. 1: lia.
    iEval (rewrite fmap_cons) in "Harr".
    iDestruct (array_slice_cons_1 with "Harr") as "(Harr_1 & Harr_2)".

    wp_rec.
    wp_apply+ (array_unsafe_get_spec_cell with "Harr_1") as "Harr_1". 1: lia.
    wp_ref r as "Hr".

    wp_apply+ (for_spec_strong (λ j _,
      ∃ xs' (i1 : Z),
      array_slice arr (S ₊i) (DfracOwn 1) (#*@{Z} xs') ∗
      r ↦ᵣ #i1 ∗
      ⌜xs ≡ₚ xs'⌝ ∗
      ⌜i < i1 ≤ j⌝%Z ∗
      ⌜ ∀ (k : nat) x,
        xs' !! k = Some x →
        (k < i1 - i - 1)%Z →
        (x ≤ pivot)%Z
      ⌝ ∗
      ⌜ ∀ (k : nat) x,
        xs' !! k = Some x →
        (i1 - i - 1 ≤ k < j - i - 1)%Z →
        (pivot ≤ x)%Z
      ⌝
    )%I with "[Harr_2 Hr]") as "(%xs' & %i1 & Harr_2 & Hr & %Hxs' & %Hi1 & %H1 & %H2)".
    { iSplitL.
      { iFrame. iPureIntro. auto with lia. }

      iIntros "!> %i2 %𝑖2 % % (%xs' & %i1 & Harr & Hr & %Hxs' & %Hi1 & %H1 & %H2)".
      destruct (lookup_lt_is_Some_2 xs' ₊(i1 - i - 1)) as (x1 & Hlookup_1).
      { rewrite -Hxs'. lia. }
      destruct (lookup_lt_is_Some_2 xs' 𝑖2) as (x2 & Hlookup_2).
      { rewrite -Hxs'. lia. }

      wp_apply+ (array_unsafe_get_spec_slice with "Harr") as "Harr".
      { lia. }
      { apply list_lookup_fmap_Some_2 => //. }
      { lia. }

      wp_pures.
      case_bool_decide as Hx2; wp_pures.

      - wp_load.

        wp_apply (array_unsafe_swap_spec_slice ₊(i1 - i - 1) with "Harr") as "Harr".
        1,2,4: lia.
        1,2: apply list_lookup_fmap_Some_2 => //.
        1: lia.
        iEval (rewrite -!list_fmap_insert) in "Harr".

        iStep 15. iPureIntro. split_and!.
        { rewrite Permutation_swap' //. }
        { lia. }
        { lia. }
        all:
          intros k x
            [ (<- & <- & _)
            | ( ?
              & [ (<- & <- & _)
                | (? & Hlookup_k)
                ]%list_lookup_insert_Some
              )
            ]%list_lookup_insert_Some Hk.
        { destruct_decide (𝑖2 = ₊(i1 - i - 1)) as -> | ?.
          - congruence.
          - lia.
        }
        all: naive_solver lia.

      - iStep 6. iPureIntro.
        intros k x Hlookup_k Hk.
        destruct_decide (k = 𝑖2) as -> | Hcase.
        all: naive_solver lia.
    }

    rewrite Z.max_r in Hi1 H2. 1: lia.
    apply Permutation_length in Hxs' as ?.

    iDestruct (array_slice_cons_2 with "Harr_1 Harr_2") as "Harr".

    wp_load. wp_pures.

    destruct_decide (i1 = i + 1)%Z as -> | Hcase.

    - wp_apply+ (array_unsafe_swap_spec_slice_id with "Harr") as "Harr". 1,2: simpl; lia.
      iSteps as "_".

      iEval (replace _ with ⁺₊i by lia).
      iApply ("HΦ" $! [] ₊i pivot xs').
      iSteps; iPureIntro.
      { rewrite Hxs' //. }
      { apply Forall_lookup. intros k x Hlookup.
        apply lookup_lt_Some in Hlookup as ?.
        eapply H2; [done | lia].
      }

    - assert (
        ∃ xs1 xs2,
        xs' = xs1 ++ xs2 ∧
        length xs1 = ₊(i1 - i - 1) ∧
        Forall ((≥)%Z pivot) xs1 ∧
        length xs2 = ₊(i + length xs + 1 - i1) ∧
        Forall ((≤)%Z pivot) xs2
      ) as (xs1 & xs2 & -> & Hxs1_length & Hxs1 & Hxs2_length & Hxs2).
      { exists (take ₊(i1 - i - 1) xs'), (drop ₊(i1 - i - 1) xs'). split_and!.
        - rewrite take_drop //.
        - simpl_length. lia.
        - apply Forall_lookup. intros k x (Hlookup & Hk)%lookup_take_Some.
          eapply Z.le_ge, H1; [done | lia].
        - simpl_length. lia.
        - apply Forall_lookup. intros k x Hlookup.
          rewrite lookup_drop in Hlookup.
          apply lookup_lt_Some in Hlookup as ?.
          eapply H2; [done | lia].
      }
      iEval (rewrite fmap_app) in "Harr".

      destruct xs1 as [| x xs1 _] using rev_ind. 1: naive_solver lia.
      simpl_length/= in Hxs1_length.
      iEval (rewrite fmap_app /=) in "Harr".

      iDestruct (array_slice_app_2 (_ :: _) with "Harr") as "(Harr_1 & Harr_2)". 1: done.
      wp_apply+ (array_unsafe_swap_spec_slice 0 ₊(i1 - i - 1) with "Harr_1") as "Harr_1". 1-4,6: auto with lia.
      { apply lookup_cons_r_Some. 1: lia.
        apply lookup_app_r_Some; simpl_length. 1: lia.
        replace _ with 0 by lia. done.
      }
      iEval (rewrite /= insert_cons_r; first lia) in "Harr_1".
      iEval (rewrite insert_app_r_alt; first (simpl_length; lia)) in "Harr_1".
      iEval (simpl_length) in "Harr_1".
      iEval (rewrite insert_cons_l; first lia) in "Harr_1".
      iDestruct (array_slice_app_1' with "Harr_1 Harr_2") as "Harr". 1: simpl_length/=.
      iEval (rewrite -(assoc _ (_ :: _))) in "Harr".

      wp_load. wp_pures.

      iEval (rewrite -(Z2Nat.id (i1 - 1)); first lia).
      iApply ("HΦ" $! (x :: xs1) _ pivot xs2).
      iFrameSteps; iPureIntro.
      { rewrite Hxs'. solve_Permutation. }
      { rewrite Permutation_cons_append //. }
  Qed.

  #[local] Lemma pool_quicksort_main_0_spec pool ctx scope arr i i_ xs sz :
    (0 ≤ i)%Z →
    i_ = ₊i →
    length xs = ₊sz →
    {{{
      pool_context pool ctx scope ∗
      array_slice arr i_ (DfracOwn 1) (#*@{Z} xs)
    }}}
      pool_quicksort_main_0 ctx arr #i #sz
    {{{
      RET ();
      pool_context pool ctx scope ∗
      pool_consumer pool (
        ∃ xs',
        ⌜xs ≡ₚ xs'⌝ ∗
        ⌜StronglySorted (≤)%Z xs'⌝ ∗
        array_slice arr i_ (DfracOwn 1) (#*@{Z} xs')
      )
    }}}.
  Proof.
    iIntros "%Hi %Hi_ %Hsz %Φ (Hctx & Harr) HΦ".

    iLöb as "HLöb" forall (ctx scope i i_ xs sz Hi Hi_ Hsz Φ).

    wp_rec. wp_pures.
    case_bool_decide; wp_pures.

    - wp_apply (pool_quicksort_partition_spec with "Harr") as (xs1 p pivot xs2) "(%Hp & %Hxs & %Hxs1 & %Hxs2 & Harr)". 1-4: done.
      iDestruct (array_slice_app3 _ [_] with "Harr") as "(Harr_1 & Harr_2 & Harr_3)".

      wp_apply+ (pool_async_spec
        ( pool_consumer pool (
            ∃ xs1',
            ⌜xs1 ≡ₚ xs1'⌝ ∗
            ⌜StronglySorted (≤)%Z xs1'⌝ ∗
            array_slice arr i_ (DfracOwn 1) (#*@{Z} xs1')
          )
        )
        True
      with "[$Hctx Harr_1]") as "(Hctx & Hpool_consumer_1 & _)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp_apply+ ("HLöb" with "[//] [//] [%] Hctx Harr_1") as "($ & $) //". 1: lia.
      }

      wp_apply+ (pool_async_spec
        ( pool_consumer pool (
            ∃ xs2',
            ⌜xs2 ≡ₚ xs2'⌝ ∗
            ⌜StronglySorted (≤)%Z xs2'⌝ ∗
            array_slice arr (S p) (DfracOwn 1) (#*@{Z} xs2')
          )
        )
        True
      with "[$Hctx Harr_3]") as "(Hctx & Hpool_consumer_2 & _)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp_apply+ ("HLöb" with "[%] [%] [%] Hctx Harr_3") as "($ & Hpool_consumer)".
        { lia. }
        { simpl_length/=. lia. }
        { apply Permutation_length in Hxs. simpl_length/= in Hxs. lia. }
        iEval (simpl_length/=) in "Hpool_consumer".
        iEval (rewrite -Hp Nat.add_1_r) in "Hpool_consumer".
        iFrameSteps.
      }

      iApply "HΦ".
      iFrame.
      iMod "Hpool_consumer_1" as ">(%xs1' & %Hxs1'_permutation & %Hxs1'_sorted & Harr_1)".
      iMod "Hpool_consumer_2" as ">(%xs2' & %Hxs2'_permutation & %Hxs2'_sorted & Harr_3)".
      iModIntro.
      iDestruct (array_slice_app3_1 with "Harr_1 Harr_2 Harr_3") as "Harr".
      { simpl_length. apply Permutation_length in Hxs1'_permutation. lia. }
      { simpl_length/=. apply Permutation_length in Hxs1'_permutation. lia. }
      iEval (rewrite -(fmap_app _ [_]) -fmap_app) in "Harr".
      iFrame. iPureIntro. split.
      { rewrite -Hxs1'_permutation -Hxs2'_permutation //. }
      { apply: StronglySorted_app_cons. 1,4: done.
        - rewrite -Hxs1'_permutation.
          eapply Forall_impl => //=. lia.
        - rewrite -Hxs2'_permutation //.
      }

    - iSteps. do 2 iModIntro.
      iExists xs. iSteps. iPureIntro.
      apply StronglySorted_trivial. lia.
  Qed.
  #[local] Lemma pool_quicksort_main_1_spec pool ctx scope arr xs :
    {{{
      pool_context pool ctx scope ∗
      array_model arr (DfracOwn 1) (#*@{Z} xs)
    }}}
      pool_quicksort_main_1 ctx arr
    {{{
      RET ();
      pool_context pool ctx scope ∗
      pool_consumer pool (
        ∃ xs',
        ⌜xs ≡ₚ xs'⌝ ∗
        ⌜StronglySorted (≤)%Z xs'⌝ ∗
        array_model arr (DfracOwn 1) (#*@{Z} xs')
      )
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Harr_model) HΦ".

    wp_rec.

    wp_apply+ (array_size_spec with "Harr_model") as "Harr_model".
    iEval (simpl_length).

    iDestruct (array_model_to_slice' with "Harr_model") as "(Harr_slice & #Harr_model)".
    wp_apply+ (pool_quicksort_main_0_spec with "[$]") as "(Hctx & Hpool_consumer)". 1-3: lia.

    iSteps.
    iMod "Hpool_consumer" as "(%xs' & %Hxs' & %Hxs'_sorted & Harr_slice)".
    iModIntro. iSteps. iPureIntro.
    simpl_length. apply Permutation_length. done.
  Qed.

  Lemma pool_quicksort_main_spec (num_dom : nat) arr xs :
    {{{
      array_model arr (DfracOwn 1) (#*@{Z} xs)
    }}}
      pool_quicksort_main #num_dom arr
    {{{
      xs'
    , RET ();
      ⌜xs ≡ₚ xs'⌝ ∗
      ⌜StronglySorted (≤)%Z xs'⌝ ∗
      array_model arr (DfracOwn 1) (#*@{Z} xs')
    }}}.
  Proof.
    iIntros "%Φ Harr HΦ".

    wp_rec.
    wp_apply+ (pool_create_spec with "[//]") as (pool) "(_ & Hpool_model)". 1: lia.

    wp_apply+ (pool_run_spec (λ _,
      pool_consumer pool (
        ∃ xs',
        ⌜xs ≡ₚ xs'⌝ ∗
        ⌜StronglySorted (≤)%Z xs'⌝ ∗
        array_model arr (DfracOwn 1) (#*@{Z} xs')
      )
    )%I with "[$Hpool_model Harr]") as (?) "(Hpool_model & Hpool_consumer)".
    { iIntros "%ctx %scope Hctx".
      wp_apply+ (pool_quicksort_main_1_spec with "[$]") as "$".
    }

    iApply wp_fupd.
    wp_apply+ (pool_close_spec with "[$Hpool_model]") as "#Hpool_finished".
    iMod (pool_consumer_finished with "Hpool_consumer Hpool_finished") as "(%xs' & % & % & Harr)".
    iSteps.
  Qed.
End pool_G.

From examples Require
  pool_quicksort__opaque.
