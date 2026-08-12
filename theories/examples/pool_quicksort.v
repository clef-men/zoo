Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Import zoo_std.for_.
Require Export examples.pool_quicksort__code.
Require Import examples.pool_quicksort__types.
Require Import zoo.options.

Section pool۰G.
  Context `{pool۰G : PoolG}.

  #[local] Lemma pool_quicksort٠partitionｰspec arr i i_ xs sz :
    (0 ≤ i)%Z →
    i_ = ₊i →
    (1 < sz)%Z →
    length xs = ₊sz →
    {{{
      array۰slice arr i_ (DfracOwn 1) (#*@{Z} xs)
    }}}
      pool_quicksort٠partition arr #i #sz
    {{{
      xs1 p pivot xs2
    , RET #p;
      ⌜p = (i_ + length xs1)%nat⌝ ∗
      ⌜xs ≡ₚ xs1 ++ pivot :: xs2⌝ ∗
      ⌜Forall ((≥)%Z pivot) xs1⌝ ∗
      ⌜Forall ((≤)%Z pivot) xs2⌝ ∗
      array۰slice arr i_ (DfracOwn 1) (#*@{Z} xs1 ++ #@{Z} pivot :: #*@{Z} xs2)
    }}}.
  Proof.
    iIntros (Hi -> Hsz Hxs) "%Φ Harr HΦ".

    destruct xs as [| pivot xs]; simpl in Hxs. 1: lia.
    iEval (rewrite fmap_cons) in "Harr".
    iDestruct (array۰sliceｰcons₁ with "Harr") as "(Harr_1 & Harr_2)".

    wp۰rec.
    wp۰apply+ (array٠unsafe_getｰspecｰcell with "Harr_1") as "Harr_1". 1: lia.
    wp۰ref r as "Hr".

    wp۰apply+ (forｰspecｰstrong (λ j _,
      ∃ xs' (i1 : Z),
      array۰slice arr ˖(₊i) (DfracOwn 1) (#*@{Z} xs') ∗
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

      wp۰apply+ (array٠unsafe_getｰspecｰslice with "Harr") as "Harr".
      { lia. }
      { apply list_lookup_fmap_Some_2 => //. }
      { lia. }

      wp۰pures.
      case_bool_decide as Hx2; wp۰pures.

      - wp۰load.

        wp۰apply (array٠unsafe_swapｰspecｰslice ₊(i1 - i - 1) with "Harr") as "Harr".
        1,2,4: lia.
        1,2: apply list_lookup_fmap_Some_2 => //.
        1: lia.
        iEval (rewrite -!list_fmap_insert) in "Harr".

        iStep 15. iPureIntro. split_and!.
        { rewrite Permutationｰswap' //. }
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

    iDestruct (array۰sliceｰcons₂ with "Harr_1 Harr_2") as "Harr".

    wp۰load. wp۰pures.

    destruct_decide (i1 = i + 1)%Z as -> | Hcase.

    - wp۰apply+ (array٠unsafe_swapｰspecｰsliceｰid with "Harr") as "Harr". 1,2: simpl; lia.
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
        - simp_length. lia.
        - apply Forall_lookup. intros k x (Hlookup & Hk)%lookup_take_Some.
          eapply Z.le_ge, H1; [done | lia].
        - simp_length. lia.
        - apply Forall_lookup. intros k x Hlookup.
          rewrite lookup_drop in Hlookup.
          apply lookup_lt_Some in Hlookup as ?.
          eapply H2; [done | lia].
      }
      iEval (rewrite fmap_app) in "Harr".

      destruct xs1 as [| x xs1 _] using rev_ind. 1: naive_solver lia.
      simp_length/= in Hxs1_length.
      iEval (rewrite fmap_app /=) in "Harr".

      iDestruct (array۰sliceｰapp₂ (_ :: _) with "Harr") as "(Harr_1 & Harr_2)". 1: done.
      wp۰apply+ (array٠unsafe_swapｰspecｰslice 0 ₊(i1 - i - 1) with "Harr_1") as "Harr_1". 1-4,6: auto with lia.
      { apply lookupｰconsｰrｰSome. 1: lia.
        apply lookupｰappｰrｰSome; simp_length. 1: lia.
        replace _ with 0 by lia. done.
      }
      iEval (rewrite /= insertｰconsｰr; first lia) in "Harr_1".
      iEval (rewrite insert_app_r_alt; first (simp_length; lia)) in "Harr_1".
      iEval (simp_length) in "Harr_1".
      iEval (rewrite insertｰconsｰl; first lia) in "Harr_1".
      iDestruct (array۰sliceｰapp₁' with "Harr_1 Harr_2") as "Harr". 1: simp_length/=.
      iEval (rewrite -(assoc _ (_ :: _))) in "Harr".

      wp۰load. wp۰pures.

      iEval (rewrite -(Z2Nat.id (i1 - 1)); first lia).
      iApply ("HΦ" $! (x :: xs1) _ pivot xs2).
      iFrameSteps; iPureIntro.
      { rewrite Hxs'. solve_Permutation. }
      { rewrite Permutation_cons_append //. }
  Qed.

  #[local] Lemma pool_quicksort٠main₂ｰspec pool ctx scope arr i i_ xs sz :
    (0 ≤ i)%Z →
    i_ = ₊i →
    length xs = ₊sz →
    {{{
      pool۰context pool ctx scope ∗
      array۰slice arr i_ (DfracOwn 1) (#*@{Z} xs)
    }}}
      pool_quicksort٠main₂ ctx arr #i #sz
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      pool۰consumer pool (
        ∃ xs',
        ⌜xs ≡ₚ xs'⌝ ∗
        ⌜StronglySorted (≤)%Z xs'⌝ ∗
        array۰slice arr i_ (DfracOwn 1) (#*@{Z} xs')
      )
    }}}.
  Proof.
    iIntros "%Hi %Hi_ %Hsz %Φ (Hctx & Harr) HΦ".

    iLöb as "HLöb" forall (ctx scope i i_ xs sz Hi Hi_ Hsz Φ).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - wp۰apply (pool_quicksort٠partitionｰspec with "Harr") as (xs1 p pivot xs2) "(%Hp & %Hxs & %Hxs1 & %Hxs2 & Harr)". 1-4: done.
      iDestruct (array۰sliceｰappｰ3 _ [_] with "Harr") as "(Harr_1 & Harr_2 & Harr_3)".

      wp۰apply+ (pool٠asyncｰspec
        ( pool۰consumer pool (
            ∃ xs1',
            ⌜xs1 ≡ₚ xs1'⌝ ∗
            ⌜StronglySorted (≤)%Z xs1'⌝ ∗
            array۰slice arr i_ (DfracOwn 1) (#*@{Z} xs1')
          )
        )
        True
      with "[$Hctx Harr_1]") as "(Hctx & Hpool_consumer_1 & _)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp۰apply+ ("HLöb" with "[//] [//] [%] Hctx Harr_1") as "($ & $) //". 1: lia.
      }

      wp۰apply+ (pool٠asyncｰspec
        ( pool۰consumer pool (
            ∃ xs2',
            ⌜xs2 ≡ₚ xs2'⌝ ∗
            ⌜StronglySorted (≤)%Z xs2'⌝ ∗
            array۰slice arr ˖p (DfracOwn 1) (#*@{Z} xs2')
          )
        )
        True
      with "[$Hctx Harr_3]") as "(Hctx & Hpool_consumer_2 & _)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp۰apply+ ("HLöb" with "[%] [%] [%] Hctx Harr_3") as "($ & Hpool_consumer)".
        { lia. }
        { simp_length/=. lia. }
        { apply Permutation_length in Hxs. simp_length/= in Hxs. lia. }
        iEval (simp_length/=) in "Hpool_consumer".
        iEval (rewrite -Hp Nat.add_1_r) in "Hpool_consumer".
        iFrameSteps.
      }

      iApply "HΦ".
      iFrame.
      iMod "Hpool_consumer_1" as ">(%xs1' & %Hxs1'_permutation & %Hxs1'_sorted & Harr_1)".
      iMod "Hpool_consumer_2" as ">(%xs2' & %Hxs2'_permutation & %Hxs2'_sorted & Harr_3)".
      iModIntro.
      iDestruct (array۰sliceｰappｰ3₁ with "Harr_1 Harr_2 Harr_3") as "Harr".
      { simp_length. apply Permutation_length in Hxs1'_permutation. lia. }
      { simp_length/=. apply Permutation_length in Hxs1'_permutation. lia. }
      iEval (rewrite -(fmap_app _ [_]) -fmap_app) in "Harr".
      iFrame. iPureIntro. split.
      { rewrite -Hxs1'_permutation -Hxs2'_permutation //. }
      { apply: StronglySortedｰappｰcons. 1,4: done.
        - rewrite -Hxs1'_permutation.
          eapply Forall_impl => //=. lia.
        - rewrite -Hxs2'_permutation //.
      }

    - iSteps. do 2 iModIntro.
      iExists xs. iSteps. iPureIntro.
      apply StronglySortedｰtrivial. lia.
  Qed.
  #[local] Lemma pool_quicksort٠main₁ｰspec pool ctx scope arr xs :
    {{{
      pool۰context pool ctx scope ∗
      array۰model arr (DfracOwn 1) (#*@{Z} xs)
    }}}
      pool_quicksort٠main₁ ctx arr
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      pool۰consumer pool (
        ∃ xs',
        ⌜xs ≡ₚ xs'⌝ ∗
        ⌜StronglySorted (≤)%Z xs'⌝ ∗
        array۰model arr (DfracOwn 1) (#*@{Z} xs')
      )
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Harr_model) HΦ".

    wp۰rec.

    wp۰apply+ (array٠sizeｰspec with "Harr_model") as "Harr_model".
    iEval (simp_length).

    iDestruct (array۰modelｰtoｰslice' with "Harr_model") as "(Harr_slice & #Harr_model)".
    wp۰apply+ (pool_quicksort٠main₂ｰspec with "[$]") as "(Hctx & Hpool_consumer)". 1-3: lia.

    iSteps.
    iMod "Hpool_consumer" as "(%xs' & %Hxs' & %Hxs'_sorted & Harr_slice)".
    iModIntro. iSteps. iPureIntro.
    simp_length. apply Permutation_length. done.
  Qed.

  Lemma pool_quicksort٠mainｰspec (num_dom : nat) arr xs :
    {{{
      array۰model arr (DfracOwn 1) (#*@{Z} xs)
    }}}
      pool_quicksort٠main #num_dom arr
    {{{
      xs'
    , RET ();
      ⌜xs ≡ₚ xs'⌝ ∗
      ⌜StronglySorted (≤)%Z xs'⌝ ∗
      array۰model arr (DfracOwn 1) (#*@{Z} xs')
    }}}.
  Proof.
    iIntros "%Φ Harr HΦ".

    wp۰rec.

    iApply wpｰfupd.
    wp۰apply+ (pool٠runｰspec (λ pool res,
      ⌜res = ()%V⌝ ∗
      pool۰consumer pool (
        ∃ xs',
        ⌜xs ≡ₚ xs'⌝ ∗
        ⌜StronglySorted (≤)%Z xs'⌝ ∗
        array۰model arr (DfracOwn 1) (#*@{Z} xs')
      )
    )%I with "[Harr]") as (pool ?) "(#Hpool_finished & -> & Hpool_consumer)". 1: lia.
    { iIntros "%pool %ctx %scope _ Hctx".
      wp۰apply+ (pool_quicksort٠main₁ｰspec with "[$]").
      iSteps.
    }

    iMod (pool۰consumerｰfinished with "Hpool_consumer Hpool_finished") as "(%xs' & % & % & Harr)".
    iSteps.
  Qed.
End pool۰G.

Require examples.pool_quicksort__opaque.
