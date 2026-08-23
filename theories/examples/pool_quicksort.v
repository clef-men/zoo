Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Export examples.pool_quicksort__code.
Require Import examples.pool_quicksort__types.
Require Import zoo.options.

Section pool۰G.
  Context `{pool۰G : PoolG}.

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

    - wp۰apply (array٠partitionｰspec with "Harr") as (xs1 p pivot xs2) "(%Hp & %Hxs & %Hxs1 & %Hxs2 & Harr)". 1-4: done.
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
        { lengths/=. lia. }
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
      { lengths. lia. }
      { lengths/=. lia. }
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
    iModIntro. iSteps. iPureIntro. lengths.
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
