From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  random_round__code.
From zoo_std Require Import
  array
  random
  random_round__types.
From zoo Require Import
  options.

Implicit Types i n : nat.
Implicit Types prevs nexts : list nat.
Implicit Types l : location.
Implicit Types t rand : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition random_round_model t sz prevs : iProp Σ :=
    ∃ l rand arr nexts,
    ⌜t = #l⌝ ∗
    ⌜nexts ++ reverse prevs ≡ₚ seq 0 sz⌝ ∗
    l.[random] ↦ rand ∗
    l.[array] ↦ arr ∗
    l.[index] ↦ #(length nexts) ∗
    random_model rand ∗
    array_model arr (DfracOwn 1) (#@{nat} <$> nexts ++ reverse prevs).

  Lemma random_round_create_spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      random_round_create #sz
    {{{ t,
      RET t;
      random_round_model t (Z.to_nat sz) []
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".
    wp_rec.
    pose (Ψ := λ i vs, (
      ⌜vs = #@{nat} <$> seq 0 i⌝
    )%I : iProp Σ).
    wp_smart_apply (array_unsafe_initi_spec Ψ) as (arr vs) "(_ & Harr & ->)"; first done.
    { iStep. iIntros "!> %i %vs _ _ ->".
      wp_pures.
      iPureIntro. rewrite seq_S fmap_snoc //.
    }
    wp_apply (random_create_spec with "[//]") as (rand) "Hrand".
    wp_block l as "(Hl_random & Hl_array & Hl_index & _)".
    iApply "HΦ".
    iExists l, rand, arr, (seq 0 (Z.to_nat sz)). rewrite right_id length_seq. iSteps.
  Qed.

  Lemma random_round_reset_spec t sz prevs :
    {{{
      random_round_model t sz prevs
    }}}
      random_round_reset t
    {{{
      RET ();
      random_round_model t sz []
    }}}.
  Proof.
    iIntros "%Φ (%l & %rand & %arr & %nexts & -> & %Hpermutation & Hl_random & Hl_array & Hl_index & Hrand & Harr) HΦ".
    wp_rec. wp_load.
    wp_apply (array_size_spec with "Harr") as "Harr".
    iSteps. iExists (nexts ++ reverse prevs). rewrite !right_id. iSteps. iPureIntro.
    rewrite length_fmap Hpermutation length_seq //.
  Qed.

  Lemma random_round_next_spec t sz prevs :
    length prevs ≠ sz →
    {{{
      random_round_model t sz prevs
    }}}
      random_round_next t
    {{{ i,
      RET #i;
      ⌜i < sz ∧ i ∉ prevs⌝ ∗
      random_round_model t sz (prevs ++ [i])
    }}}.
  Proof.
    iIntros "%Hprevs %Φ (%l & %rand & %arr & %nexts & -> & %Hpermutation & Hl_random & Hl_array & Hl_index & Hrand & Harr) HΦ".
    pose proof Hpermutation as Hlength%Permutation_length.
    rewrite length_app length_seq length_reverse in Hlength.
    wp_rec. do 3 wp_load.
    set i := length nexts.
    wp_smart_apply (random_int_spec with "Hrand") as (j) "(%Hj & Hrand)"; first lia.
    Z_to_nat j.
    destruct (lookup_lt_is_Some_2 nexts j) as (prev & Hnexts_lookup_j); first lia.
    wp_smart_apply (array_unsafe_get_spec with "Harr") as "Harr".
    { naive_solver. }
    { rewrite list_lookup_fmap. erewrite lookup_app_l_Some => //. }
    { lia. }
    destruct (lookup_lt_is_Some_2 nexts (i - 1)) as (next & Hnexts_lookup_i); first lia.
    wp_smart_apply (array_unsafe_get_spec with "Harr") as "Harr".
    { lia. }
    { rewrite list_lookup_fmap. erewrite lookup_app_l_Some => //. }
    { lia. }
    wp_smart_apply (array_unsafe_set_spec with "Harr") as "Harr".
    { rewrite length_fmap length_app. lia. }
    wp_smart_apply (array_unsafe_set_spec with "Harr") as "Harr".
    { rewrite length_insert length_fmap length_app. lia. }
    wp_store. wp_pures.
    iApply "HΦ". iSplitR.
    - iPureIntro. split.
      + assert (prev ∈ seq 0 sz) as ?%elem_of_seq; last naive_solver.
        rewrite -Hpermutation elem_of_app elem_of_list_lookup. naive_solver.
      + pose proof (NoDup_seq 0 sz) as Hnodup.
        rewrite -Hpermutation NoDup_app in Hnodup.
        setoid_rewrite elem_of_reverse in Hnodup.
        setoid_rewrite elem_of_list_lookup at 1 in Hnodup.
        naive_solver.
    - rewrite Nat2Z.id -!list_fmap_insert.
      assert (Z.to_nat (i - 1) = i - 1) as -> by lia.
      assert (<[j := next]> (take (i - 1) nexts) ++ [prev] = <[i - 1 := prev]> (<[j := next]> nexts)) as Heq.
      { destruct (decide (j = i - 1)) as [-> | H].
        - rewrite list_insert_ge. { rewrite length_take. lia. }
          rewrite list_insert_insert insert_take_drop; first lia.
          rewrite skipn_all2 //; first lia.
        - rewrite list_insert_commute // (insert_take_drop nexts); first lia.
          rewrite skipn_all2; first lia.
          rewrite -insert_app_l // length_take; first lia.
      }
      iSteps. iExists (<[j := next]> (take (i - 1) nexts)). iSteps.
      + iPureIntro.
        rewrite -Hpermutation reverse_snoc (assoc _ _ [_]) Heq Permutation_swap' //.
      + rewrite length_insert length_take. iSteps.
      + rewrite reverse_snoc (assoc _ _ [_]) Heq insert_app_l; first lia.
        rewrite insert_app_l // length_insert; first lia.
  Qed.
End zoo_G.

#[global] Opaque random_round_create.
#[global] Opaque random_round_reset.
#[global] Opaque random_round_next.

#[global] Opaque random_round_model.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition random_round_model' t sz n : iProp Σ :=
    ∃ prevs,
    ⌜(n + length prevs)%nat = sz⌝ ∗
    random_round_model t sz prevs.

  Lemma random_round_create_spec' sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      random_round_create #sz
    {{{ t,
      RET t;
      random_round_model' t (Z.to_nat sz) (Z.to_nat sz)
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".
    wp_apply (random_round_create_spec with "[//]") as (t) "Ht"; first done.
    iSteps. iExists []. iSteps.
  Qed.

  Lemma random_round_reset_spec' t sz n :
    {{{
      random_round_model' t sz n
    }}}
      random_round_reset t
    {{{
      RET ();
      random_round_model' t sz sz
    }}}.
  Proof.
    iIntros "%Φ (%prevs & %H & Ht) HΦ".
    wp_apply (random_round_reset_spec with "Ht") as "Ht".
    iSteps. iExists []. iSteps.
  Qed.

  Lemma random_round_next_spec' t sz n :
    0 < n →
    {{{
      random_round_model' t sz n
    }}}
      random_round_next t
    {{{ i,
      RET #i;
      ⌜i < sz⌝ ∗
      random_round_model' t sz (n - 1)
    }}}.
  Proof.
    iIntros "%Hn %Φ (%prevs & %H & Ht) HΦ".
    wp_apply (random_round_next_spec with "Ht") as (i) "(%Hi & Ht)"; first lia.
    iSteps. iExists (prevs ++ [i]). rewrite length_app. iSteps.
  Qed.
End zoo_G.

#[global] Opaque random_round_model'.
