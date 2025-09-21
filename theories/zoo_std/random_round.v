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
  random_state
  random_round__types.
From zoo Require Import
  options.

Implicit Types i n cnt : nat.
Implicit Types prevs nexts : list nat.
Implicit Types l : location.
Implicit Types t rand arr : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition random_round_model t sz prevs : iProp Σ :=
    ∃ l rand arr nexts,
    ⌜t = #l⌝ ∗
    ⌜nexts ++ reverse prevs ≡ₚ seq 0 sz⌝ ∗
    l.[random] ↦ rand ∗
    l.[array] ↦ arr ∗
    l.[index] ↦ #(length nexts) ∗
    random_state_model rand ∗
    array_model arr (DfracOwn 1) (#@{nat} <$> nexts ++ reverse prevs).
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l &
      %rand &
      %arr &
      %nexts &
      -> &
      %Hpermutation &
      Hl_random &
      Hl_array &
      Hl_index &
      Hrand &
      Harr
    )".

  Lemma random_round_create_spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      random_round_create #sz
    {{{ t,
      RET t;
      random_round_model t ₊sz []
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.

    pose (Ψ := λ arr i vs, (
      ⌜vs = #@{nat} <$> seq 0 i⌝
    )%I : iProp Σ).
    wp_smart_apply (array_unsafe_initi_spec Ψ) as (arr vs) "(_ & Harr & ->)"; first done.
    { iStep 2. iIntros "%arr %i %vs _ _ ->".
      wp_pures.
      iPureIntro. rewrite seq_S fmap_snoc //.
    }

    wp_apply (random_state_create_spec with "[//]") as (rand) "Hrand".
    wp_block l as "(Hl_random & Hl_array & Hl_index & _)".

    iApply "HΦ".
    iFrameSteps. iExists (seq 0 ₊sz).
    rewrite app_nil_r length_seq. iSteps.
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
    iIntros "%Φ (:model) HΦ".

    wp_rec. wp_load.
    wp_apply (array_size_spec with "Harr") as "Harr".

    iSteps. iExists (nexts ++ reverse prevs).
    rewrite app_nil_r. iSteps. simpl_length.
  Qed.

  Lemma random_round_next_spec t sz prevs :
    length prevs ≠ sz →
    {{{
      random_round_model t sz prevs
    }}}
      random_round_next t
    {{{ n,
      RET #n;
      ⌜n < sz⌝ ∗
      ⌜n ∉ prevs⌝ ∗
      random_round_model t sz (prevs ++ [n])
    }}}.
  Proof.
    iIntros "%Hprevs %Φ (:model) HΦ".
    pose proof Hpermutation as Hlength%Permutation_length.
    simpl_length in Hlength.

    wp_rec. do 3 wp_load.
    wp_smart_apply (random_state_int_spec with "Hrand") as (j) "(%Hj & Hrand)"; first lia.

    Z_to_nat j.
    set i := length nexts - 1.

    destruct (lookup_lt_is_Some_2 nexts j) as (prev & Hnexts_lookup_j); first lia.
    wp_smart_apply (array_unsafe_get_spec with "Harr") as "Harr".
    { lia. }
    { rewrite list_lookup_fmap. erewrite lookup_app_l_Some => //. }
    { lia. }

    destruct (lookup_lt_is_Some_2 nexts i) as (next & Hnexts_lookup_i); first lia.
    wp_smart_apply (array_unsafe_get_spec with "Harr") as "Harr".
    { lia. }
    { rewrite list_lookup_fmap. erewrite lookup_app_l_Some => //. }
    { lia. }

    wp_smart_apply (array_unsafe_set_spec with "Harr") as "Harr".
    { simpl_length. lia. }
    wp_smart_apply (array_unsafe_set_spec with "Harr") as "Harr".
    { simpl_length. lia. }
    wp_store. wp_pures.

    iApply "HΦ".
    iSplitR.
    { iPureIntro.
      assert (prev ∈ seq 0 sz) as ?%elem_of_seq; last naive_solver.
      rewrite -Hpermutation elem_of_app elem_of_list_lookup.
      naive_solver.
    }
    iSplitR.
    { iPureIntro.
      pose proof (NoDup_seq 0 sz) as Hnodup.
      rewrite -Hpermutation NoDup_app in Hnodup.
      setoid_rewrite elem_of_reverse in Hnodup.
      setoid_rewrite elem_of_list_lookup at 1 in Hnodup.
      naive_solver.
    }
    rewrite Nat2Z.id -!list_fmap_insert.
    assert (₊(length nexts - 1) = i) as -> by lia.
    assert (<[j := next]> (take i nexts) ++ [prev] = <[i := prev]> (<[j := next]> nexts)) as Heq.
    { destruct_decide (j = i) as -> | H.
      - rewrite list_insert_ge. { simpl_length. lia. }
        rewrite list_insert_insert insert_take_drop; first lia.
        rewrite skipn_all2 //; first lia.
      - rewrite list_insert_commute // (insert_take_drop nexts); first lia.
        rewrite skipn_all2; first lia.
        rewrite -insert_app_l // length_take; first lia.
    }
    iSteps. iExists (<[j := next]> (take i nexts)). iSteps.
    + iPureIntro.
      rewrite -Hpermutation reverse_snoc (assoc _ _ [_]) Heq Permutation_swap' //.
    + simpl_length. iSteps.
    + rewrite reverse_snoc (assoc _ _ [_]) Heq insert_app_l; first lia.
      rewrite insert_app_l // length_insert; first lia.
  Qed.
End zoo_G.

From zoo_std Require
  random_round__opaque.

#[global] Opaque random_round_model.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition random_round_model' t sz cnt : iProp Σ :=
    ∃ prevs,
    ⌜(cnt + length prevs)%nat = sz⌝ ∗
    random_round_model t sz prevs.
  #[local] Instance : CustomIpatFormat "model'" :=
    "(
      %prevs &
      %H &
      Ht
    )".

  Lemma random_round_create_spec' sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      random_round_create #sz
    {{{ t,
      RET t;
      random_round_model' t ₊sz ₊sz
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_apply (random_round_create_spec with "[//]") as (t) "Ht"; first done.
    iStepFrameSteps.
  Qed.

  Lemma random_round_reset_spec' t sz cnt :
    {{{
      random_round_model' t sz cnt
    }}}
      random_round_reset t
    {{{
      RET ();
      random_round_model' t sz sz
    }}}.
  Proof.
    iIntros "%Φ (:model') HΦ".

    wp_apply (random_round_reset_spec with "Ht") as "Ht".
    iStepFrameSteps.
  Qed.

  Lemma random_round_next_spec' t sz cnt :
    0 < cnt →
    {{{
      random_round_model' t sz cnt
    }}}
      random_round_next t
    {{{ n,
      RET #n;
      ⌜n < sz⌝ ∗
      random_round_model' t sz (cnt - 1)
    }}}.
  Proof.
    iIntros "%Hcnt %Φ (:model') HΦ".

    wp_apply (random_round_next_spec with "Ht") as (i) "(%Hi & Ht)"; first lia.
    iSteps. iExists (prevs ++ [i]). simpl_length. iSteps.
  Qed.
End zoo_G.

#[global] Opaque random_round_model'.
