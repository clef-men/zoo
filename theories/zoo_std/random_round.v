Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Export zoo_std.random_round__code.
Require Import zoo_std.random_round__types.
Require Import zoo.options.

Implicit Type i n cnt : nat.
Implicit Type prevs nexts : list nat.
Implicit Type l : location.
Implicit Type t rand arr : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition random_round۰model t sz prevs : iProp Σ :=
    ∃ l rand arr nexts,
    ⌜t = #l⌝ ∗
    ⌜nexts ++ reverse prevs ≡ₚ seq 0 sz⌝ ∗
    l.[random] ↦ rand ∗
    l.[array] ↦ arr ∗
    l.[index] ↦ #(length nexts) ∗
    random_state۰model rand ∗
    array۰model arr (DfracOwn 1) (#*@{nat} $ nexts ++ reverse prevs).
  #[local] Instance : CustomIpat "model" :=
    " ( %l
      & %rand
      & %arr
      & %nexts
      & ->
      & %Hpermutation
      & Hl_random
      & Hl_array
      & Hl_index
      & Hrand
      & Harr
      )
    ".

  Lemma random_round٠createｰspec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      random_round٠create #sz
    {{{
      t
    , RET t;
      random_round۰model t ₊sz []
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.

    pose (Ψ := λ arr i vs, (
      ⌜vs = #*@{nat} $ seq 0 i⌝
    )%I : iProp Σ).
    wp۰apply+ (array٠unsafe_initiｰspec Ψ) as (arr vs) "(_ & Harr & ->)"; first done.
    { iStep 2. iIntros "%arr %i %vs _ _ ->".
      wp۰pures.
      iPureIntro. rewrite seq_S fmap_snoc //.
    }

    wp۰apply (random_state٠createｰspec with "[//]") as (rand) "Hrand".
    wp۰block l as "Hl_random Hl_array Hl_index".

    iApply "HΦ".
    iFrameSteps. iExists (seq 0 ₊sz).
    rewrite app_nil_r length_seq. iSteps.
  Qed.

  Lemma random_round٠resetｰspec t sz prevs :
    {{{
      random_round۰model t sz prevs
    }}}
      random_round٠reset t
    {{{
      RET ();
      random_round۰model t sz []
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (array٠sizeｰspec with "Harr") as "Harr".

    iSteps. iExists (nexts ++ reverse prevs).
    rewrite app_nil_r. iSteps. simp_length.
  Qed.

  Lemma random_round٠nextｰspec t sz prevs :
    length prevs ≠ sz →
    {{{
      random_round۰model t sz prevs
    }}}
      random_round٠next t
    {{{
      n
    , RET #n;
      ⌜n < sz⌝ ∗
      ⌜n ∉ prevs⌝ ∗
      random_round۰model t sz (prevs ++ [n])
    }}}.
  Proof.
    iIntros "%Hprevs %Φ (:model) HΦ".
    pose proof Hpermutation as Hlength%Permutation_length.
    simp_length in Hlength.

    wp۰rec. do 3 wp۰load.
    wp۰apply+ (random_state٠intｰspec with "Hrand") as (j) "(%Hj & Hrand)"; first lia.

    Z_to_nat j.
    set i := length nexts - 1.

    destruct (lookup_lt_is_Some_2 nexts j) as (prev & Hnexts_lookup_j); first lia.
    wp۰apply+ (array٠unsafe_getｰspec with "Harr") as "Harr".
    { lia. }
    { rewrite list_lookup_fmap. erewrite lookup_app_l_Some => //. }
    { lia. }

    destruct (lookup_lt_is_Some_2 nexts i) as (next & Hnexts_lookup_i); first lia.
    wp۰apply+ (array٠unsafe_getｰspec with "Harr") as "Harr".
    { lia. }
    { rewrite list_lookup_fmap. erewrite lookup_app_l_Some => //. }
    { lia. }

    wp۰apply+ (array٠unsafe_setｰspec with "Harr") as "Harr".
    { simp_length. lia. }
    wp۰apply+ (array٠unsafe_setｰspec with "Harr") as "Harr".
    { simp_length. lia. }
    wp۰store. wp۰pures.

    iApply "HΦ".
    iSplitR.
    { iPureIntro.
      assert (prev ∈ seq 0 sz) as ?%elem_of_seq; last naive_solver.
      rewrite -Hpermutation elem_of_app list_elem_of_lookup.
      naive_solver.
    }
    iSplitR.
    { iPureIntro.
      pose proof (NoDup_seq 0 sz) as Hnodup.
      rewrite -Hpermutation NoDup_app in Hnodup.
      setoid_rewrite elem_of_reverse in Hnodup.
      setoid_rewrite list_elem_of_lookup at 1 in Hnodup.
      naive_solver.
    }
    rewrite Nat2Z.id -!list_fmap_insert.
    assert (₊(length nexts - 1) = i) as -> by lia.
    assert (<[j := next]> (take i nexts) ++ [prev] = <[i := prev]> (<[j := next]> nexts)) as Heq.
    { destruct_decide (j = i) as -> | H.
      - rewrite list_insert_ge. { simp_length. lia. }
        rewrite list_insert_insert_eq insert_take_drop; first lia.
        rewrite skipn_all2 //; first lia.
      - rewrite list_insert_insert_ne // (insert_take_drop nexts); first lia.
        rewrite skipn_all2; first lia.
        rewrite -insert_app_l // length_take; first lia.
    }
    iSteps. iExists (<[j := next]> (take i nexts)). iSteps.
    + iPureIntro.
      rewrite -Hpermutation reverse_snoc (assoc _ _ [_]) Heq Permutationｰswap' //.
    + simp_length. iSteps.
    + rewrite reverse_snoc (assoc _ _ [_]) Heq insert_app_l; first lia.
      rewrite insert_app_l // length_insert; first lia.
  Qed.
End zoo۰G.

Require zoo_std.random_round__opaque.

#[global] Opaque random_round۰model.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition random_round۰model' t sz cnt : iProp Σ :=
    ∃ prevs,
    ⌜(cnt + length prevs)%nat = sz⌝ ∗
    random_round۰model t sz prevs.
  #[local] Instance : CustomIpat "model'" :=
    " ( %prevs
      & %H
      & Ht
      )
    ".

  Lemma random_round٠createｰspec' sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      random_round٠create #sz
    {{{
      t
    , RET t;
      random_round۰model' t ₊sz ₊sz
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰apply (random_round٠createｰspec with "[//]") as (t) "Ht"; first done.
    iStepFrameSteps.
  Qed.

  Lemma random_round٠resetｰspec' t sz cnt :
    {{{
      random_round۰model' t sz cnt
    }}}
      random_round٠reset t
    {{{
      RET ();
      random_round۰model' t sz sz
    }}}.
  Proof.
    iIntros "%Φ (:model') HΦ".

    wp۰apply (random_round٠resetｰspec with "Ht") as "Ht".
    iStepFrameSteps.
  Qed.

  Lemma random_round٠nextｰspec' t sz cnt :
    0 < cnt →
    {{{
      random_round۰model' t sz cnt
    }}}
      random_round٠next t
    {{{
      n
    , RET #n;
      ⌜n < sz⌝ ∗
      random_round۰model' t sz (cnt - 1)
    }}}.
  Proof.
    iIntros "%Hcnt %Φ (:model') HΦ".

    wp۰apply (random_round٠nextｰspec with "Ht") as (i) "(%Hi & Ht)"; first lia.
    iSteps. iExists (prevs ++ [i]). simp_length. iSteps.
  Qed.
End zoo۰G.

#[global] Opaque random_round۰model'.
