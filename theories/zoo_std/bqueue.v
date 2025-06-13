From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  bqueue__code.
From zoo_std Require Import
  bqueue__types
  option
  array.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types front back : nat.
Implicit Types v t : val.
Implicit Types o : option val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition bqueue_model t (cap : nat) vs : iProp Σ :=
    ∃ l data front back extra,
    ⌜t = #l⌝ ∗
    l.[capacity] ↦□ #cap ∗
    l.[data] ↦□ data ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    array_cslice data cap front (DfracOwn 1) vs ∗
    array_cslice data cap back (DfracOwn 1) (replicate extra ()%V) ∗
    ⌜back = (front + length vs)%nat⌝ ∗
    ⌜cap = (length vs + extra)%nat⌝.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l &
      %data &
      %front &
      %back &
      %extra &
      -> &
      Hl_capacity &
      Hl_data &
      Hl_front &
      Hl_back &
      Hvs &
      Hextra &
      % &
      %
    )".

  #[global] Instance bqueue_model_timeless t cap vs :
    Timeless (bqueue_model t cap vs).
  Proof.
    apply _.
  Qed.

  Lemma bqueue_model_valid t cap vs :
    bqueue_model t cap vs ⊢
    ⌜length vs ≤ cap⌝.
  Proof.
    iSteps.
  Qed.
  Lemma bqueue_model_exclusive t cap1 vs1 cap2 vs2 :
    bqueue_model t cap1 vs1 -∗
    bqueue_model t cap2 vs2 -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma bqueue_create_spec cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      bqueue_create #cap
    {{{ t,
      RET t;
      bqueue_model t ₊cap []
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".

    wp_rec.
    wp_apply (array_unsafe_make_spec with "[//]") as (data) "Hextra"; first done.
    iDestruct (array_model_to_cslice with "Hextra") as "Hextra". simpl_length.
    iDestruct (array_cslice_to_inv with "Hextra") as "#Hdata_inv".
    iDestruct (array_cslice_nil with "Hdata_inv") as "Hvs".
    wp_block l as "(Hl_capacity & Hl_data & Hl_front & Hl_back & _)".
    iFrameSteps. rewrite Z2Nat.id //. iSteps.
  Qed.

  Lemma bqueue_size_spec t cap vs :
    {{{
      bqueue_model t cap vs
    }}}
      bqueue_size t
    {{{
      RET #(length vs);
      bqueue_model t cap vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_rec. do 2 wp_load. wp_pures.
    assert (back - front = length vs)%Z as -> by lia.
    iSteps.
  Qed.

  Lemma bqueue_is_empty_spec t cap vs :
    {{{
      bqueue_model t cap vs
    }}}
      bqueue_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      bqueue_model t cap vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    wp_rec.
    wp_apply (bqueue_size_spec with "Hmodel") as "Hmodel".
    wp_pures.
    rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
    { rewrite -length_zero_iff_nil. lia. }
    iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma bqueue_unsafe_get_spec {t cap vs i} v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      bqueue_model t cap vs
    }}}
      bqueue_unsafe_get t #i
    {{{
      RET v;
      bqueue_model t cap vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (:model) HΦ".

    wp_rec. do 2 wp_load.
    wp_apply (array_unsafe_cget_spec with "Hvs"); [lia | done | lia |].
    iSteps.
  Qed.

  Lemma bqueue_unsafe_set_spec t cap vs i v :
    (0 ≤ i < length vs)%Z →
    {{{
      bqueue_model t cap vs
    }}}
      bqueue_unsafe_set t #i v
    {{{
      RET ();
      bqueue_model t cap (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (:model) HΦ".

    wp_rec. do 2 wp_load.
    wp_apply (array_unsafe_cset_spec with "Hvs"); first lia.
    replace (₊(front + i) - front) with ₊i by lia.
    iSteps; simpl_length.
  Qed.

  Lemma bqueue_push_spec t cap vs v :
    {{{
      bqueue_model t cap vs
    }}}
      bqueue_push t v
    {{{ b,
      RET #b;
      ⌜if b then True else length vs = cap⌝ ∗
      bqueue_model t cap (if b then vs ++ [v] else vs)
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_rec. do 3 wp_load. wp_pures.
    case_bool_decide; first iSteps.
    wp_load.
    destruct (Nat.lt_exists_pred 0 extra) as (extra' & -> & _); first lia.
    iDestruct (array_cslice_cons with "Hextra") as "(Hcell & Hextra)". rewrite -/replicate.
    wp_apply (array_unsafe_cset_spec_cell with "Hcell") as "Hcell"; first done.
    iDestruct (array_cslice_app_1 with "Hvs Hcell") as "Hvs"; first done.
    wp_store. wp_pures.
    replace (back + 1)%Z with ⁺(S back) by lia.
    iSteps; iPureIntro; simpl_length/=; lia.
  Qed.

  Lemma bqueue_pop_front_spec t cap vs :
    {{{
      bqueue_model t cap vs
    }}}
      bqueue_pop_front t
    {{{
      RET head vs : val;
      bqueue_model t cap (tail vs)
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_rec. do 2 wp_load. wp_pures.
    case_bool_decide.

    - destruct vs; last naive_solver lia.
      iSteps.

    - destruct vs as [| v vs]; first naive_solver. simpl in *.
      wp_load.
      iDestruct (array_cslice_cons with "Hvs") as "(Hcell & Hvs)".
      wp_smart_apply (array_unsafe_cget_spec_cell with "Hcell") as "Hcell"; first done.
      wp_smart_apply (array_unsafe_cset_spec_cell with "Hcell") as "Hcell"; first done.
      wp_store. wp_pures.
      iDestruct (array_cslice_shift_forward with "Hcell") as "Hcell".
      iDestruct (array_cslice_app_1 with "Hextra Hcell") as "Hextra".
      { simpl_length. lia. }
      iApply "HΦ".
      rewrite -replicate_S_end.
      replace (front + 1)%Z with ⁺(S front) by lia.
      iFrameSteps.
  Qed.

  Lemma bqueue_pop_back_spec t cap vs :
    {{{
      bqueue_model t cap vs
    }}}
      bqueue_pop_back t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          bqueue_model t cap []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          bqueue_model t cap vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_rec. do 2 wp_load. wp_pures.
    case_bool_decide.

    - destruct vs; last naive_solver lia.
      iSpecialize ("HΦ" $! None).
      iSteps.

    - destruct vs as [| v vs _] using rev_ind; first naive_solver. simpl_length/= in *.
      wp_load.
      iDestruct (array_cslice_app with "Hvs") as "(Hvs & Hcell)".
      wp_smart_apply (array_unsafe_cget_spec_cell with "Hcell") as "Hcell"; first lia.
      wp_smart_apply (array_unsafe_cset_spec_cell with "Hcell") as "Hcell"; first lia.
      wp_store. wp_pures.
      iDestruct (array_cslice_cons_2' with "Hcell Hextra") as "Hextra"; first lia.
      iApply ("HΦ" $! (Some v)).
      rewrite -replicate_S.
      iExists vs. iFrameSteps.
  Qed.
End zoo_G.

From zoo_std Require
  bqueue__opaque.

#[global] Opaque bqueue_model.
