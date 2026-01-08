From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  queue_3__code.
From zoo_std Require Import
  queue_3__types
  option
  int
  array.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types front back : nat.
Implicit Types v t : val.
Implicit Types o : option val.

#[local] Definition min_capacity :=
  val_to_nat' queue_3_min_capacity.
#[local] Lemma queue_3_min_capacity :
  queue_3_min_capacity = #min_capacity.
Proof.
  done.
Qed.
Opaque queue_3__code.queue_3_min_capacity.
Opaque min_capacity.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Definition model' t vs extra : iProp Σ :=
    ∃ l data cap front back,
    ⌜t = #l⌝ ∗
    l.[data] ↦ data ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    array_cslice data cap front (DfracOwn 1) vs ∗
    array_cslice data cap back (DfracOwn 1) (replicate extra ()%V) ∗
    ⌜back = (front + length vs)%nat⌝ ∗
    ⌜cap = (length vs + extra)%nat⌝ ∗
    ⌜cap ≠ 0⌝.
  #[local] Instance : CustomIpatFormat "model'" :=
    " ( %l &
        %data &
        %cap &
        %front &
        %back &
        -> &
        Hl_data &
        Hl_front &
        Hl_back &
        Hvs &
        Hextra &
        %Hback &
        %Hcap &
        %
      )
    ".
  Definition queue_3_model t vs : iProp Σ :=
    ∃ extra,
    model' t vs extra.
  #[local] Instance : CustomIpatFormat "model" :=
    " ( %extra &
        {{lazy}Hmodel;(:model')}
      )
    ".

  #[global] Instance queue_3_model_timeless t vs :
    Timeless (queue_3_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma queue_3_model_exclusive t vs1 vs2 :
    queue_3_model t vs1 -∗
    queue_3_model t vs2 -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma queue_3_create_spec :
    {{{
      True
    }}}
      queue_3_create ()
    {{{ t,
      RET t;
      queue_3_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec. rewrite queue_3_min_capacity.
    wp_apply (array_unsafe_make_spec with "[//]") as (data) "Hextra"; first done.
    iDestruct (array_model_to_cslice with "Hextra") as "Hextra". simpl_length.
    iDestruct (array_cslice_to_inv with "Hextra") as "#Hdata_inv".
    iDestruct (array_cslice_nil with "Hdata_inv") as "Hvs".
    wp_block l as "(Hl_data & Hl_front & Hl_back & _)".
    iSteps.
  Qed.

  Lemma queue_3_size_spec t vs :
    {{{
      queue_3_model t vs
    }}}
      queue_3_size t
    {{{
      RET #(length vs);
      queue_3_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_rec. do 2 wp_load. wp_pures.
    assert (back - front = length vs)%Z as -> by lia.
    iSteps.
  Qed.

  Lemma queue_3_is_empty_spec t vs :
    {{{
      queue_3_model t vs
    }}}
      queue_3_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      queue_3_model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    wp_rec.
    wp_apply (queue_3_size_spec with "Hmodel") as "Hmodel".
    wp_pures.
    rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
    { rewrite -length_zero_iff_nil. lia. }
    iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma queue_3_unsafe_get_spec {t vs i} v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      queue_3_model t vs
    }}}
      queue_3_unsafe_get t #i
    {{{
      RET v;
      queue_3_model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (:model) HΦ".

    wp_rec. do 2 wp_load.
    wp_apply (array_unsafe_cget_spec with "Hvs"); [lia | done | lia |].
    iSteps.
  Qed.

  Lemma queue_3_unsafe_set_spec t vs i v :
    (0 ≤ i < length vs)%Z →
    {{{
      queue_3_model t vs
    }}}
      queue_3_unsafe_set t #i v
    {{{
      RET ();
      queue_3_model t (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (:model) HΦ".

    wp_rec. do 2 wp_load.
    wp_apply (array_unsafe_cset_spec with "Hvs"); first lia.
    replace (₊(front + i) - front) with ₊i by lia.
    iSteps; simpl_length.
  Qed.

  #[local] Lemma queue_3_next_capacity_spec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      queue_3_next_capacity #n
    {{{ m,
      RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma queue_3_grow_spec t vs extra :
    {{{
      model' t vs extra
    }}}
      queue_3_grow t
    {{{ extra,
      RET ();
      ⌜0 < extra⌝ ∗
      model' t vs extra
    }}}.
  Proof.
    iIntros "%Φ (:model') HΦ".

    wp_rec. do 3 wp_load.
    wp_smart_apply (array_size_spec_cslice with "Hvs") as "Hvs".
    wp_pures.
    case_bool_decide.

    - iClear "Hextra".
      wp_smart_apply (queue_3_next_capacity_spec with "[//]") as (cap') "%Hcap'"; first lia.
      wp_smart_apply int_max_spec.
      wp_smart_apply (array_unsafe_cgrow_spec with "Hvs") as (data') "(_ & Hvs)"; [lia.. |].
      wp_store.
      iDestruct (array_cslice_app with "Hvs") as "(Hvs & Hextra)".
      rewrite -Hback. iSteps.
      iExists ₊(((⁺cap + 1) `max` cap') - cap). iSteps.
      rewrite Z2Nat.inj_sub; first lia. rewrite Nat2Z.id. iSteps.

    - iSteps. iExists extra. iSteps.
  Qed.

  Lemma queue_3_push_spec t vs v :
    {{{
      queue_3_model t vs
    }}}
      queue_3_push t v
    {{{
      RET ();
      queue_3_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (:model lazy=) HΦ".

    wp_rec.
    wp_smart_apply (queue_3_grow_spec with "Hmodel") as (extra') "(%Hextra' & (:model'))".
    do 2 wp_load.
    destruct (Nat.lt_exists_pred 0 extra') as (extra'' & -> & _); first lia.
    iDestruct (array_cslice_cons with "Hextra") as "(Hcell & Hextra)". rewrite -/replicate.
    wp_apply (array_unsafe_cset_spec_cell with "Hcell") as "Hcell"; first done.
    iDestruct (array_cslice_app_1 with "Hvs Hcell") as "Hvs"; first done.
    wp_store.
    replace (back + 1)%Z with ⁺(S back) by lia.
    iSteps; iPureIntro; simpl_length/=; lia.
  Qed.

  #[local] Lemma queue_3_shrink_spec t vs :
    {{{
      queue_3_model t vs
    }}}
      queue_3_shrink t
    {{{
      RET ();
      queue_3_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_rec. rewrite queue_3_min_capacity. do 3 wp_load.
    wp_smart_apply (array_size_spec_cslice with "Hvs") as "Hvs".
    wp_pures.
    case_bool_decide; last iSteps.
    iDestruct (array_cslice_app_1 with "Hvs Hextra") as "Hvs"; first done.
    wp_pures. rewrite -Z.div2_spec.
    wp_apply (array_unsafe_cshrink_slice_spec with "Hvs") as (data') "(_ & Hvs)"; [simpl_length; lia.. |].
    wp_store.
    rewrite Nat2Z.id Nat.sub_diag slice_0 take_app_ge; first lia.
    rewrite take_replicate.
    iDestruct (array_cslice_app with "Hvs") as "(Hvs & Hextra)".
    iStepFrameSteps.
  Qed.

  Lemma queue_3_pop_front_spec t vs :
    {{{
      queue_3_model t vs
    }}}
      queue_3_pop_front t
    {{{
      RET head vs;
      queue_3_model t (tail vs)
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
      wp_store.
      iDestruct (array_cslice_shift_right with "Hcell") as "Hcell".
      iDestruct (array_cslice_app_1 with "Hextra Hcell") as "Hextra".
      { simpl_length. lia. }
      rewrite -replicate_S_end.
      wp_smart_apply (queue_3_shrink_spec _ vs with "[-HΦ]") as "Hmodel".
      { iExists (S extra). iFrameSteps. }
      wp_pures.
      iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma queue_3_pop_back_spec t vs :
    {{{
      queue_3_model t vs
    }}}
      queue_3_pop_back t
    {{{ o,
      RET o;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          queue_3_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          queue_3_model t vs'
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
      wp_store.
      iDestruct (array_cslice_cons_2' with "Hcell Hextra") as "Hextra"; first lia.
      rewrite -replicate_S.
      wp_smart_apply (queue_3_shrink_spec _ vs with "[-HΦ]") as "Hmodel".
      { iExists (S extra). iFrameSteps. }
      wp_pures.
      iApply ("HΦ" $! (Some v)).
      iFrameSteps.
  Qed.
End zoo_G.

From zoo_std Require
  queue_3__opaque.

#[global] Opaque queue_3_model.
