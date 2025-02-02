From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  dynarray_2__code.
From zoo_std Require Import
  diverge
  assume
  int
  array
  dynarray_2__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types i : nat.
Implicit Types l elem  : location.
Implicit Types elems : list location.
Implicit Types v t slot fn : val.
Implicit Types vs slots : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Definition element_model elem v : iProp Σ :=
    elem ↦ₕ Header 1 §Element ∗
    elem.[value] ↦ v.
  #[local] Instance : CustomIpatFormat "element_model" :=
    "(
      Helem_header &
      Helem_value
    )".
  Definition dynarray_2_model t vs : iProp Σ :=
    ∃ l data elems extra,
    ⌜t = #l⌝ ∗
    l.[size] ↦ #(length vs) ∗
    l.[data] ↦ data ∗
    array_model data (DfracOwn 1) ((#@{location} <$> elems) ++ replicate extra §Empty%V) ∗
    [∗ list] elem; v ∈ elems; vs, element_model elem v.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l &
      %data &
      %elems &
      %extra &
      -> &
      Hl_size &
      Hl_data &
      Hmodel &
      Helems
    )".

  #[global] Instance dynarray_2_model_timeless t vs :
    Timeless (dynarray_2_model t vs).
  Proof.
    apply _.
  Qed.

  #[local] Lemma dynarray_2_element_spec v :
    {{{
      True
    }}}
      dynarray_2_element v
    {{{ elem,
      RET #elem;
      element_model elem v
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2_create_spec :
    {{{
      True
    }}}
      dynarray_2_create ()
    {{{ t,
      RET t;
      dynarray_2_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_spec with "[//]") as "%data Hmodel".
    wp_block l as "(Hl_size & Hl_data & _)".
    iApply "HΦ".
    iExists l, data, [], 0. iSteps.
  Qed.

  Lemma dynarray_2_make_spec sz v :
    {{{
      True
    }}}
      dynarray_2_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      dynarray_2_model t (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    pose (Ψ i slots := (
      ∃ elems,
      ⌜slots = #@{location} <$> elems⌝ ∗
      [∗ list] elem ∈ elems, element_model elem v
    )%I).
    wp_smart_apply (array_init_spec Ψ) as "%data %slots (%Hsz & %Helems & Hmodel & (%elems & -> & Helems))".
    { iSplit.
      - iExists []. iSteps.
      - iIntros "!> %i %slots %Hi1 %Hi2 (%elems & -> & Helems)".
        wp_smart_apply (dynarray_2_element_spec with "[//]") as (elem) "Helem".
        iExists (elems ++ [elem]).
        rewrite -fmap_snoc big_sepL_snoc. iSteps.
    }
    iSteps.
    - rewrite length_replicate. iSteps.
    - iExists elems, 0. rewrite right_id. iSteps.
      iApply (big_sepL2_replicate_r_2 _ _ (λ _, element_model) with "Helems").
      { rewrite length_fmap // in Helems. }
  Qed.

  Lemma dynarray_2_initi_spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < ₊sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      dynarray_2_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜sz = length vs⌝ ∗
      dynarray_2_model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    pose (Ψ' i slots := (
      ∃ elems vs,
      ⌜slots = #@{location} <$> elems⌝ ∗
      Ψ i vs ∗
      [∗ list] elem; v ∈ elems; vs, element_model elem v
    )%I).
    wp_smart_apply (array_initi_spec Ψ' with "[HΨ]") as "%data %elems (%Hsz & %Helems & Hmodel & (%slots & %vs & -> & HΨ & Helems))".
    { iSplit.
      - iExists []. iSteps.
      - iIntros "!> %i %slots %Hi1 %Hi2 (%elems & %vs & -> & HΨ & Helems)".
        rewrite length_fmap in Hi2.
        iDestruct (big_sepL2_length with "Helems") as %Helems.
        wp_smart_apply (wp_wand with "(Hfn [%] HΨ)") as "%v HΨ"; first lia.
        wp_apply (dynarray_2_element_spec with "[//]") as (elem) "Helem".
        iExists (elems ++ [elem]), (vs ++ [v]).
        rewrite -fmap_snoc big_sepL2_snoc. iSteps.
    }
    wp_block l as "(Hl_size & Hl_data & _)".
    iDestruct (big_sepL2_length with "Helems") as %Helems'.
    iApply "HΦ".
    rewrite length_fmap in Helems.
    iFrame. iStep. iExists 0. rewrite right_id. iSteps.
  Qed.
  Lemma dynarray_2_initi_spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 ₊sz,
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      dynarray_2_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜sz = length vs⌝ ∗
      dynarray_2_model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (₊sz - i), Ξ j
    )%I).
    wp_apply (dynarray_2_initi_spec Ψ' with "[$HΨ Hfn]"); last iSteps.
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma dynarray_2_initi_spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜sz = length vs⌝ ∗
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_2_initi_spec Ψ'); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma dynarray_2_initi_spec_disentangled' Ψ sz fn :
    {{{
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜sz = length vs⌝ ∗
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_2_initi_spec' Ψ' with "[Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma dynarray_2_size_spec t vs :
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_size t
    {{{
      RET #(length vs);
      dynarray_2_model t vs
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2_capacity_spec t vs :
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_capacity t
    {{{ cap,
      RET #cap;
      ⌜length vs ≤ cap⌝ ∗
      dynarray_2_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. rewrite /dynarray_2_data. wp_load.
    wp_apply (array_size_spec with "Hmodel") as "Hmodel".
    rewrite length_app length_fmap.
    iDestruct (big_sepL2_length with "Helems") as %->.
    iSteps.
  Qed.

  Lemma dynarray_2_is_empty_spec t vs :
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      dynarray_2_model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_size_spec with "Hmodel") as "Hmodel".
    wp_pures.
    destruct vs; iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma dynarray_2_get_spec t vs (i : Z) v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_get t #i
    {{{
      RET v;
      ⌜0 ≤ i < length vs⌝%Z ∗
      dynarray_2_model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hvs_lookup %Φ (:model) HΦ".
    Z_to_nat i. rewrite Nat2Z.id in Hvs_lookup.
    clear Hi. pose proof Hvs_lookup as Hi%lookup_lt_Some.
    iDestruct (big_sepL2_length with "Helems") as "%Helems".
    iDestruct (big_sepL2_lookup_acc_r with "Helems") as "(%elem & %Helems_lookup & (:element_model) & Helems)"; first done.
    wp_rec. rewrite /dynarray_2_data. wp_load.
    wp_smart_apply (array_get_spec with "[$Hmodel]") as "(% & Hmodel)".
    { rewrite Nat2Z.id lookup_app_l.
      { rewrite length_fmap. lia. }
      rewrite list_lookup_fmap_Some. naive_solver.
    }
    wp_match. iSteps.
  Qed.

  Lemma dynarray_2_set_spec t vs (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_set t #i v
    {{{
      RET ();
      ⌜0 ≤ i < length vs⌝%Z ∗
      dynarray_2_model t (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (:model) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    iDestruct (big_sepL2_length with "Helems") as "%Helems".
    opose proof* (lookup_lookup_total vs i) as Hvs_lookup.
    { apply lookup_lt_is_Some_2. lia. }
    iDestruct (big_sepL2_insert_acc_r with "Helems") as "(%elem & %Helems_lookup & (:element_model) & Helems)"; first done.
    wp_rec. rewrite /dynarray_2_data. wp_load.
    wp_smart_apply (array_get_spec with "[$Hmodel]") as "Hmodel".
    { rewrite Nat2Z.id lookup_app_l.
      { rewrite length_fmap. lia. }
      rewrite list_lookup_fmap_Some. naive_solver.
    }
    wp_match. wp_store.
    iDestruct ("Helems" with "[Helem_header Helem_value]") as "Helems"; first iSteps.
    rewrite (list_insert_id elems) //.
    iSteps. rewrite length_insert //.
  Qed.

  #[local] Lemma dynarray_2_next_capacity_spec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      dynarray_2_next_capacity #n
    {{{ m,
      RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    iSteps; iModIntro; wp_apply int_max_spec; iSteps.
  Qed.
  Lemma dynarray_2_reserve_spec t vs (n : Z) :
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_reserve t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z ∗
      dynarray_2_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. rewrite /dynarray_2_data.
    wp_smart_apply assume_spec' as "%Hn".
    wp_load.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_pures.
    case_bool_decide; wp_pures; last iSteps.
    wp_smart_apply (dynarray_2_next_capacity_spec with "[//]") as "%n' %Hn'"; first lia.
    wp_apply int_max_spec.
    wp_smart_apply (array_unsafe_grow_spec with "Hmodel") as (data') "(Hmodel & Hmodel')"; first lia.
    rewrite /dynarray_2_set_data. wp_store.
    rewrite -assoc -replicate_add. iSteps.
  Qed.
  Lemma dynarray_2_reserve_extra_spec t vs (n : Z) :
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_reserve_extra t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z ∗
      dynarray_2_model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hn".
    wp_smart_apply (dynarray_2_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply (dynarray_2_reserve_spec with "Hmodel").
    iSteps.
  Qed.

  #[local] Lemma dynarray_2_try_push_spec t vs elem v :
    {{{
      dynarray_2_model t vs ∗
      element_model elem v
    }}}
      dynarray_2_try_push t #elem
    {{{ b,
      RET #b;
      if b then
        dynarray_2_model t (vs ++ [v])
      else
        dynarray_2_model t vs ∗
        element_model elem v
    }}}.
  Proof.
    iIntros "%Φ ((:model) & Helem) HΦ".
    iDestruct (big_sepL2_length with "Helems") as "%Helems".
    wp_rec. rewrite /dynarray_2_size /dynarray_2_data /dynarray_2_set_size. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_pures.
    case_bool_decide as Htest; wp_pures.
    { iApply "HΦ". iFrameSteps. }
    wp_store.
    wp_smart_apply (array_unsafe_set_spec with "Hmodel") as "Hmodel"; first lia.
    wp_pures.
    iApply "HΦ".
    iExists l, data, (elems ++ [elem]), (extra - 1). iStep.
    rewrite length_app Z.add_1_r -Nat2Z.inj_succ Nat.add_comm /=. iFrame.
    rewrite insert_app_r_alt.
    { rewrite length_fmap. lia. }
    destruct extra.
    - rewrite length_app length_fmap in Htest.
      naive_solver lia.
    - rewrite Nat2Z.id length_fmap Helems Nat.sub_diag.
      rewrite fmap_snoc -assoc /= Nat.sub_0_r.
      iSteps.
  Qed.
  #[local] Lemma dynarray_2_push_aux_spec t vs elem v :
    {{{
      dynarray_2_model t vs ∗
      element_model elem v
    }}}
      dynarray_2_push_aux t #elem
    {{{
      RET ();
      dynarray_2_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Helem) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply (dynarray_2_reserve_extra_spec with "Hmodel") as "(_ & Hmodel)".
    wp_smart_apply (dynarray_2_try_push_spec with "[$Hmodel $Helem]") as ([]) ""; first iSteps. iIntros "(Hmodel & Helem)".
    wp_smart_apply ("HLöb" with "Hmodel Helem HΦ").
  Qed.
  Lemma dynarray_2_push_spec t vs v :
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_push t v
    {{{
      RET ();
      dynarray_2_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_element_spec with "[//]") as (elem) "Helem".
    wp_smart_apply (dynarray_2_try_push_spec with "[$Hmodel $Helem]") as ([]) ""; first iSteps. iIntros "(Hmodel & Helem)".
    wp_smart_apply (dynarray_2_push_aux_spec with "[$Hmodel $Helem]").
    iSteps.
  Qed.

  Lemma dynarray_2_pop_spec {t vs} vs' v :
    vs = vs' ++ [v] →
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_pop t
    {{{
      RET v;
      dynarray_2_model t vs'
    }}}.
  Proof.
    iIntros (->) "%Φ (:model) HΦ".
    wp_rec. rewrite /dynarray_2_size /dynarray_2_data /dynarray_2_set_size. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    do 2 (wp_smart_apply assume_spec' as "_").
    wp_pures.
    rewrite length_app Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    iDestruct (big_sepL2_length with "Helems") as %Helems. rewrite length_app /= in Helems.
    destruct (rev_elim elems) as [-> | (slots & elem & ->)]; first (simpl in Helems; lia).
    rewrite length_app Nat.add_cancel_r in Helems. iEval (rewrite -Helems).
    iDestruct (big_sepL2_snoc with "Helems") as "(Helems & (:element_model))".
    wp_apply (array_unsafe_get_spec with "Hmodel") as "Hmodel"; [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l.
      { rewrite length_fmap length_app /=. lia. }
      rewrite list_lookup_fmap lookup_app_r // Nat.sub_diag //.
    }
    wp_match.
    wp_apply (array_unsafe_set_spec with "Hmodel") as "Hmodel".
    { rewrite length_app length_fmap length_app /=. lia. }

    rewrite fmap_snoc -assoc Nat2Z.id insert_app_r_alt.
    all: rewrite length_fmap //.
    rewrite Nat.sub_diag /=.
    wp_store. wp_load.
    iApply "HΦ".
    iExists l, data, slots, (S extra). iSteps.
  Qed.

  Lemma dynarray_2_fit_capacity_spec t vs :
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_fit_capacity t
    {{{
      RET ();
      dynarray_2_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. rewrite /dynarray_2_size /dynarray_2_data /dynarray_2_set_data. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    iDestruct (big_sepL2_length with "Helems") as %Helems.
    wp_pures.
    case_bool_decide; wp_pures; first iSteps.
    wp_apply (array_shrink_spec with "Hmodel") as "%data' (_ & _ & Hmodel')".
    wp_store.
    iApply "HΦ".
    iExists l, data', elems, 0.
    rewrite take_app_length'.
    { rewrite length_fmap. lia. }
    rewrite right_id. iSteps.
  Qed.

  Lemma dynarray_2_reset_spec t vs :
    {{{
      dynarray_2_model t vs
    }}}
      dynarray_2_reset t
    {{{
      RET ();
      dynarray_2_model t []
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. rewrite /dynarray_2_set_size /dynarray_2_set_data. wp_store.
    wp_smart_apply (array_create_spec with "[//]") as "%data' Hmodel'".
    wp_store.
    iSteps. iExists [], 0. iSteps.
  Qed.

  Lemma dynarray_2_iteri_spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_2_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_2_iteri fn t
    {{{
      RET ();
      dynarray_2_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec. rewrite /dynarray_2_data.
    wp_smart_apply (dynarray_2_size_spec with "Hmodel") as "(:model)".
    wp_load.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply assume_spec' as "%".
    pose Ψ' i slots := (
      Ψ i (take i vs) ∗
      [∗ list] elem; v ∈ elems; vs, element_model elem v
    )%I.
    wp_smart_apply (array_unsafe_iteri_slice_spec Ψ' with "[$HΨ $Helems $Hmodel]"); [lia.. | |].
    { iIntros "!> %i %slots%Hi %Hlookup (HΨ & Helems)".
      iDestruct (big_sepL2_length with "Helems") as "%Helems".
      rewrite lookup_app_l in Hlookup.
      { rewrite length_fmap. lia. }
      apply list_lookup_fmap_Some in Hlookup as (elem & Hlookup & ->).
      iDestruct (big_sepL2_lookup_acc_l with "Helems") as "(%v & % & (:element_model) & Helems)"; first done.
      wp_match. wp_load.
      rewrite slice_0 take_app_le.
      { rewrite length_fmap. lia. }
      wp_apply (wp_wand with "(Hfn [//] HΨ)").
      rewrite -take_S_r //. iSteps.
    }
    iSteps. rewrite Nat2Z.id firstn_all //.
  Qed.
  Lemma dynarray_2_iteri_spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_2_iteri fn t
    {{{
      RET ();
      dynarray_2_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left := (
      Ψ i vs_left ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (dynarray_2_iteri_spec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    iIntros "!> %i %v %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma dynarray_2_iteri_spec_disentangled Ψ fn t vs :
    {{{
      dynarray_2_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2_iteri fn t
    {{{
      RET ();
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_2_iteri_spec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma dynarray_2_iteri_spec_disentangled' Ψ fn t vs :
    {{{
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2_iteri fn t
    {{{
      RET ();
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_2_iteri_spec' Ψ' with "[$Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma dynarray_2_iter_spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_2_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_2_iter fn t
    {{{
      RET ();
      dynarray_2_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_iteri_spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_2_iter_spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_2_iter fn t
    {{{
      RET ();
      dynarray_2_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_iteri_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma dynarray_2_iter_spec_disentangled Ψ fn t vs :
    {{{
      dynarray_2_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2_iter fn t
    {{{
      RET ();
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_iteri_spec_disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_2_iter_spec_disentangled' Ψ fn t vs :
    {{{
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2_iter fn t
    {{{
      RET ();
      dynarray_2_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_iteri_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Context τ `{!iType (iPropI Σ) τ}.

  #[local] Definition itype_element elem : iProp Σ :=
    elem ↦ₕ Header 1 §Element ∗
    inv nroot (
      ∃ v,
      elem.[value] ↦ v ∗
      τ v
    ).

  Lemma element_get_type elem :
    {{{
      itype_element elem
    }}}
      (#elem).{value}
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma element_set_type elem v :
    {{{
      itype_element elem ∗
      τ v
    }}}
      #elem <-{value} v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Definition itype_slot slot : iProp Σ :=
      ⌜slot = §Empty%V⌝
    ∨ ∃ elem,
      ⌜slot = #elem⌝ ∗
      itype_element elem.
  #[local] Instance itype_slot_itype :
    iType _ itype_slot.
  Proof.
    split. apply _.
  Qed.

  #[local] Lemma wp_match_slot slot e1 x e2 Φ :
    itype_slot slot -∗
    ( WP e1 {{ Φ }} ∧
      ∀ elem, itype_element elem -∗ WP subst' x #elem e2 {{ Φ }}
    ) -∗
    WP match: slot with Empty => e1 | Element <> as: x => e2 end {{ Φ }}.
  Proof.
    iIntros "[-> | (%elem & -> & Helem_header & #Hinv)] H".
    - rewrite bi.and_elim_l. iSteps.
    - rewrite bi.and_elim_r. wp_match. iSteps.
  Qed.

  Definition itype_dynarray_2 t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ (sz : nat) cap data,
      l.[size] ↦ #sz ∗
      l.[data] ↦ data ∗ itype_array itype_slot cap data
    ).
  #[global] Instance itype_dynarray_2_itype :
    iType _ itype_dynarray_2.
  Proof.
    split. apply _.
  Qed.

  #[local] Lemma dynarray_2_element_type v :
    {{{
      τ v
    }}}
      dynarray_2_element v
    {{{ slot,
      RET slot;
      itype_slot slot
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2_create_type :
    {{{
      True
    }}}
      dynarray_2_create ()
    {{{ t,
      RET t;
      itype_dynarray_2 t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_type itype_slot with "[//]") as "%data Hdata_type".
    iSteps.
  Qed.

  Lemma dynarray_2_make_type (sz : Z) v :
    {{{
      τ v
    }}}
      dynarray_2_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype_dynarray_2 t
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply (array_init_type itype_slot) as "%data (%Hsz & Hdata_type)"; first iSteps.
    iSteps.
  Qed.

  Lemma dynarray_2_initi_type sz fn :
    {{{
      (itype_nat_upto ₊sz --> τ)%T fn
    }}}
      dynarray_2_initi #sz fn
    {{{ t,
      RET t;
      itype_dynarray_2 t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply array_initi_type; last iSteps. iIntros "!> % (% & -> & %Hi)".
    wp_smart_apply (wp_wand with "(Hfn [])") as (v) "#Hv"; first iSteps.
    wp_apply (dynarray_2_element_type with "[//]").
    iSteps.
  Qed.

  Lemma dynarray_2_size_type t :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_size t
    {{{ (sz : nat),
      RET #sz;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2_capacity_type t :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_size t
    {{{ (cap : nat),
      RET #cap;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma dynarray_2_data_type t :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_data t
    {{{ cap data,
      RET data;
      itype_array itype_slot cap data
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma dynarray_2_set_size_type t sz :
    (0 ≤ sz)%Z →
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_set_size t #sz
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma dynarray_2_set_data_type t cap data :
    {{{
      itype_dynarray_2 t ∗
      itype_array itype_slot cap data
    }}}
      dynarray_2_set_data t data
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2_is_empty_type t :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_is_empty t
    {{{ b,
      RET #b;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2_get_type t (i : Z) :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_get t #i
    {{{ v,
      RET v;
      ⌜0 ≤ i⌝%Z ∗
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_apply (array_get_type with "Hdata_type") as "%slot (%Hi & #Hslot)".
    wp_apply (wp_match_slot with "Hslot").
    iSteps.
  Qed.

  Lemma dynarray_2_set_type t (i : Z) v :
    {{{
      itype_dynarray_2 t ∗
      τ v
    }}}
      dynarray_2_set t #i v
    {{{
      RET ();
      ⌜0 ≤ i⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_apply (array_get_type with "Hdata_type") as "%slot (%Hi & #Hslot)".
    wp_apply (wp_match_slot with "Hslot").
    iSteps.
  Qed.

  Lemma dynarray_2_reserve_type t n :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_reserve t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hn".
    wp_smart_apply (dynarray_2_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type") as "_".
    wp_pures.
    case_bool_decide; wp_pures; last iSteps.
    wp_smart_apply (dynarray_2_next_capacity_spec with "[//]") as "%n' %Hn'"; first lia.
    wp_apply int_max_spec.
    wp_smart_apply (array_unsafe_grow_type itype_slot with "[$Hdata_type]") as (data') "#Hdata_type'"; [lia | iSteps |].
    wp_smart_apply (dynarray_2_set_data_type with "[$Htype $Hdata_type']") as "_".
    iSteps.
  Qed.
  Lemma dynarray_2_reserve_extra_type t n :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_reserve_extra t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hn".
    wp_smart_apply (dynarray_2_size_type with "Htype") as "%sz _".
    wp_smart_apply (dynarray_2_reserve_type with "Htype").
    iSteps.
  Qed.

  #[local] Lemma dynarray_2_try_push_type t slot :
    {{{
      itype_dynarray_2 t ∗
      itype_slot slot
    }}}
      dynarray_2_try_push t slot
    {{{ b,
      RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_size_type with "Htype") as "%sz _".
    wp_smart_apply (dynarray_2_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type") as "_".
    wp_pures.
    case_bool_decide; wp_pures; first iSteps.
    wp_apply (dynarray_2_set_size_type with "Htype") as "_"; first lia.
    wp_smart_apply (array_unsafe_set_type with "[$Hdata_type $Hslot]") as "_"; first lia.
    iSteps.
  Qed.
  #[local] Lemma dynarray_2_push_aux_type t slot :
    {{{
      itype_dynarray_2 t ∗
      itype_slot slot
    }}}
      dynarray_2_push_aux t slot
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply (dynarray_2_reserve_extra_type with "Htype") as "_".
    wp_smart_apply (dynarray_2_try_push_type with "[$Htype $Hslot]") as ([]) "_"; first iSteps.
    wp_smart_apply ("HLöb" with "HΦ").
  Qed.
  Lemma dynarray_2_push_type t v :
    {{{
      itype_dynarray_2 t ∗
      τ v
    }}}
      dynarray_2_push t v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_element_type with "[//]") as (slot) "#Hslot".
    wp_smart_apply (dynarray_2_try_push_type with "[$Htype $Hslot]") as ([]) "_"; first iSteps.
    wp_smart_apply (dynarray_2_push_aux_type with "[$Htype $Hslot]").
    iSteps.
  Qed.

  Lemma dynarray_2_pop_type t :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_pop t
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (dynarray_2_size_type with "Htype") as "%sz _".
    wp_smart_apply (dynarray_2_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type") as "_".
    wp_smart_apply assume_spec' as "%Hcap".
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_get_type with "Hdata_type") as "%slot #Hslot"; first lia.
    wp_apply (wp_match_slot with "Hslot").
    iSplit; first iSteps. iIntros "%elem #Helem /=".
    wp_smart_apply (array_unsafe_set_type with "[$Hdata_type]") as "_"; [lia | iSteps |].
    wp_smart_apply (dynarray_2_set_size_type with "Htype") as "_"; first lia.
    wp_smart_apply (element_get_type with "Helem").
    iSteps.
  Qed.

  Lemma dynarray_2_fit_capacity_type t v :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_fit_capacity t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (dynarray_2_size_type with "Htype") as "%sz _".
    wp_smart_apply (dynarray_2_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type") as "_".
    wp_pures.
    case_decide; wp_pures; first iSteps.
    wp_apply (array_shrink_type with "Hdata_type") as "%t' (_ & #Hdata_type')".
    wp_apply (dynarray_2_set_data_type with "[$Htype $Hdata_type']").
    iSteps.
  Qed.

  Lemma dynarray_2_reset_type t v :
    {{{
      itype_dynarray_2 t
    }}}
      dynarray_2_reset t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (dynarray_2_set_size_type with "Htype") as "_"; first done.
    wp_smart_apply (array_create_type with "[//]") as "%data' #Hdata_type'".
    wp_apply (dynarray_2_set_data_type with "[$Htype $Hdata_type']").
    iSteps.
  Qed.

  Lemma dynarray_2_iteri_type fn t :
    {{{
      itype_dynarray_2 t ∗
      (itype_nat --> τ --> itype_unit)%T fn
    }}}
      dynarray_2_iteri fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_size_type with "Htype") as "%sz _".
    wp_smart_apply (dynarray_2_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type") as "_".
    wp_smart_apply assume_spec' as "%".
    wp_smart_apply (array_unsafe_iteri_slice_type with "[$Hdata_type]"); [lia.. | |].
    { iSteps. iModIntro. wp_match. iSteps. }
    iSteps.
  Qed.

  Lemma dynarray_2_iter_type fn t :
    {{{
      itype_dynarray_2 t ∗
      (τ --> itype_unit)%T fn
    }}}
      dynarray_2_iter fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_2_iteri_type with "[$Htype] HΦ").
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque dynarray_2_create.
#[global] Opaque dynarray_2_make.
#[global] Opaque dynarray_2_initi.
#[global] Opaque dynarray_2_size.
#[global] Opaque dynarray_2_capacity.
#[global] Opaque dynarray_2_is_empty.
#[global] Opaque dynarray_2_get.
#[global] Opaque dynarray_2_set.
#[global] Opaque dynarray_2_reserve.
#[global] Opaque dynarray_2_reserve_extra.
#[global] Opaque dynarray_2_push.
#[global] Opaque dynarray_2_pop.
#[global] Opaque dynarray_2_fit_capacity.
#[global] Opaque dynarray_2_reset.
#[global] Opaque dynarray_2_iteri.
#[global] Opaque dynarray_2_iter.

#[global] Opaque dynarray_2_model.
#[global] Opaque itype_dynarray_2.
