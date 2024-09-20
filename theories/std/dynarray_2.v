From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base
  dynarray_2__code.
From zoo.std Require Import
  diverge
  assume
  int
  ref_
  option
  array
  dynarray_2__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types i : nat.
Implicit Types l r : location.
Implicit Types v t fn : val.
Implicit Types vs : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Definition slot_model slot v : iProp Σ :=
    ∃ r,
    ⌜slot = ‘Some( #r )%V⌝ ∗
    r ↦ᵣ v.
  Definition dynarray_2_model t vs : iProp Σ :=
    ∃ l data slots extra,
    ⌜t = #l⌝ ∗
    l.[size] ↦ #(length vs) ∗
    l.[data] ↦ data ∗ array_model data (DfracOwn 1) (slots ++ replicate extra §None%V) ∗
    [∗ list] slot; v ∈ slots; vs, slot_model slot v.

  #[global] Instance dynarray_2_model_timeless t vs :
    Timeless (dynarray_2_model t vs).
  Proof.
    apply _.
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
    wp_apply (array_create_spec with "[//]") as "%data Hdata_model".
    wp_block l as "(Hsz & Hdata & _)".
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
      dynarray_2_model t (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply (array_init_spec_disentangled (λ _ slot, slot_model slot v)) as "%data %slots (%Hsz & %Hslots & Hdata_model & Hslots)".
    { iStep 5. iModIntro. wp_ref r as "Hr". iSteps. }
    iSteps.
    - rewrite length_replicate. iSteps.
    - iExists slots, 0. rewrite right_id. iSteps.
      iApply (big_sepL2_replicate_r_2 _ _ (λ _, slot_model) with "Hslots"); first lia.
  Qed.

  Lemma dynarray_2_initi_spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
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
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    pose Ψ' i slots := (
      ∃ vs,
      Ψ i vs ∗
      [∗ list] slot; v ∈ slots; vs, slot_model slot v
    )%I.
    wp_smart_apply (array_initi_spec Ψ' with "[HΨ]") as "%data %slots (%Hsz & %Hslots & Hdata_model & (%vs & HΨ & Hslots))".
    { iStep. iIntros "!> %i %slots %Hi1 %Hi2 (%vs & HΨ & Hslots)".
      iDestruct (big_sepL2_length with "Hslots") as %Hslots.
      wp_smart_apply (wp_wand with "(Hfn [] HΨ)") as "%v HΨ"; first iSteps.
      wp_ref r as "Hr". wp_pures.
      iExists (vs ++ [v]). iFrame. iSteps.
    }
    wp_block l as "(Hsz & Hdata & _)".
    iDestruct (big_sepL2_length with "Hslots") as %Hslots'.
    iApply "HΦ".
    iFrame. iStep. iExists 0. rewrite right_id. iSteps.
  Qed.
  Lemma dynarray_2_initi_spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
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
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (Z.to_nat sz - i), Ξ j
    )%I).
    wp_apply (dynarray_2_initi_spec Ψ' with "[$HΨ Hfn]"); last iSteps.
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (Z.to_nat sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma dynarray_2_initi_spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
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
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
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
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hmodel & Hslots) HΦ".
    wp_rec. rewrite /dynarray_2_data. wp_load.
    wp_apply (array_size_spec with "Hmodel") as "Hmodel".
    rewrite length_app. iDestruct (big_sepL2_length with "Hslots") as %->.
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
    vs !! Z.to_nat i = Some v →
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
    iIntros "%Hi %Hvs_lookup %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    Z_to_nat i. rewrite Nat2Z.id in Hvs_lookup.
    clear Hi. pose proof Hvs_lookup as Hi%lookup_lt_Some.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    destruct (lookup_lt_is_Some_2 slots i) as (slot & Hslots_lookup); first lia.
    iDestruct (big_sepL2_lookup_acc with "Hslots") as "((%r & %Hr & Hr) & Hslots)"; [done.. | subst slot].
    wp_rec. rewrite /dynarray_2_data. wp_load.
    wp_smart_apply (array_get_spec with "[$Hdata_model]").
    { rewrite Nat2Z.id lookup_app_l //. lia. }
    iSteps.
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
      dynarray_2_model t (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    opose proof* (lookup_lookup_total vs i) as Hvs_lookup.
    { apply lookup_lt_is_Some_2. lia. }
    destruct (lookup_lt_is_Some_2 slots i) as (slot & Hslots_lookup); first lia.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "((%r & %Hr & Hr) & Hslots)"; [done.. | subst slot].
    wp_rec. rewrite /dynarray_2_data. wp_load.
    wp_smart_apply (array_get_spec with "[$Hdata_model]") as "Hdata_model".
    { rewrite Nat2Z.id lookup_app_l //. lia. }
    wp_store.
    iDestruct ("Hslots" with "[Hr]") as "Hslots"; first iSteps.
    rewrite (list_insert_id slots) //.
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
    Ltac Zify.zify_post_hook ::= Z.quot_rem_to_equations.
    iSteps; wp_apply maximum_spec; iSteps.
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
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /dynarray_2_data.
    wp_smart_apply assume_spec' as "%Hn".
    wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    wp_pures.
    case_bool_decide; wp_pures; last iSteps.
    wp_smart_apply (dynarray_2_next_capacity_spec with "[//]") as "%n' %Hn'"; first lia.
    wp_apply maximum_spec.
    wp_smart_apply (array_unsafe_make_spec with "[//]") as "%data' Hdata_model'"; first lia.
    rewrite /dynarray_2_size. wp_load.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    wp_smart_apply (array_copy_slice_spec with "[$Hdata_model $Hdata_model']") as "(_ & _ & _ & _ & _ & Hdata_model & Hdata_model')".
    rewrite /dynarray_2_set_data. wp_store.
    iApply "HΦ".
    iStep. iExists l, data', slots, _.
    rewrite !Nat2Z.id drop_replicate take_app_length' //. iSteps.
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

  #[local] Lemma dynarray_2_try_push_spec t vs slot v :
    {{{
      dynarray_2_model t vs ∗
      slot_model slot v
    }}}
      dynarray_2_try_push t slot
    {{{ b,
      RET #b;
      if b then
        dynarray_2_model t (vs ++ [v])
      else
        dynarray_2_model t vs ∗
        slot_model slot v
    }}}.
  Proof.
    iIntros "%Φ ((%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) & Hslot) HΦ".
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    wp_rec. rewrite /dynarray_2_size /dynarray_2_data /dynarray_2_set_size. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    wp_pures.
    case_bool_decide as Htest; wp_pures.
    { iApply "HΦ". iFrame. iSteps. }
    wp_store.
    wp_smart_apply (array_unsafe_set_spec with "Hdata_model") as "Hdata_model"; first lia.
    wp_pures.
    iApply "HΦ".
    iExists l, data, (slots ++ [slot]), (extra - 1). iStep.
    rewrite length_app Z.add_1_r -Nat2Z.inj_succ Nat.add_comm /=. iFrame.
    rewrite Nat2Z.id -Hslots -(Nat.add_0_r (length slots)) insert_app_r.
    destruct extra.
    - rewrite length_app in Htest. naive_solver lia.
    - rewrite -(assoc (++)) /= Nat.sub_0_r. iSteps.
  Qed.
  #[local] Lemma dynarray_2_push_aux_spec t vs slot v :
    {{{
      dynarray_2_model t vs ∗
      slot_model slot v
    }}}
      dynarray_2_push_aux t slot
    {{{
      RET ();
      dynarray_2_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hslot) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply (dynarray_2_reserve_extra_spec with "Hmodel") as "(_ & Hmodel)".
    wp_smart_apply (dynarray_2_try_push_spec with "[$Hmodel $Hslot]") as ([]) ""; first iSteps. iIntros "(Hmodel & Hslot)".
    wp_smart_apply ("HLöb" with "Hmodel Hslot HΦ").
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
    wp_rec. wp_ref r as "Hr".
    wp_smart_apply (dynarray_2_try_push_spec with "[$Hmodel Hr]") as ([]) ""; [iSteps.. |]. iIntros "(Hmodel & Hslot)".
    wp_smart_apply (dynarray_2_push_aux_spec with "[$Hmodel $Hslot]").
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
    iIntros (->) "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /dynarray_2_size /dynarray_2_data /dynarray_2_set_size. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    do 2 (wp_smart_apply assume_spec' as "_").
    wp_pures.
    rewrite length_app Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    iDestruct (big_sepL2_length with "Hslots") as %Hslots. rewrite length_app /= in Hslots.
    destruct (rev_elim slots) as [-> | (slots_ & slot & ->)]; first (simpl in Hslots; lia).
    rewrite length_app Nat.add_cancel_r in Hslots. iEval (rewrite -Hslots).
    iDestruct (big_sepL2_snoc with "Hslots") as "(Hslots & (%r & -> & Hr))".
    wp_apply (array_unsafe_get_spec with "Hdata_model") as "Hdata_model"; [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l; first (rewrite length_app /=; lia).
      rewrite lookup_app_r // Nat.sub_diag //.
    }
    wp_smart_apply (array_unsafe_set_spec with "Hdata_model") as "Hdata_model".
    { rewrite !length_app /=. lia. }
    rewrite -assoc Nat2Z.id insert_app_r_alt // Nat.sub_diag /=.
    wp_store. wp_load.
    iApply "HΦ".
    iExists l, data, slots_, (S extra). iSteps.
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
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /dynarray_2_size /dynarray_2_data /dynarray_2_set_data. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    iDestruct (big_sepL2_length with "Hslots") as %Hslots.
    wp_pures.
    case_bool_decide; wp_pures; first iSteps.
    wp_apply (array_shrink_spec with "Hdata_model") as "%data' (_ & Hdata_model')".
    wp_store.
    iApply "HΦ".
    iExists l, data', slots, 0.
    rewrite -Hslots Nat2Z.id take_app_length right_id. iSteps.
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
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & _ & _) HΦ".
    wp_rec. rewrite /dynarray_2_set_size /dynarray_2_set_data. wp_store.
    wp_smart_apply (array_create_spec with "[//]") as "%data' Hdata_model'".
    wp_store.
    iSteps. iExists [], 0. iSteps.
  Qed.

  Context τ `{!iType (iPropI Σ) τ}.

  #[local] Definition itype_slot :=
    itype_option (itype_ref τ).
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
    wp_smart_apply (array_init_type itype_slot) as "%data (%Hsz & Hdata_type)".
    { iStep 5. iModIntro. wp_ref r. iSteps. }
    iSteps.
  Qed.

  Lemma dynarray_2_initi_type sz fn :
    {{{
      (itype_nat_upto (Z.to_nat sz) --> τ)%T fn
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
    wp_ref slot as "Hslot".
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
    wp_apply (wp_match_option with "Hslot"). iSplit.
    - wp_apply diverge_spec.
    - iIntros "%r #Hr /=".
      wp_apply (ref_get_type with "Hr").
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
    wp_apply (wp_match_option with "Hslot"). iSplit.
    - wp_apply diverge_spec.
    - iIntros "%r #Hr /=".
      wp_apply (ref_set_type with "[$Hr $Hv]").
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
    wp_apply maximum_spec.
    wp_smart_apply (array_unsafe_make_type itype_slot) as "%data' (_ & #Hdata_type')"; [lia | iSteps |].
    wp_smart_apply dynarray_2_size_type as "%sz _"; first iSmash+.
    wp_smart_apply (array_copy_slice_type itype_slot) as "_"; first iSteps.
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
    wp_rec. wp_ref r as "Hr".
    iAssert (|={⊤}=> itype_slot ‘Some( #r ))%I with "[Hr]" as ">#Hslot"; first iSteps.
    wp_smart_apply (dynarray_2_try_push_type with "[$Htype $Hslot]") as ([]) "_"; first iSteps.
    wp_smart_apply (dynarray_2_push_aux_type with "[$Htype $Hslot]") as "_".
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
    wp_apply (wp_match_option with "Hslot"). iSplit.
    - wp_apply diverge_spec.
    - iIntros "%r #Hr /=".
      wp_smart_apply (array_unsafe_set_type with "[$Hdata_type]") as "_"; [lia | iSteps |].
      wp_smart_apply (dynarray_2_set_size_type with "Htype") as "_"; first lia.
      wp_smart_apply (ref_get_type with "Hr").
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

#[global] Opaque dynarray_2_model.
#[global] Opaque itype_dynarray_2.
