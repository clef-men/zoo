From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  dynarray_1__code.
From zoo_std Require Import
  int
  array
  dynarray_1__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types i : nat.
Implicit Types l : location.
Implicit Types v t fn : val.
Implicit Types vs : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Definition model' l (sz : nat) data vs : iProp Σ :=
    l.[size] ↦ #sz ∗
    l.[data] ↦ data ∗
    array_model data (DfracOwn 1) vs.
  #[local] Instance : CustomIpatFormat "model'" :=
    "(
      Hl_size &
      Hl_data &
      Hmodel
    )".
  Definition dynarray_1_model t vs : iProp Σ :=
    ∃ l data extra,
    ⌜t = #l⌝ ∗
    model' l (length vs) data (vs ++ replicate extra ()%V).
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l &
      %data &
      %extra &
      -> &
      {{lazy}Hmodel=(:model')}
    )".

  #[global] Instance dynarray_1_model_timeless t vs :
    Timeless (dynarray_1_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma dynarray_1_create_spec :
    {{{
      True
    }}}
      dynarray_1_create ()
    {{{ t,
      RET t;
      dynarray_1_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_spec with "[//]") as "%data Hmodel".
    wp_block l as "(Hl_size & Hl_data & _)".
    iApply "HΦ". iExists l, data, 0. iSteps.
  Qed.

  Lemma dynarray_1_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      dynarray_1_make #sz v
    {{{ t,
      RET t;
      dynarray_1_model t (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_rec.
    wp_smart_apply (array_unsafe_make_spec with "[//]") as "%data Hmodel"; first done.
    iSteps.
    - rewrite length_replicate //.
    - iExists 0. rewrite right_id Nat2Z.id. iSteps.
  Qed.

  Lemma dynarray_1_initi_spec Ψ sz fn :
    (0 ≤ sz)%Z →
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
      dynarray_1_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = ₊sz⌝ ∗
      dynarray_1_model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_unsafe_initi_spec Ψ with "[$HΨ]") as "%data %vs (%Hvs & Hmodel & HΨ)"; [done | iSteps |].
    wp_block l as "(Hl_size & Hl_data & _)".
    iSteps. iExists 0. rewrite right_id. iSteps.
  Qed.
  Lemma dynarray_1_initi_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
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
      dynarray_1_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = ₊sz⌝ ∗
      dynarray_1_model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (₊sz - i), Ξ j
    )%I).
    wp_apply (dynarray_1_initi_spec Ψ' with "[$HΨ Hfn]"); [done | | iSteps].
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)").
    iSteps. rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma dynarray_1_initi_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = ₊sz⌝ ∗
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_1_initi_spec Ψ'); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma dynarray_1_initi_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = ₊sz⌝ ∗
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_1_initi_spec' Ψ' with "[Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn").
    iSteps. rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma dynarray_1_size_spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_size t
    {{{
      RET #(length vs);
      dynarray_1_model t vs
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_1_capacity_spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_capacity t
    {{{ cap,
      RET #cap;
      ⌜length vs ≤ cap⌝ ∗
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_apply (array_size_spec with "Hmodel") as "Hmodel".
    rewrite length_app. iSteps.
  Qed.

  Lemma dynarray_1_is_empty_spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (dynarray_1_size_spec with "Hmodel") as "Hmodel".
    wp_pures.
    destruct vs; iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma dynarray_1_get_spec t vs (i : Z) v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_get t #i
    {{{
      RET v;
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_apply (array_unsafe_get_spec with "Hmodel"); [lia | | done |].
    { rewrite lookup_app_l //. eapply lookup_lt_Some. done. }
    iSteps.
  Qed.

  Lemma dynarray_1_set_spec t vs (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_set t #i v
    {{{
      RET ();
      dynarray_1_model t (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_apply (array_unsafe_set_spec with "Hmodel") as "Hmodel".
    { rewrite length_app. lia. }
    iApply "HΦ". iExists l, data, extra.
    rewrite length_insert insert_app_l; first lia. iSteps.
  Qed.

  #[local] Lemma dynarray_1_next_capacity_spec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      dynarray_1_next_capacity #n
    {{{ m,
      RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    iSteps; wp_apply int_max_spec; iSteps.
  Qed.
  #[local] Lemma dynarray_1_reserve_spec' l data vs extra n :
    (0 ≤ n)%Z →
    {{{
      model' l (length vs) data (vs ++ replicate extra ()%V)
    }}}
      dynarray_1_reserve #l #n
    {{{ data' extra',
      RET ();
      ⌜₊n ≤ length vs + extra'⌝ ∗
      model' l (length vs) data' (vs ++ replicate extra' ()%V)
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model') HΦ".
    wp_rec. wp_load.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_pures.
    case_bool_decide as Htest; wp_pures; rewrite length_app length_replicate in Htest.
    - wp_apply (dynarray_1_next_capacity_spec with "[//]") as "%n' %Hn'"; first lia.
      wp_apply int_max_spec.
      wp_smart_apply (array_unsafe_alloc_spec with "[//]") as "%data' Hmodel'"; first lia.
      wp_load.
      wp_smart_apply (array_unsafe_copy_slice_spec with "[$Hmodel $Hmodel']") as "(Hmodel & Hmodel')"; try lia.
      { rewrite length_app. lia. }
      { rewrite length_replicate. lia. }
      wp_store.
      iApply ("HΦ" $! data' (₊(n `max` n') - length vs)).
      iSteps. rewrite Nat2Z.id drop_replicate take_app_length //.
    - iApply ("HΦ" $! data extra).
      iSteps.
  Qed.
  Lemma dynarray_1_reserve_spec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_reserve t #n
    {{{
      RET ();
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model lazy=) HΦ".
    wp_apply (dynarray_1_reserve_spec' with "Hmodel"); first done.
    iSteps.
  Qed.
  #[local] Lemma dynarray_1_reserve_extra_spec' l data vs extra n :
    (0 ≤ n)%Z →
    {{{
      model' l (length vs) data (vs ++ replicate extra ()%V)
    }}}
      dynarray_1_reserve_extra #l #n
    {{{ data' extra',
      RET ();
      ⌜₊n ≤ extra'⌝ ∗
      model' l (length vs) data' (vs ++ replicate extra' ()%V)
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model') HΦ".
    wp_rec. wp_load.
    wp_smart_apply (dynarray_1_reserve_spec' with "[Hl_size Hl_data Hmodel]") as "%data' %extra' (%Hextra' & Hmodel)"; [lia | iSteps |].
    iApply ("HΦ" $! data' extra').
    iSteps.
  Qed.
  Lemma dynarray_1_reserve_extra_spec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_reserve_extra t #n
    {{{
      RET ();
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model lazy=) HΦ".
    wp_apply (dynarray_1_reserve_extra_spec' with "Hmodel"); first done.
    iSteps.
  Qed.

  Lemma dynarray_1_push_spec t vs v :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_push t v
    {{{
      RET ();
      dynarray_1_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (:model lazy=) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_1_reserve_extra_spec' with "Hmodel") as "%data' %extra' (%Hextra' & (Hl_size & Hl_data & Hmodel))"; first lia.
    wp_load. wp_store. wp_load.
    wp_apply (array_unsafe_set_spec with "Hmodel").
    { rewrite length_app length_replicate. lia. }
    rewrite Nat2Z.id insert_app_r_alt // Nat.sub_diag insert_replicate_lt // /= (assoc (++) vs [v] (replicate _ _)).
    iSteps. rewrite length_app. iSteps.
  Qed.

  Lemma dynarray_1_pop_spec {t vs} vs' v :
    vs = vs' ++ [v] →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_pop t
    {{{
      RET v;
      dynarray_1_model t vs'
    }}}.
  Proof.
    iIntros (->) "%Φ (:model) HΦ".
    wp_rec. wp_load. wp_store. wp_load.
    rewrite length_app Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    wp_smart_apply (array_unsafe_get_spec with "Hmodel") as "Hmodel"; [lia | | done |].
    { rewrite lookup_app_l; first (rewrite length_app /=; lia).
      rewrite lookup_app_r; first lia.
      rewrite Nat2Z.id Nat.sub_diag //.
    }
    wp_smart_apply (array_unsafe_set_spec with "Hmodel").
    { rewrite !length_app /=. lia. }
    iSteps. iExists (S extra).
    rewrite -assoc insert_app_r_alt; first lia. rewrite Nat2Z.id Nat.sub_diag //.
  Qed.

  Lemma dynarray_1_fit_capacity_spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_fit_capacity t
    {{{
      RET ();
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_pures. case_bool_decide; wp_pures; first iSteps.
    wp_apply (array_unsafe_shrink_spec with "Hmodel") as "%data' (_ & Hmodel)".
    { rewrite length_app. lia. }
    wp_store.
    iSteps. iExists 0. rewrite Nat2Z.id take_app_length right_id //.
  Qed.

  Lemma dynarray_1_reset_spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_reset t
    {{{
      RET ();
      dynarray_1_model t []
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. wp_store.
    wp_smart_apply (array_create_spec with "[//]") as "%data' Hmodel'".
    wp_store.
    iSteps. iExists 0. iSteps.
  Qed.

  Lemma dynarray_1_iteri_spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1_model t vs ∗
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
      dynarray_1_iteri fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & (:model) & #Hfn) HΦ".
    wp_rec. do 2 wp_load.
    wp_apply (array_unsafe_iteri_slice_spec Ψ with "[$HΨ $Hmodel]").
    { lia. }
    { lia. }
    { rewrite length_app. lia. }
    { iIntros "!> %i %v %Hi %Hlookup HΨ".
      rewrite slice_0 take_app_le; first lia.
      wp_apply (wp_wand with "(Hfn [%] HΨ)").
      { rewrite lookup_app_l // in Hlookup. lia. }
      iSteps.
    }
    rewrite slice_0 Nat2Z.id take_app_length. iSteps.
  Qed.
  Lemma dynarray_1_iteri_spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_1_iteri fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left := (
      Ψ i vs_left ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (dynarray_1_iteri_spec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    iIntros "!> %i %v %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma dynarray_1_iteri_spec_disentangled Ψ fn t vs :
    {{{
      dynarray_1_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1_iteri fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_1_iteri_spec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma dynarray_1_iteri_spec_disentangled' Ψ fn t vs :
    {{{
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1_iteri fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_1_iteri_spec' Ψ' with "[$Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma dynarray_1_iter_spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1_model t vs ∗
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
      dynarray_1_iter fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_1_iteri_spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_1_iter_spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_1_iter fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_1_iteri_spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma dynarray_1_iter_spec_disentangled Ψ fn t vs :
    {{{
      dynarray_1_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1_iter fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_1_iteri_spec_disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_1_iter_spec_disentangled' Ψ fn t vs :
    {{{
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1_iter fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_1_iteri_spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque dynarray_1_create.
#[global] Opaque dynarray_1_make.
#[global] Opaque dynarray_1_initi.
#[global] Opaque dynarray_1_size.
#[global] Opaque dynarray_1_capacity.
#[global] Opaque dynarray_1_is_empty.
#[global] Opaque dynarray_1_get.
#[global] Opaque dynarray_1_set.
#[global] Opaque dynarray_1_reserve.
#[global] Opaque dynarray_1_reserve_extra.
#[global] Opaque dynarray_1_push.
#[global] Opaque dynarray_1_pop.
#[global] Opaque dynarray_1_fit_capacity.
#[global] Opaque dynarray_1_reset.
#[global] Opaque dynarray_1_iteri.
#[global] Opaque dynarray_1_iter.

#[global] Opaque dynarray_1_model.
