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

  #[local] Definition model' t vs extra : iProp Σ :=
    ∃ l data,
    ⌜t = #l⌝ ∗
    l.[size] ↦ #(length vs) ∗
    l.[data] ↦ data ∗
    array_model data (DfracOwn 1) (vs ++ replicate extra ()%V).
  #[local] Instance : CustomIpatFormat "model'" :=
    "(
      %l{} &
      %data{} &
      -> &
      Hl{}_size &
      Hl{}_data &
      Hmodel
    )".
  Definition dynarray_1_model t vs : iProp Σ :=
    ∃ extra,
    model' t vs extra.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %extra &
      {{lazy}Hmodel;(:model')}
    )".

  #[global] Instance dynarray_1_model_timeless t vs :
    Timeless (dynarray_1_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma dynarray_1_create_spec' :
    {{{
      True
    }}}
      dynarray_1_create ()
    {{{ l,
      RET #l;
      dynarray_1_model #l [] ∗
      meta_token l (↑nroot.@"user")
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_spec with "[//]") as "%data Hmodel".
    wp_block l as "Hl_meta" "(Hl_size & Hl_data & _)".
    iDestruct (meta_token_difference (↑nroot.@"user") with "Hl_meta") as "(Hl_meta & _)"; first done.
    iStepFrameSteps. iExists 0. iSteps.
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
    wp_apply (dynarray_1_create_spec' with "[//]").
    iStepFrameSteps 3.
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
    iStepFrameSteps 7.
    - simpl_length.
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
    iStepFrameSteps. iExists 0. rewrite right_id. iSteps.
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
    wp_apply (dynarray_1_initi_spec Ψ' with "[$HΨ Hfn]"); first done.
    { rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
      destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
      rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
      wp_apply (wp_wand with "(Hfn [//] HΨ)").
      iSteps. rewrite Nat.sub_succ_r Hk //.
    }
    iStepFrameSteps 5.
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
    wp_apply (dynarray_1_initi_spec Ψ' with "[] HΦ"); first done.
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
    wp_apply (dynarray_1_initi_spec' Ψ' with "[Hfn] HΦ"); first done.
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
    iStepFrameSteps 11.
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
    simpl_length. iStepFrameSteps 2.
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
    iStepFrameSteps 2.
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
    { simpl_length. lia. }
    iApply "HΦ".
    iExists extra. iStep.
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
  #[local] Lemma dynarray_1_reserve_spec' t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_reserve t #n
    {{{ extra,
      RET ();
      ⌜₊n ≤ length vs + extra⌝ ∗
      model' t vs extra
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_smart_apply (array_size_spec with "Hmodel") as "Hmodel".
    wp_pures.
    case_bool_decide as Htest.
    all: wp_pures.
    all: simpl_length in Htest.
    - wp_apply (dynarray_1_next_capacity_spec with "[//]") as "%n' %Hn'"; first lia.
      wp_apply int_max_spec.
      wp_smart_apply (array_unsafe_alloc_spec with "[//]") as "%data' Hmodel'"; first lia.
      wp_load.
      wp_smart_apply (array_unsafe_copy_slice_spec with "[$Hmodel $Hmodel']") as "(Hmodel & Hmodel')"; try lia.
      { simpl_length. lia. }
      { simpl_length. lia. }
      wp_store.
      iApply ("HΦ" $! (₊(n `max` n') - length vs)).
      rewrite Nat2Z.id with_slice_0 drop_replicate take_app_length.
      iSteps.
    - iApply ("HΦ" $! extra).
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
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_apply (dynarray_1_reserve_spec' with "Hmodel"); first done.
    iStepFrameSteps 3.
  Qed.

  #[local] Lemma dynarray_1_reserve_extra_spec' t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_reserve_extra t #n
    {{{ extra,
      RET ();
      ⌜₊n ≤ extra⌝ ∗
      model' t vs extra
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_smart_apply (dynarray_1_reserve_spec' with "[Hl_size Hl_data Hmodel]") as "%extra' (%Hextra' & Hmodel)"; [lia | iFrameSteps |].
    iApply ("HΦ" $! extra').
    iFrameSteps.
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
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_apply (dynarray_1_reserve_extra_spec' with "Hmodel"); first done.
    iStepFrameSteps 3.
  Qed.

  Lemma dynarray_1_grow_spec t vs sz v :
    (0 ≤ sz)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1_grow t #sz v
    {{{
      RET ();
      dynarray_1_model t (vs ++ replicate (₊sz - length vs) v)
    }}}.
  Proof.
    iIntros "% %Φ (:model) HΦ".
    wp_rec. wp_load. wp_pures.
    case_bool_decide.
    - wp_smart_apply (dynarray_1_reserve_spec' with "[$Hl_size $Hl_data $Hmodel //]") as "%extra' (%Hextra' & (:model' ='))"; first lia.
      wp_load.
      wp_smart_apply (array_unsafe_fill_slice_spec with "Hmodel") as "Hmodel".
      { lia. }
      { simpl_length. lia. }
      iStepFrameSteps 8.
      { iPureIntro.
        simpl_length.
        rewrite -Nat.le_add_sub; first lia.
        rewrite Z2Nat.id //.
      } {
        rewrite Z2Nat.inj_sub; first lia.
        rewrite Nat2Z.id with_slice_app_length drop_replicate assoc.
        iSteps.
      }
    - assert (₊sz - length vs = 0) as -> by lia. rewrite right_id.
      iStepFrameSteps 5.
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
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (dynarray_1_reserve_extra_spec' with "Hmodel") as "%extra (%Hextra & (:model'))"; first lia.
    wp_load. wp_store. wp_load.
    wp_apply (array_unsafe_set_spec with "Hmodel").
    { simpl_length. lia. }
    rewrite Nat2Z.id insert_app_r_alt // Nat.sub_diag insert_replicate_lt // /= (assoc (++) vs [v] (replicate _ _)).
    iStepFrameSteps 2. simpl_length. iSteps.
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
    simpl_length. rewrite Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    wp_smart_apply (array_unsafe_get_spec with "Hmodel") as "Hmodel"; [lia | | done |].
    { rewrite lookup_app_l; first (simpl_length/=; lia).
      rewrite lookup_app_r; first lia.
      rewrite Nat2Z.id Nat.sub_diag //.
    }
    wp_smart_apply (array_unsafe_set_spec with "Hmodel").
    { simpl_length/=. lia. }
    iStepFrameSteps 6. iExists (S extra).
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
    wp_pures. case_bool_decide; wp_pures.
    - iStepFrameSteps.
    - wp_apply (array_unsafe_shrink_spec with "Hmodel") as "%data' (_ & Hmodel)".
      { simpl_length. lia. }
      wp_store.
      iStepFrameSteps. iExists 0. rewrite Nat2Z.id take_app_length right_id //.
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
    iStepFrameSteps. iExists 0. iSteps.
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
    { simpl_length. lia. }
    { iIntros "!> %i %v %Hi %Hlookup HΨ".
      rewrite slice_0 take_app_le; first lia.
      wp_apply (wp_wand with "(Hfn [%] HΨ)").
      { rewrite lookup_app_l // in Hlookup. lia. }
      iSteps.
    }
    rewrite slice_0 Nat2Z.id take_app_length. iStepFrameSteps 2.
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
    wp_apply (dynarray_1_iteri_spec Ψ' with "[$HΨ $Hmodel $Hfn]").
    { iIntros "!> %i %v %Hlookup (HΨ & HΞ)".
      erewrite drop_S => //.
      iDestruct "HΞ" as "(Hfn & HΞ)".
      rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
    }
    iStepFrameSteps 2.
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
    wp_apply (dynarray_1_iteri_spec Ψ' with "[$Hmodel]").
    { rewrite /Ψ'. iSteps.
      rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
      eapply Nat.lt_le_incl, lookup_lt_Some. done.
    }
    iStepFrameSteps 2.
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
    wp_apply (dynarray_1_iteri_spec' Ψ' with "[$Hmodel Hfn]").
    { rewrite /Ψ'. iSteps.
      iApply (big_sepL_impl with "Hfn"). iSteps.
      rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
      eapply Nat.lt_le_incl, lookup_lt_Some. done.
    }
    iStepFrameSteps 2.
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

From zoo_std Require
  dynarray_1__opaque.

#[global] Opaque dynarray_1_model.
