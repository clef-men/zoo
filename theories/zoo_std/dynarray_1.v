Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Import zoo.diaframe.
Require Export zoo_std.base.
Require Export zoo_std.dynarray_1__code.
Require Import zoo_std.array.
Require Import zoo_std.dynarray_1__types.
Require Import zoo_std.int.
Require Import zoo.options.

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
  #[local] Instance : CustomIpat "model'" :=
    " ( %l{}
      & %data{}
      & ->
      & Hl{}_size
      & Hl{}_data
      & Hmodel
      )
    ".
  Definition dynarray_1_model t vs : iProp Σ :=
    ∃ extra,
    model' t vs extra.
  #[local] Instance : CustomIpat "model" :=
    " ( %extra
      & {{lazy}Hmodel;(:model')}
      )
    ".

  #[global] Instance dynarray_1_model_timeless t vs :
    Timeless (dynarray_1_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma dynarray_1٠create𑁒spec' :
    {{{
      True
    }}}
      dynarray_1٠create ()
    {{{
      l
    , RET #l;
      dynarray_1_model #l [] ∗
      meta_token l (↑nroot.@"user")
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array٠create𑁒spec with "[//]") as "%data Hmodel".
    wp_block l as "Hl_meta" "(Hl_size & Hl_data & _)".
    iDestruct (meta_token_difference (↑nroot.@"user") with "Hl_meta") as "(Hl_meta & _)"; first done.
    iSteps. iExists 0. iSteps.
  Qed.
  Lemma dynarray_1٠create𑁒spec :
    {{{
      True
    }}}
      dynarray_1٠create ()
    {{{
      t
    , RET t;
      dynarray_1_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (dynarray_1٠create𑁒spec' with "[//]").
    iSteps.
  Qed.

  Lemma dynarray_1٠make𑁒spec sz v :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      dynarray_1٠make #sz v
    {{{
      t
    , RET t;
      dynarray_1_model t (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_rec.
    wp_apply+ (array٠unsafe_make𑁒spec with "[//]") as "%data Hmodel"; first done.
    iSteps.
    - simpl_length.
    - iExists 0. rewrite right_id Nat2Z.id. iSteps.
  Qed.

  Lemma dynarray_1٠initi𑁒spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < ₊sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ ˖i (vs ++ [v])
        }}
      )
    }}}
      dynarray_1٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      dynarray_1_model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".

    wp_rec.
    wp_apply+ (array٠unsafe_initi𑁒spec (λ _, Ψ) with "[$HΨ]") as "%data %vs (%Hvs & Hmodel & HΨ)"; [done | iSteps |].
    wp_block l as "(Hl_size & Hl_data & _)".
    iSteps. iExists 0. rewrite right_id. iSteps.
  Qed.
  Lemma dynarray_1٠initi𑁒spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 ₊sz,
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ ˖i (vs ++ [v])
        }}
      )
    }}}
      dynarray_1٠initi #sz fn
    {{{
      t vs
    , RET t;
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
    wp_apply (dynarray_1٠initi𑁒spec Ψ' with "[$HΨ Hfn]"); first done.
    { rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
      destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
      rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
      wp_apply (wp_wand with "(Hfn [//] HΨ)").
      iSteps. rewrite Nat.sub_succ_r Hk //.
    }
    iSteps.
  Qed.
  Lemma dynarray_1٠initi𑁒spec_disentangled Ψ sz fn :
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
      dynarray_1٠initi #sz fn
    {{{
      t vs
    , RET t;
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
    wp_apply (dynarray_1٠initi𑁒spec Ψ' with "[] HΦ"); first done.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma dynarray_1٠initi𑁒spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1٠initi #sz fn
    {{{
      t vs
    , RET t;
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
    wp_apply (dynarray_1٠initi𑁒spec' Ψ' with "[Hfn] HΦ"); first done.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn").
    iSteps. rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma dynarray_1٠size𑁒spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠size t
    {{{
      RET #(length vs);
      dynarray_1_model t vs
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_1٠capacity𑁒spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠capacity t
    {{{
      cap
    , RET #cap;
      ⌜length vs ≤ cap⌝ ∗
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_apply (array٠size𑁒spec with "Hmodel") as "Hmodel".
    simpl_length. iSteps.
  Qed.

  Lemma dynarray_1٠is_empty𑁒spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply+ (dynarray_1٠size𑁒spec with "Hmodel") as "Hmodel".
    wp_pures.
    destruct vs; iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma dynarray_1٠get𑁒spec t vs (i : Z) v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠get t #i
    {{{
      RET v;
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_apply (array٠unsafe_get𑁒spec with "Hmodel"); [lia | | done |].
    { rewrite lookup_app_l //. eapply lookup_lt_Some. done. }
    iSteps.
  Qed.

  Lemma dynarray_1٠set𑁒spec t vs (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠set t #i v
    {{{
      RET ();
      dynarray_1_model t (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_apply (array٠unsafe_set𑁒spec with "Hmodel") as "Hmodel".
    { simpl_length. lia. }
    iApply "HΦ".
    iExists extra. iStep.
    rewrite length_insert insert_app_l; first lia. iSteps.
  Qed.

  #[local] Lemma dynarray_1٠next_capacity𑁒spec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      dynarray_1٠next_capacity #n
    {{{
      m
    , RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma dynarray_1٠reserve𑁒spec' t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠reserve t #n
    {{{
      extra
    , RET ();
      ⌜₊n ≤ length vs + extra⌝ ∗
      model' t vs extra
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp_pures.
    case_bool_decide as Htest.
    all: wp_pures.
    all: simpl_length in Htest.
    - wp_apply (dynarray_1٠next_capacity𑁒spec with "[//]") as "%n' %Hn'"; first lia.
      wp_apply int٠max𑁒spec.
      wp_apply+ (array٠unsafe_alloc𑁒spec with "[//]") as "%data' Hmodel'"; first lia.
      wp_load.
      wp_apply+ (array٠unsafe_copy_slice𑁒spec with "[$Hmodel $Hmodel']") as "(Hmodel & Hmodel')"; try lia.
      { simpl_length. lia. }
      { simpl_length. lia. }
      wp_store.
      iApply ("HΦ" $! (₊(n `max` n') - length vs)).
      rewrite Nat2Z.id with_slice_0 drop_replicate take_app_length.
      iSteps.
    - iApply ("HΦ" $! extra).
      iSteps.
  Qed.
  Lemma dynarray_1٠reserve𑁒spec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠reserve t #n
    {{{
      RET ();
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_apply (dynarray_1٠reserve𑁒spec' with "Hmodel"); first done.
    iSteps.
  Qed.

  #[local] Lemma dynarray_1٠reserve_extra𑁒spec' t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠reserve_extra t #n
    {{{
      extra
    , RET ();
      ⌜₊n ≤ extra⌝ ∗
      model' t vs extra
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model) HΦ".
    wp_rec. wp_load.
    wp_apply+ (dynarray_1٠reserve𑁒spec' with "[Hl_size Hl_data Hmodel]") as "%extra' (%Hextra' & Hmodel)"; [lia | iFrameSteps |].
    iApply ("HΦ" $! extra').
    iFrameSteps.
  Qed.
  Lemma dynarray_1٠reserve_extra𑁒spec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠reserve_extra t #n
    {{{
      RET ();
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_apply (dynarray_1٠reserve_extra𑁒spec' with "Hmodel"); first done.
    iSteps.
  Qed.

  Lemma dynarray_1٠grow𑁒spec t vs sz v :
    (0 ≤ sz)%Z →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠grow t #sz v
    {{{
      RET ();
      dynarray_1_model t (vs ++ replicate (₊sz - length vs) v)
    }}}.
  Proof.
    iIntros "% %Φ (:model) HΦ".
    wp_rec. wp_load. wp_pures.
    case_bool_decide.
    - wp_apply+ (dynarray_1٠reserve𑁒spec' with "[$Hl_size $Hl_data $Hmodel //]") as "%extra' (%Hextra' & (:model' ='))"; first lia.
      wp_load.
      wp_apply+ (array٠unsafe_fill_slice𑁒spec with "Hmodel") as "Hmodel".
      { lia. }
      { simpl_length. lia. }
      iSteps.
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
      iSteps.
  Qed.

  Lemma dynarray_1٠push𑁒spec t vs v :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠push t v
    {{{
      RET ();
      dynarray_1_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply+ (dynarray_1٠reserve_extra𑁒spec' with "Hmodel") as "%extra (%Hextra & (:model'))"; first lia.
    wp_load. wp_store. wp_load.
    wp_apply (array٠unsafe_set𑁒spec with "Hmodel").
    { simpl_length. lia. }
    rewrite Nat2Z.id insert_app_r_alt // Nat.sub_diag insert_replicate_lt // /= (assoc (++) vs [v] (replicate _ _)).
    iSteps. simpl_length. iSteps.
  Qed.

  Lemma dynarray_1٠pop𑁒spec {t vs} vs' v :
    vs = vs' ++ [v] →
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠pop t
    {{{
      RET v;
      dynarray_1_model t vs'
    }}}.
  Proof.
    iIntros (->) "%Φ (:model) HΦ".
    wp_rec. wp_load. wp_store. wp_load.
    simpl_length. rewrite Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    wp_apply+ (array٠unsafe_get𑁒spec with "Hmodel") as "Hmodel"; [lia | | done |].
    { rewrite lookup_app_l; first (simpl_length/=; lia).
      rewrite lookup_app_r; first lia.
      rewrite Nat2Z.id Nat.sub_diag //.
    }
    wp_apply+ (array٠unsafe_set𑁒spec with "Hmodel").
    { simpl_length/=. lia. }
    iSteps. iExists ˖extra.
    rewrite -assoc insert_app_r_alt; first lia. rewrite Nat2Z.id Nat.sub_diag //.
  Qed.

  Lemma dynarray_1٠fit_capacity𑁒spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠fit_capacity t
    {{{
      RET ();
      dynarray_1_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. do 2 wp_load.
    wp_apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp_pures.
    case_bool_decide; wp_pures; first iSteps.
    wp_apply (array٠unsafe_shrink𑁒spec with "Hmodel") as "%data' (_ & Hmodel)".
    { simpl_length. lia. }
    wp_store.
    iSteps. iExists 0. rewrite Nat2Z.id take_app_length right_id //.
  Qed.

  Lemma dynarray_1٠reset𑁒spec t vs :
    {{{
      dynarray_1_model t vs
    }}}
      dynarray_1٠reset t
    {{{
      RET ();
      dynarray_1_model t []
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. wp_store.
    wp_apply+ (array٠create𑁒spec with "[//]") as "%data' Hmodel'".
    wp_store.
    iSteps. iExists 0. iSteps.
  Qed.

  Lemma dynarray_1٠iteri𑁒spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_1٠iteri fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & (:model) & #Hfn) HΦ".
    wp_rec. do 2 wp_load.
    wp_apply (array٠unsafe_iteri_slice𑁒spec Ψ with "[$HΨ $Hmodel]").
    { lia. }
    { lia. }
    { simpl_length. lia. }
    { iIntros "!> %i %v %Hi %Hlookup HΨ".
      rewrite slice_0 take_app_le; first lia.
      wp_apply (wp_wand with "(Hfn [%] HΨ)").
      { rewrite lookup_app_l // in Hlookup. lia. }
      iSteps.
    }
    rewrite slice_0 Nat2Z.id take_app_length. iSteps.
  Qed.
  Lemma dynarray_1٠iteri𑁒spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_1٠iteri fn t
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
    wp_apply (dynarray_1٠iteri𑁒spec Ψ' with "[$HΨ $Hmodel $Hfn]").
    { iIntros "!> %i %v %Hlookup (HΨ & HΞ)".
      erewrite drop_S => //.
      iDestruct "HΞ" as "(Hfn & HΞ)".
      rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
    }
    iSteps.
  Qed.
  Lemma dynarray_1٠iteri𑁒spec_disentangled Ψ fn t vs :
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
      dynarray_1٠iteri fn t
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
    wp_apply (dynarray_1٠iteri𑁒spec Ψ' with "[$Hmodel]").
    { rewrite /Ψ'. iSteps.
      rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
      eapply Nat.lt_le_incl, lookup_lt_Some. done.
    }
    iSteps.
  Qed.
  Lemma dynarray_1٠iteri𑁒spec_disentangled' Ψ fn t vs :
    {{{
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1٠iteri fn t
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
    wp_apply (dynarray_1٠iteri𑁒spec' Ψ' with "[$Hmodel Hfn]").
    { rewrite /Ψ'. iSteps.
      iApply (big_sepL_impl with "Hfn"). iSteps.
      rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
      eapply Nat.lt_le_incl, lookup_lt_Some. done.
    }
    iSteps.
  Qed.

  Lemma dynarray_1٠iter𑁒spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_1٠iter fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp_rec.
    wp_apply+ (dynarray_1٠iteri𑁒spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_1٠iter𑁒spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_1٠iter fn t
    {{{
      RET ();
      dynarray_1_model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp_rec.
    wp_apply+ (dynarray_1٠iteri𑁒spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma dynarray_1٠iter𑁒spec_disentangled Ψ fn t vs :
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
      dynarray_1٠iter fn t
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
    wp_apply+ (dynarray_1٠iteri𑁒spec_disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_1٠iter𑁒spec_disentangled' Ψ fn t vs :
    {{{
      dynarray_1_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1٠iter fn t
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
    wp_apply+ (dynarray_1٠iteri𑁒spec_disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
End zoo_G.

Require zoo_std.dynarray_1__opaque.

#[global] Opaque dynarray_1_model.
