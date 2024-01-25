From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre.std Require Import
  math
  array.
From zebre Require Import
  options.

Implicit Types b : bool.
Implicit Types i : nat.
Implicit Types l : loc.
Implicit Types v t fn : val.
Implicit Types vs : list val.

#[local] Notation "'size'" :=
  0
( in custom zebre_field
).
#[local] Notation "'data'" :=
  1
( in custom zebre_field
).

Definition dynarray_create : val :=
  λ: <>,
    { #0; array_create () }.

Definition dynarray_make : val :=
  λ: "sz" "v",
    { "sz"; array_make "sz" "v" }.

Definition dynarray_initi : val :=
  λ: "sz" "fn",
    { "sz"; array_initi "sz" "fn" }.

Definition dynarray_size : val :=
  λ: "t",
    "t".{size}.
Definition dynarray_capacity : val :=
  λ: "t",
    array_size "t".{data}.

Definition dynarray_is_empty : val :=
  λ: "t",
    dynarray_size "t" = #0.

Definition dynarray_get : val :=
  λ: "t" "i",
    array_unsafe_get "t".{data} "i".

Definition dynarray_set : val :=
  λ: "t" "i" "v",
    array_unsafe_set "t".{data} "i" "v".

#[local] Definition dynarray_next_capacity : val :=
  λ: "n",
    #8 `max` if: "n" ≤ #512 then #2 * "n" else "n" + "n" `quot` #2.
Definition dynarray_reserve : val :=
  λ: "t" "n",
    let: "data" := "t".{data} in
    let: "cap" := array_size "data" in
    ifnot: "n" ≤ "cap" then (
      let: "new_cap" := "n" `max` dynarray_next_capacity "cap" in
      let: "new_data" := array_make "new_cap" () in
      array_blit "data" #0 "new_data" #0 "t".{size} ;;
      "t" <-{data}- "new_data"
    ).
Definition dynarray_reserve_extra : val :=
  λ: "t" "n",
    if: #0 ≤ "n" then (
      dynarray_reserve "t" ("t".{size} + "n")
    ).

Definition dynarray_push : val :=
  λ: "t" "v",
    dynarray_reserve_extra "t" #1 ;;
    let: "sz" := "t".{size} in
    "t" <-{size}- "sz" + #1 ;;
    array_unsafe_set "t".{data} "sz" "v".

Definition dynarray_pop : val :=
  λ: "t",
    let: "sz" := "t".{size} - #1 in
    "t" <-{size}- "sz" ;;
    let: "data" := "t".{data} in
    let: "v" := array_unsafe_get "data" "sz" in
    array_unsafe_set "data" "sz" () ;;
    "v".

Definition dynarray_fit_capacity : val :=
  λ: "t",
    let: "sz" := "t".{size} in
    let: "data" := "t".{data} in
    ifnot: "sz" = array_size "data" then (
      "t" <-{data}- array_shrink "data" "sz"
    ).

Definition dynarray_reset : val :=
  λ: "t",
    "t" <-{size}- #0 ;;
    "t" <-{data}- array_create ().

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  #[local] Definition dynarray_model_inner l (sz : nat) data vs : iProp Σ :=
    l.[size] ↦ #sz ∗
    l.[data] ↦ data ∗ array_model data (DfracOwn 1) vs.
  Definition dynarray_model t vs : iProp Σ :=
    ∃ l data extra,
    ⌜t = #l⌝ ∗
    dynarray_model_inner l (length vs) data (vs ++ replicate extra ()%V).

  #[global] Instance dynarray_model_timeless t vs :
    Timeless (dynarray_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma dynarray_create_spec :
    {{{ True }}}
      dynarray_create ()
    {{{ t,
      RET t;
      dynarray_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_spec with "[//]") as "%data Hdata_model".
    wp_record l as "Hmeta" "(Hsz & Hdata & _)".
    iApply "HΦ". iExists l, data, 0. iSteps.
  Qed.

  Lemma dynarray_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{ True }}}
      dynarray_make #sz v
    {{{ t,
      RET t;
      dynarray_model t (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp_rec.
    wp_smart_apply (array_make_spec with "[//]") as "%data Hdata_model"; first done.
    wp_record l as "Hmeta" "(Hsz & Hdata & _)".
    iApply "HΦ". iExists l, data, 0. iStep. rewrite replicate_length right_id Nat2Z.id. iSteps.
  Qed.

  Lemma dynarray_initi_spec Ψ sz fn :
    (0 ≤ sz)%Z →
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
      dynarray_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      dynarray_model t vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_initi_spec Ψ with "[$HΨ]") as "%data %vs (%Hvs & Hdata_model & HΨ)"; [done | iSteps |].
    wp_record l as "Hmeta" "(Hsz & Hdata & _)".
    iApply "HΦ". iFrame. iStep. iExists l, data, 0. iSteps. rewrite right_id //.
  Qed.
  Lemma dynarray_initi_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
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
      dynarray_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      dynarray_model t vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (Z.to_nat sz - i), Ξ j
    )%I).
    wp_apply (dynarray_initi_spec Ψ' with "[$HΨ Hfn]"); [done | | iSteps].
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (Z.to_nat sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)").
    iSteps. rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma dynarray_initi_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      dynarray_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_initi_spec Ψ'); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma dynarray_initi_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      dynarray_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (dynarray_initi_spec' Ψ' with "[Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn").
    iSteps. rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma dynarray_size_spec t vs :
    {{{
      dynarray_model t vs
    }}}
      dynarray_size t
    {{{
      RET #(length vs);
      dynarray_model t vs
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_capacity_spec t vs :
    {{{
      dynarray_model t vs
    }}}
      dynarray_capacity t
    {{{ cap,
      RET #cap;
      ⌜length vs ≤ cap⌝ ∗
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%l & %data & %extra & -> & Hsz & Hdata & Hdata_model) HΦ".
    wp_rec. wp_load.
    wp_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    rewrite app_length. iSteps.
  Qed.

  Lemma dynarray_is_empty_spec t vs :
    {{{
      dynarray_model t vs
    }}}
      dynarray_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply (dynarray_size_spec with "Hmodel") as "Hmodel".
    wp_pures.
    destruct vs; iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma dynarray_get_spec t vs (i : Z) v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      dynarray_model t vs
    }}}
      dynarray_get t #i
    {{{
      RET v;
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (%l & %data & %extra & -> & Hsz & Hdata & Hdata_model) HΦ".
    wp_rec. wp_load.
    wp_apply (array_unsafe_get_spec with "Hdata_model"); [lia | | done |].
    { rewrite lookup_app_l //. eapply lookup_lt_Some. done. }
    iSteps.
  Qed.

  Lemma dynarray_set_spec t vs (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      dynarray_model t vs
    }}}
      dynarray_set t #i v
    {{{
      RET ();
      dynarray_model t (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (%l & %data & %extra & -> & Hsz & Hdata & Hdata_model) HΦ".
    wp_rec. wp_load.
    wp_apply (array_unsafe_set_spec with "Hdata_model") as "Hdata_model".
    { rewrite app_length. lia. }
    iApply "HΦ". iExists l, data, extra.
    rewrite insert_length insert_app_l; first lia. iSteps.
  Qed.

  #[local] Lemma dynarray_next_capacity_spec n :
    (0 ≤ n)%Z →
    {{{ True }}}
      dynarray_next_capacity #n
    {{{ m,
      RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    Ltac Zify.zify_post_hook ::= Z.quot_rem_to_equations.
    iSteps; wp_apply maximum_spec; iSteps.
  Qed.
  #[local] Lemma dynarray_reserve_spec' l data vs extra n :
    (0 ≤ n)%Z →
    {{{
      dynarray_model_inner l (length vs) data (vs ++ replicate extra ()%V)
    }}}
      dynarray_reserve #l #n
    {{{ data' extra',
      RET ();
      ⌜Z.to_nat n ≤ length vs + extra'⌝ ∗
      dynarray_model_inner l (length vs) data' (vs ++ replicate extra' ()%V)
    }}}.
  Proof.
    iIntros "%Hn %Φ (Hsz & Hdata & Hdata_model) HΦ".
    wp_rec. wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    wp_pures.
    case_bool_decide as Htest; wp_pures; rewrite app_length replicate_length in Htest.
    - iApply ("HΦ" $! data extra).
      iSteps.
    - wp_apply (dynarray_next_capacity_spec with "[//]") as "%n' %Hn'"; first lia.
      wp_apply maximum_spec.
      wp_smart_apply (array_make_spec with "[//]") as "%data' Hdata_model'"; first lia.
      wp_load.
      wp_smart_apply (array_blit_spec with "[$Hdata_model $Hdata_model']") as "(Hdata_model & Hdata_model')"; try lia.
      { rewrite app_length. lia. }
      { rewrite replicate_length. lia. }
      wp_store.
      iApply ("HΦ" $! data' (Z.to_nat (n `max` n') - length vs)).
      iSteps. rewrite Nat2Z.id drop_replicate take_app //.
  Qed.
  Lemma dynarray_reserve_spec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_model t vs
    }}}
      dynarray_reserve t #n
    {{{
      RET ();
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ (%l & %data & %extra & -> & Hmodel) HΦ".
    wp_apply (dynarray_reserve_spec' with "Hmodel"); first done.
    iSteps.
  Qed.
  #[local] Lemma dynarray_reserve_extra_spec' l data vs extra n :
    (0 ≤ n)%Z →
    {{{
      dynarray_model_inner l (length vs) data (vs ++ replicate extra ()%V)
    }}}
      dynarray_reserve_extra #l #n
    {{{ data' extra',
      RET ();
      ⌜Z.to_nat n ≤ extra'⌝ ∗
      dynarray_model_inner l (length vs) data' (vs ++ replicate extra' ()%V)
    }}}.
  Proof.
    iIntros "%Hn %Φ (Hsz & Hdata & Hdata_model) HΦ".
    wp_rec. wp_pures.
    case_bool_decide; wp_pures; last iSmash.
    wp_load.
    wp_smart_apply (dynarray_reserve_spec' with "[Hsz Hdata Hdata_model]") as "%data' %extra' (%Hextra' & Hmodel)"; [lia | iSteps |].
    iApply ("HΦ" $! data' extra').
    iSteps.
  Qed.
  Lemma dynarray_reserve_extra_spec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_model t vs
    }}}
      dynarray_reserve_extra t #n
    {{{
      RET ();
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ (%l & %data & %extra & -> & Hmodel) HΦ".
    wp_apply (dynarray_reserve_extra_spec' with "Hmodel"); first done.
    iSteps.
  Qed.

  Lemma dynarray_push_spec t vs v :
    {{{
      dynarray_model t vs
    }}}
      dynarray_push t v
    {{{
      RET ();
      dynarray_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (%l & %data & %extra & -> & Hmodel) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_reserve_extra_spec' with "Hmodel") as "%data' %extra' (%Hextra' & (Hsz & Hdata & Hdata_model))"; first lia.
    wp_load. wp_store. wp_load.
    wp_apply (array_unsafe_set_spec with "Hdata_model").
    { rewrite app_length replicate_length. lia. }
    rewrite Nat2Z.id insert_app_r_alt // Nat.sub_diag insert_replicate_lt // /= (assoc (++) vs [v] (replicate _ _)).
    iSteps. rewrite app_length. iSteps.
  Qed.

  Lemma dynarray_pop_spec {t vs} vs' v :
    vs = vs' ++ [v] →
    {{{
      dynarray_model t vs
    }}}
      dynarray_pop t
    {{{
      RET v;
      dynarray_model t vs'
    }}}.
  Proof.
    iIntros (->) "%Φ (%l & %data & %extra & -> & Hsz & Hdata & Hdata_model) HΦ".
    wp_rec. wp_load. wp_store. wp_load.
    rewrite app_length Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    wp_smart_apply (array_unsafe_get_spec with "Hdata_model") as "Hdata_model"; [lia | | done |].
    { rewrite lookup_app_l; first (rewrite app_length /=; lia).
      rewrite lookup_app_r; first lia.
      rewrite Nat2Z.id Nat.sub_diag //.
    }
    wp_smart_apply (array_unsafe_set_spec with "Hdata_model").
    { rewrite !app_length /=. lia. }
    iSteps. iExists (S extra).
    rewrite -assoc insert_app_r_alt; first lia. rewrite Nat2Z.id Nat.sub_diag //.
  Qed.

  Lemma dynarray_fit_capacity_spec t vs :
    {{{
      dynarray_model t vs
    }}}
      dynarray_fit_capacity t
    {{{
      RET ();
      dynarray_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%l & %data & %extra & -> & Hsz & Hdata & Hdata_model) HΦ".
    wp_rec. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    wp_pures. case_bool_decide; wp_pures; first iSteps.
    wp_apply (array_shrink_spec with "Hdata_model") as "%data' (_ & Hdata_model')".
    { rewrite app_length. lia. }
    wp_store.
    iSteps. iExists 0. rewrite Nat2Z.id take_app right_id //.
  Qed.

  Lemma dynarray_reset_spec t vs :
    {{{
      dynarray_model t vs
    }}}
      dynarray_reset t
    {{{
      RET ();
      dynarray_model t []
    }}}.
  Proof.
    iIntros "%Φ (%l & %data & %extra & -> & Hsz & Hdata & _) HΦ".
    wp_rec. wp_store.
    wp_smart_apply (array_create_spec with "[//]") as "%data' Hdata_model'".
    wp_store.
    iSteps. iExists 0. iSteps.
  Qed.
End zebre_G.

#[global] Opaque dynarray_create.
#[global] Opaque dynarray_make.
#[global] Opaque dynarray_initi.
#[global] Opaque dynarray_size.
#[global] Opaque dynarray_capacity.
#[global] Opaque dynarray_is_empty.
#[global] Opaque dynarray_get.
#[global] Opaque dynarray_set.
#[global] Opaque dynarray_reserve.
#[global] Opaque dynarray_reserve_extra.
#[global] Opaque dynarray_push.
#[global] Opaque dynarray_pop.
#[global] Opaque dynarray_fit_capacity.
#[global] Opaque dynarray_reset.

#[global] Opaque dynarray_model.
