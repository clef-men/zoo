(* Based on:
   https://github.com/ocaml/ocaml/blob/50ce58a33aac9d067ee88af2e84dba02f8f49033/stdlib/dynarray.ml
*)

From zebre Require Import
  prelude.
From zebre.common Require Import
  list.
From zebre.iris.bi Require Import
  big_op.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre.std Require Import
  diverge
  assume
  math
  ref_
  opt
  array.
From zebre Require Import
  options.

Implicit Types b : bool.
Implicit Types i : nat.
Implicit Types l r : loc.
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
    assume (#0 ≤ "sz") ;;
    { "sz"; array_initi "sz" (λ: <>, ‘Some{ ref "v" }) }.

Definition dynarray_initi : val :=
  λ: "sz" "fn",
    assume (#0 ≤ "sz") ;;
    { "sz"; array_initi "sz" (λ: "i", ‘Some{ ref ("fn" "i") }) }.

Definition dynarray_size : val :=
  λ: "t",
    "t".{size}.
#[local] Definition dynarray_data : val :=
  λ: "t",
    "t".{data}.
Definition dynarray_capacity : val :=
  λ: "t",
    array_size (dynarray_data "t").

#[local] Definition dynarray_set_size : val :=
  λ: "t" "sz",
    "t" <-{size} "sz".
#[local] Definition dynarray_set_data : val :=
  λ: "t" "data",
    "t" <-{data} "data".

Definition dynarray_is_empty : val :=
  λ: "t",
    dynarray_size "t" = #0.

Definition dynarray_get : val :=
  λ: "t" "i",
    match: array_get (dynarray_data "t") "i" with
    | None =>
        diverge ()
    | Some "ref" =>
        !"ref"
    end.

Definition dynarray_set : val :=
  λ: "t" "i" "v",
    match: array_get (dynarray_data "t") "i" with
    | None =>
        diverge ()
    | Some "ref" =>
        "ref" <- "v"
    end.

#[local] Definition dynarray_next_capacity : val :=
  λ: "n",
    #8 `max` if: "n" ≤ #512 then #2 * "n" else "n" + "n" `quot` #2.
Definition dynarray_reserve : val :=
  λ: "t" "n",
    assume (#0 ≤ "n") ;;
    let: "data" := dynarray_data "t" in
    let: "cap" := array_size "data" in
    ifnot: "n" ≤ "cap" then (
      let: "new_cap" := "n" `max` dynarray_next_capacity "cap" in
      let: "new_data" := array_make "new_cap" §None in
      array_blit "data" #0 "new_data" #0 (dynarray_size "t") ;;
      dynarray_set_data "t" "new_data"
    ).
Definition dynarray_reserve_extra : val :=
  λ: "t" "n",
    assume (#0 ≤ "n") ;;
    dynarray_reserve "t" (dynarray_size "t" + "n").

#[local] Definition dynarray_try_push : val :=
  λ: "t" "slot",
    let: "sz" := dynarray_size "t" in
    let: "data" := dynarray_data "t" in
    if: array_size "data" ≤ "sz" then (
      #false
    ) else (
      dynarray_set_size "t" (#1 + "sz") ;;
      array_unsafe_set "data" "sz" "slot" ;;
      #true
    ).
#[local] Definition dynarray_push_aux : val :=
  rec: "dynarray_push_aux" "t" "slot" :=
    dynarray_reserve_extra "t" #1 ;;
    ifnot: dynarray_try_push "t" "slot" then (
      "dynarray_push_aux" "t" "slot"
    ).
Definition dynarray_push : val :=
  λ: "t" "v",
    let: "slot" := ‘Some{ ref "v" } in
    ifnot: dynarray_try_push "t" "slot" then (
      dynarray_push_aux "t" "slot"
    ).

Definition dynarray_pop : val :=
  λ: "t",
    let: "sz" := dynarray_size "t" in
    let: "data" := dynarray_data "t" in
    assume ("sz" ≤ array_size "data") ;;
    assume (#0 < "sz") ;;
    let: "sz" := "sz" - #1 in
    match: array_unsafe_get "data" "sz" with
    | None =>
        diverge ()
    | Some "ref" =>
        array_unsafe_set "data" "sz" §None ;;
        dynarray_set_size "t" "sz" ;;
        !"ref"
    end.

Definition dynarray_fit_capacity : val :=
  λ: "t",
    let: "sz" := dynarray_size "t" in
    let: "data" := dynarray_data "t" in
    ifnot: array_size "data" = "sz" then (
      dynarray_set_data "t" (array_shrink "data" "sz")
    ).

Definition dynarray_reset : val :=
  λ: "t",
    dynarray_set_size "t" #0 ;;
    dynarray_set_data "t" (array_create ()).

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  #[local] Definition slot_model slot v : iProp Σ :=
    ∃ r,
    ⌜slot = ’Some{ #r }⌝ ∗
    r ↦ v.
  Definition dynarray_model t vs : iProp Σ :=
    ∃ l data slots extra,
    ⌜t = #l⌝ ∗
    l.[size] ↦ #(length vs) ∗
    l.[data] ↦ data ∗ array_model data (DfracOwn 1) (slots ++ replicate extra §None) ∗
    [∗ list] slot; v ∈ slots; vs, slot_model slot v.

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
    wp_record l as "(Hsz & Hdata & _)".
    iApply "HΦ". iExists l, data, [], 0. iSteps.
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
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (array_initi_spec_disentangled (λ _ slot, slot_model slot v)) as "%data %slots (%Hslots & Hdata_model & Hslots)"; first done.
    { iStep 5. iModIntro. wp_alloc r as "Hr". iSteps. }
    wp_record l as "(Hsz & Hdata & _)".
    iApply "HΦ". iExists l, data, slots, 0. iFrame. iSplitR; first iSteps.
    rewrite replicate_length right_id. iFrame.
    iApply (big_sepL2_replicate_r_2 _ _ (λ _, slot_model) with "Hslots"). lia.
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
    wp_smart_apply assume_spec' as "_".
    pose Ψ' i slots := (
      ∃ vs,
      Ψ i vs ∗
      [∗ list] slot; v ∈ slots; vs, slot_model slot v
    )%I.
    wp_smart_apply (array_initi_spec Ψ' with "[HΨ]") as "%data %slots (%Hslots & Hdata_model & (%vs & HΨ & Hslots))"; first done.
    { iSplitL "HΨ"; first iSteps. iIntros "!> %i %slots (%Hi1 & %Hi2) (%vs & HΨ & Hslots)".
      iDestruct (big_sepL2_length with "Hslots") as %Hslots.
      wp_smart_apply (wp_wand with "(Hfn [] HΨ)") as "%v HΨ"; first iSteps.
      wp_alloc r as "Hr". wp_pures.
      iExists (vs ++ [v]). iFrame. iSteps.
    }
    wp_record l as "(Hsz & Hdata & _)".
    iDestruct (big_sepL2_length with "Hslots") as %Hslots'.
    iApply "HΦ". iFrame. iSplitR; first iSteps.
    iExists l, data, slots, 0. iFrame. iSplitR; first iSteps. iSplitL "Hsz"; first iSteps.
    rewrite right_id //.
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
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
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
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
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
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hmodel & Hslots) HΦ".
    wp_rec. rewrite /dynarray_data. wp_load.
    wp_apply (array_size_spec with "Hmodel") as "Hmodel".
    rewrite app_length. iDestruct (big_sepL2_length with "Hslots") as %->.
    iSteps.
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
    iIntros "%Hi %Hvs_lookup %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    Z_to_nat i. rewrite Nat2Z.id in Hvs_lookup.
    clear Hi. pose proof Hvs_lookup as Hi%lookup_lt_Some.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    destruct (lookup_lt_is_Some_2 slots i) as (slot & Hslots_lookup); first lia.
    iDestruct (big_sepL2_lookup_acc with "Hslots") as "((%r & %Hr & Hr) & Hslots)"; [done.. | subst slot].
    wp_rec. rewrite /dynarray_data. wp_load.
    wp_smart_apply (array_get_spec with "Hdata_model"); [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l //. lia. }
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
    iIntros "%Hi %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    opose proof* (lookup_lookup_total vs i) as Hvs_lookup.
    { apply lookup_lt_is_Some_2. lia. }
    destruct (lookup_lt_is_Some_2 slots i) as (slot & Hslots_lookup); first lia.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "((%r & %Hr & Hr) & Hslots)"; [done.. | subst slot].
    wp_rec. rewrite /dynarray_data. wp_load.
    wp_smart_apply (array_get_spec with "Hdata_model") as "Hdata_model"; [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l //. lia. }
    wp_store.
    iDestruct ("Hslots" with "[Hr]") as "Hslots"; first iSteps.
    rewrite (list_insert_id slots) //.
    iApply "HΦ". iExists l, data, slots, extra. rewrite insert_length. iSteps.
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
    iIntros "%Hn %Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /dynarray_data.
    wp_smart_apply assume_spec' as "_".
    wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    wp_pures.
    case_bool_decide; wp_pures; first iSteps.
    wp_smart_apply (dynarray_next_capacity_spec with "[//]") as "%n' %Hn'"; first lia.
    wp_apply maximum_spec.
    wp_smart_apply (array_make_spec with "[//]") as "%data' Hdata_model'"; first lia.
    rewrite /dynarray_size. wp_load.
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    wp_smart_apply (array_blit_spec with "[$Hdata_model $Hdata_model']") as "(Hdata_model & Hdata_model')"; try lia.
    { rewrite app_length. lia. }
    { rewrite replicate_length. rewrite app_length in Hn'. lia. }
    rewrite /dynarray_set_data. wp_store.
    iApply "HΦ". iExists l, data', slots, _. iFrame. iSplitR; first iSteps.
    rewrite !Nat2Z.id drop_replicate take_app_length' //.
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
    iIntros "%Hn %Φ Hmodel HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "_".
    wp_smart_apply (dynarray_size_spec with "Hmodel") as "Hmodel".
    wp_smart_apply (dynarray_reserve_spec with "Hmodel"); first lia.
    iSteps.
  Qed.

  #[local] Lemma dynarray_try_push_spec t vs slot v :
    {{{
      dynarray_model t vs ∗
      slot_model slot v
    }}}
      dynarray_try_push t slot
    {{{ b,
      RET #b;
      if b then
        dynarray_model t (vs ++ [v])
      else
        dynarray_model t vs ∗
        slot_model slot v
    }}}.
  Proof.
    iIntros "%Φ ((%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) & Hslot) HΦ".
    iDestruct (big_sepL2_length with "Hslots") as "%Hslots".
    wp_rec. rewrite /dynarray_size /dynarray_data /dynarray_set_size. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    wp_pures.
    case_bool_decide as Htest; wp_pures.
    { iApply "HΦ". iFrame. iSteps. }
    wp_store.
    wp_smart_apply (array_unsafe_set_spec with "Hdata_model") as "Hdata_model"; first lia.
    wp_pures.
    iApply "HΦ". iExists l, data, (slots ++ [slot]), (extra - 1). iFrame. iSplitR; first iSteps.
    rewrite app_length Z.add_1_l -Nat2Z.inj_succ Nat.add_comm /=. iFrame.
    rewrite Nat2Z.id -Hslots -(Nat.add_0_r (length slots)) insert_app_r.
    destruct extra.
    - rewrite app_length in Htest. naive_solver lia.
    - rewrite -(assoc (++)) /= Nat.sub_0_r. iSteps.
  Qed.
  #[local] Lemma dynarray_push_aux_spec t vs slot v :
    {{{
      dynarray_model t vs ∗
      slot_model slot v
    }}}
      dynarray_push_aux t slot
    {{{
      RET ();
      dynarray_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hslot) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply (dynarray_reserve_extra_spec with "Hmodel") as "Hmodel"; first lia.
    wp_smart_apply (dynarray_try_push_spec with "[$Hmodel $Hslot]") as ([]) ""; first iSteps. iIntros "(Hmodel & Hslot)".
    wp_smart_apply ("HLöb" with "Hmodel Hslot HΦ").
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
    iIntros "%Φ Hmodel HΦ".
    wp_rec. wp_alloc r as "Hr".
    wp_smart_apply (dynarray_try_push_spec with "[$Hmodel Hr]") as ([]) ""; [iSteps.. |]. iIntros "(Hmodel & Hslot)".
    wp_smart_apply (dynarray_push_aux_spec with "[$Hmodel $Hslot]").
    iSteps.
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
    iIntros (->) "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /dynarray_size /dynarray_data /dynarray_set_size. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    do 2 (wp_smart_apply assume_spec' as "_").
    wp_pures.
    rewrite app_length Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    iDestruct (big_sepL2_length with "Hslots") as %Hslots. rewrite app_length /= in Hslots.
    destruct (rev_elim slots) as [-> | (slots_ & slot & ->)]; first (simpl in Hslots; lia).
    rewrite app_length Nat.add_cancel_r in Hslots. iEval (rewrite -Hslots).
    iDestruct (big_sepL2_snoc with "Hslots") as "(Hslots & (%r & -> & Hr))".
    wp_apply (array_unsafe_get_spec with "Hdata_model") as "Hdata_model"; [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l; first (rewrite app_length /=; lia).
      rewrite lookup_app_r // Nat.sub_diag //.
    }
    wp_smart_apply (array_unsafe_set_spec with "Hdata_model") as "Hdata_model".
    { rewrite !app_length /=. lia. }
    rewrite -assoc Nat2Z.id insert_app_r_alt // Nat.sub_diag /=.
    wp_store. wp_load.
    iApply "HΦ". iExists l, data, slots_, (S extra).
    iSteps.
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
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & Hdata_model & Hslots) HΦ".
    wp_rec. rewrite /dynarray_size /dynarray_data /dynarray_set_data. do 2 wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "Hdata_model".
    iDestruct (big_sepL2_length with "Hslots") as %Hslots.
    wp_pures.
    case_bool_decide; wp_pures; first iSteps.
    wp_apply (array_shrink_spec with "Hdata_model") as "%data' (_ & Hdata_model')".
    { rewrite app_length. lia. }
    wp_store.
    iEval (rewrite -Hslots Nat2Z.id take_app_length) in "Hdata_model'".
    iApply "HΦ". iExists l, data', slots, 0.
    rewrite right_id. iSteps.
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
    iIntros "%Φ (%l & %data & %slots & %extra & -> & Hsz & Hdata & _ & _) HΦ".
    wp_rec. rewrite /dynarray_set_size /dynarray_set_data. wp_store.
    wp_smart_apply (array_create_spec with "[//]") as "%data' Hdata_model'".
    wp_store.
    iSteps. iExists [], 0. iSteps.
  Qed.

  Context τ `{!iType (iPropI Σ) τ}.

  #[local] Definition itype_slot :=
    itype_opt (itype_ref τ).
  Definition itype_dynarray t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ (sz : nat) cap data,
      l.[size] ↦ #sz ∗
      l.[data] ↦ data ∗ itype_array itype_slot cap data
    ).
  #[global] Instance itype_dynarray_itype :
    iType _ itype_dynarray.
  Proof.
    split. apply _.
  Qed.

  Lemma dynarray_create_type :
    {{{ True }}}
      dynarray_create ()
    {{{ t,
      RET t;
      itype_dynarray t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (array_create_type itype_slot with "[//]") as "%data Hdata_type".
    iSteps.
  Qed.

  Lemma dynarray_make_type (sz : Z) v :
    {{{
      τ v
    }}}
      dynarray_make #sz v
    {{{ t,
      RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype_dynarray t
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_initi_type itype_slot) as "%data (_ & Hdata_type)".
    { iStep 5. iModIntro. wp_alloc r. iSteps. }
    iSteps.
  Qed.

  Lemma dynarray_size_type t :
    {{{
      itype_dynarray t
    }}}
      dynarray_size t
    {{{ (sz : nat),
      RET #sz; True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_capacity_type t :
    {{{
      itype_dynarray t
    }}}
      dynarray_size t
    {{{ (cap : nat),
      RET #cap; True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma dynarray_data_type t :
    {{{
      itype_dynarray t
    }}}
      dynarray_data t
    {{{ cap data,
      RET data;
      itype_array itype_slot cap data
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma dynarray_set_size_type t sz :
    (0 ≤ sz)%Z →
    {{{
      itype_dynarray t
    }}}
      dynarray_set_size t #sz
    {{{
      RET (); True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma dynarray_set_data_type t cap data :
    {{{
      itype_dynarray t ∗
      itype_array itype_slot cap data
    }}}
      dynarray_set_data t data
    {{{
      RET (); True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_is_empty_type t :
    {{{
      itype_dynarray t
    }}}
      dynarray_is_empty t
    {{{ b,
      RET #b; True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_get_type t (i : Z) :
    {{{
      itype_dynarray t
    }}}
      dynarray_get t #i
    {{{ v,
      RET v;
      ⌜0 ≤ i⌝%Z ∗
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply (dynarray_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_apply (array_get_type with "Hdata_type") as "%slot (%Hi & #Hslot)".
    wp_apply (wp_match_opt with "Hslot"). iSplit.
    - wp_apply diverge_spec.
    - iIntros "%r #Hr /=".
      wp_apply (ref_get_type with "Hr").
      iSteps.
  Qed.

  Lemma dynarray_set_type t (i : Z) v :
    {{{
      itype_dynarray t ∗
      τ v
    }}}
      dynarray_set t #i v
    {{{
      RET ();
      ⌜0 ≤ i⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_apply (array_get_type with "Hdata_type") as "%slot (%Hi & #Hslot)".
    wp_apply (wp_match_opt with "Hslot"). iSplit.
    - wp_apply diverge_spec.
    - iIntros "%r #Hr /=".
      wp_apply (ref_set_type with "[$Hr $Hv]").
      iSteps.
  Qed.

  Lemma dynarray_reserve_type t n :
    {{{
      itype_dynarray t
    }}}
      dynarray_reserve t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hn".
    wp_smart_apply (dynarray_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type") as "_".
    wp_pures.
    case_bool_decide; wp_pures; first iSteps.
    wp_smart_apply (dynarray_next_capacity_spec with "[//]") as "%n' %Hn'"; first lia.
    wp_apply maximum_spec.
    wp_smart_apply (array_make_type itype_slot) as "%data' (_ & #Hdata_type')"; first iSteps.
    wp_smart_apply dynarray_size_type as "%sz _"; first iSmash+.
    wp_smart_apply (array_blit_type itype_slot) as "_"; first iSteps.
    wp_smart_apply (dynarray_set_data_type with "[$Htype $Hdata_type']") as "_".
    iSteps.
  Qed.
  Lemma dynarray_reserve_extra_type t n :
    {{{
      itype_dynarray t
    }}}
      dynarray_reserve_extra t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_smart_apply assume_spec' as "%Hn".
    wp_smart_apply (dynarray_size_type with "Htype") as "%sz _".
    wp_smart_apply (dynarray_reserve_type with "Htype").
    iSteps.
  Qed.

  #[local] Lemma dynarray_try_push_type t slot :
    {{{
      itype_dynarray t ∗
      itype_slot slot
    }}}
      dynarray_try_push t slot
    {{{ b,
      RET #b; True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    wp_rec.
    wp_smart_apply (dynarray_size_type with "Htype") as "%sz _".
    wp_smart_apply (dynarray_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type") as "_".
    wp_pures.
    case_bool_decide; wp_pures; first iSteps.
    wp_apply (dynarray_set_size_type with "Htype") as "_"; first lia.
    wp_smart_apply (array_unsafe_set_type with "[$Hdata_type $Hslot]") as "_"; first lia.
    iSteps.
  Qed.
  #[local] Lemma dynarray_push_aux_type t slot :
    {{{
      itype_dynarray t ∗
      itype_slot slot
    }}}
      dynarray_push_aux t slot
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply (dynarray_reserve_extra_type with "Htype") as "_".
    wp_smart_apply (dynarray_try_push_type with "[$Htype $Hslot]") as ([]) "_"; first iSteps.
    wp_smart_apply ("HLöb" with "HΦ").
  Qed.
  Lemma dynarray_push_type t v :
    {{{
      itype_dynarray t ∗
      τ v
    }}}
      dynarray_push t v
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp_rec. wp_alloc r as "Hr".
    iAssert (|={⊤}=> itype_slot ’Some{ #r })%I with "[Hr]" as ">#Hslot"; first iSteps.
    wp_smart_apply (dynarray_try_push_type with "[$Htype $Hslot]") as ([]) "_"; first iSteps.
    wp_smart_apply (dynarray_push_aux_type with "[$Htype $Hslot]") as "_".
    iSteps.
  Qed.

  Lemma dynarray_pop_type t :
    {{{
      itype_dynarray t
    }}}
      dynarray_pop t
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (dynarray_size_type with "Htype") as "%sz _".
    wp_smart_apply (dynarray_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type") as "_".
    wp_smart_apply assume_spec' as "%Hcap".
    wp_smart_apply assume_spec' as "%Hsz".
    wp_smart_apply (array_unsafe_get_type with "Hdata_type") as "%slot #Hslot"; first lia.
    wp_apply (wp_match_opt with "Hslot"). iSplit.
    - wp_apply diverge_spec.
    - iIntros "%r #Hr /=".
      wp_smart_apply (array_unsafe_set_type with "[$Hdata_type]") as "_"; [lia | iSteps |].
      wp_smart_apply (dynarray_set_size_type with "Htype") as "_"; first lia.
      wp_smart_apply (ref_get_type with "Hr").
      iSteps.
  Qed.

  Lemma dynarray_fit_capacity_type t v :
    {{{
      itype_dynarray t
    }}}
      dynarray_fit_capacity t
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (dynarray_size_type with "Htype") as "%sz _".
    wp_smart_apply (dynarray_data_type with "Htype") as "%cap %data #Hdata_type".
    wp_smart_apply (array_size_type with "Hdata_type") as "_".
    wp_pures.
    case_decide; wp_pures; first iSteps.
    wp_apply (array_shrink_type with "Hdata_type") as "%t' (_ & #Hdata_type')".
    wp_apply (dynarray_set_data_type with "[$Htype $Hdata_type']").
    iSteps.
  Qed.

  Lemma dynarray_reset_type t v :
    {{{
      itype_dynarray t
    }}}
      dynarray_reset t
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp_rec.
    wp_apply (dynarray_set_size_type with "Htype") as "_"; first done.
    wp_smart_apply (array_create_type with "[//]") as "%data' #Hdata_type'".
    wp_apply (dynarray_set_data_type with "[$Htype $Hdata_type']").
    iSteps.
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
#[global] Opaque itype_dynarray.
