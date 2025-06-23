From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Import
  notations.
From zoo.iris.bi Require Import
  big_op.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From zoo_saturn Require Export
  base
  inf_ws_queue_2__code.
From zoo_saturn Require Import
  inf_ws_queue_1.
From zoo Require Import
  options.

Implicit Types v t : val.

Class InfWsQueue2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] inf_ws_queue_2_G :: InfWsQueue1G Σ ;
}.

Definition inf_ws_queue_2_Σ := #[
  inf_ws_queue_1_Σ
].
#[global] Instance subG_inf_ws_queue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG inf_ws_queue_2_Σ Σ →
  InfWsQueue2G Σ .
Proof.
  solve_inG.
Qed.

Section inf_ws_queue_2_G.
  Context `{inf_ws_queue_2_G : InfWsQueue2G Σ}.

  Definition inf_ws_queue_2_inv :=
    inf_ws_queue_1_inv.

  Definition inf_ws_queue_2_model t vs : iProp Σ :=
    ∃ slots,
    inf_ws_queue_1_model t (#@{location} <$> slots) ∗
    [∗ list] slot; v ∈ slots; vs, slot ↦ᵣ□ v.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %slots_vs{} &
      Hmodel{_{}} &
      Hslots_vs{}
    )".

  Definition inf_ws_queue_2_owner t ws : iProp Σ :=
    ∃ slots,
    inf_ws_queue_1_owner t (#@{location} <$> slots) ∗
    [∗ list] slot; v ∈ slots; ws, slot ↦ᵣ□ v.
  #[local] Instance : CustomIpatFormat "owner" :=
    "(
      %slots_ws{} &
      Howner{_{}} &
      Hslots_ws{}
    )".

  #[global] Instance inf_ws_queue_2_model_timeless t vs :
    Timeless (inf_ws_queue_2_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_ws_queue_2_owner_timeless t ws :
    Timeless (inf_ws_queue_2_owner t ws).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_ws_queue_2_inv_persistent t ι :
    Persistent (inf_ws_queue_2_inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma inf_ws_queue_2_model_exclusive t vs1 vs2 :
    inf_ws_queue_2_model t vs1 -∗
    inf_ws_queue_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (inf_ws_queue_1_model_exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma inf_ws_queue_2_owner_exclusive t ws1 ws2 :
    inf_ws_queue_2_owner t ws1 -∗
    inf_ws_queue_2_owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)".
    iApply (inf_ws_queue_1_owner_exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma inf_ws_queue_2_owner_model t ws vs :
    inf_ws_queue_2_owner t ws -∗
    inf_ws_queue_2_model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model)".
    iDestruct (inf_ws_queue_1_owner_model with "Howner_1 Hmodel") as %(slots & ->)%suffix_fmap; last congruence.
    iDestruct (big_sepL2_app_inv_l with "Hslots_ws1") as "(%ws1 & %vs_ & -> & _ & Hslots_vs_)".

    iAssert ⌜vs = vs_⌝%I as %<-.
    { rewrite list_eq_Forall2.
      iApply big_sepL2_Forall2.
      iDestruct (big_sepL2_retract_l with "Hslots_vs") as "(% & Hvs)".
      iDestruct (big_sepL2_retract_l with "Hslots_vs_") as "(% & Hvs_)".
      iDestruct (big_sepL2_sepL_2 with "Hvs Hvs_") as "H"; first congruence.
      iApply (big_sepL2_impl with "H"). iIntros "!> %i %v %v_ _ _ ((%slot1 & %Hslots_vs_lookup_1 & Hl1) & (%slot2 & %Hslots_vs_lookup_2 & Hl2))". simplify.
      iApply (pointsto_agree with "Hl1 Hl2").
    }

    iExists ws1. iSteps.
  Qed.

  Lemma inf_ws_queue_2_create_spec ι :
    {{{
      True
    }}}
      inf_ws_queue_2_create ()
    {{{ t,
      RET t;
      inf_ws_queue_2_inv t ι ∗
      inf_ws_queue_2_model t [] ∗
      inf_ws_queue_2_owner t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_apply (inf_ws_queue_1_create_spec with "[//]") as (t) "(#Hinv & Hmodel & Howner)".

    iSteps. iExists []. iSteps. iExists []. iSteps.
  Qed.

  Lemma inf_ws_queue_2_push_spec t ι ws v :
    <<<
      inf_ws_queue_2_inv t ι ∗
      inf_ws_queue_2_owner t ws
    | ∀∀ vs,
      inf_ws_queue_2_model t vs
    >>>
      inf_ws_queue_2_push t v @ ↑ι
    <<<
      inf_ws_queue_2_model t (vs ++ [v])
    | RET ();
      inf_ws_queue_2_owner t (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:owner)) HΦ".

    wp_rec.
    wp_ref slot as "Hslot".
    iMod (pointsto_persist with "Hslot") as "Hslot".

    awp_apply (inf_ws_queue_1_push_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; iIntros "Hmodel !>"; first iSteps.
    iDestruct (big_sepL2_snoc_2 with "Hslots_vs Hslot") as "-##Hslots_vs".
    rewrite -fmap_snoc. iSteps.
  Qed.

  Lemma inf_ws_queue_2_steal_spec t ι :
    <<<
      inf_ws_queue_2_inv t ι
    | ∀∀ vs,
      inf_ws_queue_2_model t vs
    >>>
      inf_ws_queue_2_steal t @ ↑ι
    <<<
      inf_ws_queue_2_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.

    awp_smart_apply (inf_ws_queue_1_steal_spec with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; iIntros "Hmodel !>"; first iSteps.
    destruct slots_vs as [| slot slots_vs], vs as [| v vs] => //.
    all: iFrameSteps.
  Qed.

  Lemma inf_ws_queue_2_pop_spec t ι ws :
    <<<
      inf_ws_queue_2_inv t ι ∗
      inf_ws_queue_2_owner t ws
    | ∀∀ vs,
      inf_ws_queue_2_model t vs
    >>>
      inf_ws_queue_2_pop t @ ↑ι
    <<<
      ∃∃ o ws,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws = []⌝ ∗
          inf_ws_queue_2_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws = vs'⌝ ∗
          inf_ws_queue_2_model t vs'
      end
    | RET o;
      inf_ws_queue_2_owner t ws
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:owner)) HΦ".

    wp_rec.

    awp_smart_apply (inf_ws_queue_1_pop_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([𝑠𝑙𝑜𝑡 |] ?).
    - iIntros "(%𝑠𝑙𝑜𝑡s & %Hslots & -> & Hmodel) !>".
      apply fmap_snoc_inv in Hslots as (slots' & slot & -> & -> & ->).
      iDestruct (big_sepL2_snoc_inv_l with "Hslots_vs") as "(%vs' & %v & -> & #Hslots & #Hslot)".
      iExists (Some v). iFrameSteps.
    - iIntros "(%Hslots & -> & Hmodel) !>".
      apply fmap_nil_inv in Hslots as ->.
      iDestruct (big_sepL2_nil_inv_l with "Hslots_vs") as %->.
      iExists None. iFrameSteps. iExists []. iSteps.
  Qed.
End inf_ws_queue_2_G.

From zoo_saturn Require
  inf_ws_queue_2__opaque.

#[global] Opaque inf_ws_queue_2_inv.
#[global] Opaque inf_ws_queue_2_model.
#[global] Opaque inf_ws_queue_2_owner.
