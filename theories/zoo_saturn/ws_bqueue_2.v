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
  ws_bqueue_2__code.
From zoo_saturn Require Import
  ws_bqueue_1.
From zoo Require Import
  options.

Implicit Types v t : val.

Class WsBqueue2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_bqueue_2_G :: WsBqueue1G Σ ;
}.

Definition ws_bqueue_2_Σ := #[
  ws_bqueue_1_Σ
].
#[global] Instance subG_ws_bqueue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_bqueue_2_Σ Σ →
  WsBqueue2G Σ .
Proof.
  solve_inG.
Qed.

Section ws_bqueue_2_G.
  Context `{ws_bqueue_2_G : WsBqueue2G Σ}.

  Definition ws_bqueue_2_inv :=
    ws_bqueue_1_inv.

  Definition ws_bqueue_2_model t vs : iProp Σ :=
    ∃ slots,
    ws_bqueue_1_model t (#@{location} <$> slots) ∗
    [∗ list] slot; v ∈ slots; vs, slot ↦ᵣ□ v.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %slots_vs{} &
      Hmodel{_{}} &
      Hslots_vs{}
    )".

  Definition ws_bqueue_2_owner t ws : iProp Σ :=
    ∃ slots,
    ws_bqueue_1_owner t (#@{location} <$> slots) ∗
    [∗ list] slot; v ∈ slots; ws, slot ↦ᵣ□ v.
  #[local] Instance : CustomIpatFormat "owner" :=
    "(
      %slots_ws{} &
      Howner{_{}} &
      Hslots_ws{}
    )".

  #[global] Instance ws_bqueue_2_model_timeless t vs :
    Timeless (ws_bqueue_2_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_bqueue_2_owner_timeless t ws :
    Timeless (ws_bqueue_2_owner t ws).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_bqueue_2_inv_persistent t ι cap :
    Persistent (ws_bqueue_2_inv t ι cap).
  Proof.
    apply _.
  Qed.

  Lemma ws_bqueue_2_model_valid t ι cap vs :
    ws_bqueue_2_inv t ι cap -∗
    ws_bqueue_2_model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "Hinv (:model)".
    iDestruct (big_sepL2_length with "Hslots_vs") as %<-.
    iDestruct (ws_bqueue_1_model_valid with "Hinv Hmodel") as %Hslots.
    simpl_length in Hslots.
  Qed.
  Lemma ws_bqueue_2_model_exclusive t vs1 vs2 :
    ws_bqueue_2_model t vs1 -∗
    ws_bqueue_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (ws_bqueue_1_model_exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma ws_bqueue_2_owner_exclusive t ws1 ws2 :
    ws_bqueue_2_owner t ws1 -∗
    ws_bqueue_2_owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)".
    iApply (ws_bqueue_1_owner_exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma ws_bqueue_2_owner_model t ws vs :
    ws_bqueue_2_owner t ws -∗
    ws_bqueue_2_model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model)".
    iDestruct (ws_bqueue_1_owner_model with "Howner_1 Hmodel") as %(slots & ->)%suffix_fmap; last congruence.
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

  Lemma ws_bqueue_2_create_spec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      ws_bqueue_2_create #cap
    {{{ t,
      RET t;
      ws_bqueue_2_inv t ι ₊cap ∗
      ws_bqueue_2_model t [] ∗
      ws_bqueue_2_owner t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp_apply (ws_bqueue_1_create_spec with "[//]") as (t) "(#Hinv & Hmodel & Howner)"; first done.

    iSteps. iExists []. iSteps. iExists []. iSteps.
  Qed.

  Lemma ws_bqueue_2_capacity_spec t ι cap :
    {{{
      ws_bqueue_2_inv t ι cap
    }}}
      ws_bqueue_2_capacity t
    {{{
      RET #cap;
      True
    }}}.
  Proof.
    apply: ws_bqueue_1_capacity_spec.
  Qed.

  Lemma ws_bqueue_2_push_spec t ι cap ws v :
    <<<
      ws_bqueue_2_inv t ι cap ∗
      ws_bqueue_2_owner t ws
    | ∀∀ vs,
      ws_bqueue_2_model t vs
    >>>
      ws_bqueue_2_push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      ws_bqueue_2_model t (if b then vs ++ [v] else vs)
    | RET #b;
      ws_bqueue_2_owner t (if b then vs ++ [v] else ws)
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:owner)) HΦ".

    wp_rec.
    wp_ref slot as "Hslot".
    iMod (pointsto_persist with "Hslot") as "#Hslot".

    awp_apply (ws_bqueue_1_push_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "%b (-> & Hmodel) !>".
    simpl_length.
    iDestruct (big_sepL2_length with "Hslots_vs") as %->.
    case_bool_decide.
    - iDestruct (big_sepL2_snoc_2 with "Hslots_vs Hslot") as "Hslots".
      rewrite -fmap_snoc. iSteps.
    - iSteps.
  Qed.

  Lemma ws_bqueue_2_steal_spec t ι cap :
    <<<
      ws_bqueue_2_inv t ι cap
    | ∀∀ vs,
      ws_bqueue_2_model t vs
    >>>
      ws_bqueue_2_steal t @ ↑ι
    <<<
      ws_bqueue_2_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.

    awp_smart_apply (ws_bqueue_1_steal_spec with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; iIntros "Hmodel !>"; first iSteps.
    destruct slots_vs as [| slot slots_vs], vs as [| v vs] => //.
    all: iFrameSteps.
  Qed.

  Lemma ws_bqueue_2_pop_spec t ι cap ws :
    <<<
      ws_bqueue_2_inv t ι cap ∗
      ws_bqueue_2_owner t ws
    | ∀∀ vs,
      ws_bqueue_2_model t vs
    >>>
      ws_bqueue_2_pop t @ ↑ι
    <<<
      ∃∃ o ws,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws = []⌝ ∗
          ws_bqueue_2_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws = vs'⌝ ∗
          ws_bqueue_2_model t vs'
      end
    | RET o;
      ws_bqueue_2_owner t ws
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:owner)) HΦ".

    wp_rec.

    awp_smart_apply (ws_bqueue_1_pop_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([𝑠𝑙𝑜𝑡 |] slots_ws').
    - iIntros "(%𝑠𝑙𝑜𝑡s & %Hslots_vs & <- & Hmodel) !>".
      apply fmap_snoc_inv in Hslots_vs as (slots_vs' & slot & -> & -> & ->).
      iDestruct (big_sepL2_snoc_inv_l with "Hslots_vs") as "(%vs' & %v & -> & #Hslots_vs' & #Hslot)".
      iExists (Some v). iFrameSteps.
    - iIntros "(%Hslots_vs & -> & Hmodel) !>".
      apply fmap_nil_inv in Hslots_vs as ->.
      iDestruct (big_sepL2_nil_inv_l with "Hslots_vs") as %->.
      iExists None. iFrameSteps. iExists []. iSteps.
  Qed.
End ws_bqueue_2_G.

From zoo_saturn Require
  ws_bqueue_2__opaque.

#[global] Opaque ws_bqueue_2_inv.
#[global] Opaque ws_bqueue_2_model.
#[global] Opaque ws_bqueue_2_owner.
