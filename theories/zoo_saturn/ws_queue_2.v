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
  ws_queue_2__code.
From zoo_saturn Require Import
  ws_queue_1.
From zoo Require Import
  options.

Implicit Types v t : val.

Class WsQueue2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_queue_2_G :: WsQueue1G Σ ;
}.

Definition ws_queue_2_Σ := #[
  ws_queue_1_Σ
].
#[global] Instance subG_ws_queue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_queue_2_Σ Σ →
  WsQueue2G Σ .
Proof.
  solve_inG.
Qed.

Section ws_queue_2_G.
  Context `{ws_queue_2_G : WsQueue2G Σ}.

  Definition ws_queue_2_inv :=
    ws_queue_1_inv.

  Definition ws_queue_2_model t vs : iProp Σ :=
    ∃ slots,
    ws_queue_1_model t (#@{location} <$> slots) ∗
    [∗ list] slot; v ∈ slots; vs, slot ↦ᵣ□ v.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %slots_vs{} &
      Hmodel{_{}} &
      #Hslots_vs{}
    )".

  Definition ws_queue_2_owner t ws : iProp Σ :=
    ∃ slots,
    ws_queue_1_owner t (#@{location} <$> slots) ∗
    [∗ list] slot; v ∈ slots; ws, slot ↦ᵣ□ v.
  #[local] Instance : CustomIpatFormat "owner" :=
    "(
      %slots_ws{} &
      Howner{_{}} &
      #Hslots_ws{}
    )".

  #[global] Instance ws_queue_2_model_timeless t vs :
    Timeless (ws_queue_2_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_queue_2_owner_timeless t ws :
    Timeless (ws_queue_2_owner t ws).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_queue_2_inv_persistent t ι :
    Persistent (ws_queue_2_inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma ws_queue_2_model_exclusive t vs1 vs2 :
    ws_queue_2_model t vs1 -∗
    ws_queue_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (ws_queue_1_model_exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma ws_queue_2_owner_exclusive t ws1 ws2 :
    ws_queue_2_owner t ws1 -∗
    ws_queue_2_owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)".
    iApply (ws_queue_1_owner_exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma ws_queue_2_owner_model t ws vs :
    ws_queue_2_owner t ws -∗
    ws_queue_2_model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model)".
    iDestruct (ws_queue_1_owner_model with "Howner_1 Hmodel") as %(slots & ->)%suffix_fmap; last congruence.
    iDestruct (big_sepL2_app_inv_l with "Hslots_ws1") as "(%ws1 & %vs_ & -> & _ & Hslots_vs_)".
    iDestruct (big_sepL2_ref_pointsto_agree with "Hslots_vs Hslots_vs_") as %<-.
    iExists ws1. iSteps.
  Qed.

  Lemma ws_queue_2_create_spec ι :
    {{{
      True
    }}}
      ws_queue_2_create ()
    {{{ t,
      RET t;
      ws_queue_2_inv t ι ∗
      ws_queue_2_model t [] ∗
      ws_queue_2_owner t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_apply (ws_queue_1_create_spec with "[//]") as (t) "(#Hinv & Hmodel & Howner)".

    iSteps. iExists []. iSteps. iExists []. iSteps.
  Qed.

  Lemma ws_queue_2_size_spec t ι ws :
    <<<
      ws_queue_2_inv t ι ∗
      ws_queue_2_owner t ws
    | ∀∀ vs,
      ws_queue_2_model t vs
    >>>
      ws_queue_2_size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_queue_2_model t vs
    | RET #(length vs);
      ws_queue_2_owner t vs
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:owner)) HΦ".

    awp_apply (ws_queue_1_size_spec with "[$]") without "Hslots_ws".
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; first iSteps.
    iSteps --silent / as (Hsuffix%suffix_fmap) / as (_) "HΦ Howner".
    { iApply (big_sepL2_ref_pointsto_suffix with "Hslots_vs Hslots_ws"); first done. }
    { congruence. }
    rewrite length_fmap.
    iDestruct (big_sepL2_length with "Hslots_vs") as %->.
    iSteps.
  Qed.

  Lemma ws_queue_2_is_empty_spec t ι ws :
    <<<
      ws_queue_2_inv t ι ∗
      ws_queue_2_owner t ws
    | ∀∀ vs,
      ws_queue_2_model t vs
    >>>
      ws_queue_2_is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_queue_2_model t vs
    | RET #(bool_decide (vs = []%list));
      ws_queue_2_owner t vs
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:owner)) HΦ".

    awp_apply (ws_queue_1_is_empty_spec with "[$]") without "Hslots_ws".
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; first iSteps.
    iSteps --silent / as (Hsuffix%suffix_fmap) / as (_) "HΦ Howner".
    { iApply (big_sepL2_ref_pointsto_suffix with "Hslots_vs Hslots_ws"); first done. }
    { congruence. }
    erewrite (bool_decide_ext (_ <$> _ = []) (length _ = 0)); last rewrite length_zero_iff_nil //.
    rewrite length_fmap.
    iDestruct (big_sepL2_length with "Hslots_vs") as %->.
    erewrite (bool_decide_ext (length _ = 0)); last apply length_zero_iff_nil.
    iSteps.
  Qed.

  Lemma ws_queue_2_push_spec t ι ws v :
    <<<
      ws_queue_2_inv t ι ∗
      ws_queue_2_owner t ws
    | ∀∀ vs,
      ws_queue_2_model t vs
    >>>
      ws_queue_2_push t v @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_queue_2_model t (vs ++ [v])
    | RET ();
      ws_queue_2_owner t (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:owner)) HΦ".

    wp_rec.
    wp_ref slot as "Hslot".
    iMod (pointsto_persist with "Hslot") as "#Hslot".

    awp_apply (ws_queue_1_push_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; first iSteps.
    iStep --silent / as (Hsuffix%suffix_fmap) "Hmodel"; last congruence.
    iDestruct (big_sepL2_snoc_2 with "Hslots_vs Hslot") as "#Hslots_vs'".
    rewrite -fmap_snoc. iSteps.
    iApply (big_sepL2_ref_pointsto_suffix with "Hslots_vs Hslots_ws"); first done.
  Qed.

  Lemma ws_queue_2_steal_spec t ι :
    <<<
      ws_queue_2_inv t ι
    | ∀∀ vs,
      ws_queue_2_model t vs
    >>>
      ws_queue_2_steal t @ ↑ι
    <<<
      ws_queue_2_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.

    awp_smart_apply (ws_queue_1_steal_spec with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; first iSteps.
    iStep as "Hmodel".
    destruct slots_vs as [| slot slots_vs], vs as [| v vs] => //.

    - iFrame "#". iSteps.

    - iDestruct "Hslots_vs" as "/= (Hslot & Hslots_vs)".
      iSteps.
  Qed.

  Lemma ws_queue_2_pop_spec t ι ws :
    <<<
      ws_queue_2_inv t ι ∗
      ws_queue_2_owner t ws
    | ∀∀ vs,
      ws_queue_2_model t vs
    >>>
      ws_queue_2_pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_queue_2_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          ws_queue_2_model t vs'
      end
    | RET o;
      ws_queue_2_owner t ws'
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:owner)) HΦ".

    wp_rec.

    awp_smart_apply (ws_queue_1_pop_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; first iSteps.
    iStep 3 --silent / as (o slots_ws' Hsuffix%suffix_fmap) "Ho"; last congruence.
    iDestruct (big_sepL2_ref_pointsto_suffix with "Hslots_vs Hslots_ws") as %?; first done.
    destruct o as [𝑠𝑙𝑜𝑡 |].

    - iDestruct "Ho" as "(%𝑠𝑙𝑜𝑡s & %Hslots & -> & Hmodel)".
      apply fmap_snoc_inv in Hslots as (slots' & slot & -> & -> & ->).
      iDestruct (big_sepL2_snoc_inv_l with "Hslots_vs") as "(%vs' & %v & -> & #Hslots' & #Hslot)".
      iExists (Some v). iFrameSteps.

    - iDestruct "Ho" as "(%Hslots & -> & Hmodel)".
      apply fmap_nil_inv in Hslots as ->.
      iDestruct (big_sepL2_nil_inv_l with "Hslots_vs") as %->.
      iExists None. iSteps. do 2 (iExists []; iSteps).
  Qed.
End ws_queue_2_G.

From zoo_saturn Require
  ws_queue_2__opaque.

#[global] Opaque ws_queue_2_inv.
#[global] Opaque ws_queue_2_model.
#[global] Opaque ws_queue_2_owner.
