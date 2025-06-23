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
    [∗ list] slot; v ∈ slots; vs, slot ↦ᵣ v.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %slots{} &
      Hmodel{_{}} &
      Hslots{}
    )".

  Definition ws_queue_2_owner :=
    ws_queue_1_owner.

  #[global] Instance ws_queue_2_model_timeless t vs :
    Timeless (ws_queue_2_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_queue_2_owner_timeless t :
    Timeless (ws_queue_2_owner t).
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

  Lemma ws_queue_2_owner_exclusive t :
    ws_queue_2_owner t -∗
    ws_queue_2_owner t -∗
    False.
  Proof.
    apply ws_queue_1_owner_exclusive.
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
      ws_queue_2_owner t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_apply (ws_queue_1_create_spec with "[//]") as (t) "(#Hinv & Hmodel & Howner)".

    iSteps. iExists []. iSteps.
  Qed.

  Lemma ws_queue_2_push_spec t ι v :
    <<<
      ws_queue_2_inv t ι ∗
      ws_queue_2_owner t
    | ∀∀ vs,
      ws_queue_2_model t vs
    >>>
      ws_queue_2_push t v @ ↑ι
    <<<
      ws_queue_2_model t (vs ++ [v])
    | RET ();
      ws_queue_2_owner t
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_ref slot as "Hslot".

    awp_apply (ws_queue_1_push_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; iIntros "Hmodel !>"; first iSteps.
    iDestruct (big_sepL2_snoc_2 with "Hslots Hslot") as "Hslots".
    rewrite -fmap_snoc. iFrameSteps.
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
    iAaccIntro with "Hmodel"; iIntros "Hmodel !>"; first iSteps.
    destruct slots as [| slot slots], vs as [| v vs] => //.
    all: iFrameSteps.
  Qed.

  Lemma ws_queue_2_pop_spec t ι :
    <<<
      ws_queue_2_inv t ι ∗
      ws_queue_2_owner t
    | ∀∀ vs,
      ws_queue_2_model t vs
    >>>
      ws_queue_2_pop t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ws_queue_2_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ws_queue_2_model t vs'
      end
    | RET o;
      ws_queue_2_owner t
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_smart_apply (ws_queue_1_pop_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([𝑠𝑙𝑜𝑡 |]).
    - iIntros "(%𝑠𝑙𝑜𝑡s & %Hslots & Hmodel) !>".
      apply fmap_snoc_inv in Hslots as (slots' & slot & -> & -> & ->).
      iDestruct (big_sepL2_snoc_inv_l with "Hslots") as "(%vs' & %v & -> & Hslots & Hslot)".
      iExists (Some v). iFrameSteps.
    - iIntros "(%Hslots & Hmodel) !>".
      apply fmap_nil_inv in Hslots as ->.
      iDestruct (big_sepL2_nil_inv_l with "Hslots") as %->.
      iExists None. iFrameSteps.
  Qed.
End ws_queue_2_G.

From zoo_saturn Require
  ws_queue_2__opaque.

#[global] Opaque ws_queue_2_inv.
#[global] Opaque ws_queue_2_model.
#[global] Opaque ws_queue_2_owner.
