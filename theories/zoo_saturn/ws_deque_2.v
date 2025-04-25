From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From zoo_saturn Require Export
  base
  ws_deque_2__code.
From zoo_saturn Require Import
  ws_deque_1.
From zoo Require Import
  options.

Implicit Types v t : val.

Class WsDeque2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_deque_2_G :: WsDeque1G Σ ;
}.

Definition ws_deque_2_Σ := #[
  ws_deque_1_Σ
].
#[global] Instance subG_ws_deque_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_deque_2_Σ Σ →
  WsDeque2G Σ .
Proof.
  solve_inG.
Qed.

Section ws_deque_2_G.
  Context `{ws_deque_2_G : WsDeque2G Σ}.

  Definition ws_deque_2_inv t :=
    ws_deque_1_inv t.

  Definition ws_deque_2_model t vs : iProp Σ :=
      ∃ slots,
      ws_deque_1_model t (#@{location} <$> slots) ∗
      [∗ list] slot; v ∈ slots; vs,
        slot ↦ᵣ v.

  Definition ws_deque_2_owner t :=
    ws_deque_1_owner t.

  #[global] Instance ws_deque_2_model_timeless t model :
    Timeless (ws_deque_2_model t model).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_deque_2_owner_timeless t :
    Timeless (ws_deque_2_owner t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_deque_2_inv_persistent t ι :
    Persistent (ws_deque_2_inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma ws_deque_2_owner_exclusive t :
    ws_deque_2_owner t -∗
    ws_deque_2_owner t -∗
    False.
  Proof.
    apply ws_deque_1_owner_exclusive.
  Qed.

  Lemma ws_deque_2_create_spec ι :
    {{{
      True
    }}}
      ws_deque_2_create ()
    {{{ t,
      RET t;
      ws_deque_2_inv t ι ∗
      ws_deque_2_model t [] ∗
      ws_deque_2_owner t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (ws_deque_1_create_spec with "[//]") as (t) "(#Hinv & Hmodel & Howner)".
    iSteps. iExists []. iSteps.
  Qed.

  Lemma ws_deque_2_push_spec t ι v :
    <<<
      ws_deque_2_inv t ι ∗
      ws_deque_2_owner t
    | ∀∀ model,
      ws_deque_2_model t model
    >>>
      ws_deque_2_push t v @ ↑ι
    <<<
      ws_deque_2_model t (model ++ [v])
    | RET ();
      ws_deque_2_owner t
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".
    wp_rec. wp_ref slot as "Hslot".
    awp_apply (ws_deque_1_push_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%slots & Hmodel & Hslots)".
    iAaccIntro with "Hmodel"; iIntros "Hmodel !>"; first iSteps.
    iSplitL; last iSteps. rewrite -fmap_snoc. iExists _. iFrameSteps.
  Qed.

  Lemma ws_deque_2_steal_spec t ι :
    <<<
      ws_deque_2_inv t ι
    | ∀∀ model,
      ws_deque_2_model t model
    >>>
      ws_deque_2_steal t @ ↑ι
    <<<
      ws_deque_2_model t (tail model)
    | RET head model;
      True
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_rec.
    awp_smart_apply (ws_deque_1_steal_spec with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%slots & Hmodel & Hslots)".
    iAaccIntro with "Hmodel"; iIntros "Hmodel !>"; first iSteps.
    destruct slots as [| slot slots], vs as [| v vs]; try done.
    - iSplitL; last iSteps. iExists _. auto.
    - iSteps.
  Qed.

  Lemma ws_deque_2_pop_spec t ι :
    <<<
      ws_deque_2_inv t ι ∗
      ws_deque_2_owner t
    | ∀∀ model,
      ws_deque_2_model t model
    >>>
      ws_deque_2_pop t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜model = []⌝ ∗
          ws_deque_2_model t []
      | Some v =>
          ∃ model',
          ⌜model = model' ++ [v]⌝ ∗
          ws_deque_2_model t model'
      end
    | RET o;
      ws_deque_2_owner t
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".
    wp_rec.
    awp_smart_apply (ws_deque_1_pop_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%slots & Hmodel & Hslots)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([w |]).
    - iIntros "(%ws & %Heq & Hmodel) !>".
      destruct slots as [| slot slots _] using rev_ind.
      { rewrite fmap_nil in Heq. edestruct app_cons_not_nil. done. }
      rewrite fmap_app app_inj_tail_iff in Heq. destruct Heq as (<- & <-).
      destruct vs as [| v vs _] using rev_ind.
      { iDestruct (big_sepL2_nil_inv_r with "Hslots") as %?.
        edestruct app_cons_not_nil. done.
      }
      iDestruct (big_sepL2_snoc with "Hslots") as "(Hslots & Hslot)".
      iExists (Some v). iSteps.
    - iIntros "(%Heq & Hmodel) !>".
      apply fmap_nil_inv in Heq as ->. iDestruct (big_sepL2_nil_inv_l with "Hslots") as %->.
      iExists None. iSplitL; last iSteps. iSplit; first iSteps. iExists _. auto.
  Qed.
End ws_deque_2_G.

#[global] Opaque ws_deque_2_create.
#[global] Opaque ws_deque_2_push.
#[global] Opaque ws_deque_2_steal.
#[global] Opaque ws_deque_2_pop.

#[global] Opaque ws_deque_2_inv.
#[global] Opaque ws_deque_2_model.
#[global] Opaque ws_deque_2_owner.
