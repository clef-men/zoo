From iris.proofmode Require Import
  tactics.
From iris.algebra Require Import
  lib.mono_list.
From iris.bi Require Import
  lib.fractional.
From iris.base_logic Require Export
  lib.own.
From iris.prelude Require Import
  options.

Class MonoListG Σ A := {
  #[local] mono_list_G_inG :: inG Σ (mono_listR $ leibnizO A) ;
}.

Definition mono_list_Σ A := #[
  GFunctor (mono_listR $ leibnizO A)
].
#[global] Instance subG_mono_list_Σ Σ A :
  subG (mono_list_Σ A) Σ →
  MonoListG Σ A.
Proof.
  solve_inG.
Qed.

#[local] Definition mono_list_auth_def `{mono_list_G : !MonoListG Σ A} γ q (l : list A) :=
  own γ (●ML{#q} (l : listO (leibnizO A))).
#[local] Definition mono_list_auth_aux :
  seal (@mono_list_auth_def).
Proof. by eexists. Qed.
Definition mono_list_auth :=
  mono_list_auth_aux.(unseal).
#[local] Definition mono_list_auth_unseal : @mono_list_auth = @mono_list_auth_def :=
  mono_list_auth_aux.(seal_eq).
#[global] Arguments mono_list_auth {_ _ _} _ _ _ : assert.

#[local] Definition mono_list_lb_def `{mono_list_G : !MonoListG Σ A} γ (l : list A) :=
  own γ (◯ML (l : listO (leibnizO A))).
#[local] Definition mono_list_lb_aux :
  seal (@mono_list_lb_def).
Proof. by eexists. Qed.
Definition mono_list_lb :=
  mono_list_lb_aux.(unseal).
#[local] Definition mono_list_lb_unseal : @mono_list_lb = @mono_list_lb_def :=
  mono_list_lb_aux.(seal_eq).
#[global] Arguments mono_list_lb {_ _ _} _ _ : assert.

Definition mono_list_pointsto `{mono_list_G : !MonoListG Σ A} γ i a : iProp Σ :=
  ∃ l, ⌜l !! i = Some a⌝ ∗ mono_list_lb γ l.

#[local] Ltac unseal :=
  rewrite
    /mono_list_pointsto ?mono_list_auth_unseal /mono_list_auth_def
    ?mono_list_lb_unseal /mono_list_lb_def.

Section mono_list_G.
  Context `{mono_list_G : !MonoListG Σ A}.
  Implicit Types i : nat.
  Implicit Types a : A.
  Implicit Types l : list A.

  #[global] Instance mono_list_auth_timeless γ q l :
    Timeless (mono_list_auth γ q l).
  Proof.
    unseal. apply _.
  Qed.
  #[global] Instance mono_list_lb_timeless γ l :
    Timeless (mono_list_lb γ l).
  Proof.
    unseal. apply _.
  Qed.
  #[global] Instance mono_list_lb_persistent γ l :
    Persistent (mono_list_lb γ l).
  Proof.
    unseal. apply _.
  Qed.
  #[global] Instance mono_list_pointsto_timeless γ i a :
    Timeless (mono_list_pointsto γ i a).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list_pointsto_persistent γ i a :
    Persistent (mono_list_pointsto γ i a).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_list_auth_fractional γ l :
    Fractional (λ q, mono_list_auth γ q l).
  Proof.
    unseal. intros p q. by rewrite -own_op -mono_list_auth_dfrac_op.
  Qed.
  #[global] Instance mono_list_auth_as_fractional γ q l :
    AsFractional (mono_list_auth γ q l) (λ q, mono_list_auth γ q l) q.
  Proof.
    split; [auto | apply _].
  Qed.

  Lemma mono_list_auth_agree γ q1 q2 l1 l2 :
    mono_list_auth γ q1 l1 -∗
    mono_list_auth γ q2 l2 -∗
    ⌜(q1 + q2 ≤ 1)%Qp ∧ l1 = l2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %?%mono_list_auth_dfrac_op_valid_L.
  Qed.
  Lemma mono_list_auth_exclusive γ l1 l2 :
    mono_list_auth γ 1 l1 -∗
    mono_list_auth γ 1 l2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (mono_list_auth_agree with "H1 H2") as %[]; done.
  Qed.

  Lemma mono_list_auth_lb_valid γ q l1 l2 :
    mono_list_auth γ q l1 -∗
    mono_list_lb γ l2 -∗
    ⌜(q ≤ 1)%Qp ∧ l2 `prefix_of` l1⌝.
  Proof.
    unseal. iIntros "Hauth Hlb".
    by iDestruct (own_valid_2 with "Hauth Hlb") as %?%mono_list_both_dfrac_valid_L.
  Qed.

  Lemma mono_list_lb_valid γ l1 l2 :
    mono_list_lb γ l1 -∗
    mono_list_lb γ l2 -∗
    ⌜l1 `prefix_of` l2 ∨ l2 `prefix_of` l1⌝.
  Proof.
    unseal. iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %?%mono_list_lb_op_valid_L.
  Qed.

  Lemma mono_list_pointsto_agree γ i a1 a2 :
    mono_list_pointsto γ i a1 -∗
    mono_list_pointsto γ i a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iDestruct 1 as (l1 Hl1) "H1". iDestruct 1 as (l2 Hl2) "H2".
    iDestruct (mono_list_lb_valid with "H1 H2") as %Hpre.
    iPureIntro.
    destruct Hpre as [Hpre|Hpre]; eapply prefix_lookup_Some in Hpre; eauto; congruence.
  Qed.

  Lemma mono_list_auth_pointsto_lookup γ q l i a :
    mono_list_auth γ q l -∗
    mono_list_pointsto γ i a -∗
    ⌜l !! i = Some a⌝.
  Proof.
    iIntros "Hauth". iDestruct 1 as (l1 Hl1) "Hl1".
    iDestruct (mono_list_auth_lb_valid with "Hauth Hl1") as %[_ Hpre].
    iPureIntro.
    eapply prefix_lookup_Some in Hpre; eauto; congruence.
  Qed.

  Lemma mono_list_lb_get γ q l :
    mono_list_auth γ q l ⊢
    mono_list_lb γ l.
  Proof.
    intros. unseal. by apply own_mono, mono_list_included.
  Qed.
  Lemma mono_list_lb_le {γ l} l' :
    l' `prefix_of` l →
    mono_list_lb γ l ⊢
    mono_list_lb γ l'.
  Proof.
    unseal. intros. by apply own_mono, mono_list_lb_mono.
  Qed.

  Lemma mono_list_pointsto_get {γ l} i a :
    l !! i = Some a →
    mono_list_lb γ l ⊢
    mono_list_pointsto γ i a.
  Proof.
    iIntros (Hli) "Hl". iExists l. by iFrame.
  Qed.

  Lemma mono_list_alloc l :
    ⊢ |==>
      ∃ γ,
      mono_list_auth γ 1 l.
  Proof.
    unseal. by apply own_alloc, mono_list_auth_valid.
  Qed.

  Lemma mono_list_auth_update {γ l} l' :
    l `prefix_of` l' →
    mono_list_auth γ 1 l ⊢ |==>
    mono_list_auth γ 1 l'.
  Proof.
    iIntros (?) "Hauth".
    unseal. iApply (own_update with "Hauth"). by apply mono_list_update.
  Qed.
  Lemma mono_list_auth_update_app {γ l} l' :
    mono_list_auth γ 1 l ⊢ |==>
    mono_list_auth γ 1 (l ++ l').
  Proof.
    by apply mono_list_auth_update, prefix_app_r.
  Qed.
End mono_list_G.
