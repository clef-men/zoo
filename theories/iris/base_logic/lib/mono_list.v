From zebre Require Import
  prelude.
From zebre.common Require Import
  relations.
From zebre.iris.base_logic Require Export
  lib.base.
From zebre.iris.base_logic Require Import
  lib.auth_mono.
From zebre.iris Require Import
  diaframe.
From zebre Require Import
  options.

Class MonoListG Σ A := {
  #[local] mono_list_G_mono_G :: AuthMonoG Σ (A := leibnizO (list A)) prefix ;
}.

Definition mono_list_Σ A := #[
  auth_mono_Σ (A := leibnizO (list A)) prefix
].
#[global] Instance subG_mono_list_Σ Σ A :
  subG (mono_list_Σ A) Σ →
  MonoListG Σ A.
Proof.
  solve_inG.
Qed.

Section mono_list_G.
  Context `{mono_list_G : !MonoListG Σ A}.

  Implicit Types i : nat.
  Implicit Types a : A.
  Implicit Types l : list A.

  Definition mono_list_auth γ dq l :=
    auth_mono_auth (A := leibnizO (list A)) prefix γ dq l.
  Definition mono_list_lb γ l :=
    auth_mono_lb (A := leibnizO (list A)) prefix γ l.
  Definition mono_list_elem γ i a : iProp Σ :=
    ∃ l,
    ⌜l !! i = Some a⌝ ∗
    mono_list_lb γ l.

  #[global] Instance mono_list_auth_timeless γ dq l :
    Timeless (mono_list_auth γ dq l).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list_lb_timeless γ l :
    Timeless (mono_list_lb γ l).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list_lb_persistent γ l :
    Persistent (mono_list_lb γ l).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list_elem_timeless γ i a :
    Timeless (mono_list_elem γ i a).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list_elem_persistent γ i a :
    Persistent (mono_list_elem γ i a).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_list_auth_fractional γ l :
    Fractional (λ q, mono_list_auth γ (DfracOwn q) l).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list_auth_as_fractional γ q l :
    AsFractional (mono_list_auth γ (DfracOwn q) l) (λ q, mono_list_auth γ (DfracOwn q) l) q.
  Proof.
    apply _.
  Qed.

  Lemma mono_list_alloc l :
    ⊢ |==>
      ∃ γ,
      mono_list_auth γ (DfracOwn 1) l.
  Proof.
    apply auth_mono_alloc.
  Qed.

  Lemma mono_list_auth_valid γ dq l :
    mono_list_auth γ dq l ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono_auth_valid.
  Qed.
  Lemma mono_list_auth_combine γ dq1 l1 dq2 l2 :
    mono_list_auth γ dq1 l1 -∗
    mono_list_auth γ dq2 l2 -∗
      mono_list_auth γ (dq1 ⋅ dq2) l1 ∗
      ⌜l1 = l2⌝.
  Proof.
    apply: auth_mono_auth_combine.
  Qed.
  Lemma mono_list_auth_valid_2 γ dq1 l1 dq2 l2 :
    mono_list_auth γ dq1 l1 -∗
    mono_list_auth γ dq2 l2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ l1 = l2⌝.
  Proof.
    apply: auth_mono_auth_valid_2.
  Qed.
  Lemma mono_list_auth_agree γ dq1 l1 dq2 l2 :
    mono_list_auth γ dq1 l1 -∗
    mono_list_auth γ dq2 l2 -∗
    ⌜l1 = l2⌝.
  Proof.
    apply: auth_mono_auth_agree.
  Qed.
  Lemma mono_list_auth_dfrac_ne γ1 dq1 l1 γ2 dq2 l2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    mono_list_auth γ1 dq1 l1 -∗
    mono_list_auth γ2 dq2 l2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_dfrac_ne.
  Qed.
  Lemma mono_list_auth_ne γ1 l1 γ2 dq2 l2 :
    mono_list_auth γ1 (DfracOwn 1) l1 -∗
    mono_list_auth γ2 dq2 l2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_ne.
  Qed.
  Lemma mono_list_auth_exclusive γ l1 l2 :
    mono_list_auth γ (DfracOwn 1) l1 -∗
    mono_list_auth γ (DfracOwn 1) l2 -∗
    False.
  Proof.
    apply: auth_mono_auth_exclusive.
  Qed.
  Lemma mono_list_auth_persist γ dq l :
    mono_list_auth γ dq l ⊢ |==>
    mono_list_auth γ DfracDiscarded l.
  Proof.
    apply auth_mono_auth_persist.
  Qed.

  Lemma mono_list_lb_get γ q l :
    mono_list_auth γ q l ⊢
    mono_list_lb γ l.
  Proof.
    apply auth_mono_lb_get.
  Qed.
  Lemma mono_list_elem_get {γ l} i a :
    l !! i = Some a →
    mono_list_lb γ l ⊢
    mono_list_elem γ i a.
  Proof.
    iSteps.
  Qed.

  Lemma mono_list_lb_mono {γ l} l' :
    l' `prefix_of` l →
    mono_list_lb γ l ⊢
    mono_list_lb γ l'.
  Proof.
    apply auth_mono_lb_mono'.
  Qed.

  Lemma mono_list_lb_valid γ dq l l' :
    mono_list_auth γ dq l -∗
    mono_list_lb γ l' -∗
    ⌜l' `prefix_of` l⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %Hl'.
    rewrite preorder_rtc in Hl'. iSteps.
  Qed.
  Lemma mono_list_lookup γ q l i a :
    mono_list_auth γ q l -∗
    mono_list_elem γ i a -∗
    ⌜l !! i = Some a⌝.
  Proof.
    iIntros "Hauth (%l1 & %Hlookup & Hl1)".
    iDestruct (mono_list_lb_valid with "Hauth Hl1") as %(l2 & ->).
    iPureIntro. apply lookup_app_l_Some. done.
  Qed.

  Lemma mono_list_update {γ l} l' :
    l `prefix_of` l' →
    mono_list_auth γ (DfracOwn 1) l ⊢ |==>
    mono_list_auth γ (DfracOwn 1) l'.
  Proof.
    apply auth_mono_update'.
  Qed.
  Lemma mono_list_update_app {γ l} l' :
    mono_list_auth γ (DfracOwn 1) l ⊢ |==>
    mono_list_auth γ (DfracOwn 1) (l ++ l').
  Proof.
    apply mono_list_update, prefix_app_r. done.
  Qed.
End mono_list_G.

#[global] Opaque mono_list_auth.
#[global] Opaque mono_list_lb.
#[global] Opaque mono_list_elem.
