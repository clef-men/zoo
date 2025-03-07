From zoo Require Import
  prelude.
From zoo.common Require Import
  relations.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris.base_logic Require Import
  lib.auth_mono.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
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
  Definition mono_list_at γ i a : iProp Σ :=
    ∃ l,
    ⌜l !! i = Some a⌝ ∗
    mono_list_lb γ l.
  Definition mono_list_elem γ a : iProp Σ :=
    ∃ i,
    mono_list_at γ i a.

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
  #[global] Instance mono_list_at_timeless γ i a :
    Timeless (mono_list_at γ i a).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list_at_persistent γ i a :
    Persistent (mono_list_at γ i a).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list_elem_timeless γ a :
    Timeless (mono_list_elem γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list_elem_persistent γ a :
    Persistent (mono_list_elem γ a).
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
      ⌜l1 = l2⌝ ∗
      mono_list_auth γ (dq1 ⋅ dq2) l1.
  Proof.
    apply: auth_mono_auth_combine.
  Qed.
  Lemma mono_list_auth_valid_2 γ dq1 l1 dq2 l2 :
    mono_list_auth γ dq1 l1 -∗
    mono_list_auth γ dq2 l2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜l1 = l2⌝.
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
  Lemma mono_list_auth_exclusive γ l1 dq2 l2 :
    mono_list_auth γ (DfracOwn 1) l1 -∗
    mono_list_auth γ dq2 l2 -∗
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
  Lemma mono_list_at_get {γ q l} i a :
    l !! i = Some a →
    mono_list_auth γ q l ⊢
    mono_list_at γ i a.
  Proof.
    rewrite mono_list_lb_get. iSteps.
  Qed.
  Lemma mono_list_elem_get {γ q l} a :
    a ∈ l →
    mono_list_auth γ q l ⊢
    mono_list_elem γ a.
  Proof.
    intros (i & Hlookup)%elem_of_list_lookup.
    rewrite mono_list_at_get //. iSteps.
  Qed.

  Lemma mono_list_lb_mono {γ l} l' :
    l' `prefix_of` l →
    mono_list_lb γ l ⊢
    mono_list_lb γ l'.
  Proof.
    apply auth_mono_lb_mono'.
  Qed.

  Lemma mono_list_lb_valid γ dq l1 l2 :
    mono_list_auth γ dq l1 -∗
    mono_list_lb γ l2 -∗
    ⌜l2 `prefix_of` l1⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %Hl2.
    rewrite preorder_rtc in Hl2. iSteps.
  Qed.
  Lemma mono_list_lb_agree γ l1 l2 :
    mono_list_lb γ l1 -∗
    mono_list_lb γ l2 -∗
      ∃ l,
      ⌜l1 `prefix_of` l⌝ ∧
      ⌜l2 `prefix_of` l⌝.
  Proof.
    iIntros "Hlb1 Hlb2".
    iDestruct (auth_mono_lb_agree with "Hlb1 Hlb2") as %(l & Hl1 & Hl2).
    rewrite !preorder_rtc in Hl1 Hl2. iSteps.
  Qed.
  Lemma mono_list_at_valid γ q l i a :
    mono_list_auth γ q l -∗
    mono_list_at γ i a -∗
    ⌜l !! i = Some a⌝.
  Proof.
    iIntros "Hauth (%l1 & %Hlookup & Hlb)".
    iDestruct (mono_list_lb_valid with "Hauth Hlb") as %(l2 & ->).
    iPureIntro. apply lookup_app_l_Some. done.
  Qed.
  Lemma mono_list_at_agree γ i a1 a2 :
    mono_list_at γ i a1 -∗
    mono_list_at γ i a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "(%l1 & %Hlookup1 & Hlb1) (%l2 & %Hlookup2 & Hlb2)".
    iDestruct (mono_list_lb_agree with "Hlb1 Hlb2") as %(l & Hl1 & Hl2).
    edestruct (prefix_weak_total l1 l2); [done.. | |].
    1: erewrite (prefix_lookup_Some l1 l2) in Hlookup2; [| done..].
    2: erewrite (prefix_lookup_Some l2 l1) in Hlookup1; [| done..].
    all: naive_solver.
  Qed.
  Lemma mono_list_elem_valid γ q l a :
    mono_list_auth γ q l -∗
    mono_list_elem γ a -∗
    ⌜a ∈ l⌝.
  Proof.
    iIntros "Hauth (%i & Hat)".
    iDestruct (mono_list_at_valid with "Hauth Hat") as %Hlookup.
    iPureIntro. apply elem_of_list_lookup. naive_solver.
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
  Lemma mono_list_update_snoc {γ l} a :
    mono_list_auth γ (DfracOwn 1) l ⊢ |==>
    mono_list_auth γ (DfracOwn 1) (l ++ [a]).
  Proof.
    apply mono_list_update_app.
  Qed.
End mono_list_G.

#[global] Opaque mono_list_auth.
#[global] Opaque mono_list_lb.
#[global] Typeclasses Opaque mono_list_at.
#[global] Typeclasses Opaque mono_list_elem.
