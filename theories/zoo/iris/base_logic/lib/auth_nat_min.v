From zoo Require Import
  prelude.
From zoo.common Require Import
  math
  relations.
From zoo.iris.base_logic Require Import
  lib.auth_mono.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class AuthNatMinG Σ := {
  #[local] auth_nat_min_G_mono_G :: AuthMonoG Σ ge ;
}.

Definition auth_nat_min_Σ := #[
  auth_mono_Σ ge
].
#[global] Instance subG_auth_nat_min_Σ Σ :
  subG auth_nat_min_Σ Σ →
  AuthNatMinG Σ.
Proof.
  solve_inG.
Qed.

Section auth_nat_min_G.
  Context `{auth_nat_min_G : !AuthNatMinG Σ}.

  Implicit Types n m p : nat.

  Definition auth_nat_min_auth γ dq n :=
    auth_mono_auth ge γ dq n.
  Definition auth_nat_min_ub γ n :=
    auth_mono_lb ge γ n.

  #[global] Instance auth_nat_min_auth_timeless γ dq n :
    Timeless (auth_nat_min_auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min_auth_persistent γ n :
    Persistent (auth_nat_min_auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min_ub_timeless γ n :
    Timeless (auth_nat_min_ub γ n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min_ub_persistent γ n :
    Persistent (auth_nat_min_ub γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_min_auth_fractional γ n :
    Fractional (λ q, auth_nat_min_auth γ (DfracOwn q) n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min_auth_as_fractional γ q n :
    AsFractional (auth_nat_min_auth γ (DfracOwn q) n) (λ q, auth_nat_min_auth γ (DfracOwn q) n) q.
  Proof.
    apply _.
  Qed.

  Lemma auth_nat_min_alloc n :
    ⊢ |==>
      ∃ γ,
      auth_nat_min_auth γ (DfracOwn 1) n.
  Proof.
    apply auth_mono_alloc.
  Qed.

  Lemma auth_nat_min_auth_valid γ dq a :
    auth_nat_min_auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono_auth_valid.
  Qed.
  Lemma auth_nat_min_auth_combine γ dq1 n1 dq2 n2 :
    auth_nat_min_auth γ dq1 n1 -∗
    auth_nat_min_auth γ dq2 n2 -∗
      ⌜n1 = n2⌝ ∗
      auth_nat_min_auth γ (dq1 ⋅ dq2) n1.
  Proof.
    apply: auth_mono_auth_combine.
  Qed.
  Lemma auth_nat_min_auth_valid_2 γ dq1 n1 dq2 n2 :
    auth_nat_min_auth γ dq1 n1 -∗
    auth_nat_min_auth γ dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜n1 = n2⌝.
  Proof.
    apply: auth_mono_auth_valid_2.
  Qed.
  Lemma auth_nat_min_auth_agree γ dq1 n1 dq2 n2 :
    auth_nat_min_auth γ dq1 n1 -∗
    auth_nat_min_auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    apply: auth_mono_auth_agree.
  Qed.
  Lemma auth_nat_min_auth_dfrac_ne γ1 dq1 n1 γ2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_nat_min_auth γ1 dq1 n1 -∗
    auth_nat_min_auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_dfrac_ne.
  Qed.
  Lemma auth_nat_min_auth_ne γ1 n1 γ2 dq2 n2 :
    auth_nat_min_auth γ1 (DfracOwn 1) n1 -∗
    auth_nat_min_auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_ne.
  Qed.
  Lemma auth_nat_min_auth_exclusive γ n1 dq2 n2 :
    auth_nat_min_auth γ (DfracOwn 1) n1 -∗
    auth_nat_min_auth γ dq2 n2 -∗
    False.
  Proof.
    apply: auth_mono_auth_exclusive.
  Qed.
  Lemma auth_nat_min_auth_persist γ dq n :
    auth_nat_min_auth γ dq n ⊢ |==>
    auth_nat_min_auth γ DfracDiscarded n.
  Proof.
    apply auth_mono_auth_persist.
  Qed.

  Lemma auth_nat_min_ub_get γ q n :
    auth_nat_min_auth γ q n ⊢
    auth_nat_min_ub γ n.
  Proof.
    apply auth_mono_lb_get.
  Qed.
  Lemma auth_nat_min_ub_le {γ n} n' :
    n ≤ n' →
    auth_nat_min_ub γ n ⊢
    auth_nat_min_ub γ n'.
  Proof.
    intros. apply auth_mono_lb_mono'. lia.
  Qed.

  Lemma auth_nat_min_ub_valid γ dq n m :
    auth_nat_min_auth γ dq n -∗
    auth_nat_min_ub γ m -∗
    ⌜n ≤ m⌝.
  Proof.
    iIntros "Hauth Hub".
    iDestruct (auth_mono_lb_valid with "Hauth Hub") as %Hrtc.
    rewrite preorder_rtc in Hrtc. iSteps.
  Qed.

  Lemma auth_nat_min_update {γ n} n' :
    n' ≤ n →
    auth_nat_min_auth γ (DfracOwn 1) n ⊢ |==>
    auth_nat_min_auth γ (DfracOwn 1) n'.
  Proof.
    intros. apply auth_mono_update'. lia.
  Qed.
End auth_nat_min_G.

#[global] Opaque auth_nat_min_auth.
#[global] Opaque auth_nat_min_ub.
