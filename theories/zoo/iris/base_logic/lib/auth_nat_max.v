From zoo Require Import
  prelude.
From zoo.common Require Import
  math.
From zoo.iris.base_logic Require Import
  lib.auth_monoi.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class AuthNatMaxG Σ := {
  #[local] auth_nat_max_G_mono_G :: AuthMonoiG Σ (≤) ;
}.

Definition auth_nat_max_Σ := #[
  auth_monoi_Σ (≤)
].
#[global] Instance subG_auth_nat_max_Σ Σ :
  subG auth_nat_max_Σ Σ →
  AuthNatMaxG Σ.
Proof.
  solve_inG.
Qed.

Section auth_nat_max_G.
  Context `{auth_nat_max_G : !AuthNatMaxG Σ}.

  Implicit Types n m p : nat.

  Definition auth_nat_max_auth γ dq n :=
    auth_monoi_auth (≤) γ dq n.
  Definition auth_nat_max_lb γ n :=
    auth_monoi_lb (≤) γ n.

  #[global] Instance auth_nat_max_auth_timeless γ dq n :
    Timeless (auth_nat_max_auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max_lb_timeless γ n :
    Timeless (auth_nat_max_lb γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_max_auth_persistent γ n :
    Persistent (auth_nat_max_auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max_lb_persistent γ n :
    Persistent (auth_nat_max_lb γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_max_auth_fractional γ n :
    Fractional (λ q, auth_nat_max_auth γ (DfracOwn q) n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max_auth_as_fractional γ q n :
    AsFractional (auth_nat_max_auth γ (DfracOwn q) n) (λ q, auth_nat_max_auth γ (DfracOwn q) n) q.
  Proof.
    apply _.
  Qed.

  Lemma auth_nat_max_alloc n :
    ⊢ |==>
      ∃ γ,
      auth_nat_max_auth γ (DfracOwn 1) n.
  Proof.
    apply auth_monoi_alloc.
  Qed.

  Lemma auth_nat_max_auth_valid γ dq a :
    auth_nat_max_auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_monoi_auth_valid.
  Qed.
  Lemma auth_nat_max_auth_combine γ dq1 n1 dq2 n2 :
    auth_nat_max_auth γ dq1 n1 -∗
    auth_nat_max_auth γ dq2 n2 -∗
      ⌜n1 = n2⌝ ∗
      auth_nat_max_auth γ (dq1 ⋅ dq2) n1.
  Proof.
    apply: auth_monoi_auth_combine.
  Qed.
  Lemma auth_nat_max_auth_valid_2 γ dq1 n1 dq2 n2 :
    auth_nat_max_auth γ dq1 n1 -∗
    auth_nat_max_auth γ dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜n1 = n2⌝.
  Proof.
    apply: auth_monoi_auth_valid_2.
  Qed.
  Lemma auth_nat_max_auth_agree γ dq1 n1 dq2 n2 :
    auth_nat_max_auth γ dq1 n1 -∗
    auth_nat_max_auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    apply: auth_monoi_auth_agree.
  Qed.
  Lemma auth_nat_max_auth_dfrac_ne γ1 dq1 n1 γ2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_nat_max_auth γ1 dq1 n1 -∗
    auth_nat_max_auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_monoi_auth_dfrac_ne.
  Qed.
  Lemma auth_nat_max_auth_ne γ1 n1 γ2 dq2 n2 :
    auth_nat_max_auth γ1 (DfracOwn 1) n1 -∗
    auth_nat_max_auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_monoi_auth_ne.
  Qed.
  Lemma auth_nat_max_auth_exclusive γ n1 dq2 n2 :
    auth_nat_max_auth γ (DfracOwn 1) n1 -∗
    auth_nat_max_auth γ dq2 n2 -∗
    False.
  Proof.
    apply: auth_monoi_auth_exclusive.
  Qed.
  Lemma auth_nat_max_auth_persist γ dq n :
    auth_nat_max_auth γ dq n ⊢ |==>
    auth_nat_max_auth γ DfracDiscarded n.
  Proof.
    apply auth_monoi_auth_persist.
  Qed.

  Lemma auth_nat_max_lb_0 γ :
    ⊢ |==>
      auth_nat_max_lb γ 0.
  Proof.
    apply auth_monoi_lb_initial.
  Qed.
  Lemma auth_nat_max_lb_get γ q n :
    auth_nat_max_auth γ q n ⊢
    auth_nat_max_lb γ n.
  Proof.
    apply auth_monoi_lb_get.
  Qed.
  Lemma auth_nat_max_lb_le {γ n} n' :
    n' ≤ n →
    auth_nat_max_lb γ n ⊢
    auth_nat_max_lb γ n'.
  Proof.
    apply auth_monoi_lb_mono'.
  Qed.

  Lemma auth_nat_max_lb_valid γ dq n m :
    auth_nat_max_auth γ dq n -∗
    auth_nat_max_lb γ m -∗
    ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_monoi_lb_valid with "Hauth Hlb") as %Hrtc.
    rewrite preorder_rtc in Hrtc. iSteps.
  Qed.

  Lemma auth_nat_max_update {γ n} n' :
    n ≤ n' →
    auth_nat_max_auth γ (DfracOwn 1) n ⊢ |==>
    auth_nat_max_auth γ (DfracOwn 1) n'.
  Proof.
    apply auth_monoi_update'.
  Qed.
End auth_nat_max_G.

#[global] Opaque auth_nat_max_auth.
#[global] Opaque auth_nat_max_lb.
