Require Import zoo.prelude.
Require Import zoo.common.math.
Require Import zoo.common.relations.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthNatMinG Σ :=
  { #[local] auth_nat_min۰G۰mono۰G :: AuthMonoG Σ ge
  }.

Definition auth_nat_min۰Σ :=
  #[auth_mono۰Σ ge
  ].
#[global] Instance subGｰauth_nat_min۰Σ Σ :
  subG auth_nat_min۰Σ Σ →
  AuthNatMinG Σ.
Proof.
  solve_inG.
Qed.

Section auth_nat_min۰G.
  Context `{auth_nat_min۰G : !AuthNatMinG Σ}.

  Implicit Type n m p : nat.

  Definition auth_nat_min۰auth γ dq n :=
    auth_mono۰auth ge γ dq n.
  Definition auth_nat_min۰ub γ n :=
    auth_mono۰lb ge γ n.

  #[global] Instance auth_nat_min۰authｰtimeless γ dq n :
    Timeless (auth_nat_min۰auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min۰ubｰtimeless γ n :
    Timeless (auth_nat_min۰ub γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_min۰authｰpersistent γ n :
    Persistent (auth_nat_min۰auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min۰ubｰpersistent γ n :
    Persistent (auth_nat_min۰ub γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_min۰authｰfractional γ n :
    Fractional (λ q, auth_nat_min۰auth γ (DfracOwn q) n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min۰authｰas_fractional γ q n :
    AsFractional (auth_nat_min۰auth γ (DfracOwn q) n) (λ q, auth_nat_min۰auth γ (DfracOwn q) n) q.
  Proof.
    apply _.
  Qed.

  Lemma auth_nat_minｰalloc n :
    ⊢ |==>
      ∃ γ,
      auth_nat_min۰auth γ (DfracOwn 1) n.
  Proof.
    apply auth_monoｰalloc.
  Qed.

  Lemma auth_nat_min۰authｰvalid γ dq a :
    auth_nat_min۰auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono۰authｰvalid.
  Qed.
  Lemma auth_nat_min۰authｰcombine γ dq1 n1 dq2 n2 :
    auth_nat_min۰auth γ dq1 n1 -∗
    auth_nat_min۰auth γ dq2 n2 -∗
      ⌜n1 = n2⌝ ∗
      auth_nat_min۰auth γ (dq1 ⋅ dq2) n1.
  Proof.
    apply: auth_mono۰authｰcombine.
  Qed.
  Lemma auth_nat_min۰authｰvalidｰ2 γ dq1 n1 dq2 n2 :
    auth_nat_min۰auth γ dq1 n1 -∗
    auth_nat_min۰auth γ dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜n1 = n2⌝.
  Proof.
    apply: auth_mono۰authｰvalidｰ2.
  Qed.
  Lemma auth_nat_min۰authｰagree γ dq1 n1 dq2 n2 :
    auth_nat_min۰auth γ dq1 n1 -∗
    auth_nat_min۰auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    apply: auth_mono۰authｰagree.
  Qed.
  Lemma auth_nat_min۰authｰdfracｰne γ1 dq1 n1 γ2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_nat_min۰auth γ1 dq1 n1 -∗
    auth_nat_min۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰authｰdfracｰne.
  Qed.
  Lemma auth_nat_min۰authｰne γ1 n1 γ2 dq2 n2 :
    auth_nat_min۰auth γ1 (DfracOwn 1) n1 -∗
    auth_nat_min۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰authｰne.
  Qed.
  Lemma auth_nat_min۰authｰexclusive γ n1 dq2 n2 :
    auth_nat_min۰auth γ (DfracOwn 1) n1 -∗
    auth_nat_min۰auth γ dq2 n2 -∗
    False.
  Proof.
    apply: auth_mono۰authｰexclusive.
  Qed.
  Lemma auth_nat_min۰authｰpersist γ dq n :
    auth_nat_min۰auth γ dq n ⊢ |==>
    auth_nat_min۰auth γ DfracDiscarded n.
  Proof.
    apply auth_mono۰authｰpersist.
  Qed.

  Lemma auth_nat_min۰ubｰget γ q n :
    auth_nat_min۰auth γ q n ⊢
    auth_nat_min۰ub γ n.
  Proof.
    apply auth_mono۰lbｰget.
  Qed.
  Lemma auth_nat_min۰ubｰle {γ n} n' :
    n ≤ n' →
    auth_nat_min۰ub γ n ⊢
    auth_nat_min۰ub γ n'.
  Proof.
    intros. apply auth_mono۰lbｰmono'. lia.
  Qed.

  Lemma auth_nat_min۰ubｰvalid γ dq n m :
    auth_nat_min۰auth γ dq n -∗
    auth_nat_min۰ub γ m -∗
    ⌜n ≤ m⌝.
  Proof.
    iIntros "Hauth Hub".
    iDestruct (auth_mono۰lbｰvalid with "Hauth Hub") as %Hrtc.
    rewrite preorderｰrtc in Hrtc. iSteps.
  Qed.

  Lemma auth_nat_minｰupdate {γ n} n' :
    n' ≤ n →
    auth_nat_min۰auth γ (DfracOwn 1) n ⊢ |==>
    auth_nat_min۰auth γ (DfracOwn 1) n'.
  Proof.
    intros. apply auth_monoｰupdate'. lia.
  Qed.
End auth_nat_min۰G.

#[global] Opaque auth_nat_min۰auth.
#[global] Opaque auth_nat_min۰ub.
