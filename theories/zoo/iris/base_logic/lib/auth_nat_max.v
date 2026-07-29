Require Import zoo.prelude.
Require Import zoo.common.math.
Require Import zoo.iris.base_logic.lib.auth_monoi.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthNatMaxG Σ :=
  { #[local] auth_nat_max۰G۰mono۰G :: AuthMonoiG Σ (≤)
  }.

Definition auth_nat_max۰Σ :=
  #[auth_monoi۰Σ (≤)
  ].
#[global] Instance subGｰauth_nat_max۰Σ Σ :
  subG auth_nat_max۰Σ Σ →
  AuthNatMaxG Σ.
Proof.
  solve_inG.
Qed.

Section auth_nat_max۰G.
  Context `{auth_nat_max۰G : !AuthNatMaxG Σ}.

  Implicit Type n m p : nat.

  Definition auth_nat_max۰auth γ dq n :=
    auth_monoi۰auth (≤) γ dq n.
  Definition auth_nat_max۰lb γ n :=
    auth_monoi۰lb (≤) γ n.

  #[global] Instance auth_nat_max۰authｰtimeless γ dq n :
    Timeless (auth_nat_max۰auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max۰lbｰtimeless γ n :
    Timeless (auth_nat_max۰lb γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_max۰authｰpersistent γ n :
    Persistent (auth_nat_max۰auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max۰lbｰpersistent γ n :
    Persistent (auth_nat_max۰lb γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_max۰authｰfractional γ n :
    Fractional (λ q, auth_nat_max۰auth γ (DfracOwn q) n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max۰authｰas_fractional γ q n :
    AsFractional (auth_nat_max۰auth γ (DfracOwn q) n) (λ q, auth_nat_max۰auth γ (DfracOwn q) n) q.
  Proof.
    apply _.
  Qed.

  Lemma auth_nat_maxｰalloc n :
    ⊢ |==>
      ∃ γ,
      auth_nat_max۰auth γ (DfracOwn 1) n.
  Proof.
    apply auth_monoiｰalloc.
  Qed.

  Lemma auth_nat_max۰authｰvalid γ dq a :
    auth_nat_max۰auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_monoi۰authｰvalid.
  Qed.
  Lemma auth_nat_max۰authｰcombine γ dq1 n1 dq2 n2 :
    auth_nat_max۰auth γ dq1 n1 -∗
    auth_nat_max۰auth γ dq2 n2 -∗
      ⌜n1 = n2⌝ ∗
      auth_nat_max۰auth γ (dq1 ⋅ dq2) n1.
  Proof.
    apply: auth_monoi۰authｰcombine.
  Qed.
  Lemma auth_nat_max۰authｰvalidｰ2 γ dq1 n1 dq2 n2 :
    auth_nat_max۰auth γ dq1 n1 -∗
    auth_nat_max۰auth γ dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜n1 = n2⌝.
  Proof.
    apply: auth_monoi۰authｰvalidｰ2.
  Qed.
  Lemma auth_nat_max۰authｰagree γ dq1 n1 dq2 n2 :
    auth_nat_max۰auth γ dq1 n1 -∗
    auth_nat_max۰auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    apply: auth_monoi۰authｰagree.
  Qed.
  Lemma auth_nat_max۰authｰdfracｰne γ1 dq1 n1 γ2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_nat_max۰auth γ1 dq1 n1 -∗
    auth_nat_max۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_monoi۰authｰdfracｰne.
  Qed.
  Lemma auth_nat_max۰authｰne γ1 n1 γ2 dq2 n2 :
    auth_nat_max۰auth γ1 (DfracOwn 1) n1 -∗
    auth_nat_max۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_monoi۰authｰne.
  Qed.
  Lemma auth_nat_max۰authｰexclusive γ n1 dq2 n2 :
    auth_nat_max۰auth γ (DfracOwn 1) n1 -∗
    auth_nat_max۰auth γ dq2 n2 -∗
    False.
  Proof.
    apply: auth_monoi۰authｰexclusive.
  Qed.
  Lemma auth_nat_max۰authｰpersist γ dq n :
    auth_nat_max۰auth γ dq n ⊢ |==>
    auth_nat_max۰auth γ DfracDiscarded n.
  Proof.
    apply auth_monoi۰authｰpersist.
  Qed.

  Lemma auth_nat_max۰lbｰ0 γ :
    ⊢ |==>
      auth_nat_max۰lb γ 0.
  Proof.
    apply auth_monoi۰lbｰinitial.
  Qed.
  Lemma auth_nat_max۰lbｰget γ q n :
    auth_nat_max۰auth γ q n ⊢
    auth_nat_max۰lb γ n.
  Proof.
    apply auth_monoi۰lbｰget.
  Qed.
  Lemma auth_nat_max۰lbｰle {γ n} n' :
    n' ≤ n →
    auth_nat_max۰lb γ n ⊢
    auth_nat_max۰lb γ n'.
  Proof.
    apply auth_monoi۰lbｰmono'.
  Qed.
  Lemma auth_nat_max۰lbｰmax γ n1 n2 :
    auth_nat_max۰lb γ n1 -∗
    auth_nat_max۰lb γ n2 -∗
    auth_nat_max۰lb γ (n1 `max` n2).
  Proof.
    iIntros "Hlb_1 Hlb_2".
    destruct (Nat.max_spec n1 n2) as [(_ & ->) | (_ & ->)] => //.
  Qed.

  Lemma auth_nat_max۰lbｰvalid γ dq n m :
    auth_nat_max۰auth γ dq n -∗
    auth_nat_max۰lb γ m -∗
    ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_monoi۰lbｰvalid with "Hauth Hlb") as %Hrtc.
    rewrite preorderｰrtc in Hrtc. iSteps.
  Qed.

  Lemma auth_nat_maxｰupdate {γ n} n' :
    n ≤ n' →
    auth_nat_max۰auth γ (DfracOwn 1) n ⊢ |==>
    auth_nat_max۰auth γ (DfracOwn 1) n'.
  Proof.
    apply auth_monoiｰupdate'.
  Qed.
End auth_nat_max۰G.

#[global] Opaque auth_nat_max۰auth.
#[global] Opaque auth_nat_max۰lb.
