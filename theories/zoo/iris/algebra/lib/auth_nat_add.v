Require Import iris.algebra.proofmode_classes.

Require Import zoo.prelude.
Require Export zoo.iris.algebra.base.
Require Import zoo.iris.algebra.auth.
Require Import zoo.iris.algebra.lib.nat_add.
Require Import zoo.options.

Implicit Type n m : nat.

Section sidx.
  Context {SI : sidx}.

  Definition auth_nat_add :=
    auth nat_add.
  Definition auth_nat_add۰R :=
    authR nat_add۰UR.
  Definition auth_nat_add۰UR :=
    authUR nat_add۰UR.

  Please Definition auth_nat_add۰auth dq n : auth_nat_add۰UR :=
    ●{dq} NatAdd n.
  Please Definition auth_nat_add۰frag m : auth_nat_add۰UR :=
    ◯ NatAdd m.

  #[global] Instance auth_nat_add۰authｰinj :
    Inj2 (=) (=) (≡) auth_nat_add۰auth.
  Proof.
    intros dq1 n1 dq2 n2 (-> & [= ->])%(inj2 auth_auth) => //.
  Qed.
  #[global] Instance auth_nat_add۰fragｰinj :
    Inj (=) (≡) auth_nat_add۰frag.
  Proof.
    intros n1 n2 [= ->]%(inj auth_frag) => //.
  Qed.

  #[global] Instance auth_nat_addｰcmra_discrete :
    CmraDiscrete auth_nat_add۰R.
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_add۰authｰcore_id n :
    CoreId (auth_nat_add۰auth DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_add۰fragｰcore_id :
    CoreId (auth_nat_add۰frag 0).
  Proof.
    apply _.
  Qed.

  Lemma auth_nat_add۰authｰdfracｰop dq1 dq2 n :
    auth_nat_add۰auth (dq1 ⋅ dq2) n ≡ auth_nat_add۰auth dq1 n ⋅ auth_nat_add۰auth dq2 n.
  Proof.
    apply auth_auth_dfrac_op.
  Qed.
  #[global] Instance auth_nat_add۰authｰdfracｰis_op dq dq1 dq2 n :
    IsOp dq dq1 dq2 →
    IsOp' (auth_nat_add۰auth dq n) (auth_nat_add۰auth dq1 n) (auth_nat_add۰auth dq2 n).
  Proof.
    apply _.
  Qed.

  Lemma auth_nat_add۰fragｰop m1 m2 :
    auth_nat_add۰frag (m1 + m2) ≡ auth_nat_add۰frag m1 ⋅ auth_nat_add۰frag m2.
  Proof.
    done.
  Qed.
  #[global] Instance auth_nat_add۰fragｰis_op m1 m2 :
    IsOp' (auth_nat_add۰frag (m1 + m2)) (auth_nat_add۰frag m1) (auth_nat_add۰frag m2).
  Proof.
    apply _.
  Qed.

  Lemma auth_nat_add۰authｰdfracｰvalid dq n :
    ✓ auth_nat_add۰auth dq n ↔
    ✓ dq.
  Proof.
    rewrite auth_auth_dfrac_valid.
    naive.
  Qed.
  Lemma auth_nat_add۰authｰvalid n :
    ✓ auth_nat_add۰auth (DfracOwn 1) n.
  Proof.
    rewrite auth_nat_add۰authｰdfracｰvalid //.
  Qed.

  Lemma auth_nat_add۰authｰdfracｰopｰvalid dq1 n1 dq2 n2 :
    ✓ (auth_nat_add۰auth dq1 n1 ⋅ auth_nat_add۰auth dq2 n2) →
      ✓ (dq1 ⋅ dq2) ∧
      n1 = n2.
  Proof.
    rewrite auth_auth_dfrac_op_valid.
    naive.
  Qed.
  Lemma auth_nat_add۰authｰopｰvalid n1 n2 :
    ✓ (auth_nat_add۰auth (DfracOwn 1) n1 ⋅ auth_nat_add۰auth (DfracOwn 1) n2) →
    False.
  Proof.
    apply auth_auth_op_valid.
  Qed.

  Lemma auth_nat_addｰbothｰdfracｰvalid dq n m :
    ✓ (auth_nat_add۰auth dq n ⋅ auth_nat_add۰frag m) ↔
      ✓ dq ∧
      m ≤ n.
  Proof.
    rewrite auth_both_dfrac_valid_discrete nat_addｰincluded /=.
    naive.
  Qed.
  Lemma auth_nat_addｰbothｰvalid n m :
    ✓ (auth_nat_add۰auth (DfracOwn 1) n ⋅ auth_nat_add۰frag m) ↔
    m ≤ n.
  Proof.
    rewrite auth_nat_addｰbothｰdfracｰvalid dfrac_valid_own.
    naive.
  Qed.

  Lemma auth_nat_add۰fragｰmono m1 m2 :
    m1 ≤ m2 →
    auth_nat_add۰frag m1 ≼ auth_nat_add۰frag m2.
  Proof.
    intros.
    apply auth_frag_mono, nat_addｰincluded => //.
  Qed.

  Lemma auth_nat_add۰authｰpersist dq n :
    auth_nat_add۰auth dq n ~~> auth_nat_add۰auth DfracDiscarded n.
  Proof.
    apply auth_update_auth_persist.
  Qed.

  Lemma auth_nat_addｰupdateｰincrease {n1} n2 :
    auth_nat_add۰auth (DfracOwn 1) n1 ~~> auth_nat_add۰auth (DfracOwn 1) (n1 + n2) ⋅ auth_nat_add۰frag n2.
  Proof.
    intros.
    apply auth_update_alloc, nat_addｰlocal_update => /=. lia.
  Qed.
  Lemma auth_nat_addｰupdateｰdecrease n m :
    m ≤ n →
    auth_nat_add۰auth (DfracOwn 1) n ⋅ auth_nat_add۰frag m ~~> auth_nat_add۰auth (DfracOwn 1) (n - m).
  Proof.
    intros.
    apply auth_update_dealloc, nat_addｰlocal_update => /=. lia.
  Qed.
End sidx.

Please opacify.
