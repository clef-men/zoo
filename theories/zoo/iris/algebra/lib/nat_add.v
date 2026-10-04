Require Import iris.algebra.proofmode_classes.

Require Import zoo.prelude.
Require Export zoo.iris.algebra.base.
Require Import zoo.options.

Record nat_add := NatAdd
  { nat_add۰car : nat
  }.
Add Printing Constructor nat_add.

Canonical nat_add۰O {SI : sidx} :=
  leibnizO nat_add.

Implicit Type n m p : nat.
Implicit Type x y : nat_add.

Section sidx.
  Context {SI : sidx}.

  #[local] Instance nat_addｰvalid : Valid nat_add :=
    λ _,
      True.
  #[local] Instance nat_addｰvalidN : ValidN nat_add :=
    λ _ _,
      True.
  #[local] Instance nat_addｰpcore : PCore nat_add :=
    λ _,
      Some $ NatAdd 0.
  #[local] Instance nat_addｰop : Op nat_add :=
    λ x1 x2,
      NatAdd $ nat_add۰car x1 + nat_add۰car x2.
  #[local] Instance natｰunit : Unit nat_add :=
    NatAdd 0.

  Lemma nat_addｰopｰeq n1 n2 :
    NatAdd n1 ⋅ NatAdd n2 = NatAdd (n1 + n2).
  Proof.
    done.
  Qed.

  Lemma nat_addｰincluded x1 x2 :
    x1 ≼ x2 ↔
    nat_add۰car x1 ≤ nat_add۰car x2.
  Proof.
    split.
    - intros (x & ->) => /=. lia.
    - move: x1 x2 => [n1] [n2] => /=.
      rewrite Nat.le_sum => [[n ->]].
      exists (NatAdd n) => //.
  Qed.

  Lemma nat_addｰra_mixin :
    RAMixin nat_add.
  Proof.
    apply ra_total_mixin.
    all: apply _ || auto.
    - intros [n1] [n2] [n3].
      rewrite !nat_addｰopｰeq Nat.add_assoc //.
    - intros [n1] [n2].
      rewrite nat_addｰopｰeq Nat.add_comm //.
    - intros [n].
      rewrite nat_addｰopｰeq //.
    - intros [n1] [n2].
      exists (NatAdd 0) => //.
  Qed.
  Canonical nat_add۰R :=
    discreteR nat_add nat_addｰra_mixin.
  #[global] Instance nat_addｰcmra_discrete :
    CmraDiscrete nat_add۰R.
  Proof.
    apply discrete_cmra_discrete.
  Qed.

  Lemma nat_addｰucmra_mixin :
    UcmraMixin nat_add.
  Proof.
    split => //.
    intros [n] => //.
  Qed.
  Canonical nat_add۰UR :=
    Ucmra nat_add nat_addｰucmra_mixin.

  #[global] Instance nat_addｰcancelable x :
    Cancelable x.
  Proof.
    intros idx [n1] [n2] _.
    move: x => [n].
    rewrite !nat_addｰopｰeq => [=].
    rewrite Nat.add_cancel_l => -> //.
  Qed.

  Lemma nat_addｰlocal_update x1 y1 x2 y2 :
    nat_add۰car x1 + nat_add۰car y2 = nat_add۰car x2 + nat_add۰car y1 →
    (x1, y1) ~l~> (x2, y2).
  Proof.
    move: x1 y1 x2 y2 => [n1] [m1] [n2] [m2] /= Heq.
    rewrite local_update_unital_discrete => [[p]] _.
    rewrite !nat_addｰopｰeq => [= ?].
    split => //. f_equal. lia.
  Qed.

  #[global] Instance nat_addｰis_op n1 n2 :
    IsOp (NatAdd (n1 + n2)) (NatAdd n1) (NatAdd n2).
  Proof.
    done.
  Qed.
End sidx.
