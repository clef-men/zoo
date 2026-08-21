Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.typeclasses.
Require Import zoo.options.

Variant tag :=
  | Tag0
  | Tag1
  | Tag2
  | Tag3
  | Tag4
  | Tag5
  | Tag6
  | Tag7
  | Tag8
  | Tag9
  | Tag10
  | Tag11
  | Tag12
  | Tag13
  | Tag14
  | Tag15
  | Tag16
  | Tag17
  | Tag18
  | Tag19
  | Tag20
  | Tag21
  | Tag22
  | Tag23
  | Tag24
  | Tag25
  | Tag26
  | Tag27
  | Tag28
  | Tag29
  | Tag30.
Implicit Types tag : tag.

#[global] Instance tagｰinhabited : Inhabited tag :=
  populate Tag0.
#[global] Instance tagｰeq_dec : EqDecision tag :=
  ltac:(solve_decision).
#[global] Instance tagｰcountable :
  Countable tag.
Proof.
  solve_countable.
Qed.

Definition tag۰of_nat i :=
  match i with
  | 0 =>
      Some Tag0
  | 1 =>
      Some Tag1
  | 2 =>
      Some Tag2
  | 3 =>
      Some Tag3
  | 4 =>
      Some Tag4
  | 5 =>
      Some Tag5
  | 6 =>
      Some Tag6
  | 7 =>
      Some Tag7
  | 8 =>
      Some Tag8
  | 9 =>
      Some Tag9
  | 10 =>
      Some Tag10
  | 11 =>
      Some Tag11
  | 12 =>
      Some Tag12
  | 13 =>
      Some Tag13
  | 14 =>
      Some Tag14
  | 15 =>
      Some Tag15
  | 16 =>
      Some Tag16
  | 17 =>
      Some Tag17
  | 18 =>
      Some Tag18
  | 19 =>
      Some Tag19
  | 20 =>
      Some Tag20
  | 21 =>
      Some Tag21
  | 22 =>
      Some Tag22
  | 23 =>
      Some Tag23
  | 24 =>
      Some Tag24
  | 25 =>
      Some Tag25
  | 26 =>
      Some Tag26
  | 27 =>
      Some Tag27
  | 28 =>
      Some Tag28
  | 29 =>
      Some Tag29
  | 30 =>
      Some Tag30
  | _ =>
      None
  end.
Definition tag۰of_positive pos :=
  tag۰of_nat $ Pos.to_nat pos.
Definition tag۰of_Z n :=
  match n with
  | 0%Z =>
      Some Tag0
  | Z.pos n =>
      tag۰of_positive n
  | Z.neg _ =>
      None
  end.

Coercion tag۰to_nat tag :=
  match tag with
  | Tag0 =>
      0
  | Tag1 =>
      1
  | Tag2 =>
      2
  | Tag3 =>
      3
  | Tag4 =>
      4
  | Tag5 =>
      5
  | Tag6 =>
      6
  | Tag7 =>
      7
  | Tag8 =>
      8
  | Tag9 =>
      9
  | Tag10 =>
      10
  | Tag11 =>
      11
  | Tag12 =>
      12
  | Tag13 =>
      13
  | Tag14 =>
      14
  | Tag15 =>
      15
  | Tag16 =>
      16
  | Tag17 =>
      17
  | Tag18 =>
      18
  | Tag19 =>
      19
  | Tag20 =>
      20
  | Tag21 =>
      21
  | Tag22 =>
      22
  | Tag23 =>
      23
  | Tag24 =>
      24
  | Tag25 =>
      25
  | Tag26 =>
      26
  | Tag27 =>
      27
  | Tag28 =>
      28
  | Tag29 =>
      29
  | Tag30 =>
      30
  end.
Definition tag۰to_Z tag : Z :=
  tag۰to_nat tag.

#[global] Instance tag۰to_natｰinj :
  Inj (=) (=) tag۰to_nat.
Proof.
  intros [] [] => //.
Qed.
#[global] Instance tag۰to_Zｰinj :
  Inj (=) (=) tag۰to_Z.
Proof.
  apply _.
Qed.

Definition tag۰beq tag1 tag2 :=
  tag۰to_nat tag1 ≟ tag۰to_nat tag2.
#[global] Program Instance tagｰbeq : Beq tag :=
  {|beq := tag۰beq
  |}.
Next Obligation.
  setoid_rewrite beqｰspec. naive_solver.
Qed.

Parameter tag۰string : nat.

Axiom tag۰stringｰspec : ∀ tag,
  tag < tag۰string.
#[global] Hint Resolve
  tag۰stringｰspec
: core.
