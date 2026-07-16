Require Import iris.algebra.excl.
Require Import iris.algebra.proofmode_classes.

Require Import zoo.prelude.
Require Export zoo.iris.algebra.base.
Require Import zoo.iris.algebra.lib.auth_option.
Require Import zoo.options.

Definition twins {SI : sidx} A :=
  auth_option (exclR A).
Definition twins۰R {SI : sidx} A :=
  auth_option۰R (exclR A).
Definition twins۰UR {SI : sidx} A :=
  auth_option۰UR (exclR A).

Section ofe.
  Context {SI : sidx}.
  Context {A : ofe}.

  Implicit Types a b : A.

  Definition twins۰twin₁ dq a : twins۰UR A :=
    ●O{dq} (Excl a).
  Definition twins۰twin₂ a : twins۰UR A :=
    ◯O (Excl a).

  #[global] Instance twins۰twin₁𑁒ne dq :
    NonExpansive (twins۰twin₁ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins۰twin₁𑁒proper dq :
    Proper ((≡) ==> (≡)) (twins۰twin₁ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins۰twin₂𑁒ne :
    NonExpansive twins۰twin₂.
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins۰twin₂𑁒proper :
    Proper ((≡) ==> (≡)) twins۰twin₂.
  Proof.
    solve_proper.
  Qed.

  #[global] Instance twins۰twin₁𑁒dist𑁒inj n :
    Inj2 (=) (≡{n}≡) (≡{n}≡) twins۰twin₁.
  Proof.
    intros ?* (-> & ?%(inj Excl))%(inj2 auth_option۰auth). done.
  Qed.
  #[global] Instance twins۰twin₁𑁒inj :
    Inj2 (=) (≡) (≡) twins۰twin₁.
  Proof.
    intros ?* (-> & ?%(inj Excl))%(inj2 auth_option۰auth). done.
  Qed.
  #[global] Instance twins۰twin₂𑁒dist𑁒inj n :
    Inj (≡{n}≡) (≡{n}≡) twins۰twin₂.
  Proof.
    intros ?* ?%(inj auth_option۰frag)%(inj Excl). done.
  Qed.
  #[global] Instance twins۰twin₂𑁒inj :
    Inj (≡) (≡) twins۰twin₂.
  Proof.
    intros ?* ?%(inj auth_option۰frag)%(inj Excl). done.
  Qed.

  #[global] Instance twins۰twin₁𑁒discrete dq a :
    Discrete a →
    Discrete (twins۰twin₁ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance twins۰twin₂𑁒discrete a :
    Discrete a →
    Discrete (twins۰twin₂ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance twins۰cmra_discrete :
    OfeDiscrete A →
    CmraDiscrete (twins۰R A).
  Proof.
    apply _.
  Qed.

  Lemma twins۰twin₁𑁒dfrac𑁒op dq1 dq2 a :
    twins۰twin₁ (dq1 ⋅ dq2) a ≡ twins۰twin₁ dq1 a ⋅ twins۰twin₁ dq2 a.
  Proof.
    apply auth_option۰auth𑁒dfrac𑁒op.
  Qed.
  #[global] Instance twins۰twin₁𑁒dfrac𑁒is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (twins۰twin₁ dq a) (twins۰twin₁ dq1 a) (twins۰twin₁ dq2 a).
  Proof.
    apply _.
  Qed.

  #[global] Instance twins۰twin₁𑁒core_id a :
    CoreId (twins۰twin₁ DfracDiscarded a).
  Proof.
    apply _.
  Qed.

  Lemma twins۰twin₁𑁒dfrac𑁒validN n dq a :
    ✓{n} (twins۰twin₁ dq a) ↔
    ✓ dq.
  Proof.
    rewrite auth_option۰auth𑁒dfrac𑁒validN. naive_solver.
  Qed.
  Lemma twins۰twin₁𑁒dfrac𑁒valid dq a :
    ✓ (twins۰twin₁ dq a) ↔
    ✓ dq.
  Proof.
    rewrite auth_option۰auth𑁒dfrac𑁒valid. naive_solver.
  Qed.
  Lemma twins۰twin₁𑁒validN n a :
    ✓{n} (twins۰twin₁ (DfracOwn 1) a).
  Proof.
    rewrite auth_option۰auth𑁒validN //.
  Qed.
  Lemma twins۰twin₁𑁒valid a :
    ✓ (twins۰twin₁ (DfracOwn 1) a).
  Proof.
    rewrite auth_option۰auth𑁒valid //.
  Qed.

  Lemma twins۰twin₁𑁒dfrac𑁒op𑁒validN n dq1 a1 dq2 a2 :
    ✓{n} (twins۰twin₁ dq1 a1 ⋅ twins۰twin₁ dq2 a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_option۰auth𑁒dfrac𑁒op𑁒validN. split.
    - epose proof (inj Excl). naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma twins۰twin₁𑁒dfrac𑁒op𑁒valid dq1 a1 dq2 a2 :
    ✓ (twins۰twin₁ dq1 a1 ⋅ twins۰twin₁ dq2 a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2.
  Proof.
    rewrite auth_option۰auth𑁒dfrac𑁒op𑁒valid. split.
    - epose proof (@inj _ _ equiv equiv Excl). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma twins۰twin₁𑁒op𑁒validN n a1 a2 :
    ✓{n} (twins۰twin₁ (DfracOwn 1) a1 ⋅ twins۰twin₁ (DfracOwn 1) a2) ↔
    False.
  Proof.
    rewrite auth_option۰auth𑁒op𑁒validN //.
  Qed.
  Lemma twins۰twin₁𑁒op𑁒valid a b :
    ✓ (twins۰twin₁ (DfracOwn 1) a ⋅ twins۰twin₁ (DfracOwn 1) b) ↔
    False.
  Proof.
    rewrite auth_option۰auth𑁒op𑁒valid //.
  Qed.

  Lemma twins۰twin₂𑁒validN n a :
    ✓{n} (twins۰twin₂ a).
  Proof.
    rewrite auth_option۰frag𑁒validN //.
  Qed.
  Lemma twins۰twin₂𑁒valid a :
    ✓ (twins۰twin₂ a).
  Proof.
    rewrite auth_option۰frag𑁒valid //.
  Qed.

  Lemma twins۰twin₂𑁒op𑁒validN n a b :
    ✓{n} (twins۰twin₂ a ⋅ twins۰twin₂ b) ↔
    False.
  Proof.
    rewrite auth_option۰frag𑁒op𑁒validN //.
  Qed.
  Lemma twins۰twin₂𑁒op𑁒valid a b :
    ✓ (twins۰twin₂ a ⋅ twins۰twin₂ b) ↔
    False.
  Proof.
    rewrite auth_option۰frag𑁒op𑁒valid //.
  Qed.

  Lemma twins𑁒both𑁒dfrac𑁒validN n dq a b :
    ✓{n} (twins۰twin₁ dq a ⋅ twins۰twin₂ b) ↔
    ✓ dq ∧ a ≡{n}≡ b.
  Proof.
    rewrite auth_option𑁒both𑁒dfrac𑁒validN. split.
    - intros (? & [?%(inj Excl) | ?%exclusive_includedN] & ?); done || apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma twins𑁒both𑁒dfrac𑁒valid dq a b :
    ✓ (twins۰twin₁ dq a ⋅ twins۰twin₂ b) ↔
    ✓ dq ∧ a ≡ b.
  Proof.
    rewrite auth_option𑁒both𑁒dfrac𑁒valid. split.
    - intros (? & H & ?). split; first done.
      rewrite equiv_dist. intros n.
      specialize (H n) as [?%(inj Excl) | ?%exclusive_includedN]; done || apply _.
    - intros. destruct_and!. split_and!; try done.
      intros. left. f_equiv. eauto using equiv_dist.
  Qed.
  Lemma twins𑁒both𑁒validN n a b :
    ✓{n} (twins۰twin₁ (DfracOwn 1) a ⋅ twins۰twin₂ b) ↔
    a ≡{n}≡ b.
  Proof.
    rewrite twins𑁒both𑁒dfrac𑁒validN. naive_solver done.
  Qed.
  Lemma twins𑁒both𑁒valid a b :
    ✓ (twins۰twin₁ (DfracOwn 1) a ⋅ twins۰twin₂ b) ↔
    a ≡ b.
  Proof.
    rewrite twins𑁒both𑁒dfrac𑁒valid. naive_solver done.
  Qed.

  Lemma twins۰twin₁𑁒persist dq a :
    twins۰twin₁ dq a ~~> twins۰twin₁ DfracDiscarded a.
  Proof.
    apply auth_option۰auth𑁒persist.
  Qed.
  Lemma twins𑁒both𑁒update a1 b1 a2 b2 :
    a2 ≡ b2 →
    twins۰twin₁ (DfracOwn 1) a1 ⋅ twins۰twin₂ b1 ~~> twins۰twin₁ (DfracOwn 1) a2 ⋅ twins۰twin₂ b2.
  Proof.
    intros <-.
    apply auth_option𑁒both𑁒update, exclusive_local_update. done.
  Qed.
End ofe.

#[global] Opaque twins۰twin₁.
#[global] Opaque twins۰twin₂.

Definition twins۰URF {SI : sidx} F :=
  auth_option۰URF $ exclRF F.
#[global] Instance twins۰URF𑁒contractive {SI : sidx} F :
  oFunctorContractive F →
  urFunctorContractive (twins۰URF F).
Proof.
  apply _.
Qed.

Definition twins۰RF {SI : sidx} F :=
  auth_option۰RF $ exclRF F.
#[global] Instance twins۰RF𑁒contractive {SI : sidx} F :
  oFunctorContractive F →
  rFunctorContractive (twins۰RF F).
Proof.
  apply _.
Qed.
