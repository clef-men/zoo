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

  Implicit Type a b : A.

  Definition twins۰twin₁ dq a : twins۰UR A :=
    ●O{dq} (Excl a).
  Definition twins۰twin₂ a : twins۰UR A :=
    ◯O (Excl a).

  #[global] Instance twins۰twin₁ｰne dq :
    NonExpansive (twins۰twin₁ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins۰twin₁ｰproper dq :
    Proper ((≡) ==> (≡)) (twins۰twin₁ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins۰twin₂ｰne :
    NonExpansive twins۰twin₂.
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins۰twin₂ｰproper :
    Proper ((≡) ==> (≡)) twins۰twin₂.
  Proof.
    solve_proper.
  Qed.

  #[global] Instance twins۰twin₁ｰdistｰinj n :
    Inj2 (=) (≡{n}≡) (≡{n}≡) twins۰twin₁.
  Proof.
    intros ?* (-> & ?%(inj Excl))%(inj2 auth_option۰auth). done.
  Qed.
  #[global] Instance twins۰twin₁ｰinj :
    Inj2 (=) (≡) (≡) twins۰twin₁.
  Proof.
    intros ?* (-> & ?%(inj Excl))%(inj2 auth_option۰auth). done.
  Qed.
  #[global] Instance twins۰twin₂ｰdistｰinj n :
    Inj (≡{n}≡) (≡{n}≡) twins۰twin₂.
  Proof.
    intros ?* ?%(inj auth_option۰frag)%(inj Excl). done.
  Qed.
  #[global] Instance twins۰twin₂ｰinj :
    Inj (≡) (≡) twins۰twin₂.
  Proof.
    intros ?* ?%(inj auth_option۰frag)%(inj Excl). done.
  Qed.

  #[global] Instance twins۰twin₁ｰdiscrete dq a :
    Discrete a →
    Discrete (twins۰twin₁ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance twins۰twin₂ｰdiscrete a :
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

  Lemma twins۰twin₁ｰdfracｰop dq1 dq2 a :
    twins۰twin₁ (dq1 ⋅ dq2) a ≡ twins۰twin₁ dq1 a ⋅ twins۰twin₁ dq2 a.
  Proof.
    apply auth_option۰authｰdfracｰop.
  Qed.
  #[global] Instance twins۰twin₁ｰdfracｰis_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (twins۰twin₁ dq a) (twins۰twin₁ dq1 a) (twins۰twin₁ dq2 a).
  Proof.
    apply _.
  Qed.

  #[global] Instance twins۰twin₁ｰcore_id a :
    CoreId (twins۰twin₁ DfracDiscarded a).
  Proof.
    apply _.
  Qed.

  Lemma twins۰twin₁ｰdfracｰvalidN n dq a :
    ✓{n} (twins۰twin₁ dq a) ↔
    ✓ dq.
  Proof.
    rewrite auth_option۰authｰdfracｰvalidN. naive_solver.
  Qed.
  Lemma twins۰twin₁ｰdfracｰvalid dq a :
    ✓ (twins۰twin₁ dq a) ↔
    ✓ dq.
  Proof.
    rewrite auth_option۰authｰdfracｰvalid. naive_solver.
  Qed.
  Lemma twins۰twin₁ｰvalidN n a :
    ✓{n} (twins۰twin₁ (DfracOwn 1) a).
  Proof.
    rewrite auth_option۰authｰvalidN //.
  Qed.
  Lemma twins۰twin₁ｰvalid a :
    ✓ (twins۰twin₁ (DfracOwn 1) a).
  Proof.
    rewrite auth_option۰authｰvalid //.
  Qed.

  Lemma twins۰twin₁ｰdfracｰopｰvalidN n dq1 a1 dq2 a2 :
    ✓{n} (twins۰twin₁ dq1 a1 ⋅ twins۰twin₁ dq2 a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_option۰authｰdfracｰopｰvalidN. split.
    - epose proof (inj Excl). naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma twins۰twin₁ｰdfracｰopｰvalid dq1 a1 dq2 a2 :
    ✓ (twins۰twin₁ dq1 a1 ⋅ twins۰twin₁ dq2 a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2.
  Proof.
    rewrite auth_option۰authｰdfracｰopｰvalid. split.
    - epose proof (@inj _ _ equiv equiv Excl). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma twins۰twin₁ｰopｰvalidN n a1 a2 :
    ✓{n} (twins۰twin₁ (DfracOwn 1) a1 ⋅ twins۰twin₁ (DfracOwn 1) a2) ↔
    False.
  Proof.
    rewrite auth_option۰authｰopｰvalidN //.
  Qed.
  Lemma twins۰twin₁ｰopｰvalid a b :
    ✓ (twins۰twin₁ (DfracOwn 1) a ⋅ twins۰twin₁ (DfracOwn 1) b) ↔
    False.
  Proof.
    rewrite auth_option۰authｰopｰvalid //.
  Qed.

  Lemma twins۰twin₂ｰvalidN n a :
    ✓{n} (twins۰twin₂ a).
  Proof.
    rewrite auth_option۰fragｰvalidN //.
  Qed.
  Lemma twins۰twin₂ｰvalid a :
    ✓ (twins۰twin₂ a).
  Proof.
    rewrite auth_option۰fragｰvalid //.
  Qed.

  Lemma twins۰twin₂ｰopｰvalidN n a b :
    ✓{n} (twins۰twin₂ a ⋅ twins۰twin₂ b) ↔
    False.
  Proof.
    rewrite auth_option۰fragｰopｰvalidN //.
  Qed.
  Lemma twins۰twin₂ｰopｰvalid a b :
    ✓ (twins۰twin₂ a ⋅ twins۰twin₂ b) ↔
    False.
  Proof.
    rewrite auth_option۰fragｰopｰvalid //.
  Qed.

  Lemma twinsｰbothｰdfracｰvalidN n dq a b :
    ✓{n} (twins۰twin₁ dq a ⋅ twins۰twin₂ b) ↔
    ✓ dq ∧ a ≡{n}≡ b.
  Proof.
    rewrite auth_optionｰbothｰdfracｰvalidN. split.
    - intros (? & [?%(inj Excl) | ?%exclusive_includedN] & ?); done || apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma twinsｰbothｰdfracｰvalid dq a b :
    ✓ (twins۰twin₁ dq a ⋅ twins۰twin₂ b) ↔
    ✓ dq ∧ a ≡ b.
  Proof.
    rewrite auth_optionｰbothｰdfracｰvalid. split.
    - intros (? & H & ?). split; first done.
      rewrite equiv_dist. intros n.
      specialize (H n) as [?%(inj Excl) | ?%exclusive_includedN]; done || apply _.
    - intros. destruct_and!. split_and!; try done.
      intros. left. f_equiv. eauto using equiv_dist.
  Qed.
  Lemma twinsｰbothｰvalidN n a b :
    ✓{n} (twins۰twin₁ (DfracOwn 1) a ⋅ twins۰twin₂ b) ↔
    a ≡{n}≡ b.
  Proof.
    rewrite twinsｰbothｰdfracｰvalidN. naive_solver done.
  Qed.
  Lemma twinsｰbothｰvalid a b :
    ✓ (twins۰twin₁ (DfracOwn 1) a ⋅ twins۰twin₂ b) ↔
    a ≡ b.
  Proof.
    rewrite twinsｰbothｰdfracｰvalid. naive_solver done.
  Qed.

  Lemma twins۰twin₁ｰpersist dq a :
    twins۰twin₁ dq a ~~> twins۰twin₁ DfracDiscarded a.
  Proof.
    apply auth_option۰authｰpersist.
  Qed.
  Lemma twinsｰbothｰupdate a1 b1 a2 b2 :
    a2 ≡ b2 →
    twins۰twin₁ (DfracOwn 1) a1 ⋅ twins۰twin₂ b1 ~~> twins۰twin₁ (DfracOwn 1) a2 ⋅ twins۰twin₂ b2.
  Proof.
    intros <-.
    apply auth_optionｰbothｰupdate, exclusive_local_update. done.
  Qed.
End ofe.

#[global] Opaque twins۰twin₁.
#[global] Opaque twins۰twin₂.

Definition twins۰URF {SI : sidx} F :=
  auth_option۰URF $ exclRF F.
#[global] Instance twins۰URFｰcontractive {SI : sidx} F :
  oFunctorContractive F →
  urFunctorContractive (twins۰URF F).
Proof.
  apply _.
Qed.

Definition twins۰RF {SI : sidx} F :=
  auth_option۰RF $ exclRF F.
#[global] Instance twins۰RFｰcontractive {SI : sidx} F :
  oFunctorContractive F →
  rFunctorContractive (twins۰RF F).
Proof.
  apply _.
Qed.
