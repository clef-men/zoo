From iris.algebra Require Import
  excl
  proofmode_classes.

From zoo Require Import
  prelude.
From zoo.iris.algebra Require Export
  base.
From zoo.iris.algebra Require Import
  lib.auth_option.
From zoo Require Import
  options.

Definition twins A :=
  auth_option (exclR A).
Definition twins_R A :=
  auth_option_R (exclR A).
Definition twins_UR A :=
  auth_option_UR (exclR A).

Definition twins_twin1 {A : ofe} dq (a : A) : twins_UR A :=
  ●O{dq} (Excl a).
Definition twins_twin2 {A : ofe} (a : A) : twins_UR A :=
  ◯O (Excl a).

Section ofe.
  Context {A : ofe}.

  Implicit Types a b : A.

  #[global] Instance twins_twin1_ne dq :
    NonExpansive (@twins_twin1 A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins_twin1_proper dq :
    Proper ((≡) ==> (≡)) (@twins_twin1 A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins_twin2_ne :
    NonExpansive (@twins_twin2 A).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins_twin2_proper :
    Proper ((≡) ==> (≡)) (@twins_twin2 A).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance twins_twin1_dist_inj n :
    Inj2 (=) (≡{n}≡) (≡{n}≡) (@twins_twin1 A).
  Proof.
    intros ?* (-> & ?%(inj Excl))%(inj2 auth_option_auth). done.
  Qed.
  #[global] Instance twins_twin1_inj :
    Inj2 (=) (≡) (≡) (@twins_twin1 A).
  Proof.
    intros ?* (-> & ?%(inj Excl))%(inj2 auth_option_auth). done.
  Qed.
  #[global] Instance twins_twin2_dist_inj n :
    Inj (≡{n}≡) (≡{n}≡) (@twins_twin2 A).
  Proof.
    intros ?* ?%(inj auth_option_frag)%(inj Excl). done.
  Qed.
  #[global] Instance twins_twin2_inj :
    Inj (≡) (≡) (@twins_twin2 A).
  Proof.
    intros ?* ?%(inj auth_option_frag)%(inj Excl). done.
  Qed.

  #[global] Instance twins_twin1_discrete dq a :
    Discrete a →
    Discrete (twins_twin1 dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance twins_twin2_discrete a :
    Discrete a →
    Discrete (twins_twin2 a).
  Proof.
    apply _.
  Qed.
  #[global] Instance twins_cmra_discrete :
    OfeDiscrete A →
    CmraDiscrete (twins_R A).
  Proof.
    apply _.
  Qed.

  Lemma twins_twin1_dfrac_op dq1 dq2 a :
    twins_twin1 (dq1 ⋅ dq2) a ≡ twins_twin1 dq1 a ⋅ twins_twin1 dq2 a.
  Proof.
    apply auth_option_auth_dfrac_op.
  Qed.
  #[global] Instance twins_twin1_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (twins_twin1 dq a) (twins_twin1 dq1 a) (twins_twin1 dq2 a).
  Proof.
    apply _.
  Qed.

  #[global] Instance twins_twin1_core_id a :
    CoreId (twins_twin1 DfracDiscarded a).
  Proof.
    apply _.
  Qed.

  Lemma twins_twin1_dfrac_validN n dq a :
    ✓{n} (twins_twin1 dq a) ↔
    ✓ dq.
  Proof.
    rewrite auth_option_auth_dfrac_validN. naive_solver.
  Qed.
  Lemma twins_twin1_dfrac_valid dq a :
    ✓ (twins_twin1 dq a) ↔
    ✓ dq.
  Proof.
    rewrite auth_option_auth_dfrac_valid. naive_solver.
  Qed.
  Lemma twins_twin1_validN n a :
    ✓{n} (twins_twin1 (DfracOwn 1) a).
  Proof.
    rewrite auth_option_auth_validN //.
  Qed.
  Lemma twins_twin1_valid a :
    ✓ (twins_twin1 (DfracOwn 1) a).
  Proof.
    rewrite auth_option_auth_valid //.
  Qed.

  Lemma twins_twin1_dfrac_op_validN n dq1 a1 dq2 a2 :
    ✓{n} (twins_twin1 dq1 a1 ⋅ twins_twin1 dq2 a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_option_auth_dfrac_op_validN. split.
    - epose proof (inj Excl). naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma twins_twin1_dfrac_op_valid dq1 a1 dq2 a2 :
    ✓ (twins_twin1 dq1 a1 ⋅ twins_twin1 dq2 a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2.
  Proof.
    rewrite auth_option_auth_dfrac_op_valid. split.
    - epose proof (@inj _ _ equiv equiv Excl). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma twins_twin1_op_validN n a1 a2 :
    ✓{n} (twins_twin1 (DfracOwn 1) a1 ⋅ twins_twin1 (DfracOwn 1) a2) ↔
    False.
  Proof.
    rewrite auth_option_auth_op_validN //.
  Qed.
  Lemma twins_twin1_op_valid a b :
    ✓ (twins_twin1 (DfracOwn 1) a ⋅ twins_twin1 (DfracOwn 1) b) ↔
    False.
  Proof.
    rewrite auth_option_auth_op_valid //.
  Qed.

  Lemma twins_twin2_validN n a :
    ✓{n} (twins_twin2 a).
  Proof.
    rewrite auth_option_frag_validN //.
  Qed.
  Lemma twins_twin2_valid a :
    ✓ (twins_twin2 a).
  Proof.
    rewrite auth_option_frag_valid //.
  Qed.

  Lemma twins_twin2_op_validN n a b :
    ✓{n} (twins_twin2 a ⋅ twins_twin2 b) ↔
    False.
  Proof.
    rewrite auth_option_frag_op_validN //.
  Qed.
  Lemma twins_twin2_op_valid a b :
    ✓ (twins_twin2 a ⋅ twins_twin2 b) ↔
    False.
  Proof.
    rewrite auth_option_frag_op_valid //.
  Qed.

  Lemma twins_both_dfrac_validN n dq a b :
    ✓{n} (twins_twin1 dq a ⋅ twins_twin2 b) ↔
    ✓ dq ∧ a ≡{n}≡ b.
  Proof.
    rewrite auth_option_both_dfrac_validN. split.
    - intros (? & [?%(inj Excl) | ?%exclusive_includedN] & ?); done || apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma twins_both_dfrac_valid dq a b :
    ✓ (twins_twin1 dq a ⋅ twins_twin2 b) ↔
    ✓ dq ∧ a ≡ b.
  Proof.
    rewrite auth_option_both_dfrac_valid. split.
    - intros (? & H & ?). split; first done.
      rewrite equiv_dist. intros n.
      specialize (H n) as [?%(inj Excl) | ?%exclusive_includedN]; done || apply _.
    - intros. destruct_and!. split_and!; try done.
      intros. left. f_equiv. eauto using equiv_dist.
  Qed.
  Lemma twins_both_validN n a b :
    ✓{n} (twins_twin1 (DfracOwn 1) a ⋅ twins_twin2 b) ↔
    a ≡{n}≡ b.
  Proof.
    rewrite twins_both_dfrac_validN. naive_solver done.
  Qed.
  Lemma twins_both_valid a b :
    ✓ (twins_twin1 (DfracOwn 1) a ⋅ twins_twin2 b) ↔
    a ≡ b.
  Proof.
    rewrite twins_both_dfrac_valid. naive_solver done.
  Qed.

  Lemma twins_twin1_persist dq a :
    twins_twin1 dq a ~~> twins_twin1 DfracDiscarded a.
  Proof.
    apply auth_option_auth_persist.
  Qed.
  Lemma twins_both_update a b a' b' :
    a' ≡ b' →
    twins_twin1 (DfracOwn 1) a ⋅ twins_twin2 b ~~> twins_twin1 (DfracOwn 1) a' ⋅ twins_twin2 b'.
  Proof.
    intros <-. apply auth_option_both_update, exclusive_local_update. done.
  Qed.
End ofe.

#[global] Opaque twins_twin1.
#[global] Opaque twins_twin2.

Definition twins_URF F :=
  auth_option_URF $ exclRF F.
#[global] Instance twins_URF_contractive F :
  oFunctorContractive F →
  urFunctorContractive (twins_URF F).
Proof.
  apply _.
Qed.

Definition twins_RF F :=
  auth_option_RF $ exclRF F.
#[global] Instance twins_RF_contractive F :
  oFunctorContractive F →
  rFunctorContractive (twins_RF F).
Proof.
  apply _.
Qed.
