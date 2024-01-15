From iris.algebra Require Import
  excl
  proofmode_classes.

From zebra Require Import
  prelude.
From zebra.iris.algebra Require Export
  base.
From zebra.iris.algebra Require Import
  lib.auth_option.
From zebra Require Import
  options.

Definition auth_excl A :=
  auth_option (exclR A).
Definition auth_excl_R A :=
  auth_option_R (exclR A).
Definition auth_excl_UR A :=
  auth_option_UR (exclR A).

Definition auth_excl_auth {A : ofe} dq (a : A) : auth_excl_UR A :=
  ●O{dq} (Excl a).
Definition auth_excl_frag {A : ofe} (a : A) : auth_excl_UR A :=
  ◯O (Excl a).
Notation "●E{ dq } a" := (auth_excl_auth dq a)
( at level 20,
  format "●E{ dq }  a"
).
Notation "●E{# q } a" := (●E{DfracOwn q} a)
( at level 20,
  format "●E{# q }  a"
).
Notation "●E a" := (●E{#1} a)
( at level 20
).
Notation "●E□ a" := (●E{DfracDiscarded} a)
( at level 20
).
Notation "◯E a" := (auth_excl_frag a)
( at level 20
).

Section ofe.
  Context {A : ofe}.

  Implicit Types a b : A.

  #[global] Instance auth_excl_auth_ne dq :
    NonExpansive (@auth_excl_auth A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_excl_auth_proper dq :
    Proper ((≡) ==> (≡)) (@auth_excl_auth A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_excl_frag_ne :
    NonExpansive (@auth_excl_frag A).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_excl_frag_proper :
    Proper ((≡) ==> (≡)) (@auth_excl_frag A).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance auth_excl_auth_dist_inj n :
    Inj2 (=) (≡{n}≡) (≡{n}≡) (@auth_excl_auth A).
  Proof.
    intros ?* (-> & ?%(inj Excl))%(inj2 auth_option_auth). done.
  Qed.
  #[global] Instance auth_excl_auth_inj :
    Inj2 (=) (≡) (≡) (@auth_excl_auth A).
  Proof.
    intros ?* (-> & ?%(inj Excl))%(inj2 auth_option_auth). done.
  Qed.
  #[global] Instance auth_excl_frag_dist_inj n :
    Inj (≡{n}≡) (≡{n}≡) (@auth_excl_frag A).
  Proof.
    intros ?* ?%(inj auth_option_frag)%(inj Excl). done.
  Qed.
  #[global] Instance auth_excl_frag_inj :
    Inj (≡) (≡) (@auth_excl_frag A).
  Proof.
    intros ?* ?%(inj auth_option_frag)%(inj Excl). done.
  Qed.

  #[global] Instance auth_excl_auth_discrete dq a :
    Discrete a →
    Discrete (●E{dq} a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_excl_frag_discrete a :
    Discrete a →
    Discrete (◯E a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_excl_cmra_discrete :
    OfeDiscrete A →
    CmraDiscrete (auth_excl_R A).
  Proof.
    apply _.
  Qed.

  Lemma auth_excl_auth_dfrac_op dq1 dq2 a :
    ●E{dq1 ⋅ dq2} a ≡ ●E{dq1} a ⋅ ●E{dq2} a.
  Proof.
    apply auth_option_auth_dfrac_op.
  Qed.
  #[global] Instance auth_excl_auth_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (●E{dq} a) (●E{dq1} a) (●E{dq2} a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_excl_auth_core_id a :
    CoreId (●E□ a).
  Proof.
    apply _.
  Qed.

  Lemma auth_excl_auth_dfrac_validN n dq a :
    ✓{n} (●E{dq} a) ↔
    ✓ dq.
  Proof.
    rewrite auth_option_auth_dfrac_validN. naive_solver.
  Qed.
  Lemma auth_excl_auth_dfrac_valid dq a :
    ✓ (●E{dq} a) ↔
    ✓ dq.
  Proof.
    rewrite auth_option_auth_dfrac_valid. naive_solver.
  Qed.
  Lemma auth_excl_auth_validN n a :
    ✓{n} (●E a).
  Proof.
    rewrite auth_option_auth_validN //.
  Qed.
  Lemma auth_excl_auth_valid a :
    ✓ (●E a).
  Proof.
    rewrite auth_option_auth_valid //.
  Qed.

  Lemma auth_excl_auth_dfrac_op_validN n dq1 a1 dq2 a2 :
    ✓{n} (●E{dq1} a1 ⋅ ●E{dq2} a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_option_auth_dfrac_op_validN. split.
    - naive_solver eauto using (inj Excl).
    - naive_solver solve_proper.
  Qed.
  Lemma auth_excl_auth_dfrac_op_valid dq1 a1 dq2 a2 :
    ✓ (●E{dq1} a1 ⋅ ●E{dq2} a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2.
  Proof.
    rewrite auth_option_auth_dfrac_op_valid. split.
    - naive_solver eauto using (@inj _ _ equiv equiv Excl) with typeclass_instances.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_excl_auth_op_validN n a1 a2 :
    ✓{n} (●E a1 ⋅ ●E a2) ↔
    False.
  Proof.
    rewrite auth_option_auth_op_validN //.
  Qed.
  Lemma auth_excl_auth_op_valid a b :
    ✓ (●E a ⋅ ●E b) ↔
    False.
  Proof.
    rewrite auth_option_auth_op_valid //.
  Qed.

  Lemma auth_excl_frag_validN n a :
    ✓{n} (◯E a).
  Proof.
    rewrite auth_option_frag_validN //.
  Qed.
  Lemma auth_excl_frag_valid a :
    ✓ (◯E a).
  Proof.
    rewrite auth_option_frag_valid //.
  Qed.

  Lemma auth_excl_frag_op_validN n a b :
    ✓{n} (◯E a ⋅ ◯E b) ↔
    False.
  Proof.
    rewrite auth_option_frag_op_validN //.
  Qed.
  Lemma auth_excl_frag_op_valid a b :
    ✓ (◯E a ⋅ ◯E b) ↔
    False.
  Proof.
    rewrite auth_option_frag_op_valid //.
  Qed.

  Lemma auth_excl_both_dfrac_validN n dq a b :
    ✓{n} (●E{dq} a ⋅ ◯E b) ↔
    ✓ dq ∧ a ≡{n}≡ b.
  Proof.
    rewrite auth_option_both_dfrac_validN. split.
    - intros (? & [?%(inj Excl) | ?%exclusive_includedN] & ?); done || apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_excl_both_dfrac_valid dq a b :
    ✓ (●E{dq} a ⋅ ◯E b) ↔
    ✓ dq ∧ a ≡ b.
  Proof.
    rewrite auth_option_both_dfrac_valid. split.
    - intros (? & H & ?). split; first done.
      rewrite equiv_dist. intros n.
      specialize (H n) as [?%(inj Excl) | ?%exclusive_includedN]; done || apply _.
    - intros. destruct_and!. split_and!; try done.
      intros. left. f_equiv. eauto using equiv_dist.
  Qed.
  Lemma auth_excl_both_validN n a b :
    ✓{n} (●E a ⋅ ◯E b) ↔
    a ≡{n}≡ b.
  Proof.
    rewrite auth_excl_both_dfrac_validN. naive_solver done.
  Qed.
  Lemma auth_excl_both_valid a b :
    ✓ (●E a ⋅ ◯E b) ↔
    a ≡ b.
  Proof.
    rewrite auth_excl_both_dfrac_valid. naive_solver done.
  Qed.

  Lemma auth_excl_auth_persist dq a :
    ●E{dq} a ~~> ●E□ a.
  Proof.
    apply auth_option_auth_persist.
  Qed.
  Lemma auth_excl_both_update a b a' b' :
    a' ≡ b' →
    ●E a ⋅ ◯E b ~~> ●E a' ⋅ ◯E b'.
  Proof.
    intros <-. apply auth_option_both_update, exclusive_local_update. done.
  Qed.
End ofe.

#[global] Opaque auth_excl_auth.
#[global] Opaque auth_excl_frag.

Definition auth_excl_URF F :=
  auth_option_URF $ exclRF F.
#[global] Instance auth_excl_URF_contractive F :
  oFunctorContractive F →
  urFunctorContractive (auth_excl_URF F).
Proof.
  apply _.
Qed.

Definition auth_excl_RF F :=
  auth_option_RF $ exclRF F.
#[global] Instance auth_excl_RF_contractive F :
  oFunctorContractive F →
  rFunctorContractive (auth_excl_RF F).
Proof.
  apply _.
Qed.
