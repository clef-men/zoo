From iris.algebra Require Import
  auth
  proofmode_classes.

From zebre Require Import
  prelude.
From zebre.iris.algebra Require Export
  base.
From zebre Require Import
  options.

Definition auth_option A :=
  auth (optionUR A).
Definition auth_option_O A :=
  authO (optionUR A).
Definition auth_option_R A :=
  authR (optionUR A).
Definition auth_option_UR A :=
  authUR (optionUR A).

Definition auth_option_auth {A : cmra} dq (a : A) : auth_option_UR A :=
  ●{dq} (Some a).
Definition auth_option_frag {A : cmra} (a : A) : auth_option_UR A :=
  ◯ (Some a).

Notation "●O dq a" := (
  auth_option_auth dq a
)(at level 20,
  dq custom dfrac at level 1,
  format "●O dq  a"
).
Notation "◯O a" := (
  auth_option_frag a
)(at level 20
).

Section cmra.
  Context {A : cmra}.

  Implicit Types a b : A.

  #[global] Instance auth_option_auth_ne dq :
    NonExpansive (@auth_option_auth A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_option_auth_proper dq :
    Proper ((≡) ==> (≡)) (@auth_option_auth A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_option_frag_ne :
    NonExpansive (@auth_option_frag A).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_option_frag_proper :
    Proper ((≡) ==> (≡)) (@auth_option_frag A).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance auth_option_auth_dist_inj n :
    Inj2 (=) (≡{n}≡) (≡{n}≡) (@auth_option_auth A).
  Proof.
    rewrite /Inj2. intros * (-> & ?%(inj Some))%(inj2 auth_auth). done.
  Qed.
  #[global] Instance auth_option_auth_inj :
    Inj2 (=) (≡) (≡) (@auth_option_auth A).
  Proof.
    rewrite /Inj2. intros * (-> & ?%(inj Some))%(inj2 auth_auth). done.
  Qed.
  #[global] Instance auth_option_frag_dist_inj n :
    Inj (≡{n}≡) (≡{n}≡) (@auth_option_frag A).
  Proof.
    rewrite /Inj. intros * ?%(inj auth_frag)%(inj Some). done.
  Qed.
  #[global] Instance auth_option_frag_inj :
    Inj (≡) (≡) (@auth_option_frag A).
  Proof.
    rewrite /Inj. intros * ?%(inj auth_frag)%(inj Some). done.
  Qed.

  #[global] Instance auth_option_ofe_discrete :
    OfeDiscrete A →
    OfeDiscrete (auth_option_O A).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option_auth_discrete dq a :
    Discrete a →
    Discrete (●O{dq} a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option_frag_discrete a :
    Discrete a →
    Discrete (◯O a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option_cmra_discrete :
    CmraDiscrete A →
    CmraDiscrete (auth_option_R A).
  Proof.
    apply _.
  Qed.

  Lemma auth_option_auth_dfrac_op dq1 dq2 a :
    ●O{dq1 ⋅ dq2} a ≡ ●O{dq1} a ⋅ ●O{dq2} a.
  Proof.
    apply auth_auth_dfrac_op.
  Qed.
  #[global] Instance auth_option_auth_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (●O{dq} a) (●O{dq1} a) (●O{dq2} a).
  Proof.
    apply _.
  Qed.

  Lemma auth_option_frag_op a b :
    ◯O (a ⋅ b) = ◯O a ⋅ ◯O b.
  Proof.
    rewrite -auth_frag_op //.
  Qed.
  Lemma auth_option_frag_mono a b :
    a ≼ b →
    ◯O a ≼ ◯O b.
  Proof.
    intros. apply auth_frag_mono, Some_included. naive_solver.
  Qed.
  Lemma auth_option_frag_core `{!CmraTotal A} a :
    core (◯O a) = ◯O (core a).
  Proof.
    rewrite auth_frag_core -Some_core //.
  Qed.
  Lemma auth_option_both_core_discarded `{!CmraTotal A} a b :
    core (●O□ a ⋅ ◯O b) ≡ ●O□ a ⋅ ◯O (core b).
  Proof.
    rewrite auth_both_core_discarded -Some_core //.
  Qed.
  Lemma auth_option_both_core_frac `{!CmraTotal A} q a b :
    core (●O{#q} a ⋅ ◯O b) ≡ ◯O (core b).
  Proof.
    rewrite auth_both_core_frac -Some_core //.
  Qed.

  #[global] Instance auth_option_auth_core_id a :
    CoreId (●O□ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option_frag_core_id a :
    CoreId a →
    CoreId (◯O a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option_both_core_id a1 a2 :
    CoreId a2 →
    CoreId (●O□ a1 ⋅ ◯O a2).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option_frag_is_op a b1 b2 :
    IsOp a b1 b2 →
    IsOp' (◯O a) (◯O b1) (◯O b2).
  Proof.
    apply _.
  Qed.

  Lemma auth_option_auth_dfrac_op_invN n dq1 a1 dq2 a2 :
    ✓{n} (●O{dq1} a1 ⋅ ●O{dq2} a2) →
    a1 ≡{n}≡ a2.
  Proof.
    intros. apply (inj Some). apply: auth_auth_dfrac_op_invN. done.
  Qed.
  Lemma auth_option_auth_dfrac_op_inv dq1 a1 dq2 a2 :
    ✓ (●O{dq1} a1 ⋅ ●O{dq2} a2) →
    a1 ≡ a2.
  Proof.
    intros. apply (inj Some). apply: auth_auth_dfrac_op_inv. done.
  Qed.
  Lemma auth_option_auth_dfrac_op_inv_L `{!LeibnizEquiv A} dq1 a1 dq2 a2 :
    ✓ (●O{dq1} a1 ⋅ ●O{dq2} a2) →
    a1 = a2.
  Proof.
    intros. apply (inj Some). apply: auth_auth_dfrac_op_inv_L. done.
  Qed.

  Lemma auth_option_auth_dfrac_validN n dq a :
    ✓{n} (●O{dq} a) ↔
    ✓ dq ∧ ✓{n} a.
  Proof.
    rewrite auth_auth_dfrac_validN //.
  Qed.
  Lemma auth_option_auth_dfrac_valid dq a :
    ✓ (●O{dq} a) ↔
    ✓ dq ∧ ✓ a.
  Proof.
    rewrite auth_auth_dfrac_valid //.
  Qed.
  Lemma auth_option_auth_validN n a :
    ✓{n} (●O a) ↔
    ✓{n} a.
  Proof.
    rewrite auth_auth_validN //.
  Qed.
  Lemma auth_option_auth_valid a :
    ✓ (●O a) ↔
    ✓ a.
  Proof.
    rewrite auth_auth_valid //.
  Qed.

  Lemma auth_option_auth_dfrac_op_validN n dq1 a1 dq2 a2 :
    ✓{n} (●O{dq1} a1 ⋅ ●O{dq2} a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡{n}≡ a2 ∧ ✓{n} a1.
  Proof.
    rewrite auth_auth_dfrac_op_validN. split.
    - naive_solver eauto using (inj Some).
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option_auth_dfrac_op_valid dq1 a1 dq2 a2 :
    ✓ (●O{dq1} a1 ⋅ ●O{dq2} a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2 ∧ ✓ a1.
  Proof.
    rewrite auth_auth_dfrac_op_valid. split.
    - naive_solver eauto using (@inj _ _ equiv equiv Some) with typeclass_instances.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option_auth_op_validN n a1 a2 :
    ✓{n} (●O a1 ⋅ ●O a2) ↔
    False.
  Proof.
    rewrite auth_auth_op_validN //.
  Qed.
  Lemma auth_option_auth_op_valid a1 a2 :
    ✓ (●O a1 ⋅ ●O a2) ↔
    False.
  Proof.
    rewrite auth_auth_op_valid //.
  Qed.

  Lemma auth_option_frag_validN n b :
    ✓{n} (◯O b) ↔
    ✓{n} b.
  Proof.
    rewrite auth_frag_validN //.
  Qed.
  Lemma auth_option_frag_validN_1 n b :
    ✓{n} (◯O b) →
    ✓{n} b.
  Proof.
    rewrite auth_option_frag_validN //.
  Qed.
  Lemma auth_option_frag_validN_2 n b :
    ✓{n} b →
    ✓{n} (◯O b).
  Proof.
    rewrite auth_option_frag_validN //.
  Qed.
  Lemma auth_option_frag_valid b :
    ✓ (◯O b) ↔
    ✓ b.
  Proof.
    rewrite auth_frag_valid //.
  Qed.
  Lemma auth_option_frag_valid_1 b :
    ✓ (◯O b) →
    ✓ b.
  Proof.
    rewrite auth_option_frag_valid //.
  Qed.
  Lemma auth_option_frag_valid_2 b :
    ✓ b →
    ✓ (◯O b).
  Proof.
    rewrite auth_option_frag_valid //.
  Qed.

  Lemma auth_option_frag_op_validN n b1 b2 :
    ✓{n} (◯O b1 ⋅ ◯O b2) ↔
    ✓{n} (b1 ⋅ b2).
  Proof.
    rewrite auth_frag_op_validN //.
  Qed.
  Lemma auth_option_frag_op_validN_1 n b1 b2 :
    ✓{n} (◯O b1 ⋅ ◯O b2) →
    ✓{n} (b1 ⋅ b2).
  Proof.
    rewrite auth_option_frag_op_validN //.
  Qed.
  Lemma auth_option_frag_op_validN_2 n b1 b2 :
    ✓{n} (b1 ⋅ b2) →
    ✓{n} (◯O b1 ⋅ ◯O b2).
  Proof.
    rewrite auth_option_frag_op_validN //.
  Qed.
  Lemma auth_option_frag_op_valid b1 b2 :
    ✓ (◯O b1 ⋅ ◯O b2) ↔
    ✓ (b1 ⋅ b2).
  Proof.
    rewrite auth_frag_op_valid //.
  Qed.
  Lemma auth_option_frag_op_valid_1 b1 b2 :
    ✓ (◯O b1 ⋅ ◯O b2) →
    ✓ (b1 ⋅ b2).
  Proof.
    rewrite auth_option_frag_op_valid //.
  Qed.
  Lemma auth_option_frag_op_valid_2 b1 b2 :
    ✓ (b1 ⋅ b2) →
    ✓ (◯O b1 ⋅ ◯O b2).
  Proof.
    rewrite auth_option_frag_op_valid //.
  Qed.

  Lemma auth_option_both_dfrac_validN n dq a b :
    ✓{n} (●O{dq} a ⋅ ◯O b) ↔
    ✓ dq ∧ (a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓{n} a.
  Proof.
    rewrite auth_both_dfrac_validN Some_includedN. naive_solver.
  Qed.
  Lemma auth_option_both_dfrac_valid dq a b :
    ✓ (●O{dq} a ⋅ ◯O b) ↔
    ✓ dq ∧ (∀ n, a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓ a.
  Proof.
    rewrite auth_both_dfrac_valid. setoid_rewrite Some_includedN. naive_solver.
  Qed.
  Lemma auth_option_both_validN n a b :
    ✓{n} (●O a ⋅ ◯O b) ↔
    (a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓{n} a.
  Proof.
    rewrite auth_option_both_dfrac_validN. naive_solver done.
  Qed.
  Lemma auth_option_both_valid a b :
    ✓ (●O a ⋅ ◯O b) ↔
    (∀ n, a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓ a.
  Proof.
    rewrite auth_option_both_dfrac_valid. naive_solver done.
  Qed.

  Lemma auth_option_both_dfrac_valid_discrete `{!CmraDiscrete A} dq a b :
    ✓ (●O{dq} a ⋅ ◯O b) ↔
    ✓ dq ∧ (a ≡ b ∨ b ≼ a) ∧ ✓ a.
  Proof.
    rewrite auth_both_dfrac_valid_discrete Some_included. naive_solver.
  Qed.
  Lemma auth_option_both_valid_discrete `{!CmraDiscrete A} a b :
    ✓ (●O a ⋅ ◯O b) ↔
    (a ≡ b ∨ b ≼ a) ∧ ✓ a.
  Proof.
    rewrite auth_both_valid_discrete Some_included. naive_solver.
  Qed.

  Lemma auth_option_auth_dfrac_includedN n dq1 a1 dq2 a2 b :
    ●O{dq1} a1 ≼{n} ●O{dq2} a2 ⋅ ◯O b ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_auth_dfrac_includedN. split.
    - naive_solver eauto using (inj Some).
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option_auth_dfrac_included dq1 a1 dq2 a2 b :
    ●O{dq1} a1 ≼ ●O{dq2} a2 ⋅ ◯O b ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2.
  Proof.
    rewrite auth_auth_dfrac_included. split.
    - naive_solver eauto using (@inj _ _ equiv equiv Some) with typeclass_instances.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option_auth_includedN n a1 a2 b :
    ●O a1 ≼{n} ●O a2 ⋅ ◯O b ↔
    a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_option_auth_dfrac_includedN. naive_solver.
  Qed.
  Lemma auth_option_auth_included a1 a2 b :
    ●O a1 ≼ ●O a2 ⋅ ◯O b ↔
    a1 ≡ a2.
  Proof.
    rewrite auth_option_auth_dfrac_included. naive_solver.
  Qed.

  Lemma auth_option_frag_includedN n dq a b1 b2 :
    ◯O b1 ≼{n} ●O{dq} a ⋅ ◯O b2 ↔
    b1 ≡{n}≡ b2 ∨ b1 ≼{n} b2.
  Proof.
    rewrite auth_frag_includedN Some_includedN //.
  Qed.
  Lemma auth_option_frag_included dq a b1 b2 :
    ◯O b1 ≼ ●O{dq} a ⋅ ◯O b2 ↔
    b1 ≡ b2 ∨ b1 ≼ b2.
  Proof.
    rewrite auth_frag_included Some_included //.
  Qed.

  Lemma auth_option_both_dfrac_includedN n dq1 a1 dq2 a2 b1 b2 :
    ●O{dq1} a1 ⋅ ◯O b1 ≼{n} ●O{dq2} a2 ⋅ ◯O b2 ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ (b1 ≡{n}≡ b2 ∨ b1 ≼{n} b2).
  Proof.
    rewrite auth_both_dfrac_includedN Some_includedN. split.
    - naive_solver eauto using (inj Some).
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option_both_dfrac_included dq1 a1 dq2 a2 b1 b2 :
    ●O{dq1} a1 ⋅ ◯O b1 ≼ ●O{dq2} a2 ⋅ ◯O b2 ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 ∧ (b1 ≡ b2 ∨ b1 ≼ b2).
  Proof.
    rewrite auth_both_dfrac_included Some_included. split.
    - naive_solver eauto using (@inj _ _ equiv equiv Some) with typeclass_instances.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option_both_includedN n a1 a2 b1 b2 :
    ●O a1 ⋅ ◯O b1 ≼{n} ●O a2 ⋅ ◯O b2 ↔
    a1 ≡{n}≡ a2 ∧ (b1 ≡{n}≡ b2 ∨ b1 ≼{n} b2).
  Proof.
    rewrite auth_both_includedN Some_includedN. split.
    - naive_solver eauto using (inj Some).
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option_both_included a1 a2 b1 b2 :
    ●O a1 ⋅ ◯O b1 ≼ ●O a2 ⋅ ◯O b2 ↔
    a1 ≡ a2 ∧ (b1 ≡ b2 ∨ b1 ≼ b2).
  Proof.
    rewrite auth_both_included Some_included. split.
    - naive_solver eauto using (@inj _ _ equiv equiv Some) with typeclass_instances.
    - naive_solver solve_proper.
  Qed.

  Lemma auth_option_auth_persist dq a :
    ●O{dq} a ~~> ●O□ a.
  Proof.
    apply auth_update_auth_persist.
  Qed.
  Lemma auth_option_auth_dfrac_update dq a b `{!CoreId b} :
    a ≡ b ∨ b ≼ a →
    ●O{dq} a ~~> ●O{dq} a ⋅ ◯O b.
  Proof.
    intros. apply auth_update_dfrac_alloc; first apply _.
    rewrite Some_included. naive_solver.
  Qed.
  Lemma auth_option_auth_update a b `{!CoreId b} :
    a ≡ b ∨ b ≼ a →
    ●O a ~~> ●O a ⋅ ◯O b.
  Proof.
    apply auth_option_auth_dfrac_update. done.
  Qed.
  Lemma auth_option_both_update a b a' b' :
    (a, b) ~l~> (a', b') →
    ●O a ⋅ ◯O b ~~> ●O a' ⋅ ◯O b'.
  Proof.
    intros. apply auth_update, option_local_update. done.
  Qed.

  Lemma auth_option_local_update a b0 b1 a' b0' b1' :
    (b0, b1) ~l~> (b0', b1') →
    a' ≡ b0' ∨ b0' ≼ a' →
    ✓ a' →
    (●O a ⋅ ◯O b0, ●O a ⋅ ◯O b1) ~l~> (●O a' ⋅ ◯O b0', ●O a' ⋅ ◯O b1').
  Proof.
    intros. apply auth_local_update; last done.
    - apply option_local_update. done.
    - rewrite Some_included. naive_solver.
  Qed.
End cmra.

#[global] Opaque auth_option_auth.
#[global] Opaque auth_option_frag.

Definition auth_option_URF F :=
  authURF $ optionURF F.
#[global] Instance auth_option_URF_contractive F :
  rFunctorContractive F →
  urFunctorContractive (auth_option_URF F).
Proof.
  apply _.
Qed.

Definition auth_option_RF F :=
  authRF $ optionURF F.
#[global] Instance auth_option_RF_contractive F :
  rFunctorContractive F →
  rFunctorContractive (auth_option_RF F).
Proof.
  apply _.
Qed.
