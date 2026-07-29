Require Import iris.algebra.auth.
Require Import iris.algebra.proofmode_classes.

Require Import zoo.prelude.
Require Export zoo.iris.algebra.base.
Require Import zoo.options.

Definition auth_option {SI : sidx} A :=
  auth (optionUR A).
Definition auth_option۰O {SI : sidx} A :=
  authO (optionUR A).
Definition auth_option۰R {SI : sidx} A :=
  authR (optionUR A).
Definition auth_option۰UR {SI : sidx} A :=
  authUR (optionUR A).

Definition auth_option۰auth {SI : sidx} {A : cmra} dq (a : A) : auth_option۰UR A :=
  ●{dq} (Some a).
Definition auth_option۰frag {SI : sidx} {A : cmra} (a : A) : auth_option۰UR A :=
  ◯ (Some a).

Notation "●O dq a" := (
  auth_option۰auth dq a
)(at level 20,
  dq custom dfrac at level 1,
  format "●O dq  a"
).
Notation "◯O a" := (
  auth_option۰frag a
)(at level 20
).

Section cmra.
  Context {SI : sidx}.
  Context {A : cmra}.

  Implicit Type a b : A.

  #[global] Instance auth_option۰authｰne dq :
    NonExpansive (@auth_option۰auth _ A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_option۰authｰproper dq :
    Proper ((≡) ==> (≡)) (@auth_option۰auth _ A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_option۰fragｰne :
    NonExpansive (@auth_option۰frag _ A).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_option۰fragｰproper :
    Proper ((≡) ==> (≡)) (@auth_option۰frag _ A).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance auth_option۰authｰdistｰinj n :
    Inj2 (=) (≡{n}≡) (≡{n}≡) (@auth_option۰auth _ A).
  Proof.
    rewrite /Inj2. intros * (-> & ?%(inj Some))%(inj2 auth_auth). done.
  Qed.
  #[global] Instance auth_option۰authｰinj :
    Inj2 (=) (≡) (≡) (@auth_option۰auth _ A).
  Proof.
    rewrite /Inj2. intros * (-> & ?%(inj Some))%(inj2 auth_auth). done.
  Qed.
  #[global] Instance auth_option۰fragｰdistｰinj n :
    Inj (≡{n}≡) (≡{n}≡) (@auth_option۰frag _ A).
  Proof.
    rewrite /Inj. intros * ?%(inj auth_frag)%(inj Some). done.
  Qed.
  #[global] Instance auth_option۰fragｰinj :
    Inj (≡) (≡) (@auth_option۰frag _ A).
  Proof.
    rewrite /Inj. intros * ?%(inj auth_frag)%(inj Some). done.
  Qed.

  #[global] Instance auth_option۰ofe_discrete :
    OfeDiscrete A →
    OfeDiscrete (auth_option۰O A).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option۰authｰdiscrete dq a :
    Discrete a →
    Discrete (●O{dq} a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option۰fragｰdiscrete a :
    Discrete a →
    Discrete (◯O a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option۰cmra_discrete :
    CmraDiscrete A →
    CmraDiscrete (auth_option۰R A).
  Proof.
    apply _.
  Qed.

  Lemma auth_option۰authｰdfracｰop dq1 dq2 a :
    ●O{dq1 ⋅ dq2} a ≡ ●O{dq1} a ⋅ ●O{dq2} a.
  Proof.
    apply auth_auth_dfrac_op.
  Qed.
  #[global] Instance auth_option۰authｰdfracｰis_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (●O{dq} a) (●O{dq1} a) (●O{dq2} a).
  Proof.
    apply _.
  Qed.

  Lemma auth_option۰fragｰop a b :
    ◯O (a ⋅ b) = ◯O a ⋅ ◯O b.
  Proof.
    rewrite -auth_frag_op //.
  Qed.
  Lemma auth_option۰fragｰmono a b :
    a ≼ b →
    ◯O a ≼ ◯O b.
  Proof.
    intros. apply auth_frag_mono, Some_included. naive_solver.
  Qed.
  Lemma auth_option۰fragｰcore `{!CmraTotal A} a :
    core (◯O a) = ◯O (core a).
  Proof.
    rewrite auth_frag_core -Some_core //.
  Qed.
  Lemma auth_optionｰbothｰcoreｰdiscarded `{!CmraTotal A} a b :
    core (●O□ a ⋅ ◯O b) ≡ ●O□ a ⋅ ◯O (core b).
  Proof.
    rewrite auth_both_core_discarded -Some_core //.
  Qed.
  Lemma auth_optionｰbothｰcoreｰfrac `{!CmraTotal A} q a b :
    core (●O{#q} a ⋅ ◯O b) ≡ ◯O (core b).
  Proof.
    rewrite auth_both_core_frac -Some_core //.
  Qed.

  #[global] Instance auth_option۰authｰcore_id a :
    CoreId (●O□ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option۰fragｰcore_id a :
    CoreId a →
    CoreId (◯O a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_optionｰbothｰcore_id a1 a2 :
    CoreId a2 →
    CoreId (●O□ a1 ⋅ ◯O a2).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option۰fragｰis_op a b1 b2 :
    IsOp a b1 b2 →
    IsOp' (◯O a) (◯O b1) (◯O b2).
  Proof.
    apply _.
  Qed.

  Lemma auth_option۰authｰdfracｰopｰinvN n dq1 a1 dq2 a2 :
    ✓{n} (●O{dq1} a1 ⋅ ●O{dq2} a2) →
    a1 ≡{n}≡ a2.
  Proof.
    intros. apply (inj Some). apply: auth_auth_dfrac_op_invN. done.
  Qed.
  Lemma auth_option۰authｰdfracｰopｰinv dq1 a1 dq2 a2 :
    ✓ (●O{dq1} a1 ⋅ ●O{dq2} a2) →
    a1 ≡ a2.
  Proof.
    intros. apply (inj Some). apply: auth_auth_dfrac_op_inv. done.
  Qed.
  Lemma auth_option۰authｰdfracｰopｰinvｰL `{!LeibnizEquiv A} dq1 a1 dq2 a2 :
    ✓ (●O{dq1} a1 ⋅ ●O{dq2} a2) →
    a1 = a2.
  Proof.
    intros. apply (inj Some). apply: auth_auth_dfrac_op_inv_L. done.
  Qed.

  Lemma auth_option۰authｰdfracｰvalidN n dq a :
    ✓{n} (●O{dq} a) ↔
    ✓ dq ∧ ✓{n} a.
  Proof.
    rewrite auth_auth_dfrac_validN //.
  Qed.
  Lemma auth_option۰authｰdfracｰvalid dq a :
    ✓ (●O{dq} a) ↔
    ✓ dq ∧ ✓ a.
  Proof.
    rewrite auth_auth_dfrac_valid //.
  Qed.
  Lemma auth_option۰authｰvalidN n a :
    ✓{n} (●O a) ↔
    ✓{n} a.
  Proof.
    rewrite auth_auth_validN //.
  Qed.
  Lemma auth_option۰authｰvalid a :
    ✓ (●O a) ↔
    ✓ a.
  Proof.
    rewrite auth_auth_valid //.
  Qed.

  Lemma auth_option۰authｰdfracｰopｰvalidN n dq1 a1 dq2 a2 :
    ✓{n} (●O{dq1} a1 ⋅ ●O{dq2} a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡{n}≡ a2 ∧ ✓{n} a1.
  Proof.
    rewrite auth_auth_dfrac_op_validN. split.
    - epose proof (inj Some).
      naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option۰authｰdfracｰopｰvalid dq1 a1 dq2 a2 :
    ✓ (●O{dq1} a1 ⋅ ●O{dq2} a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2 ∧ ✓ a1.
  Proof.
    rewrite auth_auth_dfrac_op_valid. split.
    - epose proof (@inj _ _ (≡) (≡) Some). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option۰authｰopｰvalidN n a1 a2 :
    ✓{n} (●O a1 ⋅ ●O a2) ↔
    False.
  Proof.
    rewrite auth_auth_op_validN //.
  Qed.
  Lemma auth_option۰authｰopｰvalid a1 a2 :
    ✓ (●O a1 ⋅ ●O a2) ↔
    False.
  Proof.
    rewrite auth_auth_op_valid //.
  Qed.

  Lemma auth_option۰fragｰvalidN n b :
    ✓{n} (◯O b) ↔
    ✓{n} b.
  Proof.
    rewrite auth_frag_validN //.
  Qed.
  Lemma auth_option۰fragｰvalidN₁ n b :
    ✓{n} (◯O b) →
    ✓{n} b.
  Proof.
    rewrite auth_option۰fragｰvalidN //.
  Qed.
  Lemma auth_option۰fragｰvalidN₂ n b :
    ✓{n} b →
    ✓{n} (◯O b).
  Proof.
    rewrite auth_option۰fragｰvalidN //.
  Qed.
  Lemma auth_option۰fragｰvalid b :
    ✓ (◯O b) ↔
    ✓ b.
  Proof.
    rewrite auth_frag_valid //.
  Qed.
  Lemma auth_option۰fragｰvalid₁ b :
    ✓ (◯O b) →
    ✓ b.
  Proof.
    rewrite auth_option۰fragｰvalid //.
  Qed.
  Lemma auth_option۰fragｰvalid₂ b :
    ✓ b →
    ✓ (◯O b).
  Proof.
    rewrite auth_option۰fragｰvalid //.
  Qed.

  Lemma auth_option۰fragｰopｰvalidN n b1 b2 :
    ✓{n} (◯O b1 ⋅ ◯O b2) ↔
    ✓{n} (b1 ⋅ b2).
  Proof.
    rewrite auth_frag_op_validN //.
  Qed.
  Lemma auth_option۰fragｰopｰvalidN₁ n b1 b2 :
    ✓{n} (◯O b1 ⋅ ◯O b2) →
    ✓{n} (b1 ⋅ b2).
  Proof.
    rewrite auth_option۰fragｰopｰvalidN //.
  Qed.
  Lemma auth_option۰fragｰopｰvalidN₂ n b1 b2 :
    ✓{n} (b1 ⋅ b2) →
    ✓{n} (◯O b1 ⋅ ◯O b2).
  Proof.
    rewrite auth_option۰fragｰopｰvalidN //.
  Qed.
  Lemma auth_option۰fragｰopｰvalid b1 b2 :
    ✓ (◯O b1 ⋅ ◯O b2) ↔
    ✓ (b1 ⋅ b2).
  Proof.
    rewrite auth_frag_op_valid //.
  Qed.
  Lemma auth_option۰fragｰopｰvalid₁ b1 b2 :
    ✓ (◯O b1 ⋅ ◯O b2) →
    ✓ (b1 ⋅ b2).
  Proof.
    rewrite auth_option۰fragｰopｰvalid //.
  Qed.
  Lemma auth_option۰fragｰopｰvalid₂ b1 b2 :
    ✓ (b1 ⋅ b2) →
    ✓ (◯O b1 ⋅ ◯O b2).
  Proof.
    rewrite auth_option۰fragｰopｰvalid //.
  Qed.

  Lemma auth_optionｰbothｰdfracｰvalidN n dq a b :
    ✓{n} (●O{dq} a ⋅ ◯O b) ↔
    ✓ dq ∧ (a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓{n} a.
  Proof.
    rewrite auth_both_dfrac_validN Some_includedN. naive_solver.
  Qed.
  Lemma auth_optionｰbothｰdfracｰvalid dq a b :
    ✓ (●O{dq} a ⋅ ◯O b) ↔
    ✓ dq ∧ (∀ n, a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓ a.
  Proof.
    rewrite auth_both_dfrac_valid. setoid_rewrite Some_includedN. naive_solver.
  Qed.
  Lemma auth_optionｰbothｰvalidN n a b :
    ✓{n} (●O a ⋅ ◯O b) ↔
    (a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓{n} a.
  Proof.
    rewrite auth_optionｰbothｰdfracｰvalidN. naive_solver done.
  Qed.
  Lemma auth_optionｰbothｰvalid a b :
    ✓ (●O a ⋅ ◯O b) ↔
    (∀ n, a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓ a.
  Proof.
    rewrite auth_optionｰbothｰdfracｰvalid. naive_solver done.
  Qed.

  Lemma auth_optionｰbothｰdfracｰvalidｰdiscrete `{!CmraDiscrete A} dq a b :
    ✓ (●O{dq} a ⋅ ◯O b) ↔
    ✓ dq ∧ (a ≡ b ∨ b ≼ a) ∧ ✓ a.
  Proof.
    rewrite auth_both_dfrac_valid_discrete Some_included. naive_solver.
  Qed.
  Lemma auth_optionｰbothｰvalidｰdiscrete `{!CmraDiscrete A} a b :
    ✓ (●O a ⋅ ◯O b) ↔
    (a ≡ b ∨ b ≼ a) ∧ ✓ a.
  Proof.
    rewrite auth_both_valid_discrete Some_included. naive_solver.
  Qed.

  Lemma auth_option۰authｰdfracｰincludedN n dq1 a1 dq2 a2 b :
    ●O{dq1} a1 ≼{n} ●O{dq2} a2 ⋅ ◯O b ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_auth_dfrac_includedN. split.
    - epose proof (inj Some).
      naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option۰authｰdfracｰincluded dq1 a1 dq2 a2 b :
    ●O{dq1} a1 ≼ ●O{dq2} a2 ⋅ ◯O b ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2.
  Proof.
    rewrite auth_auth_dfrac_included. split.
    - epose proof (@inj _ _ (≡) (≡) Some). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option۰authｰincludedN n a1 a2 b :
    ●O a1 ≼{n} ●O a2 ⋅ ◯O b ↔
    a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_option۰authｰdfracｰincludedN. naive_solver.
  Qed.
  Lemma auth_option۰authｰincluded a1 a2 b :
    ●O a1 ≼ ●O a2 ⋅ ◯O b ↔
    a1 ≡ a2.
  Proof.
    rewrite auth_option۰authｰdfracｰincluded. naive_solver.
  Qed.

  Lemma auth_option۰fragｰincludedN n dq a b1 b2 :
    ◯O b1 ≼{n} ●O{dq} a ⋅ ◯O b2 ↔
    b1 ≡{n}≡ b2 ∨ b1 ≼{n} b2.
  Proof.
    rewrite auth_frag_includedN Some_includedN //.
  Qed.
  Lemma auth_option۰fragｰincluded dq a b1 b2 :
    ◯O b1 ≼ ●O{dq} a ⋅ ◯O b2 ↔
    b1 ≡ b2 ∨ b1 ≼ b2.
  Proof.
    rewrite auth_frag_included Some_included //.
  Qed.

  Lemma auth_optionｰbothｰdfracｰincludedN n dq1 a1 dq2 a2 b1 b2 :
    ●O{dq1} a1 ⋅ ◯O b1 ≼{n} ●O{dq2} a2 ⋅ ◯O b2 ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ (b1 ≡{n}≡ b2 ∨ b1 ≼{n} b2).
  Proof.
    rewrite auth_both_dfrac_includedN Some_includedN. split.
    - epose proof (inj Some).
      naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_optionｰbothｰdfracｰincluded dq1 a1 dq2 a2 b1 b2 :
    ●O{dq1} a1 ⋅ ◯O b1 ≼ ●O{dq2} a2 ⋅ ◯O b2 ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 ∧ (b1 ≡ b2 ∨ b1 ≼ b2).
  Proof.
    rewrite auth_both_dfrac_included Some_included. split.
    - epose proof (@inj _ _ (≡) (≡) Some). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_optionｰbothｰincludedN n a1 a2 b1 b2 :
    ●O a1 ⋅ ◯O b1 ≼{n} ●O a2 ⋅ ◯O b2 ↔
    a1 ≡{n}≡ a2 ∧ (b1 ≡{n}≡ b2 ∨ b1 ≼{n} b2).
  Proof.
    rewrite auth_both_includedN Some_includedN. split.
    - epose proof (inj Some).
      naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_optionｰbothｰincluded a1 a2 b1 b2 :
    ●O a1 ⋅ ◯O b1 ≼ ●O a2 ⋅ ◯O b2 ↔
    a1 ≡ a2 ∧ (b1 ≡ b2 ∨ b1 ≼ b2).
  Proof.
    rewrite auth_both_included Some_included. split.
    - epose proof (@inj _ _ (≡) (≡) Some). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.

  Lemma auth_option۰authｰpersist dq a :
    ●O{dq} a ~~> ●O□ a.
  Proof.
    apply auth_update_auth_persist.
  Qed.
  Lemma auth_option۰authｰdfracｰupdate dq a b `{!CoreId b} :
    a ≡ b ∨ b ≼ a →
    ●O{dq} a ~~> ●O{dq} a ⋅ ◯O b.
  Proof.
    intros. apply auth_update_dfrac_alloc; first apply _.
    rewrite Some_included. naive_solver.
  Qed.
  Lemma auth_option۰authｰupdate a b `{!CoreId b} :
    a ≡ b ∨ b ≼ a →
    ●O a ~~> ●O a ⋅ ◯O b.
  Proof.
    apply auth_option۰authｰdfracｰupdate. done.
  Qed.
  Lemma auth_optionｰbothｰupdate a b a' b' :
    (a, b) ~l~> (a', b') →
    ●O a ⋅ ◯O b ~~> ●O a' ⋅ ◯O b'.
  Proof.
    intros. apply auth_update, option_local_update. done.
  Qed.

  Lemma auth_optionｰlocal_update a b0 b1 a' b0' b1' :
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

#[global] Opaque auth_option۰auth.
#[global] Opaque auth_option۰frag.

Definition auth_option۰URF {SI : sidx} F :=
  authURF $ optionURF F.
#[global] Instance auth_option۰URFｰcontractive {SI : sidx} F :
  rFunctorContractive F →
  urFunctorContractive (auth_option۰URF F).
Proof.
  apply _.
Qed.

Definition auth_option۰RF {SI : sidx} F :=
  authRF $ optionURF F.
#[global] Instance auth_option۰RFｰcontractive {SI : sidx} F :
  rFunctorContractive F →
  rFunctorContractive (auth_option۰RF F).
Proof.
  apply _.
Qed.
