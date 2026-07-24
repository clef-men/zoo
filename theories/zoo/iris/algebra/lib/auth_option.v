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

  #[global] Instance auth_option۰auth𑁒ne dq :
    NonExpansive (@auth_option۰auth _ A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_option۰auth𑁒proper dq :
    Proper ((≡) ==> (≡)) (@auth_option۰auth _ A dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_option۰frag𑁒ne :
    NonExpansive (@auth_option۰frag _ A).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_option۰frag𑁒proper :
    Proper ((≡) ==> (≡)) (@auth_option۰frag _ A).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance auth_option۰auth𑁒dist𑁒inj n :
    Inj2 (=) (≡{n}≡) (≡{n}≡) (@auth_option۰auth _ A).
  Proof.
    rewrite /Inj2. intros * (-> & ?%(inj Some))%(inj2 auth_auth). done.
  Qed.
  #[global] Instance auth_option۰auth𑁒inj :
    Inj2 (=) (≡) (≡) (@auth_option۰auth _ A).
  Proof.
    rewrite /Inj2. intros * (-> & ?%(inj Some))%(inj2 auth_auth). done.
  Qed.
  #[global] Instance auth_option۰frag𑁒dist𑁒inj n :
    Inj (≡{n}≡) (≡{n}≡) (@auth_option۰frag _ A).
  Proof.
    rewrite /Inj. intros * ?%(inj auth_frag)%(inj Some). done.
  Qed.
  #[global] Instance auth_option۰frag𑁒inj :
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
  #[global] Instance auth_option۰auth𑁒discrete dq a :
    Discrete a →
    Discrete (●O{dq} a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option۰frag𑁒discrete a :
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

  Lemma auth_option۰auth𑁒dfrac𑁒op dq1 dq2 a :
    ●O{dq1 ⋅ dq2} a ≡ ●O{dq1} a ⋅ ●O{dq2} a.
  Proof.
    apply auth_auth_dfrac_op.
  Qed.
  #[global] Instance auth_option۰auth𑁒dfrac𑁒is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (●O{dq} a) (●O{dq1} a) (●O{dq2} a).
  Proof.
    apply _.
  Qed.

  Lemma auth_option۰frag𑁒op a b :
    ◯O (a ⋅ b) = ◯O a ⋅ ◯O b.
  Proof.
    rewrite -auth_frag_op //.
  Qed.
  Lemma auth_option۰frag𑁒mono a b :
    a ≼ b →
    ◯O a ≼ ◯O b.
  Proof.
    intros. apply auth_frag_mono, Some_included. naive_solver.
  Qed.
  Lemma auth_option۰frag𑁒core `{!CmraTotal A} a :
    core (◯O a) = ◯O (core a).
  Proof.
    rewrite auth_frag_core -Some_core //.
  Qed.
  Lemma auth_option𑁒both𑁒core𑁒discarded `{!CmraTotal A} a b :
    core (●O□ a ⋅ ◯O b) ≡ ●O□ a ⋅ ◯O (core b).
  Proof.
    rewrite auth_both_core_discarded -Some_core //.
  Qed.
  Lemma auth_option𑁒both𑁒core𑁒frac `{!CmraTotal A} q a b :
    core (●O{#q} a ⋅ ◯O b) ≡ ◯O (core b).
  Proof.
    rewrite auth_both_core_frac -Some_core //.
  Qed.

  #[global] Instance auth_option۰auth𑁒core_id a :
    CoreId (●O□ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option۰frag𑁒core_id a :
    CoreId a →
    CoreId (◯O a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option𑁒both𑁒core_id a1 a2 :
    CoreId a2 →
    CoreId (●O□ a1 ⋅ ◯O a2).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_option۰frag𑁒is_op a b1 b2 :
    IsOp a b1 b2 →
    IsOp' (◯O a) (◯O b1) (◯O b2).
  Proof.
    apply _.
  Qed.

  Lemma auth_option۰auth𑁒dfrac𑁒op𑁒invN n dq1 a1 dq2 a2 :
    ✓{n} (●O{dq1} a1 ⋅ ●O{dq2} a2) →
    a1 ≡{n}≡ a2.
  Proof.
    intros. apply (inj Some). apply: auth_auth_dfrac_op_invN. done.
  Qed.
  Lemma auth_option۰auth𑁒dfrac𑁒op𑁒inv dq1 a1 dq2 a2 :
    ✓ (●O{dq1} a1 ⋅ ●O{dq2} a2) →
    a1 ≡ a2.
  Proof.
    intros. apply (inj Some). apply: auth_auth_dfrac_op_inv. done.
  Qed.
  Lemma auth_option۰auth𑁒dfrac𑁒op𑁒inv𑁒L `{!LeibnizEquiv A} dq1 a1 dq2 a2 :
    ✓ (●O{dq1} a1 ⋅ ●O{dq2} a2) →
    a1 = a2.
  Proof.
    intros. apply (inj Some). apply: auth_auth_dfrac_op_inv_L. done.
  Qed.

  Lemma auth_option۰auth𑁒dfrac𑁒validN n dq a :
    ✓{n} (●O{dq} a) ↔
    ✓ dq ∧ ✓{n} a.
  Proof.
    rewrite auth_auth_dfrac_validN //.
  Qed.
  Lemma auth_option۰auth𑁒dfrac𑁒valid dq a :
    ✓ (●O{dq} a) ↔
    ✓ dq ∧ ✓ a.
  Proof.
    rewrite auth_auth_dfrac_valid //.
  Qed.
  Lemma auth_option۰auth𑁒validN n a :
    ✓{n} (●O a) ↔
    ✓{n} a.
  Proof.
    rewrite auth_auth_validN //.
  Qed.
  Lemma auth_option۰auth𑁒valid a :
    ✓ (●O a) ↔
    ✓ a.
  Proof.
    rewrite auth_auth_valid //.
  Qed.

  Lemma auth_option۰auth𑁒dfrac𑁒op𑁒validN n dq1 a1 dq2 a2 :
    ✓{n} (●O{dq1} a1 ⋅ ●O{dq2} a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡{n}≡ a2 ∧ ✓{n} a1.
  Proof.
    rewrite auth_auth_dfrac_op_validN. split.
    - epose proof (inj Some).
      naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option۰auth𑁒dfrac𑁒op𑁒valid dq1 a1 dq2 a2 :
    ✓ (●O{dq1} a1 ⋅ ●O{dq2} a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2 ∧ ✓ a1.
  Proof.
    rewrite auth_auth_dfrac_op_valid. split.
    - epose proof (@inj _ _ (≡) (≡) Some). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option۰auth𑁒op𑁒validN n a1 a2 :
    ✓{n} (●O a1 ⋅ ●O a2) ↔
    False.
  Proof.
    rewrite auth_auth_op_validN //.
  Qed.
  Lemma auth_option۰auth𑁒op𑁒valid a1 a2 :
    ✓ (●O a1 ⋅ ●O a2) ↔
    False.
  Proof.
    rewrite auth_auth_op_valid //.
  Qed.

  Lemma auth_option۰frag𑁒validN n b :
    ✓{n} (◯O b) ↔
    ✓{n} b.
  Proof.
    rewrite auth_frag_validN //.
  Qed.
  Lemma auth_option۰frag𑁒validN₁ n b :
    ✓{n} (◯O b) →
    ✓{n} b.
  Proof.
    rewrite auth_option۰frag𑁒validN //.
  Qed.
  Lemma auth_option۰frag𑁒validN₂ n b :
    ✓{n} b →
    ✓{n} (◯O b).
  Proof.
    rewrite auth_option۰frag𑁒validN //.
  Qed.
  Lemma auth_option۰frag𑁒valid b :
    ✓ (◯O b) ↔
    ✓ b.
  Proof.
    rewrite auth_frag_valid //.
  Qed.
  Lemma auth_option۰frag𑁒valid₁ b :
    ✓ (◯O b) →
    ✓ b.
  Proof.
    rewrite auth_option۰frag𑁒valid //.
  Qed.
  Lemma auth_option۰frag𑁒valid₂ b :
    ✓ b →
    ✓ (◯O b).
  Proof.
    rewrite auth_option۰frag𑁒valid //.
  Qed.

  Lemma auth_option۰frag𑁒op𑁒validN n b1 b2 :
    ✓{n} (◯O b1 ⋅ ◯O b2) ↔
    ✓{n} (b1 ⋅ b2).
  Proof.
    rewrite auth_frag_op_validN //.
  Qed.
  Lemma auth_option۰frag𑁒op𑁒validN₁ n b1 b2 :
    ✓{n} (◯O b1 ⋅ ◯O b2) →
    ✓{n} (b1 ⋅ b2).
  Proof.
    rewrite auth_option۰frag𑁒op𑁒validN //.
  Qed.
  Lemma auth_option۰frag𑁒op𑁒validN₂ n b1 b2 :
    ✓{n} (b1 ⋅ b2) →
    ✓{n} (◯O b1 ⋅ ◯O b2).
  Proof.
    rewrite auth_option۰frag𑁒op𑁒validN //.
  Qed.
  Lemma auth_option۰frag𑁒op𑁒valid b1 b2 :
    ✓ (◯O b1 ⋅ ◯O b2) ↔
    ✓ (b1 ⋅ b2).
  Proof.
    rewrite auth_frag_op_valid //.
  Qed.
  Lemma auth_option۰frag𑁒op𑁒valid₁ b1 b2 :
    ✓ (◯O b1 ⋅ ◯O b2) →
    ✓ (b1 ⋅ b2).
  Proof.
    rewrite auth_option۰frag𑁒op𑁒valid //.
  Qed.
  Lemma auth_option۰frag𑁒op𑁒valid₂ b1 b2 :
    ✓ (b1 ⋅ b2) →
    ✓ (◯O b1 ⋅ ◯O b2).
  Proof.
    rewrite auth_option۰frag𑁒op𑁒valid //.
  Qed.

  Lemma auth_option𑁒both𑁒dfrac𑁒validN n dq a b :
    ✓{n} (●O{dq} a ⋅ ◯O b) ↔
    ✓ dq ∧ (a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓{n} a.
  Proof.
    rewrite auth_both_dfrac_validN Some_includedN. naive_solver.
  Qed.
  Lemma auth_option𑁒both𑁒dfrac𑁒valid dq a b :
    ✓ (●O{dq} a ⋅ ◯O b) ↔
    ✓ dq ∧ (∀ n, a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓ a.
  Proof.
    rewrite auth_both_dfrac_valid. setoid_rewrite Some_includedN. naive_solver.
  Qed.
  Lemma auth_option𑁒both𑁒validN n a b :
    ✓{n} (●O a ⋅ ◯O b) ↔
    (a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓{n} a.
  Proof.
    rewrite auth_option𑁒both𑁒dfrac𑁒validN. naive_solver done.
  Qed.
  Lemma auth_option𑁒both𑁒valid a b :
    ✓ (●O a ⋅ ◯O b) ↔
    (∀ n, a ≡{n}≡ b ∨ b ≼{n} a) ∧ ✓ a.
  Proof.
    rewrite auth_option𑁒both𑁒dfrac𑁒valid. naive_solver done.
  Qed.

  Lemma auth_option𑁒both𑁒dfrac𑁒valid𑁒discrete `{!CmraDiscrete A} dq a b :
    ✓ (●O{dq} a ⋅ ◯O b) ↔
    ✓ dq ∧ (a ≡ b ∨ b ≼ a) ∧ ✓ a.
  Proof.
    rewrite auth_both_dfrac_valid_discrete Some_included. naive_solver.
  Qed.
  Lemma auth_option𑁒both𑁒valid𑁒discrete `{!CmraDiscrete A} a b :
    ✓ (●O a ⋅ ◯O b) ↔
    (a ≡ b ∨ b ≼ a) ∧ ✓ a.
  Proof.
    rewrite auth_both_valid_discrete Some_included. naive_solver.
  Qed.

  Lemma auth_option۰auth𑁒dfrac𑁒includedN n dq1 a1 dq2 a2 b :
    ●O{dq1} a1 ≼{n} ●O{dq2} a2 ⋅ ◯O b ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_auth_dfrac_includedN. split.
    - epose proof (inj Some).
      naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option۰auth𑁒dfrac𑁒included dq1 a1 dq2 a2 b :
    ●O{dq1} a1 ≼ ●O{dq2} a2 ⋅ ◯O b ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2.
  Proof.
    rewrite auth_auth_dfrac_included. split.
    - epose proof (@inj _ _ (≡) (≡) Some). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option۰auth𑁒includedN n a1 a2 b :
    ●O a1 ≼{n} ●O a2 ⋅ ◯O b ↔
    a1 ≡{n}≡ a2.
  Proof.
    rewrite auth_option۰auth𑁒dfrac𑁒includedN. naive_solver.
  Qed.
  Lemma auth_option۰auth𑁒included a1 a2 b :
    ●O a1 ≼ ●O a2 ⋅ ◯O b ↔
    a1 ≡ a2.
  Proof.
    rewrite auth_option۰auth𑁒dfrac𑁒included. naive_solver.
  Qed.

  Lemma auth_option۰frag𑁒includedN n dq a b1 b2 :
    ◯O b1 ≼{n} ●O{dq} a ⋅ ◯O b2 ↔
    b1 ≡{n}≡ b2 ∨ b1 ≼{n} b2.
  Proof.
    rewrite auth_frag_includedN Some_includedN //.
  Qed.
  Lemma auth_option۰frag𑁒included dq a b1 b2 :
    ◯O b1 ≼ ●O{dq} a ⋅ ◯O b2 ↔
    b1 ≡ b2 ∨ b1 ≼ b2.
  Proof.
    rewrite auth_frag_included Some_included //.
  Qed.

  Lemma auth_option𑁒both𑁒dfrac𑁒includedN n dq1 a1 dq2 a2 b1 b2 :
    ●O{dq1} a1 ⋅ ◯O b1 ≼{n} ●O{dq2} a2 ⋅ ◯O b2 ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ (b1 ≡{n}≡ b2 ∨ b1 ≼{n} b2).
  Proof.
    rewrite auth_both_dfrac_includedN Some_includedN. split.
    - epose proof (inj Some).
      naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option𑁒both𑁒dfrac𑁒included dq1 a1 dq2 a2 b1 b2 :
    ●O{dq1} a1 ⋅ ◯O b1 ≼ ●O{dq2} a2 ⋅ ◯O b2 ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 ∧ (b1 ≡ b2 ∨ b1 ≼ b2).
  Proof.
    rewrite auth_both_dfrac_included Some_included. split.
    - epose proof (@inj _ _ (≡) (≡) Some). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option𑁒both𑁒includedN n a1 a2 b1 b2 :
    ●O a1 ⋅ ◯O b1 ≼{n} ●O a2 ⋅ ◯O b2 ↔
    a1 ≡{n}≡ a2 ∧ (b1 ≡{n}≡ b2 ∨ b1 ≼{n} b2).
  Proof.
    rewrite auth_both_includedN Some_includedN. split.
    - epose proof (inj Some).
      naive_solver.
    - naive_solver solve_proper.
  Qed.
  Lemma auth_option𑁒both𑁒included a1 a2 b1 b2 :
    ●O a1 ⋅ ◯O b1 ≼ ●O a2 ⋅ ◯O b2 ↔
    a1 ≡ a2 ∧ (b1 ≡ b2 ∨ b1 ≼ b2).
  Proof.
    rewrite auth_both_included Some_included. split.
    - epose proof (@inj _ _ (≡) (≡) Some). naive_solver apply _.
    - naive_solver solve_proper.
  Qed.

  Lemma auth_option۰auth𑁒persist dq a :
    ●O{dq} a ~~> ●O□ a.
  Proof.
    apply auth_update_auth_persist.
  Qed.
  Lemma auth_option۰auth𑁒dfrac𑁒update dq a b `{!CoreId b} :
    a ≡ b ∨ b ≼ a →
    ●O{dq} a ~~> ●O{dq} a ⋅ ◯O b.
  Proof.
    intros. apply auth_update_dfrac_alloc; first apply _.
    rewrite Some_included. naive_solver.
  Qed.
  Lemma auth_option۰auth𑁒update a b `{!CoreId b} :
    a ≡ b ∨ b ≼ a →
    ●O a ~~> ●O a ⋅ ◯O b.
  Proof.
    apply auth_option۰auth𑁒dfrac𑁒update. done.
  Qed.
  Lemma auth_option𑁒both𑁒update a b a' b' :
    (a, b) ~l~> (a', b') →
    ●O a ⋅ ◯O b ~~> ●O a' ⋅ ◯O b'.
  Proof.
    intros. apply auth_update, option_local_update. done.
  Qed.

  Lemma auth_option𑁒local_update a b0 b1 a' b0' b1' :
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
#[global] Instance auth_option۰URF𑁒contractive {SI : sidx} F :
  rFunctorContractive F →
  urFunctorContractive (auth_option۰URF F).
Proof.
  apply _.
Qed.

Definition auth_option۰RF {SI : sidx} F :=
  authRF $ optionURF F.
#[global] Instance auth_option۰RF𑁒contractive {SI : sidx} F :
  rFunctorContractive F →
  rFunctorContractive (auth_option۰RF F).
Proof.
  apply _.
Qed.
