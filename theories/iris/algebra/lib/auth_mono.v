From iris.algebra Require Import
  proofmode_classes.

From zebra Require Import
  prelude.
From zebra.iris.algebra Require Export
  base.
From zebra.iris.algebra Require Import
  auth
  mono.
From zebra Require Import
  options.

Section rel.
  Context `(rel : relation A).

  Implicit Types a b : A.

  Let A_O :=
    leibnizO A.
  #[local] Canonical A_O.

  Notation rels := (
    rtc rel
  ).

  Definition auth_mono :=
    auth (mra rels).
  Definition auth_mono_R :=
    authR (mraUR rels).
  Definition auth_mono_UR :=
    authUR (mraUR rels).

  Definition auth_mono_auth dq a : auth_mono_UR :=
    ●{dq} principal rels a ⋅ ◯ principal rels a.
  Definition auth_mono_lb a : auth_mono_UR :=
    ◯ principal rels a.

  #[global] Instance auth_mono_auth_inj `{!AntiSymm (=) rels} :
    Inj2 (=) (=) (≡) auth_mono_auth.
  Proof.
    rewrite /Inj2. setoid_rewrite auth_auth_frag_dfrac_op.
    intros * (-> & ->%(@inj _ _ (≡) _ _ _) & _). done.
  Qed.
  #[global] Instance auth_mono_lb_inj `{!AntiSymm (=) rels} :
    Inj (=) (≡) auth_mono_lb.
  Proof.
    intros a1 a2 ->%(inj auth_frag)%(@inj _ _ (≡) _ _ _). done.
  Qed.

  #[global] Instance auth_mono_cmra_discrete :
    CmraDiscrete auth_mono_R.
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_mono_auth_core_id a :
    CoreId (auth_mono_auth DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono_lb_core_id a :
    CoreId (auth_mono_lb a).
  Proof.
    apply _.
  Qed.

  Lemma auth_mono_auth_dfrac_op dq1 dq2 a :
    auth_mono_auth (dq1 ⋅ dq2) a ≡ auth_mono_auth dq1 a ⋅ auth_mono_auth dq2 a.
  Proof.
    rewrite /auth_mono_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)) -core_id_dup (comm _ (◯ _)) //.
  Qed.
  #[global] Instance auth_mono_auth_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (auth_mono_auth dq a) (auth_mono_auth dq1 a) (auth_mono_auth dq2 a).
  Proof.
    rewrite /IsOp' /IsOp => ->. rewrite auth_mono_auth_dfrac_op //.
  Qed.

  Lemma auth_mono_lb_op a a' :
    rels a a' →
    auth_mono_lb a' ≡ auth_mono_lb a ⋅ auth_mono_lb a'.
  Proof.
    intros. rewrite -auth_frag_op principal_R_op //.
  Qed.

  Lemma auth_mono_auth_frag_op dq a :
    auth_mono_auth dq a ≡ auth_mono_auth dq a ⋅ auth_mono_lb a.
  Proof.
    rewrite /auth_mono_auth /auth_mono_lb.
    rewrite -!assoc -auth_frag_op -core_id_dup //.
  Qed.

  Lemma auth_mono_auth_dfrac_valid dq a :
    ✓ auth_mono_auth dq a ↔
    ✓ dq.
  Proof.
    rewrite auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma auth_mono_auth_valid a :
    ✓ auth_mono_auth (DfracOwn 1) a.
  Proof.
    rewrite auth_mono_auth_dfrac_valid //.
  Qed.

  Lemma auth_mono_auth_dfrac_op_valid `{!AntiSymm (=) rels} dq1 a1 dq2 a2 :
    ✓ (auth_mono_auth dq1 a1 ⋅ auth_mono_auth dq2 a2) ↔
    ✓ (dq1 ⋅ dq2) ∧ a1 = a2.
  Proof.
    rewrite /auth_mono_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move => /cmra_valid_op_l /auth_auth_dfrac_op_valid.
      split; last apply (inj (principal rels)); naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      apply auth_both_dfrac_valid_discrete. done.
  Qed.
  Lemma auth_mono_auth_op_valid `{!AntiSymm (=) rels} a1 a2 :
    ✓ (auth_mono_auth (DfracOwn 1) a1 ⋅ auth_mono_auth (DfracOwn 1) a2) ↔
    False.
  Proof.
    rewrite auth_mono_auth_dfrac_op_valid. naive_solver.
  Qed.

  Lemma auth_mono_both_dfrac_valid dq a b :
    ✓ (auth_mono_auth dq a ⋅ auth_mono_lb b) ↔
    ✓ dq ∧ rels b a.
  Proof.
    rewrite -assoc -auth_frag_op auth_both_dfrac_valid_discrete. split.
    - intros. split; first naive_solver.
      rewrite -principal_included. etrans; [apply @cmra_included_r | naive_solver].
    - intros. rewrite (comm op) principal_R_op; naive_solver.
  Qed.
  Lemma auth_mono_both_valid a b :
    ✓ (auth_mono_auth (DfracOwn 1) a ⋅ auth_mono_lb b) ↔
    rels b a.
  Proof.
    rewrite auth_mono_both_dfrac_valid dfrac_valid_own. naive_solver.
  Qed.

  Lemma auth_mono_lb_mono a1 a2 :
    rels a1 a2 →
    auth_mono_lb a1 ≼ auth_mono_lb a2.
  Proof.
    intros. apply auth_frag_mono. rewrite principal_included //.
  Qed.

  Lemma auth_mono_auth_dfrac_included `{!AntiSymm (=) rels} dq1 a1 dq2 a2 :
    auth_mono_auth dq1 a1 ≼ auth_mono_auth dq2 a2 ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2.
  Proof.
    rewrite auth_both_dfrac_included principal_included. split; last naive_solver.
    intros (? & ->%(@inj _ _ (≡) _ _ _) & ?). done.
  Qed.
  Lemma auth_mono_auth_included `{!AntiSymm (=) rels} a1 a2 :
    auth_mono_auth (DfracOwn 1) a1 ≼ auth_mono_auth (DfracOwn 1) a2 ↔
    a1 = a2.
  Proof.
    rewrite auth_mono_auth_dfrac_included. naive_solver.
  Qed.

  Lemma auth_mono_lb_included a1 dq a2 :
    auth_mono_lb a1 ≼ auth_mono_auth dq a2 ↔
    rels a1 a2.
  Proof.
    rewrite auth_frag_included principal_included //.
  Qed.
  Lemma auth_mono_lb_included' a dq :
    auth_mono_lb a ≼ auth_mono_auth dq a.
  Proof.
    rewrite auth_mono_lb_included //.
  Qed.

  Lemma auth_mono_auth_persist dq a :
    auth_mono_auth dq a ~~> auth_mono_auth DfracDiscarded a.
  Proof.
    eapply cmra_update_op_proper; last done.
    eapply auth_update_auth_persist.
  Qed.
  Lemma auth_mono_auth_update {a} a' :
    rels a a' →
    auth_mono_auth (DfracOwn 1) a ~~> auth_mono_auth (DfracOwn 1) a'.
  Proof.
    intros. apply auth_update, mra_local_update_grow. done.
  Qed.

  Lemma auth_mono_auth_local_update a a' :
    rels a a' →
    (auth_mono_auth (DfracOwn 1) a, auth_mono_auth (DfracOwn 1) a) ~l~>
    (auth_mono_auth (DfracOwn 1) a', auth_mono_auth (DfracOwn 1) a').
  Proof.
    intros. apply auth_local_update.
    - apply mra_local_update_grow. done.
    - rewrite principal_included //.
    - done.
  Qed.
End rel.

#[global] Opaque auth_mono_auth.
#[global] Opaque auth_mono_lb.
