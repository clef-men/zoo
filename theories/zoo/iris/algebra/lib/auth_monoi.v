From iris.algebra Require Import
  proofmode_classes.

From zoo Require Import
  prelude.
From zoo.common Require Export
  relations.
From zoo.iris.algebra Require Export
  base.
From zoo.iris.algebra Require Import
  auth
  monopoi.
From zoo Require Import
  options.

#[local] Hint Resolve monopoi_principal_valid : core.

Section relation.
  Context {SI : sidx}.
  Context {A : ofe} (R : relation A).
  Context `{!Initial R}.

  Implicit Types a b : A.

  Notation Rs := (
    rtc R
  ).

  #[local] Instance Rs_antisymm `{!AntiSymm (=) Rs} :
    AntiSymm (≡) Rs.
  Proof.
    apply: rtc_equivalence_antisymm.
  Qed.

  Definition auth_monoi :=
    auth (monopoi Rs).
  Definition auth_monoi_R :=
    authR (monopoi_UR Rs).
  Definition auth_monoi_UR :=
    authUR (monopoi_UR Rs).

  Definition auth_monoi_auth dq a : auth_monoi_UR :=
    ●{dq} monopoi_principal Rs a ⋅ ◯ monopoi_principal Rs a.
  Definition auth_monoi_lb a : auth_monoi_UR :=
    ◯ monopoi_principal Rs a.

  #[global] Instance auth_monoi_auth_inj `{!AntiSymm (≡) Rs} :
    Inj2 (=) (≡) (≡) auth_monoi_auth
  | 10.
  Proof.
    rewrite /Inj2. setoid_rewrite auth_auth_frag_dfrac_op.
    intros * (-> & ?%(@inj _ _ (≡) _ _ _) & _). done.
  Qed.
  #[global] Instance auth_monoi_auth_inj_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} :
    Inj2 (=) (=) (≡) auth_monoi_auth
  | 9.
  Proof.
    intros ?* (-> & ->%leibniz_equiv)%(inj2 _). done.
  Qed.
  #[global] Instance auth_monoi_lb_inj `{!AntiSymm (≡) Rs} :
    Inj (≡) (≡) auth_monoi_lb
  | 10.
  Proof.
    intros a1 a2 ->%(inj auth_frag)%(@inj _ _ (≡) _ _ _). done.
  Qed.
  #[global] Instance auth_monoi_lb_inj_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} :
    Inj (=) (≡) auth_monoi_lb
  | 9.
  Proof.
    intros ?* ?%(@inj _ _ (≡) _ _ _). auto.
  Qed.

  #[global] Instance auth_monoi_cmra_discrete :
    CmraDiscrete auth_monoi_R.
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_monoi_auth_core_id a :
    CoreId (auth_monoi_auth DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_monoi_lb_core_id a :
    CoreId (auth_monoi_lb a).
  Proof.
    apply _.
  Qed.

  Lemma auth_monoi_auth_dfrac_op dq1 dq2 a :
    auth_monoi_auth (dq1 ⋅ dq2) a ≡ auth_monoi_auth dq1 a ⋅ auth_monoi_auth dq2 a.
  Proof.
    rewrite /auth_monoi_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)) -core_id_dup (comm _ (◯ _)) //.
  Qed.
  #[global] Instance auth_monoi_auth_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (auth_monoi_auth dq a) (auth_monoi_auth dq1 a) (auth_monoi_auth dq2 a).
  Proof.
    rewrite /IsOp' /IsOp => ->. rewrite auth_monoi_auth_dfrac_op //.
  Qed.

  Lemma auth_monoi_lb_op a a' :
    Rs a a' →
    auth_monoi_lb a' ≡ auth_monoi_lb a ⋅ auth_monoi_lb a'.
  Proof.
    intros. rewrite -auth_frag_op monopoi_principal_R_op //.
  Qed.

  Lemma auth_monoi_auth_lb_op dq a :
    auth_monoi_auth dq a ≡ auth_monoi_auth dq a ⋅ auth_monoi_lb a.
  Proof.
    rewrite /auth_monoi_auth /auth_monoi_lb.
    rewrite -!assoc -auth_frag_op -core_id_dup //.
  Qed.

  Lemma auth_monoi_auth_dfrac_valid dq a :
    ✓ auth_monoi_auth dq a ↔
    ✓ dq.
  Proof.
    rewrite auth_both_dfrac_valid_discrete. naive_solver.
  Qed.
  Lemma auth_monoi_auth_valid a :
    ✓ auth_monoi_auth (DfracOwn 1) a.
  Proof.
    rewrite auth_monoi_auth_dfrac_valid //.
  Qed.

  Lemma auth_monoi_auth_dfrac_op_valid `{!AntiSymm (≡) Rs} dq1 a1 dq2 a2 :
    ✓ (auth_monoi_auth dq1 a1 ⋅ auth_monoi_auth dq2 a2) →
      ✓ (dq1 ⋅ dq2) ∧
      a1 ≡ a2.
  Proof.
    rewrite /auth_monoi_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc.
    move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid.
    split; first naive_solver.
    apply (inj (monopoi_principal Rs)). naive_solver.
  Qed.
  Lemma auth_monoi_auth_dfrac_op_valid_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} dq1 a1 dq2 a2 :
    ✓ (auth_monoi_auth dq1 a1 ⋅ auth_monoi_auth dq2 a2) ↔
      ✓ (dq1 ⋅ dq2) ∧
      a1 = a2.
  Proof.
    split.
    - intros (? & ->%leibniz_equiv)%auth_monoi_auth_dfrac_op_valid. done.
    - rewrite /auth_monoi_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
      rewrite -auth_frag_op (comm _ (◯ _)) assoc.
      intros (? & ->).
      rewrite -core_id_dup -auth_auth_dfrac_op auth_both_dfrac_valid_discrete //.
  Qed.
  Lemma auth_monoi_auth_op_valid `{!AntiSymm (≡) Rs} a1 a2 :
    ✓ (auth_monoi_auth (DfracOwn 1) a1 ⋅ auth_monoi_auth (DfracOwn 1) a2) →
    False.
  Proof.
    intros ?%auth_monoi_auth_dfrac_op_valid. naive_solver.
  Qed.
  Lemma auth_monoi_auth_op_valid_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} a1 a2 :
    ✓ (auth_monoi_auth (DfracOwn 1) a1 ⋅ auth_monoi_auth (DfracOwn 1) a2) ↔
    False.
  Proof.
    rewrite auth_monoi_auth_dfrac_op_valid_L. naive_solver.
  Qed.

  Lemma auth_monoi_lb_op_valid a1 a2 :
    ✓ (auth_monoi_lb a1 ⋅ auth_monoi_lb a2) →
      ∃ a,
      Rs a1 a ∧
      Rs a2 a.
  Proof.
    rewrite auth_frag_op_valid.
    intros ?%monopoi_principal_op_valid. done.
  Qed.

  Lemma auth_monoi_both_dfrac_valid dq a b :
    ✓ (auth_monoi_auth dq a ⋅ auth_monoi_lb b) ↔
      ✓ dq ∧
      Rs b a.
  Proof.
    rewrite -assoc -auth_frag_op auth_both_dfrac_valid_discrete. split.
    - intros. split; first naive_solver.
      rewrite -monopoi_principal_included.
      eapply (cmra_included_trans (A := monopoi_UR _)).
      + apply cmra_included_r.
      + naive_solver.
    - intros (? & ?).
      rewrite (comm op) monopoi_principal_R_op //.
  Qed.
  Lemma auth_monoi_both_valid a b :
    ✓ (auth_monoi_auth (DfracOwn 1) a ⋅ auth_monoi_lb b) ↔
    Rs b a.
  Proof.
    rewrite auth_monoi_both_dfrac_valid dfrac_valid_own. naive_solver.
  Qed.

  Lemma auth_monoi_lb_mono a1 a2 :
    Rs a1 a2 →
    auth_monoi_lb a1 ≼ auth_monoi_lb a2.
  Proof.
    intros. apply auth_frag_mono. rewrite monopoi_principal_included //.
  Qed.

  Lemma auth_monoi_auth_dfrac_included `{!AntiSymm (≡) Rs} dq1 a1 dq2 a2 :
    auth_monoi_auth dq1 a1 ≼ auth_monoi_auth dq2 a2 →
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧
      a1 ≡ a2.
  Proof.
    rewrite auth_both_dfrac_included monopoi_principal_included.
    intros (? & ?%(@inj _ _ (≡) _ _ _) & _). done.
  Qed.
  Lemma auth_monoi_auth_dfrac_included_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} dq1 a1 dq2 a2 :
    auth_monoi_auth dq1 a1 ≼ auth_monoi_auth dq2 a2 ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧
      a1 = a2.
  Proof.
    split.
    - intros (? & ->%leibniz_equiv)%auth_monoi_auth_dfrac_included. done.
    - rewrite auth_both_dfrac_included monopoi_principal_included. naive_solver.
  Qed.
  Lemma auth_monoi_auth_included `{!AntiSymm (≡) Rs} a1 a2 :
    auth_monoi_auth (DfracOwn 1) a1 ≼ auth_monoi_auth (DfracOwn 1) a2 →
    a1 ≡ a2.
  Proof.
    intros ?%auth_monoi_auth_dfrac_included. naive_solver.
  Qed.
  Lemma auth_monoi_auth_included_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} a1 a2 :
    auth_monoi_auth (DfracOwn 1) a1 ≼ auth_monoi_auth (DfracOwn 1) a2 ↔
    a1 = a2.
  Proof.
    rewrite auth_monoi_auth_dfrac_included_L. naive_solver.
  Qed.

  Lemma auth_monoi_lb_included a1 dq a2 :
    auth_monoi_lb a1 ≼ auth_monoi_auth dq a2 ↔
    Rs a1 a2.
  Proof.
    rewrite auth_frag_included monopoi_principal_included //.
  Qed.
  Lemma auth_monoi_lb_included' a dq :
    auth_monoi_lb a ≼ auth_monoi_auth dq a.
  Proof.
    rewrite auth_monoi_lb_included //.
  Qed.

  Lemma auth_monoi_auth_persist dq a :
    auth_monoi_auth dq a ~~> auth_monoi_auth DfracDiscarded a.
  Proof.
    apply cmra_update_op_proper; last done.
    apply auth_update_auth_persist.
  Qed.
  Lemma auth_monoi_auth_update {a} a' :
    Rs a a' →
    auth_monoi_auth (DfracOwn 1) a ~~> auth_monoi_auth (DfracOwn 1) a'.
  Proof.
    intros. apply auth_update, monopoi_local_update_grow. done.
  Qed.

  Lemma auth_monoi_auth_local_update a a' :
    Rs a a' →
    (auth_monoi_auth (DfracOwn 1) a, auth_monoi_auth (DfracOwn 1) a) ~l~>
    (auth_monoi_auth (DfracOwn 1) a', auth_monoi_auth (DfracOwn 1) a').
  Proof.
    intros. apply auth_local_update.
    - apply monopoi_local_update_grow. done.
    - rewrite monopoi_principal_included //.
    - done.
  Qed.
End relation.

#[global] Opaque auth_monoi_auth.
#[global] Opaque auth_monoi_lb.
