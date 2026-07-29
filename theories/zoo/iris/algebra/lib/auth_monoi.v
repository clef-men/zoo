Require Import iris.algebra.proofmode_classes.

Require Import zoo.prelude.
Require Export zoo.common.relations.
Require Export zoo.iris.algebra.base.
Require Import zoo.iris.algebra.auth.
Require Import zoo.iris.algebra.monopoi.
Require Import zoo.options.

#[local] Hint Resolve monopoi۰principalｰvalid : core.

Section relation.
  Context {SI : sidx}.
  Context {A : ofe} (R : relation A).
  Context `{!Initial R}.

  Implicit Type a b : A.

  Notation Rs := (
    rtc R
  ).

  #[local] Instance Rsｰantisymm `{!AntiSymm (=) Rs} :
    AntiSymm (≡) Rs.
  Proof.
    apply: rtcｰequivalenceｰantisymm.
  Qed.

  Definition auth_monoi :=
    auth (monopoi Rs).
  Definition auth_monoi۰R :=
    authR (monopoi۰UR Rs).
  Definition auth_monoi۰UR :=
    authUR (monopoi۰UR Rs).

  Definition auth_monoi۰auth dq a : auth_monoi۰UR :=
    ●{dq} monopoi۰principal Rs a ⋅ ◯ monopoi۰principal Rs a.
  Definition auth_monoi۰lb a : auth_monoi۰UR :=
    ◯ monopoi۰principal Rs a.

  #[global] Instance auth_monoi۰authｰinj `{!AntiSymm (≡) Rs} :
    Inj2 (=) (≡) (≡) auth_monoi۰auth
  | 10.
  Proof.
    rewrite /Inj2. setoid_rewrite authｰauthｰfragｰdfracｰop.
    intros * (-> & ?%(@inj _ _ (≡) _ _ _) & _). done.
  Qed.
  #[global] Instance auth_monoi۰authｰinjｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} :
    Inj2 (=) (=) (≡) auth_monoi۰auth
  | 9.
  Proof.
    intros ?* (-> & ->%leibniz_equiv)%(inj2 _). done.
  Qed.
  #[global] Instance auth_monoi۰lbｰinj `{!AntiSymm (≡) Rs} :
    Inj (≡) (≡) auth_monoi۰lb
  | 10.
  Proof.
    intros a1 a2 ->%(inj auth_frag)%(@inj _ _ (≡) _ _ _). done.
  Qed.
  #[global] Instance auth_monoi۰lbｰinjｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} :
    Inj (=) (≡) auth_monoi۰lb
  | 9.
  Proof.
    intros ?* ?%(@inj _ _ (≡) _ _ _). auto.
  Qed.

  #[global] Instance auth_monoiｰcmra_discrete :
    CmraDiscrete auth_monoi۰R.
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_monoi۰authｰcore_id a :
    CoreId (auth_monoi۰auth DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_monoi۰lbｰcore_id a :
    CoreId (auth_monoi۰lb a).
  Proof.
    apply _.
  Qed.

  Lemma auth_monoi۰authｰdfracｰop dq1 dq2 a :
    auth_monoi۰auth (dq1 ⋅ dq2) a ≡ auth_monoi۰auth dq1 a ⋅ auth_monoi۰auth dq2 a.
  Proof.
    rewrite /auth_monoi۰auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)) -core_id_dup (comm _ (◯ _)) //.
  Qed.
  #[global] Instance auth_monoi۰authｰdfracｰis_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (auth_monoi۰auth dq a) (auth_monoi۰auth dq1 a) (auth_monoi۰auth dq2 a).
  Proof.
    rewrite /IsOp' /IsOp => ->. rewrite auth_monoi۰authｰdfracｰop //.
  Qed.

  Lemma auth_monoi۰lbｰop a a' :
    Rs a a' →
    auth_monoi۰lb a' ≡ auth_monoi۰lb a ⋅ auth_monoi۰lb a'.
  Proof.
    intros. rewrite -auth_frag_op monopoi۰principalｰRｰop //.
  Qed.

  Lemma auth_monoi۰authｰlbｰop dq a :
    auth_monoi۰auth dq a ≡ auth_monoi۰auth dq a ⋅ auth_monoi۰lb a.
  Proof.
    rewrite /auth_monoi۰auth /auth_monoi۰lb.
    rewrite -!assoc -auth_frag_op -core_id_dup //.
  Qed.

  Lemma auth_monoi۰authｰdfracｰvalid dq a :
    ✓ auth_monoi۰auth dq a ↔
    ✓ dq.
  Proof.
    rewrite auth_both_dfrac_valid_discrete. naive_solver.
  Qed.
  Lemma auth_monoi۰authｰvalid a :
    ✓ auth_monoi۰auth (DfracOwn 1) a.
  Proof.
    rewrite auth_monoi۰authｰdfracｰvalid //.
  Qed.

  Lemma auth_monoi۰authｰdfracｰopｰvalid `{!AntiSymm (≡) Rs} dq1 a1 dq2 a2 :
    ✓ (auth_monoi۰auth dq1 a1 ⋅ auth_monoi۰auth dq2 a2) →
      ✓ (dq1 ⋅ dq2) ∧
      a1 ≡ a2.
  Proof.
    rewrite /auth_monoi۰auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc.
    move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid.
    split; first naive_solver.
    apply (inj (monopoi۰principal Rs)). naive_solver.
  Qed.
  Lemma auth_monoi۰authｰdfracｰopｰvalidｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} dq1 a1 dq2 a2 :
    ✓ (auth_monoi۰auth dq1 a1 ⋅ auth_monoi۰auth dq2 a2) ↔
      ✓ (dq1 ⋅ dq2) ∧
      a1 = a2.
  Proof.
    split.
    - intros (? & ->%leibniz_equiv)%auth_monoi۰authｰdfracｰopｰvalid. done.
    - rewrite /auth_monoi۰auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
      rewrite -auth_frag_op (comm _ (◯ _)) assoc.
      intros (? & ->).
      rewrite -core_id_dup -auth_auth_dfrac_op auth_both_dfrac_valid_discrete //.
  Qed.
  Lemma auth_monoi۰authｰopｰvalid `{!AntiSymm (≡) Rs} a1 a2 :
    ✓ (auth_monoi۰auth (DfracOwn 1) a1 ⋅ auth_monoi۰auth (DfracOwn 1) a2) →
    False.
  Proof.
    intros ?%auth_monoi۰authｰdfracｰopｰvalid. naive_solver.
  Qed.
  Lemma auth_monoi۰authｰopｰvalidｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} a1 a2 :
    ✓ (auth_monoi۰auth (DfracOwn 1) a1 ⋅ auth_monoi۰auth (DfracOwn 1) a2) ↔
    False.
  Proof.
    rewrite auth_monoi۰authｰdfracｰopｰvalidｰL. naive_solver.
  Qed.

  Lemma auth_monoi۰lbｰopｰvalid a1 a2 :
    ✓ (auth_monoi۰lb a1 ⋅ auth_monoi۰lb a2) →
      ∃ a,
      Rs a1 a ∧
      Rs a2 a.
  Proof.
    rewrite auth_frag_op_valid.
    intros ?%monopoi۰principalｰopｰvalid. done.
  Qed.

  Lemma auth_monoiｰbothｰdfracｰvalid dq a b :
    ✓ (auth_monoi۰auth dq a ⋅ auth_monoi۰lb b) ↔
      ✓ dq ∧
      Rs b a.
  Proof.
    rewrite -assoc -auth_frag_op auth_both_dfrac_valid_discrete. split.
    - intros. split; first naive_solver.
      rewrite -monopoi۰principalｰincluded.
      eapply (cmra_included_trans (A := monopoi۰UR _)).
      + apply cmra_included_r.
      + naive_solver.
    - intros (? & ?).
      rewrite (comm op) monopoi۰principalｰRｰop //.
  Qed.
  Lemma auth_monoiｰbothｰvalid a b :
    ✓ (auth_monoi۰auth (DfracOwn 1) a ⋅ auth_monoi۰lb b) ↔
    Rs b a.
  Proof.
    rewrite auth_monoiｰbothｰdfracｰvalid dfrac_valid_own. naive_solver.
  Qed.

  Lemma auth_monoi۰lbｰmono a1 a2 :
    Rs a1 a2 →
    auth_monoi۰lb a1 ≼ auth_monoi۰lb a2.
  Proof.
    intros. apply auth_frag_mono. rewrite monopoi۰principalｰincluded //.
  Qed.

  Lemma auth_monoi۰authｰdfracｰincluded `{!AntiSymm (≡) Rs} dq1 a1 dq2 a2 :
    auth_monoi۰auth dq1 a1 ≼ auth_monoi۰auth dq2 a2 →
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧
      a1 ≡ a2.
  Proof.
    rewrite auth_both_dfrac_included monopoi۰principalｰincluded.
    intros (? & ?%(@inj _ _ (≡) _ _ _) & _). done.
  Qed.
  Lemma auth_monoi۰authｰdfracｰincludedｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} dq1 a1 dq2 a2 :
    auth_monoi۰auth dq1 a1 ≼ auth_monoi۰auth dq2 a2 ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧
      a1 = a2.
  Proof.
    split.
    - intros (? & ->%leibniz_equiv)%auth_monoi۰authｰdfracｰincluded. done.
    - rewrite auth_both_dfrac_included monopoi۰principalｰincluded. naive_solver.
  Qed.
  Lemma auth_monoi۰authｰincluded `{!AntiSymm (≡) Rs} a1 a2 :
    auth_monoi۰auth (DfracOwn 1) a1 ≼ auth_monoi۰auth (DfracOwn 1) a2 →
    a1 ≡ a2.
  Proof.
    intros ?%auth_monoi۰authｰdfracｰincluded. naive_solver.
  Qed.
  Lemma auth_monoi۰authｰincludedｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} a1 a2 :
    auth_monoi۰auth (DfracOwn 1) a1 ≼ auth_monoi۰auth (DfracOwn 1) a2 ↔
    a1 = a2.
  Proof.
    rewrite auth_monoi۰authｰdfracｰincludedｰL. naive_solver.
  Qed.

  Lemma auth_monoi۰lbｰincluded a1 dq a2 :
    auth_monoi۰lb a1 ≼ auth_monoi۰auth dq a2 ↔
    Rs a1 a2.
  Proof.
    rewrite auth_frag_included monopoi۰principalｰincluded //.
  Qed.
  Lemma auth_monoi۰lbｰincluded' a dq :
    auth_monoi۰lb a ≼ auth_monoi۰auth dq a.
  Proof.
    rewrite auth_monoi۰lbｰincluded //.
  Qed.

  Lemma auth_monoi۰authｰpersist dq a :
    auth_monoi۰auth dq a ~~> auth_monoi۰auth DfracDiscarded a.
  Proof.
    apply cmra_update_op_proper; last done.
    apply auth_update_auth_persist.
  Qed.
  Lemma auth_monoi۰authｰupdate {a} a' :
    Rs a a' →
    auth_monoi۰auth (DfracOwn 1) a ~~> auth_monoi۰auth (DfracOwn 1) a'.
  Proof.
    intros. apply auth_update, monopoiｰlocal_updateｰgrow. done.
  Qed.

  Lemma auth_monoi۰authｰlocal_update a a' :
    Rs a a' →
    (auth_monoi۰auth (DfracOwn 1) a, auth_monoi۰auth (DfracOwn 1) a) ~l~>
    (auth_monoi۰auth (DfracOwn 1) a', auth_monoi۰auth (DfracOwn 1) a').
  Proof.
    intros. apply auth_local_update.
    - apply monopoiｰlocal_updateｰgrow. done.
    - rewrite monopoi۰principalｰincluded //.
    - done.
  Qed.
End relation.

#[global] Opaque auth_monoi۰auth.
#[global] Opaque auth_monoi۰lb.
