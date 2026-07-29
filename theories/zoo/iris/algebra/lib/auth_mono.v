Require Import iris.algebra.proofmode_classes.

Require Import zoo.prelude.
Require Import zoo.common.relations.
Require Export zoo.iris.algebra.base.
Require Import zoo.iris.algebra.auth.
Require Import zoo.iris.algebra.monopo.
Require Import zoo.options.

#[local] Hint Resolve monopo۰principalｰvalid : core.

Section relation.
  Context {SI : sidx}.
  Context {A : ofe} (R : relation A).

  Implicit Type a b : A.

  Notation Rs := (
    rtc R
  ).

  #[local] Instance Rsｰantisymm `{!AntiSymm (=) Rs} :
    AntiSymm (≡) Rs.
  Proof.
    apply: rtcｰequivalenceｰantisymm.
  Qed.

  Definition auth_mono :=
    auth (monopo Rs).
  Definition auth_mono۰R :=
    authR (monopo۰UR Rs).
  Definition auth_mono۰UR :=
    authUR (monopo۰UR Rs).

  Definition auth_mono۰auth dq a : auth_mono۰UR :=
    ●{dq} monopo۰principal Rs a ⋅ ◯ monopo۰principal Rs a.
  Definition auth_mono۰lb a : auth_mono۰UR :=
    ◯ monopo۰principal Rs a.

  #[global] Instance auth_mono۰authｰinj `{!AntiSymm (≡) Rs} :
    Inj2 (=) (≡) (≡) auth_mono۰auth
  | 10.
  Proof.
    rewrite /Inj2. setoid_rewrite authｰauthｰfragｰdfracｰop.
    intros * (-> & ?%(@inj _ _ (≡) _ _ _) & _). done.
  Qed.
  #[global] Instance auth_mono۰authｰinjｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} :
    Inj2 (=) (=) (≡) auth_mono۰auth
  | 9.
  Proof.
    intros ?* (-> & ->%leibniz_equiv)%(inj2 _). done.
  Qed.
  #[global] Instance auth_mono۰lbｰinj `{!AntiSymm (≡) Rs} :
    Inj (≡) (≡) auth_mono۰lb
  | 10.
  Proof.
    intros a1 a2 ->%(inj auth_frag)%(@inj _ _ (≡) _ _ _). done.
  Qed.
  #[global] Instance auth_mono۰lbｰinjｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} :
    Inj (=) (≡) auth_mono۰lb
  | 9.
  Proof.
    intros ?* ?%(@inj _ _ (≡) _ _ _). auto.
  Qed.

  #[global] Instance auth_monoｰcmra_discrete :
    CmraDiscrete auth_mono۰R.
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_mono۰authｰcore_id a :
    CoreId (auth_mono۰auth DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono۰lbｰcore_id a :
    CoreId (auth_mono۰lb a).
  Proof.
    apply _.
  Qed.

  Lemma auth_mono۰authｰdfracｰop dq1 dq2 a :
    auth_mono۰auth (dq1 ⋅ dq2) a ≡ auth_mono۰auth dq1 a ⋅ auth_mono۰auth dq2 a.
  Proof.
    rewrite /auth_mono۰auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)) -core_id_dup (comm _ (◯ _)) //.
  Qed.
  #[global] Instance auth_mono۰authｰdfracｰis_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 →
    IsOp' (auth_mono۰auth dq a) (auth_mono۰auth dq1 a) (auth_mono۰auth dq2 a).
  Proof.
    rewrite /IsOp' /IsOp => ->. rewrite auth_mono۰authｰdfracｰop //.
  Qed.

  Lemma auth_mono۰lbｰop a a' :
    Rs a a' →
    auth_mono۰lb a' ≡ auth_mono۰lb a ⋅ auth_mono۰lb a'.
  Proof.
    intros. rewrite -auth_frag_op monopo۰principalｰRｰop //.
  Qed.

  Lemma auth_monoｰauthｰlbｰop dq a :
    auth_mono۰auth dq a ≡ auth_mono۰auth dq a ⋅ auth_mono۰lb a.
  Proof.
    rewrite /auth_mono۰auth /auth_mono۰lb.
    rewrite -!assoc -auth_frag_op -core_id_dup //.
  Qed.

  Lemma auth_mono۰authｰdfracｰvalid dq a :
    ✓ auth_mono۰auth dq a ↔
    ✓ dq.
  Proof.
    rewrite auth_both_dfrac_valid_discrete. naive_solver.
  Qed.
  Lemma auth_mono۰authｰvalid a :
    ✓ auth_mono۰auth (DfracOwn 1) a.
  Proof.
    rewrite auth_mono۰authｰdfracｰvalid //.
  Qed.

  Lemma auth_mono۰authｰdfracｰopｰvalid `{!AntiSymm (≡) Rs} dq1 a1 dq2 a2 :
    ✓ (auth_mono۰auth dq1 a1 ⋅ auth_mono۰auth dq2 a2) →
      ✓ (dq1 ⋅ dq2) ∧
      a1 ≡ a2.
  Proof.
    rewrite /auth_mono۰auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc.
    move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid.
    split; first naive_solver.
    apply (inj (monopo۰principal Rs)). naive_solver.
  Qed.
  Lemma auth_mono۰authｰdfracｰopｰvalidｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} dq1 a1 dq2 a2 :
    ✓ (auth_mono۰auth dq1 a1 ⋅ auth_mono۰auth dq2 a2) ↔
      ✓ (dq1 ⋅ dq2) ∧
      a1 = a2.
  Proof.
    split.
    - intros (? & ->%leibniz_equiv)%auth_mono۰authｰdfracｰopｰvalid. done.
    - rewrite /auth_mono۰auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
      rewrite -auth_frag_op (comm _ (◯ _)) assoc.
      intros (? & ->).
      rewrite -core_id_dup -auth_auth_dfrac_op auth_both_dfrac_valid_discrete //.
  Qed.
  Lemma auth_mono۰authｰopｰvalid `{!AntiSymm (≡) Rs} a1 a2 :
    ✓ (auth_mono۰auth (DfracOwn 1) a1 ⋅ auth_mono۰auth (DfracOwn 1) a2) →
    False.
  Proof.
    intros ?%auth_mono۰authｰdfracｰopｰvalid. naive_solver.
  Qed.
  Lemma auth_mono۰authｰopｰvalidｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} a1 a2 :
    ✓ (auth_mono۰auth (DfracOwn 1) a1 ⋅ auth_mono۰auth (DfracOwn 1) a2) ↔
    False.
  Proof.
    rewrite auth_mono۰authｰdfracｰopｰvalidｰL. naive_solver.
  Qed.

  Lemma auth_mono۰lbｰopｰvalid a1 a2 :
    ✓ (auth_mono۰lb a1 ⋅ auth_mono۰lb a2) →
      ∃ a,
      Rs a1 a ∧
      Rs a2 a.
  Proof.
    rewrite auth_frag_op_valid.
    intros ?%monopo۰principalｰopｰvalid. done.
  Qed.

  Lemma auth_monoｰbothｰdfracｰvalid dq a b :
    ✓ (auth_mono۰auth dq a ⋅ auth_mono۰lb b) ↔
      ✓ dq ∧
      Rs b a.
  Proof.
    rewrite -assoc -auth_frag_op auth_both_dfrac_valid_discrete. split.
    - intros. split; first naive_solver.
      rewrite -monopo۰principalｰincluded.
      eapply (cmra_included_trans (A := monopo۰UR _)).
      + apply cmra_included_r.
      + naive_solver.
    - intros (? & ?).
      rewrite (comm op) monopo۰principalｰRｰop //.
  Qed.
  Lemma auth_monoｰbothｰvalid a b :
    ✓ (auth_mono۰auth (DfracOwn 1) a ⋅ auth_mono۰lb b) ↔
    Rs b a.
  Proof.
    rewrite auth_monoｰbothｰdfracｰvalid dfrac_valid_own. naive_solver.
  Qed.

  Lemma auth_mono۰lbｰmono a1 a2 :
    Rs a1 a2 →
    auth_mono۰lb a1 ≼ auth_mono۰lb a2.
  Proof.
    intros. apply auth_frag_mono. rewrite monopo۰principalｰincluded //.
  Qed.

  Lemma auth_mono۰authｰdfracｰincluded `{!AntiSymm (≡) Rs} dq1 a1 dq2 a2 :
    auth_mono۰auth dq1 a1 ≼ auth_mono۰auth dq2 a2 →
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧
      a1 ≡ a2.
  Proof.
    rewrite auth_both_dfrac_included monopo۰principalｰincluded.
    intros (? & ?%(@inj _ _ (≡) _ _ _) & _). done.
  Qed.
  Lemma auth_mono۰authｰdfracｰincludedｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} dq1 a1 dq2 a2 :
    auth_mono۰auth dq1 a1 ≼ auth_mono۰auth dq2 a2 ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧
      a1 = a2.
  Proof.
    split.
    - intros (? & ->%leibniz_equiv)%auth_mono۰authｰdfracｰincluded. done.
    - rewrite auth_both_dfrac_included monopo۰principalｰincluded. naive_solver.
  Qed.
  Lemma auth_mono۰authｰincluded `{!AntiSymm (≡) Rs} a1 a2 :
    auth_mono۰auth (DfracOwn 1) a1 ≼ auth_mono۰auth (DfracOwn 1) a2 →
    a1 ≡ a2.
  Proof.
    intros ?%auth_mono۰authｰdfracｰincluded. naive_solver.
  Qed.
  Lemma auth_mono۰authｰincludedｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} a1 a2 :
    auth_mono۰auth (DfracOwn 1) a1 ≼ auth_mono۰auth (DfracOwn 1) a2 ↔
    a1 = a2.
  Proof.
    rewrite auth_mono۰authｰdfracｰincludedｰL. naive_solver.
  Qed.

  Lemma auth_mono۰lbｰincluded a1 dq a2 :
    auth_mono۰lb a1 ≼ auth_mono۰auth dq a2 ↔
    Rs a1 a2.
  Proof.
    rewrite auth_frag_included monopo۰principalｰincluded //.
  Qed.
  Lemma auth_mono۰lbｰincluded' a dq :
    auth_mono۰lb a ≼ auth_mono۰auth dq a.
  Proof.
    rewrite auth_mono۰lbｰincluded //.
  Qed.

  Lemma auth_mono۰authｰpersist dq a :
    auth_mono۰auth dq a ~~> auth_mono۰auth DfracDiscarded a.
  Proof.
    apply cmra_update_op_proper; last done.
    apply auth_update_auth_persist.
  Qed.
  Lemma auth_mono۰authｰupdate {a} a' :
    Rs a a' →
    auth_mono۰auth (DfracOwn 1) a ~~> auth_mono۰auth (DfracOwn 1) a'.
  Proof.
    intros. apply auth_update, monopoｰlocal_updateｰgrow. done.
  Qed.

  Lemma auth_mono۰authｰlocal_update a a' :
    Rs a a' →
    (auth_mono۰auth (DfracOwn 1) a, auth_mono۰auth (DfracOwn 1) a) ~l~>
    (auth_mono۰auth (DfracOwn 1) a', auth_mono۰auth (DfracOwn 1) a').
  Proof.
    intros. apply auth_local_update.
    - apply monopoｰlocal_updateｰgrow. done.
    - rewrite monopo۰principalｰincluded //.
    - done.
  Qed.
End relation.

#[global] Opaque auth_mono۰auth.
#[global] Opaque auth_mono۰lb.
