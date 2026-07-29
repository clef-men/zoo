Require Import zoo.prelude.
Require Export zoo.common.relations.
Require Import zoo.iris.algebra.lib.auth_monoi.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthMonoiG Σ {A : ofe} (R : relation A) `{!Initial R} :=
  { #[local] auth_monoi۰G۰inG :: inG Σ (auth_monoi۰UR R)
  }.

Definition auth_monoi۰Σ {A : ofe} (R : relation A) `{!Initial R} :=
  #[GFunctor (auth_monoi۰UR R)
  ].
#[global] Instance subGｰauth_monoi۰Σ Σ {A : ofe} (R : relation A) `{!Initial R} :
  subG (auth_monoi۰Σ R) Σ →
  AuthMonoiG Σ R.
Proof.
  solve_inG.
Qed.

Section auth_monoi۰G.
  Context {A : ofe} (R : relation A) `{!Initial R}.
  Context `{auth_monoi۰G : !AuthMonoiG Σ R}.

  Implicit Type a : A.

  Notation Rs := (
    rtc R
  ).

  Definition auth_monoi۰auth γ dq a :=
    own γ (auth_monoi۰auth R dq a).
  Definition auth_monoi۰lb γ a :=
    own γ (auth_monoi۰lb R a).

  #[global] Instance auth_monoi۰authｰtimeless γ dq a :
    Timeless (auth_monoi۰auth γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_monoi۰lbｰtimeless γ a :
    Timeless (auth_monoi۰lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_monoi۰authｰpersistent γ a :
    Persistent (auth_monoi۰auth γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_monoi۰lbｰpersistent γ a :
    Persistent (auth_monoi۰lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_monoi۰authｰfractional γ a :
    Fractional (λ q, auth_monoi۰auth γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -auth_monoi۰authｰdfracｰop //.
  Qed.
  #[global] Instance auth_monoi۰authｰas_fractional γ q a :
    AsFractional (auth_monoi۰auth γ (DfracOwn q) a) (λ q, auth_monoi۰auth γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_monoiｰalloc a :
    ⊢ |==>
      ∃ γ,
      auth_monoi۰auth γ (DfracOwn 1) a.
  Proof.
    apply own_alloc, auth_monoi۰authｰvalid.
  Qed.

  Lemma auth_monoi۰authｰvalid γ dq a :
    auth_monoi۰auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%auth_monoi۰authｰdfracｰvalid.
    iSteps.
  Qed.
  Lemma auth_monoi۰authｰcombine `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
      ⌜a1 = a2⌝ ∗
      auth_monoi۰auth γ (dq1 ⋅ dq2) a1.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(_ & <-)%auth_monoi۰authｰdfracｰopｰvalidｰL.
    rewrite -auth_monoi۰authｰdfracｰop. iSteps.
  Qed.
  Lemma auth_monoi۰authｰvalidｰ2 `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & ?)%auth_monoi۰authｰdfracｰopｰvalid.
    iSteps.
  Qed.
  Lemma auth_monoi۰authｰvalidｰ2ｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & <-)%auth_monoi۰authｰdfracｰopｰvalidｰL.
    iSteps.
  Qed.
  Lemma auth_monoi۰authｰagree `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
    ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi۰authｰvalidｰ2 with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_monoi۰authｰagreeｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi۰authｰvalidｰ2ｰL with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_monoi۰authｰdfracｰne `{!AntiSymm (≡) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_monoi۰auth γ1 dq1 a1 -∗
    auth_monoi۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_monoi۰authｰvalidｰ2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_monoi۰authｰdfracｰneｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_monoi۰auth γ1 dq1 a1 -∗
    auth_monoi۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_monoi۰authｰvalidｰ2ｰL with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_monoi۰authｰne `{!AntiSymm (≡) Rs} γ1 a1 γ2 dq2 a2 :
    auth_monoi۰auth γ1 (DfracOwn 1) a1 -∗
    auth_monoi۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_monoi۰authｰdfracｰne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_monoi۰authｰneｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 a1 γ2 dq2 a2 :
    auth_monoi۰auth γ1 (DfracOwn 1) a1 -∗
    auth_monoi۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_monoi۰authｰdfracｰneｰL; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_monoi۰authｰexclusive `{!AntiSymm (≡) Rs} γ a1 dq2 a2 :
    auth_monoi۰auth γ (DfracOwn 1) a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi۰authｰne with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_monoi۰authｰexclusiveｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 dq2 a2 :
    auth_monoi۰auth γ (DfracOwn 1) a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi۰authｰneｰL with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_monoi۰authｰpersist γ dq a :
    auth_monoi۰auth γ dq a ⊢ |==>
    auth_monoi۰auth γ DfracDiscarded a.
  Proof.
    apply own_update, auth_monoi۰authｰpersist.
  Qed.

  Lemma auth_monoi۰lbｰinitial γ :
    ⊢ |==>
      auth_monoi۰lb γ initial.
  Proof.
    apply own_unit.
  Qed.
  Lemma auth_monoi۰lbｰmono {γ a} a' :
    Rs a' a →
    auth_monoi۰lb γ a ⊢
    auth_monoi۰lb γ a'.
  Proof.
    intros. apply own_mono, auth_monoi۰lbｰmono. done.
  Qed.
  Lemma auth_monoi۰lbｰmono' {γ a} a' :
    R a' a →
    auth_monoi۰lb γ a ⊢
    auth_monoi۰lb γ a'.
  Proof.
    intros. apply auth_monoi۰lbｰmono, rtc_once. done.
  Qed.

  Lemma auth_monoi۰lbｰget γ q a :
    auth_monoi۰auth γ q a ⊢
    auth_monoi۰lb γ a.
  Proof.
    apply own_mono, auth_monoi۰lbｰincluded'.
  Qed.
  Lemma auth_monoi۰lbｰgetｰmono' γ q a a' :
    R a' a →
    auth_monoi۰auth γ q a ⊢
    auth_monoi۰lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_monoi۰lbｰmono' // auth_monoi۰lbｰget //.
  Qed.
  Lemma auth_monoi۰lbｰgetｰmono γ q a a' :
    Rs a' a →
    auth_monoi۰auth γ q a ⊢
    auth_monoi۰lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_monoi۰lbｰmono // auth_monoi۰lbｰget //.
  Qed.

  Lemma auth_monoi۰lbｰvalid γ dq a a' :
    auth_monoi۰auth γ dq a -∗
    auth_monoi۰lb γ a' -∗
    ⌜Rs a' a⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (own_valid_2 with "Hauth Hlb") as %?%auth_monoiｰbothｰdfracｰvalid.
    naive_solver.
  Qed.
  Lemma auth_monoi۰lbｰagree γ a1 a2 :
    auth_monoi۰lb γ a1 -∗
    auth_monoi۰lb γ a2 -∗
      ∃ a,
      ⌜Rs a1 a⌝ ∧
      ⌜Rs a2 a⌝.
  Proof.
    iIntros "Hlb1 Hlb2".
    iDestruct (own_valid_2 with "Hlb1 Hlb2") as %?%auth_monoi۰lbｰopｰvalid. done.
  Qed.

  Lemma auth_monoiｰupdate {γ a} a' :
    Rs a a' →
    auth_monoi۰auth γ (DfracOwn 1) a ⊢ |==>
    auth_monoi۰auth γ (DfracOwn 1) a'.
  Proof.
    iIntros "% Hauth".
    iMod (own_update with "Hauth"); first by apply auth_monoi۰authｰupdate.
    iSteps.
  Qed.
  Lemma auth_monoiｰupdate' {γ a} a' :
    R a a' →
    auth_monoi۰auth γ (DfracOwn 1) a ⊢ |==>
    auth_monoi۰auth γ (DfracOwn 1) a'.
  Proof.
    intros. apply auth_monoiｰupdate, rtc_once. done.
  Qed.
End auth_monoi۰G.

#[global] Opaque auth_monoi۰auth.
#[global] Opaque auth_monoi۰lb.
