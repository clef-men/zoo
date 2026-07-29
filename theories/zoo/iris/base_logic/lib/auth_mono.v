Require Import zoo.prelude.
Require Import zoo.iris.algebra.lib.auth_mono.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthMonoG Σ {A : ofe} (R : relation A) :=
  { #[local] auth_mono۰G۰inG :: inG Σ (auth_mono۰UR R)
  }.

Definition auth_mono۰Σ {A : ofe} (R : relation A) :=
  #[GFunctor (auth_mono۰UR R)
  ].
#[global] Instance subGｰauth_mono۰Σ Σ {A : ofe} (R : relation A) :
  subG (auth_mono۰Σ R) Σ →
  AuthMonoG Σ R.
Proof.
  solve_inG.
Qed.

Section auth_mono۰G.
  Context {A : ofe} (R : relation A).
  Context `{auth_mono۰G : !AuthMonoG Σ R}.

  Implicit Type a : A.

  Notation Rs := (
    rtc R
  ).

  Definition auth_mono۰auth γ dq a :=
    own γ (auth_mono۰auth R dq a).
  Definition auth_mono۰lb γ a :=
    own γ (auth_mono۰lb R a).

  #[global] Instance auth_mono۰authｰtimeless γ dq a :
    Timeless (auth_mono۰auth γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono۰lbｰtimeless γ a :
    Timeless (auth_mono۰lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_mono۰authｰpersistent γ a :
    Persistent (auth_mono۰auth γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono۰lbｰpersistent γ a :
    Persistent (auth_mono۰lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_mono۰authｰfractional γ a :
    Fractional (λ q, auth_mono۰auth γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -auth_mono۰authｰdfracｰop //.
  Qed.
  #[global] Instance auth_mono۰authｰas_fractional γ q a :
    AsFractional (auth_mono۰auth γ (DfracOwn q) a) (λ q, auth_mono۰auth γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_monoｰalloc a :
    ⊢ |==>
      ∃ γ,
      auth_mono۰auth γ (DfracOwn 1) a.
  Proof.
    apply own_alloc, auth_mono۰authｰvalid.
  Qed.

  Lemma auth_mono۰authｰvalid γ dq a :
    auth_mono۰auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%auth_mono۰authｰdfracｰvalid.
    iSteps.
  Qed.
  Lemma auth_mono۰authｰcombine `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_mono۰auth γ dq1 a1 -∗
    auth_mono۰auth γ dq2 a2 -∗
      ⌜a1 = a2⌝ ∗
      auth_mono۰auth γ (dq1 ⋅ dq2) a1.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(_ & <-)%auth_mono۰authｰdfracｰopｰvalidｰL.
    rewrite -auth_mono۰authｰdfracｰop. iSteps.
  Qed.
  Lemma auth_mono۰authｰvalidｰ2 `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_mono۰auth γ dq1 a1 -∗
    auth_mono۰auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & ?)%auth_mono۰authｰdfracｰopｰvalid.
    iSteps.
  Qed.
  Lemma auth_mono۰authｰvalidｰ2ｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_mono۰auth γ dq1 a1 -∗
    auth_mono۰auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & <-)%auth_mono۰authｰdfracｰopｰvalidｰL.
    iSteps.
  Qed.
  Lemma auth_mono۰authｰagree `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_mono۰auth γ dq1 a1 -∗
    auth_mono۰auth γ dq2 a2 -∗
    ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono۰authｰvalidｰ2 with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_mono۰authｰagreeｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_mono۰auth γ dq1 a1 -∗
    auth_mono۰auth γ dq2 a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono۰authｰvalidｰ2ｰL with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_mono۰authｰdfracｰne `{!AntiSymm (≡) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_mono۰auth γ1 dq1 a1 -∗
    auth_mono۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_mono۰authｰvalidｰ2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_mono۰authｰdfracｰneｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_mono۰auth γ1 dq1 a1 -∗
    auth_mono۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_mono۰authｰvalidｰ2ｰL with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_mono۰authｰne `{!AntiSymm (≡) Rs} γ1 a1 γ2 dq2 a2 :
    auth_mono۰auth γ1 (DfracOwn 1) a1 -∗
    auth_mono۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_mono۰authｰdfracｰne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_mono۰authｰneｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 a1 γ2 dq2 a2 :
    auth_mono۰auth γ1 (DfracOwn 1) a1 -∗
    auth_mono۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_mono۰authｰdfracｰneｰL; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_mono۰authｰexclusive `{!AntiSymm (≡) Rs} γ a1 dq2 a2 :
    auth_mono۰auth γ (DfracOwn 1) a1 -∗
    auth_mono۰auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono۰authｰne with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_mono۰authｰexclusiveｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 dq2 a2 :
    auth_mono۰auth γ (DfracOwn 1) a1 -∗
    auth_mono۰auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono۰authｰneｰL with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_mono۰authｰpersist γ dq a :
    auth_mono۰auth γ dq a ⊢ |==>
    auth_mono۰auth γ DfracDiscarded a.
  Proof.
    apply own_update, auth_mono۰authｰpersist.
  Qed.

  Lemma auth_mono۰lbｰmono {γ a} a' :
    Rs a' a →
    auth_mono۰lb γ a ⊢
    auth_mono۰lb γ a'.
  Proof.
    intros. apply own_mono, auth_mono۰lbｰmono. done.
  Qed.
  Lemma auth_mono۰lbｰmono' {γ a} a' :
    R a' a →
    auth_mono۰lb γ a ⊢
    auth_mono۰lb γ a'.
  Proof.
    intros. apply auth_mono۰lbｰmono, rtc_once. done.
  Qed.

  Lemma auth_mono۰lbｰget γ q a :
    auth_mono۰auth γ q a ⊢
    auth_mono۰lb γ a.
  Proof.
    apply own_mono, auth_mono۰lbｰincluded'.
  Qed.
  Lemma auth_mono۰lbｰgetｰmono' γ q a a' :
    R a' a →
    auth_mono۰auth γ q a ⊢
    auth_mono۰lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_mono۰lbｰmono' // auth_mono۰lbｰget //.
  Qed.
  Lemma auth_mono۰lbｰgetｰmono γ q a a' :
    Rs a' a →
    auth_mono۰auth γ q a ⊢
    auth_mono۰lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_mono۰lbｰmono // auth_mono۰lbｰget //.
  Qed.

  Lemma auth_mono۰lbｰvalid γ dq a a' :
    auth_mono۰auth γ dq a -∗
    auth_mono۰lb γ a' -∗
    ⌜Rs a' a⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (own_valid_2 with "Hauth Hlb") as %?%auth_monoｰbothｰdfracｰvalid.
    naive_solver.
  Qed.
  Lemma auth_mono۰lbｰagree γ a1 a2 :
    auth_mono۰lb γ a1 -∗
    auth_mono۰lb γ a2 -∗
      ∃ a,
      ⌜Rs a1 a⌝ ∧
      ⌜Rs a2 a⌝.
  Proof.
    iIntros "Hlb1 Hlb2".
    iDestruct (own_valid_2 with "Hlb1 Hlb2") as %?%auth_mono۰lbｰopｰvalid. done.
  Qed.

  Lemma auth_monoｰupdate {γ a} a' :
    Rs a a' →
    auth_mono۰auth γ (DfracOwn 1) a ⊢ |==>
    auth_mono۰auth γ (DfracOwn 1) a'.
  Proof.
    iIntros "% Hauth".
    iMod (own_update with "Hauth"); first by apply auth_mono۰authｰupdate.
    iSteps.
  Qed.
  Lemma auth_monoｰupdate' {γ a} a' :
    R a a' →
    auth_mono۰auth γ (DfracOwn 1) a ⊢ |==>
    auth_mono۰auth γ (DfracOwn 1) a'.
  Proof.
    intros. apply auth_monoｰupdate, rtc_once. done.
  Qed.
End auth_mono۰G.

#[global] Opaque auth_mono۰auth.
#[global] Opaque auth_mono۰lb.
