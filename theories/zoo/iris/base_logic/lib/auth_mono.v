Require Import zoo.prelude.
Require Import zoo.iris.algebra.lib.auth_mono.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthMonoG Σ {A : ofe} (R : relation A) :=
  { #[local] auth_mono_G_inG :: inG Σ (auth_mono_UR R)
  }.

Definition auth_mono_Σ {A : ofe} (R : relation A) :=
  #[GFunctor (auth_mono_UR R)
  ].
#[global] Instance subG_auth_mono_Σ Σ {A : ofe} (R : relation A) :
  subG (auth_mono_Σ R) Σ →
  AuthMonoG Σ R.
Proof.
  solve_inG.
Qed.

Section auth_mono_G.
  Context {A : ofe} (R : relation A).
  Context `{auth_mono_G : !AuthMonoG Σ R}.

  Implicit Types a : A.

  Notation Rs := (
    rtc R
  ).

  Definition auth_mono_auth γ dq a :=
    own γ (auth_mono_auth R dq a).
  Definition auth_mono_lb γ a :=
    own γ (auth_mono_lb R a).

  #[global] Instance auth_mono_auth_timeless γ dq a :
    Timeless (auth_mono_auth γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono_lb_timeless γ a :
    Timeless (auth_mono_lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_mono_auth_persistent γ a :
    Persistent (auth_mono_auth γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono_lb_persistent γ a :
    Persistent (auth_mono_lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_mono_auth_fractional γ a :
    Fractional (λ q, auth_mono_auth γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -auth_mono_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_mono_auth_as_fractional γ q a :
    AsFractional (auth_mono_auth γ (DfracOwn q) a) (λ q, auth_mono_auth γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_mono_alloc a :
    ⊢ |==>
      ∃ γ,
      auth_mono_auth γ (DfracOwn 1) a.
  Proof.
    apply own_alloc, auth_mono_auth_valid.
  Qed.

  Lemma auth_mono_auth_valid γ dq a :
    auth_mono_auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%auth_mono_auth_dfrac_valid.
    iSteps.
  Qed.
  Lemma auth_mono_auth_combine `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_mono_auth γ dq1 a1 -∗
    auth_mono_auth γ dq2 a2 -∗
      ⌜a1 = a2⌝ ∗
      auth_mono_auth γ (dq1 ⋅ dq2) a1.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(_ & <-)%auth_mono_auth_dfrac_op_valid_L.
    rewrite -auth_mono_auth_dfrac_op. iSteps.
  Qed.
  Lemma auth_mono_auth_valid_2 `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_mono_auth γ dq1 a1 -∗
    auth_mono_auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & ?)%auth_mono_auth_dfrac_op_valid.
    iSteps.
  Qed.
  Lemma auth_mono_auth_valid_2_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_mono_auth γ dq1 a1 -∗
    auth_mono_auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & <-)%auth_mono_auth_dfrac_op_valid_L.
    iSteps.
  Qed.
  Lemma auth_mono_auth_agree `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_mono_auth γ dq1 a1 -∗
    auth_mono_auth γ dq2 a2 -∗
    ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono_auth_valid_2 with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_mono_auth_agree_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_mono_auth γ dq1 a1 -∗
    auth_mono_auth γ dq2 a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono_auth_valid_2_L with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_mono_auth_dfrac_ne `{!AntiSymm (≡) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_mono_auth γ1 dq1 a1 -∗
    auth_mono_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_mono_auth_valid_2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_mono_auth_dfrac_ne_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_mono_auth γ1 dq1 a1 -∗
    auth_mono_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_mono_auth_valid_2_L with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_mono_auth_ne `{!AntiSymm (≡) Rs} γ1 a1 γ2 dq2 a2 :
    auth_mono_auth γ1 (DfracOwn 1) a1 -∗
    auth_mono_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_mono_auth_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_mono_auth_ne_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 a1 γ2 dq2 a2 :
    auth_mono_auth γ1 (DfracOwn 1) a1 -∗
    auth_mono_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_mono_auth_dfrac_ne_L; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_mono_auth_exclusive `{!AntiSymm (≡) Rs} γ a1 dq2 a2 :
    auth_mono_auth γ (DfracOwn 1) a1 -∗
    auth_mono_auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono_auth_ne with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_mono_auth_exclusive_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 dq2 a2 :
    auth_mono_auth γ (DfracOwn 1) a1 -∗
    auth_mono_auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono_auth_ne_L with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_mono_auth_persist γ dq a :
    auth_mono_auth γ dq a ⊢ |==>
    auth_mono_auth γ DfracDiscarded a.
  Proof.
    apply own_update, auth_mono_auth_persist.
  Qed.

  Lemma auth_mono_lb_mono {γ a} a' :
    Rs a' a →
    auth_mono_lb γ a ⊢
    auth_mono_lb γ a'.
  Proof.
    intros. apply own_mono, auth_mono_lb_mono. done.
  Qed.
  Lemma auth_mono_lb_mono' {γ a} a' :
    R a' a →
    auth_mono_lb γ a ⊢
    auth_mono_lb γ a'.
  Proof.
    intros. apply auth_mono_lb_mono, rtc_once. done.
  Qed.

  Lemma auth_mono_lb_get γ q a :
    auth_mono_auth γ q a ⊢
    auth_mono_lb γ a.
  Proof.
    apply own_mono, auth_mono_lb_included'.
  Qed.
  Lemma auth_mono_lb_get_mono' γ q a a' :
    R a' a →
    auth_mono_auth γ q a ⊢
    auth_mono_lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_mono_lb_mono' // auth_mono_lb_get //.
  Qed.
  Lemma auth_mono_lb_get_mono γ q a a' :
    Rs a' a →
    auth_mono_auth γ q a ⊢
    auth_mono_lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_mono_lb_mono // auth_mono_lb_get //.
  Qed.

  Lemma auth_mono_lb_valid γ dq a a' :
    auth_mono_auth γ dq a -∗
    auth_mono_lb γ a' -∗
    ⌜Rs a' a⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (own_valid_2 with "Hauth Hlb") as %?%auth_mono_both_dfrac_valid.
    naive_solver.
  Qed.
  Lemma auth_mono_lb_agree γ a1 a2 :
    auth_mono_lb γ a1 -∗
    auth_mono_lb γ a2 -∗
      ∃ a,
      ⌜Rs a1 a⌝ ∧
      ⌜Rs a2 a⌝.
  Proof.
    iIntros "Hlb1 Hlb2".
    iDestruct (own_valid_2 with "Hlb1 Hlb2") as %?%auth_mono_lb_op_valid. done.
  Qed.

  Lemma auth_mono_update {γ a} a' :
    Rs a a' →
    auth_mono_auth γ (DfracOwn 1) a ⊢ |==>
    auth_mono_auth γ (DfracOwn 1) a'.
  Proof.
    iIntros "% Hauth".
    iMod (own_update with "Hauth"); first by apply auth_mono_auth_update.
    iSteps.
  Qed.
  Lemma auth_mono_update' {γ a} a' :
    R a a' →
    auth_mono_auth γ (DfracOwn 1) a ⊢ |==>
    auth_mono_auth γ (DfracOwn 1) a'.
  Proof.
    intros. apply auth_mono_update, rtc_once. done.
  Qed.
End auth_mono_G.

#[global] Opaque auth_mono_auth.
#[global] Opaque auth_mono_lb.
