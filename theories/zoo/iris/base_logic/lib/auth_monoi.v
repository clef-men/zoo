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
#[global] Instance subG𑁒auth_monoi۰Σ Σ {A : ofe} (R : relation A) `{!Initial R} :
  subG (auth_monoi۰Σ R) Σ →
  AuthMonoiG Σ R.
Proof.
  solve_inG.
Qed.

Section auth_monoi۰G.
  Context {A : ofe} (R : relation A) `{!Initial R}.
  Context `{auth_monoi۰G : !AuthMonoiG Σ R}.

  Implicit Types a : A.

  Notation Rs := (
    rtc R
  ).

  Definition auth_monoi۰auth γ dq a :=
    own γ (auth_monoi۰auth R dq a).
  Definition auth_monoi۰lb γ a :=
    own γ (auth_monoi۰lb R a).

  #[global] Instance auth_monoi۰auth𑁒timeless γ dq a :
    Timeless (auth_monoi۰auth γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_monoi۰lb𑁒timeless γ a :
    Timeless (auth_monoi۰lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_monoi۰auth𑁒persistent γ a :
    Persistent (auth_monoi۰auth γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_monoi۰lb𑁒persistent γ a :
    Persistent (auth_monoi۰lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_monoi۰auth𑁒fractional γ a :
    Fractional (λ q, auth_monoi۰auth γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -auth_monoi۰auth𑁒dfrac𑁒op //.
  Qed.
  #[global] Instance auth_monoi۰auth𑁒as_fractional γ q a :
    AsFractional (auth_monoi۰auth γ (DfracOwn q) a) (λ q, auth_monoi۰auth γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_monoi𑁒alloc a :
    ⊢ |==>
      ∃ γ,
      auth_monoi۰auth γ (DfracOwn 1) a.
  Proof.
    apply own_alloc, auth_monoi۰auth𑁒valid.
  Qed.

  Lemma auth_monoi۰auth𑁒valid γ dq a :
    auth_monoi۰auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%auth_monoi۰auth𑁒dfrac𑁒valid.
    iSteps.
  Qed.
  Lemma auth_monoi۰auth𑁒combine `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
      ⌜a1 = a2⌝ ∗
      auth_monoi۰auth γ (dq1 ⋅ dq2) a1.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(_ & <-)%auth_monoi۰auth𑁒dfrac𑁒op𑁒valid𑁒L.
    rewrite -auth_monoi۰auth𑁒dfrac𑁒op. iSteps.
  Qed.
  Lemma auth_monoi۰auth𑁒valid𑁒2 `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & ?)%auth_monoi۰auth𑁒dfrac𑁒op𑁒valid.
    iSteps.
  Qed.
  Lemma auth_monoi۰auth𑁒valid𑁒2𑁒L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & <-)%auth_monoi۰auth𑁒dfrac𑁒op𑁒valid𑁒L.
    iSteps.
  Qed.
  Lemma auth_monoi۰auth𑁒agree `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
    ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi۰auth𑁒valid𑁒2 with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_monoi۰auth𑁒agree𑁒L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi۰auth γ dq1 a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi۰auth𑁒valid𑁒2𑁒L with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_monoi۰auth𑁒dfrac𑁒ne `{!AntiSymm (≡) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_monoi۰auth γ1 dq1 a1 -∗
    auth_monoi۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_monoi۰auth𑁒valid𑁒2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_monoi۰auth𑁒dfrac𑁒ne𑁒L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_monoi۰auth γ1 dq1 a1 -∗
    auth_monoi۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_monoi۰auth𑁒valid𑁒2𑁒L with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_monoi۰auth𑁒ne `{!AntiSymm (≡) Rs} γ1 a1 γ2 dq2 a2 :
    auth_monoi۰auth γ1 (DfracOwn 1) a1 -∗
    auth_monoi۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_monoi۰auth𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_monoi۰auth𑁒ne𑁒L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 a1 γ2 dq2 a2 :
    auth_monoi۰auth γ1 (DfracOwn 1) a1 -∗
    auth_monoi۰auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_monoi۰auth𑁒dfrac𑁒ne𑁒L; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_monoi۰auth𑁒exclusive `{!AntiSymm (≡) Rs} γ a1 dq2 a2 :
    auth_monoi۰auth γ (DfracOwn 1) a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi۰auth𑁒ne with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_monoi۰auth𑁒exclusive𑁒L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 dq2 a2 :
    auth_monoi۰auth γ (DfracOwn 1) a1 -∗
    auth_monoi۰auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi۰auth𑁒ne𑁒L with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_monoi۰auth𑁒persist γ dq a :
    auth_monoi۰auth γ dq a ⊢ |==>
    auth_monoi۰auth γ DfracDiscarded a.
  Proof.
    apply own_update, auth_monoi۰auth𑁒persist.
  Qed.

  Lemma auth_monoi۰lb𑁒initial γ :
    ⊢ |==>
      auth_monoi۰lb γ initial.
  Proof.
    apply own_unit.
  Qed.
  Lemma auth_monoi۰lb𑁒mono {γ a} a' :
    Rs a' a →
    auth_monoi۰lb γ a ⊢
    auth_monoi۰lb γ a'.
  Proof.
    intros. apply own_mono, auth_monoi۰lb𑁒mono. done.
  Qed.
  Lemma auth_monoi۰lb𑁒mono' {γ a} a' :
    R a' a →
    auth_monoi۰lb γ a ⊢
    auth_monoi۰lb γ a'.
  Proof.
    intros. apply auth_monoi۰lb𑁒mono, rtc_once. done.
  Qed.

  Lemma auth_monoi۰lb𑁒get γ q a :
    auth_monoi۰auth γ q a ⊢
    auth_monoi۰lb γ a.
  Proof.
    apply own_mono, auth_monoi۰lb𑁒included'.
  Qed.
  Lemma auth_monoi۰lb𑁒get𑁒mono' γ q a a' :
    R a' a →
    auth_monoi۰auth γ q a ⊢
    auth_monoi۰lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_monoi۰lb𑁒mono' // auth_monoi۰lb𑁒get //.
  Qed.
  Lemma auth_monoi۰lb𑁒get𑁒mono γ q a a' :
    Rs a' a →
    auth_monoi۰auth γ q a ⊢
    auth_monoi۰lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_monoi۰lb𑁒mono // auth_monoi۰lb𑁒get //.
  Qed.

  Lemma auth_monoi۰lb𑁒valid γ dq a a' :
    auth_monoi۰auth γ dq a -∗
    auth_monoi۰lb γ a' -∗
    ⌜Rs a' a⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (own_valid_2 with "Hauth Hlb") as %?%auth_monoi𑁒both𑁒dfrac𑁒valid.
    naive_solver.
  Qed.
  Lemma auth_monoi۰lb𑁒agree γ a1 a2 :
    auth_monoi۰lb γ a1 -∗
    auth_monoi۰lb γ a2 -∗
      ∃ a,
      ⌜Rs a1 a⌝ ∧
      ⌜Rs a2 a⌝.
  Proof.
    iIntros "Hlb1 Hlb2".
    iDestruct (own_valid_2 with "Hlb1 Hlb2") as %?%auth_monoi۰lb𑁒op𑁒valid. done.
  Qed.

  Lemma auth_monoi𑁒update {γ a} a' :
    Rs a a' →
    auth_monoi۰auth γ (DfracOwn 1) a ⊢ |==>
    auth_monoi۰auth γ (DfracOwn 1) a'.
  Proof.
    iIntros "% Hauth".
    iMod (own_update with "Hauth"); first by apply auth_monoi۰auth𑁒update.
    iSteps.
  Qed.
  Lemma auth_monoi𑁒update' {γ a} a' :
    R a a' →
    auth_monoi۰auth γ (DfracOwn 1) a ⊢ |==>
    auth_monoi۰auth γ (DfracOwn 1) a'.
  Proof.
    intros. apply auth_monoi𑁒update, rtc_once. done.
  Qed.
End auth_monoi۰G.

#[global] Opaque auth_monoi۰auth.
#[global] Opaque auth_monoi۰lb.
