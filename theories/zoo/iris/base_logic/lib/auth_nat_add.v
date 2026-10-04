Require Import zoo.prelude.
Require Import zoo.iris.algebra.lib.auth_nat_add.
Require Export zoo.iris.bi.big_op.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Implicit Type n m : nat.

Class AuthNatAddG Σ :=
  { #[local] auth_nat_add۰G :: inG Σ auth_nat_add۰UR
  }.

Definition auth_nat_add۰Σ :=
  #[GFunctor auth_nat_add۰UR
  ].
#[global] Instance subGｰauth_nat_add۰Σ Σ :
  subG auth_nat_add۰Σ Σ →
  AuthNatAddG Σ.
Proof.
  solve_inG.
Qed.

Section auth_nat_add_G.
  Context `{auth_nat_add_G : AuthNatAddG Σ}.

  Please Definition auth_nat_add۰auth γ dq n :=
    own γ (auth_nat_add۰auth dq n).
  Please Definition auth_nat_add۰frag γ m :=
    own γ (auth_nat_add۰frag m).

  #[global] Instance auth_nat_add۰authｰtimeless γ dq n :
    Timeless (auth_nat_add۰auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_add۰fragｰtimeless γ m :
    Timeless (auth_nat_add۰frag γ m).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_add۰authｰpersistent γ n :
    Persistent (auth_nat_add۰auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_add۰fragｰpersistent γ :
    Persistent (auth_nat_add۰frag γ 0).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_add۰authｰfractional γ n :
    Fractional (λ q, auth_nat_add۰auth γ (DfracOwn q) n).
  Proof.
    intros ?*.
    rewrite -own_op -auth_nat_add۰authｰdfracｰop //.
  Qed.
  #[global] Instance auth_nat_add۰authｰas_fractional γ q n :
    AsFractional (auth_nat_add۰auth γ (DfracOwn q) n) (λ q, auth_nat_add۰auth γ (DfracOwn q) n) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_nat_addｰalloc n :
    ⊢ |==>
      ∃ γ,
      auth_nat_add۰auth γ (DfracOwn 1) n ∗
      auth_nat_add۰frag γ n.
  Proof.
    iMod (own_alloc (auth_nat_add.auth_nat_add۰auth (DfracOwn 1) n ⋅ auth_nat_add.auth_nat_add۰frag n)) as "(%γ & $ & $)" => //.
    { rewrite auth_nat_addｰbothｰvalid //. }
  Qed.

  Lemma auth_nat_add۰authｰvalid γ dq n :
    auth_nat_add۰auth γ dq n ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%auth_nat_add۰authｰdfracｰvalid.
    iSteps.
  Qed.
  Lemma auth_nat_add۰authｰcombine γ dq1 n1 dq2 n2 :
    auth_nat_add۰auth γ dq1 n1 -∗
    auth_nat_add۰auth γ dq2 n2 -∗
      ⌜n1 = n2⌝ ∗
      auth_nat_add۰auth γ (dq1 ⋅ dq2) n1.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(_ & <-)%auth_nat_add۰authｰdfracｰopｰvalid.
    rewrite -auth_nat_add۰authｰdfracｰop. iSteps.
  Qed.
  Lemma auth_nat_add۰authｰvalidｰ2 γ dq1 n1 dq2 n2 :
    auth_nat_add۰auth γ dq1 n1 -∗
    auth_nat_add۰auth γ dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜n1 = n2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & <-)%auth_nat_add۰authｰdfracｰopｰvalid.
    iSteps.
  Qed.
  Lemma auth_nat_add۰authｰagree γ dq1 n1 dq2 n2 :
    auth_nat_add۰auth γ dq1 n1 -∗
    auth_nat_add۰auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_nat_add۰authｰvalidｰ2 with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_nat_add۰authｰdfracｰne γ1 dq1 n1 γ2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_nat_add۰auth γ1 dq1 n1 -∗
    auth_nat_add۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_nat_add۰authｰvalidｰ2 with "Hauth1 Hauth2") as %(? & _) => //.
  Qed.
  Lemma auth_nat_add۰authｰne γ1 n1 γ2 dq2 n2 :
    auth_nat_add۰auth γ1 (DfracOwn 1) n1 -∗
    auth_nat_add۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_nat_add۰authｰdfracｰne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_nat_add۰authｰexclusive γ n1 dq2 n2 :
    auth_nat_add۰auth γ (DfracOwn 1) n1 -∗
    auth_nat_add۰auth γ dq2 n2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_nat_add۰authｰne with "Hauth1 Hauth2") as %? => //.
  Qed.
  Lemma auth_nat_add۰authｰpersist γ dq n :
    auth_nat_add۰auth γ dq n ⊢ |==>
    auth_nat_add۰auth γ DfracDiscarded n.
  Proof.
    apply own_update, auth_nat_add۰authｰpersist.
  Qed.

  Lemma auth_nat_add۰fragｰ0 γ :
    ⊢ |==>
      auth_nat_add۰frag γ 0.
  Proof.
    apply own_unit.
  Qed.
  Lemma auth_nat_add۰fragｰadd γ m1 m2 :
    auth_nat_add۰frag γ (m1 + m2) ⊣⊢
      auth_nat_add۰frag γ m1 ∗
      auth_nat_add۰frag γ m2.
  Proof.
    rewrite /auth_nat_add۰frag auth_nat_add۰fragｰop own_op //.
  Qed.
  Lemma auth_nat_add۰fragｰcombine γ m1 m2 :
    auth_nat_add۰frag γ m1 -∗
    auth_nat_add۰frag γ m2 -∗
    auth_nat_add۰frag γ (m1 + m2).
  Proof.
    rewrite auth_nat_add۰fragｰadd. iSteps.
  Qed.
  Lemma auth_nat_add۰fragｰsplit γ m1 m2 :
    auth_nat_add۰frag γ (m1 + m2) ⊢
      auth_nat_add۰frag γ m1 ∗
      auth_nat_add۰frag γ m2.
  Proof.
    rewrite auth_nat_add۰fragｰadd. iSteps.
  Qed.
  Lemma auth_nat_add۰fragｰsucc γ m :
    auth_nat_add۰frag γ ˖m ⊣⊢
      auth_nat_add۰frag γ 1 ∗
      auth_nat_add۰frag γ m.
  Proof.
    rewrite -auth_nat_add۰fragｰadd Nat.add_1_l //.
  Qed.
  Lemma auth_nat_add۰fragｰatomize γ m :
    auth_nat_add۰frag γ m ⊢
    [∗ list] _ ∈ seq 0 m, auth_nat_add۰frag γ 1.
  Proof.
    iInduction m as [| m] "IH".
    - iSteps.
    - iEval (rewrite auth_nat_add۰fragｰsucc big_sepLｰseqｰsnoc).
      iSteps.
  Qed.
  Lemma auth_nat_add۰fragｰmono {γ m1} m2 :
    m2 ≤ m1 →
    auth_nat_add۰frag γ m1 ⊢
    auth_nat_add۰frag γ m2.
  Proof.
    intros.
    apply own_mono, auth_nat_add۰fragｰmono => //.
  Qed.

  Lemma auth_nat_add۰fragｰvalid γ dq n m :
    auth_nat_add۰auth γ dq n -∗
    auth_nat_add۰frag γ m -∗
    ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %?%auth_nat_addｰbothｰdfracｰvalid.
    iSteps.
  Qed.

  Lemma auth_nat_addｰupdateｰincrease {γ n1} n2 :
    auth_nat_add۰auth γ (DfracOwn 1) n1 ⊢ |==>
      auth_nat_add۰auth γ (DfracOwn 1) (n1 + n2) ∗
      auth_nat_add۰frag γ n2.
  Proof.
    rewrite -own_op.
    apply own_update, auth_nat_addｰupdateｰincrease.
  Qed.
  Lemma auth_nat_addｰupdateｰincr γ n :
    auth_nat_add۰auth γ (DfracOwn 1) n ⊢ |==>
      auth_nat_add۰auth γ (DfracOwn 1) ˖n ∗
      auth_nat_add۰frag γ 1.
  Proof.
    rewrite -Nat.add_1_r.
    apply auth_nat_addｰupdateｰincrease.
  Qed.
  Lemma auth_nat_addｰupdateｰdecrease {γ n} m :
    auth_nat_add۰auth γ (DfracOwn 1) n -∗
    auth_nat_add۰frag γ m ==∗
    auth_nat_add۰auth γ (DfracOwn 1) (n - m).
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (auth_nat_add۰fragｰvalid with "Hauth Hfrag") as %?.
    iApply (own_update_2 with "Hauth Hfrag").
    { apply auth_nat_addｰupdateｰdecrease => //. }
  Qed.
End auth_nat_add_G.

Please opacify.

Section auth_nat_add_G.
  Context `{auth_nat_add_G : AuthNatAddG Σ}.

  #[global] Instance from_sepｰauth_nat_add۰fragｰadd γ m1 m2 :
    FromSep
      (auth_nat_add۰frag γ (m1 + m2))
      (auth_nat_add۰frag γ m1)
      (auth_nat_add۰frag γ m2)
  | 0.
  Proof.
    rewrite /FromSep auth_nat_add۰fragｰadd //.
  Qed.
  #[global] Instance from_sepｰauth_nat_add۰fragｰsucc γ m :
    FromSep
      (auth_nat_add۰frag γ ˖m)
      (auth_nat_add۰frag γ 1)
      (auth_nat_add۰frag γ m)
  | 1.
  Proof.
    rewrite /FromSep -auth_nat_add۰fragｰsucc //.
  Qed.

  #[global] Instance combine_sepｰauth_nat_add۰fragｰadd γ m1 m2 :
    CombineSepAs
      (auth_nat_add۰frag γ m1)
      (auth_nat_add۰frag γ m2)
      (auth_nat_add۰frag γ (m1 + m2))
  | 1.
  Proof.
    rewrite /CombineSepAs auth_nat_add۰fragｰadd //.
  Qed.
  #[global] Instance combine_sepｰauth_nat_add۰fragｰsucc γ m :
    CombineSepAs
      (auth_nat_add۰frag γ 1)
      (auth_nat_add۰frag γ m)
      (auth_nat_add۰frag γ ˖m)
  | 0.
  Proof.
    rewrite /CombineSepAs -auth_nat_add۰fragｰsucc //.
  Qed.

  #[global] Instance into_sepｰauth_nat_add۰fragｰadd γ m1 m2 :
    IntoSep
      (auth_nat_add۰frag γ (m1 + m2))
      (auth_nat_add۰frag γ m1)
      (auth_nat_add۰frag γ m2)
  | 0.
  Proof.
    rewrite /IntoSep auth_nat_add۰fragｰadd //.
  Qed.
  #[global] Instance into_sepｰauth_nat_add۰fragｰsucc γ m :
    IntoSep
      (auth_nat_add۰frag γ ˖m)
      (auth_nat_add۰frag γ 1)
      (auth_nat_add۰frag γ m)
  | 1.
  Proof.
    rewrite /IntoSep auth_nat_add۰fragｰsucc //.
  Qed.
End auth_nat_add_G.
