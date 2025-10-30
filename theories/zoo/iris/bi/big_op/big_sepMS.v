From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Section bi.
  Context {PROP : bi}.

  Section big_sepMS.
    Context `{Countable K}.

    Implicit Types s : gmultiset K.
    Implicit Types P : PROP.
    Implicit Types Φ : K → PROP.

    Lemma big_sepMS_insert_1 {Φ} x s :
      ([∗ mset] y ∈ ({[+x+]} ⊎ s), Φ y) ⊢
        Φ x ∗
        [∗ mset] y ∈ s, Φ y.
    Proof.
      rewrite big_sepMS_insert //.
    Qed.
    Lemma big_sepMS_insert_2 {Φ} x s :
      ([∗ mset] y ∈ s, Φ y) -∗
      Φ x -∗
      [∗ mset] y ∈ ({[+x+]} ⊎ s), Φ y.
    Proof.
      rewrite big_sepMS_insert. iSteps.
    Qed.

    Lemma big_sepMS_delete_1 {Φ} x s :
      x ∈ s →
      ([∗ mset] y ∈ s, Φ y) ⊢
        Φ x ∗
        [∗ mset] y ∈ (s ∖ {[+x+]}), Φ y.
    Proof.
      intros.
      rewrite big_sepMS_delete //.
    Qed.
    Lemma big_sepMS_delete_2 {Φ} x s :
      x ∈ s →
      ([∗ mset] y ∈ (s ∖ {[+x+]}), Φ y) -∗
      Φ x -∗
      [∗ mset] y ∈ s, Φ y.
    Proof.
      intros.
      setoid_rewrite big_sepMS_delete at 2; last done.
      iSteps.
    Qed.

    Lemma big_sepMS_disj_union_list {Φ} ss :
      ([∗ mset] x ∈ ⋃+ ss, Φ x) ⊣⊢
      [∗ list] s ∈ ss, [∗ mset] x ∈ s, Φ x.
    Proof.
      iInduction ss as [| s ss IH].
      - rewrite big_sepMS_empty. iSteps.
      - rewrite /= big_sepMS_disj_union.
        iSplit.
        all: iIntros "($ & H)".
        all: iApply ("IH" with "H").
    Qed.
    Lemma big_sepMS_disj_union_list_1 {Φ} ss :
      ([∗ mset] x ∈ ⋃+ ss, Φ x) ⊢
      [∗ list] s ∈ ss, [∗ mset] x ∈ s, Φ x.
    Proof.
      rewrite big_sepMS_disj_union_list //.
    Qed.
    Lemma big_sepMS_disj_union_list_2 {Φ} ss :
      ([∗ list] s ∈ ss, [∗ mset] x ∈ s, Φ x) ⊢
      [∗ mset] x ∈ ⋃+ ss, Φ x.
    Proof.
      rewrite big_sepMS_disj_union_list //.
    Qed.
  End big_sepMS.
End bi.
