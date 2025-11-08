From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Export
  big_op.big_sepL.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Section bi.
  Context {PROP : bi}.

  Section big_sepL_seqZ.
    Context {A : Type}.

    Implicit Types l : list A.
    Implicit Types Φ : Z → PROP.

    Lemma big_sepL_seqZ_intro Φ i n :
      □ (
        ∀ k,
        ⌜i ≤ k < i + n⌝%Z -∗
        Φ k
      ) ⊢
      [∗ list] k ∈ seqZ i n, Φ k.
    Proof.
      iIntros "#H".
      iApply big_sepL_intro. iIntros "!>" (k k_ (-> & Hk)%lookup_seqZ).
      iSteps.
    Qed.

    Lemma big_sepL_seqZ_to_seq `{!BiAffine PROP} Φ i n :
      (0 ≤ i)%Z →
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ k) ⊢
      [∗ list] k ∈ seq ₊i ₊n, Φ ⁺k.
    Proof.
      iIntros "%Hi %Hn H".
      iApply (big_sepL_impl_strong with "H").
      { simpl_length. }
      iIntros "!>" (k k1 k2 (-> & _)%lookup_seqZ (-> & _)%lookup_seq) "HΦ".
      replace ⁺(₊i + k) with (i + k)%Z by lia. done.
    Qed.
    Lemma big_sepL_seqZ_to_seq' `{!BiAffine PROP} (Φ : nat → PROP) i n :
      (0 ≤ i)%Z →
      (0 ≤ n)%Z →
      ([∗ list] k ∈ seqZ i n, Φ ₊k) ⊢
      [∗ list] k ∈ seq ₊i ₊n, Φ k.
    Proof.
      intros.
      rewrite big_sepL_seqZ_to_seq //.
      setoid_rewrite Nat2Z.id => //.
    Qed.
  End big_sepL_seqZ.
End bi.
