From zoo Require Import
  prelude.
From zoo.iris.bi Require Export
  big_op.big_sepL.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Section bi.
  Context {PROP : bi}.

  Section big_sepS.
    Context `{Countable K}.

    Implicit Types s : gset K.
    Implicit Types P : PROP.
    Implicit Types Φ : K → PROP.

    Lemma big_sepS_impl_thread {Φ1} P Φ2 s :
      ([∗ set] x ∈ s, Φ1 x) -∗
      P -∗
      □ (
        ∀ x,
        ⌜x ∈ s⌝ →
        Φ1 x -∗
        P -∗
          Φ2 x ∗
          P
      ) -∗
        ([∗ set] x ∈ s, Φ2 x) ∗
        P.
    Proof.
      rewrite !big_sepS_elements.
      iIntros "Hs HP #HΦ".
      iApply (big_sepL_impl_thread with "Hs HP"). iIntros "!>" (k x Hx%elem_of_list_lookup_2%elem_of_elements) "HΦ1 HP".
      iApply ("HΦ" with "[//] HΦ1 HP").
    Qed.
    Lemma big_sepS_impl_thread_fupd `{!BiFUpd PROP} {Φ1} P Φ2 s E :
      ([∗ set] x ∈ s, Φ1 x) -∗
      P -∗
      □ (
        ∀ x,
        ⌜x ∈ s⌝ →
        Φ1 x -∗
        P -∗
          |={E}=>
          Φ2 x ∗
          P
      ) -∗
        |={E}=>
        ([∗ set] x ∈ s, Φ2 x) ∗
        P.
    Proof.
      rewrite !big_sepS_elements.
      iIntros "Hs HP #HΦ".
      iApply (big_sepL_impl_thread_fupd with "Hs HP"). iIntros "!>" (k x Hx%elem_of_list_lookup_2%elem_of_elements) "HΦ1 HP".
      iApply ("HΦ" with "[//] HΦ1 HP").
    Qed.
  End big_sepS.
End bi.
