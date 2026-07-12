Require Import zoo.prelude.
Require Export zoo.iris.bi.big_op.big_sepL.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

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
      iApply (big_sepL_impl_thread with "Hs HP"). iIntros "!>" (k x Hx%list_elem_of_lookup_2%elem_of_elements) "HΦ1 HP".
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
      iApply (big_sepL_impl_thread_fupd with "Hs HP"). iIntros "!>" (k x Hx%list_elem_of_lookup_2%elem_of_elements) "HΦ1 HP".
      iApply ("HΦ" with "[//] HΦ1 HP").
    Qed.

    Lemma big_sepS_exists `{!BiAffine PROP} {V} (Φ : K → V → PROP) s :
      ([∗ set] x ∈ s, ∃ v, Φ x v) ⊢
        ∃ m,
        ⌜dom m = s⌝ ∗
        [∗ map] x ↦ v ∈ m, Φ x v.
    Proof.
      rewrite big_sepS_elements big_sepL_exists.
      setoid_rewrite big_sepL2_alt.
      iIntros "(%vs & %Hvs & _ & H)".
      iDestruct (big_sepM_list_to_map with "H") as "$".
      { rewrite fst_zip. 1: lia.
        apply NoDup_elements.
      }
      iPureIntro.
      rewrite dom_list_to_map_L fst_zip. 1: lia.
      rewrite list_to_set_elements_L //.
    Qed.
  End big_sepS.
End bi.
