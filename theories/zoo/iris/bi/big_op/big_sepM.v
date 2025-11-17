From zoo Require Import
  prelude.
From zoo.common Require Import
  fin_maps.
From zoo.iris.bi Require Import
  big_op.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Section bi.
  Context {PROP : bi}.

  Section big_sepM.
    Context `{Countable K} {A : Type}.

    Implicit Types m : gmap K A.
    Implicit Types P : PROP.
    Implicit Types Φ : K → A → PROP.

    Lemma big_sepM_impl_thread {Φ1} P Φ2 m :
      ([∗ map] k ↦ x ∈ m, Φ1 k x) -∗
      P -∗
      □ (
        ∀ k x,
        ⌜m !! k = Some x⌝ →
        Φ1 k x -∗
        P -∗
          Φ2 k x ∗
          P
      ) -∗
        ([∗ map] k ↦ x ∈ m, Φ2 k x) ∗
        P.
    Proof.
      iIntros "Hm HP #HΦ".
      iInduction m as [| k x m Hlookup] "IH" using map_ind.
      - rewrite !big_sepM_empty. iSteps.
      - iDestruct (big_sepM_insert with "Hm") as "(Hk & Hm)"; first done.
        iDestruct ("HΦ" with "[%] Hk HP") as "(Hk & HP)".
        { rewrite lookup_insert_eq //. }
        iDestruct ("IH" with "[HΦ] Hm HP") as "(Hm & $)".
        { iIntros "!> %k' %a' %Hlookup' Hk' HP".
          iApply ("HΦ" with "[%] Hk' HP").
          rewrite lookup_insert_ne //. congruence.
        }
        iApply big_sepM_insert; first done.
        iSteps.
    Qed.
    Lemma big_sepM_impl_thread_fupd `{!BiFUpd PROP} {Φ1} P Φ2 m E :
      ([∗ map] k ↦ x ∈ m, Φ1 k x) -∗
      P -∗
      □ (
        ∀ k x,
        ⌜m !! k = Some x⌝ →
        Φ1 k x -∗
        P -∗
          |={E}=>
          Φ2 k x ∗
          P
      ) -∗
        |={E}=>
        ([∗ map] k ↦ x ∈ m, Φ2 k x) ∗
        P.
    Proof.
      iIntros "Hm HP #HΦ".
      iInduction m as [| k x m Hlookup] "IH" using map_ind.
      - rewrite !big_sepM_empty. iSteps.
      - iDestruct (big_sepM_insert with "Hm") as "(Hk & Hm)"; first done.
        iMod ("HΦ" with "[%] Hk HP") as "(Hk & HP)".
        { rewrite lookup_insert_eq //. }
        iMod ("IH" with "[HΦ] Hm HP") as "(Hm & $)".
        { iIntros "!> %k' %a' %Hlookup' Hk' HP".
          iApply ("HΦ" with "[%] Hk' HP").
          rewrite lookup_insert_ne //. congruence.
        }
        iApply big_sepM_insert; first done.
        iSteps.
    Qed.

    Lemma big_sepM_delete_1 {Φ m} i x :
      m !! i = Some x →
      ([∗ map] k ↦ y ∈ m, Φ k y) ⊢
        Φ i x ∗
        [∗ map] k ↦ y ∈ delete i m, Φ k y.
    Proof.
      intros.
      rewrite big_sepM_delete //.
    Qed.
    Lemma big_sepM_delete_2 Φ m i x :
      m !! i = Some x →
      ([∗ map] k ↦ y ∈ delete i m, Φ k y) -∗
      Φ i x -∗
      [∗ map] k ↦ y ∈ m, Φ k y.
    Proof.
      iIntros "%Hlookup Hm Hx".
      iApply (big_sepM_delete with "[$Hm $Hx]"); first done.
    Qed.

    Lemma big_sepM_insert_delete_2 {Φ m i} x :
      ([∗ map] k ↦ y ∈ delete i m, Φ k y) -∗
      Φ i x -∗
      [∗ map] k ↦ y ∈ <[i := x]> m, Φ k y.
    Proof.
      rewrite big_sepM_insert_delete. iSteps.
    Qed.

    Lemma big_sepM_kmap Φ f `{!Inj (=) (=) f} m :
      ([∗ map] k ↦ x ∈ (kmap f m), Φ k x) ⊣⊢
      [∗ map] k ↦ x ∈ m, Φ (f k) x.
    Proof.
      rewrite !big_opM_map_to_list map_to_list_kmap big_sepL_fmap //.
    Qed.
  End big_sepM.

  Section big_sepM.
    Context {A : Type}.

    Implicit Types Φ : nat → A → PROP.

    Lemma big_sepM_map_seq start l Φ :
      ([∗ map] k ↦ x ∈ map_seq start l, Φ k x) ⊣⊢
      [∗ list] k ↦ x ∈ l, Φ (start + k) x.
    Proof.
      iInduction l as [| x l] "IH" forall (start).
      - rewrite big_sepM_empty. iSteps.
      - rewrite /= Nat.add_0_r.
        setoid_rewrite <- Nat.add_succ_comm.
        rewrite big_sepM_insert.
        { rewrite map_seq_cons_disjoint //. }
        iSplit.
        all: iIntros "($ & Hl)".
        all: iApply ("IH" with "Hl").
    Qed.
    Lemma big_sepM_map_seq_0 l Φ :
      ([∗ map] k ↦ x ∈ map_seq 0 l, Φ k x) ⊣⊢
      [∗ list] k ↦ x ∈ l, Φ k x.
    Proof.
      apply big_sepM_map_seq.
    Qed.
  End big_sepM.
End bi.
