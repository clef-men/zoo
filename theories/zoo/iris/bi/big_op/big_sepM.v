Require Import zoo.prelude.
Require Import zoo.common.fin_maps.
Require Import zoo.iris.bi.big_op.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Section bi.
  Context {PROP : bi}.

  Section big_sepM.
    Context `{Countable K} {A : Type}.

    Implicit Type m : gmap K A.
    Implicit Type P : PROP.
    Implicit Type Φ : K → A → PROP.

    Lemma big_sepMｰsingleton₁ Φ k v :
      ([∗ map] k ↦ v ∈ {[k := v]}, Φ k v) ⊢
      Φ k v.
    Proof.
      rewrite big_sepM_singleton //.
    Qed.
    Lemma big_sepMｰsingleton₂ Φ k v :
      Φ k v ⊢
      [∗ map] k ↦ v ∈ {[k := v]}, Φ k v.
    Proof.
      rewrite big_sepM_singleton //.
    Qed.

    Lemma big_sepMｰimplｰthread {Φ1} P Φ2 m :
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
    Lemma big_sepMｰimplｰthreadｰfupd `{!BiFUpd PROP} {Φ1} P Φ2 m E :
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

    Lemma big_sepMｰdelete₁ {Φ m} i x :
      m !! i = Some x →
      ([∗ map] k ↦ y ∈ m, Φ k y) ⊢
        Φ i x ∗
        [∗ map] k ↦ y ∈ delete i m, Φ k y.
    Proof.
      intros.
      rewrite big_sepM_delete //.
    Qed.
    Lemma big_sepMｰdelete₂ Φ m i x :
      m !! i = Some x →
      ([∗ map] k ↦ y ∈ delete i m, Φ k y) -∗
      Φ i x -∗
      [∗ map] k ↦ y ∈ m, Φ k y.
    Proof.
      iIntros "%Hlookup Hm Hx".
      iApply (big_sepM_delete with "[$Hm $Hx]"); first done.
    Qed.

    Lemma big_sepMｰinsertｰdelete₂ {Φ m i} x :
      ([∗ map] k ↦ y ∈ delete i m, Φ k y) -∗
      Φ i x -∗
      [∗ map] k ↦ y ∈ <[i := x]> m, Φ k y.
    Proof.
      rewrite big_sepM_insert_delete. iSteps.
    Qed.

    Lemma big_sepMｰkmap Φ f `{!Inj (=) (=) f} m :
      ([∗ map] k ↦ x ∈ (kmap f m), Φ k x) ⊣⊢
      [∗ map] k ↦ x ∈ m, Φ (f k) x.
    Proof.
      rewrite !big_opM_map_to_list map_to_list_kmap big_sepL_fmap //.
    Qed.
  End big_sepM.

  Section big_sepM.
    Context {A : Type}.

    Implicit Type Φ : nat → A → PROP.

    Lemma big_sepMｰmap_seq start l Φ :
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
    Lemma big_sepMｰmap_seqｰ0 l Φ :
      ([∗ map] k ↦ x ∈ map_seq 0 l, Φ k x) ⊣⊢
      [∗ list] k ↦ x ∈ l, Φ k x.
    Proof.
      apply big_sepMｰmap_seq.
    Qed.
  End big_sepM.
End bi.
