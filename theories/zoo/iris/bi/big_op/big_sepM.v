Require Import zoo.prelude.
Require Import zoo.common.fin_maps.
Require Import zoo.iris.bi.big_op.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Section bi.
  Context {PROP : bi}.

  Section big_sepM.
    Context `{Countable K}.
    Context {A : Type}.

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
      - iSteps.
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
      - iSteps.
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

    Lemma big_sepMｰunion₂ Φ m1 m2 :
      m1 ##ₘ m2 →
      ([∗ map] k ↦ y ∈ m1, Φ k y) -∗
      ([∗ map] k ↦ y ∈ m2, Φ k y) -∗
      [∗ map] k ↦ y ∈ m1 ∪ m2, Φ k y.
    Proof.
      intros.
      rewrite big_sepM_union //.
      iSteps.
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
      - iSteps.
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

  Section big_sepM.
    Context `{Countable K}.
    Context `{Countable A}.

    Implicit Type m : gmap K A.
    Implicit Type P : PROP.
    Implicit Type Φ : A → PROP.

    Lemma big_sepMｰmap_img `{!BiAffine PROP} Φ m :
      ([∗ map] x ∈ m, Φ x) ⊢
      [∗ set] x ∈ map_img m, Φ x.
    Proof.
      iInduction m as [| k x m Hlookup] "IH" using map_ind.
      all: iIntros "H".
      - rewrite map_img_empty_L. iSteps.
      - iDestruct (big_sepM_insert with "H") as "(HΦ & H)". 1: done.
        iEval (rewrite map_img_insert_notin_L //).
        iApply (big_sepS_insert_2 with "HΦ (IH H)").
    Qed.

    Lemma big_sepSｰmap_img `{!BiAffine PROP} {Φ} m s :
      map_img m = s →
      size m = size s →
      ([∗ set] x ∈ s, Φ x) ⊢
      [∗ map] x ∈ m, Φ x.
    Proof.
      iInduction s as [| x s Hx] "IH" using set_ind_L forall (m).
      all: iIntros (Hm Hsize) "H".
      - apply map_img_empty_inv_L in Hm as ->.
        iSteps.
      - iDestruct (big_sepS_insert with "H") as "(HΦ & H)". 1: done.
        apply map_img_union_inv_L in Hm as (m1 & m2 & -> & Hdisjoint & Hm1 & Hm2). 2: set_solver.
        rewrite map_size_disj_union // size_union in Hsize. 1: set_solver.
        rewrite size_singleton in Hsize.
        pose proof (sizeｰmap_img (SA := gset A) m1) as Hsize_1.
        rewrite Hm1 size_singleton in Hsize_1.
        pose proof (sizeｰmap_img (SA := gset A) m2) as Hsize_2.
        rewrite Hm2 in Hsize_2.
        assert (size m1 = 1) as (k & x_ & ->)%mapｰsizeｰ1ｰinv by lia.
        assert (size m2 = size s) by lia.
        rewrite map_img_singleton_L in Hm1. simp.
        iApply (big_sepMｰunion₂ with "[HΦ] [H]"). 1: done.
        { iApply (big_sepM_singleton with "HΦ"). }
        { iSteps. }
    Qed.
  End big_sepM.
End bi.
