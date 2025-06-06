From zoo Require Import
  prelude.
From zoo.common Require Import
  relations.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris.base_logic Require Import
  lib.auth_mono.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class MonoGmapG Σ K V `{Countable K} := {
  #[local] mono_gmap_G_mono_G :: AuthMonoG Σ (A := leibnizO (gmap K V)) (subseteq (A := gmap K V)) ;
}.

Definition mono_gmap_Σ K V `{Countable K} := #[
  auth_mono_Σ (A := leibnizO (gmap K V)) (subseteq (A := gmap K V))
].
#[global] Instance subG_mono_gmap_Σ Σ K V `{Countable K} :
  subG (mono_gmap_Σ K V) Σ →
  MonoGmapG Σ K V.
Proof.
  solve_inG.
Qed.

Section mono_gmap_G.
  Context `{mono_gmap_G : MonoGmapG Σ K V}.

  Implicit Types v : V.
  Implicit Types m : gmap K V.

  #[local] Instance map_subseteq_partialorder :
    PartialOrder (A := gmap K V) subseteq.
  Proof.
    apply _.
  Qed.

  Definition mono_gmap_auth γ dq m :=
    auth_mono_auth subseteq γ dq m.
  Definition mono_gmap_lb γ m :=
    auth_mono_lb subseteq γ m.
  Definition mono_gmap_at γ i v :=
    mono_gmap_lb γ {[i := v]}.
  Definition mono_gmap_elem γ i : iProp Σ :=
    ∃ v,
    mono_gmap_at γ i v.

  #[global] Instance mono_gmap_auth_timeless γ dq m :
    Timeless (mono_gmap_auth γ dq m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap_lb_timeless γ m :
    Timeless (mono_gmap_lb γ m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap_elem_timeless γ i :
    Timeless (mono_gmap_elem γ i).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap_auth_persistent γ m :
    Persistent (mono_gmap_auth γ DfracDiscarded m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap_lb_persistent γ m :
    Persistent (mono_gmap_lb γ m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap_elem_persistent γ i :
    Persistent (mono_gmap_elem γ i).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_gmap_auth_fractional γ m :
    Fractional (λ q, mono_gmap_auth γ (DfracOwn q) m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap_auth_as_fractional γ q m :
    AsFractional (mono_gmap_auth γ (DfracOwn q) m) (λ q, mono_gmap_auth γ (DfracOwn q) m) q.
  Proof.
    apply _.
  Qed.

  Lemma mono_gmap_alloc m :
    ⊢ |==>
      ∃ γ,
      mono_gmap_auth γ (DfracOwn 1) m.
  Proof.
    apply auth_mono_alloc.
  Qed.

  Lemma mono_gmap_at_to_elem γ i v :
    mono_gmap_at γ i v ⊢
    mono_gmap_elem γ i.
  Proof.
    rewrite /mono_gmap_elem. iSteps.
  Qed.
  Lemma mono_gmap_elem_to_at γ i :
    mono_gmap_elem γ i ⊢
      ∃ v,
      mono_gmap_at γ i v.
  Proof.
    done.
  Qed.

  Lemma mono_gmap_auth_valid γ dq m :
    mono_gmap_auth γ dq m ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono_auth_valid.
  Qed.
  Lemma mono_gmap_auth_combine γ dq1 m1 dq2 m2 :
    mono_gmap_auth γ dq1 m1 -∗
    mono_gmap_auth γ dq2 m2 -∗
      ⌜m1 = m2⌝ ∗
      mono_gmap_auth γ (dq1 ⋅ dq2) m1.
  Proof.
    apply: auth_mono_auth_combine.
  Qed.
  Lemma mono_gmap_auth_valid_2 γ dq1 m1 dq2 m2 :
    mono_gmap_auth γ dq1 m1 -∗
    mono_gmap_auth γ dq2 m2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜m1 = m2⌝.
  Proof.
    apply: auth_mono_auth_valid_2.
  Qed.
  Lemma mono_gmap_auth_agree γ dq1 m1 dq2 m2 :
    mono_gmap_auth γ dq1 m1 -∗
    mono_gmap_auth γ dq2 m2 -∗
    ⌜m1 = m2⌝.
  Proof.
    apply: auth_mono_auth_agree.
  Qed.
  Lemma mono_gmap_auth_dfrac_ne γ1 dq1 m1 γ2 dq2 m2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    mono_gmap_auth γ1 dq1 m1 -∗
    mono_gmap_auth γ2 dq2 m2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_dfrac_ne.
  Qed.
  Lemma mono_gmap_auth_ne γ1 m1 γ2 dq2 m2 :
    mono_gmap_auth γ1 (DfracOwn 1) m1 -∗
    mono_gmap_auth γ2 dq2 m2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_ne.
  Qed.
  Lemma mono_gmap_auth_exclusive γ m1 dq2 m2 :
    mono_gmap_auth γ (DfracOwn 1) m1 -∗
    mono_gmap_auth γ dq2 m2 -∗
    False.
  Proof.
    apply: auth_mono_auth_exclusive.
  Qed.
  Lemma mono_gmap_auth_persist γ dq m :
    mono_gmap_auth γ dq m ⊢ |==>
    mono_gmap_auth γ DfracDiscarded m.
  Proof.
    apply auth_mono_auth_persist.
  Qed.

  Lemma mono_gmap_lb_get γ dq m :
    mono_gmap_auth γ dq m ⊢
    mono_gmap_lb γ m.
  Proof.
    apply auth_mono_lb_get.
  Qed.
  Lemma mono_gmap_lb_mono {γ m} m' :
    m' ⊆ m →
    mono_gmap_lb γ m ⊢
    mono_gmap_lb γ m'.
  Proof.
    apply auth_mono_lb_mono'.
  Qed.
  Lemma mono_gmap_at_get {γ dq m} i v :
    m !! i = Some v →
    mono_gmap_auth γ dq m ⊢
    mono_gmap_at γ i v.
  Proof.
    iIntros "%Hlookup Hauth".
    iDestruct (mono_gmap_lb_get with "Hauth") as "Hlb".
    iApply (mono_gmap_lb_mono with "Hlb").
    rewrite map_singleton_subseteq_l //.
  Qed.

  Lemma mono_gmap_lb_valid γ dq m1 m2 :
    mono_gmap_auth γ dq m1 -∗
    mono_gmap_lb γ m2 -∗
    ⌜m2 ⊆ m1⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %Hm2.
    rewrite preorder_rtc in Hm2. iSteps.
  Qed.
  Lemma mono_gmap_at_valid γ dq m i v :
    mono_gmap_auth γ dq m -∗
    mono_gmap_at γ i v -∗
    ⌜m !! i = Some v⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (mono_gmap_lb_valid with "Hauth Hat") as %?%map_singleton_subseteq_l.
    iSteps.
  Qed.
  Lemma mono_gmap_elem_valid γ dq m i :
    mono_gmap_auth γ dq m -∗
    mono_gmap_elem γ i -∗
      ∃ v,
      ⌜m !! i = Some v⌝.
  Proof.
    iIntros "Hauth (%v & Hat)".
    iDestruct (mono_gmap_at_valid with "Hauth Hat") as "$".
  Qed.

  Lemma mono_gmap_update {γ m} m' :
    m ⊆ m' →
    mono_gmap_auth γ (DfracOwn 1) m ⊢ |==>
    mono_gmap_auth γ (DfracOwn 1) m'.
  Proof.
    apply auth_mono_update'.
  Qed.
  Lemma mono_gmap_insert {γ m} i v :
    m !! i = None →
    mono_gmap_auth γ (DfracOwn 1) m ⊢ |==>
    mono_gmap_auth γ (DfracOwn 1) (<[i := v]> m).
  Proof.
    intros Hlookup.
    apply mono_gmap_update, insert_subseteq. done.
  Qed.
  Lemma mono_gmap_insert' {γ m} i v :
    m !! i = None →
    mono_gmap_auth γ (DfracOwn 1) m ⊢ |==>
      mono_gmap_auth γ (DfracOwn 1) (<[i := v]> m) ∗
      mono_gmap_at γ i v.
  Proof.
    iIntros "%Hlookup Hauth".
    iMod (mono_gmap_insert i v with "Hauth") as "Hauth"; first done.
    iDestruct (mono_gmap_at_get i v with "Hauth") as "#Hat"; first rewrite lookup_insert //.
    iSteps.
  Qed.
End mono_gmap_G.

#[global] Opaque mono_gmap_auth.
#[global] Opaque mono_gmap_lb.
#[global] Opaque mono_gmap_elem.
