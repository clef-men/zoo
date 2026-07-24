Require Import zoo.prelude.
Require Import zoo.common.relations.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class MonoGmapG Σ K V `{Countable K} :=
  { #[local] mono_gmap۰G۰mono۰G :: AuthMonoG Σ (A := leibnizO (gmap K V)) (subseteq (A := gmap K V))
  }.

Definition mono_gmap۰Σ K V `{Countable K} :=
  #[auth_mono۰Σ (A := leibnizO (gmap K V)) (subseteq (A := gmap K V))
  ].
#[global] Instance subG𑁒mono_gmap۰Σ Σ K V `{Countable K} :
  subG (mono_gmap۰Σ K V) Σ →
  MonoGmapG Σ K V.
Proof.
  solve_inG.
Qed.

Section mono_gmap۰G.
  Context `{mono_gmap۰G : MonoGmapG Σ K V}.

  Implicit Type v : V.
  Implicit Type m : gmap K V.

  #[local] Instance map𑁒subseteq𑁒partialorder :
    PartialOrder (A := gmap K V) subseteq.
  Proof.
    apply _.
  Qed.

  Definition mono_gmap۰auth γ dq m :=
    auth_mono۰auth subseteq γ dq m.
  Definition mono_gmap۰lb γ m :=
    auth_mono۰lb subseteq γ m.
  Definition mono_gmap۰at γ i v :=
    mono_gmap۰lb γ {[i := v]}.
  Definition mono_gmap۰elem γ i : iProp Σ :=
    ∃ v,
    mono_gmap۰at γ i v.

  #[global] Instance mono_gmap۰auth𑁒timeless γ dq m :
    Timeless (mono_gmap۰auth γ dq m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap۰lb𑁒timeless γ m :
    Timeless (mono_gmap۰lb γ m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap۰elem𑁒timeless γ i :
    Timeless (mono_gmap۰elem γ i).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_gmap۰auth𑁒persistent γ m :
    Persistent (mono_gmap۰auth γ DfracDiscarded m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap۰lb𑁒persistent γ m :
    Persistent (mono_gmap۰lb γ m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap۰elem𑁒persistent γ i :
    Persistent (mono_gmap۰elem γ i).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_gmap۰auth𑁒fractional γ m :
    Fractional (λ q, mono_gmap۰auth γ (DfracOwn q) m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmap۰auth𑁒as_fractional γ q m :
    AsFractional (mono_gmap۰auth γ (DfracOwn q) m) (λ q, mono_gmap۰auth γ (DfracOwn q) m) q.
  Proof.
    apply _.
  Qed.

  Lemma mono_gmap𑁒alloc m :
    ⊢ |==>
      ∃ γ,
      mono_gmap۰auth γ (DfracOwn 1) m.
  Proof.
    apply auth_mono𑁒alloc.
  Qed.

  Lemma mono_gmap۰at𑁒to𑁒elem γ i v :
    mono_gmap۰at γ i v ⊢
    mono_gmap۰elem γ i.
  Proof.
    rewrite /mono_gmap۰elem. iSteps.
  Qed.
  Lemma mono_gmap۰elem𑁒to𑁒at γ i :
    mono_gmap۰elem γ i ⊢
      ∃ v,
      mono_gmap۰at γ i v.
  Proof.
    done.
  Qed.

  Lemma mono_gmap۰auth𑁒valid γ dq m :
    mono_gmap۰auth γ dq m ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono۰auth𑁒valid.
  Qed.
  Lemma mono_gmap۰auth𑁒combine γ dq1 m1 dq2 m2 :
    mono_gmap۰auth γ dq1 m1 -∗
    mono_gmap۰auth γ dq2 m2 -∗
      ⌜m1 = m2⌝ ∗
      mono_gmap۰auth γ (dq1 ⋅ dq2) m1.
  Proof.
    apply: auth_mono۰auth𑁒combine.
  Qed.
  Lemma mono_gmap۰auth𑁒valid𑁒2 γ dq1 m1 dq2 m2 :
    mono_gmap۰auth γ dq1 m1 -∗
    mono_gmap۰auth γ dq2 m2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜m1 = m2⌝.
  Proof.
    apply: auth_mono۰auth𑁒valid𑁒2.
  Qed.
  Lemma mono_gmap۰auth𑁒agree γ dq1 m1 dq2 m2 :
    mono_gmap۰auth γ dq1 m1 -∗
    mono_gmap۰auth γ dq2 m2 -∗
    ⌜m1 = m2⌝.
  Proof.
    apply: auth_mono۰auth𑁒agree.
  Qed.
  Lemma mono_gmap۰auth𑁒dfrac𑁒ne γ1 dq1 m1 γ2 dq2 m2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    mono_gmap۰auth γ1 dq1 m1 -∗
    mono_gmap۰auth γ2 dq2 m2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰auth𑁒dfrac𑁒ne.
  Qed.
  Lemma mono_gmap۰auth𑁒ne γ1 m1 γ2 dq2 m2 :
    mono_gmap۰auth γ1 (DfracOwn 1) m1 -∗
    mono_gmap۰auth γ2 dq2 m2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰auth𑁒ne.
  Qed.
  Lemma mono_gmap۰auth𑁒exclusive γ m1 dq2 m2 :
    mono_gmap۰auth γ (DfracOwn 1) m1 -∗
    mono_gmap۰auth γ dq2 m2 -∗
    False.
  Proof.
    apply: auth_mono۰auth𑁒exclusive.
  Qed.
  Lemma mono_gmap۰auth𑁒persist γ dq m :
    mono_gmap۰auth γ dq m ⊢ |==>
    mono_gmap۰auth γ DfracDiscarded m.
  Proof.
    apply auth_mono۰auth𑁒persist.
  Qed.

  Lemma mono_gmap۰lb𑁒get γ dq m :
    mono_gmap۰auth γ dq m ⊢
    mono_gmap۰lb γ m.
  Proof.
    apply auth_mono۰lb𑁒get.
  Qed.
  Lemma mono_gmap۰lb𑁒mono {γ m} m' :
    m' ⊆ m →
    mono_gmap۰lb γ m ⊢
    mono_gmap۰lb γ m'.
  Proof.
    apply auth_mono۰lb𑁒mono'.
  Qed.
  Lemma mono_gmap۰at𑁒get {γ dq m} i v :
    m !! i = Some v →
    mono_gmap۰auth γ dq m ⊢
    mono_gmap۰at γ i v.
  Proof.
    iIntros "%Hlookup Hauth".
    iDestruct (mono_gmap۰lb𑁒get with "Hauth") as "Hlb".
    iApply (mono_gmap۰lb𑁒mono with "Hlb").
    rewrite map_singleton_subseteq_l //.
  Qed.

  Lemma mono_gmap۰lb𑁒valid γ dq m1 m2 :
    mono_gmap۰auth γ dq m1 -∗
    mono_gmap۰lb γ m2 -∗
    ⌜m2 ⊆ m1⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono۰lb𑁒valid with "Hauth Hlb") as %Hm2.
    rewrite preorder𑁒rtc in Hm2. iSteps.
  Qed.
  Lemma mono_gmap۰at𑁒valid γ dq m i v :
    mono_gmap۰auth γ dq m -∗
    mono_gmap۰at γ i v -∗
    ⌜m !! i = Some v⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (mono_gmap۰lb𑁒valid with "Hauth Hat") as %?%map_singleton_subseteq_l.
    iSteps.
  Qed.
  Lemma mono_gmap۰elem𑁒valid γ dq m i :
    mono_gmap۰auth γ dq m -∗
    mono_gmap۰elem γ i -∗
      ∃ v,
      ⌜m !! i = Some v⌝.
  Proof.
    iIntros "Hauth (%v & Hat)".
    iDestruct (mono_gmap۰at𑁒valid with "Hauth Hat") as "$".
  Qed.

  Lemma mono_gmap𑁒update {γ m} m' :
    m ⊆ m' →
    mono_gmap۰auth γ (DfracOwn 1) m ⊢ |==>
    mono_gmap۰auth γ (DfracOwn 1) m'.
  Proof.
    apply auth_mono𑁒update'.
  Qed.
  Lemma mono_gmap𑁒insert {γ m} i v :
    m !! i = None →
    mono_gmap۰auth γ (DfracOwn 1) m ⊢ |==>
    mono_gmap۰auth γ (DfracOwn 1) (<[i := v]> m).
  Proof.
    intros Hlookup.
    apply mono_gmap𑁒update, insert_subseteq. done.
  Qed.
  Lemma mono_gmap𑁒insert' {γ m} i v :
    m !! i = None →
    mono_gmap۰auth γ (DfracOwn 1) m ⊢ |==>
      mono_gmap۰auth γ (DfracOwn 1) (<[i := v]> m) ∗
      mono_gmap۰at γ i v.
  Proof.
    iIntros "%Hlookup Hauth".
    iMod (mono_gmap𑁒insert i v with "Hauth") as "Hauth"; first done.
    iDestruct (mono_gmap۰at𑁒get i v with "Hauth") as "#Hat"; first rewrite lookup_insert_eq //.
    iSteps.
  Qed.
End mono_gmap۰G.

#[global] Opaque mono_gmap۰auth.
#[global] Opaque mono_gmap۰lb.
#[global] Opaque mono_gmap۰elem.
