Require Import zoo.prelude.
Require Import zoo.common.relations.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class MonoListG Σ A :=
  { #[local] mono_list۰G۰mono۰G :: AuthMonoG Σ (A := leibnizO (list A)) prefix
  }.

Definition mono_list۰Σ A :=
  #[auth_mono۰Σ (A := leibnizO (list A)) prefix
  ].
#[global] Instance subG𑁒mono_list۰Σ Σ A :
  subG (mono_list۰Σ A) Σ →
  MonoListG Σ A.
Proof.
  solve_inG.
Qed.

Section mono_list۰G.
  Context `{mono_list۰G : !MonoListG Σ A}.

  Implicit Type i : nat.
  Implicit Type a : A.
  Implicit Type l : list A.

  Definition mono_list۰auth γ dq l :=
    auth_mono۰auth (A := leibnizO (list A)) prefix γ dq l.
  Definition mono_list۰lb γ l :=
    auth_mono۰lb (A := leibnizO (list A)) prefix γ l.
  Definition mono_list۰at γ i a : iProp Σ :=
    ∃ l,
    ⌜l !! i = Some a⌝ ∗
    mono_list۰lb γ l.
  Definition mono_list۰elem γ a : iProp Σ :=
    ∃ i,
    mono_list۰at γ i a.

  #[global] Instance mono_list۰auth𑁒timeless γ dq l :
    Timeless (mono_list۰auth γ dq l).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list۰lb𑁒timeless γ l :
    Timeless (mono_list۰lb γ l).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list۰at𑁒timeless γ i a :
    Timeless (mono_list۰at γ i a).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list۰elem𑁒timeless γ a :
    Timeless (mono_list۰elem γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_list۰lb𑁒persistent γ l :
    Persistent (mono_list۰lb γ l).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list۰at𑁒persistent γ i a :
    Persistent (mono_list۰at γ i a).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list۰elem𑁒persistent γ a :
    Persistent (mono_list۰elem γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_list۰auth𑁒fractional γ l :
    Fractional (λ q, mono_list۰auth γ (DfracOwn q) l).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_list۰auth𑁒as_fractional γ q l :
    AsFractional (mono_list۰auth γ (DfracOwn q) l) (λ q, mono_list۰auth γ (DfracOwn q) l) q.
  Proof.
    apply _.
  Qed.

  Lemma mono_list𑁒alloc l :
    ⊢ |==>
      ∃ γ,
      mono_list۰auth γ (DfracOwn 1) l.
  Proof.
    apply auth_mono𑁒alloc.
  Qed.

  Lemma mono_list۰auth𑁒valid γ dq l :
    mono_list۰auth γ dq l ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono۰auth𑁒valid.
  Qed.
  Lemma mono_list۰auth𑁒combine γ dq1 l1 dq2 l2 :
    mono_list۰auth γ dq1 l1 -∗
    mono_list۰auth γ dq2 l2 -∗
      ⌜l1 = l2⌝ ∗
      mono_list۰auth γ (dq1 ⋅ dq2) l1.
  Proof.
    apply: auth_mono۰auth𑁒combine.
  Qed.
  Lemma mono_list۰auth𑁒valid𑁒2 γ dq1 l1 dq2 l2 :
    mono_list۰auth γ dq1 l1 -∗
    mono_list۰auth γ dq2 l2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜l1 = l2⌝.
  Proof.
    apply: auth_mono۰auth𑁒valid𑁒2.
  Qed.
  Lemma mono_list۰auth𑁒agree γ dq1 l1 dq2 l2 :
    mono_list۰auth γ dq1 l1 -∗
    mono_list۰auth γ dq2 l2 -∗
    ⌜l1 = l2⌝.
  Proof.
    apply: auth_mono۰auth𑁒agree.
  Qed.
  Lemma mono_list۰auth𑁒dfrac𑁒ne γ1 dq1 l1 γ2 dq2 l2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    mono_list۰auth γ1 dq1 l1 -∗
    mono_list۰auth γ2 dq2 l2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰auth𑁒dfrac𑁒ne.
  Qed.
  Lemma mono_list۰auth𑁒ne γ1 l1 γ2 dq2 l2 :
    mono_list۰auth γ1 (DfracOwn 1) l1 -∗
    mono_list۰auth γ2 dq2 l2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰auth𑁒ne.
  Qed.
  Lemma mono_list۰auth𑁒exclusive γ l1 dq2 l2 :
    mono_list۰auth γ (DfracOwn 1) l1 -∗
    mono_list۰auth γ dq2 l2 -∗
    False.
  Proof.
    apply: auth_mono۰auth𑁒exclusive.
  Qed.
  Lemma mono_list۰auth𑁒persist γ dq l :
    mono_list۰auth γ dq l ⊢ |==>
    mono_list۰auth γ DfracDiscarded l.
  Proof.
    apply auth_mono۰auth𑁒persist.
  Qed.

  Lemma mono_list۰lb𑁒get γ q l :
    mono_list۰auth γ q l ⊢
    mono_list۰lb γ l.
  Proof.
    apply auth_mono۰lb𑁒get.
  Qed.
  Lemma mono_list۰at𑁒get {γ q l} i a :
    l !! i = Some a →
    mono_list۰auth γ q l ⊢
    mono_list۰at γ i a.
  Proof.
    rewrite mono_list۰lb𑁒get. iSteps.
  Qed.
  Lemma mono_list۰elem𑁒get {γ q l} a :
    a ∈ l →
    mono_list۰auth γ q l ⊢
    mono_list۰elem γ a.
  Proof.
    intros (i & Hlookup)%list_elem_of_lookup.
    rewrite mono_list۰at𑁒get //. iSteps.
  Qed.

  Lemma mono_list۰lb𑁒mono {γ l} l' :
    l' `prefix_of` l →
    mono_list۰lb γ l ⊢
    mono_list۰lb γ l'.
  Proof.
    apply auth_mono۰lb𑁒mono'.
  Qed.

  Lemma mono_list۰lb𑁒valid γ dq l1 l2 :
    mono_list۰auth γ dq l1 -∗
    mono_list۰lb γ l2 -∗
    ⌜l2 `prefix_of` l1⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono۰lb𑁒valid with "Hauth Hlb") as %Hl2.
    rewrite preorder𑁒rtc in Hl2. iSteps.
  Qed.
  Lemma mono_list۰lb𑁒agree γ l1 l2 :
    mono_list۰lb γ l1 -∗
    mono_list۰lb γ l2 -∗
      ∃ l,
      ⌜l1 `prefix_of` l⌝ ∧
      ⌜l2 `prefix_of` l⌝.
  Proof.
    iIntros "Hlb1 Hlb2".
    iDestruct (auth_mono۰lb𑁒agree with "Hlb1 Hlb2") as %(l & Hl1 & Hl2).
    rewrite !preorder𑁒rtc in Hl1 Hl2. iSteps.
  Qed.
  Lemma mono_list۰at𑁒valid γ q l i a :
    mono_list۰auth γ q l -∗
    mono_list۰at γ i a -∗
    ⌜l !! i = Some a⌝.
  Proof.
    iIntros "Hauth (%l1 & %Hlookup & Hlb)".
    iDestruct (mono_list۰lb𑁒valid with "Hauth Hlb") as %(l2 & ->).
    iPureIntro. apply lookup_app_l_Some. done.
  Qed.
  Lemma mono_list۰at𑁒agree γ i a1 a2 :
    mono_list۰at γ i a1 -∗
    mono_list۰at γ i a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "(%l1 & %Hlookup1 & Hlb1) (%l2 & %Hlookup2 & Hlb2)".
    iDestruct (mono_list۰lb𑁒agree with "Hlb1 Hlb2") as %(l & Hl1 & Hl2).
    edestruct (prefix_weak_total l1 l2); [done.. | |].
    1: erewrite (prefix_lookup_Some l1 l2) in Hlookup2; [| done..].
    2: erewrite (prefix_lookup_Some l2 l1) in Hlookup1; [| done..].
    all: naive_solver.
  Qed.
  Lemma mono_list۰elem𑁒valid γ q l a :
    mono_list۰auth γ q l -∗
    mono_list۰elem γ a -∗
    ⌜a ∈ l⌝.
  Proof.
    iIntros "Hauth (%i & Hat)".
    iDestruct (mono_list۰at𑁒valid with "Hauth Hat") as %Hlookup.
    iPureIntro. apply list_elem_of_lookup. naive_solver.
  Qed.

  Lemma mono_list𑁒update {γ l} l' :
    l `prefix_of` l' →
    mono_list۰auth γ (DfracOwn 1) l ⊢ |==>
    mono_list۰auth γ (DfracOwn 1) l'.
  Proof.
    apply auth_mono𑁒update'.
  Qed.
  Lemma mono_list𑁒update𑁒app {γ l} l' :
    mono_list۰auth γ (DfracOwn 1) l ⊢ |==>
    mono_list۰auth γ (DfracOwn 1) (l ++ l').
  Proof.
    apply mono_list𑁒update, prefix_app_r. done.
  Qed.
  Lemma mono_list𑁒update𑁒snoc {γ l} a :
    mono_list۰auth γ (DfracOwn 1) l ⊢ |==>
    mono_list۰auth γ (DfracOwn 1) (l ++ [a]).
  Proof.
    apply mono_list𑁒update𑁒app.
  Qed.
End mono_list۰G.

#[global] Opaque mono_list۰auth.
#[global] Opaque mono_list۰lb.
#[global] Typeclasses Opaque mono_list۰at.
#[global] Typeclasses Opaque mono_list۰elem.
