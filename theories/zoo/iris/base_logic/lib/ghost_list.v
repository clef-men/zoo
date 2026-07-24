Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.iris.bi.big_op.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class GhostListG Σ A :=
  { #[local] ghost_list۰G۰map۰G :: ghost_mapG Σ nat A
  }.

Definition ghost_list۰Σ A :=
  #[ghost_mapΣ nat A
  ].
#[global] Instance subG𑁒ghost_list۰Σ Σ A :
  subG (ghost_list۰Σ A) Σ →
  GhostListG Σ A.
Proof.
  solve_inG.
Qed.

Section ghost_list۰G.
  Context `{ghost_list۰G : !GhostListG Σ A}.

  Implicit Type x : A.
  Implicit Type xs : list A.

  Definition ghost_list۰auth γ xs :=
    ghost_map_auth γ 1 (map_seq 0 xs).
  Definition ghost_list۰at γ :=
    ghost_map_elem γ.

  #[global] Instance ghost_list۰auth𑁒timeless γ vs :
    Timeless (ghost_list۰auth γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_list۰at𑁒timeless γ i dq x :
    Timeless (ghost_list۰at γ i dq x).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_list۰at𑁒persistent γ i x :
    Persistent (ghost_list۰at γ i DfracDiscarded x).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_list۰at𑁒fractional γ i x :
    Fractional (λ q, ghost_list۰at γ i (DfracOwn q) x).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_list۰at𑁒as_fractional γ i q x :
    AsFractional (ghost_list۰at γ i (DfracOwn q) x) (λ q, ghost_list۰at γ i (DfracOwn q) x) q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_list𑁒alloc xs :
    ⊢ |==>
      ∃ γ,
      ghost_list۰auth γ xs ∗
      [∗ list] i ↦ x ∈ xs,
        ghost_list۰at γ i (DfracOwn 1) x.
  Proof.
    iMod (ghost_map_alloc (map_seq 0 xs)) as "(%γ & $ & ?)".
    rewrite big_sepM𑁒map_seq𑁒0 //.
  Qed.

  Lemma ghost_list۰auth𑁒exclusive γ xs1 xs2 :
    ghost_list۰auth γ xs1 -∗
    ghost_list۰auth γ xs2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (ghost_map_auth_valid_2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.

  Lemma ghost_list۰at𑁒valid γ i dq x :
    ghost_list۰at γ i dq x ⊢
    ⌜✓ dq⌝.
  Proof.
    iApply ghost_map_elem_valid.
  Qed.
  Lemma ghost_list۰at𑁒combine γ i dq1 x1 dq2 x2 :
    ghost_list۰at γ i dq1 x1 -∗
    ghost_list۰at γ i dq2 x2 -∗
      ⌜x1 = x2⌝ ∗
      ghost_list۰at γ i (dq1 ⋅ dq2) x1.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_map_elem_combine with "Hat1 Hat2") as "($ & $)".
  Qed.
  Lemma ghost_list۰at𑁒valid𑁒2 γ i dq1 x1 dq2 x2 :
    ghost_list۰at γ i dq1 x1 -∗
    ghost_list۰at γ i dq2 x2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜x1 = x2⌝.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_list۰at𑁒combine with "Hat1 Hat2") as "(-> & Hat)".
    iDestruct (ghost_list۰at𑁒valid with "Hat") as "$".
    iSteps.
  Qed.
  Lemma ghost_list۰at𑁒agree γ i dq1 x1 dq2 x2 :
    ghost_list۰at γ i dq1 x1 -∗
    ghost_list۰at γ i dq2 x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_list۰at𑁒valid𑁒2 with "Hat1 Hat2") as "(_ & $)".
  Qed.
  Lemma ghost_list۰at𑁒dfrac𑁒ne γ1 i1 dq1 x1 γ2 i2 dq2 x2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_list۰at γ1 i1 dq1 x1 -∗
    ghost_list۰at γ2 i2 dq2 x2 -∗
    ⌜γ1 ≠ γ2 ∨ i1 ≠ i2⌝.
  Proof.
    rewrite -not_and_r. iIntros "% Hat1 Hat2 (-> & ->)".
    iDestruct (ghost_list۰at𑁒valid𑁒2 with "Hat1 Hat2") as "(% & _)". done.
  Qed.
  Lemma ghost_list۰at𑁒ne γ1 i1 x1 γ2 i2 dq2 x2 :
    ghost_list۰at γ1 i1 (DfracOwn 1) x1 -∗
    ghost_list۰at γ2 i2 dq2 x2 -∗
    ⌜γ1 ≠ γ2 ∨ i1 ≠ i2⌝.
  Proof.
    iApply ghost_list۰at𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma ghost_list۰at𑁒exclusive γ i x1 dq2 x2 :
    ghost_list۰at γ i (DfracOwn 1) x1 -∗
    ghost_list۰at γ i dq2 x2 -∗
    False.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_list۰at𑁒ne with "Hat1 Hat2") as %?. naive_solver.
  Qed.
  Lemma ghost_list۰at𑁒persist γ i dq x :
    ghost_list۰at γ i dq x ⊢ |==>
    ghost_list۰at γ i DfracDiscarded x.
  Proof.
    iApply ghost_map_elem_persist.
  Qed.

  Lemma ghost_list𑁒lookup γ xs i dq x :
    ghost_list۰auth γ xs -∗
    ghost_list۰at γ i dq x -∗
    ⌜xs !! i = Some x⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (ghost_map_lookup with "Hauth Hat") as %?%(lookup_map_seq_Some_inv 0).
    iSteps.
  Qed.
  Lemma ghost_list𑁒auth𑁒ats γ xs1 dq xs2 :
    length xs1 = length xs2 →
    ghost_list۰auth γ xs1 -∗
    ([∗ list] i ↦ x ∈ xs2, ghost_list۰at γ i dq x) -∗
    ⌜xs1 = xs2⌝.
  Proof.
    iIntros "% Hauth Hats".
    rewrite list𑁒eq.
    iStep 6 as (i x1 x2 Hxs1_lookup Hxs2_lookup).
    iDestruct (big_sepL_lookup with "Hats") as "Hat"; first done.
    iDestruct (ghost_list𑁒lookup with "Hauth Hat") as %Hxs1_lookup_.
    naive_solver.
  Qed.

  Lemma ghost_list𑁒update𑁒push {γ xs} x :
    ghost_list۰auth γ xs ⊢ |==>
      ghost_list۰auth γ (xs ++ [x]) ∗
      ghost_list۰at γ (length xs) (DfracOwn 1) x.
  Proof.
    iIntros "Hauth".
    iMod (ghost_map_insert (length xs) with "Hauth") as "(Hauth & $)".
    { apply (map_seq_snoc_disjoint 0). }
    rewrite -(map_seq_snoc 0) //.
  Qed.
  Lemma ghost_list𑁒update𑁒at {γ xs i x} x' :
    ghost_list۰auth γ xs -∗
    ghost_list۰at γ i (DfracOwn 1) x ==∗
      ghost_list۰auth γ (<[i := x']> xs) ∗
      ghost_list۰at γ i (DfracOwn 1) x'.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (ghost_list𑁒lookup with "Hauth Hat") as %?%lookup_lt_Some.
    iMod (ghost_map_update x' with "Hauth Hat") as "(Hauth & $)".
    rewrite insert_map_seq_0 //.
  Qed.
End ghost_list۰G.

#[global] Opaque ghost_list۰auth.
#[global] Opaque ghost_list۰at.
