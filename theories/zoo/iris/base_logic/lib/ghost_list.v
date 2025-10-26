From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class GhostListG Σ A := {
  #[local] ghost_list_G_map_G :: ghost_mapG Σ nat A ;
}.

Definition ghost_list_Σ A := #[
  ghost_mapΣ nat A
].
#[global] Instance subG_ghost_list_Σ Σ A :
  subG (ghost_list_Σ A) Σ →
  GhostListG Σ A.
Proof.
  solve_inG.
Qed.

Section ghost_list_G.
  Context `{ghost_list_G : !GhostListG Σ A}.

  Implicit Types x : A.
  Implicit Types xs : list A.

  Definition ghost_list_auth γ xs :=
    ghost_map_auth γ 1 (map_seq 0 xs).
  Definition ghost_list_at γ :=
    ghost_map_elem γ.

  #[global] Instance ghost_list_auth_timeless γ vs :
    Timeless (ghost_list_auth γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_list_at_timeless γ i dq x :
    Timeless (ghost_list_at γ i dq x).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_list_at_persistent γ i x :
    Persistent (ghost_list_at γ i DfracDiscarded x).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_list_at_fractional γ i x :
    Fractional (λ q, ghost_list_at γ i (DfracOwn q) x).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_list_at_as_fractional γ i q x :
    AsFractional (ghost_list_at γ i (DfracOwn q) x) (λ q, ghost_list_at γ i (DfracOwn q) x) q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_list_alloc xs :
    ⊢ |==>
      ∃ γ,
      ghost_list_auth γ xs ∗
      [∗ list] i ↦ x ∈ xs,
        ghost_list_at γ i (DfracOwn 1) x.
  Proof.
    iMod (ghost_map_alloc (map_seq 0 xs)) as "(%γ & $ & ?)".
    rewrite big_sepM_map_seq_0 //.
  Qed.

  Lemma ghost_list_auth_exclusive γ xs1 xs2 :
    ghost_list_auth γ xs1 -∗
    ghost_list_auth γ xs2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (ghost_map_auth_valid_2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.

  Lemma ghost_list_at_valid γ i dq x :
    ghost_list_at γ i dq x ⊢
    ⌜✓ dq⌝.
  Proof.
    iApply ghost_map_elem_valid.
  Qed.
  Lemma ghost_list_at_combine γ i dq1 x1 dq2 x2 :
    ghost_list_at γ i dq1 x1 -∗
    ghost_list_at γ i dq2 x2 -∗
      ⌜x1 = x2⌝ ∗
      ghost_list_at γ i (dq1 ⋅ dq2) x1.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_map_elem_combine with "Hat1 Hat2") as "($ & $)".
  Qed.
  Lemma ghost_list_at_valid_2 γ i dq1 x1 dq2 x2 :
    ghost_list_at γ i dq1 x1 -∗
    ghost_list_at γ i dq2 x2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜x1 = x2⌝.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_list_at_combine with "Hat1 Hat2") as "(-> & Hat)".
    iDestruct (ghost_list_at_valid with "Hat") as "$".
    iSteps.
  Qed.
  Lemma ghost_list_at_agree γ i dq1 x1 dq2 x2 :
    ghost_list_at γ i dq1 x1 -∗
    ghost_list_at γ i dq2 x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_list_at_valid_2 with "Hat1 Hat2") as "(_ & $)".
  Qed.
  Lemma ghost_list_at_dfrac_ne γ1 i1 dq1 x1 γ2 i2 dq2 x2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_list_at γ1 i1 dq1 x1 -∗
    ghost_list_at γ2 i2 dq2 x2 -∗
    ⌜γ1 ≠ γ2 ∨ i1 ≠ i2⌝.
  Proof.
    rewrite -not_and_r. iIntros "% Hat1 Hat2 (-> & ->)".
    iDestruct (ghost_list_at_valid_2 with "Hat1 Hat2") as "(% & _)". done.
  Qed.
  Lemma ghost_list_at_ne γ1 i1 x1 γ2 i2 dq2 x2 :
    ghost_list_at γ1 i1 (DfracOwn 1) x1 -∗
    ghost_list_at γ2 i2 dq2 x2 -∗
    ⌜γ1 ≠ γ2 ∨ i1 ≠ i2⌝.
  Proof.
    iApply ghost_list_at_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma ghost_list_at_exclusive γ i x1 dq2 x2 :
    ghost_list_at γ i (DfracOwn 1) x1 -∗
    ghost_list_at γ i dq2 x2 -∗
    False.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_list_at_ne with "Hat1 Hat2") as %?. naive_solver.
  Qed.
  Lemma ghost_list_at_persist γ i dq x :
    ghost_list_at γ i dq x ⊢ |==>
    ghost_list_at γ i DfracDiscarded x.
  Proof.
    iApply ghost_map_elem_persist.
  Qed.

  Lemma ghost_list_lookup γ xs i dq x :
    ghost_list_auth γ xs -∗
    ghost_list_at γ i dq x -∗
    ⌜xs !! i = Some x⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (ghost_map_lookup with "Hauth Hat") as %?%(lookup_map_seq_Some_inv 0).
    iSteps.
  Qed.
  Lemma ghost_list_auth_ats γ xs1 dq xs2 :
    length xs1 = length xs2 →
    ghost_list_auth γ xs1 -∗
    ([∗ list] i ↦ x ∈ xs2, ghost_list_at γ i dq x) -∗
    ⌜xs1 = xs2⌝.
  Proof.
    iIntros "% Hauth Hats".
    rewrite common.list.list_eq.
    iStep 6 as (i x1 x2 Hxs1_lookup Hxs2_lookup).
    iDestruct (big_sepL_lookup with "Hats") as "Hat"; first done.
    iDestruct (ghost_list_lookup with "Hauth Hat") as %Hxs1_lookup_.
    naive_solver.
  Qed.

  Lemma ghost_list_update_push {γ xs} x :
    ghost_list_auth γ xs ⊢ |==>
      ghost_list_auth γ (xs ++ [x]) ∗
      ghost_list_at γ (length xs) (DfracOwn 1) x.
  Proof.
    iIntros "Hauth".
    iMod (ghost_map_insert (length xs) with "Hauth") as "(Hauth & $)".
    { apply (map_seq_snoc_disjoint 0). }
    rewrite -(map_seq_snoc 0) //.
  Qed.
  Lemma ghost_list_update_at {γ xs i x} x' :
    ghost_list_auth γ xs -∗
    ghost_list_at γ i (DfracOwn 1) x ==∗
      ghost_list_auth γ (<[i := x']> xs) ∗
      ghost_list_at γ i (DfracOwn 1) x'.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (ghost_list_lookup with "Hauth Hat") as %?%lookup_lt_Some.
    iMod (ghost_map_update x' with "Hauth Hat") as "(Hauth & $)".
    rewrite insert_map_seq_0 //.
  Qed.
End ghost_list_G.

#[global] Opaque ghost_list_auth.
#[global] Opaque ghost_list_at.
