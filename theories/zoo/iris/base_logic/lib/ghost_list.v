From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class GhostListG Σ V := {
  #[local] ghost_list_G_map_G :: ghost_mapG Σ nat V ;
}.

Definition ghost_list_Σ V := #[
  ghost_mapΣ nat V
].
#[global] Instance subG_ghost_list_Σ Σ V :
  subG (ghost_list_Σ V) Σ →
  GhostListG Σ V.
Proof.
  solve_inG.
Qed.

Section ghost_list_G.
  Context `{ghost_list_G : !GhostListG Σ V}.

  Definition ghost_list_auth γ vs :=
    ghost_map_auth γ 1 (map_seq 0 vs).
  Definition ghost_list_at γ :=
    ghost_map_elem γ.

  #[global] Instance ghost_list_auth_timeless γ vs :
    Timeless (ghost_list_auth γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_list_at_timeless γ i dq v :
    Timeless (ghost_list_at γ i dq v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_list_at_persistent γ i v :
    Persistent (ghost_list_at γ i DfracDiscarded v).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_list_at_fractional γ i v :
    Fractional (λ q, ghost_list_at γ i (DfracOwn q) v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_list_at_as_fractional γ i q v :
    AsFractional (ghost_list_at γ i (DfracOwn q) v) (λ q, ghost_list_at γ i (DfracOwn q) v) q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_list_alloc vs :
    ⊢ |==>
      ∃ γ,
      ghost_list_auth γ vs ∗
      [∗ list] i ↦ v ∈ vs,
        ghost_list_at γ i (DfracOwn 1) v.
  Proof.
    iMod (ghost_map_alloc (map_seq 0 vs)) as "(%γ & $ & ?)".
    rewrite big_sepM_map_seq_0 //.
  Qed.

  Lemma ghost_list_auth_exclusive γ vs1 vs2 :
    ghost_list_auth γ vs1 -∗
    ghost_list_auth γ vs2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (ghost_map_auth_valid_2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.

  Lemma ghost_list_at_valid γ i dq v :
    ghost_list_at γ i dq v ⊢
    ⌜✓ dq⌝.
  Proof.
    iApply ghost_map_elem_valid.
  Qed.
  Lemma ghost_list_at_combine γ i dq1 v1 dq2 v2 :
    ghost_list_at γ i dq1 v1 -∗
    ghost_list_at γ i dq2 v2 -∗
      ⌜v1 = v2⌝ ∗
      ghost_list_at γ i (dq1 ⋅ dq2) v1.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_map_elem_combine with "Hat1 Hat2") as "($ & $)".
  Qed.
  Lemma ghost_list_at_valid_2 γ i dq1 v1 dq2 v2 :
    ghost_list_at γ i dq1 v1 -∗
    ghost_list_at γ i dq2 v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_list_at_combine with "Hat1 Hat2") as "(-> & Hat)".
    iDestruct (ghost_list_at_valid with "Hat") as "$".
    iSteps.
  Qed.
  Lemma ghost_list_at_agree γ i dq1 v1 dq2 v2 :
    ghost_list_at γ i dq1 v1 -∗
    ghost_list_at γ i dq2 v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_list_at_valid_2 with "Hat1 Hat2") as "(_ & $)".
  Qed.
  Lemma ghost_list_at_dfrac_ne γ1 i1 dq1 v1 γ2 i2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_list_at γ1 i1 dq1 v1 -∗
    ghost_list_at γ2 i2 dq2 v2 -∗
    ⌜γ1 ≠ γ2 ∨ i1 ≠ i2⌝.
  Proof.
    rewrite -not_and_r. iIntros "% Hat1 Hat2 (-> & ->)".
    iDestruct (ghost_list_at_valid_2 with "Hat1 Hat2") as "(% & _)". done.
  Qed.
  Lemma ghost_list_at_ne γ1 i1 v1 γ2 i2 dq2 v2 :
    ghost_list_at γ1 i1 (DfracOwn 1) v1 -∗
    ghost_list_at γ2 i2 dq2 v2 -∗
    ⌜γ1 ≠ γ2 ∨ i1 ≠ i2⌝.
  Proof.
    iApply ghost_list_at_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma ghost_list_at_exclusive γ i v1 dq2 v2 :
    ghost_list_at γ i (DfracOwn 1) v1 -∗
    ghost_list_at γ i dq2 v2 -∗
    False.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (ghost_list_at_ne with "Hat1 Hat2") as %?. naive_solver.
  Qed.
  Lemma ghost_list_at_persist γ i dq v :
    ghost_list_at γ i dq v ⊢ |==>
    ghost_list_at γ i DfracDiscarded v.
  Proof.
    iApply ghost_map_elem_persist.
  Qed.

  Lemma ghost_list_lookup γ vs i dq v :
    ghost_list_auth γ vs -∗
    ghost_list_at γ i dq v -∗
    ⌜vs !! i = Some v⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (ghost_map_lookup with "Hauth Hat") as %?%(lookup_map_seq_Some_inv 0).
    iSteps.
  Qed.

  Lemma ghost_list_update_push {γ vs} v :
    ghost_list_auth γ vs ⊢ |==>
      ghost_list_auth γ (vs ++ [v]) ∗
      ghost_list_at γ (length vs) (DfracOwn 1) v.
  Proof.
    iIntros "Hauth".
    iMod (ghost_map_insert (length vs) with "Hauth") as "(Hauth & $)".
    { apply (map_seq_snoc_disjoint 0). }
    rewrite -(map_seq_snoc 0) //.
  Qed.
  Lemma ghost_list_update_at {γ vs i w} v :
    ghost_list_auth γ vs -∗
    ghost_list_at γ i (DfracOwn 1) w ==∗
      ghost_list_auth γ (<[i := v]> vs) ∗
      ghost_list_at γ i (DfracOwn 1) v.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (ghost_list_lookup with "Hauth Hat") as %?%lookup_lt_Some.
    iMod (ghost_map_update v with "Hauth Hat") as "(Hauth & $)".
    rewrite insert_map_seq_0 //.
  Qed.
End ghost_list_G.

#[global] Opaque ghost_list_auth.
#[global] Opaque ghost_list_at.
