From iris.bi Require Import
  lib.fractional.
From iris.base_logic Require Export
  lib.gen_heap.

From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Export
  wp.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Export
  language.
From zoo Require Import
  options.

Implicit Types σ : state.
Implicit Types κ : list observation.

Class ZooGpre Σ := {
  #[global] zoo_Gpre_inv_Gpre :: invGpreS Σ ;
  #[local] zoo_Gpre_heap_Gpre :: gen_heapGpreS location val Σ ;
}.

Definition zoo_Σ := #[
  invΣ ;
  gen_heapΣ location val
].
#[global] Instance subG_zoo_Σ Σ :
  subG zoo_Σ Σ →
  ZooGpre Σ.
Proof.
  solve_inG.
Qed.

Class ZooG Σ := {
  zoo_G_inv_G : invGS Σ ;
  #[global] zoo_G_heap_G :: gen_heapGS location val Σ ;
}.
#[global] Arguments Build_ZooG _ {_ _} : assert.

Definition zoo_state_interp `{zoo_G : !ZooG Σ} (_ : nat) σ κ : iProp Σ :=
  gen_heap_interp σ.(state_heap).
#[global] Instance zoo_G_iris_G `{zoo_G : !ZooG Σ} : IrisG zoo Σ := {
  iris_G_inv_G :=
    zoo_G_inv_G ;
  state_interp :=
    zoo_state_interp ;
  fork_post _ :=
    True%I ;
}.

Lemma zoo_init `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} nt σ κ :
  ⊢ |==>
    ∃ zoo_G : ZooG Σ,
    state_interp nt σ κ.
Proof.
  iMod (gen_heap_init σ.(state_heap)) as (?) "(Hσ & _)".
  iExists (Build_ZooG Σ). iFrame. iSteps.
Qed.
Lemma zoo_init' `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} σ κ :
  ⊢ |==>
    ∃ zoo_G : ZooG Σ,
    state_interp 0 σ κ.
Proof.
  apply zoo_init.
Qed.

Notation "l ↦ dq v" := (
  pointsto (L := location) (V := val) l dq v%V
)(at level 20,
  dq custom dfrac at level 1,
  format "l  ↦ dq  v"
) : bi_scope.

Notation "l ↦∗ dq vs" :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v)%I
( at level 20,
  dq custom dfrac at level 1,
  format "l  ↦∗ dq  vs"
) : bi_scope.
