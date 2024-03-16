From iris.bi Require Import
  lib.fractional.
From iris.base_logic Require Export
  lib.gen_heap
  lib.proph_map.
From iris.program_logic Require Export
  weakestpre.

From zebre Require Import
  prelude.
From zebre.iris Require Import
  diaframe.
From zebre.language Require Export
  language.
From zebre Require Import
  options.

Implicit Types σ : state.
Implicit Types κ : list observation.

Class ZebreGpre Σ := {
  #[global] zebre_Gpre_inv_Gpre :: invGpreS Σ ;
  #[local] zebre_Gpre_heap_Gpre :: gen_heapGpreS location val Σ ;
  #[local] zebre_Gpre_prophecy_Gpre :: proph_mapGpreS prophecy_id (val * val) Σ ;
}.

Definition zebre_Σ := #[
  invΣ ;
  gen_heapΣ location val ;
  proph_mapΣ prophecy_id (val * val)
].
#[global] Instance subG_zebre_Σ Σ :
  subG zebre_Σ Σ →
  ZebreGpre Σ.
Proof.
  solve_inG.
Qed.

Class ZebreG Σ := {
  zebre_G_inv_G : invGS Σ ;
  #[global] zebre_G_heap_G :: gen_heapGS location val Σ ;
  #[global] zebre_G_prophecy_map_G :: proph_mapGS prophecy_id (val * val) Σ ;
}.
#[global] Arguments Build_ZebreG _ {_ _ _} : assert.

Definition zebre_state_interp `{zebre_G : !ZebreG Σ} σ κ : iProp Σ :=
  gen_heap_interp σ.(state_heap) ∗
  proph_map_interp κ σ.(state_prophs).
#[global] Instance zebre_G_iris_G `{zebre_G : !ZebreG Σ} : irisGS zebre Σ := {
  iris_invGS :=
    zebre_G_inv_G ;
  state_interp σ _ κ _ :=
    zebre_state_interp σ κ ;
  fork_post _ :=
    True%I ;
  num_laters_per_step _ :=
    0 ;
  state_interp_mono _ _ _ _ :=
    fupd_intro _ _ ;
}.

Lemma zebre_init `{zebre_Gpre : !ZebreGpre Σ} `{inv_G : !invGS Σ} σ κ :
  ⊢ |==>
    ∃ zebre_G : ZebreG Σ,
    zebre_state_interp σ κ.
Proof.
  iMod (gen_heap_init σ.(state_heap)) as (?) "(Hσ & _)".
  iMod (proph_map_init κ σ.(state_prophs)) as "(% & Hκ)".
  iExists (Build_ZebreG Σ). iFrame. iSteps.
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
