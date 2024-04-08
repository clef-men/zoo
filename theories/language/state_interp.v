From iris.bi Require Import
  lib.fractional.
From iris.base_logic Require Export
  lib.gen_heap.

From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Export
  prophet_map.
From zebre.iris.program_logic Require Export
  wp.
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
  #[local] zebre_Gpre_prophecy_Gpre :: ProphetMapGpre Σ prophet_id (val * val) ;
}.

Definition zebre_Σ := #[
  invΣ ;
  gen_heapΣ location val ;
  prophet_map_Σ prophet_id (val * val)
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
  #[global] zebre_G_prophecy_map_G :: ProphetMapG Σ prophet_id (val * val) ;
}.
#[global] Arguments Build_ZebreG _ {_ _ _} : assert.

Definition zebre_state_interp `{zebre_G : !ZebreG Σ} (_ : nat) σ κ : iProp Σ :=
  gen_heap_interp σ.(state_heap) ∗
  prophet_map_interp κ σ.(state_prophets).
#[global] Instance zebre_G_iris_G `{zebre_G : !ZebreG Σ} : IrisG zebre Σ := {
  iris_G_inv_G :=
    zebre_G_inv_G ;
  state_interp :=
    zebre_state_interp ;
  fork_post _ :=
    True%I ;
}.

Lemma zebre_init `{zebre_Gpre : !ZebreGpre Σ} `{inv_G : !invGS Σ} nt σ κ :
  ⊢ |==>
    ∃ zebre_G : ZebreG Σ,
    state_interp nt σ κ.
Proof.
  iMod (gen_heap_init σ.(state_heap)) as (?) "(Hσ & _)".
  iMod (prophet_map_init κ σ.(state_prophets)) as "(% & Hκ)".
  iExists (Build_ZebreG Σ). iFrame. iSteps.
Qed.
Lemma zebre_init' `{zebre_Gpre : !ZebreGpre Σ} `{inv_G : !invGS Σ} σ κ :
  ⊢ |==>
    ∃ zebre_G : ZebreG Σ,
    state_interp 0 σ κ.
Proof.
  apply zebre_init.
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
