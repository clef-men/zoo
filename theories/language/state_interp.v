From iris.bi Require Import
  lib.fractional.
From iris.base_logic Require Export
  lib.gen_heap.
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
Implicit Types κ : list ().

Class ZebreGpre Σ := {
  #[global] zebre_Gpre_inv_Gpre :: invGpreS Σ ;
  #[local] zebre_Gpre_heap_Gpre :: gen_heapGpreS loc val Σ ;
}.

Definition zebre_Σ := #[
  invΣ ;
  gen_heapΣ loc val
].
#[global] Instance subG_zebre_Σ Σ :
  subG zebre_Σ Σ →
  ZebreGpre Σ.
Proof.
  solve_inG.
Qed.

Class ZebreG Σ := {
  zebre_G_inv_G : invGS Σ ;
  #[global] zebre_G_heap_G :: gen_heapGS loc val Σ ;
}.
#[global] Arguments Build_ZebreG _ {_ _} : assert.

Definition zebre_state_interp `{zebre_G : !ZebreG Σ} σ (_ : nat) κ (_ : nat) : iProp Σ :=
  gen_heap_interp σ.
#[global] Program Instance zebre_G_iris_G `{zebre_G : !ZebreG Σ} : irisGS zebre Σ := {
  iris_invGS :=
    zebre_G_inv_G ;
  state_interp :=
    zebre_state_interp ;
  fork_post _ :=
    True%I ;
  num_laters_per_step n :=
    n ;
}.
Next Obligation.
  intros. iSteps.
Qed.

Lemma zebre_init `{zebre_Gpre : !ZebreGpre Σ} `{inv_G : !invGS Σ} σ ns κ nt :
  ⊢ |==>
    ∃ zebre_G : ZebreG Σ,
    state_interp σ ns κ nt.
Proof.
  iMod (gen_heap_init σ) as (?) "(Hσ & _)".
  iExists (Build_ZebreG Σ). iFrame. iSteps.
Qed.

Notation "l ↦ dq v" := (
  pointsto (L := loc) (V := val) l dq v%V
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
