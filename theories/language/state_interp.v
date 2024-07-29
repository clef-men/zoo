From iris.bi Require Import
  lib.fractional.
From iris.base_logic Require Export
  lib.gen_heap.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.mono_map.
From zoo.iris.base_logic Require Export
  lib.prophet_map.
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
  #[local] zoo_Gpre_headers_G :: MonoMapG Σ location header ;
  #[local] zoo_Gpre_heap_Gpre :: gen_heapGpreS location val Σ ;
  #[local] zoo_Gpre_prophecy_Gpre :: ProphetMapGpre Σ prophet_id (val * val) ;
}.

Definition zoo_Σ := #[
  invΣ ;
  mono_map_Σ location header ;
  gen_heapΣ location val ;
  prophet_map_Σ prophet_id (val * val)
].
#[global] Instance subG_zoo_Σ Σ :
  subG zoo_Σ Σ →
  ZooGpre Σ.
Proof.
  solve_inG.
Qed.

Class ZooG Σ := {
  zoo_G_inv_G : invGS Σ ;
  #[local] zoo_G_headers_G :: MonoMapG Σ location header ;
  zoo_G_headers : gname ;
  #[global] zoo_G_heap_G :: gen_heapGS location val Σ ;
  #[global] zoo_G_prophecy_map_G :: ProphetMapG Σ prophet_id (val * val) ;
}.
#[global] Arguments Build_ZooG _ {_ _} _ {_ _} : assert.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition zoo_state_interp (_ : nat) σ κ : iProp Σ :=
    mono_map_auth zoo_G_headers (DfracOwn 1) σ.(state_headers) ∗
    gen_heap_interp σ.(state_heap) ∗
    prophet_map_interp κ σ.(state_prophets).
  #[global] Instance zoo_G_iris_G : IrisG zoo Σ := {
    iris_G_inv_G :=
      zoo_G_inv_G ;
    state_interp :=
      zoo_state_interp ;
    fork_post _ :=
      True%I ;
  }.

  Definition has_header l hdr :=
    mono_map_elem zoo_G_headers l hdr.
End zoo_G.

Notation "l ↦ₕ hdr" := (
  has_header l hdr
)(at level 20,
  format "l  ↦ₕ  hdr"
) : bi_scope.

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

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[global] Instance has_header_timeless l hdr :
    Timeless (l ↦ₕ hdr).
  Proof.
    apply _.
  Qed.
  #[global] Instance has_header_persistent l hdr :
    Persistent (l ↦ₕ hdr).
  Proof.
    apply _.
  Qed.
End zoo_G.

Lemma zoo_init `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} nt σ κ :
  ⊢ |==>
    ∃ zoo_G : ZooG Σ,
    state_interp nt σ κ.
Proof.
  iMod mono_map_alloc as (γ_headers) "Hheaders".
  iMod (gen_heap_init σ.(state_heap)) as (?) "(Hσ & _)".
  iMod (prophet_map_init κ σ.(state_prophets)) as "(% & Hκ)".
  iExists (Build_ZooG Σ γ_headers). iFrame. iSteps.
Qed.
Lemma zoo_init' `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} σ κ :
  ⊢ |==>
    ∃ zoo_G : ZooG Σ,
    state_interp 0 σ κ.
Proof.
  apply zoo_init.
Qed.

#[global] Opaque has_header.
