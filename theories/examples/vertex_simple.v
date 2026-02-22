From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.fupd.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  mpsc_flag.
From zoo_parabs Require Import
  pool
  vertex.
From examples Require Export
  vertex_simple__code.
From zoo Require Import
  options.

Implicit Types a b c d : val.

Class VertexSimpleG Σ `{zoo_G : !ZooG Σ} := {
  #[local] vertex_simple_G_pool_G :: PoolG Σ ;
  #[local] vertex_simple_G_vertex_G :: VertexG Σ ;
  #[local] vertex_simple_G_mpsc_flag_G :: MpscFlagG Σ ;
}.

Definition vertex_simple_Σ := #[
  pool_Σ ;
  vertex_Σ ;
  mpsc_flag_Σ
].
#[global] Instance subG_vertex_simple_Σ Σ `{zoo_G : !ZooG Σ} :
  subG vertex_simple_Σ Σ →
  VertexSimpleG Σ.
Proof.
  base.solve_inG.
Qed.

Section vertex_simple_G.
  Context `{vertex_simple_G : VertexSimpleG Σ}.

  Implicit Types P_ab P_ac P_b P_c P_d : iProp Σ.

  Lemma vertex_simple_main_spec P_ab P_ac P_b P_c P_d (num_dom : nat) a b c d :
    {{{
      WP a () {{ res, ⌜res = ()%V⌝ ∗ P_ab ∗ P_ac }} ∗
      (P_ab -∗ WP b () {{ res, ⌜res = ()%V⌝ ∗ P_b }}) ∗
      (P_ac -∗ WP c () {{ res, ⌜res = ()%V⌝ ∗ P_c }}) ∗
      (P_b -∗ P_c -∗ WP d () {{ res, ⌜res = ()%V⌝ ∗ P_d }})
    }}}
      vertex_simple_main #num_dom a b c d
    {{{
      RET ();
      P_d
    }}}.
  Proof.
    iIntros "%Φ (Ha & Hb & Hc & Hd) HΦ".

    wp_rec.
    wp_smart_apply (mpsc_flag_create_spec P_d with "[//]") as (flag) "(#Hflag_inv & Hflag_consumer)".

    wp_smart_apply (vertex_create_spec
      (P_ab ∗ P_ac)
      True
      (Some _)
    with "[//]") as (vtx_a iter_a) "(#Hvtx_a_inv & Hvtx_a_model & Hvtx_a_output)".
    iMod (vertex_output_split with "Hvtx_a_inv Hvtx_a_output") as "(Hvtx_a_output_b & Hvtx_a_output_c)".
    wp_smart_apply (vertex_create_spec
      P_b
      True
      (Some _)
    with "[//]") as (vtx_b iter_b) "(#Hvtx_b_inv & Hvtx_b_model & Hvtx_b_output)".
    wp_smart_apply (vertex_create_spec
      P_c
      True
      (Some _)
    with "[//]") as (vtx_c iter_c) "(#Hvtx_c_inv & Hvtx_c_model & Hvtx_c_output)".
    wp_smart_apply (vertex_create_spec
      True
      True
      (Some _)
    with "[//]") as (vtx_d iter_d) "(#Hvtx_d_inv & Hvtx_d_model & _)".

    wp_smart_apply (vertex_precede_spec with "[$Hvtx_b_model]") as "(Hvtx_b_model & #Hvtx_a_predecessor_b)". 1: iFrame "#".
    wp_smart_apply (vertex_precede_spec with "[$Hvtx_c_model]") as "(Hvtx_c_model & #Hvtx_a_predecessor_c)". 1: iFrame "#".
    wp_smart_apply (vertex_precede_spec with "[$Hvtx_d_model]") as "(Hvtx_d_model & #Hvtx_b_predecessor)". 1: iFrame "#".
    wp_smart_apply (vertex_precede_spec with "[$Hvtx_d_model]") as "(Hvtx_d_model & #Hvtx_c_predecessor)". 1: iFrame "#".

    wp_smart_apply (pool_create_spec with "[//]") as (pool) "(_ & Hpool_model)". 1: lia.

    wp_smart_apply (pool_run_spec (λ _,
      P_d
    )%I with "[- HΦ $Hpool_model]") as (?) "(Hpool_model & HP_d)".
    { iIntros "%ctx %scope Hctx".

      wp_smart_apply (vertex_release_spec with "[$Hctx $Hvtx_d_model Hvtx_b_output Hvtx_c_output Hd]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope %iter_d' Hctx Hvtx_d_ready Hvtx_d_model".
        wp_pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.
        iDestruct (vertex_predecessor_finished with "Hvtx_b_predecessor Hvtx_d_ready") as "#Hvtx_b_finished".
        iMod (vertex_inv_finished_output with "Hvtx_b_inv Hvtx_b_finished Hvtx_b_output") as "HP_b".
        iDestruct (vertex_predecessor_finished with "Hvtx_c_predecessor Hvtx_d_ready") as "#Hvtx_c_finished".
        iMod (vertex_inv_finished_output with "Hvtx_c_inv Hvtx_c_finished Hvtx_c_output") as "HP_c".
        iMod (lc_fupd_elim_laterN _ (P_b ∗ P_c) with "H£ [$]") as "(HP_b & HP_c)".
        wp_apply (wp_wand with "(Hd HP_b HP_c)") as (res) "(-> & HP_d)".
        wp_smart_apply (mpsc_flag_set_spec with "[$Hflag_inv $HP_d]").
        iSteps => //.
      }

      wp_smart_apply (vertex_release_spec with "[$Hctx $Hvtx_c_model Hvtx_a_output_c Hc]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope %iter_c' Hctx Hvtx_c_ready Hvtx_c_model".
        wp_pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.
        iDestruct (vertex_predecessor_finished with "Hvtx_a_predecessor_c Hvtx_c_ready") as "#Hvtx_a_finished".
        iMod (vertex_inv_finished_output' with "H£ Hvtx_a_inv Hvtx_a_finished Hvtx_a_output_c") as "HP_ac".
        wp_apply (wp_wand with "(Hc HP_ac)") as (res) "(-> & $)".
        iSteps => //.
      }

      wp_smart_apply (vertex_release_spec with "[$Hctx $Hvtx_b_model Hvtx_a_output_b Hb]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope %iter_b' Hctx Hvtx_b_ready Hvtx_b_model".
        wp_pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.
        iDestruct (vertex_predecessor_finished with "Hvtx_a_predecessor_b Hvtx_b_ready") as "#Hvtx_a_finished".
        iMod (vertex_inv_finished_output' with "H£ Hvtx_a_inv Hvtx_a_finished Hvtx_a_output_b") as "HP_ab".
        wp_apply (wp_wand with "(Hb HP_ab)") as (res) "(-> & $)".
        iSteps => //.
      }

      wp_smart_apply (vertex_release_spec with "[$Hctx $Hvtx_a_model Ha]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope %iter_a' Hctx Hvtx_a_ready Hvtx_a_model".
        wp_smart_apply (wp_wand with "Ha") as (res) "(-> & $)".
        iSteps => //.
      }

      wp_smart_apply (pool_wait_until_spec
        (mpsc_flag_consumer flag)
        P_d
      with "[$Hctx Hflag_consumer]").
      { iStep 3 as "Hflag_consumer".
        wp_smart_apply (mpsc_flag_get_spec with "[$Hflag_inv $Hflag_consumer]").
        iSteps.
      }

      iSteps.
    }

    wp_smart_apply (pool_kill_spec with "[$Hpool_model]").
    iSteps.
  Qed.
End vertex_simple_G.

From examples Require
  vertex_simple__opaque.
