From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.fupd
  lib.saved_prop.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  ivar_4.
From zoo_parabs Require Import
  pool
  vertex.
From examples Require Export
  vertex_simple__code.
From zoo Require Import
  options.

Implicit Types v ctx a b c d : val.

Class VertexSimpleG Σ `{zoo_G : !ZooG Σ} :=
  { #[local] vertex_simple_G_pool_G :: PoolG Σ
  ; #[local] vertex_simple_G_vertex_G :: VertexG Σ
  ; #[local] vertex_simple_G_ivar_G :: Ivar4G Σ
  ; #[local] vertex_simple_G_saved_prop_G :: SavedPropG Σ
  }.

Definition vertex_simple_Σ := #[
  pool_Σ ;
  vertex_Σ ;
  ivar_4_Σ ;
  saved_prop_Σ
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

  Lemma vertex_simple_main𑁒spec P_ab P_ac P_b P_c P_d (num_dom : nat) a b c d :
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

    wp_apply+ (ivar_4_create𑁒spec
      (λ _, P_d)
      (λ _, True)%I
      (λ _ (_ : unit), True)%I
    with "[//]") as (ivar) "(#Hivar_inv & Hivar_producer & Hivar_consumer)".

    wp_apply+ (vertex_create'𑁒spec
      (P_ab ∗ P_ac)
      True
    with "[//]") as (vtx_a iter_a) "(#Hvtx_a_inv & Hvtx_a_model & Hvtx_a_output)".
    iMod (vertex_output_split with "Hvtx_a_inv Hvtx_a_output") as "(Hvtx_a_output_b & Hvtx_a_output_c)".
    wp_apply+ (vertex_create'𑁒spec
      P_b
      True
    with "[//]") as (vtx_b iter_b) "(#Hvtx_b_inv & Hvtx_b_model & Hvtx_b_output)".
    wp_apply+ (vertex_create'𑁒spec
      P_c
      True
    with "[//]") as (vtx_c iter_c) "(#Hvtx_c_inv & Hvtx_c_model & Hvtx_c_output)".
    wp_apply+ (vertex_create'𑁒spec
      True
      True
    with "[//]") as (vtx_d iter_d) "(#Hvtx_d_inv & Hvtx_d_model & _)".

    wp_apply+ (vertex_precede𑁒spec with "[$Hvtx_b_model]") as "(Hvtx_b_model & #Hvtx_a_predecessor_b)". 1: iFrame "#".
    wp_apply+ (vertex_precede𑁒spec with "[$Hvtx_c_model]") as "(Hvtx_c_model & #Hvtx_a_predecessor_c)". 1: iFrame "#".
    wp_apply+ (vertex_precede𑁒spec with "[$Hvtx_d_model]") as "(Hvtx_d_model & #Hvtx_b_predecessor)". 1: iFrame "#".
    wp_apply+ (vertex_precede𑁒spec with "[$Hvtx_d_model]") as "(Hvtx_d_model & #Hvtx_c_predecessor)". 1: iFrame "#".

    wp_apply+ (pool_run𑁒spec (λ pool res,
      ⌜res = ()%V⌝ ∗
      P_d
    )%I with "[- HΦ]") as (pool ?) "(_ & -> & HP_d)". 1: lia.
    { iIntros "%pool %ctx %scope _ Hctx".

      wp_apply+ (vertex_release𑁒spec' with "[$Hctx $Hvtx_d_model Hvtx_b_output Hvtx_c_output Hd Hivar_producer]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx #Hvtx_d_ready".

        wp_pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

        iDestruct (vertex_predecessor_finished with "Hvtx_b_predecessor Hvtx_d_ready") as "#Hvtx_b_finished".
        iMod (vertex_inv_finished_output with "Hvtx_b_inv Hvtx_b_finished Hvtx_b_output") as "HP_b".

        iDestruct (vertex_predecessor_finished with "Hvtx_c_predecessor Hvtx_d_ready") as "#Hvtx_c_finished".
        iMod (vertex_inv_finished_output with "Hvtx_c_inv Hvtx_c_finished Hvtx_c_output") as "HP_c".

        iMod (lc_fupd_elim_laterN _ (P_b ∗ P_c) with "H£ [$]") as "(HP_b & HP_c)".
        wp_apply (wp_wand with "(Hd HP_b HP_c)") as (res) "(-> & HP_d)".

        wp_apply+ (ivar_4_notify𑁒spec () with "[$Hivar_inv $Hivar_producer $HP_d]"). 1: iSteps.
        iSteps.
      }

      wp_apply+ (vertex_release𑁒spec' with "[$Hctx $Hvtx_c_model Hvtx_a_output_c Hc]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx #Hvtx_c_ready".

        wp_pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

        iDestruct (vertex_predecessor_finished with "Hvtx_a_predecessor_c Hvtx_c_ready") as "#Hvtx_a_finished".
        iMod (vertex_inv_finished_output' with "H£ Hvtx_a_inv Hvtx_a_finished Hvtx_a_output_c") as "HP_ac".

        wp_apply (wp_wand with "(Hc HP_ac)") as (res) "(-> & $)".
        iSteps => //.
      }

      wp_apply+ (vertex_release𑁒spec' with "[$Hctx $Hvtx_b_model Hvtx_a_output_b Hb]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx #Hvtx_b_ready".

        wp_pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

        iDestruct (vertex_predecessor_finished with "Hvtx_a_predecessor_b Hvtx_b_ready") as "#Hvtx_a_finished".
        iMod (vertex_inv_finished_output' with "H£ Hvtx_a_inv Hvtx_a_finished Hvtx_a_output_b") as "HP_ab".

        wp_apply (wp_wand with "(Hb HP_ab)") as (res) "(-> & $)".
        iSteps => //.
      }

      wp_apply+ (vertex_release𑁒spec' with "[$Hctx $Hvtx_a_model Ha]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx Hvtx_a_ready".

        wp_apply+ (wp_wand with "Ha") as (res) "(-> & $)".
        iSteps => //.
      }

      iApply wp_fupd.
      wp_apply+ (pool_wait_ivar𑁒spec with "[$Hctx $Hivar_inv]") as "(H£ & $ & (%v & #Hivar_result))". 1: iSteps.
      iMod (ivar_4_inv_result_consumer' with "H£ Hivar_inv Hivar_result Hivar_consumer") as "($ & _)" => //.
    }

    iSteps.
  Qed.
End vertex_simple_G.

From examples Require
  vertex_simple__opaque.
