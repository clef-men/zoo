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
  fibonacci
  vertex_fibonacci__code.
From zoo Require Import
  options.

Implicit Types r : location.
Implicit Types ctx vtx : val.

Class VertexFibonacciG Σ `{zoo_G : !ZooG Σ} := {
  #[local] vertex_fibonacci_G_pool_G :: PoolG Σ ;
  #[local] vertex_fibonacci_G_vertex_G :: VertexG Σ ;
  #[local] vertex_fibonacci_G_mpsc_flag_G :: MpscFlagG Σ ;
}.

Definition vertex_fibonacci_Σ := #[
  pool_Σ ;
  vertex_Σ ;
  mpsc_flag_Σ
].
#[global] Instance subG_vertex_fibonacci_Σ Σ `{zoo_G : !ZooG Σ} :
  subG vertex_fibonacci_Σ Σ →
  VertexFibonacciG Σ.
Proof.
  base.solve_inG.
Qed.

Section vertex_fibonacci_G.
  Context `{vertex_fibonacci_G : VertexFibonacciG Σ}.

  #[local] Lemma vertex_fibonacci_main_0_spec vtx iter r n :
    vertex_inv vtx (r ↦ᵣ #(fibonacci n)) True -∗
    r ↦ᵣ 0 -∗
    vertex_wp
      vtx
      (r ↦ᵣ #(fibonacci n))
      True
      (fun: "ctx" => vertex_fibonacci_main_0 "ctx" vtx #r #n)
      iter.
  Proof.
    iLöb as "HLöb" forall (vtx iter r n).

    iEval (setoid_rewrite vertex_wp_unfold).
    iIntros "#Hvtx_inv Hr %pool %ctx %scope %iter' Hctx _ Hvtx_model".

    wp_pures. wp_rec. wp_pures.
    case_bool_decide as Hif; wp_pures.

    - iSteps. iPureIntro.
      rewrite fibonacci_base //. 1: lia.

    - wp_ref r1 as "Hr1".
      wp_smart_apply (vertex_create_spec
        (r1 ↦ᵣ #(fibonacci (n - 1)))
        True
        None
      with "[//]") as (vtx1 iter1) "(#Hvtx1_inv & Hvtx1_model & Hvtx1_output)".
      wp_smart_apply (vertex_set_task_spec with "Hvtx1_model") as "Hvtx1_model".
      wp_smart_apply (vertex_release_spec with "[$Hctx $Hvtx1_model Hr1]") as "Hctx".
      { iFrame "#".
        iEval (replace (n - 1)%Z with ⁺(n - 1) by lia).
        iApply ("HLöb" with "Hvtx1_inv Hr1").
      }

      wp_ref r2 as "Hr2".
      wp_smart_apply (vertex_create_spec
        (r2 ↦ᵣ #(fibonacci (n - 2)))
        True
        None
      with "[//]") as (vtx2 iter2) "(#Hvtx2_inv & Hvtx2_model & Hvtx2_output)".
      wp_smart_apply (vertex_set_task_spec with "Hvtx2_model") as "Hvtx2_model".
      wp_smart_apply (vertex_release_spec with "[$Hctx $Hvtx2_model Hr2]") as "Hctx".
      { iFrame "#".
        iEval (replace (n - 2)%Z with ⁺(n - 2) by lia).
        iApply ("HLöb" with "Hvtx2_inv Hr2").
      }

      wp_smart_apply (vertex_precede_spec with "[$Hvtx_model]") as "(Hvtx_model & #Hvtx1_predecessor)". 1: iFrame "#".
      wp_smart_apply (vertex_precede_spec with "[$Hvtx_model]") as "(Hvtx_model & #Hvtx2_predecessor)". 1: iFrame "#".
      wp_smart_apply (vertex_yield_spec with "[$Hvtx_model]") as "Hvtx_model".
      iStep 4.

      iEval (rewrite vertex_wp_unfold).
      iIntros "{%- Hif} %pool %ctx %scope %iter'' Hctx #Hvtx_ready Hvtx_model".

      wp_pures credits:"H£".
      iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

      iDestruct (vertex_predecessor_finished with "Hvtx1_predecessor Hvtx_ready") as "#Hvtx1_finished".
      iMod (vertex_inv_finished_output with "Hvtx1_inv Hvtx1_finished Hvtx1_output") as "Hr1".

      iDestruct (vertex_predecessor_finished with "Hvtx2_predecessor Hvtx_ready") as "#Hvtx2_finished".
      iMod (vertex_inv_finished_output with "Hvtx2_inv Hvtx2_finished Hvtx2_output") as "Hr2".

      iMod (lc_fupd_elim_laterN _ (_ ∗ _) with "H£ [Hr1 Hr2]") as "(Hr1 & Hr2)".
      { iNext. iAccu. }

      iSteps. iPureIntro.
      rewrite (fibonacci_recursive n). 1: lia.
      rewrite -Nat2Z.inj_add //.
  Qed.

  Lemma vertex_fibonacci_main_spec (num_dom n : nat) :
    {{{
      True
    }}}
      vertex_fibonacci_main #num_dom #n
    {{{
      RET #(fibonacci n);
      True
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_smart_apply (pool_create_spec with "[//]") as (pool) "(_ & Hpool_model)". 1: lia.

    wp_smart_apply (pool_run_spec (λ v,
      ⌜v = #_⌝
    )%I with "[$Hpool_model]") as (?) "(Hpool_model & ->)".
    { iIntros "%ctx %scope Hctx".

      wp_ref r as "Hr".
      wp_smart_apply (vertex_create_spec
        (r ↦ᵣ #(fibonacci n))
        True
        None
      with "[//]") as (vtx1 iter) "(#Hvtx1_inv & Hvtx1_model & Hvtx1_output)".
      wp_smart_apply (vertex_set_task_spec with "Hvtx1_model") as "Hvtx1_model".
      wp_smart_apply (vertex_release_spec with "[$Hctx $Hvtx1_inv $Hvtx1_model Hr]") as "Hctx".
      { iApply (vertex_fibonacci_main_0_spec with "Hvtx1_inv Hr"). }

      wp_smart_apply (mpsc_flag_create_spec
        (r ↦ᵣ #(fibonacci n))
      with "[//]") as (flag) "(#Hflag_inv & Hflag_consumer)".

      wp_smart_apply (vertex_create'_spec
        True
        True
      with "[//]") as (vtx2 iter2) "(#Hvtx2_inv & Hvtx2_model & _)".
      wp_smart_apply (vertex_precede_spec with "[$Hvtx2_model]") as "(Hvtx2_model & #Hvtx1_predecessor)". 1: iFrame "#".
      wp_smart_apply (vertex_release_spec' with "[$Hctx $Hvtx2_model Hvtx1_output]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx #Hvtx2_ready".

        wp_pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

        iDestruct (vertex_predecessor_finished with "Hvtx1_predecessor Hvtx2_ready") as "#Hvtx1_finished".
        iMod (vertex_inv_finished_output' with "H£ Hvtx1_inv Hvtx1_finished Hvtx1_output") as "Hr".

        wp_smart_apply (mpsc_flag_set_spec with "[$Hflag_inv $Hr]").
        iSteps.
      }

      wp_smart_apply (pool_wait_until_spec
        (mpsc_flag_consumer flag)
        (r ↦ᵣ #(fibonacci n))
      with "[$Hctx Hflag_consumer]").
      { iStep 3 as "Hflag_consumer".
        wp_smart_apply (mpsc_flag_get_spec with "[$Hflag_inv $Hflag_consumer]").
        iSteps.
      }

      iSteps.
    }

    wp_smart_apply (pool_kill_spec with "Hpool_model").
    iSteps.
  Qed.
End vertex_fibonacci_G.

From examples Require
  vertex_fibonacci__opaque.
