From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  array
  domain
  spmc_future.
From zoo_parabs Require Export
  base
  pool__code.
From zoo_parabs Require Import
  pool__types
  ws_hub_std.
From zoo Require Import
  options.

Implicit Types b not_killed : bool.
Implicit Types v t hub task pred : val.

#[local] Parameter pool_max_round_noyield_ : nat.
Axiom pool_max_round_noyield_eq :
  pool_max_round_noyield = #pool_max_round_noyield_.

#[local] Parameter pool_max_round_yield_ : nat.
Axiom pool_max_round_yield_eq :
  pool_max_round_yield = #pool_max_round_yield_.

Class SchedulerG Σ `{zoo_G : !ZooG Σ} := {
  #[local] pool_G_domain_G :: DomainG Σ ;
  #[local] pool_G_future_G :: SpmcFutureG Σ ;
  #[local] pool_G_ws_hub_G :: WsHubStdG Σ ;
}.

Definition pool_Σ := #[
  domain_Σ ;
  spmc_future_Σ ;
  ws_hub_std_Σ
].
#[global] Instance subG_pool_Σ Σ `{zoo_G : !ZooG Σ} :
  subG pool_Σ Σ →
  SchedulerG Σ.
Proof.
  solve_inG.
Qed.

Section pool_G.
  Context `{pool_G : SchedulerG Σ}.

  #[local] Definition pool_task hub task Ψ : iProp Σ :=
    ∀ i,
    ws_hub_std_owner hub i -∗
    WP task (hub, #i)%V {{ v,
      ws_hub_std_owner hub i ∗
      Ψ v
    }}.
  #[local] Definition pool_inv_inner hub : iProp Σ :=
    ∃ tasks,
    ws_hub_std_model hub tasks ∗
    [∗ mset] task ∈ tasks,
      pool_task hub task (λ _, True).
  #[local] Definition pool_inv hub : iProp Σ :=
    ws_hub_std_inv hub (nroot.@"hub") ∗
    inv (nroot.@"inv") (pool_inv_inner hub).

  Definition pool_model t : iProp Σ :=
    ∃ hub v_doms doms,
    ⌜t = (hub, v_doms)%V⌝ ∗
    pool_inv hub ∗
    ws_hub_std_owner hub 0 ∗
    array_model v_doms DfracDiscarded doms ∗
    [∗ list] dom ∈ doms,
      domain_model dom itype_unit.

  #[local] Definition pool_context' ctx (i : nat) : iProp Σ :=
    ∃ hub,
    ⌜ctx = (hub, #i)%V⌝ ∗
    pool_inv hub ∗
    ws_hub_std_owner hub i.
  Definition pool_context ctx : iProp Σ :=
    ∃ i,
    pool_context' ctx i.

  Definition pool_future :=
    spmc_future_inv.

  #[global] Instance pool_future_proper t :
    Proper ((pointwise_relation _ (≡)) ==> (≡)) (pool_future t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance pool_future_persistent fut Ψ :
    Persistent (pool_future fut Ψ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma pool_execute_spec hub i task Ψ :
    {{{
      ws_hub_std_owner hub i ∗
      pool_task hub task Ψ
    }}}
      pool_execute (hub, #i)%V task
    {{{ v,
      RET v;
      ws_hub_std_owner hub i ∗
      Ψ v
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma pool_worker_spec ctx :
    {{{
      pool_context ctx
    }}}
      pool_worker ctx
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (%i & %hub & -> & (#Hhub_inv & #Hinv) & Hhub_owner) HΦ".

    iLöb as "HLöb".

    wp_rec.
    rewrite pool_max_round_noyield_eq pool_max_round_yield_eq.

    awp_smart_apply (ws_hub_std_pop_steal_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; [done | lia.. |].
    iInv "Hinv" as "(%tasks & >Hhub_model & Htasks)".
    iAaccIntro with "Hhub_model"; first iSteps.
    iIntros ([task |]) "Hhub_model !>"; last iSteps.
    iDestruct "Hhub_model" as "(%tasks' & -> & Hhub_model)".
    iDestruct (big_sepMS_disj_union with "Htasks") as "(Htask & Htasks)".
    rewrite big_sepMS_singleton.
    iSplitR "Htask"; first iSteps.
    iIntros "Hhub_owner HΦ". clear- pool_G.

    wp_smart_apply (pool_execute_spec with "[$Hhub_owner $Htask]") as (res) "(Hhub_owner & _)".
    wp_smart_apply ("HLöb" with "Hhub_owner HΦ").
  Qed.

  Lemma pool_create_spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      pool_create #sz
    {{{ t,
      RET t;
      pool_model t
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_std_create_spec with "[//]") as (t) "(#Hhub_inv & Hhub_model & Hhub_owners)"; first lia.
    rewrite Z2Nat.inj_add // Nat.add_1_r.
    iDestruct "Hhub_owners" as "(Hhub_owner & Hhub_owners)".

    iMod (inv_alloc _ _ (pool_inv_inner t) with "[Hhub_model]") as "#Hinv".
    { iSteps. rewrite big_sepMS_empty //. }

    wp_smart_apply (array_unsafe_initi_spec_disentangled' (λ _ dom, domain_model dom itype_unit) with "[Hhub_owners]") as (v_doms doms) "(_ & Hv_doms & Hdoms)"; first done.
    { iApply (big_sepL_impl_strong with "Hhub_owners").
      { rewrite !length_seq. lia. }
      iIntros "!>" (k i1 i2 (-> & Hi1)%lookup_seq (-> & Hi2)%lookup_seq) "Hhub_owner".
      wp_smart_apply (domain_spawn_spec itype_unit with "[Hhub_owner]"); last iSteps. iIntros "%tid _".
      iApply wp_thread_id_mono.
      wp_smart_apply (pool_worker_spec with "[Hhub_owner]"); last iSteps.
      rewrite Z.add_1_r -Nat2Z.inj_succ. iExists _. iSteps.
    }
    iMod (array_model_persist with "Hv_doms") as "#Hv_doms".
    iSteps.
  Qed.

  Lemma pool_run_spec Ψ t task :
    {{{
      pool_model t ∗
      ( ∀ ctx,
        pool_context ctx -∗
        WP task ctx {{ v,
          pool_context ctx ∗
          Ψ v
        }}
      )
    }}}
      pool_run t task
    {{{ v,
      RET v;
      pool_model t ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((%hub & %v_doms & %doms & -> & (#Hhub_inv & #Hinv) & Hhub_owner & Hv_doms & Hdoms) & Htask) HΦ".

    wp_rec.
    wp_smart_apply (pool_execute_spec _ 0 _ Ψ with "[$Hhub_owner Htask]") as (v) "(Hhub_owner & HΨ)"; last iSteps. iIntros "%i Hhub_owner".
    wp_apply (wp_wand with "(Htask [Hhub_owner])"); last iSteps.
    iExists i. iSteps.
  Qed.

  Lemma pool_silent_async_spec ctx task :
    {{{
      pool_context ctx ∗
      ( ∀ ctx,
        pool_context ctx -∗
        WP task ctx {{ res,
          pool_context ctx
        }}
      )
    }}}
      pool_silent_async ctx task
    {{{
      RET ();
      pool_context ctx
    }}}.
  Proof.
    iIntros "%Φ ((%i & %hub & -> & (#Hhub_inv & #Hinv) & Hhub_owner) & Htask) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_push_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; first done.
    iInv "Hinv" as "(%tasks & >Hhub_model & Htasks)".
    iAaccIntro with "Hhub_model"; first iFrameSteps. iIntros "Hhub_model".
    iSplitL.
    { iExists _. iFrame. rewrite big_sepMS_singleton. iIntros "!> !> %j Hhub_owner".
      wp_smart_apply (wp_wand with "(Htask [Hhub_owner])"); last iSteps.
      iExists j. iSteps.
    }
    iIntros "!> Hhub_owner HΦ". clear.

    iApply "HΦ".
    iExists i. iSteps.
  Qed.

  Lemma pool_async_spec Ψ ctx task :
    {{{
      pool_context ctx ∗
      ( ∀ ctx,
        pool_context ctx -∗
        WP task ctx {{ v,
          pool_context ctx ∗
          □ Ψ v
        }}
      )
    }}}
      pool_async ctx task
    {{{ fut,
      RET fut;
      pool_context ctx ∗
      pool_future fut Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Htask) HΦ".

    wp_rec.
    wp_smart_apply (spmc_future_create_spec with "[//]") as (fut) "(#Hfut_inv & Hfut_producer)".
    wp_smart_apply (pool_silent_async_spec with "[$Hctx Htask Hfut_producer]") as "Hctx".
    { clear ctx. iIntros "%ctx Hctx".
      wp_smart_apply (wp_wand with "(Htask Hctx)") as (v) "(Hctx & HΨ)".
      wp_apply (spmc_future_set_spec with "[$Hfut_inv $Hfut_producer $HΨ]") as "_ //".
    }
    wp_pures.
    iApply ("HΦ" with "[$Hctx $Hfut_inv]").
  Qed.

  Lemma pool_wait_until_spec P ctx pred :
    {{{
      pool_context ctx ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    }}}
      pool_wait_until ctx pred
    {{{
      RET ();
      pool_context ctx ∗
      P
    }}}.
  Proof.
    iIntros "%Φ ((%i & %hub & -> & (#Hhub_inv & #Hinv) & Hhub_owner) & #Hpred) HΦ".

    iLöb as "HLöb".

    wp_rec.
    rewrite pool_max_round_noyield_eq.
    wp_smart_apply (wp_wand with "Hpred") as (res) "(%b & -> & HP)".
    destruct b.

    - wp_pures.
      iApply ("HΦ" with "[Hhub_owner $HP]").
      iExists i. iSteps.

    - awp_smart_apply (ws_hub_std_pop_steal_until_spec P with "[$Hhub_inv $Hhub_owner $Hpred]") without "HΦ"; [lia.. |].
      iInv "Hinv" as "(%tasks & >Hhub_model & Htasks)".
      iAaccIntro with "Hhub_model"; first iSteps. iIntros ([task |]) "Hhub_model !>".

      + iDestruct "Hhub_model" as "(%tasks' & -> & Hhub_model)".
        iDestruct (big_sepMS_insert with "Htasks") as "(Htask & Htasks')".
        iSplitR "Htask"; first iSteps.
        iIntros "(Hhub_owner & _) HΦ". clear- pool_G.

        wp_smart_apply (pool_execute_spec with "[$Hhub_owner $Htask]") as (res) "(Hhub_owner & _)".
        wp_smart_apply ("HLöb" with "Hhub_owner HΦ").

      + iSplitL; first iSteps.
        iIntros "(Hhub_owner & HP) HΦ". clear.

        wp_pures.
        iApply ("HΦ" with "[Hhub_owner $HP]").
        iExists i. iSteps.
  Qed.

  Lemma pool_wait_while_spec P ctx pred :
    {{{
      pool_context ctx ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then True else P
      }}
    }}}
      pool_wait_while ctx pred
    {{{
      RET ();
      pool_context ctx ∗
      P
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hpred) HΦ".

    wp_rec.
    wp_smart_apply (pool_wait_until_spec with "[$Hctx] HΦ"). iModIntro.
    wp_smart_apply (wp_wand with "Hpred") as (res) "(%b & -> & HP)".
    destruct b; iSteps.
  Qed.

  Lemma pool_await_spec ctx fut Ψ :
    {{{
      pool_context ctx ∗
      pool_future fut Ψ
    }}}
      pool_await ctx fut
    {{{ v,
      RET v;
      pool_context ctx ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hfut_inv) HΦ".

    wp_rec.
    wp_smart_apply (pool_wait_until_spec (∃ v, spmc_future_result fut v)%I with "[$Hctx]") as "(Hctx & %v & #Hfut_result)".
    { iModIntro.
      wp_smart_apply (spmc_future_is_set_spec with "Hfut_inv") as (b) "HΨ".
      destruct b; iSteps.
    }
    wp_smart_apply (spmc_future_get_spec_result with "[$Hfut_inv $Hfut_result]") as "HΨ".
    iApply ("HΦ" with "[$Hctx $HΨ]").
  Qed.

  Lemma pool_kill_spec t :
    {{{
      pool_model t
    }}}
      pool_kill t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (%hub & %v_doms & %doms & -> & (#Hhub_inv & #Hinv) & Hhub_owner & Hv_doms & Hdoms) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_std_kill_spec with "Hhub_inv") as "_".
    wp_smart_apply (array_iter_spec_disentangled' (λ _ _, True)%I with "[$Hv_doms Hdoms]"); last iSteps.
    iApply (big_sepL_impl with "Hdoms"). iIntros "!> %i %dom _ Hdom".
    wp_apply (domain_join_spec with "Hdom").
    iSteps.
  Qed.
End pool_G.

#[global] Opaque pool_create.
#[global] Opaque pool_run.
#[global] Opaque pool_silent_async.
#[global] Opaque pool_async.
#[global] Opaque pool_wait_until.
#[global] Opaque pool_wait_while.
#[global] Opaque pool_await.
#[global] Opaque pool_kill.

#[global] Opaque pool_model.
#[global] Opaque pool_context.
#[global] Opaque pool_future.
