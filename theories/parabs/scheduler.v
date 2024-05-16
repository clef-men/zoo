From zebre Require Import
  prelude.
From zebre.iris.bi Require Import
big_op.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  array
  domain
  spmc_future.
From zebre.parabs Require Export
  base.
From zebre.parabs Require Import
  ws_hub.
From zebre Require Import
  options.

Implicit Types not_killed : bool.
Implicit Types v t hub task : val.

#[local] Notation "'hub'" := (
  in_type "t" 0
)(in custom zebre_proj
).
#[local] Notation "'domains'" := (
  in_type "t" 1
)(in custom zebre_proj
).

#[local] Notation "'context_hub'" := (
  in_type "context" 0
)(in custom zebre_proj
).
#[local] Notation "'context_id'" := (
  in_type "context" 1
)(in custom zebre_proj
).

Section ws_deques.
  Context `{zebre_G : !ZebreG Σ}.
  Context (ws_hub : ws_hub Σ).

  #[local] Parameter scheduler_max_round_noyield : nat.
  #[local] Parameter scheduler_max_round_yield : nat.
  #[local] Definition scheduler_max_round : val :=
    (#scheduler_max_round_noyield, #scheduler_max_round_yield).

  #[local] Definition scheduler_execute : val :=
    λ: "ctx" "task",
      "task" "ctx".

  #[local] Definition scheduler_worker : val :=
    rec: "scheduler_worker" "ctx" :=
      match: ws_hub_pop_steal ws_hub "ctx".<context_hub> "ctx".<context_id> scheduler_max_round with
      | None =>
          ()
      | Some "task" =>
          scheduler_execute "ctx" "task" ;;
          "scheduler_worker" "ctx"
      end.

  Definition scheduler_create : val :=
    λ: "sz",
      let: "hub" := ws_hub.(ws_hub_create) (#1 + "sz") in
      let: "doms" := array_initi "sz" (λ: "i",
        domain_spawn (λ: <>, scheduler_worker ("hub", #1 + "i"))
      ) in
      ("hub", "doms").

  #[using="ws_hub"]
  Definition scheduler_run : val :=
    λ: "t" "task",
      scheduler_execute ("t".<hub>, #0) "task".

  Definition scheduler_silent_async : val :=
    λ: "ctx" "task",
      ws_hub.(ws_hub_push) "ctx".<context_hub> "ctx".<context_id> "task".

  Definition scheduler_async : val :=
    λ: "ctx" "task",
      let: "fut" := spmc_future_create () in
      scheduler_silent_async "ctx" (λ: "ctx",
        spmc_future_set "fut" ("task" "ctx")
      ) ;;
      "fut".

  Definition scheduler_await : val :=
    rec: "scheduler_await" "ctx" "fut" :=
      match: spmc_future_try_get "fut" with
      | Some "res" =>
          "res"
      | None =>
          match: ws_hub_pop_try_steal ws_hub "ctx".<context_hub> "ctx".<context_id> scheduler_max_round with
          | None =>
              Yield
          | Some "task" =>
              scheduler_execute "ctx" "task"
          end ;;
          "scheduler_await" "ctx" "fut"
      end.

  Definition scheduler_kill : val :=
    λ: "t",
      ws_hub.(ws_hub_kill) "t".<hub> ;;
      array_iter "t".<domains> domain_join.
End ws_deques.

Class SchedulerG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] scheduler_G_domain_G :: DomainG Σ ;
  #[local] scheduler_G_future_G :: SpmcFutureG Σ ;
}.

Definition scheduler_Σ := #[
  domain_Σ ;
  spmc_future_Σ
].
#[global] Instance subG_scheduler_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG scheduler_Σ Σ →
  SchedulerG Σ.
Proof.
  solve_inG.
Qed.

Section scheduler_G.
  Context `{scheduler_G : SchedulerG Σ}.
  Context (ws_hub : ws_hub Σ).

  #[local] Definition scheduler_task hub task Ψ : iProp Σ :=
    ∀ i,
    ws_hub.(ws_hub_owner) hub i -∗
    WP task (hub, #i)%V {{ v,
      ws_hub.(ws_hub_owner) hub i ∗
      Ψ v
    }}.
  #[local] Definition scheduler_inv_inner hub : iProp Σ :=
    ∃ tasks,
    ws_hub.(ws_hub_model) hub tasks ∗
    [∗ mset] task ∈ tasks,
      scheduler_task hub task (λ _, True).
  #[local] Definition scheduler_inv hub : iProp Σ :=
    ws_hub.(ws_hub_inv) hub (nroot.@"hub") ∗
    inv (nroot.@"inv") (scheduler_inv_inner hub).

  Definition scheduler_model t : iProp Σ :=
    ∃ hub v_doms doms,
    ⌜t = (hub, v_doms)%V⌝ ∗
    scheduler_inv hub ∗
    ws_hub.(ws_hub_owner) hub 0 ∗
    array_model v_doms DfracDiscarded doms ∗
    [∗ list] dom ∈ doms,
      domain_model dom (λ res, ⌜res = ()%V⌝).

  #[local] Definition scheduler_context' ctx (i : nat) : iProp Σ :=
    ∃ hub,
    ⌜ctx = (hub, #i)%V⌝ ∗
    scheduler_inv hub ∗
    ws_hub.(ws_hub_owner) hub i.
  Definition scheduler_context ctx : iProp Σ :=
    ∃ i,
    scheduler_context' ctx i.

  #[using="ws_hub"]
  Definition scheduler_future :=
    spmc_future_inv.

  #[global] Instance scheduler_future_proper t :
    Proper ((pointwise_relation _ (≡)) ==> (≡)) (scheduler_future t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance scheduler_future_persistent fut Ψ :
    Persistent (scheduler_future fut Ψ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma scheduler_execute_spec hub i task Ψ :
    {{{
      ws_hub.(ws_hub_owner) hub i ∗
      scheduler_task hub task Ψ
    }}}
      scheduler_execute (hub, #i)%V task
    {{{ v,
      RET v;
      ws_hub.(ws_hub_owner) hub i ∗
      Ψ v
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma scheduler_worker_spec ctx :
    {{{
      scheduler_context ctx
    }}}
      scheduler_worker ws_hub ctx
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (%i & %hub & -> & (#Hhub_inv & #Hinv) & Hhub_owner) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_smart_apply (ws_hub_pop_steal_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; [done | lia.. |].
    iInv "Hinv" as "(%tasks & >Hhub_model & Htasks)".
    iAaccIntro with "Hhub_model"; first iSteps.
    iIntros ([task |]) "Hhub_model !>"; last iSteps.
    iDestruct "Hhub_model" as "(%tasks' & -> & Hhub_model)".
    iDestruct (big_sepMS_disj_union with "Htasks") as "(Htask & Htasks)".
    rewrite big_sepMS_singleton.
    iSplitR "Htask"; first iSteps.
    iIntros "Hhub_owner HΦ". clear- scheduler_G.

    wp_smart_apply (scheduler_execute_spec with "[$Hhub_owner $Htask]") as (res) "(Hhub_owner & _)".
    wp_smart_apply ("HLöb" with "Hhub_owner HΦ").
  Qed.

  Lemma scheduler_create_spec sz :
    (0 ≤ sz)%Z →
    {{{ True }}}
      scheduler_create ws_hub #sz
    {{{ t,
      RET t;
      scheduler_model t
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_create_spec with "[//]") as (t) "(#Hhub_inv & Hhub_model & Hhub_owners)"; first lia.
    rewrite Z2Nat.inj_add //.
    iDestruct "Hhub_owners" as "(Hhub_owner & Hhub_owners)".

    iMod (inv_alloc _ _ (scheduler_inv_inner t) with "[Hhub_model]") as "#Hinv".
    { iSteps. rewrite big_sepMS_empty //. }

    pose Ψ res : iProp Σ := (
      ⌜res = ()%V⌝
    )%I.
    wp_smart_apply (array_initi_spec_disentangled' (λ _ dom, domain_model dom Ψ) with "[Hhub_owners]") as (v_doms doms) "(_ & Hv_doms & Hdoms)"; first done.
    { iApply (big_sepL_mono_strong with "Hhub_owners").
      { rewrite !seq_length. lia. }
      iIntros "!>" (k i1 i2 ((-> & Hi1)%lookup_seq & (-> & Hi2)%lookup_seq)) "Hhub_owner".
      wp_smart_apply (domain_spawn_spec Ψ with "[Hhub_owner]"); last iSteps.
      wp_smart_apply (scheduler_worker_spec with "[Hhub_owner]"); last iSteps.
      rewrite Z.add_1_l -Nat2Z.inj_succ. iExists _. iSteps.
    }
    iMod (array_model_persist with "Hv_doms") as "#Hv_doms".
    iSteps.
  Qed.

  Lemma scheduler_run_spec Ψ t task :
    {{{
      scheduler_model t ∗
      ( ∀ ctx,
        scheduler_context ctx -∗
        WP task ctx {{ v,
          scheduler_context ctx ∗
          Ψ v
        }}
      )
    }}}
      scheduler_run ws_hub t task
    {{{ v,
      RET v;
      scheduler_model t ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((%hub & %v_doms & %doms & -> & (#Hhub_inv & #Hinv) & Hhub_owner & Hv_doms & Hdoms) & Htask) HΦ".

    wp_rec.
    wp_smart_apply (scheduler_execute_spec _ 0 _ Ψ with "[$Hhub_owner Htask]") as (v) "(Hhub_owner & HΨ)"; last iSteps. iIntros "%i Hhub_owner".
    wp_apply (wp_wand with "(Htask [Hhub_owner])"); last iSteps.
    iExists i. iSteps.
  Qed.

  Lemma scheduler_silent_async_spec ctx task :
    {{{
      scheduler_context ctx ∗
      ( ∀ ctx,
        scheduler_context ctx -∗
        WP task ctx {{ res,
          scheduler_context ctx
        }}
      )
    }}}
      scheduler_silent_async ws_hub ctx task
    {{{
      RET ();
      scheduler_context ctx
    }}}.
  Proof.
    iIntros "%Φ ((%i & %hub & -> & (#Hhub_inv & #Hinv) & Hhub_owner) & Htask) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_push_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; first done.
    iInv "Hinv" as "(%tasks & >Hhub_model & Htasks)".
    iAaccIntro with "Hhub_model". { iFrame. iSteps. } iIntros "Hhub_model".
    iSplitL.
    { iExists _. iFrame. rewrite big_sepMS_singleton. iIntros "!> !> %j Hhub_owner".
      wp_smart_apply (wp_wand with "(Htask [Hhub_owner])"); last iSteps.
      iExists j. iSteps.
    }
    iIntros "!> Hhub_owner HΦ". clear.

    iApply "HΦ".
    iExists i. iSteps.
  Qed.

  Lemma scheduler_async_spec Ψ ctx task :
    {{{
      scheduler_context ctx ∗
      ( ∀ ctx,
        scheduler_context ctx -∗
        WP task ctx {{ v,
          scheduler_context ctx ∗
          □ Ψ v
        }}
      )
    }}}
      scheduler_async ws_hub ctx task
    {{{ fut,
      RET fut;
      scheduler_context ctx ∗
      scheduler_future fut Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Htask) HΦ".

    wp_rec.
    wp_smart_apply (spmc_future_create_spec with "[//]") as (fut) "(#Hfut_inv & Hfut_producer)".
    wp_smart_apply (scheduler_silent_async_spec with "[$Hctx Htask Hfut_producer]") as "Hctx".
    { clear ctx. iIntros "%ctx Hctx".
      wp_smart_apply (wp_wand with "(Htask Hctx)") as (v) "(Hctx & HΨ)".
      wp_apply (spmc_future_set_spec with "[$Hfut_inv $Hfut_producer $HΨ]") as "_ //".
    }
    wp_pures.
    iApply ("HΦ" with "[$Hctx $Hfut_inv]").
  Qed.

  Lemma scheduler_await_spec ctx fut Ψ :
    {{{
      scheduler_context ctx ∗
      scheduler_future fut Ψ
    }}}
      scheduler_await ws_hub ctx fut
    {{{ v,
      RET v;
      scheduler_context ctx ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((%i & %hub & -> & (#Hhub_inv & #Hinv) & Hhub_owner) & #Hfut_inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (spmc_future_try_get_spec with "Hfut_inv") as ([task |]) "HΨ".

    - wp_pures.
      iApply ("HΦ" with "[Hhub_owner $HΨ]").
      iExists i. iSteps.

    - wp_pures.
      wp_bind (Match _ _ _ _).
      wp_apply (wp_wand _ _ (λ res, ws_hub.(ws_hub_owner) hub i)%I with "[Hhub_owner]") as (res) "Hhub_owner".
      { awp_smart_apply (ws_hub_pop_try_steal_spec with "[$Hhub_inv $Hhub_owner]"); [done | lia.. |].
        iInv "Hinv" as "(%tasks & >Hhub_model & Htasks)".
        iAaccIntro with "Hhub_model"; first iSteps.
        iIntros ([task |]) "Hhub_model !>"; last iSteps.
        iDestruct "Hhub_model" as "(%tasks' & -> & Hhub_model)".
        iDestruct (big_sepMS_disj_union with "Htasks") as "(Htask & Htasks)".
        rewrite big_sepMS_singleton.
        iSplitR "Htask"; first iSteps.
        iIntros "Hhub_owner". clear.

        wp_smart_apply (scheduler_execute_spec with "[$Hhub_owner $Htask]") as (res) "($ & _)".
      }
      wp_smart_apply ("HLöb" with "Hhub_owner HΦ").
  Qed.

  Lemma scheduler_kill_spec t :
    {{{
      scheduler_model t
    }}}
      scheduler_kill ws_hub t
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (%hub & %v_doms & %doms & -> & (#Hhub_inv & #Hinv) & Hhub_owner & Hv_doms & Hdoms) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_kill_spec with "Hhub_inv") as "_".
    wp_smart_apply (array_iter_spec_disentangled' (λ _ _, True)%I with "[$Hv_doms Hdoms]"); last iSteps.
    iApply (big_sepL_impl with "Hdoms"). iIntros "!> %i %dom _ Hdom".
    wp_apply (domain_join_spec with "Hdom").
    iSteps.
  Qed.
End scheduler_G.

#[global] Opaque scheduler_create.
#[global] Opaque scheduler_run.
#[global] Opaque scheduler_silent_async.
#[global] Opaque scheduler_async.
#[global] Opaque scheduler_await.
#[global] Opaque scheduler_kill.

#[global] Opaque scheduler_model.
#[global] Opaque scheduler_context.
#[global] Opaque scheduler_future.
