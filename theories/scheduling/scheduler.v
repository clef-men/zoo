From zebre Require Import
  prelude.
From zebre.iris.bi Require Import
  big_op.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  for_upto
  spmc_future.
From zebre.scheduling Require Export
  base.
From zebre.scheduling Require Import
  ws_deques
  ws_hub.
From zebre Require Import
  options.

Implicit Types v t task : val.

#[local] Notation "'hub'" := (
in_type "context" 0
)(in custom zebre_proj
).
#[local] Notation "'id'" := (
  in_type "context" 1
)(in custom zebre_proj
).

Section ws_deques.
  Context `{zebre_G : !ZebreG Σ}.
  Context (ws_deques : ws_deques Σ).

  #[local] Definition scheduler_max_round :=
    2048.

  #[using="ws_deques"]
  #[local] Definition scheduler_execute : val :=
    λ: "ctx" "task",
      "task" "ctx".

  #[local] Definition scheduler_worker_aux : val :=
    λ: "ctx",
      let: "task" := ws_hub_pop ws_deques "ctx".<hub> "ctx".<id> #scheduler_max_round in
      scheduler_execute "ctx" "task".
  #[local] Definition scheduler_worker : val :=
    rec: "scheduler_worker" "ctx" :=
      scheduler_worker_aux "ctx" ;;
      "scheduler_worker" "ctx".

  Definition scheduler_create : val :=
    λ: "sz",
      let: "t" := ws_hub_create ws_deques (#1 + "sz") in
      for: "i" := #1 to #1 + "sz" begin
        Fork (scheduler_worker ("t", "i"))
      end ;;
      ("t", #0).

  Definition scheduler_run :=
    scheduler_execute.

  Definition scheduler_async : val :=
    λ: "ctx" "task",
      let: "fut" := spmc_future_create () in
      ws_hub_push ws_deques "ctx".<hub> "ctx".<id> (λ: "ctx",
        spmc_future_set "fut" ("task" "ctx")
      ) ;;
      "fut".

  Definition scheduler_await : val :=
    rec: "scheduler_await" "ctx" "fut" :=
      match: spmc_future_try_get "fut" with
      | Some "res" =>
          "res"
      | None =>
          scheduler_worker_aux "ctx" ;;
          "scheduler_await" "ctx" "fut"
      end.
End ws_deques.

Class SchedulerG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] scheduler_G_hub_G :: WsHubG Σ ;
  #[local] scheduler_G_future_G :: SpmcFutureG Σ ;
}.

Definition scheduler_Σ := #[
  ws_hub_Σ ;
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
  Context (ws_deques : ws_deques Σ).

  #[local] Definition scheduler_task t task : iProp Σ :=
    ∀ i,
    ws_hub_owner ws_deques t i -∗
    WP task (t, #i)%V {{ _,
      ws_hub_owner ws_deques t i
    }}.
  #[local] Definition scheduler_inv_inner t : iProp Σ :=
    ∃ tasks,
    ws_hub_model ws_deques t tasks ∗
    [∗ mset] task ∈ tasks,
      scheduler_task t task.
  Definition scheduler_inv t : iProp Σ :=
    ws_hub_inv ws_deques t (nroot.@"hub") ∗
    inv (nroot.@"inv") (scheduler_inv_inner t).

  Definition scheduler_context t ctx : iProp Σ :=
    ∃ (i : nat),
    ⌜ctx = (t, #i)%V⌝ ∗
    ws_hub_owner ws_deques t i.

  #[using="ws_deques"]
  Definition scheduler_future :=
    spmc_future_inv.

  #[global] Instance scheduler_future_proper t :
    Proper ((pointwise_relation _ (≡)) ==> (≡)) (scheduler_future t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance scheduler_context_timeless t ctx :
    Timeless (scheduler_context t ctx).
  Proof.
    apply _.
  Qed.
  #[global] Instance scheduler_inv_persistent t :
    Persistent (scheduler_inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance scheduler_future_persistent fut Ψ :
    Persistent (scheduler_future fut Ψ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma scheduler_execute_spec t i task :
    (0 ≤ i)%Z →
    {{{
      ws_hub_owner ws_deques t (Z.to_nat i) ∗
      scheduler_task t task
    }}}
      scheduler_execute ws_deques (t, #i)%V task
    {{{ res,
      RET res;
      ws_hub_owner ws_deques t (Z.to_nat i)
    }}}.
  Proof.
    iIntros "%Hi %Φ (Hhub_owner & Htask) HΦ".

    iSpecialize ("Htask" with "Hhub_owner").
    rewrite Z2Nat.id //. iSteps.
  Qed.

  #[local] Lemma scheduler_worker_aux_spec t i :
    (0 ≤ i)%Z →
    {{{
      scheduler_inv t ∗
      ws_hub_owner ws_deques t (Z.to_nat i)
    }}}
      scheduler_worker_aux ws_deques (t, #i)%V
    {{{ res,
      RET res;
      ws_hub_owner ws_deques t (Z.to_nat i)
    }}}.
  Proof.
    iIntros "%Hi %Φ ((#Hhub_inv & #Hinv) & Hhub_owner) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_pop_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; [done.. |].
    iInv "Hinv" as "(%tasks & >Hhub_model & Htasks)".
    iAaccIntro with "Hhub_model"; first iSteps. iIntros "%task %tasks' (-> & Hhub_model)".
    iDestruct (big_sepMS_disj_union with "Htasks") as "(Htask & Htasks)".
    rewrite big_sepMS_singleton.
    iSplitR "Htask"; first iSteps.
    iIntros "!> Hhub_owner HΦ". clear- Hi.

    wp_smart_apply (scheduler_execute_spec with "[$Hhub_owner $Htask] HΦ"); first done.
  Qed.
  #[local] Lemma scheduler_worker_spec t i :
    (0 ≤ i)%Z →
    {{{
      scheduler_inv t ∗
      ws_hub_owner ws_deques t (Z.to_nat i)
    }}}
      scheduler_worker ws_deques (t, #i)%V
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Hi %Φ (#Hinv & Hhub_owner) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_apply (scheduler_worker_aux_spec with "[$Hinv $Hhub_owner]") as (res) "Hhub_owner"; first done.
    wp_smart_apply ("HLöb" with "Hhub_owner HΦ").
  Qed.

  Lemma scheduler_create_spec sz :
    (0 ≤ sz)%Z →
    {{{ True }}}
      scheduler_create ws_deques #sz
    {{{ t ctx,
      RET ctx;
      scheduler_inv t ∗
      scheduler_context t ctx
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_create_spec with "[//]") as (t) "(#Hhub_inv & Hhub_model & Hhub_owners)"; [lia | done |].

    iMod (inv_alloc _ _ (scheduler_inv_inner t) with "[Hhub_model]") as "#Hinv".
    { iSteps. rewrite big_sepMS_empty //. }

    rewrite Z.add_1_l Z2Nat.inj_succ // -cons_seq.
    iDestruct "Hhub_owners" as "(Hhub_owner & Hhub_owners)".
    wp_smart_apply (for_upto_spec_disentangled' (λ _ _, True)%I with "[Hhub_owners]"); last first.
    { iSteps. iExists 0. iSteps. }
    iApply (big_sepL_mono_strong with "Hhub_owners").
    { rewrite !seq_length. lia. }
    iIntros "!>" (δ i1 i2 ((-> & Hi1)%lookup_seq & (-> & Hi2)%lookup_seq)) "Hhub_owner %i -> /=".
    wp_smart_apply (wp_fork with "[Hhub_owner]"); last iSteps. iModIntro.
    rewrite Z.add_1_l -Nat2Z.inj_succ.
    wp_smart_apply (scheduler_worker_spec with "[$Hhub_inv $Hinv Hhub_owner]").
    { done. }
    { rewrite Nat2Z.id //. }
    iSteps.
  Qed.

  Lemma scheduler_run_spec Ψ t ctx task :
    {{{
      scheduler_inv t ∗
      scheduler_context t ctx ∗
      ( ∀ ctx,
        scheduler_context t ctx -∗
        WP task ctx {{ v,
          scheduler_context t ctx ∗
          Ψ v
        }}
      )
    }}}
      scheduler_run ws_deques ctx task
    {{{ v,
      RET v;
      scheduler_context t ctx ∗
      Ψ v
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma scheduler_async_spec Ψ t ctx task :
    {{{
      scheduler_inv t ∗
      scheduler_context t ctx ∗
      ( ∀ ctx,
        scheduler_context t ctx -∗
        WP task ctx {{ v,
          scheduler_context t ctx ∗
          □ Ψ v
        }}
      )
    }}}
      scheduler_async ws_deques ctx task
    {{{ fut,
      RET fut;
      scheduler_context t ctx ∗
      scheduler_future fut Ψ
    }}}.
  Proof.
    iIntros "%Φ ((#Hhub_inv & #Hinv) & (%i & -> & Hhub_owner) & Htask) HΦ".

    wp_rec.
    wp_smart_apply (spmc_future_create_spec with "[//]") as (fut) "(#Hfut_inv & Hfut_producer)".

    awp_smart_apply (ws_hub_push_spec with "[$Hhub_inv Hhub_owner]") without "HΦ".
    { lia. }
    { rewrite Nat2Z.id //. }
    iInv "Hinv" as "(%tasks & >Hhub_model & Htasks)".
    iAaccIntro with "Hhub_model". { iFrame. iSteps. } iIntros "Hhub_model".
    iSplitL.
    { iExists _. iFrame. rewrite big_sepMS_singleton. iIntros "!> !> %j Hhub_owner".
      wp_smart_apply (wp_wand with "(Htask [Hhub_owner])") as (v) "((%_j & %Heq & Hhub_owner) & HΨ)"; first iSteps.
      injection Heq as [= <-%(inj _)].
      wp_smart_apply (spmc_future_set_spec with "[$Hfut_inv $Hfut_producer $HΨ]").
      iSteps.
    }
    rewrite Nat2Z.id. iSteps.
  Qed.

  Lemma scheduler_await_spec t ctx fut Ψ :
    {{{
      scheduler_inv t ∗
      scheduler_context t ctx ∗
      scheduler_future fut Ψ
    }}}
      scheduler_await ws_deques ctx fut
    {{{ v,
      RET v;
      scheduler_context t ctx ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((#Hhub_inv & #Hinv) & (%i & -> & Hhub_owner) & #Hfut_inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (spmc_future_try_get_spec with "Hfut_inv") as ([task |]) "HΨ"; first iSteps.
    wp_smart_apply (scheduler_worker_aux_spec with "[$Hhub_inv $Hinv Hhub_owner]") as (res) "Hhub_owner".
    { lia. }
    { rewrite Nat2Z.id //. }
    rewrite Nat2Z.id.
    wp_smart_apply ("HLöb" with "Hhub_owner HΦ").
  Qed.
End scheduler_G.

#[global] Opaque scheduler_create.
#[global] Opaque scheduler_run.
#[global] Opaque scheduler_async.
#[global] Opaque scheduler_await.

#[global] Opaque scheduler_inv.
#[global] Opaque scheduler_context.
#[global] Opaque scheduler_future.
