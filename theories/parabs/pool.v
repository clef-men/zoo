From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  option
  array
  domain
  spmc_future.
From zoo.parabs Require Export
  base.
From zoo.parabs Require Import
  ws_hub.
From zoo Require Import
  options.

Implicit Types b not_killed : bool.
Implicit Types v t hub task pred : val.

#[local] Notation "'hub'" := (
  in_type "t" 0
)(in custom zoo_proj
).
#[local] Notation "'domains'" := (
  in_type "t" 1
)(in custom zoo_proj
).

#[local] Notation "'context_hub'" := (
  in_type "context" 0
)(in custom zoo_proj
).
#[local] Notation "'context_id'" := (
  in_type "context" 1
)(in custom zoo_proj
).

Section ws_deques.
  Context `{zoo_G : !ZooG Σ}.
  Context (ws_hub : ws_hub Σ).

  #[local] Parameter pool_max_round_noyield : nat.
  #[local] Parameter pool_max_round_yield : nat.
  #[local] Definition pool_max_round : val :=
    (#pool_max_round_noyield, #pool_max_round_yield).

  #[local] Definition pool_execute : val :=
    fun: "ctx" "task" =>
      "task" "ctx".

  #[local] Definition pool_worker : val :=
    rec: "pool_worker" "ctx" =>
      match: ws_hub_pop_steal ws_hub "ctx".<context_hub> "ctx".<context_id> pool_max_round with
      | None =>
          ()
      | Some "task" =>
          pool_execute "ctx" "task" ;;
          "pool_worker" "ctx"
      end.

  Definition pool_create : val :=
    fun: "sz" =>
      let: "hub" := ws_hub.(ws_hub_create) (#1 + "sz") in
      let: "doms" := array_unsafe_initi "sz" (fun: "i" =>
        domain_spawn (fun: <> => pool_worker ("hub", #1 + "i"))
      ) in
      ("hub", "doms").

  #[using="ws_hub"]
  Definition pool_run : val :=
    fun: "t" "task" =>
      pool_execute ("t".<hub>, #0) "task".

  Definition pool_silent_async : val :=
    fun: "ctx" "task" =>
      ws_hub.(ws_hub_push) "ctx".<context_hub> "ctx".<context_id> "task".

  Definition pool_async : val :=
    fun: "ctx" "task" =>
      let: "fut" := spmc_future_create () in
      pool_silent_async "ctx" (fun: "ctx" =>
        spmc_future_set "fut" ("task" "ctx")
      ) ;;
      "fut".

  Definition pool_wait_until : val :=
    rec: "pool_wait_until" "ctx" "pred" =>
      ifnot: "pred" () then
        match: ws_hub_pop_steal_until ws_hub "ctx".<context_hub> "ctx".<context_id> #pool_max_round_noyield "pred" with
        | None =>
            ()
        | Some "task" =>
            pool_execute "ctx" "task" ;;
            "pool_wait_until" "ctx" "pred"
        end.

  Definition pool_wait_while : val :=
    fun: "ctx" "pred" =>
      pool_wait_until "ctx" (fun: <> => ~ "pred" ()).

  Definition pool_await : val :=
    fun: "ctx" "fut" =>
      pool_wait_until "ctx" (fun: <> => spmc_future_is_set "fut") ;;
      spmc_future_get "fut".

  Definition pool_kill : val :=
    fun: "t" =>
      ws_hub.(ws_hub_kill) "t".<hub> ;;
      array_iter "t".<domains> domain_join.
End ws_deques.

Class SchedulerG Σ `{zoo_G : !ZooG Σ} := {
  #[local] pool_G_domain_G :: DomainG Σ ;
  #[local] pool_G_future_G :: SpmcFutureG Σ ;
}.

Definition pool_Σ := #[
  domain_Σ ;
  spmc_future_Σ
].
#[global] Instance subG_pool_Σ Σ `{zoo_G : !ZooG Σ} :
  subG pool_Σ Σ →
  SchedulerG Σ.
Proof.
  solve_inG.
Qed.

Section pool_G.
  Context `{pool_G : SchedulerG Σ}.
  Context (ws_hub : ws_hub Σ).

  #[local] Definition pool_task hub task Ψ : iProp Σ :=
    ∀ i,
    ws_hub.(ws_hub_owner) hub i -∗
    WP task (hub, #i)%V {{ v,
      ws_hub.(ws_hub_owner) hub i ∗
      Ψ v
    }}.
  #[local] Definition pool_inv_inner hub : iProp Σ :=
    ∃ tasks,
    ws_hub.(ws_hub_model) hub tasks ∗
    [∗ mset] task ∈ tasks,
      pool_task hub task (λ _, True).
  #[local] Definition pool_inv hub : iProp Σ :=
    ws_hub.(ws_hub_inv) hub (nroot.@"hub") ∗
    inv (nroot.@"inv") (pool_inv_inner hub).

  Definition pool_model t : iProp Σ :=
    ∃ hub v_doms doms,
    ⌜t = (hub, v_doms)%V⌝ ∗
    pool_inv hub ∗
    ws_hub.(ws_hub_owner) hub 0 ∗
    array_model v_doms DfracDiscarded doms ∗
    [∗ list] dom ∈ doms,
      domain_model dom (λ res, ⌜res = ()%V⌝).

  #[local] Definition pool_context' ctx (i : nat) : iProp Σ :=
    ∃ hub,
    ⌜ctx = (hub, #i)%V⌝ ∗
    pool_inv hub ∗
    ws_hub.(ws_hub_owner) hub i.
  Definition pool_context ctx : iProp Σ :=
    ∃ i,
    pool_context' ctx i.

  #[using="ws_hub"]
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
      ws_hub.(ws_hub_owner) hub i ∗
      pool_task hub task Ψ
    }}}
      pool_execute (hub, #i)%V task
    {{{ v,
      RET v;
      ws_hub.(ws_hub_owner) hub i ∗
      Ψ v
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma pool_worker_spec ctx :
    {{{
      pool_context ctx
    }}}
      pool_worker ws_hub ctx
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
    iIntros "Hhub_owner HΦ". clear- pool_G.

    wp_smart_apply (pool_execute_spec with "[$Hhub_owner $Htask]") as (res) "(Hhub_owner & _)".
    wp_smart_apply ("HLöb" with "Hhub_owner HΦ").
  Qed.

  Lemma pool_create_spec sz :
    (0 ≤ sz)%Z →
    {{{ True }}}
      pool_create ws_hub #sz
    {{{ t,
      RET t;
      pool_model t
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_create_spec with "[//]") as (t) "(#Hhub_inv & Hhub_model & Hhub_owners)"; first lia.
    rewrite Z2Nat.inj_add //.
    iDestruct "Hhub_owners" as "(Hhub_owner & Hhub_owners)".

    iMod (inv_alloc _ _ (pool_inv_inner t) with "[Hhub_model]") as "#Hinv".
    { iSteps. rewrite big_sepMS_empty //. }

    pose Ψ res : iProp Σ := (
      ⌜res = ()%V⌝
    )%I.
    wp_smart_apply (array_unsafe_initi_spec_disentangled' (λ _ dom, domain_model dom Ψ) with "[Hhub_owners]") as (v_doms doms) "(_ & Hv_doms & Hdoms)"; first done.
    { iApply (big_sepL_mono_strong with "Hhub_owners").
      { rewrite !seq_length. lia. }
      iIntros "!>" (k i1 i2 ((-> & Hi1)%lookup_seq & (-> & Hi2)%lookup_seq)) "Hhub_owner".
      wp_smart_apply (domain_spawn_spec Ψ with "[Hhub_owner]"); last iSteps.
      wp_smart_apply (pool_worker_spec with "[Hhub_owner]"); last iSteps.
      rewrite Z.add_1_l -Nat2Z.inj_succ. iExists _. iSteps.
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
      pool_run ws_hub t task
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
      pool_silent_async ws_hub ctx task
    {{{
      RET ();
      pool_context ctx
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
      pool_async ws_hub ctx task
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
      pool_wait_until ws_hub ctx pred
    {{{
      RET ();
      pool_context ctx ∗
      P
    }}}.
  Proof.
    iIntros "%Φ ((%i & %hub & -> & (#Hhub_inv & #Hinv) & Hhub_owner) & #Hpred) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (wp_wand with "Hpred") as (res) "(%b & -> & HP)".
    destruct b.

    - wp_pures.
      iApply ("HΦ" with "[Hhub_owner $HP]").
      iExists i. iSteps.

    - awp_smart_apply (ws_hub_pop_steal_until_spec _ P with "[$Hhub_inv $Hhub_owner $Hpred]") without "HΦ"; [lia.. |].
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
      pool_wait_while ws_hub ctx pred
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
      pool_await ws_hub ctx fut
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
      pool_kill ws_hub t
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
