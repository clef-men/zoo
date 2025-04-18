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

Implicit Types b : bool.
Implicit Types v t ctx hub task pred : val.

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

Record common := {
  common_size : nat ;
  common_hub : val ;
}.
Implicit Types 𝑐𝑜𝑚 : common.

Record t := {
  t_size : nat ;
  t_hub : val ;
  t_domains : val ;
}.
Implicit Types 𝑡 : t.

#[local] Coercion t_to_val 𝑡 :=
  ( #𝑡.(t_size),
    𝑡.(t_hub),
    𝑡.(t_domains)
  )%V.
#[local] Coercion t_to_common 𝑡 :=
  {|common_size := 𝑡.(t_size) ;
    common_hub := 𝑡.(t_hub) ;
  |}.

#[local] Lemma t_to_val_inj' t 𝑡1 𝑡2 :
  t = 𝑡1 →
  t = 𝑡2 →
  𝑡1 = 𝑡2.
Proof.
  destruct 𝑡1, 𝑡2. naive_solver.
Qed.
#[local] Instance t_to_val_inj :
  Inj (=) (=) t_to_val.
Proof.
  intros ?*. eapply t_to_val_inj'; done.
Qed.

Record context := {
  context_size : nat ;
  context_hub : val ;
  context_id : nat ;
}.
Implicit Types 𝑐𝑡𝑥 : context.

#[local] Coercion context_to_val 𝑐𝑡𝑥 :=
  ( #𝑐𝑡𝑥.(context_size),
    𝑐𝑡𝑥.(context_hub),
    #𝑐𝑡𝑥.(context_id)
  )%V.
#[local] Coercion context_to_common 𝑐𝑡𝑥 :=
  {|common_size := 𝑐𝑡𝑥.(context_size) ;
    common_hub := 𝑐𝑡𝑥.(context_hub) ;
  |}.

#[local] Lemma context_to_val_inj' ctx 𝑐𝑡𝑥1 𝑐𝑡𝑥2 :
  ctx = 𝑐𝑡𝑥1 →
  ctx = 𝑐𝑡𝑥2 →
  𝑐𝑡𝑥1 = 𝑐𝑡𝑥2.
Proof.
  destruct 𝑐𝑡𝑥1, 𝑐𝑡𝑥2. naive_solver.
Qed.
#[local] Instance context_to_val_inj :
  Inj (=) (=) context_to_val.
Proof.
  intros ?*. eapply context_to_val_inj'; done.
Qed.

#[local] Definition common_to_t 𝑐𝑜𝑚 domains :=
  {|t_size := 𝑐𝑜𝑚.(common_size) ;
    t_hub := 𝑐𝑜𝑚.(common_hub) ;
    t_domains := domains ;
  |}.
#[local] Definition common_to_context 𝑐𝑜𝑚 i :=
  {|context_size := 𝑐𝑜𝑚.(common_size) ;
    context_hub := 𝑐𝑜𝑚.(common_hub) ;
    context_id := i ;
  |}.

Section pool_G.
  Context `{pool_G : SchedulerG Σ}.

  #[local] Definition task_model 𝑐𝑜𝑚 task Ψ : iProp Σ :=
    ∀ i,
    ws_hub_std_owner 𝑐𝑜𝑚.(common_hub) i Nonblocked -∗
    WP task (common_to_context 𝑐𝑜𝑚 i) {{ v,
      ws_hub_std_owner 𝑐𝑜𝑚.(common_hub) i Nonblocked ∗
      Ψ v
    }}.

  #[local] Definition inv_inner 𝑐𝑜𝑚 : iProp Σ :=
    ∃ tasks,
    ws_hub_std_model 𝑐𝑜𝑚.(common_hub) tasks ∗
    [∗ mset] task ∈ tasks,
      task_model 𝑐𝑜𝑚 task (λ _, True).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %tasks &
      >Hhub_model &
      Htasks
    )".
  #[local] Definition inv' 𝑐𝑜𝑚 : iProp Σ :=
    ws_hub_std_inv 𝑐𝑜𝑚.(common_hub) (nroot.@"hub") (S 𝑐𝑜𝑚.(common_size)) ∗
    inv (nroot.@"inv") (inv_inner 𝑐𝑜𝑚).
  #[local] Instance : CustomIpatFormat "inv'" :=
    "(
      #Hhub{}_inv &
      #Hinv{}
    )".
  Definition pool_inv t sz : iProp Σ :=
    ∃ 𝑡,
    ⌜t = 𝑡⌝ ∗
    ⌜sz = 𝑡.(t_size)⌝ ∗
    inv' 𝑡.
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %𝑡{} &
      {%Heq{}=->} &
      -> &
      {#Hinv{}=(:inv')}
    )".

  Definition pool_model t : iProp Σ :=
    ∃ 𝑡 doms,
    ⌜t = 𝑡⌝ ∗
    inv' 𝑡 ∗
    ws_hub_std_owner 𝑡.(t_hub) 0 Blocked ∗
    array_model 𝑡.(t_domains) DfracDiscarded doms ∗
    [∗ list] dom ∈ doms,
      domain_model dom itype_unit.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %𝑡{} &
      %doms{} &
      {%Heq{}=->} &
      {#Hinv{}=(:inv')} &
      Hhub{}_owner &
      Hdomains{} &
      Hdoms{}
    )".

  Definition pool_context_inv t ctx : iProp Σ :=
    ∃ 𝑡 𝑐𝑡𝑥,
    ⌜t = 𝑡⌝ ∗
    ⌜ctx = 𝑐𝑡𝑥⌝ ∗
    ⌜𝑡 = 𝑐𝑡𝑥 :> common⌝.
  #[local] Instance : CustomIpatFormat "context_inv" :=
    "(
      %𝑡{} &
      %𝑐𝑡𝑥{=_} &
      {%H𝑡{}_eq=->} &
      %H𝑐𝑡𝑥{}_eq &
      %Hcommon{}
    )".

  Definition pool_context_model ctx : iProp Σ :=
    ∃ 𝑐𝑡𝑥,
    ⌜ctx = 𝑐𝑡𝑥⌝ ∗
    inv' 𝑐𝑡𝑥 ∗
    ws_hub_std_owner 𝑐𝑡𝑥.(context_hub) 𝑐𝑡𝑥.(context_id) Nonblocked.
  #[local] Instance : CustomIpatFormat "context_model" :=
    "(
      %𝑐𝑡𝑥{} &
      {%H𝑐𝑡𝑥{}_eq=->} &
      {#Hinv{}=(:inv')} &
      Hhub_owner
    )".

  Definition pool_future :=
    spmc_future_inv.

  #[global] Instance pool_future_proper t :
    Proper ((pointwise_relation _ (≡)) ==> (≡)) (pool_future t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance pool_context_inv_persistent t ctx :
    Persistent (pool_context_inv t ctx).
  Proof.
    apply _.
  Qed.
  #[global] Instance pool_future_persistent fut Ψ :
    Persistent (pool_future fut Ψ).
  Proof.
    apply _.
  Qed.

  Lemma pool_inv_agree t sz1 sz2 :
    pool_inv t sz1 -∗
    pool_inv t sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)".
    erewrite (t_to_val_inj' _ 𝑡1 𝑡2); done.
  Qed.

  #[local] Lemma pool_execute_spec 𝑐𝑜𝑚 i task Ψ :
    {{{
      ws_hub_std_owner 𝑐𝑜𝑚.(common_hub) i Nonblocked ∗
      task_model 𝑐𝑜𝑚 task Ψ
    }}}
      pool_execute (common_to_context 𝑐𝑜𝑚 i) task
    {{{ v,
      RET v;
      ws_hub_std_owner 𝑐𝑜𝑚.(common_hub) i Nonblocked ∗
      Ψ v
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma pool_worker_spec 𝑐𝑜𝑚 i ctx :
    ctx = common_to_context 𝑐𝑜𝑚 i →
    {{{
      inv' 𝑐𝑜𝑚 ∗
      ws_hub_std_owner 𝑐𝑜𝑚.(common_hub) i Nonblocked
    }}}
      pool_worker ctx
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv') & Hhub_owner) HΦ".

    iLöb as "HLöb".

    wp_rec.
    rewrite pool_max_round_noyield_eq pool_max_round_yield_eq.

    awp_smart_apply (ws_hub_std_pop_steal_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; [done | lia.. |].
    iInv "Hinv" as "(:inv_inner)".
    iAaccIntro with "Hhub_model"; first iSteps. iIntros ([task |]) "Hhub_model !>".

    - iDestruct "Hhub_model" as "(%tasks' & -> & Hhub_model)".
      iDestruct (big_sepMS_disj_union with "Htasks") as "(Htask & Htasks)".
      rewrite big_sepMS_singleton.
      iSplitR "Htask"; first iSteps.
      iIntros "{%} Hhub_owner HΦ".

      wp_smart_apply (pool_execute_spec with "[$Hhub_owner $Htask]") as (res) "(Hhub_owner & _)".
      wp_smart_apply ("HLöb" with "Hhub_owner HΦ").

    - iSplitL; first iSteps.
      iIntros "{%} Hhub_owner HΦ".

      wp_smart_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]"); first done.
      iSteps.
  Qed.

  Lemma pool_create_spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      pool_create #sz
    {{{ t,
      RET t;
      pool_inv t ₊sz ∗
      pool_model t
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec. rewrite /pool_context.
    wp_smart_apply (ws_hub_std_create_spec with "[//]") as (hub) "(#Hhub_inv & Hhub_model & Hhub_owners)"; first lia.
    rewrite Z2Nat.inj_add // Nat.add_1_r.
    iDestruct "Hhub_owners" as "(Hhub_owner & Hhub_owners)".

    pose 𝑐𝑜𝑚 := {|
      common_size := ₊sz ;
      common_hub := hub ;
    |}.

    iMod (inv_alloc _ _ (inv_inner 𝑐𝑜𝑚) with "[Hhub_model]") as "#Hinv".
    { iSteps. rewrite big_sepMS_empty //. }

    wp_smart_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
    wp_smart_apply (array_unsafe_initi_spec_disentangled' (λ _ dom, domain_model dom itype_unit) with "[Hhub_owners]") as (domains doms) "(_ & Hdomains & Hdoms)"; first done.
    { iApply (big_sepL_impl_strong with "Hhub_owners").
      { simpl_length. }
      iIntros "!>" (k i1 i2 (-> & Hi1)%lookup_seq (-> & Hi2)%lookup_seq) "Hhub_owner".
      wp_smart_apply (domain_spawn_spec itype_unit with "[Hhub_owner]"); last iSteps. iIntros "%tid _".
      iApply wp_thread_id_mono.
      wp_smart_apply (pool_worker_spec with "[$Hinv $Hhub_owner]"); [| iSteps..].
      assert ((⁺k + 1)%Z = S k) as -> by lia.
      rewrite /context_to_val Z2Nat.id //.
    }
    iMod (array_model_persist with "Hdomains") as "#Hdomains".
    wp_pures.

    pose 𝑡 := {|
      t_size := ₊sz ;
      t_hub := hub ;
      t_domains := domains ;
    |}.

    iApply "HΦ".
    iSplitR.
    all: iExists 𝑡.
    all: rewrite /t_to_val Z2Nat.id //.
    all: iSteps.
  Qed.

  Lemma pool_run_spec Ψ t task :
    {{{
      pool_model t ∗
      ( ∀ ctx,
        pool_context_inv t ctx -∗
        pool_context_model ctx -∗
        WP task ctx {{ v,
          pool_context_model ctx ∗
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
    iIntros "%Φ ((:model) & Htask) HΦ".

    wp_rec. rewrite /pool_context.
    wp_smart_apply (ws_hub_std_unblock_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
    wp_smart_apply (pool_execute_spec _ 0 _ Ψ with "[$Hhub_owner Htask]") as (v) "(Hhub_owner & HΨ)".
    { iIntros "%i Hhub_owner".
      wp_apply (wp_wand with "(Htask [] [Hhub_owner])") as "%v ((:context_model =1) & $)"; [iSteps.. |].
      apply (inj context_to_val) in H𝑐𝑡𝑥1_eq as <-.
      iSteps.
    }
    wp_smart_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
    iSteps.
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
    iIntros "%Φ (:model) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_std_kill_spec with "Hhub_inv") as "_".
    wp_smart_apply (array_iter_spec_disentangled' (λ _ _, True)%I with "[$Hdomains Hdoms]"); last iSteps.
    iApply (big_sepL_impl with "Hdoms"). iIntros "!> %i %dom _ Hdom".
    wp_apply (domain_join_spec with "Hdom").
    iSteps.
  Qed.

  Lemma pool_size_spec t sz ctx :
    {{{
      pool_inv t sz ∗
      pool_context_inv t ctx
    }}}
      pool_size ctx
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:context_inv =2)) HΦ". simplify.
    wp_rec. wp_pures.
    apply (f_equal common_size) in Hcommon2 as Hsize2. simpl in Hsize2. rewrite -Hsize2.
    iSteps.
  Qed.

  Lemma pool_silent_async_spec_inv t ctx task :
    {{{
      pool_context_inv t ctx ∗
      pool_context_model ctx ∗
      ( ∀ ctx,
        pool_context_inv t ctx -∗
        pool_context_model ctx -∗
        WP task ctx {{ res,
          pool_context_model ctx
        }}
      )
    }}}
      pool_silent_async ctx task
    {{{
      RET ();
      pool_context_model ctx
    }}}.
  Proof.
    iIntros "%Φ ((:context_inv) & (:context_model) & Htask) HΦ".
    apply (inj context_to_val) in H𝑐𝑡𝑥_eq as <-.

    wp_rec.

    awp_smart_apply (ws_hub_std_push_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; first done.
    iInv "Hinv" as "(:inv_inner)".
    iAaccIntro with "Hhub_model"; first iFrameSteps. iIntros "Hhub_model".
    iSplitL. { iFrame. rewrite big_sepMS_singleton. iSteps. }
    iSteps.
  Qed.
  Lemma pool_silent_async_spec ctx task :
    {{{
      pool_context_model ctx ∗
      ( ∀ ctx,
        pool_context_model ctx -∗
        WP task ctx {{ res,
          pool_context_model ctx
        }}
      )
    }}}
      pool_silent_async ctx task
    {{{
      RET ();
      pool_context_model ctx
    }}}.
  Proof.
    iIntros "%Φ ((:context_model) & Htask) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_push_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; first done.
    iInv "Hinv" as "(:inv_inner)".
    iAaccIntro with "Hhub_model"; first iFrameSteps. iIntros "Hhub_model".
    iSplitL. { iFrame. rewrite big_sepMS_singleton. iSteps. }
    iSteps.
  Qed.

  Lemma pool_async_spec_inv Ψ t ctx task :
    {{{
      pool_context_inv t ctx ∗
      pool_context_model ctx ∗
      ( ∀ ctx,
        pool_context_inv t ctx -∗
        pool_context_model ctx -∗
        WP task ctx {{ v,
          pool_context_model ctx ∗
          □ Ψ v
        }}
      )
    }}}
      pool_async ctx task
    {{{ fut,
      RET fut;
      pool_context_model ctx ∗
      pool_future fut Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx_inv & Hctx_model & Htask) HΦ".

    wp_rec.
    wp_smart_apply (spmc_future_create_spec with "[//]") as (fut) "(#Hfut_inv & Hfut_producer)".
    wp_smart_apply (pool_silent_async_spec_inv with "[$Hctx_inv $Hctx_model Htask Hfut_producer]") as "Hctx_model".
    { clear ctx. iIntros "%ctx Hctx_inv Hctx_model".
      wp_smart_apply (wp_wand with "(Htask Hctx_inv Hctx_model)") as (v) "(Hctx_model & HΨ)".
      wp_apply (spmc_future_set_spec with "[$Hfut_inv $Hfut_producer $HΨ]") as "_ //".
    }
    wp_pures.
    iApply ("HΦ" with "[$Hctx_model $Hfut_inv]").
  Qed.
  Lemma pool_async_spec Ψ ctx task :
    {{{
      pool_context_model ctx ∗
      ( ∀ ctx,
        pool_context_model ctx -∗
        WP task ctx {{ v,
          pool_context_model ctx ∗
          □ Ψ v
        }}
      )
    }}}
      pool_async ctx task
    {{{ fut,
      RET fut;
      pool_context_model ctx ∗
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
      pool_context_model ctx ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    }}}
      pool_wait_until ctx pred
    {{{
      RET ();
      pool_context_model ctx ∗
      P
    }}}.
  Proof.
    iIntros "%Φ ((:context_model) & #Hpred) HΦ".

    iLöb as "HLöb".

    wp_rec.
    rewrite pool_max_round_noyield_eq.
    wp_smart_apply (wp_wand with "Hpred") as (res) "(%b & -> & HP)".
    destruct b; first iSteps.
    awp_smart_apply (ws_hub_std_pop_steal_until_spec P with "[$Hhub_inv $Hhub_owner $Hpred]") without "HΦ"; [lia.. |].
    iInv "Hinv" as "(:inv_inner)".
    iAaccIntro with "Hhub_model"; first iSteps. iIntros ([task |]) "Hhub_model !>"; last iSteps.
    iDestruct "Hhub_model" as "(%tasks' & -> & Hhub_model)".
    iDestruct (big_sepMS_insert with "Htasks") as "(Htask & Htasks')".
    iSplitR "Htask"; first iSteps.
    iIntros "{%} (Hhub_owner & _) HΦ".

    wp_smart_apply (pool_execute_spec with "[$Hhub_owner $Htask]") as (res) "(Hhub_owner & _)".
    wp_smart_apply ("HLöb" with "Hhub_owner HΦ").
  Qed.

  Lemma pool_wait_while_spec P ctx pred :
    {{{
      pool_context_model ctx ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then True else P
      }}
    }}}
      pool_wait_while ctx pred
    {{{
      RET ();
      pool_context_model ctx ∗
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
      pool_context_model ctx ∗
      pool_future fut Ψ
    }}}
      pool_await ctx fut
    {{{ v,
      RET v;
      pool_context_model ctx ∗
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
End pool_G.

#[global] Opaque pool_create.
#[global] Opaque pool_run.
#[global] Opaque pool_kill.
#[global] Opaque pool_size.
#[global] Opaque pool_silent_async.
#[global] Opaque pool_async.
#[global] Opaque pool_wait_until.
#[global] Opaque pool_wait_while.
#[global] Opaque pool_await.

#[global] Opaque pool_inv.
#[global] Opaque pool_model.
#[global] Opaque pool_context_inv.
#[global] Opaque pool_context_model.
#[global] Opaque pool_future.
