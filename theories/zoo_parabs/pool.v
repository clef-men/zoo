From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  array
  domain
  ivar_3
  lst
  option.
From zoo_parabs Require Export
  base
  pool__code.
From zoo_parabs Require Import
  pool__types
  ws_hub_std.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v t ctx hub task fut waiter pred fn : val.

#[local] Definition max_round_noyield :=
  val_to_nat pool_max_round_noyield.
#[local] Lemma pool_max_round_noyield :
  pool_max_round_noyield = #max_round_noyield.
Proof.
  done.
Qed.
Opaque pool__code.pool_max_round_noyield.
Opaque max_round_noyield.

#[local] Definition max_round_yield :=
  val_to_nat pool_max_round_yield.
#[local] Lemma pool_max_round_yield :
  pool_max_round_yield = #max_round_yield.
Proof.
  done.
Qed.
Opaque pool__code.pool_max_round_yield.
Opaque max_round_yield.

Class SchedulerG Σ `{zoo_G : !ZooG Σ} := {
  #[local] pool_G_domain_G :: DomainG Σ ;
  #[local] pool_G_ivar_G :: Ivar3G Σ ;
  #[local] pool_G_ws_hub_G :: WsHubStdG Σ ;
}.

Definition pool_Σ := #[
  domain_Σ ;
  ivar_3_Σ ;
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

  Implicit Types Ψ Χ Ξ : val → iProp Σ.

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
      {%Heq{};->} &
      -> &
      {#Hinv{};(:inv')}
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
      {%Heq{};->} &
      {#Hinv{};(:inv')} &
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
      %𝑐𝑡𝑥{;_} &
      {%H𝑡{}_eq;->} &
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
      {%H𝑐𝑡𝑥{}_eq;->} &
      {#Hinv{};(:inv')} &
      Hhub_owner
    )".

  Definition pool_future_inv fut Ψ Ξ :=
    ivar_3_inv fut Ψ Ξ (λ fut waiter,
      ∀ ctx v,
      pool_context_model ctx -∗
      ivar_3_result fut v -∗
      WP waiter ctx v {{ res,
        ⌜res = ()%V⌝ ∗
        pool_context_model ctx
      }}
    )%I.

  Definition pool_future_consumer :=
    ivar_3_consumer.

  Definition pool_future_result :=
    ivar_3_result.

  #[global] Instance pool_future_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (pool_future_inv t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance pool_future_result_timeless fut v :
    Timeless (pool_future_result fut v).
  Proof.
    apply _.
  Qed.
  #[global] Instance pool_context_inv_persistent t ctx :
    Persistent (pool_context_inv t ctx).
  Proof.
    apply _.
  Qed.
  #[global] Instance pool_future_inv_persistent fut Ψ Ξ :
    Persistent (pool_future_inv fut Ψ Ξ).
  Proof.
    apply _.
  Qed.
  #[global] Instance pool_future_result_persistent fut v :
    Persistent (pool_future_result fut v).
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

  Lemma pool_future_consumer_divide {t Ψ Ξ Χ} Χs :
    pool_future_inv t Ψ Ξ -∗
    pool_future_consumer t Χ -∗
    (∀ x, Χ x -∗ [∗ list] Χ ∈ Χs, Χ x) ={⊤}=∗
    [∗ list] Χ ∈ Χs, pool_future_consumer t Χ.
  Proof.
    apply ivar_3_consumer_divide.
  Qed.
  Lemma pool_future_consumer_split {t Ψ Χ Ξ} Χ1 Χ2 :
    pool_future_inv t Ψ Ξ -∗
    pool_future_consumer t Χ -∗
    (∀ v, Χ v -∗ Χ1 v ∗ Χ2 v) ={⊤}=∗
      pool_future_consumer t Χ1 ∗
      pool_future_consumer t Χ2.
  Proof.
    apply ivar_3_consumer_split.
  Qed.

  Lemma pool_future_result_agree t v1 v2 :
    pool_future_result t v1 -∗
    pool_future_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_3_result_agree.
  Qed.

  Lemma pool_future_inv_result t Ψ Ξ v :
    pool_future_inv t Ψ Ξ -∗
    pool_future_result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    apply ivar_3_inv_result.
  Qed.
  Lemma pool_future_inv_result' t Ψ Ξ v :
    £ 1 -∗
    pool_future_inv t Ψ Ξ -∗
    pool_future_result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    apply ivar_3_inv_result'.
  Qed.
  Lemma pool_future_inv_result_consumer t Ψ Ξ v Χ :
    pool_future_inv t Ψ Ξ -∗
    pool_future_result t v -∗
    pool_future_consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    apply ivar_3_inv_result_consumer.
  Qed.
  Lemma pool_future_inv_result_consumer' t Ψ Ξ v Χ :
    £ 2 -∗
    pool_future_inv t Ψ Ξ -∗
    pool_future_result t v -∗
    pool_future_consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    apply ivar_3_inv_result_consumer'.
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

    wp_rec. rewrite pool_max_round_noyield pool_max_round_yield.

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

  Lemma pool_async_silent_spec_inv t ctx task :
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
      pool_async_silent ctx task
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
  Lemma pool_async_silent_spec ctx task :
    {{{
      pool_context_model ctx ∗
      ( ∀ ctx,
        pool_context_model ctx -∗
        WP task ctx {{ res,
          pool_context_model ctx
        }}
      )
    }}}
      pool_async_silent ctx task
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

  Lemma pool_async_spec_inv Ψ Ξ t ctx task :
    {{{
      pool_context_inv t ctx ∗
      pool_context_model ctx ∗
      ( ∀ ctx,
        pool_context_inv t ctx -∗
        pool_context_model ctx -∗
        WP task ctx {{ v,
          pool_context_model ctx ∗
          Ψ v ∗
          □ Ξ v
        }}
      )
    }}}
      pool_async ctx task
    {{{ fut,
      RET fut;
      pool_context_model ctx ∗
      pool_future_inv fut Ψ Ξ ∗
      pool_future_consumer fut Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx_inv & Hctx_model & Htask) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_create_spec Ψ Ξ with "[//]") as (ivar) "(#Hivar_inv & Hivar_producer & Hivar_consumer)".
    wp_smart_apply (pool_async_silent_spec_inv with "[$Hctx_inv $Hctx_model Htask Hivar_producer]") as "Hctx_model".
    { iIntros "{%} %ctx Hctx_inv Hctx_model".
      wp_smart_apply (wp_wand with "(Htask Hctx_inv Hctx_model)") as (v) "(Hctx_model & HΨ & HΞ)".
      wp_smart_apply (ivar_3_set_spec with "[$Hivar_inv $Hivar_producer $HΨ $HΞ]") as (waiters) "(#Hivar_result & Hwaiters)".
      wp_smart_apply (lst_iter_spec' (λ _ _, pool_context_model ctx)%I with "[$Hctx_model Hwaiters]") as "$"; try done.
      iApply (big_sepL_impl with "Hwaiters").
      iSteps.
    }
    wp_pures.
    iApply ("HΦ" with "[$]").
  Qed.
  Lemma pool_async_spec Ψ Ξ ctx task :
    {{{
      pool_context_model ctx ∗
      ( ∀ ctx,
        pool_context_model ctx -∗
        WP task ctx {{ v,
          pool_context_model ctx ∗
          Ψ v ∗
          □ Ξ v
        }}
      )
    }}}
      pool_async ctx task
    {{{ fut,
      RET fut;
      pool_context_model ctx ∗
      pool_future_inv fut Ψ Ξ ∗
      pool_future_consumer fut Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Htask) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_create_spec Ψ Ξ with "[//]") as (ivar) "(#Hivar_inv & Hivar_producer & Hivar_consumer)".
    wp_smart_apply (pool_async_silent_spec with "[$Hctx Htask Hivar_producer]") as "Hctx".
    { iIntros "{%} %ctx Hctx".
      wp_smart_apply (wp_wand with "(Htask Hctx)") as (v) "(Hctx & HΨ & HΞ)".
      wp_smart_apply (ivar_3_set_spec with "[$Hivar_inv $Hivar_producer $HΨ $HΞ]") as (waiters) "(#Hivar_result & Hwaiters)".
      wp_smart_apply (lst_iter_spec' (λ _ _, pool_context_model ctx)%I with "[$Hctx Hwaiters]") as "$"; try done.
      iApply (big_sepL_impl with "Hwaiters").
      iSteps.
    }
    wp_pures.
    iApply ("HΦ" with "[$]").
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

    wp_rec. rewrite pool_max_round_noyield.
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

  Lemma pool_wait_spec ctx fut Ψ Ξ :
    {{{
      pool_context_model ctx ∗
      pool_future_inv fut Ψ Ξ
    }}}
      pool_wait ctx fut
    {{{ v,
      RET v;
      £ 2 ∗
      pool_context_model ctx ∗
      pool_future_result fut v
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hivar_inv) HΦ".

    wp_rec.
    wp_smart_apply (pool_wait_until_spec (ivar_3_result' fut)%I with "[$Hctx]") as "(Hctx & %v & #Hivar_result)".
    { iModIntro.
      wp_smart_apply (ivar_3_is_set_spec with "Hivar_inv") as (b) "Hivar_result".
      rewrite /ivar_3_result'. destruct b; iSteps.
    }
    wp_smart_apply (ivar_3_get_spec with "[$Hivar_inv $Hivar_result]") as "H£".
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma pool_iter_spec ctx fut Ψ Ξ fn :
    {{{
      pool_context_model ctx ∗
      pool_future_inv fut Ψ Ξ ∗
      ( ∀ ctx v,
        pool_context_model ctx -∗
        pool_future_result fut v -∗
        WP fn ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context_model ctx
        }}
      )
    }}}
      pool_iter ctx fut fn
    {{{
      RET ();
      pool_context_model ctx
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hivar_inv & Hfn) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_wait_spec with "[$Hivar_inv $Hfn]") as ([v |]) "H".
    all: wp_pures.

    - iDestruct "H" as "(_ & #Hivar_result & Hfn)".
      wp_apply (wp_wand with "(Hfn Hctx Hivar_result)").
      iSteps.

    - iApply ("HΦ" with "Hctx").
  Qed.

  Lemma pool_map_spec {ctx fut1 Ψ1 Ξ1} Ψ2 Ξ2 fn :
    {{{
      pool_context_model ctx ∗
      pool_future_inv fut1 Ψ1 Ξ1 ∗
      ( ∀ ctx v1,
        pool_context_model ctx -∗
        pool_future_result fut1 v1 -∗
        WP fn ctx v1 {{ v2,
          pool_context_model ctx ∗
          ▷ Ψ2 v2 ∗
          ▷ □ Ξ2 v2
        }}
      )
    }}}
      pool_map ctx fut1 fn
    {{{ fut2,
      RET fut2;
      pool_context_model ctx ∗
      pool_future_inv fut2 Ψ2 Ξ2 ∗
      pool_future_consumer fut2 Ψ2
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hfut1_inv & Hfn) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_create_spec Ψ2 Ξ2 with "[//]") as (fut2) "(#Hivar2_inv & Hivar2_producer & Hivar2_consumer)".
    wp_smart_apply (pool_iter_spec with "[$Hctx $Hfut1_inv Hfn Hivar2_producer]"); last iSteps.
    iIntros "{%} %ctx %v1 Hctx #Hfut1_result".
    wp_smart_apply (wp_wand with "(Hfn Hctx Hfut1_result)") as (v2) "(Hctx & HΨ2 & HΞ2)".
    wp_smart_apply (ivar_3_set_spec with "[$Hivar2_inv $Hivar2_producer $HΨ2 $HΞ2]") as (waiters) "(#Hivar2_result & Hwaiters)".
    wp_smart_apply (lst_iter_spec' (λ _ _, pool_context_model ctx)%I with "[$Hctx Hwaiters]") as "$"; try done.
    iApply (big_sepL_impl with "Hwaiters").
    iSteps.
  Qed.
End pool_G.

From zoo_parabs Require
  pool__opaque.

#[global] Opaque pool_inv.
#[global] Opaque pool_model.
#[global] Opaque pool_context_inv.
#[global] Opaque pool_context_model.
#[global] Opaque pool_future_inv.
#[global] Opaque pool_future_consumer.
#[global] Opaque pool_future_result.
