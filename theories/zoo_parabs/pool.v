From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
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
Implicit Types l : location.
Implicit Types v t ctx hub task fut waiter pred fn : val.
Implicit Types empty : emptiness.

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

Section pool_G.
  Context `{pool_G : SchedulerG Σ}.

  Implicit Types Ψ Χ Ξ : val → iProp Σ.

  Record metadata := {
    metadata_size : nat ;
    metadata_hub : val ;
    metadata_domains : val ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
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

  #[local] Definition context_consistent γ 𝑐𝑡𝑥 :=
    γ.(metadata_size) = 𝑐𝑡𝑥.(context_size) ∧
    γ.(metadata_hub) = 𝑐𝑡𝑥.(context_hub).
  #[local] Instance : CustomIpatFormat "context_consistent" :=
    "(
      %H𝑐𝑡𝑥{}_size &
      %H𝑐𝑡𝑥{}_hub
    )".

  #[local] Definition task_model γ task Ψ : iProp Σ :=
    ∀ 𝑐𝑡𝑥 empty,
    ⌜context_consistent γ 𝑐𝑡𝑥⌝ -∗
    ws_hub_std_owner γ.(metadata_hub) 𝑐𝑡𝑥.(context_id) Nonblocked empty -∗
    WP task 𝑐𝑡𝑥 {{ v,
      ∃ empty,
      ws_hub_std_owner γ.(metadata_hub) 𝑐𝑡𝑥.(context_id) Nonblocked empty ∗
      Ψ v
    }}.

  #[local] Definition inv_inner γ : iProp Σ :=
    ∃ tasks,
    ws_hub_std_model γ.(metadata_hub) tasks ∗
    [∗ mset] task ∈ tasks,
      task_model γ task (λ _, True).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %tasks &
      >Hhub_model &
      Htasks
    )".
  #[local] Definition inv_1 γ : iProp Σ :=
    inv (nroot.@"inv") (inv_inner γ).
  #[local] Definition inv_2 γ : iProp Σ :=
    ws_hub_std_inv γ.(metadata_hub) (nroot.@"hub") (S γ.(metadata_size)) ∗
    inv_1 γ.
  #[local] Instance : CustomIpatFormat "inv_2" :=
    "(
      #Hhub_inv{_{}} &
      #Hinv{_{}}
    )".
  Definition pool_inv t sz : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜sz = γ.(metadata_size)⌝ ∗
    inv_2 γ.
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l{} &
      %γ{} &
      {%Heq{};->} &
      #Hmeta{_{}} &
      -> &
      {#Hinv{};(:inv_2)}
    )".

  Definition pool_model t : iProp Σ :=
    ∃ l γ empty doms,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[size] ↦□ #γ.(metadata_size) ∗
    l.[hub] ↦□ γ.(metadata_hub) ∗
    l.[domains] ↦□ γ.(metadata_domains) ∗
    inv_2 γ ∗
    ws_hub_std_owner γ.(metadata_hub) 0 Blocked empty ∗
    array_model γ.(metadata_domains) DfracDiscarded doms ∗
    [∗ list] dom ∈ doms,
      domain_model dom itype_unit.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l{} &
      %γ{} &
      %empty{} &
      %doms{} &
      {%Heq{};->} &
      #Hmeta{_{}} &
      #Hl{}_size &
      #Hl{}_hub &
      #Hl{}_domains &
      {#Hinv{};(:inv_2)} &
      Hhub{}_owner &
      Hdomains{} &
      Hdoms{}
    )".

  #[local] Definition context_1 γ 𝑐𝑡𝑥 : iProp Σ :=
    ∃ empty,
    ws_hub_std_owner 𝑐𝑡𝑥.(context_hub) 𝑐𝑡𝑥.(context_id) Nonblocked empty.
  #[local] Instance : CustomIpatFormat "context_1" :=
    "(
      %empty{} &
      Hhub_owner
    )".
  #[local] Definition context_2 γ 𝑐𝑡𝑥 : iProp Σ :=
    ⌜context_consistent γ 𝑐𝑡𝑥⌝ ∗
    inv_2 γ ∗
    context_1 γ 𝑐𝑡𝑥.
  #[local] Instance : CustomIpatFormat "context_2" :=
    "(
      (:context_consistent {//}) &
      {#Hinv_{};(:inv_2)} &
      { {lazy} H𝑐𝑡𝑥{}
      ; {lazy} H𝑐𝑡𝑥
      ; (:context_1 ={})
      ; (:context_1)
      }
    )".
  Definition pool_context t ctx : iProp Σ :=
    ∃ l γ 𝑐𝑡𝑥,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜ctx = 𝑐𝑡𝑥⌝ ∗
    context_2 γ 𝑐𝑡𝑥.
  #[local] Instance : CustomIpatFormat "context" :=
    "(
      %l{} &
      %γ{} &
      %𝑐𝑡𝑥{} &
      {%Heq{};->} &
      #Hmeta{_{}} &
      {%H𝑐𝑡𝑥{}_eq;->} &
      (:context_2 {//} {/lazy/})
    )".

  Definition pool_future_inv t fut Ψ Ξ :=
    ivar_3_inv fut Ψ Ξ (λ fut waiter,
      ∀ ctx v,
      pool_context t ctx -∗
      ivar_3_result fut v -∗
      WP waiter ctx v {{ res,
        ⌜res = ()%V⌝ ∗
        pool_context t ctx
      }}
    )%I.

  Definition pool_future_consumer :=
    ivar_3_consumer.

  Definition pool_future_result :=
    ivar_3_result.

  #[global] Instance pool_future_proper t fut :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (pool_future_inv t fut).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance pool_future_result_timeless fut v :
    Timeless (pool_future_result fut v).
  Proof.
    apply _.
  Qed.
  #[global] Instance pool_future_inv_persistent t fut Ψ Ξ :
    Persistent (pool_future_inv t fut Ψ Ξ).
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
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. done.
  Qed.

  Lemma pool_future_consumer_divide {t fut Ψ Ξ Χ} Χs :
    pool_future_inv t fut Ψ Ξ -∗
    pool_future_consumer fut Χ -∗
    (∀ x, Χ x -∗ [∗ list] Χ ∈ Χs, Χ x) ={⊤}=∗
    [∗ list] Χ ∈ Χs, pool_future_consumer fut Χ.
  Proof.
    apply ivar_3_consumer_divide.
  Qed.
  Lemma pool_future_consumer_split {t fut Ψ Χ Ξ} Χ1 Χ2 :
    pool_future_inv t fut Ψ Ξ -∗
    pool_future_consumer fut Χ -∗
    (∀ v, Χ v -∗ Χ1 v ∗ Χ2 v) ={⊤}=∗
      pool_future_consumer fut Χ1 ∗
      pool_future_consumer fut Χ2.
  Proof.
    apply ivar_3_consumer_split.
  Qed.

  Lemma pool_future_result_agree fut v1 v2 :
    pool_future_result fut v1 -∗
    pool_future_result fut v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_3_result_agree.
  Qed.

  Lemma pool_future_inv_result t fut Ψ Ξ v :
    pool_future_inv t fut Ψ Ξ -∗
    pool_future_result fut v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    apply ivar_3_inv_result.
  Qed.
  Lemma pool_future_inv_result' t fut Ψ Ξ v :
    £ 1 -∗
    pool_future_inv t fut Ψ Ξ -∗
    pool_future_result fut v ={⊤}=∗
    □ Ξ v.
  Proof.
    apply ivar_3_inv_result'.
  Qed.
  Lemma pool_future_inv_result_consumer t fut Ψ Ξ v Χ :
    pool_future_inv t fut Ψ Ξ -∗
    pool_future_result fut v -∗
    pool_future_consumer fut Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    apply ivar_3_inv_result_consumer.
  Qed.
  Lemma pool_future_inv_result_consumer' t fut Ψ Ξ v Χ :
    £ 2 -∗
    pool_future_inv t fut Ψ Ξ -∗
    pool_future_result fut v -∗
    pool_future_consumer fut Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    apply ivar_3_inv_result_consumer'.
  Qed.

  #[local] Lemma pool_execute_spec γ 𝑐𝑡𝑥 task Ψ :
    {{{
      context_2 γ 𝑐𝑡𝑥 ∗
      task_model γ task Ψ
    }}}
      pool_execute 𝑐𝑡𝑥 task
    {{{ v,
      RET v;
      context_1 γ 𝑐𝑡𝑥 ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:context_2) & Htask) HΦ".

    wp_rec.
    wp_smart_apply (wp_wand with "(Htask [//] [Hhub_owner])").
    { rewrite H𝑐𝑡𝑥_hub //. }
    rewrite H𝑐𝑡𝑥_hub. iStepFrameSteps 3.
  Qed.

  #[local] Lemma pool_worker_spec {γ ctx} 𝑐𝑡𝑥 :
    ctx = 𝑐𝑡𝑥 →
    {{{
      context_2 γ 𝑐𝑡𝑥
    }}}
      pool_worker ctx
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros (->) "%Φ (:context_2 lazy=) HΦ".
    iLöb as "HLöb".
    iDestruct "H𝑐𝑡𝑥" as "(:context_1)".

    wp_rec. rewrite pool_max_round_noyield pool_max_round_yield.
    wp_pures. rewrite -H𝑐𝑡𝑥_hub.

    awp_apply (ws_hub_std_pop_steal_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; [done | lia.. |].
    iInv "Hinv" as "(:inv_inner)".
    iAaccIntro with "Hhub_model"; first iSteps. iIntros ([task |]) "Hhub_model !>".

    - iDestruct "Hhub_model" as "(%tasks' & -> & Hhub_model)".
      iDestruct (big_sepMS_disj_union with "Htasks") as "(Htask & Htasks)".
      rewrite big_sepMS_singleton.
      iSplitR "Htask"; first iSteps.
      clear empty. iIntros "%empty (Hhub_owner & _) HΦ".

      wp_smart_apply (pool_execute_spec with "[Hhub_owner $Htask]") as (res) "(H𝑐𝑡𝑥 & _)".
      { iStep 2. rewrite H𝑐𝑡𝑥_hub. iFrame. }
      wp_smart_apply ("HLöb" with "H𝑐𝑡𝑥 HΦ").

    - iSplitL; first iSteps.
      clear empty. iIntros "%empty (Hhub_owner & ->) HΦ".

      wp_pures. rewrite -H𝑐𝑡𝑥_hub.
      wp_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]"); first done.
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

    wp_rec. rewrite /pool__code.pool_context.

    wp_smart_apply (ws_hub_std_create_spec with "[//]") as (hub) "(#Hhub_inv & Hhub_model & Hhub_owners)"; first lia.
    rewrite Z2Nat.inj_add // Nat.add_1_r.
    iDestruct (big_sepL_seq_cons_1 with "Hhub_owners") as "(Hhub_owner & Hhub_owners)".

    wp_smart_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.

    pose γ 𝑑𝑜𝑚𝑠 := {|
      metadata_size := ₊sz ;
      metadata_hub := hub ;
      metadata_domains := 𝑑𝑜𝑚𝑠 ;
    |}.

    wp_smart_apply (array_unsafe_initi_spec_disentangled_strong'
      (λ 𝑑𝑜𝑚𝑠, inv_1 (γ 𝑑𝑜𝑚𝑠))
      (λ _ dom, domain_model dom itype_unit)
    with "[Hhub_model Hhub_owners]") as (𝑑𝑜𝑚𝑠 doms) "(_ & Hdomains & #Hinv & Hdoms)"; first done.
    { iSplitL "Hhub_model".

      - iIntros "!> %𝑑𝑜𝑚𝑠".
        iApply inv_alloc.
        iFrame. rewrite big_sepMS_empty //.

      - iApply (big_sepL_impl_strong with "Hhub_owners").
        { simpl_length. }
        iIntros "!>" (k i1 i2 (-> & Hi1)%lookup_seq (-> & Hi2)%lookup_seq) "Hhub_owner %𝑑𝑜𝑚𝑠 #Hinv".

        wp_smart_apply (domain_spawn_spec itype_unit with "[Hhub_owner]"); last iSteps. iIntros "%tid _".
        iApply wp_thread_id_mono.

        pose 𝑐𝑡𝑥 := {|
          context_size := ₊sz ;
          context_hub := hub ;
          context_id := S k ;
        |}.
        wp_smart_apply (pool_worker_spec 𝑐𝑡𝑥 with "[$Hinv $Hhub_owner]"); [| iSteps..].
        { rewrite /context_to_val /=. repeat f_equal; lia. }
    }
    iMod (array_model_persist with "Hdomains") as "#Hdomains".

    wp_block l as "Hmeta" "(Hl_size & Hl_hub & Hl_domains & _)".
    iMod (pointsto_persist with "Hl_size") as "#Hl_size".
    iMod (pointsto_persist with "Hl_hub") as "#Hl_hub".
    iMod (pointsto_persist with "Hl_domains") as "#Hl_domains".

    iMod (meta_set (γ 𝑑𝑜𝑚𝑠) with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.

  Lemma pool_run_spec Ψ t task :
    {{{
      pool_model t ∗
      ( ∀ ctx,
        pool_context t ctx -∗
        WP task ctx {{ v,
          pool_context t ctx ∗
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

    wp_rec. rewrite /pool__code.pool_context.
    wp_load.
    wp_apply (ws_hub_std_unblock_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
    do 2 wp_load.

    pose 𝑐𝑡𝑥 := {|
      context_size := γ.(metadata_size) ;
      context_hub := γ.(metadata_hub) ;
      context_id := 0 ;
    |}.
    wp_smart_apply (pool_execute_spec _ 𝑐𝑡𝑥 _ Ψ with "[$Hhub_owner Htask]") as (v) "{%} ((:context_1 =1) & HΨ)".
    { iSplit.
      - iFrame "#" => //.
      - iIntros "{%} %𝑐𝑡𝑥 %empty (:context_consistent) Hhub_owner".
        wp_apply (wp_wand with "(Htask [Hhub_owner])") as (v) "((:context =1) & $)".
        { iStep 5. rewrite H𝑐𝑡𝑥_hub. iFrame. }
        apply (inj context_to_val) in H𝑐𝑡𝑥1_eq as <-.
        rewrite H𝑐𝑡𝑥_hub. iSteps.
    }

    wp_load.
    wp_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
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

    wp_rec. wp_load.
    wp_smart_apply (ws_hub_std_kill_spec with "Hhub_inv") as "_".
    wp_load.
    wp_smart_apply (array_iter_spec_disentangled' (λ _ _, True)%I with "[$Hdomains Hdoms]"); last iSteps.
    iApply (big_sepL_impl with "Hdoms"). iIntros "!> %i %dom _ Hdom".
    wp_apply (domain_join_spec with "Hdom").
    iSteps.
  Qed.

  Lemma pool_size_spec t sz ctx :
    {{{
      pool_inv t sz ∗
      pool_context t ctx
    }}}
      pool_size ctx
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:context =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
    rewrite H𝑐𝑡𝑥2_size. iSteps.
  Qed.

  Lemma pool_async_silent_spec t ctx task :
    {{{
      pool_context t ctx ∗
      ( ∀ ctx,
        pool_context t ctx -∗
        WP task ctx {{ res,
          pool_context t ctx
        }}
      )
    }}}
      pool_async_silent ctx task
    {{{
      RET ();
      pool_context t ctx
    }}}.
  Proof.
    iIntros "%Φ ((:context) & Htask) HΦ".

    wp_rec.
    wp_pures. rewrite -H𝑐𝑡𝑥_hub.

    awp_apply (ws_hub_std_push_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; first done.
    iInv "Hinv" as "(:inv_inner)".
    iAaccIntro with "Hhub_model"; first iFrameSteps. iIntros "Hhub_model !>".
    iSplitL.
    { iFrame. rewrite big_sepMS_singleton.
      iIntros "{%} !> %𝑐𝑡𝑥 %empty (:context_consistent) Hhub_owner".
      wp_apply (wp_wand with "(Htask [Hhub_owner])") as (res) "(:context =1)".
      { iStep 5. rewrite H𝑐𝑡𝑥_hub. iFrame. }
      apply (inj context_to_val) in H𝑐𝑡𝑥1_eq as <-.
      rewrite H𝑐𝑡𝑥_hub. iSteps.
    }
    iIntros "Hhub_owner HΦ".

    iStep 6. rewrite H𝑐𝑡𝑥_hub. iFrame.
  Qed.

  Lemma pool_async_spec Ψ Ξ t ctx task :
    {{{
      pool_context t ctx ∗
      ( ∀ ctx,
        pool_context t ctx -∗
        WP task ctx {{ v,
          pool_context t ctx ∗
          ▷ Ψ v ∗
          ▷ □ Ξ v
        }}
      )
    }}}
      pool_async ctx task
    {{{ fut,
      RET fut;
      pool_context t ctx ∗
      pool_future_inv t fut Ψ Ξ ∗
      pool_future_consumer fut Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Htask) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_create_spec Ψ Ξ with "[//]") as (ivar) "(#Hivar_inv & Hivar_producer & Hivar_consumer)".

    wp_smart_apply (pool_async_silent_spec with "[$Hctx Htask Hivar_producer]") as "Hctx".
    { clear ctx. iIntros "%ctx Hctx".

      wp_smart_apply (wp_wand with "(Htask Hctx)") as (v) "(Hctx & HΨ & HΞ)".
      wp_smart_apply (ivar_3_set_spec with "[$Hivar_inv $Hivar_producer $HΨ $HΞ]") as (waiters) "(#Hivar_result & Hwaiters)".
      wp_smart_apply (lst_iter_spec' (λ _ _, pool_context t ctx)%I with "[$Hctx Hwaiters]") as "$"; try done.

      iApply (big_sepL_impl with "Hwaiters").
      iIntros "!> %i %waiter %Hwaiters_lookup Hwaiter Hctx".
      wp_smart_apply (wp_wand with "(Hwaiter [$] [$])") as (res) "(-> & $) //".
    }

    wp_pures.

    iApply ("HΦ" with "[$]").
  Qed.

  Lemma pool_wait_until_spec P t ctx pred :
    {{{
      pool_context t ctx ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    }}}
      pool_wait_until ctx pred
    {{{
      RET ();
      pool_context t ctx ∗
      P
    }}}.
  Proof.
    iIntros "%Φ ((:context lazy=) & #Hpred) HΦ".
    iLöb as "HLöb".
    iDestruct "H𝑐𝑡𝑥" as "(:context_1)".

    wp_rec. rewrite pool_max_round_noyield.
    wp_smart_apply (wp_wand with "Hpred") as (res) "(%b & -> & HP)".
    destruct b; first iStepFrameSteps 8.

    awp_smart_apply (ws_hub_std_pop_steal_until_spec P with "[$Hhub_owner $Hpred]") without "HΦ".
    { lia. }
    { lia. }
    { rewrite H𝑐𝑡𝑥_hub //. }
    iInv "Hinv" as "(:inv_inner)".
    rewrite -H𝑐𝑡𝑥_hub.
    iAaccIntro with "Hhub_model"; first iSteps. iIntros ([task |]) "Hhub_model !>"; last first.
    { iStep 9. iFrame "#∗". rewrite H𝑐𝑡𝑥_hub. iFrameSteps. }
    iDestruct "Hhub_model" as "(%tasks' & -> & Hhub_model)".
    iDestruct (big_sepMS_insert with "Htasks") as "(Htask & Htasks')".
    iSplitR "Htask"; first iSteps.
    clear empty. iIntros "%empty (Hhub_owner & _) HΦ".

    wp_smart_apply (pool_execute_spec with "[Hhub_owner $Htask]") as (res) "(H𝑐𝑡𝑥 & _)".
    { iStep 2. rewrite H𝑐𝑡𝑥_hub. iFrame. }

    wp_smart_apply ("HLöb" with "H𝑐𝑡𝑥 HΦ").
  Qed.

  Lemma pool_wait_while_spec P t ctx pred :
    {{{
      pool_context t ctx ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then True else P
      }}
    }}}
      pool_wait_while ctx pred
    {{{
      RET ();
      pool_context t ctx ∗
      P
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hpred) HΦ".

    wp_rec.
    wp_smart_apply (pool_wait_until_spec with "[$Hctx] HΦ"). iModIntro.
    wp_smart_apply (wp_wand with "Hpred") as (res) "(%b & -> & HP)".
    destruct b; iSteps.
  Qed.

  Lemma pool_wait_spec t ctx fut Ψ Ξ :
    {{{
      pool_context t ctx ∗
      pool_future_inv t fut Ψ Ξ
    }}}
      pool_wait ctx fut
    {{{ v,
      RET v;
      £ 2 ∗
      pool_context t ctx ∗
      pool_future_result fut v
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hivar_inv) HΦ".

    wp_rec.
    wp_smart_apply (pool_wait_until_spec (ivar_3_determined fut)%I with "[$Hctx]") as "(Hctx & %v & #Hivar_result)".
    { iModIntro.
      wp_smart_apply (ivar_3_is_set_spec with "Hivar_inv") as (b) "Hivar_result".
      rewrite /ivar_3_determined. destruct b; iSteps.
    }
    wp_smart_apply (ivar_3_get_spec with "[$Hivar_inv $Hivar_result]") as "H£".
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma pool_iter_spec t ctx fut Ψ Ξ fn :
    {{{
      pool_context t ctx ∗
      pool_future_inv t fut Ψ Ξ ∗
      ( ∀ ctx v,
        pool_context t ctx -∗
        pool_future_result fut v -∗
        WP fn ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context t ctx
        }}
      )
    }}}
      pool_iter ctx fut fn
    {{{
      RET ();
      pool_context t ctx
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hivar_inv & Hfn) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_wait_spec with "[$Hivar_inv $Hfn]") as ([v |]) "H".
    all: wp_pures.

    - iDestruct "H" as "(_ & #Hivar_result & Hfn)".
      wp_apply (wp_wand with "(Hfn Hctx Hivar_result)") as (res) "(-> & Hctx)".
      iApply ("HΦ" with "Hctx").

    - iApply ("HΦ" with "Hctx").
  Qed.

  Lemma pool_map_spec {t ctx fut1 Ψ1 Ξ1} Ψ2 Ξ2 fn :
    {{{
      pool_context t ctx ∗
      pool_future_inv t fut1 Ψ1 Ξ1 ∗
      ( ∀ ctx v1,
        pool_context t ctx -∗
        pool_future_result fut1 v1 -∗
        WP fn ctx v1 {{ v2,
          pool_context t ctx ∗
          ▷ Ψ2 v2 ∗
          ▷ □ Ξ2 v2
        }}
      )
    }}}
      pool_map ctx fut1 fn
    {{{ fut2,
      RET fut2;
      pool_context t ctx ∗
      pool_future_inv t fut2 Ψ2 Ξ2 ∗
      pool_future_consumer fut2 Ψ2
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hfut1_inv & Hfn) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_create_spec Ψ2 Ξ2 with "[//]") as (fut2) "(#Hivar2_inv & Hivar2_producer & Hivar2_consumer)".

    wp_smart_apply (pool_iter_spec with "[$Hctx $Hfut1_inv Hfn Hivar2_producer]") as "Hctx".
    { clear ctx. iIntros "%ctx %v1 Hctx #Hfut1_result".
      wp_smart_apply (wp_wand with "(Hfn Hctx Hfut1_result)") as (v2) "(Hctx & HΨ2 & HΞ2)".
      wp_smart_apply (ivar_3_set_spec with "[$Hivar2_inv $Hivar2_producer $HΨ2 $HΞ2]") as (waiters) "(#Hivar2_result & Hwaiters)".
      wp_smart_apply (lst_iter_spec' (λ _ _, pool_context t ctx)%I with "[$Hctx Hwaiters]") as "$"; try done.
      iApply (big_sepL_impl with "Hwaiters").
      iIntros "!> %i %waiter %Hwaiters_lookup Hwaiter Hctx".
      wp_smart_apply (wp_wand with "(Hwaiter [$] [$])") as (res) "(-> & $) //".
    }

    wp_pures.

    iApply ("HΦ" with "[$]").
  Qed.
End pool_G.

From zoo_parabs Require
  pool__opaque.

#[global] Opaque pool_inv.
#[global] Opaque pool_model.
#[global] Opaque pool_context.
#[global] Opaque pool_future_inv.
#[global] Opaque pool_future_consumer.
#[global] Opaque pool_future_result.
