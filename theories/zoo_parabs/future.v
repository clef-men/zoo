From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.saved_prop.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  ivar_3
  lst.
From zoo_parabs Require Export
  base
  future__code.
From zoo_parabs Require Import
  pool.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types depth : nat.
Implicit Types v t pool ctx task waiter : val.
Implicit Types scope : pool_scope.
Implicit Types ω : gname.
Implicit Types ωs : list gname.

Class FutureG Σ `{pool_G : PoolG Σ} := {
  #[local] future_G_ivar_G :: Ivar3G Σ gname ;
  #[local] future_G_saved_prop_G :: SavedPropG Σ ;
}.

Definition future_Σ := #[
  ivar_3_Σ gname ;
  saved_prop_Σ
].
#[global] Instance subG_future_Σ Σ `{pool_G : PoolG Σ} :
  subG future_Σ Σ →
  FutureG Σ.
Proof.
  solve_inG.
Qed.

Section future_G.
  Context `{future_G : FutureG Σ}.

  Implicit Types P : iProp Σ.
  Implicit Types Ψ Χ Ξ : val → iProp Σ.

  #[local] Definition waiter_model pool t waiter ω : iProp Σ :=
    ∀ ctx scope v,
    pool_context pool ctx scope -∗
    ivar_3_result t v -∗
    WP waiter ctx v {{ res,
      ∃ P,
      ⌜res = ()%V⌝ ∗
      pool_context pool ctx scope ∗
      saved_prop ω P ∗
      ▷ □ P
    }}.

  #[local] Definition receipt_1 t : iProp Σ :=
    ∃ waiters ωs,
    ivar_3_resolved t ∗
    ivar_3_waiters t waiters ωs ∗
    [∗ list] ω ∈ ωs,
      ∃ P,
      saved_prop ω P ∗
      □ P.
  #[local] Instance : CustomIpat "receipt_1" :=
    " ( %waiters &
        %ωs &
        #H{{}_}resolved &
        #H{{}_}waiters &
        #Hωs
      )
    ".
  #[local] Definition receipt_2 pool t :=
    pool_obligation pool (receipt_1 t).

  Fixpoint future_inv pool t depth Ψ Ξ : iProp Σ :=
    ivar_3_inv t Ψ Ξ (waiter_model pool) ∗
    ( receipt_1 t
    ∨ receipt_2 pool t
    ∨ match depth with
      | 0 =>
          False
      | S depth =>
          ∃ parent Ψ_parent Ξ_parent waiter ω,
          future_inv pool parent depth Ψ_parent Ξ_parent ∗
          ivar_3_waiter parent waiter ω ∗
          saved_prop ω (receipt_2 pool t)
      end
    ).
  #[local] Instance : CustomIpat "inv" :=
    " ( #H{{}_}inv &
        H{{}_}receipt
      )
    ".

  Definition obligation' pool depth P : iProp Σ :=
    ∃ t Ψ Ξ waiter ω,
    future_inv pool t depth Ψ Ξ ∗
    ivar_3_waiter t waiter ω ∗
    saved_prop ω P.
  #[local] Instance : CustomIpat "obligation'" :=
    " ( %{;t} &
        %Ψ{_{}} &
        %Ξ{_{}} &
        %waiter &
        %ω &
        #H{{}_}inv &
        #H{{}_}waiter &
        #Hω
      )
    ".
  Definition future_obligation pool depth P : iProp Σ :=
      □ P
    ∨ obligation' pool depth P.
  #[local] Instance : CustomIpat "obligation" :=
    " [ #HP
      | Hobligation
      ]
    ".

  #[local] Definition receipt_3 pool t depth : iProp Σ :=
      receipt_1 t
    ∨ receipt_2 pool t
    ∨ match depth with
      | 0 =>
          False
      | S depth =>
          obligation' pool depth (receipt_2 pool t)
      end.
  #[local] Instance : CustomIpat "receipt_3" :=
    " [ H{{}_}receipt
      | [ H{{}_}receipt
        | H{{}_}receipt
        ]
      ]
    ".

  Definition future_consumer :=
    ivar_3_consumer.

  Definition future_result :=
    ivar_3_result.
  Definition future_resolved t : iProp Σ :=
    ∃ v,
    future_result t v.

  #[global] Instance future_inv_proper pool t depth :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (future_inv pool t depth).
  Proof.
    destruct depth; solve_proper.
  Qed.

  #[global] Instance future_result_timeless t v :
    Timeless (future_result t v).
  Proof.
    apply _.
  Qed.

  #[global] Instance future_inv_persistent pool t depth Ψ Ξ :
    Persistent (future_inv pool t depth Ψ Ξ).
  Proof.
    move: t Ψ Ξ. induction depth; apply _.
  Qed.
  #[global] Instance future_obligation_persistent pool depth P :
    Persistent (future_obligation pool depth P).
  Proof.
    apply _.
  Qed.
  #[global] Instance future_result_persistent t v :
    Persistent (future_result t v).
  Proof.
    apply _.
  Qed.

  #[local] Lemma future_inv_unfold pool t depth Ψ Ξ :
    future_inv pool t depth Ψ Ξ ⊣⊢
      ivar_3_inv t Ψ Ξ (waiter_model pool) ∗
      receipt_3 pool t depth.
  Proof.
    destruct depth as [| depth].
    all: iSplit.
    all: iIntros "(:inv)".
    all: iFrame "#∗".
  Qed.

  #[local] Lemma future_inv_finished_receipt pool t depth Ψ Ξ :
    future_inv pool t depth Ψ Ξ -∗
    pool_finished pool -∗
    ▷^(2 * depth + 1) receipt_1 t.
  Proof.
    iInduction depth as [| depth] "IH" forall (t Ψ Ξ).
    all: rewrite future_inv_unfold.
    all: iIntros "(:inv =t) #Hpool_finished".
    all: iDestruct "Ht_receipt" as "(:receipt_3 =t)"; try done.

    - iDestruct (pool_obligation_finished with "Ht_receipt Hpool_finished") as "Ht_receipt".
      iNext => //.

    - iDestruct (pool_obligation_finished with "Ht_receipt Hpool_finished") as "Hreceipt".
      iNext => //.

    - iDestruct "Ht_receipt" as "(:obligation' =parent)".

      iDestruct ("IH" with "Hparent_inv Hpool_finished") as "(:receipt_1 =parent)".

      iEval (replace (2 * S depth + 1) with (2 * depth + 1 + 2) by lia).
      iEval (rewrite bi.laterN_add).
      iNext.

      iDestruct (ivar_3_waiter_valid with "Hparent_waiters Hparent_waiter") as %(i & _ & Hωs_lookup).
      iDestruct (big_sepL_lookup with "Hωs") as "(%P & Hω_ & -#Hreceipt)"; first done.
      iDestruct (saved_prop_agree with "Hω Hω_") as "Heq".
      iNext.
      iRewrite -"Heq" in "Hreceipt".

      iDestruct (pool_obligation_finished with "Hreceipt Hpool_finished") as "Hreceipt".
      iNext => //.
  Qed.
  Lemma future_inv_finished pool t depth Ψ Ξ :
    future_inv pool t depth Ψ Ξ -∗
    pool_finished pool -∗
    ▷^(2 * depth + 1) future_resolved t.
  Proof.
    iIntros "Hinv Hpool_finished".
    iDestruct (future_inv_finished_receipt with "Hinv Hpool_finished") as "(:receipt_1)".
    auto.
  Qed.

  Lemma future_obligation_finished pool depth P :
    future_obligation pool depth P -∗
    pool_finished pool -∗
    ▷^(2 * depth + 2) □ P.
  Proof.
    iIntros "(:obligation) Hpool_finished //".
    iDestruct "Hobligation" as "(:obligation')".

    iDestruct (future_inv_finished_receipt with "Hinv Hpool_finished") as "(:receipt_1)".

    iEval (replace (2 * depth + 2) with (2 * depth + 1 + 1) by lia).
    iEval (rewrite bi.laterN_add).
    iNext.

    iDestruct (ivar_3_waiter_valid with "Hwaiters Hwaiter") as %(i & _ & Hωs_lookup).
    iDestruct (big_sepL_lookup with "Hωs") as "(%P_ & Hω_ & HP)"; first done.
    iDestruct (saved_prop_agree with "Hω Hω_") as "Heq".
    iNext.
    iRewrite -"Heq" in "HP" => //.
  Qed.

  Lemma future_consumer_divide {pool t depth Ψ Ξ Χ} Χs :
    future_inv pool t depth Ψ Ξ -∗
    future_consumer t Χ -∗
    (∀ x, Χ x -∗ [∗ list] Χ ∈ Χs, Χ x) ={⊤}=∗
    [∗ list] Χ ∈ Χs, future_consumer t Χ.
  Proof.
    rewrite future_inv_unfold.
    iIntros "(:inv)".
    iApply (ivar_3_consumer_divide with "Hinv").
  Qed.
  Lemma future_consumer_split {pool t depth Ψ Χ Ξ} Χ1 Χ2 :
    future_inv pool t depth Ψ Ξ -∗
    future_consumer t Χ -∗
    (∀ v, Χ v -∗ Χ1 v ∗ Χ2 v) ={⊤}=∗
      future_consumer t Χ1 ∗
      future_consumer t Χ2.
  Proof.
    rewrite future_inv_unfold.
    iIntros "(:inv)".
    iApply (ivar_3_consumer_split with "Hinv").
  Qed.

  Lemma future_result_agree t v1 v2 :
    future_result t v1 -∗
    future_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_3_result_agree.
  Qed.

  Lemma future_inv_result pool t depth Ψ Ξ v :
    future_inv pool t depth Ψ Ξ -∗
    future_result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    rewrite future_inv_unfold.
    iIntros "(:inv) Hresult".
    iApply (ivar_3_inv_result with "Hinv Hresult").
  Qed.
  Lemma future_inv_result' pool t depth Ψ Ξ v :
    £ 1 -∗
    future_inv pool t depth Ψ Ξ -∗
    future_result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hfut_inv Hfut_result".
    iMod (future_inv_result with "Hfut_inv Hfut_result") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma future_inv_result_consumer pool t depth Ψ Ξ v Χ :
    future_inv pool t depth Ψ Ξ -∗
    future_result t v -∗
    future_consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    rewrite future_inv_unfold.
    iIntros "(:inv) Hresult Hconsumer".
    iApply (ivar_3_inv_result_consumer with "Hinv Hresult Hconsumer").
  Qed.
  Lemma future_inv_result_consumer' pool t depth Ψ Ξ v Χ :
    £ 2 -∗
    future_inv pool t depth Ψ Ξ -∗
    future_result t v -∗
    future_consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hfut_inv Hfut_result Hfut_consumer".
    iMod (future_inv_result_consumer with "Hfut_inv Hfut_result Hfut_consumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma future_return_spec pool Ψ Ξ v :
    {{{
      Ψ v ∗
      □ Ξ v
    }}}
      future_return v
    {{{ t,
      RET t;
      future_inv pool t 0 Ψ Ξ ∗
      future_consumer t Ψ ∗
      future_result t v
    }}}.
  Proof.
    iIntros "%Φ (HΨ & HΞ) HΦ".

    wp_apply (ivar_3_make_spec Ψ Ξ with "[$]") as (t) "(#Hinv & Hconsumer & #Hresult & Hwaiters)".
    iApply "HΦ".
    iFrame "#∗". auto.
  Qed.

  #[local] Lemma future_set_spec pool ctx scope t Ψ Ξ v :
    {{{
      pool_context pool ctx scope ∗
      ivar_3_inv t Ψ Ξ (waiter_model pool) ∗
      ivar_3_producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      future_set ctx t v
    {{{
      RET ();
      pool_context pool ctx scope ∗
      receipt_1 t
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hinv & Hproducer & HΨ & HΞ) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_set_spec with "[$Hinv $Hproducer $HΨ $HΞ]") as (waiters ωs) "(#Hresult & #Hwaiters & Hwaiter_models)".

    iDestruct (big_sepL2_length with "Hwaiter_models") as %Hlength.

    wp_smart_apply (lst_iter_spec (λ i _,
      pool_context pool ctx scope ∗
      ( [∗ list] ω ∈ take i ωs,
        ∃ P,
        saved_prop ω P ∗
        □ P
      ) ∗
      ( [∗ list] waiter; ω ∈ drop i waiters; drop i ωs,
        waiter_model pool t waiter ω
      )
    )%I with "[$Hctx Hwaiter_models]") as "(Hctx & #Hωs & _)"; first done.
    { iStep.
      iIntros "!> %i %waiter %Hwaiters_lookup (Hctx & Hωs & Hwaiter_models)".

      iEval (rewrite (drop_S waiters waiter) //) in "Hwaiter_models".
      iDestruct (big_sepL2_cons_inv_l with "Hwaiter_models") as "(%ω & %ωs' & %Heq & Hwaiter_model & Hwaiter_models)".
      apply drop_cons_inv in Heq as (Hωs_lookup & ->).

      wp_smart_apply (wp_wand with "(Hwaiter_model Hctx Hresult)") as (res) "(%P & -> & $ & Hω & HP)".

      iFrameStep.
      iEval (rewrite (take_S_r _ _ ω) //).
      iApply big_sepL_snoc.
      iFrame.
    }
    iEval (rewrite Hlength firstn_all) in "Hωs".

    iApply "HΦ".
    iFrame "#∗".
  Qed.

  Lemma future_async_spec Ψ Ξ pool ctx scope task :
    {{{
      pool_context pool ctx scope ∗
      ( ∀ ctx scope,
        pool_context pool ctx scope -∗
        WP task ctx {{ v,
          pool_context pool ctx scope ∗
          ▷ Ψ v ∗
          ▷ □ Ξ v
        }}
      )
    }}}
      future_async ctx task
    {{{ t,
      RET t;
      pool_context pool ctx scope ∗
      future_inv pool t 0 Ψ Ξ ∗
      future_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Htask) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_create_spec Ψ Ξ (waiter_model pool) with "[//]") as (t) "(#Hinv & Hproducer & Hconsumer)".

    wp_smart_apply (pool_async_spec (
      receipt_1 t
    ) with "[$Hctx Htask Hproducer]") as "(Hctx & Hreceipt)".
    { iIntros "{%} %ctx %scope Hctx".
      wp_smart_apply (wp_wand with "(Htask Hctx)") as (v) "(Hctx & HΨ & HΞ)".
      wp_apply (future_set_spec with "[$]") as "($ & #$)".
    }

    iSteps.
  Qed.

  Lemma future_wait_spec pool ctx scope t depth Ψ Ξ :
    {{{
      pool_context pool ctx scope ∗
      future_inv pool t depth Ψ Ξ
    }}}
      future_wait ctx t
    {{{ v,
      RET v;
      £ 2 ∗
      pool_context pool ctx scope ∗
      future_result t v
    }}}.
  Proof.
    setoid_rewrite future_inv_unfold.
    iIntros "%Φ (Hctx & (:inv)) HΦ".

    wp_rec.

    wp_smart_apply (pool_wait_until_spec (
      ivar_3_resolved t
    )%I with "[$Hctx]") as "(Hctx & %v & #Hresult)".
    { iModIntro.
      wp_smart_apply (ivar_3_is_set_spec with "Hinv") as (b) "Hresult".
      rewrite /ivar_3_resolved. destruct b; iSteps.
    }

    wp_smart_apply (ivar_3_get_spec with "[$Hinv $Hresult]") as "H£".
    iSteps.
  Qed.

  Lemma future_iter_spec P pool ctx scope t depth Ψ Ξ task :
    {{{
      pool_context pool ctx scope ∗
      future_inv pool t depth Ψ Ξ ∗
      ( ∀ ctx scope v,
        pool_context pool ctx scope -∗
        future_result t v -∗
        WP task ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          ▷ □ P
        }}
      )
    }}}
      future_iter ctx t task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      future_obligation pool depth P
    }}}.
  Proof.
    setoid_rewrite future_inv_unfold.
    iIntros "%Φ (Hctx & (:inv) & Htask) HΦ".

    wp_rec credit:"H£".

    iMod (saved_prop_alloc P) as "(%ω & #Hω)".
    wp_smart_apply (ivar_3_wait_spec ω with "[$Hinv Htask]") as ([v |]) "H".
    { iIntros "{%} !> %ctx %scope %v Hctx #Hresult".
      wp_apply (wp_wand with "(Htask Hctx Hresult)").
      iSteps.
    }

    - iDestruct "H" as "(_ & #Hresult & Hwaiter_model)".

      iApply wp_fupd.
      wp_smart_apply (wp_wand with "(Hwaiter_model Hctx Hresult)") as (res) "(%P_ & -> & Hctx & Hω_ & HP)".

      iApply "HΦ".
      iDestruct (saved_prop_agree with "Hω Hω_") as "Heq".
      iMod (lc_fupd_elim_later with "H£ [HP Heq]") as "H".
      { iNext. iAccu. }
      iDestruct "H" as "(#HP & Heq)".
      iRewrite -"Heq" in "HP".
      iFrameSteps.

    - wp_pures.

      iApply "HΦ".
      iFrame. iRight. iExists t, Ψ, Ξ, task, ω.
      rewrite future_inv_unfold. iFrameSteps.
  Qed.

  Lemma future_map_spec {pool ctx scope t1 depth Ψ1 Ξ1} Ψ2 Ξ2 task :
    {{{
      pool_context pool ctx scope ∗
      future_inv pool t1 depth Ψ1 Ξ1 ∗
      ( ∀ ctx scope v1,
        pool_context pool ctx scope -∗
        future_result t1 v1 -∗
        WP task ctx v1 {{ v2,
          pool_context pool ctx scope ∗
          ▷ Ψ2 v2 ∗
          ▷ □ Ξ2 v2
        }}
      )
    }}}
      future_map ctx t1 task
    {{{ t2,
      RET t2;
      pool_context pool ctx scope ∗
      future_inv pool t2 (S depth) Ψ2 Ξ2 ∗
      future_consumer t2 Ψ2
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Ht1_inv & Htask) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_create_spec Ψ2 Ξ2 (waiter_model pool) with "[//]") as (t2) "(#Ht2_inv & Ht2_producer & Ht2_consumer)".

    wp_smart_apply (future_iter_spec (
      receipt_2 pool t2
    ) with "[$Hctx $Ht1_inv Htask Ht2_producer]") as "(Hctx & Hobligation)".
    { iIntros "{%} %ctx %scope %v1 Hctx #Ht1_result".
      wp_smart_apply (pool_async_spec (
        receipt_1 t2
      ) with "[$Hctx Htask Ht2_producer]") as "($ & #$) //".
      { iIntros "{%} %ctx %scope Hctx".
        wp_smart_apply (wp_wand with "(Htask Hctx Ht1_result)") as (v2) "(Hctx & HΨ2 & HΞ2)".
        wp_apply (future_set_spec with "[$]") as "($ & #$)".
      }
    }

    wp_pures.

    iApply "HΦ".
    iEval (rewrite future_inv_unfold).
    iFrame "∗ Ht2_inv". iRight.
    iDestruct "Hobligation" as "(:obligation)"; auto.
  Qed.
End future_G.

From zoo_parabs Require
  future__opaque.

#[global] Opaque future_inv.
#[global] Opaque future_obligation.
#[global] Opaque future_consumer.
#[global] Opaque future_result.
