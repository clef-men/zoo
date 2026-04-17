From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  biglater.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  ivar_4
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

Class FutureG Σ `{pool_G : PoolG Σ} :=
  { #[local] future_G_ivar_G :: Ivar4G Σ
  }.

Definition future_Σ := #[
  ivar_4_Σ
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

  #[local] Definition finished t : iProp Σ :=
    ∃ waiters Ps,
    ivar_4_resolved t ∗
    ivar_4_waiters t waiters Ps ∗
    [∗ list] P ∈ Ps, □ P.
  #[local] Instance : CustomIpat "finished" :=
    " ( %waiters
      & %Ps
      & #Hresolved
      & #Hwaiters
      & #HPs
      )
    ".

  Definition future_inv pool t Ψ Ξ : iProp Σ :=
    ∃ depth,
    ivar_4_inv t Ψ Ξ (pool_context pool) ∗
    ⧖ depth ∗
    □ (
      pool_finished pool -∗
      ▷^(2 * depth + 1) finished t
    ).
  #[local] Instance : CustomIpat "inv" :=
    " ( %depth{}
      & #Hinv{_{}}
      & #H⧖{_{}}
      & #Htermination{_{}}
      )
    ".

  Definition future_obligation pool P : iProp Σ :=
    ∃ depth,
    ⧖ depth ∗
    □ (
      pool_finished pool -∗
      ▷^(2 * depth + 2) □ P
    ).
  #[local] Instance : CustomIpat "obligation" :=
    " ( %depth
      & #H⧖
      & #Htermination
      )
    ".

  Definition future_consumer :=
    ivar_4_consumer.

  Definition future_result :=
    ivar_4_result.
  Definition future_resolved t : iProp Σ :=
    ∃ v,
    future_result t v.

  #[global] Instance future_inv_proper pool t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (future_inv pool t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance future_obligation_proper pool :
    Proper (
      (≡) ==>
      (≡)
    ) (future_obligation pool).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance future_consumer_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (future_consumer t).
  Proof.
    apply _.
  Qed.

  #[global] Instance future_result_timeless t v :
    Timeless (future_result t v).
  Proof.
    apply _.
  Qed.

  #[global] Instance future_inv_persistent pool t Ψ Ξ :
    Persistent (future_inv pool t Ψ Ξ).
  Proof.
    apply _.
  Qed.
  #[global] Instance future_obligation_persistent pool P :
    Persistent (future_obligation pool P).
  Proof.
    apply _.
  Qed.
  #[global] Instance future_result_persistent t v :
    Persistent (future_result t v).
  Proof.
    apply _.
  Qed.

  #[local] Ltac solve_biglater :=
    iFrame "#";
    iApply bi.laterN_le;
    last iFrame "#∗";
    apply Nat.add_le_mono;
    [ auto using Nat.mul_le_mono_r
    | etrans;
      last apply later_constant_lb;
      lia
    ].

  Lemma future_inv_finished pool t Ψ Ξ :
    future_inv pool t Ψ Ξ -∗
    pool_finished pool -∗
    ▶ future_resolved t.
  Proof.
    iIntros "(:inv) #Hpool_finished".
    iDestruct ("Htermination" with "Hpool_finished") as "(:finished)".
    solve_biglater.
  Qed.

  Lemma future_obligation_finished pool P :
    future_obligation pool P -∗
    pool_finished pool -∗
    ▶ □ P.
  Proof.
    iIntros "(:obligation) Hpool_finished".
    iDestruct ("Htermination" with "Hpool_finished") as "HP".
    solve_biglater.
  Qed.

  Lemma future_consumer_wand {pool t Ψ Ξ Χ1} Χ2 :
    future_inv pool t Ψ Ξ -∗
    future_consumer t Χ1 -∗
    (∀ x, Χ1 x -∗ Χ2 x) ={⊤}=∗
    future_consumer t Χ2.
  Proof.
    iIntros "(:inv)".
    iApply (ivar_4_consumer_wand with "Hinv").
  Qed.
  Lemma future_consumer_divide {pool t Ψ Ξ} Χs :
    future_inv pool t Ψ Ξ -∗
    future_consumer t (λ x, [∗ list] Χ ∈ Χs, Χ x) ={⊤}=∗
    [∗ list] Χ ∈ Χs, future_consumer t Χ.
  Proof.
    iIntros "(:inv)".
    iApply (ivar_4_consumer_divide with "Hinv").
  Qed.
  Lemma future_consumer_split {pool t Ψ Ξ} Χ1 Χ2 :
    future_inv pool t Ψ Ξ -∗
    future_consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      future_consumer t Χ1 ∗
      future_consumer t Χ2.
  Proof.
    iIntros "(:inv)".
    iApply (ivar_4_consumer_split with "Hinv").
  Qed.

  Lemma future_result_agree t v1 v2 :
    future_result t v1 -∗
    future_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_4_result_agree.
  Qed.

  Lemma future_inv_result pool t Ψ Ξ v :
    future_inv pool t Ψ Ξ -∗
    future_result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) Hresult".
    iApply (ivar_4_inv_result with "Hinv Hresult").
  Qed.
  Lemma future_inv_result' pool t Ψ Ξ v :
    £ 1 -∗
    future_inv pool t Ψ Ξ -∗
    future_result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hfut_inv Hfut_result".
    iMod (future_inv_result with "Hfut_inv Hfut_result") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma future_inv_result_consumer pool t Ψ Ξ v Χ :
    future_inv pool t Ψ Ξ -∗
    future_result t v -∗
    future_consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) Hresult Hconsumer".
    iApply (ivar_4_inv_result_consumer with "Hinv Hresult Hconsumer").
  Qed.
  Lemma future_inv_result_consumer' pool t Ψ Ξ v Χ :
    £ 2 -∗
    future_inv pool t Ψ Ξ -∗
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

  Lemma future_return𑁒spec pool Ψ Ξ v :
    {{{
      Ψ v ∗
      □ Ξ v
    }}}
      future_return v
    {{{
      t
    , RET t;
      future_inv pool t Ψ Ξ ∗
      future_consumer t Ψ ∗
      future_result t v
    }}}.
  Proof.
    iIntros "%Φ (HΨ & HΞ) HΦ".

    iMod steps_lb_0 as "#H⧖".

    wp_apply (ivar_4_make𑁒spec Ψ Ξ with "[$]") as (t) "(#Hinv & Hconsumer & #Hresult & #Hwaiters)".

    iApply "HΦ".
    iFrame "#∗". iSteps.
  Qed.

  #[local] Lemma future_set𑁒spec pool ctx scope t Ψ Ξ v :
    {{{
      pool_context pool ctx scope ∗
      ivar_4_inv t Ψ Ξ (pool_context pool) ∗
      ivar_4_producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      future_set ctx t v
    {{{
      RET ();
      pool_context pool ctx scope ∗
      finished t
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hinv & Hproducer & HΨ & HΞ) HΦ".

    wp_rec.
    wp_apply+ (ivar_4_notify𑁒spec with "[$Hinv $Hproducer $Hctx $HΨ $HΞ]").
    iSteps.
  Qed.

  Lemma future_async𑁒spec Ψ Ξ pool ctx scope task :
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
    {{{
      t
    , RET t;
      pool_context pool ctx scope ∗
      future_inv pool t Ψ Ξ ∗
      future_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Htask) HΦ".

    iMod steps_lb_0 as "#H⧖".

    wp_rec.
    wp_apply+ (ivar_4_create𑁒spec Ψ Ξ (pool_context pool) with "[//]") as (t) "(#Hinv & Hproducer & Hconsumer)".

    wp_apply+ (pool_async𑁒spec
      True
      (finished t)
    with "[$Hctx Htask Hproducer]") as "(Hctx & _ & #Hpool_obligation)".
    { iIntros "{%} %ctx %scope Hctx".
      wp_apply+ (wp_wand with "(Htask Hctx)") as (v) "(Hctx & HΨ & HΞ)".
      wp_apply (future_set𑁒spec _ _ _ _ Ψ with "[$]") as "($ & #$) //".
    }

    iStep 6. iFrame "#∗". iIntros "!> !> Hpool_finished".
    iDestruct (pool_obligation_finished with "Hpool_obligation Hpool_finished") as "#Hfinished".
    iNext => //.
  Qed.

  Lemma future_wait𑁒spec pool ctx scope t Ψ Ξ :
    {{{
      pool_context pool ctx scope ∗
      future_inv pool t Ψ Ξ
    }}}
      future_wait ctx t
    {{{
      v
    , RET v;
      £ 2 ∗
      pool_context pool ctx scope ∗
      future_result t v
    }}}.
  Proof.
    iIntros "%Φ (Hctx & (:inv)) HΦ".

    wp_rec.

    wp_apply+ (pool_wait_ivar𑁒spec with "[$Hctx $Hinv]") as "(_ & Hctx & %v & #Hresult)". 1: iSteps.
    wp_apply+ (ivar_4_get𑁒spec with "[$Hinv $Hresult]") as "H£".
    iSteps.
  Qed.

  Lemma future_iter𑁒spec P pool ctx scope t Ψ Ξ task :
    {{{
      pool_context pool ctx scope ∗
      future_inv pool t Ψ Ξ ∗
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
      future_obligation pool P
    }}}.
  Proof.
    iIntros "%Φ (Hctx & (:inv) & Htask) HΦ".

    wp_rec steps:"H⧖" credit:"H£".

    lazymatch iTypeOf "Htask" with
    | Some (_, ?P) =>
        pose P_task := P
    end.
    wp_apply+ (ivar_4_wait𑁒spec P P_task with "[$Hinv $Htask]") as ([v |]) "H".
    { iIntros "{%} %ctx %scope %v Htask Hctx #Hresult".
      wp_apply (wp_wand with "(Htask Hctx Hresult)").
      iSteps.
    }

    - iDestruct "H" as "(_ & #Hresult & Htask)".

      iApply wp_fupd.
      wp_apply+ (wp_wand with "(Htask Hctx Hresult)") as (res) "(-> & Hctx & HP)".

      iApply "HΦ".
      iMod (lc_fupd_elim_later with "H£ HP") as "#HP".
      iFrameSteps.

    - iDestruct "H" as "#Hwaiter".

      wp_pures.

      iApply "HΦ".
      iFrame "#∗". iIntros "!> !> #Hpool_finished".
      iDestruct ("Htermination" with "Hpool_finished") as "Hfinished".
      iEval (replace (2 * depth + 2) with ((2 * depth + 1) + 1) by lia).
      iEval (rewrite bi.laterN_add).
      iNext.
      iDestruct "Hfinished" as "(:finished)".
      iDestruct (ivar_4_waiter_valid with "Hwaiters Hwaiter") as "(%i & %P_ & _ & %HPs_lookup & Heq)".
      iDestruct (big_sepL_lookup with "HPs") as "HP". 1: done.
      iNext.
      iRewrite -"Heq" in "HP" => //.
  Qed.

  Lemma future_map𑁒spec {pool ctx scope t1 Ψ1 Ξ1} Ψ2 Ξ2 task :
    {{{
      pool_context pool ctx scope ∗
      future_inv pool t1 Ψ1 Ξ1 ∗
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
    {{{
      t2
    , RET t2;
      pool_context pool ctx scope ∗
      future_inv pool t2 Ψ2 Ξ2 ∗
      future_consumer t2 Ψ2
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hinv_1 & Htask) HΦ".

    wp_rec.
    wp_apply+ (ivar_4_create𑁒spec Ψ2 Ξ2 (pool_context pool) with "[//]") as (t2) "(#Hinv_2 & Hproducer_2 & Hconsumer_2)".

    wp_apply+ (future_iter𑁒spec (
      pool_obligation pool (finished t2)
    ) with "[$Hctx $Hinv_1 Htask Hproducer_2]") as "(Hctx & (:obligation))".
    { iIntros "{%} %ctx %scope %v1 Hctx #Hresult_1".
      wp_apply+ (pool_async𑁒spec
        True
        (finished t2)
      with "[$Hctx Htask Hproducer_2]") as "($ & _ & #$) //".
      { iIntros "{%} %ctx %scope Hctx".
        wp_apply+ (wp_wand with "(Htask Hctx Hresult_1)") as (v2) "(Hctx & HΨ2 & HΞ2)".
        wp_apply (future_set𑁒spec _ _ _ _ Ψ2 with "[$]") as "($ & #$) //".
      }
    }

    wp_pures steps:"H⧖".

    iApply "HΦ".
    iFrame "#∗". iIntros "!> !> #Hpool_finished".
    iDestruct ("Htermination" with "Hpool_finished") as "Hpool_obligation".
    iEval (replace (2 * S depth + 1) with ((2 * depth + 2) + 1) by lia).
    iEval (rewrite bi.laterN_add).
    iNext.
    iDestruct (pool_obligation_finished with "Hpool_obligation Hpool_finished") as "Hfinished".
    iNext => //.
  Qed.
End future_G.

From zoo_parabs Require
  future__opaque.

#[global] Opaque future_inv.
#[global] Opaque future_obligation.
#[global] Opaque future_consumer.
#[global] Opaque future_result.
