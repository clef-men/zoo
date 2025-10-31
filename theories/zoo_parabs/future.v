From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
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
Implicit Types v t pool ctx task waiter fn : val.
Implicit Types scope : pool_scope.
Implicit Types ω : unit.

Class FutureG Σ `{pool_G : PoolG Σ} := {
  #[local] future_G_ivar_G :: Ivar3G Σ unit ;
}.

Definition future_Σ := #[
  ivar_3_Σ unit
].
#[global] Instance subG_future_Σ Σ `{pool_G : PoolG Σ} :
  subG future_Σ Σ →
  FutureG Σ.
Proof.
  solve_inG.
Qed.

Section future_G.
  Context `{future_G : FutureG Σ}.

  Implicit Types Ψ Χ Ξ : val → iProp Σ.

  #[local] Definition waiter_model pool t waiter ω : iProp Σ :=
    ∀ ctx scope v,
    pool_context pool ctx scope -∗
    ivar_3_result t v -∗
    WP waiter ctx v {{ res,
      ⌜res = ()%V⌝ ∗
      pool_context pool ctx scope
    }}.
  Definition future_inv pool t Ψ Ξ :=
    ivar_3_inv t Ψ Ξ (waiter_model pool).

  Definition future_consumer :=
    ivar_3_consumer.

  Definition future_result :=
    ivar_3_result.
  Definition future_finished t : iProp Σ :=
    ∃ v,
    future_result t v.

  #[global] Instance future_proper pool t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (future_inv pool t).
  Proof.
    solve_proper.
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
  #[global] Instance future_result_persistent t v :
    Persistent (future_result t v).
  Proof.
    apply _.
  Qed.

  Lemma future_consumer_divide {pool t Ψ Ξ Χ} Χs :
    future_inv pool t Ψ Ξ -∗
    future_consumer t Χ -∗
    (∀ x, Χ x -∗ [∗ list] Χ ∈ Χs, Χ x) ={⊤}=∗
    [∗ list] Χ ∈ Χs, future_consumer t Χ.
  Proof.
    apply ivar_3_consumer_divide.
  Qed.
  Lemma future_consumer_split {pool t Ψ Χ Ξ} Χ1 Χ2 :
    future_inv pool t Ψ Ξ -∗
    future_consumer t Χ -∗
    (∀ v, Χ v -∗ Χ1 v ∗ Χ2 v) ={⊤}=∗
      future_consumer t Χ1 ∗
      future_consumer t Χ2.
  Proof.
    apply ivar_3_consumer_split.
  Qed.

  Lemma future_result_agree t v1 v2 :
    future_result t v1 -∗
    future_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_3_result_agree.
  Qed.

  Lemma future_inv_result pool t Ψ Ξ v :
    future_inv pool t Ψ Ξ -∗
    future_result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    apply ivar_3_inv_result.
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
    apply ivar_3_inv_result_consumer.
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
      future_inv pool t Ψ Ξ ∗
      future_consumer t Ψ ∗
      pool_obligation pool (future_finished t)
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Htask) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_create_spec Ψ Ξ with "[//]") as (ivar) "(#Hivar_inv & Hivar_producer & Hivar_consumer)".

    wp_smart_apply (pool_async_spec (
      ivar_3_resolved ivar
    ) with "[$Hctx Htask Hivar_producer]") as "(Hctx & Hobligation)".
    { clear ctx scope. iIntros "%ctx %scope Hctx".

      wp_smart_apply (wp_wand with "(Htask Hctx)") as (v) "(Hctx & HΨ & HΞ)".
      wp_smart_apply (ivar_3_set_spec with "[$Hivar_inv $Hivar_producer $HΨ $HΞ]") as (waiters ωs) "(#Hivar_result & _ & Hwaiters)".

      wp_smart_apply (lst_iter_spec' (λ _ _, pool_context pool ctx scope)%I with "[$Hctx Hwaiters]") as "$"; first done.
      { iDestruct (big_sepL2_retract_r with "Hwaiters") as "(_ & Hwaiters)".
        iApply (big_sepL_impl with "Hwaiters").
        iSteps.
      }

      iFrame "#∗".
    }

    iSteps.
  Qed.

  Lemma future_wait_spec pool ctx scope t Ψ Ξ :
    {{{
      pool_context pool ctx scope ∗
      future_inv pool t Ψ Ξ
    }}}
      future_wait ctx t
    {{{ v,
      RET v;
      £ 2 ∗
      pool_context pool ctx scope ∗
      future_result t v
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hivar_inv) HΦ".

    wp_rec.

    wp_smart_apply (pool_wait_until_spec (ivar_3_resolved t)%I with "[$Hctx]") as "(Hctx & %v & #Hivar_result)".
    { iModIntro.
      wp_smart_apply (ivar_3_is_set_spec with "Hivar_inv") as (b) "Hivar_result".
      rewrite /ivar_3_resolved. destruct b; iSteps.
    }

    wp_smart_apply (ivar_3_get_spec with "[$Hivar_inv $Hivar_result]") as "H£".
    iSteps.
  Qed.

  Lemma future_iter_spec pool ctx scope t Ψ Ξ fn :
    {{{
      pool_context pool ctx scope ∗
      future_inv pool t Ψ Ξ ∗
      ( ∀ ctx scope v,
        pool_context pool ctx scope -∗
        future_result t v -∗
        WP fn ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope
        }}
      )
    }}}
      future_iter ctx t fn
    {{{
      RET ();
      pool_context pool ctx scope
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hivar_inv & Hfn) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_wait_spec inhabitant with "[$Hivar_inv $Hfn]") as ([v |]) "H"; iSteps.
  Qed.

  Lemma future_map_spec {pool ctx scope t1 Ψ1 Ξ1} Ψ2 Ξ2 fn :
    {{{
      pool_context pool ctx scope ∗
      future_inv pool t1 Ψ1 Ξ1 ∗
      ( ∀ ctx scope v1,
        pool_context pool ctx scope -∗
        future_result t1 v1 -∗
        WP fn ctx v1 {{ v2,
          pool_context pool ctx scope ∗
          ▷ Ψ2 v2 ∗
          ▷ □ Ξ2 v2
        }}
      )
    }}}
      future_map ctx t1 fn
    {{{ t2,
      RET t2;
      pool_context pool ctx scope ∗
      future_inv pool t2 Ψ2 Ξ2 ∗
      future_consumer t2 Ψ2
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Ht1_inv & Hfn) HΦ".

    wp_rec.
    wp_smart_apply (ivar_3_create_spec Ψ2 Ξ2 with "[//]") as (t2) "(#Hivar2_inv & Hivar2_producer & Hivar2_consumer)".

    wp_smart_apply (future_iter_spec with "[$Hctx $Ht1_inv Hfn Hivar2_producer]") as "Hctx".
    { clear ctx scope. iIntros "%ctx %scope %v1 Hctx #Ht1_result".

      wp_smart_apply (wp_wand with "(Hfn Hctx Ht1_result)") as (v2) "(Hctx & HΨ2 & HΞ2)".
      wp_smart_apply (ivar_3_set_spec with "[$Hivar2_inv $Hivar2_producer $HΨ2 $HΞ2]") as (waiters ωs) "(#Hivar2_result & _ & Hwaiters)".

      wp_smart_apply (lst_iter_spec' (λ _ _, pool_context pool ctx scope)%I with "[$Hctx Hwaiters]") as "$"; first done.
      { iDestruct (big_sepL2_retract_r with "Hwaiters") as "(_ & Hwaiters)".
        iApply (big_sepL_impl with "Hwaiters").
        iSteps.
      }

      iSteps.
    }

    iSteps.
  Qed.
End future_G.

From zoo_parabs Require
  future__opaque.

#[global] Opaque future_inv.
#[global] Opaque future_consumer.
#[global] Opaque future_result.
