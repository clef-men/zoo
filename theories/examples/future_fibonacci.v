From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_parabs Require Import
  future
  pool.
From examples Require Export
  fibonacci
  future_fibonacci__code.
From zoo Require Import
  options.

Section future_G.
  Context `{future_G : FutureG Σ}.

  #[local] Lemma future_fibonacci_main_0_spec n pool ctx scope :
    (0 ≤ n)%Z →
    {{{
      pool_context pool ctx scope
    }}}
      future_fibonacci_main_0 ctx #n
    {{{
      RET #(fibonacci ₊n);
      pool_context pool ctx scope
    }}}.
  Proof.
    iLöb as "HLöb" forall (n ctx scope).

    iIntros "%Hn %Φ Hctx HΦ".

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - assert (n = 0 ∨ n = 1) as [-> | ->] by lia; iSteps.

    - wp_apply (future_async_spec
        (λ v1, ⌜v1 = #_⌝)%I
        (λ _, True)%I
      with "[$Hctx]") as (fut1) "(Hctx & #Hfut1_inv & Hfut1_consumer)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp_smart_apply ("HLöb" with "[] Hctx"); iSteps.
      }

      wp_smart_apply (future_async_spec
        (λ v2, ⌜v2 = #_⌝)%I
        (λ _, True)%I
      with "[$Hctx]") as (fut2) "(Hctx & #Hfut2_inv & Hfut2_consumer)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp_smart_apply ("HLöb" with "[] Hctx"); iSteps.
      }

      wp_smart_apply (future_wait_spec with "[$Hctx $Hfut2_inv]") as (res) "(H£ & Hctx & Hfut2_result)".
      iMod (future_inv_result_consumer' with "H£ Hfut2_inv Hfut2_result Hfut2_consumer") as "(-> & _)".

      wp_smart_apply (future_wait_spec with "[$Hctx $Hfut1_inv]") as (res) "(H£ & Hctx & Hfut1_result)".
      iMod (future_inv_result_consumer' with "H£ Hfut1_inv Hfut1_result Hfut1_consumer") as "(-> & _)".

      wp_pures.

      rewrite (fibonacci_spec_Z n) // -Nat2Z.inj_add.
      rewrite decide_False; first lia.
      iSteps.
  Qed.
  Lemma future_fibonacci_main_spec (num_dom n : nat) :
    {{{
      True
    }}}
      future_fibonacci_main #num_dom #n
    {{{
      RET #(fibonacci n);
      True
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_smart_apply (pool_create_spec with "[//]") as (pool) "(_ & Hpool_model)". 1: lia.

    wp_smart_apply (pool_run_spec (λ v,
      ⌜v = #_⌝
    )%I with "[$Hpool_model]") as (?) "(Hpool_model & ->)".
    { iIntros "%ctx %scope Hctx".
      wp_smart_apply (future_fibonacci_main_0_spec with "Hctx"); first lia.
      rewrite Nat2Z.id. iSteps.
    }

    wp_smart_apply (pool_kill_spec with "Hpool_model").
    iSteps.
  Qed.
End future_G.

From examples Require
  future_fibonacci__opaque.
