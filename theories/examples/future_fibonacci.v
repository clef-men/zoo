Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_parabs.future.
Require Import zoo_parabs.pool.
Require Export examples.fibonacci.
Require Export examples.future_fibonacci__code.
Require Import zoo.options.

Section future۰G.
  Context `{future۰G : FutureG Σ}.

  #[local] Lemma future_fibonacci٠main₁ｰspec n pool ctx scope :
    (0 ≤ n)%Z →
    {{{
      pool۰context pool ctx scope
    }}}
      future_fibonacci٠main₁ ctx #n
    {{{
      RET #(fibonacci ₊n);
      pool۰context pool ctx scope
    }}}.
  Proof.
    iLöb as "HLöb" forall (n ctx scope).

    iIntros "%Hn %Φ Hctx HΦ".

    wp۰rec. wp۰pures.
    case_bool_decide as Hcase; wp۰pures.

    - assert (n = 0 ∨ n = 1) as [-> | ->] by lia; iSteps.

    - wp۰apply (future٠asyncｰspec
        (λ v1, ⌜v1 = #_⌝)%I
        (λ _, True)%I
      with "[$Hctx]") as (fut1) "(Hctx & #Hfut1_inv & Hfut1_consumer)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp۰apply+ ("HLöb" with "[] Hctx"); iSteps.
      }

      wp۰apply+ (future٠asyncｰspec
        (λ v2, ⌜v2 = #_⌝)%I
        (λ _, True)%I
      with "[$Hctx]") as (fut2) "(Hctx & #Hfut2_inv & Hfut2_consumer)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp۰apply+ ("HLöb" with "[] Hctx"); iSteps.
      }

      wp۰apply+ (future٠waitｰspec with "[$Hctx $Hfut2_inv]") as (res) "(H£ & Hctx & Hfut2_result)".
      iMod (futureｰinvｰresultｰconsumer' with "H£ Hfut2_inv Hfut2_result Hfut2_consumer") as "(-> & _)".

      wp۰apply+ (future٠waitｰspec with "[$Hctx $Hfut1_inv]") as (res) "(H£ & Hctx & Hfut1_result)".
      iMod (futureｰinvｰresultｰconsumer' with "H£ Hfut1_inv Hfut1_result Hfut1_consumer") as "(-> & _)".

      wp۰pures.

      rewrite (fibonacciｰspecｰZ n) // -Nat2Z.inj_add.
      rewrite decide_False; first lia.
      iSteps.
  Qed.
  Lemma future_fibonacci٠mainｰspec (num_dom n : nat) :
    {{{
      True
    }}}
      future_fibonacci٠main #num_dom #n
    {{{
      RET #(fibonacci n);
      True
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.

    wp۰apply+ (pool٠runｰspec (λ pool v,
      ⌜v = #_⌝
    )%I) as (pool ?) "(_ & ->)". 1: lia.
    { iIntros "%pool %ctx %scope _ Hctx".
      wp۰apply+ (future_fibonacci٠main₁ｰspec with "Hctx"); first lia.
      rewrite Nat2Z.id. iSteps.
    }

    iSteps.
  Qed.
End future۰G.

Require examples.future_fibonacci__opaque.
