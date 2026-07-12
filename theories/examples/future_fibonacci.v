Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Import zoo.diaframe.
Require Import zoo_parabs.future.
Require Import zoo_parabs.pool.
Require Export examples.fibonacci.
Require Export examples.future_fibonacci__code.
Require Import zoo.options.

Section future_G.
  Context `{future_G : FutureG Σ}.

  #[local] Lemma future_fibonacci٠main₀𑁒spec n pool ctx scope :
    (0 ≤ n)%Z →
    {{{
      pool_context pool ctx scope
    }}}
      future_fibonacci٠main₀ ctx #n
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

    - wp_apply (future٠async𑁒spec
        (λ v1, ⌜v1 = #_⌝)%I
        (λ _, True)%I
      with "[$Hctx]") as (fut1) "(Hctx & #Hfut1_inv & Hfut1_consumer)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp_apply+ ("HLöb" with "[] Hctx"); iSteps.
      }

      wp_apply+ (future٠async𑁒spec
        (λ v2, ⌜v2 = #_⌝)%I
        (λ _, True)%I
      with "[$Hctx]") as (fut2) "(Hctx & #Hfut2_inv & Hfut2_consumer)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp_apply+ ("HLöb" with "[] Hctx"); iSteps.
      }

      wp_apply+ (future٠wait𑁒spec with "[$Hctx $Hfut2_inv]") as (res) "(H£ & Hctx & Hfut2_result)".
      iMod (future_inv_result_consumer' with "H£ Hfut2_inv Hfut2_result Hfut2_consumer") as "(-> & _)".

      wp_apply+ (future٠wait𑁒spec with "[$Hctx $Hfut1_inv]") as (res) "(H£ & Hctx & Hfut1_result)".
      iMod (future_inv_result_consumer' with "H£ Hfut1_inv Hfut1_result Hfut1_consumer") as "(-> & _)".

      wp_pures.

      rewrite (fibonacci_spec_Z n) // -Nat2Z.inj_add.
      rewrite decide_False; first lia.
      iSteps.
  Qed.
  Lemma future_fibonacci٠main𑁒spec (num_dom n : nat) :
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

    wp_rec.

    wp_apply+ (pool٠run𑁒spec (λ pool v,
      ⌜v = #_⌝
    )%I) as (pool ?) "(_ & ->)". 1: lia.
    { iIntros "%pool %ctx %scope _ Hctx".
      wp_apply+ (future_fibonacci٠main₀𑁒spec with "Hctx"); first lia.
      rewrite Nat2Z.id. iSteps.
    }

    iSteps.
  Qed.
End future_G.

Require examples.future_fibonacci__opaque.
