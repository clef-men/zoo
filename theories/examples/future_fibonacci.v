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
  future_fibonacci__code.
From zoo Require Import
  options.

Fixpoint fib n :=
  match n with
  | 0 =>
      0
  | S n =>
      match n with
      | 0 =>
          1
      | S m =>
          fib n + fib m
      end
  end.
#[global] Arguments fib !_ /.

Lemma fib_spec n :
  fib n =
    if decide (n ≤ 1) then
      n
    else
      fib (n - 1) + fib (n - 2).
Proof.
  destruct n as [| [| n]]; simpl; try done.
  rewrite right_id //.
Qed.
Lemma fib_spec_Z n :
  (0 ≤ n)%Z →
  fib ₊n =
    if decide (n ≤ 1)%Z then
      ₊n
    else
      fib ₊(n - 1) + fib ₊(n - 2).
Proof.
  intros Hn.
  rewrite fib_spec.
  assert (₊(n - 1) = ₊n - 1) as -> by lia.
  assert (₊(n - 2) = ₊n - 2) as -> by lia.
  apply decide_ext. lia.
Qed.

Section future_G.
  Context `{future_G : FutureG Σ}.

  #[local] Lemma future_fibonacci_main_0_spec n pool ctx scope :
    (0 ≤ n)%Z →
    {{{
      pool_context pool ctx scope
    }}}
      future_fibonacci_main_0 ctx #n
    {{{
      RET #(fib ₊n);
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

      rewrite (fib_spec_Z n) // -Nat2Z.inj_add.
      rewrite decide_False; first lia.
      iSteps.
  Qed.
  Lemma future_fibonacci_main_spec (num_dom n : nat) :
    {{{
      True
    }}}
      future_fibonacci_main #num_dom #n
    {{{
      RET #(fib n);
      True
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_smart_apply (pool_create_spec with "[//]") as (pool) "(_ & Hpool)". 1: lia.

    wp_smart_apply (pool_run_spec (λ v,
      ⌜v = #_⌝
    )%I with "[$Hpool]") as (?) "(Hpool& ->)".
    { iIntros "%ctx %scope Hctx".
      wp_smart_apply (future_fibonacci_main_0_spec with "Hctx"); first lia.
      rewrite Nat2Z.id. iSteps.
    }

    wp_smart_apply (pool_kill_spec with "Hpool") as "_".
    iSteps.
  Qed.
End future_G.

From examples Require
  future_fibonacci__opaque.
