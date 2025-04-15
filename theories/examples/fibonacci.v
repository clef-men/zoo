From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_parabs Require Import
  pool.
From examples Require Export
  fibonacci__code.
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

Section pool_G.
  Context `{pool_G : SchedulerG Σ}.

  #[local] Lemma fibonacci_fibonacci_0_spec n ctx :
    (0 ≤ n)%Z →
    {{{
      pool_context_model ctx
    }}}
      fibonacci_fibonacci_0 #n ctx
    {{{
      RET #(fib ₊n);
      pool_context_model ctx
    }}}.
  Proof.
    iLöb as "HLöb" forall (n ctx).

    iIntros "%Hn %Φ Hctx HΦ".

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - assert (n = 0 ∨ n = 1) as [-> | ->] by lia; iSteps.

    - wp_apply (pool_async_spec (λ v1, ⌜v1 = #_⌝)%I with "[$Hctx]") as (fut1) "(Hctx & #Hfut1)".
      { clear ctx. iIntros "%ctx Hctx".
        wp_smart_apply ("HLöb" with "[] Hctx"); iSteps.
      }
      wp_smart_apply (pool_async_spec (λ v2, ⌜v2 = #_⌝)%I with "[$Hctx]") as (fut2) "(Hctx & #Hfut2)".
      { clear ctx. iIntros "%ctx Hctx".
        wp_smart_apply ("HLöb" with "[] Hctx"); iSteps.
      }
      wp_smart_apply (pool_await_spec with "[$Hctx $Hfut2]") as (?) "(Hctx & ->)".
      wp_smart_apply (pool_await_spec with "[$Hctx $Hfut1]") as (?) "(Hctx & ->)".
      wp_pures.
      rewrite (fib_spec_Z n) // -Nat2Z.inj_add.
      rewrite decide_False; first lia.
      iSteps.
  Qed.
  Lemma fibonacci_fibonacci_spec (n : nat) pool :
    {{{
      pool_model pool
    }}}
      fibonacci_fibonacci #n pool
    {{{
      RET #(fib n);
      pool_model pool
    }}}.
  Proof.
    iIntros "%Φ Hpool HΦ".
    wp_rec.
    wp_smart_apply (pool_run_spec (λ v, ⌜v = #_⌝)%I with "[$Hpool]") as (?) "(Hctx & ->)"; last iSteps. iIntros "%ctx _ Hctx".
    wp_smart_apply (fibonacci_fibonacci_0_spec with "Hctx"); first lia.
    rewrite Nat2Z.id. iSteps.
  Qed.
End pool_G.

#[global] Opaque fibonacci_fibonacci.
