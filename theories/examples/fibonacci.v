From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.parabs Require Import
  ws_hub
  scheduler.
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
  fib (Z.to_nat n) =
    if decide (n ≤ 1)%Z then
      Z.to_nat n
    else
      fib (Z.to_nat (n - 1)) + fib (Z.to_nat (n - 2)).
Proof.
  intros Hn.
  rewrite fib_spec.
  assert (Z.to_nat (n - 1) = Z.to_nat n - 1) as -> by lia.
  assert (Z.to_nat (n - 2) = Z.to_nat n - 2) as -> by lia.
  apply decide_ext. lia.
Qed.

Section scheduler_G.
  Context `{scheduler_G : SchedulerG Σ}.
  Context (ws_hub : ws_hub Σ).

  #[local] Definition fibonacci_aux : val :=
    rec: "fibonacci_aux" "n" "ctx" :=
      if: "n" ≤ #1 then (
        "n"
      ) else (
        let: "fut1" := scheduler_async ws_hub "ctx" (λ: "ctx", "fibonacci_aux" ("n" - #1) "ctx") in
        let: "fut2" := scheduler_async ws_hub "ctx" (λ: "ctx", "fibonacci_aux" ("n" - #2) "ctx") in
        scheduler_await ws_hub "ctx" "fut1" + scheduler_await ws_hub "ctx" "fut2"
      ).
  Definition fibonacci : val :=
    λ: "n" "sched",
      scheduler_run ws_hub "sched" (λ: "ctx", fibonacci_aux "n" "ctx").

  #[local] Lemma fibonacci_aux_spec n ctx :
    (0 ≤ n)%Z →
    {{{
      scheduler_context ws_hub ctx
    }}}
      fibonacci_aux #n ctx
    {{{
      RET #(fib (Z.to_nat n));
      scheduler_context ws_hub ctx
    }}}.
  Proof.
    iLöb as "HLöb" forall (n ctx).

    iIntros "%Hn %Φ Hctx HΦ".

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - assert (n = 0 ∨ n = 1) as [-> | ->] by lia; iSteps.

    - wp_smart_apply (scheduler_async_spec _ (λ v1, ⌜v1 = #_⌝)%I with "[$Hctx]") as (fut1) "(Hctx & #Hfut1)".
      { clear ctx. iIntros "%ctx Hctx".
        wp_smart_apply ("HLöb" with "[] Hctx"); iSteps.
      }
      wp_smart_apply (scheduler_async_spec _ (λ v2, ⌜v2 = #_⌝)%I with "[$Hctx]") as (fut2) "(Hctx & #Hfut2)".
      { clear ctx. iIntros "%ctx Hctx".
        wp_smart_apply ("HLöb" with "[] Hctx"); iSteps.
      }
      wp_smart_apply (scheduler_await_spec with "[$Hctx $Hfut2]") as (?) "(Hctx & ->)".
      wp_smart_apply (scheduler_await_spec with "[$Hctx $Hfut1]") as (?) "(Hctx & ->)".
      wp_pures.
      rewrite (fib_spec_Z n) // -Nat2Z.inj_add.
      rewrite decide_False; first lia.
      iSteps.
  Qed.
  Lemma fibonacci_spec (n : nat) sched :
    {{{
      scheduler_model ws_hub sched
    }}}
      fibonacci #n sched
    {{{
      RET #(fib n);
      scheduler_model ws_hub sched
    }}}.
  Proof.
    iIntros "%Φ Hsched HΦ".
    wp_rec.
    wp_smart_apply (scheduler_run_spec _ (λ v, ⌜v = #_⌝)%I with "[$Hsched]") as (?) "(Hctx & ->)"; last iSteps. iIntros "%ctx Hctx".
    wp_smart_apply (fibonacci_aux_spec with "Hctx"); first lia.
    rewrite Nat2Z.id. iSteps.
  Qed.
End scheduler_G.

#[global] Opaque fibonacci.
