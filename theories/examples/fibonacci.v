From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.scheduling Require Import
  ws_deques
  scheduler.
From zebre Require Import
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
  Context (ws_deques : ws_deques Σ).

  #[local] Definition fibonacci_aux : val :=
    rec: "fibonacci_aux" "n" "hdl" :=
      if: "n" ≤ #1 then (
        "n"
      ) else (
        let: "fut1" := scheduler_async ws_deques "hdl" (λ: "hdl", "fibonacci_aux" ("n" - #1) "hdl") in
        let: "fut2" := scheduler_async ws_deques "hdl" (λ: "hdl", "fibonacci_aux" ("n" - #2) "hdl") in
        scheduler_await ws_deques "hdl" "fut1" + scheduler_await ws_deques "hdl" "fut2"
      ).
  Definition fibonacci : val :=
    λ: "n" "hdl",
      scheduler_run ws_deques "hdl" (λ: "hdl", fibonacci_aux "n" "hdl").

  #[local] Lemma fibonacci_aux_spec n sched hdl :
    (0 ≤ n)%Z →
    {{{
      scheduler_inv ws_deques sched ∗
      scheduler_handle ws_deques sched hdl
    }}}
      fibonacci_aux #n hdl
    {{{
      RET #(fib (Z.to_nat n));
      scheduler_handle ws_deques sched hdl
    }}}.
  Proof.
    iLöb as "HLöb" forall (n hdl).

    iIntros "%Hn %Φ (#Hsched & Hhdl) HΦ".

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - assert (n = 0 ∨ n = 1) as [-> | ->] by lia; iSteps.

    - wp_smart_apply (scheduler_async_spec _ (λ v1, ⌜v1 = #_⌝)%I with "[$Hsched $Hhdl]") as (fut1) "(Hhdl & #Hfut1)".
      { clear hdl. iIntros "%hdl Hhdl".
        wp_smart_apply ("HLöb" with "[] [$Hsched $Hhdl]"); iSteps.
      }
      wp_smart_apply (scheduler_async_spec _ (λ v2, ⌜v2 = #_⌝)%I with "[$Hsched $Hhdl]") as (fut2) "(Hhdl & #Hfut2)".
      { clear hdl. iIntros "%hdl Hhdl".
        wp_smart_apply ("HLöb" with "[] [$Hsched $Hhdl]"); iSteps.
      }
      wp_smart_apply (scheduler_await_spec with "[$Hsched $Hhdl $Hfut2]") as (?) "(Hhdl & ->)".
      wp_smart_apply (scheduler_await_spec with "[$Hsched $Hhdl $Hfut1]") as (?) "(Hhdl & ->)".
      wp_pures.
      rewrite (fib_spec_Z n) // -Nat2Z.inj_add.
      rewrite decide_False; first lia.
      iSteps.
  Qed.
  Lemma fibonacci_spec (n : nat) sched hdl :
    {{{
      scheduler_inv ws_deques sched ∗
      scheduler_handle ws_deques sched hdl
    }}}
      fibonacci #n hdl
    {{{
      RET #(fib n);
      scheduler_handle ws_deques sched hdl
    }}}.
  Proof.
    iIntros "%Φ (#Hsched & Hhdl) HΦ".
    wp_rec.
    wp_smart_apply (scheduler_run_spec _ (λ v, ⌜v = #_⌝)%I with "[$Hsched $Hhdl]") as (?) "(Hhdl & ->)"; last iSteps.
    clear hdl. iIntros "%hdl Hhdl".
    wp_smart_apply (fibonacci_aux_spec with "[$Hsched $Hhdl]"); first lia.
    rewrite Nat2Z.id. iSteps.
  Qed.
End scheduler_G.

#[global] Opaque fibonacci.
