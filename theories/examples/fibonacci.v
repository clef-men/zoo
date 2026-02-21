From zoo Require Import
  prelude.
From zoo Require Import
  options.

Fixpoint fibonacci n :=
  match n with
  | 0 =>
      0
  | S n =>
      match n with
      | 0 =>
          1
      | S m =>
          fibonacci n + fibonacci m
      end
  end.
#[global] Arguments fibonacci !_ /.

Lemma fibonacci_spec n :
  fibonacci n =
    if decide (n ≤ 1) then
      n
    else
      fibonacci (n - 1) + fibonacci (n - 2).
Proof.
  destruct n as [| [| n]]; simpl; try done.
  rewrite right_id //.
Qed.
Lemma fibonacci_spec_Z n :
  (0 ≤ n)%Z →
  fibonacci ₊n =
    if decide (n ≤ 1)%Z then
      ₊n
    else
      fibonacci ₊(n - 1) + fibonacci ₊(n - 2).
Proof.
  intros Hn.
  rewrite fibonacci_spec.
  assert (₊(n - 1) = ₊n - 1) as -> by lia.
  assert (₊(n - 2) = ₊n - 2) as -> by lia.
  apply decide_ext. lia.
Qed.
