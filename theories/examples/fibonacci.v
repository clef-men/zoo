Require Import zoo.prelude.
Require Import zoo.options.

Fixpoint fibonacci n :=
  match n with
  | 0 =>
      0
  | ˖n =>
      match n with
      | 0 =>
          1
      | ˖m =>
          fibonacci n + fibonacci m
      end
  end.
#[global] Arguments fibonacci !_ /.

Lemma fibonacciｰspec n :
  fibonacci n =
    if decide (n ≤ 1) then
      n
    else
      fibonacci (n - 1) + fibonacci (n - 2).
Proof.
  destruct n as [| [| n]]; simpl; try done.
  rewrite right_id //.
Qed.
Lemma fibonacciｰspecｰZ n :
  (0 ≤ n)%Z →
  fibonacci ₊n =
    if decide (n ≤ 1)%Z then
      ₊n
    else
      fibonacci ₊(n - 1) + fibonacci ₊(n - 2).
Proof.
  intros Hn.
  rewrite fibonacciｰspec.
  assert (₊(n - 1) = ₊n - 1) as -> by lia.
  assert (₊(n - 2) = ₊n - 2) as -> by lia.
  apply decide_ext. lia.
Qed.

Lemma fibonacciｰbase n :
  n ≤ 1 →
  fibonacci n = n.
Proof.
  intros Hn.
  rewrite fibonacciｰspec decide_True //.
Qed.
Lemma fibonacciｰrecursive n :
  1 < n →
  fibonacci n = fibonacci (n - 1) + fibonacci (n - 2).
Proof.
  intros Hn.
  rewrite fibonacciｰspec decide_False //. 1: lia.
Qed.
