From Coq.ssr Require Export
  ssreflect.

From stdpp Require Export
  prelude.

Open Scope general_if_scope.

Coercion Z.of_nat : nat >-> Z.

Notation "₊ n" := (
  Z.to_nat n
)(at level 3,
  right associativity,
  format "₊ n"
) : stdpp_scope.
Notation "⁺ n" := (
  Z.of_nat n
)(at level 3,
  right associativity,
  format "⁺ n"
) : stdpp_scope.

Reserved Notation "x0 ≤ x1 ≤ x2 ≤ x3 ≤ x4"
( at level 70,
  x1 at next level,
  x2 at next level,
  x3 at next level,
  x4 at next level
).
Notation "x0 ≤ x1 ≤ x2 ≤ x3 ≤ x4" := (
  x0 ≤ x1 ∧
  x1 ≤ x2 ∧
  x2 ≤ x3 ∧
  x3 ≤ x4
)%nat
: nat_scope.
Notation "x0 ≤ x1 ≤ x2 ≤ x3 ≤ x4" := (
  x0 ≤ x1 ∧
  x1 ≤ x2 ∧
  x2 ≤ x3 ∧
  x3 ≤ x4
)%Z
: Z_scope.
