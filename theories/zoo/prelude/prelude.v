From zoo.prelude Require Export
  base
  tactics.

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
