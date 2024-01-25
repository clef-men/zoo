From zebre Require Import
  prelude.
From zebre.language Require Export
  rules.
From zebre Require Import
  options.

Class iType (PROP : bi) (τ : val → PROP) := {
  #[global] itype_persistent v :: Persistent (τ v) ;
}.

Section basic_types.
  Context {PROP : bi}.

  Implicit Types v : val.

  Definition bool_type v : PROP :=
    ∃ b, ⌜v = ValLiteral (LiteralBool b)⌝.
  #[global] Instance bool_type_itype :
    iType _ bool_type.
  Proof.
    split. apply _.
  Qed.

  Definition unit_type v : PROP :=
    ⌜v = ValUnit⌝.
  #[global] Instance unit_type_itype :
    iType _ unit_type.
  Proof.
    split. apply _.
  Qed.

  Definition int_type v : PROP :=
    ∃ i, ⌜v = ValLiteral (LiteralInt i)⌝.
  #[global] Instance int_type_itype :
    iType _ int_type.
  Proof.
    split. apply _.
  Qed.

  Definition refined_int_type ϕ v : PROP :=
    ∃ i, ⌜v = ValLiteral (LiteralInt i) ∧ ϕ i⌝.
  #[global] Instance refined_int_type_itype ϕ :
    iType _ (refined_int_type ϕ).
  Proof.
    split. apply _.
  Qed.

  Definition int_range_type lb ub :=
    refined_int_type (λ i, (lb ≤ i < ub)%Z).

  Definition nat_type v : PROP :=
    ∃ i, ⌜v = ValLiteral (LiteralInt (Z.of_nat i))⌝.
  #[global] Instance nat_type_itype :
    iType _ nat_type.
  Proof.
    split. apply _.
  Qed.

  Definition refined_nat_type ϕ v : PROP :=
    ∃ i, ⌜v = ValLiteral (LiteralInt (Z.of_nat i)) ∧ ϕ i⌝.
  #[global] Instance refined_nat_type_itype ϕ :
    iType _ (refined_nat_type ϕ).
  Proof.
    split. apply _.
  Qed.

  Definition nat_range_type lb ub :=
    refined_nat_type (λ i, lb ≤ i < ub).
  Definition nat_upto_type ub :=
    refined_nat_type (λ i, i < ub).
End basic_types.

Section other_types.
  Context `{zebre_G : !ZebreG Σ}.

  Implicit Types v fn : val.

  Definition function_type τ1 `{!iType _ τ1} τ2 `{!iType _ τ2} fn : iProp Σ :=
    □ (∀ v, τ1 v -∗ WP App (Val fn) (Val v) {{ τ2 }}).
  #[global] Instance function_type_itype τ1 `{!iType _ τ1} τ2 `{!iType _ τ2} :
    iType _ (function_type τ1 τ2).
  Proof.
    split. apply _.
  Qed.

  Definition later_type τ `{!iType _ τ} v : iProp Σ :=
    ▷ τ v.
  #[global] Instance later_type_itype τ `{!iType _ τ} :
    iType _ (later_type τ).
  Proof.
    split. apply _.
  Qed.
End other_types.

Declare Scope itype_scope.
Delimit Scope itype_scope with T.

Infix "-->" := (
  function_type
) : itype_scope.
Notation "▷ τ" := (
  later_type τ
) : itype_scope.
