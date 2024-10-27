From zoo Require Import
  prelude.
From zoo.language Require Export
  wp.
From zoo Require Import
  options.

Class iType (PROP : bi) (τ : val → PROP) := {
  #[global] itype_persistent v :: Persistent (τ v) ;
}.

Section basic.
  Context {PROP : bi}.

  Implicit Types v : val.

  Definition itype_unit v : PROP :=
    ⌜v = ValUnit⌝.
  #[global] Instance itype_unit_itype :
    iType _ itype_unit.
  Proof.
    split. apply _.
  Qed.

  Definition itype_bool v : PROP :=
    ∃ b, ⌜v = ValBool b⌝.
  #[global] Instance itype_bool_itype :
    iType _ itype_bool.
  Proof.
    split. apply _.
  Qed.

  Definition itype_int v : PROP :=
    ∃ i, ⌜v = ValInt i⌝.
  #[global] Instance itype_int_itype :
    iType _ itype_int.
  Proof.
    split. apply _.
  Qed.

  Definition itype_refined_int ϕ v : PROP :=
    ∃ i, ⌜v = ValInt i ∧ ϕ i⌝.
  #[global] Instance itype_refined_int_itype ϕ :
    iType _ (itype_refined_int ϕ).
  Proof.
    split. apply _.
  Qed.

  Definition itype_int_range lb ub :=
    itype_refined_int (λ i, (lb ≤ i < ub)%Z).

  Definition itype_nat v : PROP :=
    ∃ i, ⌜v = ValInt (Z.of_nat i)⌝.
  #[global] Instance itype_nat_itype :
    iType _ itype_nat.
  Proof.
    split. apply _.
  Qed.

  Definition itype_refined_nat ϕ v : PROP :=
    ∃ i, ⌜v = ValInt (Z.of_nat i) ∧ ϕ i⌝.
  #[global] Instance itype_refined_nat_itype ϕ :
    iType _ (itype_refined_nat ϕ).
  Proof.
    split. apply _.
  Qed.

  Definition itype_nat_range lb ub :=
    itype_refined_nat (λ i, lb ≤ i < ub).
  Definition itype_nat_upto ub :=
    itype_refined_nat (λ i, i < ub).
End basic.

Section other.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types v fn : val.

  Definition itype_fun τ1 `{!iType _ τ1} τ2 `{!iType _ τ2} fn : iProp Σ :=
    □ (∀ v, τ1 v -∗ WP App (Val fn) (Val v) {{ τ2 }}).
  #[global] Instance itype_fun_itype τ1 `{!iType _ τ1} τ2 `{!iType _ τ2} :
    iType _ (itype_fun τ1 τ2).
  Proof.
    split. apply _.
  Qed.

  Definition itype_later τ `{!iType _ τ} v : iProp Σ :=
    ▷ τ v.
  #[global] Instance itype_later_itype τ `{!iType _ τ} :
    iType _ (itype_later τ).
  Proof.
    split. apply _.
  Qed.
End other.

Declare Scope zoo_itype.
Delimit Scope zoo_itype with T.

Infix "-->" := (
  itype_fun
) : zoo_itype.
Notation "▷ τ" := (
  itype_later τ
) : zoo_itype.
