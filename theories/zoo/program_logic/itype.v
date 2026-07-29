Require Import zoo.prelude.
Require Export zoo.program_logic.wp.
Require Import zoo.options.

Class iType (PROP : bi) (τ : val → PROP) :=
  { #[global] itypeｰpersistent v ::
      Persistent (τ v)
  }.

Section basic.
  Context {PROP : bi}.

  Implicit Type v : val.

  Definition itype۰unit v : PROP :=
    ⌜v = ValUnit⌝.
  #[global] Instance itype۰unitｰitype :
    iType _ itype۰unit.
  Proof.
    split. apply _.
  Qed.

  Definition itype۰bool v : PROP :=
    ∃ b, ⌜v = ValBool b⌝.
  #[global] Instance itype۰boolｰitype :
    iType _ itype۰bool.
  Proof.
    split. apply _.
  Qed.

  Definition itype۰int v : PROP :=
    ∃ i, ⌜v = ValInt i⌝.
  #[global] Instance itype۰intｰitype :
    iType _ itype۰int.
  Proof.
    split. apply _.
  Qed.

  Definition itype۰refined_int ϕ v : PROP :=
    ∃ i, ⌜v = ValInt i ∧ ϕ i⌝.
  #[global] Instance itype۰refined_intｰitype ϕ :
    iType _ (itype۰refined_int ϕ).
  Proof.
    split. apply _.
  Qed.

  Definition itype۰int_range lb ub :=
    itype۰refined_int (λ i, (lb ≤ i < ub)%Z).

  Definition itype۰nat v : PROP :=
    ∃ i, ⌜v = ValInt ⁺i⌝.
  #[global] Instance itype۰natｰitype :
    iType _ itype۰nat.
  Proof.
    split. apply _.
  Qed.

  Definition itype۰refined_nat ϕ v : PROP :=
    ∃ i, ⌜v = ValInt ⁺i ∧ ϕ i⌝.
  #[global] Instance itype۰refined_natｰitype ϕ :
    iType _ (itype۰refined_nat ϕ).
  Proof.
    split. apply _.
  Qed.

  Definition itype۰nat_range lb ub :=
    itype۰refined_nat (λ i, lb ≤ i < ub).
  Definition itype۰nat_upto ub :=
    itype۰refined_nat (λ i, i < ub).
End basic.

Section other.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type v fn : val.

  Definition itype۰fun τ1 `{!iType _ τ1} τ2 `{!iType _ τ2} fn : iProp Σ :=
    □ (∀ v, τ1 v -∗ WP App (Val fn) (Val v) {{ τ2 }}).
  #[global] Instance itype۰funｰitype τ1 `{!iType _ τ1} τ2 `{!iType _ τ2} :
    iType _ (itype۰fun τ1 τ2).
  Proof.
    split. apply _.
  Qed.

  Definition itype۰later τ `{!iType _ τ} v : iProp Σ :=
    ▷ τ v.
  #[global] Instance itype۰laterｰitype τ `{!iType _ τ} :
    iType _ (itype۰later τ).
  Proof.
    split. apply _.
  Qed.
End other.

Declare Scope zoo_itype.
Delimit Scope zoo_itype with T.

Infix "-->" := (
  itype۰fun
) : zoo_itype.
Notation "▷ τ" := (
  itype۰later τ
) : zoo_itype.
