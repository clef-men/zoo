From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo Require Import
  options.

Definition listne A :=
  { x : list A | x ≠ [] }.

Section listne.
  Context {A : Type}.

  Implicit Types x y : A.
  Implicit Types l : listne A.

  Program Definition listne_app l1 l2 : listne A :=
    `l1 ++ `l2.
  Next Obligation.
    intros (l1, Hl1) (l2, Hl2).
    auto using app_not_nil.
  Qed.

  #[global] Instance listne_elem_of : ElemOf A (listne A) :=
    λ x l,
      x ∈ `l.

  Definition listne_Forall P l :=
    Forall P (`l).

  Lemma listne_non_empty l :
    ∃ x,
    x ∈ l.
  Proof.
    destruct l as ([| x] & Hl); first done.
    exists x. apply list_elem_of_here.
  Qed.

  Lemma listne_elem_of_singleton x y H :
    x ∈ [y]↾H ↔
    x = y.
  Proof.
    apply list_elem_of_singleton.
  Qed.
  Lemma listne_elem_of_app l1 l2 x :
    x ∈ listne_app l1 l2 ↔
    x ∈ l1 ∨ x ∈ l2.
  Proof.
    rewrite -elem_of_app //.
  Qed.

  Lemma listne_Forall_forall P l :
    listne_Forall P l ↔
    ∀ x, x ∈ l → P x.
  Proof.
    apply Forall_forall.
  Qed.
  Lemma listne_Forall_singleton {P} x H :
    listne_Forall P ([x]↾H) ↔
    P x.
  Proof.
    apply Forall_singleton.
  Qed.
  Lemma listne_Forall_app P l1 l2 :
    listne_Forall P (listne_app l1 l2) ↔
      listne_Forall P l1 ∧
      listne_Forall P l2.
  Proof.
    apply Forall_app.
  Qed.
  Lemma listne_Forall_elem_of P l x :
    listne_Forall P l →
    x ∈ l →
    P x.
  Proof.
    apply Forall_elem_of.
  Qed.
End listne.
