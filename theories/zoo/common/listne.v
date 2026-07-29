Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.options.

Definition listne A :=
  { x : list A | x ≠ [] }.

Section listne.
  Context {A : Type}.

  Implicit Type x y : A.
  Implicit Type l : listne A.

  Program Definition listne۰app l1 l2 : listne A :=
    `l1 ++ `l2.
  Next Obligation.
    intros (l1, Hl1) (l2, Hl2).
    auto using appｰnotｰnil.
  Qed.

  #[global] Instance listne۰elem_of : ElemOf A (listne A) :=
    λ x l,
      x ∈ `l.

  Definition listne۰Forall P l :=
    Forall P (`l).

  Lemma listneｰnon_empty l :
    ∃ x,
    x ∈ l.
  Proof.
    destruct l as ([| x] & Hl); first done.
    exists x. apply list_elem_of_here.
  Qed.

  Lemma listneｰelem_ofｰsingleton x y H :
    x ∈ [y]↾H ↔
    x = y.
  Proof.
    apply list_elem_of_singleton.
  Qed.
  Lemma listneｰelem_ofｰapp l1 l2 x :
    x ∈ listne۰app l1 l2 ↔
    x ∈ l1 ∨ x ∈ l2.
  Proof.
    rewrite -elem_of_app //.
  Qed.

  Lemma listne۰Forallｰforall P l :
    listne۰Forall P l ↔
    ∀ x, x ∈ l → P x.
  Proof.
    apply Forall_forall.
  Qed.
  Lemma listne۰Forallｰsingleton {P} x H :
    listne۰Forall P ([x]↾H) ↔
    P x.
  Proof.
    apply Forall_singleton.
  Qed.
  Lemma listne۰Forallｰapp P l1 l2 :
    listne۰Forall P (listne۰app l1 l2) ↔
      listne۰Forall P l1 ∧
      listne۰Forall P l2.
  Proof.
    apply Forall_app.
  Qed.
  Lemma listne۰Forallｰelem_of P l x :
    listne۰Forall P l →
    x ∈ l →
    P x.
  Proof.
    apply Forallｰelem_of.
  Qed.
End listne.
