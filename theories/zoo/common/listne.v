Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.options.

Definition listne A :=
  { x : list A | x ≠ [] }.

Section listne.
  Context {A : Type}.

  Implicit Types x y : A.
  Implicit Types l : listne A.

  Program Definition listne۰app l1 l2 : listne A :=
    `l1 ++ `l2.
  Next Obligation.
    intros (l1, Hl1) (l2, Hl2).
    auto using app𑁒not𑁒nil.
  Qed.

  #[global] Instance listne۰elem_of : ElemOf A (listne A) :=
    λ x l,
      x ∈ `l.

  Definition listne۰Forall P l :=
    Forall P (`l).

  Lemma listne𑁒non_empty l :
    ∃ x,
    x ∈ l.
  Proof.
    destruct l as ([| x] & Hl); first done.
    exists x. apply list_elem_of_here.
  Qed.

  Lemma listne𑁒elem_of𑁒singleton x y H :
    x ∈ [y]↾H ↔
    x = y.
  Proof.
    apply list_elem_of_singleton.
  Qed.
  Lemma listne𑁒elem_of𑁒app l1 l2 x :
    x ∈ listne۰app l1 l2 ↔
    x ∈ l1 ∨ x ∈ l2.
  Proof.
    rewrite -elem_of_app //.
  Qed.

  Lemma listne۰Forall𑁒forall P l :
    listne۰Forall P l ↔
    ∀ x, x ∈ l → P x.
  Proof.
    apply Forall_forall.
  Qed.
  Lemma listne۰Forall𑁒singleton {P} x H :
    listne۰Forall P ([x]↾H) ↔
    P x.
  Proof.
    apply Forall_singleton.
  Qed.
  Lemma listne۰Forall𑁒app P l1 l2 :
    listne۰Forall P (listne۰app l1 l2) ↔
      listne۰Forall P l1 ∧
      listne۰Forall P l2.
  Proof.
    apply Forall_app.
  Qed.
  Lemma listne۰Forall𑁒elem_of P l x :
    listne۰Forall P l →
    x ∈ l →
    P x.
  Proof.
    apply Forall𑁒elem_of.
  Qed.
End listne.
