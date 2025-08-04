From iris.algebra Require Export
  big_op
  gset.

From zoo Require Import
  prelude.
From zoo.iris.algebra Require Export
  base.
From zoo Require Import
  options.

Section big_opS.
  Context {SI : sidx}.
  Context `{!Monoid (M := M) o}.
  Context `{Countable A}.

  Implicit Types f : A → M.

  Lemma big_opS_singleton_L `{!LeibnizEquiv M} f x :
    ([^o set] y ∈ {[x]}, f y) = f x.
  Proof.
    apply leibniz_equiv, big_opS_singleton.
  Qed.
End big_opS.

Notation "'[∪' 'list]' k ↦ s ∈ l , P" := (
  big_opL union (λ k s, P) l
)(at level 200,
  l at level 10,
  k, s at level 1,
  right associativity,
  format "[∪  list]  k  ↦  s  ∈  l ,  P"
) : stdpp_scope.
Notation "'[∪' 'list]' s ∈ l , P" := (
  big_opL union (λ _ s, P) l
)(at level 200,
  l at level 10,
  s at level 1,
  right associativity,
  format "[∪  list]  s  ∈  l ,  P"
) : stdpp_scope.

Section big_unionL.
  Context {SI : sidx}.
  Context {A : Type}.
  Context `{Countable K}.

  Implicit Types x : A.
  Implicit Types l : list A.
  Implicit Types f : nat → A → gset K.

  Lemma big_unionL_elem_of {f} y l :
    y ∈ ([∪ list] k ↦ x ∈ l, f k x) →
      ∃ i x,
      l !! i = Some x ∧
      y ∈ f i x.
  Proof.
    cut (∀ n,
      y ∈ ([∪ list] k ↦ x ∈ l, f (n + k) x) →
        ∃ i x,
        l !! i = Some x ∧
        y ∈ f (n + i) x
    ).
    { move/(_ 0) => //. }
    induction l as [| x l IH] => /= n Hx; first done.
    apply elem_of_union in Hx as [Hx | Hx].
    - exists 0, x. done.
    - setoid_rewrite Nat.add_succ_r in Hx.
      specialize (IH (S n) Hx) as (i & x' & ? & ?).
      exists (S i), x'. split.
      + rewrite lookup_cons //.
      + rewrite Nat.add_succ_r //.
  Qed.
End big_unionL.

Notation "'[∪' 'set]' s ∈ X , P" := (
  big_opS union (λ s, P) X
)(at level 200,
  X at level 10,
  s at level 1,
  right associativity,
  format "[∪  set]  s  ∈  X ,  P"
) : stdpp_scope.

Section big_unionS.
  Context {SI : sidx}.
  Context `{Countable A}.
  Context `{Countable K}.

  Implicit Types x : A.
  Implicit Types X : gset A.
  Implicit Types f : A → gset K.

  Lemma big_unionS_elem_of {f} y X :
    y ∈ ([∪ set] x ∈ X, f x) →
      ∃ x,
      x ∈ X ∧
      y ∈ f x.
  Proof.
    rewrite big_opS_elements.
    intros (i & s & Hs%elem_of_list_lookup_2%elem_of_elements & Hy)%big_unionL_elem_of.
    naive_solver.
  Qed.
End big_unionS.

Notation "'[∪' 'map]' k ↦ x ∈ m , P" := (
  big_opM union (λ k x, P) m
)(at level 200,
  m at level 10,
  k, x at level 1,
  right associativity,
  format "[∪  map]  k  ↦  x  ∈  m ,  P"
) : stdpp_scope.
Notation "'[∪' 'map]' x ∈ m , P" := (
  big_opM union (λ _ x, P) m
)(at level 200,
  m at level 10,
  x at level 1,
  right associativity,
  format "[∪  map]  x  ∈  m ,  P"
) : stdpp_scope.

Section big_unionM.
  Context {SI : sidx}.
  Context `{Countable K}.
  Context {A : Type}.
  Context `{Countable B}.

  Implicit Types k : K.
  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types m : gmap K A.
  Implicit Types f : K → A → gset B.

  Lemma big_unionM_elem_of {f} y m :
    y ∈ ([∪ map] k ↦ x ∈ m, f k x) →
      ∃ k x,
      m !! k = Some x ∧
      y ∈ f k x.
  Proof.
    rewrite big_opM_map_to_list.
    intros (i & (k, x) & Hlookup%elem_of_list_lookup_2%elem_of_map_to_list & Hy)%big_unionL_elem_of.
    naive_solver.
  Qed.
End big_unionM.
