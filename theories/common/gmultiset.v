From stdpp Require Export
  gmultiset.

From zebre Require Import
  prelude.
From zebre Require Import
  options.

Section lemmas.
  Context `{Countable A}.

  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.

  Lemma gmultiset_size_singleton_inv X x y :
    size X = 1 →
    x ∈ X →
    y ∈ X →
    x = y.
  Proof.
    rewrite /size /gmultiset_size /= -!gmultiset_elem_of_elements.
    generalize (elements X). intros [| ? l] ?*; simplify.
    rewrite (nil_length_inv l) // !elem_of_list_singleton. congruence.
  Qed.
  Lemma gmultiset_size_1_elem_of X :
    size X = 1 →
      ∃ x,
      X = {[+x+]}.
  Proof.
    intros Hsize.
    destruct (gmultiset_size_pos_elem_of X) as (x & Hx); first lia. exists x.
    assert ({[+x+]} ⊆ X) by multiset_solver.
    rewrite (gmultiset_disj_union_difference {[+x+]} X) //.
    assert (X ∖ {[+x+]} = ∅) as ->; last multiset_solver.
    rewrite -gmultiset_size_empty_iff gmultiset_size_difference // gmultiset_size_singleton. lia.
  Qed.
End lemmas.
