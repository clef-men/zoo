Require Export stdpp.gmap.

Require Import zoo.prelude.
Require Import zoo.options.

Section list_to_set.
  Context `{Countable K}.

  Implicit Types l : list K.

  Lemma list_to_set𑁒empty l :
    list_to_set (C := gset K) l = ∅ ↔
    l = [].
  Proof.
    split.
    - destruct l; first done. set_solver.
    - intros ->. apply list_to_set_nil.
  Qed.
  Lemma list_to_set𑁒not_empty l :
    list_to_set (C := gset K) l ≠ ∅ ↔
    l ≠ [].
  Proof.
    rewrite list_to_set𑁒empty //.
  Qed.
End list_to_set.
