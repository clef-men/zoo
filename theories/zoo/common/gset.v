From stdpp Require Export
  gmap.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Section list_to_set.
  Context `{Countable K}.

  Implicit Types l : list K.

  Lemma list_to_set_empty l :
    list_to_set (C := gset K) l = ∅ ↔
    l = [].
  Proof.
    split.
    - destruct l; first done. set_solver.
    - intros ->. apply list_to_set_nil.
  Qed.
  Lemma list_to_set_not_empty l :
    list_to_set (C := gset K) l ≠ ∅ ↔
    l ≠ [].
  Proof.
    rewrite list_to_set_empty //.
  Qed.
End list_to_set.
