Require Export stdpp.gmap.

Require Import zoo.prelude.
Require Import zoo.options.

Section gset.
  Context `{Countable K}.

  Implicit Type s : gset K.

  Lemma elem_ofｰsizeｰpos x s :
    x ∈ s →
    0 < size s.
  Proof.
    destruct_decide (size s = 0) as Hs. 2: lia.
    rewrite size_empty_iff in Hs.
    rewrite Hs //.
  Qed.
End gset.

Section list_to_set.
  Context `{Countable K}.

  Implicit Type l : list K.

  Lemma list_to_setｰempty l :
    list_to_set (C := gset K) l = ∅ ↔
    l = [].
  Proof.
    split.
    - destruct l; first done. set_solver.
    - intros ->. apply list_to_set_nil.
  Qed.
  Lemma list_to_setｰnot_empty l :
    list_to_set (C := gset K) l ≠ ∅ ↔
    l ≠ [].
  Proof.
    rewrite list_to_setｰempty //.
  Qed.
End list_to_set.
