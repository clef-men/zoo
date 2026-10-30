Require Export stdpp.gmap.

Require Import zoo.prelude.
Require Export zoo.common.fin_maps.
Require Import zoo.common.list.
Require Import zoo.options.

Section gset_to_gmap.
  Context `{Countable K}.
  Context {A : Type}.

  Implicit Type s : gset K.
  Implicit Type x : A.

  Lemma sizeｰgset_to_gmap x s :
    size (gset_to_gmap x s) = size s.
  Proof.
    rewrite gset_to_gmap_set_to_map map_size_list_to_map.
    { apply NoDup_fmap_fst. 1: set_solver.
      apply NoDup_fmap. 1: congruence.
      apply NoDup_elements.
    }
    simp_length.
  Qed.

  Lemma map_Forallｰgset_to_gmap ϕ x s :
    map_Forall ϕ (gset_to_gmap x s) ↔
    set_Forall (λ k, ϕ k x) s.
  Proof.
    rewrite map_Forall_to_list set_Forall_elements map_to_list_gset_to_gmap Forall_fmap //.
  Qed.
End gset_to_gmap.
