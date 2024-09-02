From stdpp Require Export
  fin_maps.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Section kmap.
  Context `{FinMap K1 M1} `{FinMap K2 M2}.
  Context (f : K1 → K2) `{!Inj (=) (=) f}.

  Notation kmap := (
    kmap (M1 := M1) (M2 := M2)
  ).

  #[local] Lemma NoDup_fst_prod_map_map_to_list {A} (m : M1 A) :
    NoDup (prod_map f id <$> map_to_list m).*1.
  Proof.
    rewrite -list_fmap_compose -(list_fmap_ext (f ∘ fst)) // list_fmap_compose.
    apply NoDup_fmap; first done.
    apply NoDup_fst_map_to_list.
  Qed.
  Lemma map_to_list_kmap {A} (m : M1 A) :
    map_to_list (kmap f m) ≡ₚ prod_map f id <$> map_to_list m.
  Proof.
    apply map_to_list_to_map, NoDup_fst_prod_map_map_to_list.
  Qed.
  Lemma kmap_list_to_map {A} (l : list (K1 * A)) :
    NoDup l.*1 →
    kmap f (list_to_map l) = list_to_map (prod_map f id <$> l).
  Proof.
    intros Hnodup.
    apply list_to_map_proper.
    { apply NoDup_fst_prod_map_map_to_list. }
    rewrite map_to_list_to_map //.
  Qed.
End kmap.
