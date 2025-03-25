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

Section map_oflatten.
  Context `{FinMap K M}.
  Context {A : Type}.

  Definition map_oflatten (m : M (option A)) :=
    omap id m.

  Lemma lookup_map_oflatten_None m k :
    m !! k = None →
    map_oflatten m !! k = None.
  Proof.
    rewrite lookup_omap => -> //.
  Qed.
  Lemma lookup_map_oflatten_Some_None m k :
    m !! k = Some None →
    map_oflatten m !! k = None.
  Proof.
    rewrite lookup_omap => -> //.
  Qed.
  Lemma lookup_map_oflatten_Some_Some {m k} a :
    m !! k = Some (Some a) →
    map_oflatten m !! k = Some a.
  Proof.
    rewrite lookup_omap_id_Some //.
  Qed.

  Lemma lookup_map_oflatten_Some_inv m k a :
    map_oflatten m !! k = Some a →
    m !! k = Some (Some a).
  Proof.
    intros Hoflatten_lookup.
    destruct (m !! k) as [[v |] |] eqn:Hm_lookup.
    all: rewrite lookup_omap Hm_lookup /= in Hoflatten_lookup.
    all: congruence.
  Qed.

  Lemma map_oflatten_empty m :
    (∀ k o, m !! k = Some o → o = None) →
    map_oflatten m = ∅.
  Proof.
    intros Hm.
    apply map_empty => k.
    rewrite eq_None_not_Some. intros (a & Hlookup%lookup_map_oflatten_Some_inv).
    naive_solver.
  Qed.

  Lemma map_oflatten_union m1 m2 :
    m1 ##ₘ m2 →
    map_oflatten (m1 ∪ m2) = map_oflatten m1 ∪ map_oflatten m2.
  Proof.
    intros.
    rewrite /map_oflatten map_omap_union //.
  Qed.

  Lemma map_oflatten_insert {m} k :
    m !! k = None →
    map_oflatten (<[k := None]> m) = map_oflatten m.
  Proof.
    intros Hlookup.
    rewrite /map_oflatten omap_insert_None // delete_notin // lookup_omap Hlookup //.
  Qed.
  Lemma map_oflatten_update {m} k a :
    map_oflatten (<[k := Some a]> m) = <[k := a]> (map_oflatten m).
  Proof.
    rewrite /map_oflatten omap_insert //.
  Qed.
End map_oflatten.
