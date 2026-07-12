Require Export stdpp.fin_maps.
Require Export stdpp.fin_map_dom.

Require Import zoo.prelude.
Require Import zoo.common.option.
Require Import zoo.options.

Section dom.
  Context `{FinMapDom K M D}.
  Context {A : Type}.

  Implicit Types m : M A.

  Lemma elem_of_dom_1 m k :
    k ∈ dom m →
    is_Some (m !! k).
  Proof.
    rewrite elem_of_dom //.
  Qed.
End dom.

Section fmap.
  Context `{FinMapDom K M D}.
  Context {A : Type}.

  Implicit Types m : M A.

  Lemma lookup_fmap_None {B} (f : A → B) m k :
    (f <$> m) !! k = None ↔
    m !! k = None.
  Proof.
    rewrite lookup_fmap fmap_None //.
  Qed.
End fmap.

Section map_Forall.
  Context `{FinMap K M}.
  Context {A : Type}.

  Implicit Types m : M A.

  Lemma map_Forall_impl' P1 P2 m :
    map_Forall P1 m →
    ( ∀ k x,
      m !! k = Some x →
      P1 k x →
      P2 k x
    ) →
    map_Forall P2 m.
  Proof.
    rewrite !map_Forall_lookup. auto.
  Qed.

  Lemma map_Forall_insert_2' {P m} k x :
    P k x →
    map_Forall P (delete k m) →
    map_Forall P (<[k := x]> m).
  Proof.
    rewrite -insert_delete_eq.
    apply map_Forall_insert_2.
  Qed.

  Lemma map_Forall_delete_lookup P m k :
    map_Forall P (delete k m) ↔
      ∀ k' x,
      k ≠ k' →
      m !! k' = Some x →
      P k' x.
  Proof.
    rewrite map_Forall_lookup.
    setoid_rewrite lookup_delete_Some.
    naive_solver.
  Qed.
  Lemma map_Forall_delete_lookup_1 {P m k} k' x :
    map_Forall P (delete k m) →
    k ≠ k' →
    m !! k' = Some x →
    P k' x.
  Proof.
    rewrite map_Forall_delete_lookup.
    naive_solver.
  Qed.
  Lemma map_Forall_delete_lookup_2 P m k :
    ( ∀ k' x,
      k ≠ k' →
      m !! k' = Some x →
      P k' x
    ) →
    map_Forall P (delete k m).
  Proof.
    rewrite map_Forall_delete_lookup //.
  Qed.
End map_Forall.

Section map_Forall2.
  Context `{FinMapDom K M D}.

  Lemma map_Forall2_alt {A B R} (m : M A) (𝑚 : M B) :
    map_Forall2 R m 𝑚 ↔
      dom m ≡ dom 𝑚 ∧
        ∀ k x 𝑥,
        m !! k = Some x →
        𝑚 !! k = Some 𝑥 →
        R k x 𝑥.
  Proof.
    split.
    - intros Hm𝑚. split.
      + eapply map_Forall2_dom. done.
      + intros k x 𝑥 Hm_lookup H𝑚_lookup.
        specialize (Hm𝑚 k).
        rewrite Hm_lookup H𝑚_lookup // in Hm𝑚.
        invert Hm𝑚. done.
    - intros (Hdom & Hm𝑚) k.
      specialize (Hm𝑚 k).
      destruct (m !! k) as [x |] eqn:Hm_lookup.
      + destruct (elem_of_dom_1 𝑚 k) as (𝑥 & H𝑚_lookup).
        { apply elem_of_dom_2 in Hm_lookup. set_solver. }
        rewrite H𝑚_lookup. auto.
      + opose proof* (not_elem_of_dom_1 𝑚 k) as H𝑚_lookup.
        { apply not_elem_of_dom in Hm_lookup. set_solver. }
        rewrite H𝑚_lookup //.
  Qed.

  Lemma map_Forall2_flip {A B} R (m : M A) (𝑚 : M B) :
    map_Forall2 R m 𝑚 ↔
    map_Forall2 (λ k x 𝑥, R k 𝑥 x) 𝑚 m.
  Proof.
    rewrite !map_Forall2_alt. naive_solver.
  Qed.

  Lemma map_Forall2_lookup_None_l {A B R} {m : M A} {𝑚 : M B} k :
    map_Forall2 R m 𝑚 →
    m !! k = None →
    𝑚 !! k = None.
  Proof.
    rewrite -!not_elem_of_dom.
    intros Hdom%map_Forall2_dom.
    set_solver.
  Qed.
  Lemma map_Forall2_lookup_None_r {A B R} {m : M A} {𝑚 : M B} k :
    map_Forall2 R m 𝑚 →
    𝑚 !! k = None →
    m !! k = None.
  Proof.
    rewrite map_Forall2_flip.
    apply map_Forall2_lookup_None_l.
  Qed.

  Lemma map_Forall2_lookup_Some {A B R} {m : M A} {𝑚 : M B} k x 𝑥 :
    map_Forall2 R m 𝑚 →
    m !! k = Some x →
    𝑚 !! k = Some 𝑥 →
    R k x 𝑥.
  Proof.
    rewrite map_Forall2_alt. naive_solver.
  Qed.
  Lemma map_Forall2_lookup_Some_l {A B R} {m : M A} {𝑚 : M B} k x :
    map_Forall2 R m 𝑚 →
    m !! k = Some x →
      ∃ 𝑥,
      𝑚 !! k = Some 𝑥 ∧
      R k x 𝑥.
  Proof.
    intros Hm𝑚 Hm_lookup.
    apply elem_of_dom_2 in Hm_lookup as Hm_elem.
    apply map_Forall2_dom in Hm𝑚 as Hdom.
    destruct (elem_of_dom_1 𝑚 k) as (𝑥 & H𝑚_lookup); first set_solver.
    exists 𝑥. split; first done.
    eapply map_Forall2_lookup_Some; done.
  Qed.
  Lemma map_Forall2_lookup_Some_r {A B R} {m : M A} {𝑚 : M B} k 𝑥 :
    map_Forall2 R m 𝑚 →
    𝑚 !! k = Some 𝑥 →
      ∃ x,
      m !! k = Some x ∧
      R k x 𝑥.
  Proof.
    rewrite map_Forall2_flip.
    apply: map_Forall2_lookup_Some_l.
  Qed.

  Lemma map_Forall2_insert_l {A B R} {m : M A} {𝑚 : M B} k x 𝑥 :
    map_Forall2 R m 𝑚 →
    𝑚 !! k = Some 𝑥 →
    R k x 𝑥 →
    map_Forall2 R (<[k := x]> m) 𝑚.
  Proof.
    intros Hm𝑚 H𝑚_lookup Hx𝑥.
    odestruct map_Forall2_lookup_Some_r as (y & Hm_lookup & _); [done.. |].
    rewrite -(insert_id 𝑚 k 𝑥) //.
    apply map_Forall2_insert_2; done.
  Qed.
  Lemma map_Forall2_insert_r {A B R} {m : M A} {𝑚 : M B} k x 𝑥 :
    map_Forall2 R m 𝑚 →
    m !! k = Some x →
    R k x 𝑥 →
    map_Forall2 R m (<[k := 𝑥]> 𝑚).
  Proof.
    setoid_rewrite map_Forall2_flip.
    apply: map_Forall2_insert_l.
  Qed.

  Lemma map_Forall2_fmap_l {A B C R} (f : A → C) (m : M A) (𝑚 : M B) :
    map_Forall2 (λ k x 𝑥, R k (f x) 𝑥) m 𝑚 ↔
    map_Forall2 R (f <$> m) 𝑚.
  Proof.
    rewrite !map_Forall2_alt dom_fmap.
    setoid_rewrite lookup_fmap_Some.
    naive_solver.
  Qed.
  Lemma map_Forall2_fmap_l_1 {A B C R} (f : A → C) (m : M A) (𝑚 : M B) :
    map_Forall2 (λ k x 𝑥, R k (f x) 𝑥) m 𝑚 →
    map_Forall2 R (f <$> m) 𝑚.
  Proof.
    rewrite map_Forall2_fmap_l //.
  Qed.
  Lemma map_Forall2_fmap_l_2 {A B C R} (f : A → C) (m : M A) (𝑚 : M B) :
    map_Forall2 R (f <$> m) 𝑚 →
    map_Forall2 (λ k x 𝑥, R k (f x) 𝑥) m 𝑚.
  Proof.
    rewrite -map_Forall2_fmap_l //.
  Qed.
  Lemma map_Forall2_fmap_r {A B C R} (f : B → C) (m : M A) (𝑚 : M B) :
    map_Forall2 (λ k x 𝑥, R k x (f 𝑥)) m 𝑚 ↔
    map_Forall2 R m (f <$> 𝑚).
  Proof.
    setoid_rewrite map_Forall2_flip at 1 2.
    apply: map_Forall2_fmap_l.
  Qed.
  Lemma map_Forall2_fmap_r_1 {A B C R} (f : B → C) (m : M A) (𝑚 : M B) :
    map_Forall2 (λ k x 𝑥, R k x (f 𝑥)) m 𝑚 →
    map_Forall2 R m (f <$> 𝑚).
  Proof.
    rewrite map_Forall2_fmap_r //.
  Qed.
  Lemma map_Forall2_fmap_r_2 {A B C R} (f : B → C) (m : M A) (𝑚 : M B) :
    map_Forall2 R m (f <$> 𝑚) →
    map_Forall2 (λ k x 𝑥, R k x (f 𝑥)) m 𝑚.
  Proof.
    rewrite -map_Forall2_fmap_r //.
  Qed.
End map_Forall2.

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
    rewrite /map_oflatten omap_insert_None // delete_id // lookup_omap Hlookup //.
  Qed.
  Lemma map_oflatten_update {m} k a :
    map_oflatten (<[k := Some a]> m) = <[k := a]> (map_oflatten m).
  Proof.
    rewrite /map_oflatten omap_insert //.
  Qed.
End map_oflatten.
