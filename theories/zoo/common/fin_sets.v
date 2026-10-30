Require Export stdpp.fin_sets.

Require Import zoo.prelude.
Require Import zoo.options.

Section filter.
  Context `{FinSet A C}.
  Context (P : A → Prop) `{!∀ x, Decision (P x)}.

  #[global] Instance set_filterｰproper :
    Proper ((≡) ==> (≡)) (filter (B := C) P).
  Proof.
    rewrite /filter /set_filter.
    solve_proper.
  Qed.

  Lemma filterｰFalse s :
    (∀ x, x ∈ s → ¬ P x) →
    filter (B := C) P s ≡ ∅.
  Proof.
    move: s. refine (set_ind _ _ _ _).
    - apply _.
    - intros s1 s2 Hs Hs1.
      setoid_rewrite Hs in Hs1 => //.
    - set_solver.
    - set_solver.
  Qed.

  Lemma filterｰlist_to_set l :
    filter (B := C) P (list_to_set l) ≡ list_to_set (filter P l).
  Proof.
    induction l as [| x l IH] => /=.
    - apply filter_empty.
    - rewrite filter_union fin_sets.filter_singleton IH filter_cons.
      case_decide; set_solver.
  Qed.
End filter.

Section list_to_set.
  Context `{FinSet A C}.

  Abbreviation list_to_set := (
    list_to_set (C := C)
  ).

  Lemma elementsｰlist_to_setｰsubmseteq l :
    elements (list_to_set l) ⊆+ l.
  Proof.
    remember (list_to_set l) as s eqn:Hs.
    apply (reflexive_eq (R := equiv)) in Hs.
    move: s l Hs. refine (set_ind (C := C) _ _ _ _).
    - apply _.
    - intros s1 s2 Hs Hs1.
      setoid_rewrite Hs in Hs1 => //.
    - intros l _.
      rewrite elements_empty.
      apply submseteq_nil_l.
    - intros x s Hx IH l Heq.
      rewrite elements_union_singleton //.
      rewrite -(filter_app_complement (.= x) l).
      apply (submseteq_app [_]).
      + apply singleton_submseteq_l.
        set_solver.
      + apply IH.
        set_solver.
  Qed.

  Lemma sizeｰlist_to_setｰle l :
    size (list_to_set l) ≤ length l.
  Proof.
    apply submseteq_length, elementsｰlist_to_setｰsubmseteq.
  Qed.
End list_to_set.
