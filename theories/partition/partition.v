From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  lst.
From partition Require Import
  partition__types.
From partition Require Export
  partition__code.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types sz : nat.
Implicit Types elt : location.
Implicit Types elts : list location.
Implicit Types v v_elts t : val.
Implicit Types cl : gset location.
Implicit Types part : gset (gset location).

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition partition_model t part : iProp Σ.
  Admitted.

  Definition partition_elt t elt v : iProp Σ.
  Admitted.

  (* #[global] Instance partition_model_timeless t part : *)
  (*   Timeless (partition_model t part). *)
  (* Proof. *)
  (*   apply _. *)
  (* Qed. *)
  (* #[global] Instance partition_elt_timeless t elt v : *)
  (*   Timeless (partition_elt t elt v). *)
  (* Proof. *)
  (*   apply _. *)
  (* Qed. *)

  Lemma partition_model_non_empty {t part} cl :
    cl ∈ part →
    partition_model t part ⊢
    ⌜cl ≠ ∅⌝.
  Proof.
  Admitted.
  Lemma partition_model_disjoint {t part} elt cl1 cl2 :
    cl1 ∈ part →
    elt ∈ cl1 →
    cl2 ∈ part →
    elt ∈ cl2 →
    partition_model t part ⊢
    ⌜cl1 = cl2⌝.
  Proof.
  Admitted.

  Lemma partition_elt_exclusive t1 t2 elt v1 v2 :
    partition_elt t1 elt v1 -∗
    partition_elt t2 elt v2 -∗
    False.
  Proof.
  Admitted.
  Lemma partition_elt_valid t part elt v :
    partition_model t part -∗
    partition_elt t elt v -∗
      ∃ cl,
      ⌜cl ∈ part⌝ ∗
      ⌜elt ∈ cl⌝.
  Proof.
  Admitted.

  Lemma partition_elt_equal_spec t elt1 v1 elt2 v2 :
    {{{
      partition_elt t elt1 v1 ∗
      partition_elt t elt2 v2
    }}}
      partition_elt_equal #elt1 #elt2
    {{{
      RET #(bool_decide (elt1 = elt2));
      partition_elt t elt1 v1 ∗
      partition_elt t elt2 v2
    }}}.
  Proof.
  Admitted.

  Lemma partition_elt_equiv_spec t part elt1 v1 elt2 v2 :
    {{{
      partition_model t part ∗
      partition_elt t elt1 v1 ∗
      partition_elt t elt2 v2
    }}}
      partition_elt_equiv #elt1 #elt2
    {{{ b,
      RET #b;
      partition_model t part ∗
      partition_elt t elt1 v1 ∗
      partition_elt t elt2 v2 ∗
      ⌜ ∀ cl1 cl2,
        cl1 ∈ part →
        elt1 ∈ cl1 →
        cl2 ∈ part →
        elt2 ∈ cl2 →
        if b then cl1 = cl2 else cl1 ≠ cl2
      ⌝
    }}}.
  Proof.
  Admitted.

  Lemma partition_elt_repr_spec t part elt v :
    {{{
      partition_model t part ∗
      partition_elt t elt v
    }}}
      partition_elt_repr #elt
    {{{ elt',
      RET #elt';
      partition_model t part ∗
      partition_elt t elt v ∗
      ⌜ ∀ cl,
        cl ∈ part →
        elt ∈ cl ↔ elt' ∈ cl
      ⌝
    }}}.
  Proof.
  Admitted.

  Lemma partition_elt_get_spec t elt v :
    {{{
      partition_elt t elt v
    }}}
      partition_elt_get #elt
    {{{
      RET v;
      partition_elt t elt v
    }}}.
  Proof.
  Admitted.

  Lemma partition_elt_cardinal_spec t part elt v :
    {{{
      partition_model t part ∗
      partition_elt t elt v
    }}}
      partition_elt_cardinal #elt
    {{{ sz,
      RET #sz;
      partition_model t part ∗
      partition_elt t elt v ∗
      ⌜ ∀ cl,
        cl ∈ part →
        elt ∈ cl →
        size cl = sz
      ⌝
    }}}.
  Proof.
  Admitted.

  Lemma partition_create_spec v :
    {{{
      True
    }}}
      partition_create v
    {{{ t elt,
      RET (t, #elt);
      partition_model t {[{[elt]}]} ∗
      partition_elt t elt v
    }}}.
  Proof.
  Admitted.

  Lemma partition_add_same_class_spec t part elt v v' :
    {{{
      partition_model t part ∗
      partition_elt t elt v
    }}}
      partition_add_same_class #elt v'
    {{{ elt' part',
      RET #elt';
      partition_model t part' ∗
      partition_elt t elt v ∗
      partition_elt t elt' v' ∗
      ⌜ ∃ part'' cl,
        elt ∈ cl ∧
        part = part'' ∪ {[cl]} ∧
        part' = part'' ∪ {[cl ∪ {[elt']}]}
      ⌝
    }}}.
  Proof.
  Admitted.

  Lemma partition_add_new_class_spec t part v :
    {{{
      partition_model t part
    }}}
      partition_add_new_class t v
    {{{ elt,
      RET #elt;
      partition_model t (part ∪ {[{[elt]}]}) ∗
      partition_elt t elt v
    }}}.
  Proof.
  Admitted.

  Lemma partition_refine_spec {t part v_elts} elts :
    lst_model' v_elts (#@{location} <$> elts) →
    {{{
      partition_model t part
    }}}
      partition_refine t v_elts
    {{{ part',
      RET ();
      partition_model t part' ∗
      ⌜ ∀ cl',
        cl' ∈ part' ↔
          cl' ≠ ∅ ∧
            ∃ cl,
            cl ∈ part ∧
            ( cl' = cl ∩ list_to_set elts
            ∨ cl' = cl ∖ list_to_set elts
            )
      ⌝
    }}}.
  Proof.
  Admitted.
End zoo_G.
