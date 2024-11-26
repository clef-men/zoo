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
Implicit Types v v_elts : val.
Implicit Types cl : gset location.
Implicit Types part : gset (gset location).
Implicit Types γ : gname.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition partition_model γ part : iProp Σ.
  Admitted.

  Definition partition_elt γ elt v : iProp Σ.
  Admitted.

  (* #[global] Instance partition_model_timeless γ part : *)
  (*   Timeless (partition_model γ part). *)
  (* Proof. *)
  (*   apply _. *)
  (* Qed. *)
  (* #[global] Instance partition_elt_timeless γ elt v : *)
  (*   Timeless (partition_elt γ elt v). *)
  (* Proof. *)
  (*   apply _. *)
  (* Qed. *)

  Lemma partition_model_non_empty {γ part} cl :
    cl ∈ part →
    partition_model γ part ⊢
    ⌜cl ≠ ∅⌝.
  Proof.
  Admitted.
  Lemma partition_model_disjoint {γ part} elt cl1 cl2 :
    cl1 ∈ part →
    elt ∈ cl1 →
    cl2 ∈ part →
    elt ∈ cl2 →
    partition_model γ part ⊢
    ⌜cl1 = cl2⌝.
  Proof.
  Admitted.

  Lemma partition_elt_exclusive t1 t2 elt v1 v2 :
    partition_elt t1 elt v1 -∗
    partition_elt t2 elt v2 -∗
    False.
  Proof.
  Admitted.
  Lemma partition_elt_valid γ part elt v :
    partition_model γ part -∗
    partition_elt γ elt v -∗
      ∃ cl,
      ⌜cl ∈ part⌝ ∗
      ⌜elt ∈ cl⌝.
  Proof.
  Admitted.

  Lemma partition_elt_equal_spec γ elt1 v1 elt2 v2 :
    {{{
      partition_elt γ elt1 v1 ∗
      partition_elt γ elt2 v2
    }}}
      partition_elt_equal #elt1 #elt2
    {{{
      RET #(bool_decide (elt1 = elt2));
      partition_elt γ elt1 v1 ∗
      partition_elt γ elt2 v2
    }}}.
  Proof.
  Admitted.

  Lemma partition_elt_equiv_spec γ part elt1 v1 elt2 v2 :
    {{{
      partition_model γ part ∗
      partition_elt γ elt1 v1 ∗
      partition_elt γ elt2 v2
    }}}
      partition_elt_equiv #elt1 #elt2
    {{{ b,
      RET #b;
      partition_model γ part ∗
      partition_elt γ elt1 v1 ∗
      partition_elt γ elt2 v2 ∗
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

  Lemma partition_elt_repr_spec γ part elt v :
    {{{
      partition_model γ part ∗
      partition_elt γ elt v
    }}}
      partition_elt_repr #elt
    {{{ elt',
      RET #elt';
      partition_model γ part ∗
      partition_elt γ elt v ∗
      ⌜ ∀ cl,
        cl ∈ part →
        elt ∈ cl ↔ elt' ∈ cl
      ⌝
    }}}.
  Proof.
  Admitted.

  Lemma partition_elt_get_spec γ elt v :
    {{{
      partition_elt γ elt v
    }}}
      partition_elt_get #elt
    {{{
      RET v;
      partition_elt γ elt v
    }}}.
  Proof.
  Admitted.

  Lemma partition_elt_cardinal_spec γ part elt v :
    {{{
      partition_model γ part ∗
      partition_elt γ elt v
    }}}
      partition_elt_cardinal #elt
    {{{ sz,
      RET #sz;
      partition_model γ part ∗
      partition_elt γ elt v ∗
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
    {{{ γ elt,
      RET #elt;
      partition_model γ {[{[elt]}]} ∗
      partition_elt γ elt v
    }}}.
  Proof.
  Admitted.

  Lemma partition_add_same_class_spec γ part elt v v' :
    {{{
      partition_model γ part ∗
      partition_elt γ elt v
    }}}
      partition_add_same_class #elt v'
    {{{ elt' part',
      RET #elt';
      partition_model γ part' ∗
      partition_elt γ elt v ∗
      partition_elt γ elt' v' ∗
      ⌜ ∃ part'' cl,
        elt ∈ cl ∧
        part = part'' ∪ {[cl]} ∧
        part' = part'' ∪ {[cl ∪ {[elt']}]}
      ⌝
    }}}.
  Proof.
  Admitted.

  Lemma partition_add_new_class_spec γ part v :
    {{{
      partition_model γ part
    }}}
      partition_add_new_class v
    {{{ elt,
      RET #elt;
      partition_model γ (part ∪ {[{[elt]}]}) ∗
      partition_elt γ elt v
    }}}.
  Proof.
  Admitted.

  Lemma partition_refine_spec {γ part v_elts} elts :
    lst_model' v_elts (#@{location} <$> elts) →
    {{{
      partition_model γ part
    }}}
      partition_refine v_elts
    {{{ part',
      RET ();
      partition_model γ part' ∗
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

#[global] Opaque partition_elt_equal.
#[global] Opaque partition_elt_equiv.
#[global] Opaque partition_elt_repr.
#[global] Opaque partition_elt_get.
#[global] Opaque partition_elt_cardinal.
#[global] Opaque partition_create.
#[global] Opaque partition_add_same_class.
#[global] Opaque partition_add_new_class.
#[global] Opaque partition_refine.
