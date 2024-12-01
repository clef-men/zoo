From iris.algebra Require Import
  gset.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  mono_set.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  lst
  xdlchain.
From partition Require Import
  partition__types.
From partition Require Export
  partition__code.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types sz : nat.
Implicit Types elt first last split : location.
Implicit Types v v_elts : val.
Implicit Types cl : gset location.
Implicit Types part : gset (gset location).
Implicit Types γ : gname.

Record partition_descr := {
  partition_descr_class : location ;
  partition_descr_elts : list location ;
}.

#[local] Instance partition_descr_inhabited : Inhabited partition_descr :=
  populate {|
    partition_descr_class := inhabitant ;
    partition_descr_elts := inhabitant ;
  |}.
#[local] Instance partition_descr_eq_dec : EqDecision partition_descr :=
  ltac:(solve_decision).
#[local] Instance partition_descr_countable :
  Countable partition_descr.
Proof.
  pose encode descr := (
    descr.(partition_descr_class),
    descr.(partition_descr_elts)
  ).
  pose decode := λ '(class, elts), {|
    partition_descr_class := class ;
    partition_descr_elts := elts ;
  |}.
  refine (inj_countable' encode decode _). intros []. done.
Qed.

Implicit Types descr : partition_descr.
Implicit Types descrs : gset partition_descr.

Class PartitionG Σ `{zoo_G : !ZooG Σ} := {
  #[local] partition_G_elts_G :: MonoSetG Σ location ;
}.

Definition partition_Σ := #[
  mono_set_Σ location
].
#[global] Instance subG_partition_Σ Σ `{zoo_G : !ZooG Σ} :
  subG partition_Σ Σ →
  PartitionG Σ.
Proof.
  solve_inG.
Qed.

Section partition_G.
  Context `{partition_G : PartitionG Σ}.

  #[local] Definition partition_elts_auth γ elts :=
    mono_set_auth γ (DfracOwn 1) elts.
  #[local] Definition partition_elts_elem γ elt :=
    mono_set_elem γ elt.

  Definition partition_model γ part : iProp Σ :=
    ∃ descrs,
    ⌜part = set_map (list_to_set ∘ partition_descr_elts) descrs⌝ ∗
    partition_elts_auth γ ([^(∪) set] descr ∈ descrs, list_to_set descr.(partition_descr_elts)) ∗
    ( [∗ set] descr ∈ descrs,
      ∃ first last prev_descr prev next_descr next,
      ⌜head descr.(partition_descr_elts) = Some first⌝ ∗
      ⌜list.last descr.(partition_descr_elts) = Some last⌝ ∗
      ⌜prev_descr ∈ descrs⌝ ∗
      ⌜list.last prev_descr.(partition_descr_elts) = Some prev⌝ ∗
      ⌜next_descr ∈ descrs⌝ ∗
      ⌜head next_descr.(partition_descr_elts) = Some next⌝ ∗
      descr.(partition_descr_class).[first] ↦ #first ∗
      descr.(partition_descr_class).[last] ↦ #last ∗
      descr.(partition_descr_class).[len] ↦ #(length descr.(partition_descr_elts)) ∗
      descr.(partition_descr_class).[split] ↦ #first ∗
      descr.(partition_descr_class).[split_len] ↦ #0 ∗
      xdlchain_model #prev descr.(partition_descr_elts) #next ∗
      ( [∗ list] elt ∈ descr.(partition_descr_elts),
        elt.[class_] ↦ #descr.(partition_descr_class) ∗
        elt.[seen] ↦ #false
      )
    ).

  Definition partition_elt γ elt v : iProp Σ :=
    partition_elts_elem γ elt ∗
    elt.[data] ↦ v.

  #[global] Instance partition_model_timeless γ part :
    Timeless (partition_model γ part).
  Proof.
    apply _.
  Qed.
  #[global] Instance partition_elt_timeless γ elt v :
    Timeless (partition_elt γ elt v).
  Proof.
    apply _.
  Qed.

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
End partition_G.

#[global] Opaque partition_elt_equal.
#[global] Opaque partition_elt_equiv.
#[global] Opaque partition_elt_repr.
#[global] Opaque partition_elt_get.
#[global] Opaque partition_elt_cardinal.
#[global] Opaque partition_create.
#[global] Opaque partition_add_same_class.
#[global] Opaque partition_add_new_class.
#[global] Opaque partition_refine.

#[global] Opaque partition_model.
#[global] Opaque partition_elt.
