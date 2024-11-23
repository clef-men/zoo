From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  stack__code.
From zoo_std Require Import
  dynarray_1.
From zoo Require Import
  options.

Implicit Types v t : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition stack_model t vs :=
    dynarray_1_model t (reverse vs).

  #[global] Instance stack_model_timeless t vs :
    Timeless (stack_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma stack_make_spec :
    {{{
      True
    }}}
      stack_create ()
    {{{ t,
      RET t;
      stack_model t []
    }}}.
  Proof.
    apply dynarray_1_create_spec.
  Qed.

  Lemma stack_is_empty_spec t vs :
    {{{
      stack_model t vs
    }}}
      stack_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      stack_model t vs
    }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp_apply (dynarray_1_is_empty_spec with "Ht").
    rewrite (bool_decide_ext (reverse vs = []) (vs = [])) // -{1}reverse_nil. naive_solver.
  Qed.

  Lemma stack_push_spec t vs v :
    {{{
      stack_model t vs
    }}}
      stack_push t v
    {{{
      RET ();
      stack_model t (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp_apply (dynarray_1_push_spec with "Ht").
    rewrite -reverse_cons //.
  Qed.

  Lemma stack_pop_spec {t vs} v vs' :
    vs = v :: vs' →
    {{{
      stack_model t vs
    }}}
      stack_pop t
    {{{
      RET v;
      stack_model t vs'
    }}}.
  Proof.
    iIntros (->) "%Φ Ht HΦ".
    wp_apply (dynarray_1_pop_spec with "Ht"); last iSteps.
    rewrite reverse_cons //.
  Qed.
End zoo_G.

#[global] Opaque stack_create.
#[global] Opaque stack_is_empty.
#[global] Opaque stack_push.
#[global] Opaque stack_pop.

#[global] Opaque stack_model.
