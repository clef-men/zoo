From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre.std Require Import
  dynarray.
From zebre Require Import
  options.

Implicit Types v t : val.

Definition stack_create :=
  dynarray_create.

Definition stack_is_empty :=
  dynarray_is_empty.

Definition stack_push :=
  dynarray_push.

Definition stack_pop :=
  dynarray_pop.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Definition stack_model t vs :=
    dynarray_model t (reverse vs).

  #[global] Instance stack_model_timeless t vs :
    Timeless (stack_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma stack_make_spec :
    {{{ True }}}
      stack_create #()
    {{{ t,
      RET t;
      stack_model t []
    }}}.
  Proof.
    apply dynarray_create_spec.
  Qed.

  Lemma stack_is_empty_spec t vs :
    {{{
      stack_model t vs
    }}}
      stack_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      stack_model t vs
    }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp_apply (dynarray_is_empty_spec with "Ht").
    rewrite (bool_decide_ext (reverse vs = []) (vs = [])) // -{1}reverse_nil. naive_solver.
  Qed.

  Lemma stack_push_spec t vs v :
    {{{
      stack_model t vs
    }}}
      stack_push t v
    {{{
      RET #();
      stack_model t (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp_apply (dynarray_push_spec with "Ht").
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
    wp_apply (dynarray_pop_spec with "Ht"); last iSteps.
    rewrite reverse_cons //.
  Qed.
End zebre_G.

#[global] Opaque stack_create.
#[global] Opaque stack_is_empty.
#[global] Opaque stack_push.
#[global] Opaque stack_pop.

#[global] Opaque stack_model.
