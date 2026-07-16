Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.stack__code.
Require Import zoo_std.dynarray_1.
Require Import zoo.options.

Implicit Types v t : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition stack۰model t vs :=
    dynarray_1۰model t (reverse vs).

  #[global] Instance stack۰model𑁒timeless t vs :
    Timeless (stack۰model t vs).
  Proof.
    apply _.
  Qed.

  Lemma stack٠make𑁒spec :
    {{{
      True
    }}}
      stack٠create ()
    {{{
      t
    , RET t;
      stack۰model t []
    }}}.
  Proof.
    apply dynarray_1٠create𑁒spec.
  Qed.

  Lemma stack٠is_empty𑁒spec t vs :
    {{{
      stack۰model t vs
    }}}
      stack٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      stack۰model t vs
    }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp۰apply (dynarray_1٠is_empty𑁒spec with "Ht").
    rewrite (bool_decide_ext (reverse vs = []) (vs = [])) // -{1}reverse_nil. naive_solver.
  Qed.

  Lemma stack٠push𑁒spec t vs v :
    {{{
      stack۰model t vs
    }}}
      stack٠push t v
    {{{
      RET ();
      stack۰model t (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp۰apply (dynarray_1٠push𑁒spec with "Ht").
    rewrite -reverse_cons //.
  Qed.

  Lemma stack٠pop𑁒spec {t vs} v vs' :
    vs = v :: vs' →
    {{{
      stack۰model t vs
    }}}
      stack٠pop t
    {{{
      RET v;
      stack۰model t vs'
    }}}.
  Proof.
    iIntros (->) "%Φ Ht HΦ".
    wp۰apply (dynarray_1٠pop𑁒spec with "Ht"); last iSteps.
    rewrite reverse_cons //.
  Qed.
End zoo۰G.

Require zoo_std.stack__opaque.

#[global] Opaque stack۰model.
