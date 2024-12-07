From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  random__code.
From zoo Require Import
  options.

Implicit Types t : val.

Parameter random_model : ∀ `{zoo_G : !ZooG Σ}, val → iProp Σ.

Axiom random_create_spec : ∀ `{zoo_G : !ZooG Σ},
  {{{
    True
  }}}
    random_create ()
  {{{ t,
    RET t;
    random_model t
  }}}.

Axiom random_bits_spec : ∀ `{zoo_G : !ZooG Σ} t,
  {{{
    random_model t
  }}}
    random_bits t
  {{{ (n : Z),
    RET #n;
    random_model t
  }}}.

Axiom random_int_spec : ∀ `{zoo_G : !ZooG Σ} t ub,
  (0 < ub)%Z →
  {{{
    random_model t
  }}}
    random_int t #ub
  {{{ n,
    RET #n;
    ⌜0 ≤ n < ub⌝%Z ∗
    random_model t
  }}}.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma random_int_spec_nat t (ub : nat) :
    0 < ub →
    {{{
      random_model t
    }}}
      random_int t #ub
    {{{ n,
      RET #n;
      ⌜n < ub⌝ ∗
      random_model t
    }}}.
  Proof.
    iIntros "%Hub %Φ Ht HΦ".
    wp_apply (random_int_spec with "Ht") as (n) "(%Hn & Ht)"; first lia.
    Z_to_nat n. iSteps.
  Qed.

  Lemma random_int_in_range_spec t lb ub :
    (lb < ub)%Z →
    {{{
      random_model t
    }}}
      random_int_in_range t #lb #ub
    {{{ n,
      RET #n;
      ⌜lb ≤ n < ub⌝%Z ∗
      random_model t
    }}}.
  Proof.
    iIntros "%Hlt %Φ Ht HΦ".
    wp_rec.
    wp_smart_apply (random_int_spec with "Ht") as "%n (%Hn & Ht)"; first lia.
    iSteps.
  Qed.
  Lemma random_int_in_range_spec_nat t lb ub :
    lb < ub →
    {{{
      random_model t
    }}}
      random_int_in_range t #lb #ub
    {{{ n,
      RET #n;
      ⌜lb ≤ n < ub⌝ ∗
      random_model t
    }}}.
  Proof.
    iIntros "%Hlt %Φ Ht HΦ".
    wp_rec.
    wp_smart_apply (random_int_spec with "Ht") as "%n (%Hn & Ht)"; first lia.
    wp_pures.
    Z_to_nat n. rewrite -Nat2Z.inj_add. iSteps.
  Qed.
End zoo_G.

#[global] Opaque random_int_in_range.
