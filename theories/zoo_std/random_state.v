Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Import zoo.diaframe.
Require Export zoo_std.base.
Require Export zoo_std.random_state__code.
Require Import zoo.options.

Implicit Types t : val.

Parameter random_state_model : ∀ `{zoo_G : !ZooG Σ}, val → iProp Σ.

Axiom random_state٠create𑁒spec : ∀ `{zoo_G : !ZooG Σ},
  {{{
    True
  }}}
    random_state٠create ()
  {{{
    t
  , RET t;
    random_state_model t
  }}}.

Axiom random_state٠bits𑁒spec : ∀ `{zoo_G : !ZooG Σ} t,
  {{{
    random_state_model t
  }}}
    random_state٠bits t
  {{{
    (n : Z)
  , RET #n;
    random_state_model t
  }}}.

Axiom random_state٠int𑁒spec : ∀ `{zoo_G : !ZooG Σ} t ub,
  (0 < ub)%Z →
  {{{
    random_state_model t
  }}}
    random_state٠int t #ub
  {{{
    n
  , RET #n;
    ⌜0 ≤ n < ub⌝%Z ∗
    random_state_model t
  }}}.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma random_state٠int𑁒spec_nat t (ub : nat) :
    0 < ub →
    {{{
      random_state_model t
    }}}
      random_state٠int t #ub
    {{{
      n
    , RET #n;
      ⌜n < ub⌝ ∗
      random_state_model t
    }}}.
  Proof.
    iIntros "%Hub %Φ Ht HΦ".
    wp_apply (random_state٠int𑁒spec with "Ht") as (n) "(%Hn & Ht)"; first lia.
    Z_to_nat n. iSteps.
  Qed.

  Lemma random_state٠int_in_range𑁒spec t lb ub :
    (lb < ub)%Z →
    {{{
      random_state_model t
    }}}
      random_state٠int_in_range t #lb #ub
    {{{
      n
    , RET #n;
      ⌜lb ≤ n < ub⌝%Z ∗
      random_state_model t
    }}}.
  Proof.
    iIntros "%Hlt %Φ Ht HΦ".
    wp_rec.
    wp_apply+ (random_state٠int𑁒spec with "Ht") as "%n (%Hn & Ht)"; first lia.
    iSteps.
  Qed.
  Lemma random_state٠int_in_range𑁒spec_nat t lb ub :
    lb < ub →
    {{{
      random_state_model t
    }}}
      random_state٠int_in_range t #lb #ub
    {{{
      n
    , RET #n;
      ⌜lb ≤ n < ub⌝ ∗
      random_state_model t
    }}}.
  Proof.
    iIntros "%Hlt %Φ Ht HΦ".
    wp_rec.
    wp_apply+ (random_state٠int𑁒spec with "Ht") as "%n (%Hn & Ht)"; first lia.
    wp_pures.
    Z_to_nat n. rewrite -Nat2Z.inj_add. iSteps.
  Qed.
End zoo_G.

Require zoo_std.random_state__opaque.
