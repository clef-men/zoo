Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.random_state__code.
Require Import zoo.options.

Implicit Type t : val.

Parameter random_state۰model : ∀ `{zoo۰G : !ZooG Σ}, val → iProp Σ.

Axiom random_state٠createｰspec : ∀ `{zoo۰G : !ZooG Σ},
  {{{
    True
  }}}
    random_state٠create ()
  {{{
    t
  , RET t;
    random_state۰model t
  }}}.

Axiom random_state٠bitsｰspec : ∀ `{zoo۰G : !ZooG Σ} t,
  {{{
    random_state۰model t
  }}}
    random_state٠bits t
  {{{
    (n : Z)
  , RET #n;
    random_state۰model t
  }}}.

Axiom random_state٠intｰspec : ∀ `{zoo۰G : !ZooG Σ} t ub,
  (0 < ub)%Z →
  {{{
    random_state۰model t
  }}}
    random_state٠int t #ub
  {{{
    n
  , RET #n;
    ⌜0 ≤ n < ub⌝%Z ∗
    random_state۰model t
  }}}.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma random_state٠intｰspecｰnat t (ub : nat) :
    0 < ub →
    {{{
      random_state۰model t
    }}}
      random_state٠int t #ub
    {{{
      n
    , RET #n;
      ⌜n < ub⌝ ∗
      random_state۰model t
    }}}.
  Proof.
    iIntros "%Hub %Φ Ht HΦ".
    wp۰apply (random_state٠intｰspec with "Ht") as (n) "(%Hn & Ht)"; first lia.
    Z_to_nat n. iSteps.
  Qed.

  Lemma random_state٠int_in_rangeｰspec t lb ub :
    (lb < ub)%Z →
    {{{
      random_state۰model t
    }}}
      random_state٠int_in_range t #lb #ub
    {{{
      n
    , RET #n;
      ⌜lb ≤ n < ub⌝%Z ∗
      random_state۰model t
    }}}.
  Proof.
    iIntros "%Hlt %Φ Ht HΦ".
    wp۰rec.
    wp۰apply+ (random_state٠intｰspec with "Ht") as "%n (%Hn & Ht)"; first lia.
    iSteps.
  Qed.
  Lemma random_state٠int_in_rangeｰspecｰnat t lb ub :
    lb < ub →
    {{{
      random_state۰model t
    }}}
      random_state٠int_in_range t #lb #ub
    {{{
      n
    , RET #n;
      ⌜lb ≤ n < ub⌝ ∗
      random_state۰model t
    }}}.
  Proof.
    iIntros "%Hlt %Φ Ht HΦ".
    wp۰rec.
    wp۰apply+ (random_state٠intｰspec with "Ht") as "%n (%Hn & Ht)"; first lia.
    wp۰pures.
    Z_to_nat n. rewrite -Nat2Z.inj_add. iSteps.
  Qed.
End zoo۰G.

Require zoo_std.random_state__opaque.
