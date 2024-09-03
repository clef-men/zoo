From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base.
From zoo Require Import
  options.

Implicit Types t : val.

Parameter random_create : val.
Parameter random_gen : val.

Parameter random_inv : ∀ `{zoo_G : !ZooG Σ}, val → iProp Σ.

Axiom random_inv_persistent : ∀ `{zoo_G : !ZooG Σ} t,
  Persistent (random_inv t).
#[global] Existing Instance random_inv_persistent.

Axiom random_create_spec : ∀ `{zoo_G : !ZooG Σ},
  {{{
    True
  }}}
    random_create ()
  {{{ t,
    RET t;
    random_inv t
  }}}.

Axiom random_gen_spec : ∀ `{zoo_G : !ZooG Σ} t ub,
  (0 < ub)%Z →
  {{{
    random_inv t
  }}}
    random_gen t #ub
  {{{ n,
    RET #n;
    ⌜0 ≤ n < ub⌝%Z
  }}}.

Definition random_gen' : val :=
  fun: "t" "lb" "ub" =>
    "lb" + random_gen "t" ("ub" - "lb").

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma random_gen_spec_nat t (ub : nat) :
    0 < ub →
    {{{
      random_inv t
    }}}
      random_gen t #ub
    {{{ n,
      RET #n;
      ⌜n < ub⌝
    }}}.
  Proof.
    iIntros "%Hub %Φ #Ht HΦ".
    wp_apply (random_gen_spec with "Ht") as (n) "%Hn"; first lia.
    Z_to_nat n. iSteps.
  Qed.

  Lemma random_gen'_spec t lb ub :
    (lb < ub)%Z →
    {{{
      random_inv t
    }}}
      random_gen' t #lb #ub
    {{{ n,
      RET #n;
      ⌜lb ≤ n < ub⌝%Z
    }}}.
  Proof.
    iIntros "%Hlt %Φ #Ht HΦ".
    wp_rec.
    wp_smart_apply (random_gen_spec with "Ht") as "%n %Hn"; first lia.
    iSteps.
  Qed.
  Lemma random_gen'_spec_nat t lb ub :
    lb < ub →
    {{{
      random_inv t
    }}}
      random_gen' t #lb #ub
    {{{ n,
      RET #n;
      ⌜lb ≤ n < ub⌝
    }}}.
  Proof.
    iIntros "%Hlt %Φ Ht HΦ".
    wp_rec.
    wp_smart_apply (random_gen_spec with "Ht") as "%n %Hn"; first lia.
    wp_pures.
    Z_to_nat n. rewrite -Nat2Z.inj_add. iSteps.
  Qed.
End zoo_G.

#[global] Opaque random_gen'.
