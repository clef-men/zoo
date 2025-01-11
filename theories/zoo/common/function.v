From stdpp Require Export
  functions.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Definition funeq {A B} (f1 f2 : A → B) :=
  ∀ x,
  f1 x = f2 x.

Infix "≡ᶠ" :=
  funeq
( at level 70,
  no associativity
) : stdpp_scope.
Notation "(≡ᶠ)" :=
  funeq
( only parsing
) : stdpp_scope.

Section function.
  Context `{!EqDecision A} {B : Type}.

  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types f : A → B.

  Lemma fn_lookup_insert f x1 y x2 :
    <[x1 := y]> f x2 = if decide (x1 = x2) then y else f x2.
  Proof.
    done.
  Qed.
  Lemma fn_lookup_insert_eq f x1 y x2 :
    x1 = x2 →
    <[x1 := y]> f x2 = y.
  Proof.
    rewrite fn_lookup_insert. case_decide; done.
  Qed.
  Lemma fn_lookup_insert_ne f x1 y x2 :
    x1 ≠ x2 →
    <[x1 := y]> f x2 = f x2.
  Proof.
    rewrite fn_lookup_insert. case_decide; done.
  Qed.

  Lemma fn_lookup_alter g f x1 x2 :
    alter g x1 f x2 = if decide (x1 = x2) then g (f x1) else f x2.
  Proof.
    done.
  Qed.
  Lemma fn_lookup_alter_eq g f x1 x2 :
    x1 = x2 →
    alter g x1 f x2 = g (f x1).
  Proof.
    rewrite fn_lookup_alter. case_decide; done.
  Qed.
  Lemma fn_lookup_alter_ne g f x1 x2 :
    x1 ≠ x2 →
    alter g x1 f x2 = f x2.
  Proof.
    rewrite fn_lookup_alter. case_decide; done.
  Qed.
End function.
