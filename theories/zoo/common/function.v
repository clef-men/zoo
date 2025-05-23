From Coq.Logic Require Import
  FunctionalExtensionality.

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

Definition scons `(x : X) f i :=
  match i with
  | 0 =>
      x
  | S i =>
      f i
  end.

Notation "x .: f" := (
  scons x f
)(at level 55,
  f at level 56,
  right associativity
) : stdpp_scope.

Section lookup.
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
End lookup.

Section fmap.
  Context `{!EqDecision A} {B C : Type}.

  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types f : A → B.
  Implicit Types g : B → C.

  Lemma fn_compose_insert f g x y :
    g ∘ <[x := y]> f = <[x := g y]> (g ∘ f).
  Proof.
    apply functional_extensionality => 𝑥.
    rewrite /= !fn_lookup_insert.
    case_decide; done.
  Qed.
End fmap.
