Require Import Stdlib.Logic.FunctionalExtensionality.

Require Export stdpp.functions.

Require Import zoo.prelude.
Require Import zoo.options.

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
  | ˖i =>
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

  Implicit Type x : A.
  Implicit Type y : B.
  Implicit Type f : A → B.

  Lemma fnｰlookupｰinsert f x1 y x2 :
    <[x1 := y]> f x2 = if decide (x1 = x2) then y else f x2.
  Proof.
    done.
  Qed.
  Lemma fnｰlookupｰinsertｰeq f x1 y x2 :
    x1 = x2 →
    <[x1 := y]> f x2 = y.
  Proof.
    rewrite fnｰlookupｰinsert. case_decide; done.
  Qed.
  Lemma fnｰlookupｰinsertｰne f x1 y x2 :
    x1 ≠ x2 →
    <[x1 := y]> f x2 = f x2.
  Proof.
    rewrite fnｰlookupｰinsert. case_decide; done.
  Qed.

  Lemma fnｰlookupｰalter g f x1 x2 :
    alter g x1 f x2 = if decide (x1 = x2) then g (f x1) else f x2.
  Proof.
    done.
  Qed.
  Lemma fnｰlookupｰalterｰeq g f x1 x2 :
    x1 = x2 →
    alter g x1 f x2 = g (f x1).
  Proof.
    rewrite fnｰlookupｰalter. case_decide; done.
  Qed.
  Lemma fnｰlookupｰalterｰne g f x1 x2 :
    x1 ≠ x2 →
    alter g x1 f x2 = f x2.
  Proof.
    rewrite fnｰlookupｰalter. case_decide; done.
  Qed.
End lookup.

Section fmap.
  Context `{!EqDecision A} {B C : Type}.

  Implicit Type x : A.
  Implicit Type y : B.
  Implicit Type f : A → B.
  Implicit Type g : B → C.

  Lemma fnｰcomposeｰinsert f g x y :
    g ∘ <[x := y]> f = <[x := g y]> (g ∘ f).
  Proof.
    apply functional_extensionality => 𝑥.
    rewrite /= !fnｰlookupｰinsert.
    case_decide; done.
  Qed.
End fmap.
