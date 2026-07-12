Require Export stdpp.option.

Require Import zoo.prelude.
Require Import zoo.options.

#[global] Hint Constructors option_Forall2 : core.

Lemma from_option_default {A B} (f : A → B) x o :
  from_option f (f x) o = f (default x o).
Proof.
  destruct o; done.
Qed.

#[global] Instance from_option_dec {A} (fn : A → Prop) `{∀ a, Decision (fn a)} default `{!Decision default} o : Decision (from_option fn default o) :=
  match o with
  | None =>
      _
  | Some _ =>
      _
  end.
