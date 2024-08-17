From stdpp Require Export
  option.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Lemma from_option_default {A B} (f : A → B) x o :
  from_option f (f x) o = f (default x o).
Proof.
  destruct o; done.
Qed.

