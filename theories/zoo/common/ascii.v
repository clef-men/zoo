Require Export Stdlib.Strings.Ascii.

Require Import zoo.prelude.
Require Import zoo.options.

#[global] Instance nat_of_asciiｰinj :
  Inj (=) (=) nat_of_ascii.
Proof.
  intros chr1 chr2 Heq%(f_equal ascii_of_nat).
  rewrite !ascii_nat_embedding // in Heq.
Qed.
