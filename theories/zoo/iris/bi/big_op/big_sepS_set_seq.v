Require Import zoo.prelude.
Require Export zoo.iris.bi.big_op.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Section bi.
  Context {PROP : bi}.

  Implicit Type Φ : nat → PROP.

  Lemma big_sepSｰset_seqｰtoｰbig_sepL Φ i n :
    ([∗ set] k ∈ set_seq i n, Φ k) ⊢
    [∗ list] k ∈ seq i n, Φ k.
  Proof.
    rewrite -list_to_set_seq big_sepS_list_to_set //. 1: apply NoDup_seq.
  Qed.
End bi.
