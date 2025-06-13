From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base.
From zoo_std Require Export
  base
  int__code.
From zoo Require Import
  options.

Notation "e1 `min` e2" := (
  (Val int_min) e1%E e2%E
)(at level 35
) : expr_scope.
Notation "e1 `max` e2" := (
  (Val int_max) e1%E e2%E
)(at level 35
) : expr_scope.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Section Z.
    Implicit Types n : Z.

    Lemma int_min_spec n1 n2 E Φ :
      ▷ Φ #(n1 `min` n2) -∗
      WP #n1 `min` #n2 @ E {{ Φ }}.
    Proof.
      iSteps.
      - rewrite Z.min_l; [lia; done | done].
      - rewrite Z.min_r; [lia; done | done].
    Qed.

    Lemma int_max_spec n1 n2 E Φ :
      ▷ Φ #(n1 `max` n2) -∗
      WP #n1 `max` #n2 @ E {{ Φ }}.
    Proof.
      iSteps.
      - rewrite Z.max_r; [lia; done | done].
      - rewrite Z.max_l; [lia; done | done].
    Qed.

    Lemma int_positive_part_spec n E Φ :
      ▷ Φ #₊n -∗
      WP int_positive_part #n @ E {{ Φ }}.
    Proof.
      iIntros "HΦ".
      wp_rec.
      iApply int_max_spec.
      assert (0 `max` n = ₊n)%Z as -> by lia. iSteps.
    Qed.
  End Z.

  Section nat.
    Implicit Types n : nat.

    Lemma int_min_spec_nat n1 n2 E Φ :
      ▷ Φ #(n1 `min` n2)%nat -∗
      WP #n1 `min` #n2 @ E {{ Φ }}.
    Proof.
      iIntros "HΦ". iApply int_min_spec. rewrite Nat2Z.inj_min //.
    Qed.

    Lemma int_max_spec_nat n1 n2 E Φ :
      ▷ Φ #(n1 `max` n2)%nat -∗
      WP #n1 `max` #n2 @ E {{ Φ }}.
    Proof.
      iIntros "HΦ". iApply int_max_spec. rewrite Nat2Z.inj_max //.
    Qed.

    Lemma int_positive_part_spec_nat n E Φ :
      ▷ Φ #n -∗
      WP int_positive_part #n @ E {{ Φ }}.
    Proof.
      rewrite -{1}(Nat2Z.id n). apply int_positive_part_spec.
    Qed.
  End nat.
End zoo_G.

From zoo_std Require
  int__opaque.
