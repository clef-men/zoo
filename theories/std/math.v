From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Definition minimum : val :=
  λ: "n1" "n2",
    if: "n1" < "n2" then "n1" else "n2".

Definition maximum : val :=
  λ: "n1" "n2",
    if: "n1" < "n2" then "n2" else "n1".

Notation "e1 `min` e2" := (
  (Val minimum) e1%E e2%E
)(at level 35
) : expr_scope.
Notation "e1 `max` e2" := (
  (Val maximum) e1%E e2%E
)(at level 35
) : expr_scope.

Definition positive_part : val :=
  λ: "n",
    #0 `max` "n".

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Section Z.
    Implicit Types n : Z.

    Lemma minimum_spec n1 n2 E Φ :
      ▷ Φ #(n1 `min` n2) -∗
      WP #n1 `min` #n2 @ E {{ Φ }}.
    Proof.
      iSteps.
      - rewrite Z.min_l; [lia; done | done].
      - rewrite Z.min_r; [lia; done | done].
    Qed.

    Lemma maximum_spec n1 n2 E Φ :
      ▷ Φ #(n1 `max` n2) -∗
      WP #n1 `max` #n2 @ E {{ Φ }}.
    Proof.
      iSteps.
      - rewrite Z.max_r; [lia; done | done].
      - rewrite Z.max_l; [lia; done | done].
    Qed.

    Lemma positive_part_spec n E Φ :
      ▷ Φ #(Z.to_nat n) -∗
      WP positive_part #n @ E {{ Φ }}.
    Proof.
      iIntros "HΦ".
      wp_rec.
      iApply maximum_spec.
      assert (0 `max` n = Z.to_nat n)%Z as -> by lia. iSteps.
    Qed.
  End Z.

  Section nat.
    Implicit Types n : nat.

    Lemma minimum_spec_nat n1 n2 E Φ :
      ▷ Φ #(n1 `min` n2)%nat -∗
      WP #n1 `min` #n2 @ E {{ Φ }}.
    Proof.
      iIntros "HΦ". iApply minimum_spec. rewrite Nat2Z.inj_min //.
    Qed.

    Lemma maximum_spec_nat n1 n2 E Φ :
      ▷ Φ #(n1 `max` n2)%nat -∗
      WP #n1 `max` #n2 @ E {{ Φ }}.
    Proof.
      iIntros "HΦ". iApply maximum_spec. rewrite Nat2Z.inj_max //.
    Qed.

    Lemma positive_part_spec_nat n E Φ :
      ▷ Φ #n -∗
      WP positive_part #n @ E {{ Φ }}.
    Proof.
      rewrite -{1}(Nat2Z.id n). apply positive_part_spec.
    Qed.
  End nat.
End zebre_G.

#[global] Opaque minimum.
#[global] Opaque maximum.
#[global] Opaque positive_part.
