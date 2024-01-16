From zebra Require Import
  prelude.
From zebra.language Require Import
  notations
  diaframe.
From zebra.std Require Export
  base.
From zebra Require Import
  options.

Definition minimum : val :=
  λ: "n1" "n2",
    if: "n1" < "n2" then "n1" else "n2".

Definition maximum : val :=
  λ: "n1" "n2",
    if: "n1" < "n2" then "n2" else "n1".

Section zebra_G.
  Context `{zebra_G : !ZebraG Σ}.

  Section Z.
    Implicit Types n : Z.

    Lemma minimum_spec n1 n2 E Φ :
      ▷ Φ #(n1 `min` n2) -∗
      WP minimum #n1 #n2 @ E {{ Φ }}.
    Proof.
      iSteps.
      - rewrite Z.min_l; [lia; done | done].
      - rewrite Z.min_r; [lia; done | done].
    Qed.

    Lemma maximum_spec n1 n2 E Φ :
      ▷ Φ #(n1 `max` n2) -∗
      WP maximum #n1 #n2 @ E {{ Φ }}.
    Proof.
      iSteps.
      - rewrite Z.max_r; [lia; done | done].
      - rewrite Z.max_l; [lia; done | done].
    Qed.
  End Z.

  Section nat.
    Implicit Types n : nat.

    Lemma minimum_spec_nat n1 n2 E Φ :
      ▷ Φ #(n1 `min` n2)%nat -∗
      WP minimum #n1 #n2 @ E {{ Φ }}.
    Proof.
      iIntros "HΦ". iApply minimum_spec. rewrite Nat2Z.inj_min //.
    Qed.

    Lemma maximum_spec_nat n1 n2 E Φ :
      ▷ Φ #(n1 `max` n2)%nat -∗
      WP maximum #n1 #n2 @ E {{ Φ }}.
    Proof.
      iIntros "HΦ". iApply maximum_spec. rewrite Nat2Z.inj_max //.
    Qed.
  End nat.
End zebra_G.

#[global] Opaque minimum.
#[global] Opaque maximum.
