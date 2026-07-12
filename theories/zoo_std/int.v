Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Import zoo.diaframe.
Require Export zoo_std.base.
Require Export zoo_std.base.
Require Export zoo_std.int__code.
Require Import zoo.options.

Notation "e1 `min` e2" := (
  (Val int٠min) e1%E e2%E
)(at level 35
) : expr_scope.
Notation "e1 `max` e2" := (
  (Val int٠max) e1%E e2%E
)(at level 35
) : expr_scope.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Section Z.
    Implicit Types n : Z.

    Lemma int٠min𑁒spec n1 n2 E Φ :
      ▷ Φ #(n1 `min` n2) -∗
      WP #n1 `min` #n2 @ E {{ Φ }}.
    Proof.
      iSteps.
      - rewrite Z.min_l; [lia; done | done].
      - rewrite Z.min_r; [lia; done | done].
    Qed.
    #[global] Instance int٠min𑁒diaspec n1 n2 E :
      DIASPEC
      {{
        True
      }}
        #n1 `min` #n2 @ E
      {{
        RET #(n1 `min` n2);
        True
      }}
    | 30.
    Proof.
      iStep 3 as (Φ) "HΦ".
      wp_apply (int٠min𑁒spec with "(HΦ [//])").
    Qed.

    Lemma int٠max𑁒spec n1 n2 E Φ :
      ▷ Φ #(n1 `max` n2) -∗
      WP #n1 `max` #n2 @ E {{ Φ }}.
    Proof.
      iSteps.
      - rewrite Z.max_r; [lia; done | done].
      - rewrite Z.max_l; [lia; done | done].
    Qed.
    #[global] Instance int٠max𑁒diaspec n1 n2 E :
      DIASPEC
      {{
        True
      }}
        #n1 `max` #n2 @ E
      {{
        RET #(n1 `max` n2);
        True
      }}
    | 30.
    Proof.
      iStep 3 as (Φ) "HΦ".
      wp_apply (int٠max𑁒spec with "(HΦ [//])").
    Qed.

    Lemma int٠positive_part𑁒spec n E Φ :
      ▷ Φ #₊n -∗
      WP int٠positive_part #n @ E {{ Φ }}.
    Proof.
      iIntros "HΦ".

      wp_rec.
      iApply int٠max𑁒spec.
      assert (0 `max` n = ₊n)%Z as -> by lia. iSteps.
    Qed.
    #[global] Instance int٠positive_part𑁒diaspec n E :
      DIASPEC
      {{
        True
      }}
        int٠positive_part #n @ E
      {{
        RET #₊n;
        True
      }}
    | 30.
    Proof.
      iStep 3 as (Φ) "HΦ".
      wp_apply (int٠positive_part𑁒spec with "(HΦ [//])").
    Qed.
  End Z.

  Section nat.
    Implicit Types n : nat.

    Lemma int٠min𑁒spec_nat n1 n2 E Φ :
      ▷ Φ #(n1 `min` n2)%nat -∗
      WP #n1 `min` #n2 @ E {{ Φ }}.
    Proof.
      iIntros "HΦ".
      iApply int٠min𑁒spec.
      rewrite Nat2Z.inj_min //.
    Qed.
    #[global] Instance int٠min𑁒diaspec_nat n1 n2 E :
      DIASPEC
      {{
        True
      }}
        #n1 `min` #n2 @ E
      {{
        RET #(n1 `min` n2)%nat;
        True
      }}
    | 20.
    Proof.
      iStep 3 as (Φ) "HΦ".
      wp_apply (int٠min𑁒spec_nat with "(HΦ [//])").
    Qed.

    Lemma int٠max𑁒spec_nat n1 n2 E Φ :
      ▷ Φ #(n1 `max` n2)%nat -∗
      WP #n1 `max` #n2 @ E {{ Φ }}.
    Proof.
      iIntros "HΦ".
      iApply int٠max𑁒spec.
      rewrite Nat2Z.inj_max //.
    Qed.
    #[global] Instance int٠max𑁒diaspec_nat n1 n2 E :
      DIASPEC
      {{
        True
      }}
        #n1 `max` #n2 @ E
      {{
        RET #(n1 `max` n2)%nat;
        True
      }}
    | 20.
    Proof.
      iStep 3 as (Φ) "HΦ".
      wp_apply (int٠max𑁒spec_nat with "(HΦ [//])").
    Qed.

    Lemma int٠positive_part𑁒spec_nat n E Φ :
      ▷ Φ #n -∗
      WP int٠positive_part #n @ E {{ Φ }}.
    Proof.
      rewrite -{1}(Nat2Z.id n).
      apply int٠positive_part𑁒spec.
    Qed.
    #[global] Instance int٠positive_part𑁒diaspec_nat n E :
      DIASPEC
      {{
        True
      }}
        int٠positive_part #n @ E
      {{
        RET #n;
        True
      }}
    | 20.
    Proof.
      iStep 3 as (Φ) "HΦ".
      wp_apply (int٠positive_part𑁒spec_nat with "(HΦ [//])").
    Qed.
  End nat.
End zoo_G.

Require zoo_std.int__opaque.
