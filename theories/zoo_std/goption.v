Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.goption__code.
Require Import zoo_std.goption__types.
Require Import zoo.options.

Implicit Type o : option val.
Implicit Type v : val.

Coercion goption۰to_val o :=
  match o with
  | None =>
      §None
  | Some v =>
      ‘Some[ v ]
  end%V.
#[global] Arguments goption۰to_val !_ / : assert.

#[global] Instance goption۰to_valｰinjｰsimilar :
  Inj (=) (≈@{val}) goption۰to_val.
Proof.
  intros [] [] ?; try done.
  zoo۰simp. done.
Qed.
#[global] Instance goption۰to_valｰinj :
  Inj (=) (=) goption۰to_val.
Proof.
  intros ?* ->%valｰsimilarｰrefl%(inj _). done.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype۰goption t : iProp Σ :=
      ⌜t = §None%V⌝
    ∨ ∃ v,
      ⌜t = ‘Some[ v ]%V⌝ ∗
      τ v.
  #[global] Instance itype۰goptionｰitype :
    iType _ itype۰goption.
  Proof.
    split. apply _.
  Qed.

  Lemma wpｰmatchｰgoption t e1 x e2 Φ :
    itype۰goption t -∗
    ( WP e1 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e2 {{ Φ }}
    ) -∗
    WP 𝗺𝗮𝘁𝗰𝗵 t 𝘄𝗶𝘁𝗵 None -> e1 | Some x -> e2 𝗲𝗻𝗱 {{ Φ }}.
  Proof.
    iIntros "[-> | (%v & -> & #Hv)] H";
      [rewrite bi.and_elim_l | rewrite bi.and_elim_r];
      iSteps.
  Qed.
End zoo۰G.
