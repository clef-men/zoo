Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.goption__types.
Require Import zoo.options.

Implicit Types o : option val.
Implicit Types v : val.

Coercion goption۰to_val o :=
  match o with
  | None =>
      §Gnone
  | Some v =>
      ‘Gsome[ v ]
  end%V.
#[global] Arguments goption۰to_val !_ / : assert.

#[global] Instance goption۰to_val𑁒inj𑁒similar :
  Inj (=) (≈@{val}) goption۰to_val.
Proof.
  intros [] [] ?; try done.
  zoo_simplify. done.
Qed.
#[global] Instance goption۰to_val𑁒inj :
  Inj (=) (=) goption۰to_val.
Proof.
  intros ?* ->%val𑁒similar𑁒refl%(inj _). done.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype۰goption t : iProp Σ :=
      ⌜t = §Gnone%V⌝
    ∨ ∃ v,
      ⌜t = ‘Gsome[ v ]%V⌝ ∗
      τ v.
  #[global] Instance itype۰goption𑁒itype :
    iType _ itype۰goption.
  Proof.
    split. apply _.
  Qed.

  Lemma wp𑁒match𑁒goption t e1 x e2 Φ :
    itype۰goption t -∗
    ( WP e1 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e2 {{ Φ }}
    ) -∗
    WP match: t with None => e1 | Some x => e2 end {{ Φ }}.
  Proof.
    iIntros "[-> | (%v & -> & #Hv)] H";
      [rewrite bi.and_elim_l | rewrite bi.and_elim_r];
      iSteps.
  Qed.
End zoo۰G.
