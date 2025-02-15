From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  goption__types.
From zoo Require Import
  options.

Implicit Types o : option val.
Implicit Types v : val.

Coercion goption_to_val o :=
  match o with
  | None =>
      §Gnone
  | Some v =>
      ‘Gsome[ v ]
  end%V.
#[global] Arguments goption_to_val !_ / : assert.

#[global] Instance goption_to_val_inj_similar :
  Inj (=) (≈@{val}) goption_to_val.
Proof.
  intros [] []; naive_solver.
Qed.
#[global] Instance goption_to_val_inj :
  Inj (=) (=) goption_to_val.
Proof.
  intros ?* ->%val_similar_refl%(inj _). done.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype_goption t : iProp Σ :=
      ⌜t = §Gnone%V⌝
    ∨ ∃ v,
      ⌜t = ‘Gsome[ v ]%V⌝ ∗
      τ v.
  #[global] Instance itype_goption_itype :
    iType _ itype_goption.
  Proof.
    split. apply _.
  Qed.

  Lemma wp_match_goption t e1 x e2 Φ :
    itype_goption t -∗
    ( WP e1 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e2 {{ Φ }}
    ) -∗
    WP match: t with None => e1 | Some x => e2 end {{ Φ }}.
  Proof.
    iIntros "[-> | (%v & -> & #Hv)] H";
      [rewrite bi.and_elim_l | rewrite bi.and_elim_r];
      iSteps.
  Qed.
End zoo_G.
