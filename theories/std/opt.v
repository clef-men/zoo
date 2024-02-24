From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Implicit Types v : val.

Notation "'None'" := (
  in_type "opt" 0
)(in custom zebre_tag
).
Notation "'Some'" := (
  in_type "opt" 1
)(in custom zebre_tag
).

Coercion opt_to_val o :=
  match o with
  | None =>
      §None
  | Some v =>
      ’Some{ v }
  end.
#[global] Arguments opt_to_val !_ / : assert.

#[global] Instance opt_to_val_inj' :
  Inj (=) val_eq opt_to_val.
Proof.
  intros [] []; naive_solver.
Qed.
#[global] Instance opt_to_val_inj :
  Inj (=) (=) opt_to_val.
Proof.
  intros ?* ->%eq_val_eq%(inj _). done.
Qed.
#[global] Instance lst_to_val_physical o :
  ValPhysical (opt_to_val o).
Proof.
  destruct o; done.
Qed.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype_opt t : iProp Σ :=
      ⌜t = §None⌝
    ∨ ∃ v, ⌜t = ’Some{ v }⌝ ∗ τ v.
  #[global] Instance itype_opt_itype :
    iType _ itype_opt.
  Proof.
    split. apply _.
  Qed.

  Lemma wp_match_opt t e1 x e2 Φ :
    itype_opt t -∗
    ( WP e1 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e2 {{ Φ }}
    ) -∗
    WP match: t with None => e1 | Some x => e2 end {{ Φ }}.
  Proof.
    iIntros "[-> | (%v & -> & #Hv)] H";
      [rewrite bi.and_elim_l | rewrite bi.and_elim_r];
      iSteps.
  Qed.
End zebre_G.
