From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base.
From zoo Require Import
  options.

Implicit Types v : val.

Coercion option_to_val o :=
  match o with
  | None =>
      §None
  | Some v =>
      ’Some( v )
  end%V.
#[global] Arguments option_to_val !_ / : assert.

#[global] Instance option_to_val_inj :
  Inj (=) (=) option_to_val.
Proof.
  intros [] []; naive_solver.
Qed.
#[global] Instance option_to_val_physical o :
  ValPhysical (option_to_val o).
Proof.
  destruct o; done.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype_option t : iProp Σ :=
      ⌜t = §None%V⌝
    ∨ ∃ v, ⌜t = ’Some( v )%V⌝ ∗ τ v.
  #[global] Instance itype_option_itype :
    iType _ itype_option.
  Proof.
    split. apply _.
  Qed.

  Lemma wp_match_option t e1 x e2 Φ :
    itype_option t -∗
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
