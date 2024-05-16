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

Inductive option2 {A} :=
  | Some2 (a : A)
  | None1
  | None2.
#[global] Arguments option2 : clear implicits.

Definition option_to_option2 {A} (o : option A) :=
  match o with
  | None =>
      None1
  | Some a =>
      Some2 a
  end.

#[global] Instance Some2_inj A :
  Inj (=) (=) (@Some2 A).
Proof.
  rewrite /Inj. naive_solver.
Qed.

Notation "'None1'" := (
  in_type "opt" 0
)(in custom zoo_tag
).
Notation "'None2'" := (
  in_type "opt" 1
)(in custom zoo_tag
).
Notation "'Some2'" := (
  in_type "opt" 2
)(in custom zoo_tag
).

Coercion opt2_to_val o :=
  match o with
  | None1 =>
      §None1
  | None2 =>
      §None2
  | Some2 v =>
      ’Some2{ v }
  end.
#[global] Arguments opt2_to_val !_ / : assert.

#[global] Instance opt2_to_val_inj' :
  Inj (=) val_eq opt2_to_val.
Proof.
  intros [] []; naive_solver.
Qed.
#[global] Instance opt2_to_val_inj :
  Inj (=) (=) opt2_to_val.
Proof.
  intros ?* ->%eq_val_eq%(inj _). done.
Qed.
#[global] Instance opt2_to_val_physical o :
  ValPhysical (opt2_to_val o).
Proof.
  destruct o; done.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype_opt2 t : iProp Σ :=
      ⌜t = §None1⌝
    ∨ ⌜t = §None2⌝
    ∨ ∃ v, ⌜t = ’Some2{ v }⌝ ∗ τ v.
  #[global] Instance itype_opt2_itype :
    iType _ itype_opt2.
  Proof.
    split. apply _.
  Qed.

  Lemma wp_match_opt2 t e1 e2 x e3 Φ :
    itype_opt2 t -∗
    ( WP e1 {{ Φ }} ∧
      WP e2 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e3 {{ Φ }}
    ) -∗
    WP match: t with None1 => e1 | None2 => e2 | Some2 x => e3 end {{ Φ }}.
  Proof.
    iIntros "[-> | [-> | (%v & -> & #Hv)]] H".
    1: rewrite bi.and_elim_l.
    2,3: rewrite bi.and_elim_r.
    2: rewrite bi.and_elim_l.
    3: rewrite bi.and_elim_r.
    all: iSteps.
  Qed.
End zoo_G.
