From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  optional__types.
From zoo Require Import
  options.

Implicit Types v : val.

Inductive optional {A} :=
  | Nothing
  | Anything
  | Something (a : A).
#[global] Arguments optional : clear implicits.

Definition option_to_optional {A} (o : option A) :=
  match o with
  | None =>
      Nothing
  | Some a =>
      Something a
  end.

#[global] Instance Something_inj A :
  Inj (=) (=) (@Something A).
Proof.
  rewrite /Inj. naive_solver.
Qed.

Coercion optional_to_val o :=
  match o with
  | Nothing =>
      §Nothing
  | Anything =>
      §Anything
  | Something v =>
      ‘Something( v )
  end%V.
#[global] Arguments optional_to_val !_ / : assert.

#[global] Instance optional_to_val_inj :
  Inj (=) (=) optional_to_val.
Proof.
  intros [] []; naive_solver.
Qed.
#[global] Instance optional_to_val_physical o :
  ValPhysical (optional_to_val o).
Proof.
  destruct o; done.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype_optional t : iProp Σ :=
      ⌜t = §Nothing%V⌝
    ∨ ⌜t = §Anything%V⌝
    ∨ ∃ v, ⌜t = ‘Something( v )%V⌝ ∗ τ v.
  #[global] Instance itype_optional_itype :
    iType _ itype_optional.
  Proof.
    split. apply _.
  Qed.

  Lemma wp_match_optional t e1 e2 x e3 Φ :
    itype_optional t -∗
    ( WP e1 {{ Φ }} ∧
      WP e2 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e3 {{ Φ }}
    ) -∗
    WP match: t with Nothing => e1 | Anything => e2 | Something x => e3 end {{ Φ }}.
  Proof.
    iIntros "[-> | [-> | (%v & -> & #Hv)]] H".
    1: rewrite bi.and_elim_l.
    2,3: rewrite bi.and_elim_r.
    2: rewrite bi.and_elim_l.
    3: rewrite bi.and_elim_r.
    all: iSteps.
  Qed.
End zoo_G.
