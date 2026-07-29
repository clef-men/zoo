Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Implicit Type o : option val.
Implicit Type v : val.

Coercion option۰to_val o :=
  match o with
  | None =>
      §None
  | Some v =>
      ‘Some( v )
  end%V.
#[global] Arguments option۰to_val !_ / : assert.

#[global] Instance option۰to_valｰinj :
  Inj (=) (=) option۰to_val.
Proof.
  intros [] []; naive_solver.
Qed.

Lemma option۰to_valｰsimilarｰNoneｰl o :
  §None%V ≈ o →
  o = None.
Proof.
  destruct o; done.
Qed.
Lemma option۰to_valｰsimilarｰNoneｰr o :
  (o : val) ≈ §None%V →
  o = None.
Proof.
  intros ?%symmetry%option۰to_valｰsimilarｰNoneｰl. done.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype۰option t : iProp Σ :=
      ⌜t = §None%V⌝
    ∨ ∃ v,
      ⌜t = ‘Some( v )%V⌝ ∗
      τ v.
  #[global] Instance itype۰optionｰitype :
    iType _ itype۰option.
  Proof.
    split. apply _.
  Qed.

  Lemma wpｰmatchｰoption t e1 x e2 Φ :
    itype۰option t -∗
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
