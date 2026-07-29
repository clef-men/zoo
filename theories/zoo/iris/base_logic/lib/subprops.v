Require Import iris.base_logic.lib.fancy_updates.

Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.subpreds.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Implicit Type state : bool.

Class SubpropsG Σ :=
  { #[local] subprops۰G۰subpreds۰G :: SubpredsG Σ ()
  }.

Definition subprops۰Σ :=
  #[subpreds۰Σ ()
  ].
#[global] Instance subGｰsubprops۰Σ Σ :
  subG subprops۰Σ Σ →
  SubpropsG Σ.
Proof.
  solve_inG.
Qed.

Section subprops۰G.
  Context `{subprops۰G : !SubpropsG Σ}.

  Implicit Type P Q : iProp Σ.

  Definition subprops۰auth γ P state :=
    subpreds۰auth γ (λ _, P) (if state then Some () else None).

  Definition subprops۰frag γ Q :=
    subpreds۰frag γ (λ _, Q).

  #[global] Instance subprops۰authｰne γ n :
    Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡)) (subprops۰auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subprops۰authｰproper γ :
    Proper ((≡) ==> (=) ==> (≡)) (subprops۰auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subprops۰fragｰcontractive γ :
    Contractive (subprops۰frag γ).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance subprops۰fragｰproper γ :
    Proper ((≡) ==> (≡)) (subprops۰frag γ).
  Proof.
    solve_proper.
  Qed.

  Lemma subpropsｰalloc P :
    ⊢ |==>
      ∃ γ,
      subprops۰auth γ P false ∗
      subprops۰frag γ P.
  Proof.
    apply subpredsｰalloc.
  Qed.

  Lemma subpropsｰwand `{inv۰G : !invGS Σ} {γ P state Q1} Q2 E :
    ▷ subprops۰auth γ P state -∗
    subprops۰frag γ Q1 -∗
    (Q1 -∗ Q2) ={E}=∗
      ▷ subprops۰auth γ P state ∗
      subprops۰frag γ Q2.
  Proof.
    iIntros "Hauth Hfrag H".
    iApply (subpredsｰwand with "Hauth Hfrag [H]"). 1: iSteps.
  Qed.
  Lemma subpropsｰsplit `{inv۰G : !invGS Σ} {γ P state} Q1 Q2 E :
    ▷ subprops۰auth γ P state -∗
    subprops۰frag γ (Q1 ∗ Q2) ={E}=∗
      ▷ subprops۰auth γ P state ∗
      subprops۰frag γ Q1 ∗
      subprops۰frag γ Q2.
  Proof.
    iIntros "Hauth Hfrag".
    iApply (subpredsｰsplit with "Hauth Hfrag").
  Qed.
  Lemma subpropsｰdivide `{inv۰G : !invGS Σ} {γ P state} Qs E :
    ▷ subprops۰auth γ P state -∗
    subprops۰frag γ ([∗ list] Q ∈ Qs, Q) ={E}=∗
      ▷ subprops۰auth γ P state ∗
      [∗ list] Q ∈ Qs, subprops۰frag γ Q.
  Proof.
    iIntros "Hauth Hfrag".
    iMod (subpredsｰdivide ((λ Q _, Q) <$> Qs) with "Hauth [Hfrag]") as "($ & Hfrags)".
    all: setoid_rewrite big_sepL_fmap.
    all: iSteps.
  Qed.

  Lemma subpropsｰproduce γ P :
    subprops۰auth γ P false -∗
    P -∗
    subprops۰auth γ P true.
  Proof.
    iApply subpredsｰproduce.
  Qed.

  Lemma subpropsｰconsume `{inv۰G : !invGS Σ} γ P Q E :
    ▷ subprops۰auth γ P true -∗
    subprops۰frag γ Q ={E}=∗
      ▷ subprops۰auth γ P true ∗
      ▷^2 Q.
  Proof.
    apply subpredsｰconsume.
  Qed.
End subprops۰G.

#[global] Opaque subprops۰auth.
#[global] Opaque subprops۰frag.
