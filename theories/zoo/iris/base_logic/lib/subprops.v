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
#[global] Instance subG𑁒subprops۰Σ Σ :
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

  #[global] Instance subprops۰auth𑁒ne γ n :
    Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡)) (subprops۰auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subprops۰auth𑁒proper γ :
    Proper ((≡) ==> (=) ==> (≡)) (subprops۰auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subprops۰frag𑁒contractive γ :
    Contractive (subprops۰frag γ).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance subprops۰frag𑁒proper γ :
    Proper ((≡) ==> (≡)) (subprops۰frag γ).
  Proof.
    solve_proper.
  Qed.

  Lemma subprops𑁒alloc P :
    ⊢ |==>
      ∃ γ,
      subprops۰auth γ P false ∗
      subprops۰frag γ P.
  Proof.
    apply subpreds𑁒alloc.
  Qed.

  Lemma subprops𑁒wand `{inv۰G : !invGS Σ} {γ P state Q1} Q2 E :
    ▷ subprops۰auth γ P state -∗
    subprops۰frag γ Q1 -∗
    (Q1 -∗ Q2) ={E}=∗
      ▷ subprops۰auth γ P state ∗
      subprops۰frag γ Q2.
  Proof.
    iIntros "Hauth Hfrag H".
    iApply (subpreds𑁒wand with "Hauth Hfrag [H]"). 1: iSteps.
  Qed.
  Lemma subprops𑁒split `{inv۰G : !invGS Σ} {γ P state} Q1 Q2 E :
    ▷ subprops۰auth γ P state -∗
    subprops۰frag γ (Q1 ∗ Q2) ={E}=∗
      ▷ subprops۰auth γ P state ∗
      subprops۰frag γ Q1 ∗
      subprops۰frag γ Q2.
  Proof.
    iIntros "Hauth Hfrag".
    iApply (subpreds𑁒split with "Hauth Hfrag").
  Qed.
  Lemma subprops𑁒divide `{inv۰G : !invGS Σ} {γ P state} Qs E :
    ▷ subprops۰auth γ P state -∗
    subprops۰frag γ ([∗ list] Q ∈ Qs, Q) ={E}=∗
      ▷ subprops۰auth γ P state ∗
      [∗ list] Q ∈ Qs, subprops۰frag γ Q.
  Proof.
    iIntros "Hauth Hfrag".
    iMod (subpreds𑁒divide ((λ Q _, Q) <$> Qs) with "Hauth [Hfrag]") as "($ & Hfrags)".
    all: setoid_rewrite big_sepL_fmap.
    all: iSteps.
  Qed.

  Lemma subprops𑁒produce γ P :
    subprops۰auth γ P false -∗
    P -∗
    subprops۰auth γ P true.
  Proof.
    iApply subpreds𑁒produce.
  Qed.

  Lemma subprops𑁒consume `{inv۰G : !invGS Σ} γ P Q E :
    ▷ subprops۰auth γ P true -∗
    subprops۰frag γ Q ={E}=∗
      ▷ subprops۰auth γ P true ∗
      ▷^2 Q.
  Proof.
    apply subpreds𑁒consume.
  Qed.
End subprops۰G.

#[global] Opaque subprops۰auth.
#[global] Opaque subprops۰frag.
