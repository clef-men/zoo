From iris.base_logic Require Import
  lib.fancy_updates.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.subpreds.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Implicit Types state : bool.

Class SubpropsG Σ := {
  #[local] subprops_G_subpreds_G :: SubpredsG Σ () ;
}.

Definition subprops_Σ := #[
  subpreds_Σ ()
].
#[global] Instance subG_subprops_Σ Σ :
  subG subprops_Σ Σ →
  SubpropsG Σ.
Proof.
  solve_inG.
Qed.

Section subprops_G.
  Context `{subprops_G : !SubpropsG Σ}.

  Implicit Types P Q : iProp Σ.

  Definition subprops_auth γ P state :=
    subpreds_auth γ (λ _, P) (if state then Some () else None).

  Definition subprops_frag γ Q :=
    subpreds_frag γ (λ _, Q).

  #[global] Instance subprops_auth_ne γ n :
    Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡)) (subprops_auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subprops_auth_proper γ :
    Proper ((≡) ==> (=) ==> (≡)) (subprops_auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subprops_frag_contractive γ :
    Contractive (subprops_frag γ).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance subprops_frag_proper γ :
    Proper ((≡) ==> (≡)) (subprops_frag γ).
  Proof.
    solve_proper.
  Qed.

  Lemma subprops_alloc P :
    ⊢ |==>
      ∃ γ,
      subprops_auth γ P false ∗
      subprops_frag γ P.
  Proof.
    apply subpreds_alloc.
  Qed.

  Lemma subprops_split `{inv_G : !invGS Σ} {γ P state Q} Q1 Q2 E :
    ▷ subprops_auth γ P state -∗
    subprops_frag γ Q -∗
    (Q -∗ Q1 ∗ Q2) ={E}=∗
      ▷ subprops_auth γ P state ∗
      subprops_frag γ Q1 ∗
      subprops_frag γ Q2.
  Proof.
    iIntros "Hauth Hfrag H".
    iApply (subpreds_split with "Hauth Hfrag [H]").
    iSteps.
  Qed.
  Lemma subprops_divide `{inv_G : !invGS Σ} {γ P state Q} Qs E :
    ▷ subprops_auth γ P state -∗
    subprops_frag γ Q -∗
    (Q -∗ [∗ list] Q ∈ Qs, Q) ={E}=∗
      ▷ subprops_auth γ P state ∗
      [∗ list] Q ∈ Qs, subprops_frag γ Q.
  Proof.
    iIntros "Hauth Hfrag H".
    iMod (subpreds_divide ((λ Q _, Q) <$> Qs) with "Hauth Hfrag [H]") as "($ & Hfrags)".
    all: setoid_rewrite big_sepL_fmap.
    all: iSteps.
  Qed.

  Lemma subprops_produce γ P :
    subprops_auth γ P false -∗
    P -∗
    subprops_auth γ P true.
  Proof.
    iApply subpreds_produce.
  Qed.

  Lemma subprops_consume `{inv_G : !invGS Σ} γ P Q E :
    ▷ subprops_auth γ P true -∗
    subprops_frag γ Q ={E}=∗
      ▷ subprops_auth γ P true ∗
      ▷^2 Q.
  Proof.
    apply subpreds_consume.
  Qed.
End subprops_G.

#[global] Opaque subprops_auth.
#[global] Opaque subprops_frag.
