Require Import iris.base_logic.lib.fancy_updates.

Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.auth_dgset.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class SubpredsG Σ A :=
  { #[local] subpreds۰G۰auth_dgset۰G :: AuthDgsetG Σ gname
  ; #[local] subpreds۰G۰saved_pred۰G :: SavedPredG Σ A
  }.

Definition subpreds۰Σ A :=
  #[auth_dgset۰Σ gname
  ; saved_pred۰Σ A
  ].
#[global] Instance subG𑁒subpreds۰Σ Σ A :
  subG (subpreds۰Σ A) Σ →
  SubpredsG Σ A.
Proof.
  solve_inG.
Qed.

Section subpreds۰G.
  Context `{subpreds۰G : !SubpredsG Σ A}.

  Implicit Type state : option A.
  Implicit Type η : gname.
  Implicit Type Ψ Χ : A → iProp Σ.

  Definition subpreds۰auth γ Ψ state : iProp Σ :=
    ∃ ηs,
    auth_dgset۰auth γ (DfracOwn 1) ηs ∗
      ∀ x,
      (if state is Some y then ⌜x = y⌝ else Ψ x) -∗
      [∗ set] η ∈ ηs,
        ∃ Χ,
        saved_pred η Χ ∗
        ▷ Χ x.
  #[local] Instance : CustomIpat "auth" :=
    " ( %ηs
      & {>;}Hauth
      & Hηs
      )
    ".

  Definition subpreds۰frag γ Χ : iProp Σ :=
    ∃ η,
    auth_dgset۰frag γ {[η]} ∗
    saved_pred η Χ.
  #[local] Instance : CustomIpat "frag" :=
    " ( %η{}
      & Hfrag{_{}}
      & #Hη{}
      )
    ".

  #[global] Instance subpreds۰auth𑁒ne γ n :
    Proper (
      (pointwise_relation _ (≡{n}≡)) ==>
      (=) ==>
      (≡{n}≡)
    ) (subpreds۰auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subpreds۰auth𑁒proper γ :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (=) ==>
      (≡)
    ) (subpreds۰auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subpreds۰frag𑁒contractive γ n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (subpreds۰frag γ).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance subpreds۰frag𑁒proper γ :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (subpreds۰frag γ).
  Proof.
    solve_proper.
  Qed.

  Lemma subpreds𑁒alloc Ψ :
    ⊢ |==>
      ∃ γ,
      subpreds۰auth γ Ψ None ∗
      subpreds۰frag γ Ψ.
  Proof.
    iMod (saved_pred𑁒alloc Ψ) as "(%η & #Hη)".
    iMod (auth_dgset𑁒alloc {[η]}) as "(%γ & Hauth & Hfrag)".
    iFrame "#∗".
    setoid_rewrite big_sepS_singleton. iSteps.
  Qed.

  Lemma subpreds𑁒split𑁒wand `{inv۰G : !invGS Σ} {γ Ψ state Χ} Χ1 Χ2 E :
    ▷ subpreds۰auth γ Ψ state -∗
    subpreds۰frag γ Χ -∗
    (∀ x, Χ x -∗ Χ1 x ∗ Χ2 x) ={E}=∗
      ▷ subpreds۰auth γ Ψ state ∗
      subpreds۰frag γ Χ1 ∗
      subpreds۰frag γ Χ2.
  Proof.
    iIntros "(:auth >) (:frag) H".
    iDestruct (auth_dgset𑁒elem_of with "Hauth Hfrag") as %Hη.
    iMod (auth_dgset𑁒update𑁒dealloc {[η]} with "Hauth Hfrag") as "Hauth".
    iMod (saved_pred𑁒alloc𑁒cofinite (ηs ∖ {[η]}) Χ1) as "(%η1 & %Hη1 & #Hη1)".
    iMod (auth_dgset𑁒update𑁒alloc𑁒singleton η1 with "Hauth") as "(Hauth & Hfrag1)"; first done.
    iMod (saved_pred𑁒alloc𑁒cofinite ({[η1]} ∪ ηs ∖ {[η]}) Χ2) as "(%η2 & %Hη2 & #Hη2)".
    iMod (auth_dgset𑁒update𑁒alloc𑁒singleton η2 with "Hauth") as "(Hauth & Hfrag2)"; first done.
    iFrame "#∗". iIntros "!> !> %x Hstate".
    iDestruct ("Hηs" with "Hstate") as "Hηs".
    iDestruct (big_sepS_delete with "Hηs") as "((%Χ_ & Hη_ & HΧ) & Hηs)"; first done.
    iDestruct (saved_pred𑁒agree x with "Hη Hη_") as "Heq".
    iAssert (▷ (Χ1 x ∗ Χ2 x))%I with "[H HΧ Heq]" as "(HΧ1 & HΧ2)".
    { iModIntro.
      iApply "H".
      iRewrite "Heq" => //.
    }
    do 2 (rewrite big_sepS_union; first set_solver).
    rewrite !big_sepS_singleton. iFrame "#∗".
  Qed.
  Lemma subpreds𑁒wand `{inv۰G : !invGS Σ} {γ Ψ state Χ1} Χ2 E :
    ▷ subpreds۰auth γ Ψ state -∗
    subpreds۰frag γ Χ1 -∗
    (∀ x, Χ1 x -∗ Χ2 x) ={E}=∗
      ▷ subpreds۰auth γ Ψ state ∗
      subpreds۰frag γ Χ2.
  Proof.
    iIntros "Hauth Hfrag H".
    iDestruct (subpreds۰frag𑁒proper _ _ (λ x, Χ1 x ∗ True)%I with "Hfrag") as "Hfrag".
    { rewrite /pointwise_relation. iSteps. }
    iMod (subpreds𑁒split𑁒wand Χ2 (λ _, True)%I with "Hauth Hfrag [H]") as "($ & $ & _)" => //. 1: iSteps.
  Qed.
  Lemma subpreds𑁒split `{inv۰G : !invGS Σ} {γ Ψ state} Χ1 Χ2 E :
    ▷ subpreds۰auth γ Ψ state -∗
    subpreds۰frag γ (λ x, Χ1 x ∗ Χ2 x)%I ={E}=∗
      ▷ subpreds۰auth γ Ψ state ∗
      subpreds۰frag γ Χ1 ∗
      subpreds۰frag γ Χ2.
  Proof.
    iIntros "Hauth Hfrag".
    iApply (subpreds𑁒split𑁒wand with "Hauth Hfrag"). 1: iSteps.
  Qed.
  Lemma subpreds𑁒divide `{inv۰G : !invGS Σ} {γ Ψ state} Χs E :
    ▷ subpreds۰auth γ Ψ state -∗
    subpreds۰frag γ (λ x, [∗ list] Χ ∈ Χs, Χ x) ={E}=∗
      ▷ subpreds۰auth γ Ψ state ∗
      [∗ list] Χ ∈ Χs, subpreds۰frag γ Χ.
  Proof.
    iInduction Χs as [| Χ0 Χs] "IH"; first auto.
    iIntros "Hauth Hfrag".
    iMod (subpreds𑁒split Χ0 (λ x, [∗ list] Χ ∈ Χs, Χ x)%I with "Hauth Hfrag") as "(Hauth & $ & Hfrag)".
    iApply ("IH" with "Hauth Hfrag").
  Qed.

  Lemma subpreds𑁒produce {γ Ψ} x :
    subpreds۰auth γ Ψ None -∗
    Ψ x -∗
    subpreds۰auth γ Ψ (Some x).
  Proof.
    iSteps.
  Qed.

  Lemma subpreds𑁒consume `{inv۰G : !invGS Σ} γ Ψ x Χ E :
    ▷ subpreds۰auth γ Ψ (Some x) -∗
    subpreds۰frag γ Χ ={E}=∗
      ▷ subpreds۰auth γ Ψ (Some x) ∗
      ▷^2 Χ x.
  Proof.
    iIntros "(:auth >) (:frag)".
    iDestruct ("Hηs" with "[//]") as "Hηs".
    iDestruct (auth_dgset𑁒elem_of with "Hauth Hfrag") as %Hη.
    iMod (auth_dgset𑁒update𑁒dealloc {[η]} with "Hauth Hfrag") as "Hauth".
    iDestruct (big_sepS_delete with "Hηs") as "((%Χ_ & Hη_ & HΧ) & Hηs)"; first done.
    iDestruct (saved_pred𑁒agree x with "Hη Hη_") as "Heq".
    iFrame "#∗". iSplitL "Hηs"; first iSteps.
    do 3 iModIntro.
    iRewrite "Heq" => //.
  Qed.
End subpreds۰G.

#[global] Opaque subpreds۰auth.
#[global] Opaque subpreds۰frag.
