Require Export iris.base_logic.lib.fancy_updates.

Require Import zoo.prelude.
Require Import zoo.iris.diaframe.
Require Import zoo.language.tactics.
Require Import zoo.language.notations.
Require Export zoo.program_logic.state_interp.
Require Import zoo.options.

Parameter later_coefficient : nat.
Axiom later۰coefficient_lb :
  2 ≤ later_coefficient.
#[global] Hint Resolve
  later۰coefficient_lb
: core.

Parameter later_constant : nat.
Axiom later۰constant_lb :
  2 ≤ later_constant.
#[global] Hint Resolve
  later۰constant_lb
: core.

Definition later۰function ns :=
  later_coefficient * ns + later_constant.
Lemma later۰functionｰlb ns :
  later_constant ≤ later۰function ns.
Proof.
  rewrite /later۰function. lia.
Qed.
Lemma later۰functionｰmono ns1 ns2 :
  ns1 ≤ ns2 →
  later۰function ns1 ≤ later۰function ns2.
Proof.
  intros.
  apply Nat.add_le_mono_r, Nat.mul_le_mono_l => //.
Qed.
Lemma later۰functionｰ0 :
  later۰function 0 = later_constant.
Proof.
  rewrite /later۰function. lia.
Qed.
#[global] Hint Resolve
  later۰functionｰlb
  later۰functionｰmono
: core.

Fixpoint later۰sum ns n : nat :=
  match n with
  | 0 =>
      0
  | ˖n =>
      later۰function ns + later۰sum ˖ns n
  end.

Lemma later۰sumｰlb ns n :
  n * later_constant ≤ later۰sum ns n.
Proof.
  move: ns. induction n as [| n IH] => ns.
  - lia.
  - apply Nat.add_le_mono; done.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition bwp۰pre (bwp : expr -d> thread_id -d> coPset -d> (val -d> iPropO Σ) -d> iPropO Σ)
  : expr -d> thread_id -d> coPset -d> (val -d> iPropO Σ) -d> iPropO Σ
  := (
    λ e tid E Φ,
      ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E}=∗
      match to_val e with
      | Some v =>
          state_interp ns nt σ κs ∗
          Φ v
      | None =>
          |={E,∅}=>
          ⌜reducible tid e σ⌝ ∗
            ∀ κ κs' e' σ' es,
            ⌜κs = κ ++ κs'⌝ -∗
            ⌜prim_step tid e σ κ e' σ' es⌝ -∗
            £ (later۰function ns) ={∅}=∗
              ▷ |={∅,E}=>
              state_interp ˖ns (nt + length es) σ' κs' ∗
              bwp e' tid E Φ ∗
              [∗ list] i ↦ e ∈ es,
                bwp e (nt + i) ⊤ fork_post
      end
  )%I.
  #[global] Arguments bwp۰pre bwp e%_E tid E Φ%_I : rename.

  #[local] Instance bwp۰preｰcontractive :
    Contractive bwp۰pre.
  Proof.
    rewrite /bwp۰pre => n bwp1 bwp2 Hbwp e tid E Φ.
    repeat (apply Hbwp || f_contractive || f_equiv).
  Qed.

  #[local] Definition bwp۰def
  : expr → thread_id → coPset → (val → iProp Σ) → iProp Σ
  :=
    fixpoint bwp۰pre.
  #[global] Arguments bwp۰def e%_E tid E Φ%_I : rename.
End zoo۰G.

#[local] Definition bwp۰aux : seal (@bwp۰def).
  Proof. by eexists. Qed.
Definition bwp :=
  bwp۰aux.(unseal).
#[global] Arguments bwp {_ _} e%_E tid E Φ%_I : rename.
#[local] Lemma bwpｰunseal `{zoo۰G : !ZooG Σ} :
  bwp = bwp۰def.
Proof.
  rewrite -bwp۰aux.(seal_eq) //.
Qed.

Declare Custom Entry wp۰mask.
Notation "" := (
  @top coPset _
)(in custom wp۰mask
).
Notation "@ E" :=
  E
( in custom wp۰mask at level 200,
  E constr,
  format "'/  ' @  E "
).

Notation "'BWP' e ∶ tid E {{ Φ } }" := (
  bwp e%E tid E Φ%I
)(at level 0,
  e at level 200,
  tid at level 200,
  E custom wp۰mask at level 200,
  Φ at level 200,
  format "'[hv' BWP  '/  ' '[' e ']'  '/  ' ∶  tid  E '/' {{  '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'BWP' e ∶ tid E {{ v , Q } }" := (
  bwp e%E tid E (λ v, Q%I)
)(at level 0,
  e at level 200,
  tid at level 200,
  E custom wp۰mask at level 200,
  v at level 200 as pattern,
  Q at level 200,
  format "'[hv' BWP  '/  ' '[' e ']'  '/  ' ∶  tid  E '/' {{  '[' v ,  '/' Q ']'  '/' } } ']'"
) : bi_scope.

Implicit Type ns nt : nat.
Implicit Type l : location.
Implicit Type pid : prophet_id.
Implicit Type e : expr.
Implicit Type es : list expr.
Implicit Type v : val.
Implicit Type tid : thread_id.
Implicit Type σ : state.
Implicit Type κ κs : list observation.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type P R : iProp Σ.
  Implicit Type Φ : val → iProp Σ.

  Lemma bwpｰunfold e tid E Φ :
    BWP e ∶ tid @ E {{ Φ }} ⊣⊢
    bwp۰pre bwp e tid E Φ.
  Proof.
    rewrite bwpｰunseal.
    apply: (fixpoint_unfold bwp۰pre).
  Qed.

  #[global] Instance bwpｰne e tid E n :
    Proper (pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) (bwp e tid E).
  Proof.
    move: e. induction (lt_wf n) as [n _ IH] => e Φ1 Φ2 HΦ.
    rewrite !bwpｰunfold /bwp۰pre.
    do 31 (f_contractive || f_equiv).
    apply IH; first done.
    f_equiv.
    eapply dist_le; last by apply SIdx.lt_le_incl.
    apply HΦ.
  Qed.
  #[global] Instance bwpｰproper e tid E :
    Proper (pointwise_relation _ (≡) ==> (≡)) (bwp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply equiv_dist => n.
    apply bwpｰne => v.
    apply equiv_dist. done.
  Qed.
  #[global] Instance bwpｰcontractive e tid E n :
    TCEq (to_val e) None →
    Proper (pointwise_relation _ (dist_later n) ==> (≡{n}≡)) (bwp e tid E).
  Proof.
    intros He Φ1 Φ2 HΦ.
    rewrite !bwpｰunfold /bwp۰pre He.
    repeat (f_contractive || f_equiv).
  Qed.

  Lemma bwpｰstate_interp e tid E Φ :
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E}=∗
        state_interp ns nt σ κs ∗
        BWP e ∶ tid @ E {{ Φ }}
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iEval (rewrite bwpｰunfold).
    iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "(Hinterp & H)".
    iApply (bwpｰunfold with "H Hinterp").
  Qed.

  Lemma bwpｰvalueｰfupd' v tid E Φ :
    (|={E}=> Φ v) ⊢
    BWP of_val v ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwpｰunfold.
    iSteps.
  Qed.
  Lemma bwpｰvalueｰfupd e v tid E Φ :
    AsVal e v →
    (|={E}=> Φ v) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwpｰvalueｰfupd' => <- //.
  Qed.
  Lemma bwpｰvalue' v tid E Φ :
    Φ v ⊢
    BWP of_val v ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (bwpｰvalueｰfupd' with "HΦ").
  Qed.
  Lemma bwpｰvalue e v tid E Φ :
    AsVal e v →
    Φ v ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwpｰvalue' => <- //.
  Qed.

  Lemma bwpｰvalueｰmono v tid E Φ1 Φ2 :
    BWP of_val v ∶ tid @ E {{ Φ1 }} -∗
    (Φ1 v ={E}=∗ Φ2 v) -∗
    BWP of_val v ∶ tid @ E {{ Φ2 }}.
  Proof.
    rewrite !bwpｰunfold.
    iIntros "H HΦ %ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iSteps.
  Qed.

  Lemma bwpｰstrongｰmono e tid E1 Φ1 E2 Φ2 :
    E1 ⊆ E2 →
    BWP e ∶ tid @ E1 {{ Φ1 }} -∗
    (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
    BWP e ∶ tid @ E2 {{ Φ2 }}.
  Proof.
    iIntros "%HE H HΦ".
    iLöb as "HLöb" forall (e).
    rewrite !bwpｰunfold /bwp۰pre.
    iIntros "%ns %nt %σ1 %κs Hinterp".
    destruct (to_val e) as [v |] eqn:He.
    - iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
      iMod ("H" with "Hinterp") as "(Hinterp & HΦ1)".
      iSteps.
    - iModIntro.
      iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
      iMod ("H" with "Hinterp") as ">(%Hreducible & H)".
      iStep. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep H£".
      iMod ("H" with "[//] [//] H£") as "H".
      do 2 iModIntro.
      iMod "H" as "($ & H & Hes)".
      iMod "Hclose" as "_".
      iSplitR "Hes"; iSteps.
  Qed.
  Lemma bwpｰmono e tid E Φ1 Φ2 :
    (∀ v, Φ1 v ⊢ Φ2 v) →
    BWP e ∶ tid @ E {{ Φ1 }} ⊢
    BWP e ∶ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "%HΦ H".
    iApply (bwpｰstrongｰmono with "H"); first done. iIntros "%v HΦ".
    iApply (HΦ with "HΦ").
  Qed.
  #[global] Instance bwpｰmono' e tid E :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (bwp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply bwpｰmono. done.
  Qed.
  #[global] Instance bwpｰflipｰmono' e tid E :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (bwp e tid E).
  Proof.
    solve_proper.
  Qed.

  Lemma fupdｰbwp e tid E Φ :
    (|={E}=> BWP e ∶ tid @ E {{ Φ }}) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite {2}bwpｰunfold.
    iIntros "H %ns %nt %σ %κs Hinterp".
    iMod "H" as "H".
    iRevert (ns nt σ κs) "Hinterp".
    iApply (bwpｰunfold with "H").
  Qed.
  Lemma bwpｰfupd e tid E Φ :
    BWP e ∶ tid @ E {{ v, |={E}=> Φ v }} ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (bwpｰstrongｰmono with "H"); first done.
    iSteps.
  Qed.

  Lemma bwpｰframeｰl e tid E Φ R :
    R ∗ BWP e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "(HR & H)".
    iApply (bwpｰstrongｰmono with "H"); first done.
    iSteps.
  Qed.
  Lemma bwpｰframeｰr e tid E Φ R :
    BWP e ∶ tid @ E {{ Φ }} ∗ R ⊢
    BWP e ∶ tid @ E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "(H & HR)".
    iApply (bwpｰstrongｰmono with "H"); first done.
    iSteps.
  Qed.

  Lemma bwpｰwand {e tid E} Φ1 Φ2 :
    BWP e ∶ tid @ E {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    BWP e ∶ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "H HΦ".
    iApply (bwpｰstrongｰmono with "H"); first done.
    iSteps.
  Qed.
  Lemma bwpｰframeｰwand e tid E Φ R :
    R -∗
    BWP e ∶ tid @ E {{ v, R -∗ Φ v }} -∗
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "HR H".
    iApply (bwpｰwand with "H").
    iSteps.
  Qed.

  Lemma bwpｰatomic e `{!Atomic e} tid E1 E2 Φ :
    (|={E1,E2}=> BWP e ∶ tid @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    rewrite !bwpｰunfold /bwp۰pre.
    iIntros "H %ns %nt %σ %κs Hinterp".
    destruct (to_val e) as [v |] eqn:He.
    - iMod ("H" with "Hinterp") as ">($ & $)".
    - iModIntro.
      iMod ("H" with "Hinterp") as ">>(%Hreducible & H)".
      iStep. iIntros "%κ %κs' %e2 %σ2 %es1 -> %Hstep1 H£".
      iMod ("H" with "[//] [//] H£") as "H".
      do 2 iModIntro.
      iMod "H" as "(Hinterp & H & $)".
      rewrite !bwpｰunfold /bwp۰pre.
      destruct (to_val e2) as [v2 |] eqn:He2.
      + iMod ("H" with "Hinterp") as "($ & >H)".
        iFrameSteps.
      + iMod ("H" with "Hinterp") as ">(%Hreducible2 & _)".
        destruct Hreducible2 as (κ2 & e3 & σ3 & es2 & Hstep2).
        edestruct atomic; [done | congruence].
  Qed.

  Lemma bwpｰbind K `{!Context K} e tid E Φ :
    BWP e ∶ tid @ E {{ v, BWP K (of_val v) ∶ tid @ E {{ Φ }} }} ⊢
    BWP K e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    rewrite bwpｰunfold /bwp۰pre.
    destruct (to_val e) as [v |] eqn:He.
    - apply of_valｰto_val in He as <-.
      iApply (bwpｰstate_interp with "H").
    - rewrite bwpｰunfold /bwp۰pre contextｰfillｰnot_val //.
      iIntros "%ns %nt %σ1 %κs Hinterp !>".
      iMod ("H" with "Hinterp") as ">(%Hreducible1 & H)".
      iModIntro; iSplit; first eauto using reducibleｰcontext.
      iIntros "%κ %κs' %e2 %σ2 %es1 -> %Hstep1 H£".
      destruct (contextｰfillｰstepｰinv tid e σ1 κ e2 σ2 es1) as (e2' & -> & Hstep1'); [done.. |].
      iMod ("H" with "[//] [//] H£") as "H".
      iModIntro. iSteps.
  Qed.

  Lemma bwpｰbindｰinv K `{!Context K} e tid E Φ :
    BWP K e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ v, BWP K (of_val v) ∶ tid @ E {{ Φ }} }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    destruct (to_val e) as [v |] eqn:He.
    - apply of_valｰto_val in He as <-.
      iApply bwpｰvalue'.
      iApply "H".
    - rewrite !bwpｰunfold /bwp۰pre contextｰfillｰnot_val He //.
      iIntros "%ns %nt %σ1 %κs Hinterp !>".
      iMod ("H" with "Hinterp") as ">(%Hreducible & H)".
      iModIntro; iSplit; first eauto using reducibleｰcontextｰinv.
      iIntros "%κ %κs' %e2 %σ2 %es1 -> %Hstep1 H£".
      iMod ("H" with "[//] [] H£") as "H".
      { eauto using contextｰfillｰstep. }
      iModIntro. iSteps.
  Qed.

  #[global] Instance frameｰbwp p e tid E R Φ1 Φ2 :
    (∀ v, Frame p R (Φ1 v) (Φ2 v)) →
    Frame
      p
      R
      (BWP e ∶ tid @ E {{ Φ1 }})
      (BWP e ∶ tid @ E {{ Φ2 }})
  | 2.
  Proof.
    rewrite /Frame bwpｰframeｰl => HR.
    apply bwpｰmono, HR.
  Qed.

  #[global] Instance is_except_0ｰbwp e tid E Φ :
    IsExcept0 (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 -{2}fupdｰbwp -except_0_fupd -fupd_intro //.
  Qed.

  #[global] Instance elim_modalｰbupdｰbwp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|==> P)
      P
      (BWP e ∶ tid @ E {{ Φ }})
      (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupdｰbwp //.
  Qed.

  #[global] Instance elim_modalｰfupdｰbwp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|={E}=> P)
      P
      (BWP e ∶ tid @ E {{ Φ }})
      (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r fupdｰbwp //.
  Qed.
  #[global] Instance elim_modalｰfupdｰbwpｰwrong_mask p e tid E1 E2 P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupdｰbwp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2}=> P)
      False
      (BWP e ∶ tid @ E1 {{ Φ }})
      False
  | 100.
  Proof.
    intros [].
  Qed.

  #[global] Instance elim_modalｰfupdｰbwpｰatomic p e tid E1 E2 P Φ :
    ElimModal
      (Atomic e)
      p
      false
      (|={E1,E2}=> P)
      P
      (BWP e ∶ tid @ E1 {{ Φ }})
      (BWP e ∶ tid @ E2 {{ v, |={E2,E1}=> Φ v }})%I
  | 100.
  Proof.
    intros He.
    rewrite bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r bwpｰatomic //.
  Qed.
  #[global] Instance elim_modalｰfupdｰbwpｰatomicｰwrong_mask p e tid E1 E2 E2' P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2,E2'}=> P)
      False
      (BWP e ∶ tid @ E1 {{ Φ }})
      False
  | 200.
  Proof.
    intros [].
  Qed.

  #[global] Instance add_modalｰfupdｰbwp e tid E P Φ :
    AddModal
      (|={E}=> P)
      P
      (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /AddModal fupd_frame_r bi.wand_elim_r fupdｰbwp //.
  Qed.

  #[global] Instance elim_accｰbwpｰatomic {X} e tid E1 E2 α β γ Φ :
    ElimAcc (X := X)
      (Atomic e)
      (fupd E1 E2)
      (fupd E2 E1)
      α
      β
      γ
      (BWP e ∶ tid @ E1 {{ Φ }})
      (λ x, BWP e ∶ tid @ E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I
  | 100.
  Proof.
    iIntros "%He Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply (bwpｰwand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.

  #[global] Instance elim_accｰbwpｰnonatomic {X} e tid E α β γ Φ :
    ElimAcc (X := X)
      True
      (fupd E E)
      (fupd E E)
      α
      β
      γ
      (BWP e ∶ tid @ E {{ Φ }})
      (λ x, BWP e ∶ tid @ E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply bwpｰfupd.
    iApply (bwpｰwand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.

  Lemma bwpｰliftｰstep e tid E Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E, ∅}=>
        ⌜reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ (later۰function ns) ={∅}=∗
            ▷ |={∅, E}=>
            state_interp ns (nt + length es) σ' κs' ∗
            ( ⧖ (˖ns) -∗
                BWP e' ∶ tid @ E {{ Φ }} ∗
                [∗ list] i ↦ e ∈ es,
                  BWP e ∶ nt + i {{ fork_post }}
            )
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwpｰunfold /bwp۰pre => ->.
    iIntros "H %ns %nt %σ %κs Hinterp !>".
    iMod ("H" with "Hinterp") as "(%Hreducible & H)".
    iStep 9 as (κ κs' e' σ' es Hstep) "H H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(Hinterp & H)".
    iMod (state_interpｰmono with "Hinterp") as "Hinterp".
    iDestruct (state_interpｰsteps۰lbｰget with "Hinterp") as "#H⧖".
    iFrameSteps.
  Qed.
  Lemma bwpｰliftｰstepｰnofork e tid E Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E, ∅}=>
        ⌜reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ (later۰function ns) ={∅}=∗
            ▷ |={∅, E}=>
            ⌜es = []⌝ ∗
            state_interp ns nt σ' κs' ∗
            ( ⧖ (˖ns) -∗
              BWP e' ∶ tid @ E {{ Φ }}
            )
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwpｰliftｰstep; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iFrameSteps.
  Qed.

  Lemma bwpｰliftｰatomicｰstep e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E1}=∗
        ⌜reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ (later۰function ns) -∗
            |={E1}[E2]▷=>
            state_interp ns (nt + length es) σ' κs' ∗
            ( ⧖ (˖ns) -∗
                from_option Φ False (to_val e') ∗
                [∗ list] i ↦ e ∈ es,
                  BWP e ∶ nt + i {{ fork_post }}
            )
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwpｰliftｰstep; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod "Hclose" as "_".
    iMod ("H" with "[//] [//] H£") as "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_".
    iMod "H" as "($ & H)". iIntros "!> H⧖".
    iDestruct ("H" with "H⧖") as "(HΦ & $)".
    destruct (to_val e') eqn:He'; last by iExFalso.
    iApply (bwpｰvalue with "HΦ").
    apply of_valｰto_val. done.
  Qed.
  Lemma bwpｰliftｰatomicｰstepｰnofork e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E1}=∗
        ⌜reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ (later۰function ns) -∗
            |={E1}[E2]▷=>
            ⌜es = []⌝ ∗
            state_interp ns nt σ' κs' ∗
            ( ⧖ (˖ns) -∗
              from_option Φ False (to_val e')
            )
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwpｰliftｰatomicｰstep; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iFrameSteps.
  Qed.

  Lemma bwpｰliftｰpureｰstepｰnofork e tid ns E1 E2 Φ :
    ( ∀ σ,
      reducible tid e σ
    ) →
    ( ∀ σ κ e' σ' es,
      prim_step tid e σ κ e' σ' es →
        κ = [] ∧
        σ' = σ ∧
        es = []
    ) →
    ⧖ ns -∗
    ( |={E1}[E2]▷=>
      ∀ σ e' κ es,
      ⌜prim_step tid e σ κ e' σ es⌝ -∗
      ⧖ (˖ns) -∗
      £ (later۰function ns) -∗
      BWP e' ∶ tid @ E1 {{ Φ }}
    ) -∗
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H⧖ H".
    iApply bwpｰliftｰstepｰnofork.
    { specialize (Hsafe inhabitant). eauto using reducibleｰnot_val. }
    iIntros "%ns' %nt %σ %κs Hinterp".
    iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first iSteps. iIntros "%κ %κs' %e' %σ' %es -> %Hstep H£ !> !>".
    edestruct Hpure as (? & ? & ?); first done. subst.
    iDestruct (state_interpｰsteps۰lbｰvalid with "Hinterp H⧖") as %?.
    iDestruct (lc_weaken (later۰function ns) with "H£") as "H£"; first auto.
    iFrameStep 2.
    iMod "H".
    iSteps.
  Qed.

  Lemma bwpｰliftｰpureｰdetｰstepｰnofork e1 e2 tid ns E1 E2 Φ :
    ( ∀ σ1,
      reducible tid e1 σ1
    ) →
    ( ∀ σ1 κ e2' σ2 es,
      prim_step tid e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = []
    ) →
    ⧖ ns -∗
    ( |={E1}[E2]▷=>
      ⧖ (˖ns) -∗
      £ (later۰function ns) -∗
      BWP e2 ∶ tid @ E1 {{ Φ }}
    ) -∗
    BWP e1 ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H⧖ H".
    iApply (bwpｰliftｰpureｰstepｰnofork with "H⧖"); [done | naive_solver |].
    iApply (step_fupd_wand with "H"). iIntros "H %σ1 %e2' %κ %es %Hstep H£".
    apply Hpure in Hstep as (-> & _ & -> & ->).
    iSteps.
  Qed.

  Lemma bwpｰpureｰstep ϕ n e1 e2 ns tid E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    ⧖ ns -∗
    ▷^n (
      ⧖ (ns + n) -∗
      £ (later۰sum ns n) -∗
      BWP e2 ∶ tid @ E {{ Φ }}
    ) -∗
    BWP e1 ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%Hexec %Hϕ H⧖ H".
    specialize (Hexec Hϕ).
    iInduction Hexec as [e | n e1 e2 e3 (Hsafe & Hpure)] "IH" forall (ns).
    - iMod lc_zero as "H£".
      iSteps.
    - iApply (bwpｰliftｰpureｰdetｰstepｰnofork with "H⧖").
      { eauto using reducible_no_obsｰreducible. }
      { eauto. }
      do 3 iModIntro.
      rewrite lc_split. iSteps.
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.

  #[local] Hint Resolve
    base_reducibleｰreducible
    base_reducibleｰprim_step
  : core.

  Lemma bwpｰliftｰbaseｰstep e tid E Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E, ∅}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ (later۰function ns) ={∅}=∗
            ▷ |={∅, E}=>
            state_interp ns (nt + length es) σ' κs' ∗
            ( ⧖ (˖ns) -∗
                BWP e' ∶ tid @ E {{ Φ }} ∗
                [∗ list] i ↦ e ∈ es,
                  BWP e ∶ nt + i {{ fork_post }}
            )
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwpｰliftｰstep; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%κ %κs' %e' %σ' %es -> %Hstep".
    iApply ("H" with "[//] [%]"); first auto.
  Qed.
  Lemma bwpｰliftｰbaseｰstepｰnofork e tid E Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E, ∅}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ (later۰function ns) ={∅}=∗
            ▷ |={∅, E}=>
            ⌜es = []⌝ ∗
            state_interp ns nt σ' κs' ∗
            ( ⧖ ns -∗
              BWP e' ∶ tid @ E {{ Φ }}
            )
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwpｰliftｰbaseｰstep; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma bwpｰliftｰatomicｰbaseｰstep e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E1}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ (later۰function ns) -∗
            |={E1}[E2]▷=>
            state_interp ns (nt + length es) σ' κs' ∗
            ( ⧖ (˖ns) -∗
                from_option Φ False (to_val e') ∗
                [∗ list] i ↦ e ∈ es,
                  BWP e ∶ nt + i {{ fork_post }}
            )
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwpｰliftｰatomicｰstep; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%κ %κs' %e' %σ' %es -> %Hstep".
    iApply ("H" with "[//] [%]"); first auto.
  Qed.
  Lemma bwpｰliftｰatomicｰbaseｰstepｰnofork e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E1}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ (later۰function ns) -∗
            |={E1}[E2]▷=>
            ⌜es = []⌝ ∗
            state_interp ns nt σ' κs' ∗
            ( ⧖ (˖ns) -∗
              from_option Φ False (to_val e')
            )
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwpｰliftｰatomicｰbaseｰstep; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma bwpｰmatch l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ BWP e ∶ tid @ E {{ Φ }} -∗
    BWP Match #l x_fb e_fb brs ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He >#Hl H".
    iApply bwpｰliftｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interpｰheaders۰atｰvalid with "Hinterp Hl") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e_ %σ_ %es -> %Hstep _ !>".
    inv_base_step.
    iSteps.
  Qed.
  Lemma bwpｰmatchｰcontext K `{!Context K} l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ BWP K e ∶ tid @ E {{ Φ }} -∗
    BWP K (Match #l x_fb e_fb brs) ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He Hl H".
    iApply bwpｰbind.
    iApply (bwpｰmatch with "Hl"); first done.
    iApply (bwpｰbindｰinv with "H").
  Qed.

  Lemma bwpｰresolve e pid v prophs tid E Φ :
    Atomic e →
    to_val e = None →
    prophet۰model pid prophs -∗
    BWP e ∶ tid @ E {{ res,
      ∀ prophs',
      ⌜prophs = (res, v) :: prophs'⌝ -∗
      prophet۰model pid prophs' -∗
      Φ res
    }} -∗
    BWP Resolve e #pid v ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%Hatomic %He Hpid H".
    rewrite !bwpｰunfold /bwp۰pre He.
    iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iMod ("H" with "Hinterp") as ">(%Hreducible & H)".
    iSplitR. { iPureIntro. apply reducibleｰresolve; done. }
    iIntros "!> %κ %κs' %e2 %σ2 %es -> %Hstep H£".
    destruct κ as [| (pid' & (w' & v')) κ _] using rev_ind.
    - exfalso. apply prim_stepｰresolveｰinv in Hstep; last done.
      inv_base_step.
      destruct κ; done.
    - rewrite -assoc.
      apply prim_stepｰresolveｰinv in Hstep; last done.
      inv_base_step. simplify_list_eq.
      iMod ("H" $! _ _ (Val w') σ2 es with "[%] [%] H£") as "H".
      { done. }
      { eexists [] _ _; done. }
      do 2 iModIntro.
      iMod "H" as "(Hinterp & H & $)".
      iMod (state_interpｰprophetｰresolve with "Hinterp Hpid") as "(%prophs' & -> & $ & Hpid')".
      iApply (bwpｰvalueｰmono with "H").
      iSteps.
  Qed.
End zoo۰G.
