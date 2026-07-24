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
Lemma later۰function𑁒lb ns :
  later_constant ≤ later۰function ns.
Proof.
  rewrite /later۰function. lia.
Qed.
Lemma later۰function𑁒mono ns1 ns2 :
  ns1 ≤ ns2 →
  later۰function ns1 ≤ later۰function ns2.
Proof.
  intros.
  apply Nat.add_le_mono_r, Nat.mul_le_mono_l => //.
Qed.
Lemma later۰function𑁒0 :
  later۰function 0 = later_constant.
Proof.
  rewrite /later۰function. lia.
Qed.
#[global] Hint Resolve
  later۰function𑁒lb
  later۰function𑁒mono
: core.

Fixpoint later۰sum ns n : nat :=
  match n with
  | 0 =>
      0
  | ˖n =>
      later۰function ns + later۰sum ˖ns n
  end.

Lemma later۰sum𑁒lb ns n :
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

  #[local] Instance bwp۰pre𑁒contractive :
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
#[local] Lemma bwp𑁒unseal `{zoo۰G : !ZooG Σ} :
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

  Lemma bwp𑁒unfold e tid E Φ :
    BWP e ∶ tid @ E {{ Φ }} ⊣⊢
    bwp۰pre bwp e tid E Φ.
  Proof.
    rewrite bwp𑁒unseal.
    apply: (fixpoint_unfold bwp۰pre).
  Qed.

  #[global] Instance bwp𑁒ne e tid E n :
    Proper (pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) (bwp e tid E).
  Proof.
    move: e. induction (lt_wf n) as [n _ IH] => e Φ1 Φ2 HΦ.
    rewrite !bwp𑁒unfold /bwp۰pre.
    do 31 (f_contractive || f_equiv).
    apply IH; first done.
    f_equiv.
    eapply dist_le; last by apply SIdx.lt_le_incl.
    apply HΦ.
  Qed.
  #[global] Instance bwp𑁒proper e tid E :
    Proper (pointwise_relation _ (≡) ==> (≡)) (bwp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply equiv_dist => n.
    apply bwp𑁒ne => v.
    apply equiv_dist. done.
  Qed.
  #[global] Instance bwp𑁒contractive e tid E n :
    TCEq (to_val e) None →
    Proper (pointwise_relation _ (dist_later n) ==> (≡{n}≡)) (bwp e tid E).
  Proof.
    intros He Φ1 Φ2 HΦ.
    rewrite !bwp𑁒unfold /bwp۰pre He.
    repeat (f_contractive || f_equiv).
  Qed.

  Lemma bwp𑁒state_interp e tid E Φ :
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E}=∗
        state_interp ns nt σ κs ∗
        BWP e ∶ tid @ E {{ Φ }}
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iEval (rewrite bwp𑁒unfold).
    iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "(Hinterp & H)".
    iApply (bwp𑁒unfold with "H Hinterp").
  Qed.

  Lemma bwp𑁒value𑁒fupd' v tid E Φ :
    (|={E}=> Φ v) ⊢
    BWP of_val v ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp𑁒unfold.
    iSteps.
  Qed.
  Lemma bwp𑁒value𑁒fupd e v tid E Φ :
    AsVal e v →
    (|={E}=> Φ v) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp𑁒value𑁒fupd' => <- //.
  Qed.
  Lemma bwp𑁒value' v tid E Φ :
    Φ v ⊢
    BWP of_val v ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (bwp𑁒value𑁒fupd' with "HΦ").
  Qed.
  Lemma bwp𑁒value e v tid E Φ :
    AsVal e v →
    Φ v ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp𑁒value' => <- //.
  Qed.

  Lemma bwp𑁒value𑁒mono v tid E Φ1 Φ2 :
    BWP of_val v ∶ tid @ E {{ Φ1 }} -∗
    (Φ1 v ={E}=∗ Φ2 v) -∗
    BWP of_val v ∶ tid @ E {{ Φ2 }}.
  Proof.
    rewrite !bwp𑁒unfold.
    iIntros "H HΦ %ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iSteps.
  Qed.

  Lemma bwp𑁒strong𑁒mono e tid E1 Φ1 E2 Φ2 :
    E1 ⊆ E2 →
    BWP e ∶ tid @ E1 {{ Φ1 }} -∗
    (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
    BWP e ∶ tid @ E2 {{ Φ2 }}.
  Proof.
    iIntros "%HE H HΦ".
    iLöb as "HLöb" forall (e).
    rewrite !bwp𑁒unfold /bwp۰pre.
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
  Lemma bwp𑁒mono e tid E Φ1 Φ2 :
    (∀ v, Φ1 v ⊢ Φ2 v) →
    BWP e ∶ tid @ E {{ Φ1 }} ⊢
    BWP e ∶ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "%HΦ H".
    iApply (bwp𑁒strong𑁒mono with "H"); first done. iIntros "%v HΦ".
    iApply (HΦ with "HΦ").
  Qed.
  #[global] Instance bwp𑁒mono' e tid E :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (bwp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply bwp𑁒mono. done.
  Qed.
  #[global] Instance bwp𑁒flip𑁒mono' e tid E :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (bwp e tid E).
  Proof.
    solve_proper.
  Qed.

  Lemma fupd𑁒bwp e tid E Φ :
    (|={E}=> BWP e ∶ tid @ E {{ Φ }}) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite {2}bwp𑁒unfold.
    iIntros "H %ns %nt %σ %κs Hinterp".
    iMod "H" as "H".
    iRevert (ns nt σ κs) "Hinterp".
    iApply (bwp𑁒unfold with "H").
  Qed.
  Lemma bwp𑁒fupd e tid E Φ :
    BWP e ∶ tid @ E {{ v, |={E}=> Φ v }} ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (bwp𑁒strong𑁒mono with "H"); first done.
    iSteps.
  Qed.

  Lemma bwp𑁒frame𑁒l e tid E Φ R :
    R ∗ BWP e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "(HR & H)".
    iApply (bwp𑁒strong𑁒mono with "H"); first done.
    iSteps.
  Qed.
  Lemma bwp𑁒frame𑁒r e tid E Φ R :
    BWP e ∶ tid @ E {{ Φ }} ∗ R ⊢
    BWP e ∶ tid @ E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "(H & HR)".
    iApply (bwp𑁒strong𑁒mono with "H"); first done.
    iSteps.
  Qed.

  Lemma bwp𑁒wand {e tid E} Φ1 Φ2 :
    BWP e ∶ tid @ E {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    BWP e ∶ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "H HΦ".
    iApply (bwp𑁒strong𑁒mono with "H"); first done.
    iSteps.
  Qed.
  Lemma bwp𑁒frame𑁒wand e tid E Φ R :
    R -∗
    BWP e ∶ tid @ E {{ v, R -∗ Φ v }} -∗
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "HR H".
    iApply (bwp𑁒wand with "H").
    iSteps.
  Qed.

  Lemma bwp𑁒atomic e `{!Atomic e} tid E1 E2 Φ :
    (|={E1,E2}=> BWP e ∶ tid @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    rewrite !bwp𑁒unfold /bwp۰pre.
    iIntros "H %ns %nt %σ %κs Hinterp".
    destruct (to_val e) as [v |] eqn:He.
    - iMod ("H" with "Hinterp") as ">($ & $)".
    - iModIntro.
      iMod ("H" with "Hinterp") as ">>(%Hreducible & H)".
      iStep. iIntros "%κ %κs' %e2 %σ2 %es1 -> %Hstep1 H£".
      iMod ("H" with "[//] [//] H£") as "H".
      do 2 iModIntro.
      iMod "H" as "(Hinterp & H & $)".
      rewrite !bwp𑁒unfold /bwp۰pre.
      destruct (to_val e2) as [v2 |] eqn:He2.
      + iMod ("H" with "Hinterp") as "($ & >H)".
        iFrameSteps.
      + iMod ("H" with "Hinterp") as ">(%Hreducible2 & _)".
        destruct Hreducible2 as (κ2 & e3 & σ3 & es2 & Hstep2).
        edestruct atomic; [done | congruence].
  Qed.

  Lemma bwp𑁒bind K `{!Context K} e tid E Φ :
    BWP e ∶ tid @ E {{ v, BWP K (of_val v) ∶ tid @ E {{ Φ }} }} ⊢
    BWP K e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    rewrite bwp𑁒unfold /bwp۰pre.
    destruct (to_val e) as [v |] eqn:He.
    - apply of_val𑁒to_val in He as <-.
      iApply (bwp𑁒state_interp with "H").
    - rewrite bwp𑁒unfold /bwp۰pre context𑁒fill𑁒not_val //.
      iIntros "%ns %nt %σ1 %κs Hinterp !>".
      iMod ("H" with "Hinterp") as ">(%Hreducible1 & H)".
      iModIntro; iSplit; first eauto using reducible𑁒context.
      iIntros "%κ %κs' %e2 %σ2 %es1 -> %Hstep1 H£".
      destruct (context𑁒fill𑁒step𑁒inv tid e σ1 κ e2 σ2 es1) as (e2' & -> & Hstep1'); [done.. |].
      iMod ("H" with "[//] [//] H£") as "H".
      iModIntro. iSteps.
  Qed.

  Lemma bwp𑁒bind𑁒inv K `{!Context K} e tid E Φ :
    BWP K e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ v, BWP K (of_val v) ∶ tid @ E {{ Φ }} }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    destruct (to_val e) as [v |] eqn:He.
    - apply of_val𑁒to_val in He as <-.
      iApply bwp𑁒value'.
      iApply "H".
    - rewrite !bwp𑁒unfold /bwp۰pre context𑁒fill𑁒not_val He //.
      iIntros "%ns %nt %σ1 %κs Hinterp !>".
      iMod ("H" with "Hinterp") as ">(%Hreducible & H)".
      iModIntro; iSplit; first eauto using reducible𑁒context𑁒inv.
      iIntros "%κ %κs' %e2 %σ2 %es1 -> %Hstep1 H£".
      iMod ("H" with "[//] [] H£") as "H".
      { eauto using context𑁒fill𑁒step. }
      iModIntro. iSteps.
  Qed.

  #[global] Instance frame𑁒bwp p e tid E R Φ1 Φ2 :
    (∀ v, Frame p R (Φ1 v) (Φ2 v)) →
    Frame
      p
      R
      (BWP e ∶ tid @ E {{ Φ1 }})
      (BWP e ∶ tid @ E {{ Φ2 }})
  | 2.
  Proof.
    rewrite /Frame bwp𑁒frame𑁒l => HR.
    apply bwp𑁒mono, HR.
  Qed.

  #[global] Instance is_except_0𑁒bwp e tid E Φ :
    IsExcept0 (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 -{2}fupd𑁒bwp -except_0_fupd -fupd_intro //.
  Qed.

  #[global] Instance elim_modal𑁒bupd𑁒bwp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|==> P)
      P
      (BWP e ∶ tid @ E {{ Φ }})
      (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd𑁒bwp //.
  Qed.

  #[global] Instance elim_modal𑁒fupd𑁒bwp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|={E}=> P)
      P
      (BWP e ∶ tid @ E {{ Φ }})
      (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r fupd𑁒bwp //.
  Qed.
  #[global] Instance elim_modal𑁒fupd𑁒bwp𑁒wrong_mask p e tid E1 E2 P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd𑁒bwp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
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

  #[global] Instance elim_modal𑁒fupd𑁒bwp𑁒atomic p e tid E1 E2 P Φ :
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
    rewrite bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r bwp𑁒atomic //.
  Qed.
  #[global] Instance elim_modal𑁒fupd𑁒bwp𑁒atomic𑁒wrong_mask p e tid E1 E2 E2' P Φ :
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

  #[global] Instance add_modal𑁒fupd𑁒bwp e tid E P Φ :
    AddModal
      (|={E}=> P)
      P
      (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd𑁒bwp //.
  Qed.

  #[global] Instance elim_acc𑁒bwp𑁒atomic {X} e tid E1 E2 α β γ Φ :
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
    iApply (bwp𑁒wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.

  #[global] Instance elim_acc𑁒bwp𑁒nonatomic {X} e tid E α β γ Φ :
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
    iApply bwp𑁒fupd.
    iApply (bwp𑁒wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.

  Lemma bwp𑁒lift𑁒step e tid E Φ :
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
    rewrite bwp𑁒unfold /bwp۰pre => ->.
    iIntros "H %ns %nt %σ %κs Hinterp !>".
    iMod ("H" with "Hinterp") as "(%Hreducible & H)".
    iStep 9 as (κ κs' e' σ' es Hstep) "H H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(Hinterp & H)".
    iMod (state_interp𑁒mono with "Hinterp") as "Hinterp".
    iDestruct (state_interp𑁒steps۰lb𑁒get with "Hinterp") as "#H⧖".
    iFrameSteps.
  Qed.
  Lemma bwp𑁒lift𑁒step𑁒nofork e tid E Φ :
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
    iApply bwp𑁒lift𑁒step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iFrameSteps.
  Qed.

  Lemma bwp𑁒lift𑁒atomic𑁒step e tid E1 E2 Φ :
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
    iApply bwp𑁒lift𑁒step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod "Hclose" as "_".
    iMod ("H" with "[//] [//] H£") as "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_".
    iMod "H" as "($ & H)". iIntros "!> H⧖".
    iDestruct ("H" with "H⧖") as "(HΦ & $)".
    destruct (to_val e') eqn:He'; last by iExFalso.
    iApply (bwp𑁒value with "HΦ").
    apply of_val𑁒to_val. done.
  Qed.
  Lemma bwp𑁒lift𑁒atomic𑁒step𑁒nofork e tid E1 E2 Φ :
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
    iApply bwp𑁒lift𑁒atomic𑁒step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iFrameSteps.
  Qed.

  Lemma bwp𑁒lift𑁒pure𑁒step𑁒nofork e tid ns E1 E2 Φ :
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
    iApply bwp𑁒lift𑁒step𑁒nofork.
    { specialize (Hsafe inhabitant). eauto using reducible𑁒not_val. }
    iIntros "%ns' %nt %σ %κs Hinterp".
    iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first iSteps. iIntros "%κ %κs' %e' %σ' %es -> %Hstep H£ !> !>".
    edestruct Hpure as (? & ? & ?); first done. subst.
    iDestruct (state_interp𑁒steps۰lb𑁒valid with "Hinterp H⧖") as %?.
    iDestruct (lc_weaken (later۰function ns) with "H£") as "H£"; first auto.
    iFrameStep 2.
    iMod "H".
    iSteps.
  Qed.

  Lemma bwp𑁒lift𑁒pure𑁒det𑁒step𑁒nofork e1 e2 tid ns E1 E2 Φ :
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
    iApply (bwp𑁒lift𑁒pure𑁒step𑁒nofork with "H⧖"); [done | naive_solver |].
    iApply (step_fupd_wand with "H"). iIntros "H %σ1 %e2' %κ %es %Hstep H£".
    apply Hpure in Hstep as (-> & _ & -> & ->).
    iSteps.
  Qed.

  Lemma bwp𑁒pure𑁒step ϕ n e1 e2 ns tid E Φ :
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
    - iApply (bwp𑁒lift𑁒pure𑁒det𑁒step𑁒nofork with "H⧖").
      { eauto using reducible_no_obs𑁒reducible. }
      { eauto. }
      do 3 iModIntro.
      rewrite lc_split. iSteps.
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.

  #[local] Hint Resolve
    base_reducible𑁒reducible
    base_reducible𑁒prim_step
  : core.

  Lemma bwp𑁒lift𑁒base𑁒step e tid E Φ :
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
    iApply bwp𑁒lift𑁒step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%κ %κs' %e' %σ' %es -> %Hstep".
    iApply ("H" with "[//] [%]"); first auto.
  Qed.
  Lemma bwp𑁒lift𑁒base𑁒step𑁒nofork e tid E Φ :
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
    iApply bwp𑁒lift𑁒base𑁒step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma bwp𑁒lift𑁒atomic𑁒base𑁒step e tid E1 E2 Φ :
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
    iApply bwp𑁒lift𑁒atomic𑁒step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%κ %κs' %e' %σ' %es -> %Hstep".
    iApply ("H" with "[//] [%]"); first auto.
  Qed.
  Lemma bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork e tid E1 E2 Φ :
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
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step; first done. iIntros "%ns %nt %σ %κs Hinterp".
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

  Lemma bwp𑁒match l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ BWP e ∶ tid @ E {{ Φ }} -∗
    BWP Match #l x_fb e_fb brs ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He >#Hl H".
    iApply bwp𑁒lift𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp𑁒headers۰at𑁒valid with "Hinterp Hl") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e_ %σ_ %es -> %Hstep _ !>".
    invert_base_step.
    iSteps.
  Qed.
  Lemma bwp𑁒match𑁒context K `{!Context K} l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ BWP K e ∶ tid @ E {{ Φ }} -∗
    BWP K (Match #l x_fb e_fb brs) ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He Hl H".
    iApply bwp𑁒bind.
    iApply (bwp𑁒match with "Hl"); first done.
    iApply (bwp𑁒bind𑁒inv with "H").
  Qed.

  Lemma bwp𑁒resolve e pid v prophs tid E Φ :
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
    rewrite !bwp𑁒unfold /bwp۰pre He.
    iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iMod ("H" with "Hinterp") as ">(%Hreducible & H)".
    iSplitR. { iPureIntro. apply reducible𑁒resolve; done. }
    iIntros "!> %κ %κs' %e2 %σ2 %es -> %Hstep H£".
    destruct κ as [| (pid' & (w' & v')) κ _] using rev_ind.
    - exfalso. apply prim_step𑁒resolve𑁒inv in Hstep; last done.
      invert_base_step.
      destruct κ; done.
    - rewrite -assoc.
      apply prim_step𑁒resolve𑁒inv in Hstep; last done.
      invert_base_step. simplify_list_eq.
      iMod ("H" $! _ _ (Val w') σ2 es with "[%] [%] H£") as "H".
      { done. }
      { eexists [] _ _; done. }
      do 2 iModIntro.
      iMod "H" as "(Hinterp & H & $)".
      iMod (state_interp𑁒prophet𑁒resolve with "Hinterp Hpid") as "(%prophs' & -> & $ & Hpid')".
      iApply (bwp𑁒value𑁒mono with "H").
      iSteps.
  Qed.
End zoo۰G.
