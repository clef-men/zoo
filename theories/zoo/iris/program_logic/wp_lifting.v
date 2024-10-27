From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.iris.program_logic Require Import
  ectx_language.
From zoo.iris.program_logic Require Export
  wp.
From zoo Require Import
  options.

Section language.
  Context `{iris_G : !IrisG Λ Σ}.

  Implicit Types e : expr Λ.
  Implicit Types Φ : val Λ → iProp Σ.

  Lemma wp_lift_step e E Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E, ∅}=>
        ⌜reducible e σ⌝ ∗
          ∀ e' σ' es,
          ⌜prim_step e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={∅}=> ▷ |={∅, E}=>
            state_interp (nt + length es) σ' κs ∗
            wp e' E Φ ∗
            [∗ list] i ↦ e ∈ es,
              wp e ⊤ fork_post
    ) ⊢
    WP e @ E {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre => -> //.
  Qed.
  Lemma wp_lift_step_nofork e E Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E, ∅}=>
        ⌜reducible e σ⌝ ∗
          ∀ e' σ' es,
          ⌜prim_step e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={∅}=> ▷ |={∅, E}=>
            ⌜es = []⌝ ∗
            state_interp nt σ' κs ∗
            wp e' E Φ
    ) ⊢
    WP e @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply wp_lift_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e' %σ' %es %Hstep H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hσ & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma wp_lift_atomic_step e E1 E2 Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E1}=>
        ⌜reducible e σ⌝ ∗
          ∀ e' σ' es,
          ⌜prim_step e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={E1}[E2]▷=>
            state_interp (nt + length es) σ' κs ∗
            from_option Φ False (to_val e') ∗
            [∗ list] e ∈ es,
              WP e @ ⊤ {{ fork_post }}
    ) ⊢
    WP e @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply wp_lift_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose %e' %σ' %es %Hstep H£".
    iMod "Hclose" as "_".
    iMod ("H" with "[//] H£") as "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_".
    iMod "H" as "($ & HΦ & $)".
    destruct (to_val e') eqn:He'; last by iExFalso.
    iApply (wp_value with "HΦ").
    apply of_to_val. done.
  Qed.
  Lemma wp_lift_atomic_step_nofork e E1 E2 Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E1}=>
        ⌜reducible e σ⌝ ∗
          ∀ e' σ' es,
          ⌜prim_step e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={E1}[E2]▷=>
            ⌜es = []⌝ ∗
            state_interp nt σ' κs ∗
            from_option Φ False (to_val e')
    ) ⊢
    WP e @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply wp_lift_atomic_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e' %σ' %es %Hstep H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hσ & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma wp_lift_pure_step_nofork `{!Inhabited (state Λ)} e E1 E2 Φ :
    ( ∀ σ,
      reducible e σ
    ) →
    ( ∀ σ κ e' σ' es,
      prim_step e σ κ e' σ' es →
        κ = [] ∧
        σ' = σ ∧
        es = []
    ) →
    ( |={E1}[E2]▷=>
      ∀ σ e' κ es,
      ⌜prim_step e σ κ e' σ es⌝ -∗
      £ 1 -∗
      WP e' @ E1 {{ Φ }}
    ) ⊢
    WP e @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H".
    iApply wp_lift_step.
    { specialize (Hsafe inhabitant). eauto using reducible_not_val. }
    iIntros "%nt %σ %κ %κs Hσ".
    iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first iSteps. iIntros "%e' %σ' %es %Hstep H£ !> !>".
    edestruct Hpure as (? & ? & ?); first done. subst.
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma wp_lift_pure_det_step_nofork `{!Inhabited (state Λ)} e1 e2 E1 E2 Φ :
    ( ∀ σ1,
      reducible e1 σ1
    ) →
    ( ∀ σ1 κ e2' σ2 es,
      prim_step e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = []
    ) →
    ( |={E1}[E2]▷=>
      £ 1 -∗
      WP e2 @ E1 {{ Φ }}
    ) ⊢
    WP e1 @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H".
    iApply (wp_lift_pure_step_nofork); [done | naive_solver |].
    iApply (step_fupd_wand with "H"). iIntros "H %σ1 %e2' %κ %es %Hstep H£".
    apply Hpure in Hstep as (-> & _ & -> & ->).
    iSteps.
  Qed.

  Lemma wp_pure_step `{!Inhabited (state Λ)} ψ n e1 e2 E1 E2 Φ :
    PureExec ψ n e1 e2 →
    ψ →
    ( |={E1}[E2]▷=>^n
      £ n -∗
      WP e2 @ E1 {{ Φ }}
    ) ⊢
    WP e1 @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hexec %Hψ H".
    specialize (Hexec Hψ).
    iInduction Hexec as [e | n e1 e2 e3 (Hsafe & Hpure)] "IH" => /=.
    - iMod lc_zero as "H£".
      iSteps.
    - iApply wp_lift_pure_det_step_nofork.
      + eauto using reducible_no_obs_reducible.
      + done.
      + iApply (step_fupd_wand with "H"). iIntros "H H£".
        iApply "IH".
        iApply (step_fupdN_wand with "H").
        rewrite (lc_succ n). iSteps.
  Qed.
  Lemma wp_pure_step_later `{!Inhabited (state Λ)} ψ n e1 e2 E Φ :
    PureExec ψ n e1 e2 →
    ψ →
    ▷^n (
      £ n -∗
      WP e2 @ E {{ Φ }}
    ) ⊢
    WP e1 @ E {{ Φ }}.
  Proof.
    intros Hexec Hψ.
    rewrite -wp_pure_step // {Hexec}.
    enough (∀ P, ▷^n P ⊢ |={E}▷=>^n P) as H by apply H.
    intros P. induction n as [| n IH]; rewrite //= -step_fupd_intro // IH //.
  Qed.
End language.

Section ectx_language.
  Context {Λ : ectx_language} `{iris_G : !IrisG Λ Σ}.

  Implicit Types e : expr Λ.
  Implicit Types Φ : val Λ → iProp Σ.

  #[local] Hint Resolve
    base_prim_reducible
    base_reducible_prim_step
  : core.

  Lemma wp_lift_base_step e E Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E, ∅}=>
        ⌜base_reducible e σ⌝ ∗
          ∀ e' σ' es,
          ⌜base_step e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={∅}=> ▷ |={∅, E}=>
            state_interp (nt + length es) σ' κs ∗
            wp e' E Φ ∗
            [∗ list] i ↦ e ∈ es,
              wp e ⊤ fork_post
    ) ⊢
    WP e @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply wp_lift_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%e' %σ' %es %Hstep".
    iApply ("H" with "[%]").
    naive_solver.
  Qed.
  Lemma wp_lift_base_step_nofork e E Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E, ∅}=>
        ⌜base_reducible e σ⌝ ∗
          ∀ e' σ' es,
          ⌜base_step e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={∅}=> ▷ |={∅, E}=>
            ⌜es = []⌝ ∗
            state_interp nt σ' κs ∗
            wp e' E Φ
    ) ⊢
    WP e @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply wp_lift_base_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e' %σ' %es %Hstep H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hσ & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma wp_lift_atomic_base_step e E1 E2 Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E1}=>
        ⌜base_reducible e σ⌝ ∗
        ∀ e' σ' es,
        ⌜base_step e σ κ e' σ' es⌝ -∗
        £ 1 -∗
          |={E1}[E2]▷=>
          state_interp (nt + length es) σ' κs ∗
          from_option Φ False (to_val e') ∗
          [∗ list] e ∈ es,
            WP e @ ⊤ {{ fork_post }}
    ) ⊢
    WP e @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply wp_lift_atomic_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%e' %σ' %es %Hstep".
    iApply ("H" with "[%]").
    naive_solver.
  Qed.
  Lemma wp_lift_atomic_base_step_nofork e E1 E2 Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E1}=>
        ⌜base_reducible e σ⌝ ∗
          ∀ e' σ' es,
          ⌜base_step e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={E1}[E2]▷=>
            ⌜es = []⌝ ∗
            state_interp nt σ' κs ∗
            from_option Φ False (to_val e')
    ) ⊢
    WP e @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply wp_lift_atomic_base_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e' %σ' %es %Hstep H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hσ & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma wp_lift_pure_base_step_nofork `{!Inhabited (state Λ)} e E1 E2 Φ :
    ( ∀ σ,
      base_reducible e σ
    ) →
    ( ∀ σ κ e' σ' es,
      base_step e σ κ e' σ' es →
        κ = [] ∧
        σ' = σ ∧
        es = []
    ) →
    ( |={E1}[E2]▷=>
      ∀ σ e' κ es,
      ⌜base_step e σ κ e' σ es⌝ -∗
      £ 1 -∗
      WP e' @ E1 {{ Φ }}
    ) ⊢
    WP e @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H".
    iApply wp_lift_pure_step_nofork; [eauto.. |].
    iMod "H" as "H".
    iIntros "!> !>".
    iMod "H".
    iIntros "!> %σ %e' %κ %es %Hstep H£".
    iApply ("H" with "[%] H£"); first eauto.
  Qed.

  Lemma wp_lift_pure_det_base_step_nofork `{!Inhabited (state Λ)} e1 e2 E1 E2 Φ :
    ( ∀ σ1,
      base_reducible e1 σ1
    ) →
    ( ∀ σ1 κ e2' σ2 es,
      base_step e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = []
    ) →
    ( |={E1}[E2]▷=>
      £ 1 -∗
      WP e2 @ E1 {{ Φ }}
    ) ⊢
    WP e1 @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H".
    iApply wp_lift_pure_det_step_nofork; [eauto.. |].
    iSteps.
  Qed.
End ectx_language.
