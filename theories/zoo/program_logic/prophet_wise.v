From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.agree
  lib.mono_list.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  prophet_typed.
From zoo.diaframe Require Import
  diaframe.
From zoo Require Import
  options.

Class ProphetWiseStrongG Σ `{zoo_G : !ZooG Σ} prophet :=
  { #[local] prophet_wise_strong_G_full_G :: AgreeG Σ (leibnizO (list prophet.(prophet_typed_strong_type)))
  ; #[local] prophet_wise_strong_G_past_G :: MonoListG Σ prophet.(prophet_typed_strong_type)
  }.

Definition prophet_wise_strong_Σ prophet :=
  #[agree_Σ (leibnizO (list prophet.(prophet_typed_strong_type)))
  ; mono_list_Σ prophet.(prophet_typed_strong_type)
  ].
#[global] Instance subG_prophet_wise_strong_Σ Σ `{zoo_G : !ZooG Σ} prophet :
  subG (prophet_wise_strong_Σ prophet) Σ →
  ProphetWiseStrongG Σ prophet.
Proof.
  solve_inG.
Qed.

Section prophet_wise_strong_G.
  Context (prophet : prophet_typed_strong).
  Context `{prophet_wise_strong_G : ProphetWiseStrongG Σ prophet}.

  Implicit Types proph : prophet.(prophet_typed_strong_type).
  Implicit Types prophs : list prophet.(prophet_typed_strong_type).

  Record prophet_wise_strong_name :=
    { prophet_wise_strong_name_full : gname
    ; prophet_wise_strong_name_past : gname
    }.

  #[global] Instance prophet_wise_strong_name_eq_dec : EqDecision prophet_wise_strong_name :=
    ltac:(solve_decision).
  #[global] Instance prophet_wise_strong_name_countable :
    Countable prophet_wise_strong_name.
  Proof.
    solve_countable.
  Qed.

  Definition prophet_wise_strong_full γ prophs :=
    agree_on γ.(prophet_wise_strong_name_full) prophs.
  #[local] Instance : CustomIpat "full" :=
    " #Hfull{}
    ".

  Definition prophet_wise_strong_model pid γ past prophs : iProp Σ :=
    prophet_wise_strong_full γ (past ++ prophs) ∗
    mono_list_auth γ.(prophet_wise_strong_name_past) (DfracOwn 1) past ∗
    prophet_typed_strong_model prophet pid prophs.
  #[local] Instance : CustomIpat "model" :=
    " ( #Hfull{}
      & Hpast{}_auth
      & Hmodel{}
      )
    ".

  Definition prophet_wise_strong_snapshot γ past prophs : iProp Σ :=
    prophet_wise_strong_full γ (past ++ prophs) ∗
    mono_list_lb γ.(prophet_wise_strong_name_past) past.
  #[local] Instance : CustomIpat "snapshot" :=
    " ( #Hfull{suff}
      & #Hpast_lb
      )
    ".

  Definition prophet_wise_strong_lb γ lb : iProp Σ :=
    ∃ past,
    prophet_wise_strong_snapshot γ past lb.
  #[local] Instance : CustomIpat "lb" :=
    " ( %past{suff}
      & Hsnapshot
      )
    ".

  #[global] Instance prophet_wise_strong_full_timeless γ prophs :
    Timeless (prophet_wise_strong_full γ prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_strong_model_timeless pid γ past prophs :
    Timeless (prophet_wise_strong_model pid γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_strong_snapshot_timeless γ past prophs :
    Timeless (prophet_wise_strong_snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_strong_lb_timeless γ lb :
    Timeless (prophet_wise_strong_lb γ lb).
  Proof.
    apply _.
  Qed.

  #[global] Instance prophet_wise_strong_full_persistent γ prophs :
    Persistent (prophet_wise_strong_full γ prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_strong_snapshot_persistent γ past prophs :
    Persistent (prophet_wise_strong_snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_strong_lb_persistent γ lb :
    Persistent (prophet_wise_strong_lb γ lb).
  Proof.
    apply _.
  Qed.

  Lemma prophet_wise_strong_model_exclusive pid γ1 past1 prophs1 γ2 past2 prophs2 :
    prophet_wise_strong_model pid γ1 past1 prophs1 -∗
    prophet_wise_strong_model pid γ2 past2 prophs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_typed_strong_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_wise_strong_full_get pid γ past prophs :
    prophet_wise_strong_model pid γ past prophs ⊢
    prophet_wise_strong_full γ (past ++ prophs).
  Proof.
    iSteps.
  Qed.
  Lemma prophet_wise_strong_full_get' pid γ past prophs :
    prophet_wise_strong_model pid γ past prophs ⊢
      ∃ prophs',
      prophet_wise_strong_full γ prophs'.
  Proof.
    rewrite prophet_wise_strong_full_get. iSteps.
  Qed.
  Lemma prophet_wise_strong_full_valid pid γ past prophs1 prophs2 :
    prophet_wise_strong_model pid γ past prophs1 -∗
    prophet_wise_strong_full γ prophs2 -∗
    ⌜prophs2 = past ++ prophs1⌝.
  Proof.
    iIntros "(:model =1) (:full =2)".
    iDestruct (agree_on_agree_L with "Hfull1 Hfull2") as %<-.
    iSteps.
  Qed.
  Lemma prophet_wise_strong_full_agree γ prophs1 prophs2 :
    prophet_wise_strong_full γ prophs1 -∗
    prophet_wise_strong_full γ prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    apply: agree_on_agree_L.
  Qed.

  Lemma prophet_wise_strong_snapshot_get pid γ past prophs :
    prophet_wise_strong_model pid γ past prophs ⊢
    prophet_wise_strong_snapshot γ past prophs.
  Proof.
    iIntros "(:model)".
    iStep.
    iApply (mono_list_lb_get with "Hpast_auth").
  Qed.
  Lemma prophet_wise_strong_snapshot_valid pid γ past1 prophs1 past2 prophs2 :
    prophet_wise_strong_model pid γ past1 prophs1 -∗
    prophet_wise_strong_snapshot γ past2 prophs2 -∗
      ∃ past3,
      ⌜past1 = past2 ++ past3⌝ ∗
      ⌜prophs2 = past3 ++ prophs1⌝.
  Proof.
    iIntros "(:model) (:snapshot suff=')".
    iDestruct (agree_on_agree_L with "Hfull Hfull'") as %Hfull.
    iDestruct (mono_list_lb_valid with "Hpast_auth Hpast_lb") as %(past3 & ->).
    iPureIntro. rewrite -assoc in Hfull. naive_solver.
  Qed.

  Lemma prophet_wise_strong_lb_get pid γ past prophs :
    prophet_wise_strong_model pid γ past prophs ⊢
    prophet_wise_strong_lb γ prophs.
  Proof.
    rewrite prophet_wise_strong_snapshot_get.
    iSteps.
  Qed.
  Lemma prophet_wise_strong_lb_valid pid γ past prophs lb :
    prophet_wise_strong_model pid γ past prophs -∗
    prophet_wise_strong_lb γ lb -∗
      ∃ past1 past2,
      ⌜past = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophs⌝.
  Proof.
    iIntros "Hmodel (:lb suff=')".
    iExists past'.
    iApply (prophet_wise_strong_snapshot_valid with "Hmodel Hsnapshot").
  Qed.

  Lemma prophet_wise_strong_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{
      pid γ prophs
    , RET #pid;
      prophet_wise_strong_model pid γ [] prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd. wp_apply (prophet_typed_strong_wp_proph with "[//]") as "%pid %prophs Hpid".
    iMod (agree_alloc (agree_G := prophet_wise_strong_G_full_G) prophs) as "(%γ_full & #Hfull)".
    iMod (mono_list_alloc []) as "(%γ_past & Hpast_auth)".
    set γ :=
      {|prophet_wise_strong_name_full := γ_full
      ; prophet_wise_strong_name_past := γ_past
      |}.
    iApply ("HΦ" $! pid γ).
    iSteps.
  Qed.

  Lemma prophet_wise_strong_wp_resolve e pid v γ past prophs E Φ :
    Atomic e →
    to_val e = None →
    prophet_wise_strong_model pid γ past prophs -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜prophet.(prophet_typed_strong_of_val) w v = Some proph⌝ ∗
        ∀ prophs',
        ⌜prophs = proph :: prophs'⌝ -∗
        prophet_wise_strong_model pid γ (past ++ [proph]) prophs' -∗
        Φ w
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros "% % (:model) HΦ".
    wp_apply (prophet_typed_strong_wp_resolve with "Hmodel"); first done.
    iApply wp_fupd. wp_apply (wp_wand with "HΦ") as "%w (%proph & % & HΦ)".
    iExists proph. iSplitR; first done.
    iMod (mono_list_update_snoc proph with "Hpast_auth") as "Hpast_auth".
    iIntros "!> %prophs' -> Hpid".
    iApply ("HΦ" with "[//]").
    rewrite (assoc _ _ [_]). iSteps.
  Qed.
End prophet_wise_strong_G.

#[global] Opaque prophet_wise_strong_full.
#[global] Opaque prophet_wise_strong_model.
#[global] Opaque prophet_wise_strong_snapshot.
#[global] Opaque prophet_wise_strong_lb.

Class ProphetWiseG Σ `{zoo_G : !ZooG Σ} prophet :=
  { #[local] prophet_wise_G :: ProphetWiseStrongG Σ prophet
  }.

Definition prophet_wise_Σ prophet :=
  #[prophet_wise_strong_Σ prophet
  ].
#[global] Instance subG_prophet_wise_Σ Σ `{zoo_G : !ZooG Σ} prophet :
  subG (prophet_wise_Σ prophet) Σ →
  ProphetWiseG Σ prophet.
Proof.
  solve_inG.
Qed.

Section prophet_wise_G.
  Context (prophet : prophet_typed).
  Context `{prophet_wise_G : ProphetWiseG Σ prophet}.

  Implicit Types proph : prophet.(prophet_typed_type).
  Implicit Types past prophs lb : list prophet.(prophet_typed_type).

  Definition prophet_wise_name :=
    prophet_wise_strong_name.
  Implicit Types γ : prophet_wise_name.

  Definition prophet_wise_full γ prophs :=
    prophet_wise_strong_full prophet γ prophs.

  Definition prophet_wise_model pid γ past prophs :=
    prophet_wise_strong_model prophet pid γ past prophs.

  Definition prophet_wise_snapshot γ past prophs :=
    prophet_wise_strong_snapshot prophet γ past prophs.

  Definition prophet_wise_lb γ lb :=
    prophet_wise_strong_lb prophet γ lb.
  #[local] Instance : CustomIpat "lb" :=
    " ( %slb
      & ->
      & Hlb
      )
    ".

  #[global] Instance prophet_wise_full_timeless γ prophs :
    Timeless (prophet_wise_full γ prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_model_timeless pid γ past prophs :
    Timeless (prophet_wise_model pid γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_snapshot_timeless γ past prophs :
    Timeless (prophet_wise_snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_lb_timeless γ lb :
    Timeless (prophet_wise_lb γ lb).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_full_persistent γ prophs :
    Persistent (prophet_wise_full γ prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_snapshot_persistent γ past prophs :
    Persistent (prophet_wise_snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise_lb_persistent γ lb :
    Persistent (prophet_wise_lb γ lb).
  Proof.
    apply _.
  Qed.

  Lemma prophet_wise_model_exclusive pid γ1 past1 prophs1 γ2 past2 prophs2 :
    prophet_wise_model pid γ1 past1 prophs1 -∗
    prophet_wise_model pid γ2 past2 prophs2 -∗
    False.
  Proof.
    apply prophet_wise_strong_model_exclusive.
  Qed.

  Lemma prophet_wise_full_get pid γ past prophs :
    prophet_wise_model pid γ past prophs ⊢
    prophet_wise_full γ (past ++ prophs).
  Proof.
    apply prophet_wise_strong_full_get.
  Qed.
  Lemma prophet_wise_full_get' pid γ past prophs :
    prophet_wise_model pid γ past prophs ⊢
      ∃ prophs',
      prophet_wise_full γ prophs'.
  Proof.
    rewrite prophet_wise_full_get. iSteps.
  Qed.
  Lemma prophet_wise_full_valid pid γ past prophs1 prophs2 :
    prophet_wise_model pid γ past prophs1 -∗
    prophet_wise_full γ prophs2 -∗
    ⌜prophs2 = past ++ prophs1⌝.
  Proof.
    apply prophet_wise_strong_full_valid.
  Qed.
  Lemma prophet_wise_full_agree γ prophs1 prophs2 :
    prophet_wise_full γ prophs1 -∗
    prophet_wise_full γ prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    apply prophet_wise_strong_full_agree.
  Qed.

  Lemma prophet_wise_snapshot_get pid γ past prophs :
    prophet_wise_model pid γ past prophs ⊢
    prophet_wise_snapshot γ past prophs.
  Proof.
    apply prophet_wise_strong_snapshot_get.
  Qed.
  Lemma prophet_wise_snapshot_valid pid γ past1 prophs1 past2 prophs2 :
    prophet_wise_model pid γ past1 prophs1 -∗
    prophet_wise_snapshot γ past2 prophs2 -∗
      ∃ past3,
      ⌜past1 = past2 ++ past3⌝ ∗
      ⌜prophs2 = past3 ++ prophs1⌝.
  Proof.
    apply prophet_wise_strong_snapshot_valid.
  Qed.

  Lemma prophet_wise_lb_get pid γ past prophs :
    prophet_wise_model pid γ past prophs -∗
    prophet_wise_lb γ prophs.
  Proof.
    iApply prophet_wise_strong_lb_get.
  Qed.
  Lemma prophet_wise_lb_valid pid γ past prophs lb :
    prophet_wise_model pid γ past prophs -∗
    prophet_wise_lb γ lb -∗
      ∃ past1 past2,
      ⌜past = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophs⌝.
  Proof.
    apply prophet_wise_strong_lb_valid.
  Qed.

  Lemma prophet_wise_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{
      pid γ prophs
    , RET #pid;
      prophet_wise_model pid γ [] prophs
    }}}.
  Proof.
    apply: prophet_wise_strong_wp_proph.
  Qed.

  Lemma prophet_wise_wp_resolve proph e pid v γ past prophs E Φ :
    Atomic e →
    to_val e = None →
    prophet.(prophet_typed_of_val) v = Some proph →
    prophet_wise_model pid γ past prophs -∗
    WP e @ E {{ w,
      ∀ prophs',
      ⌜prophs = proph :: prophs'⌝ -∗
      prophet_wise_model pid γ (past ++ [proph]) prophs' -∗
      Φ w
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros (? ? Hproph) "Hmodel HΦ".
    wp_apply (prophet_wise_strong_wp_resolve with "Hmodel"); first done.
    iSteps.
  Qed.
End prophet_wise_G.

#[global] Opaque prophet_wise_name.
#[global] Opaque prophet_wise_full.
#[global] Opaque prophet_wise_model.
#[global] Opaque prophet_wise_snapshot.
#[global] Opaque prophet_wise_lb.
