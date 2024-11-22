From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.agree
  lib.mono_list.
From zoo.language Require Export
  typed_prophet.
From zoo.language Require Import
  notations
  diaframe.

Class WiseStrongProphetG Σ `{zoo_G : !ZooG Σ} prophet := {
  #[local] wise_strong_prophet_G_full_G :: AgreeG Σ (leibnizO (list prophet.(typed_strong_prophet_type))) ;
  #[local] wise_strong_prophet_G_past_G :: MonoListG Σ prophet.(typed_strong_prophet_type) ;
}.

Definition wise_strong_prophet_Σ prophet := #[
  agree_Σ (leibnizO (list prophet.(typed_strong_prophet_type))) ;
  mono_list_Σ prophet.(typed_strong_prophet_type)
].
#[global] Instance subG_wise_strong_prophet_Σ Σ `{zoo_G : !ZooG Σ} prophet :
  subG (wise_strong_prophet_Σ prophet) Σ →
  WiseStrongProphetG Σ prophet.
Proof.
  solve_inG.
Qed.

Section typed_strong_prophet.
  Context (prophet : typed_strong_prophet).
  Context `{wise_prophet_G : WiseStrongProphetG Σ prophet}.

  Record wise_strong_prophet_name := {
    wise_strong_prophet_name_full : gname ;
    wise_strong_prophet_name_past : gname ;
  }.

  #[global] Instance wise_strong_prophet_name_eq_dec : EqDecision wise_strong_prophet_name :=
    ltac:(solve_decision).
  #[global] Instance wise_strong_prophet_name_countable :
    Countable wise_strong_prophet_name.
  Proof.
    pose encode γ := (
      γ.(wise_strong_prophet_name_full),
      γ.(wise_strong_prophet_name_past)
    ).
    pose decode := λ '(γ_full, γ_past), {|
      wise_strong_prophet_name_full := γ_full ;
      wise_strong_prophet_name_past := γ_past ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  Definition wise_strong_prophet_model pid γ past prophs : iProp Σ :=
    agree_on γ.(wise_strong_prophet_name_full) (past ++ prophs) ∗
    mono_list_auth γ.(wise_strong_prophet_name_past) (DfracOwn 1) past ∗
    typed_strong_prophet_model prophet pid prophs.

  Definition wise_strong_prophet_snapshot γ past prophs : iProp Σ :=
    agree_on γ.(wise_strong_prophet_name_full) (past ++ prophs) ∗
    mono_list_lb γ.(wise_strong_prophet_name_past) past.

  Definition wise_strong_prophet_lb γ lb : iProp Σ :=
    ∃ past,
    wise_strong_prophet_snapshot γ past lb.

  #[global] Instance wise_strong_prophet_model_timeless pid γ past prophs :
    Timeless (wise_strong_prophet_model pid γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophet_snapshot_timeless γ past prophs :
    Timeless (wise_strong_prophet_snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophet_lb_timeless γ lb :
    Timeless (wise_strong_prophet_lb γ lb).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophet_snapshot_persistent γ past prophs :
    Persistent (wise_strong_prophet_snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophet_lb_persistent γ lb :
    Persistent (wise_strong_prophet_lb γ lb).
  Proof.
    apply _.
  Qed.

  Lemma wise_strong_prophet_model_exclusive pid γ1 past1 prophs1 γ2 past2 prophs2 :
    wise_strong_prophet_model pid γ1 past1 prophs1 -∗
    wise_strong_prophet_model pid γ2 past2 prophs2 -∗
    False.
  Proof.
    iIntros "(_ & _ & Hmodel1) (_ & _ & Hmodel2)".
    iApply (typed_strong_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma wise_strong_prophet_snapshot_get pid γ past prophs :
    wise_strong_prophet_model pid γ past prophs ⊢
    wise_strong_prophet_snapshot γ past prophs.
  Proof.
    iIntros "(#Hfull & Hpast_auth & Hmodel)".
    iStep.
    iApply (mono_list_lb_get with "Hpast_auth").
  Qed.
  Lemma wise_strong_prophet_snapshot_valid pid γ past prophs past' prophs' :
    wise_strong_prophet_model pid γ past prophs -∗
    wise_strong_prophet_snapshot γ past' prophs' -∗
      ∃ past'',
      ⌜past = past' ++ past''⌝ ∗
      ⌜prophs' = past'' ++ prophs⌝.
  Proof.
    iIntros "(#Hfull & Hpast_auth & Hmodel) (#Hfull' & #Hpast_lb)".
    iDestruct (agree_on_agree_L with "Hfull Hfull'") as %Hfull.
    iDestruct (mono_list_lb_valid with "Hpast_auth Hpast_lb") as %(past2 & ->).
    iPureIntro. rewrite -assoc in Hfull. naive_solver.
  Qed.

  Lemma wise_strong_prophet_lb_get pid γ past prophs :
    wise_strong_prophet_model pid γ past prophs ⊢
    wise_strong_prophet_lb γ prophs.
  Proof.
    rewrite wise_strong_prophet_snapshot_get.
    iSteps.
  Qed.
  Lemma wise_strong_prophet_lb_valid pid γ past prophs lb :
    wise_strong_prophet_model pid γ past prophs -∗
    wise_strong_prophet_lb γ lb -∗
      ∃ past1 past2,
      ⌜past = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophs⌝.
  Proof.
    iIntros "Hmodel (%past' & Hsnapshot)".
    iExists past'.
    iApply (wise_strong_prophet_snapshot_valid with "Hmodel Hsnapshot").
  Qed.

  Lemma wise_strong_prophet_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid γ prophs,
      RET #pid;
      wise_strong_prophet_model pid γ [] prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd. wp_apply (typed_strong_prophet_wp_proph with "[//]") as "%pid %prophs Hpid".
    iMod (agree_alloc (agree_G := wise_strong_prophet_G_full_G) prophs) as "(%γ_full & #Hfull)".
    iMod (mono_list_alloc []) as "(%γ_past & Hpast_auth)".
    set γ := {|
      wise_strong_prophet_name_full := γ_full ;
      wise_strong_prophet_name_past := γ_past ;
    |}.
    iApply ("HΦ" $! pid γ).
    iSteps.
  Qed.

  Lemma wise_strong_prophet_wp_resolve e v E pid γ past prophs Φ :
    Atomic e →
    to_val e = None →
    wise_strong_prophet_model pid γ past prophs -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = prophet.(typed_strong_prophet_to_val) proph⌝ ∗
        ∀ prophs',
        ⌜prophs = proph :: prophs'⌝ -∗
        wise_strong_prophet_model pid γ (past ++ [proph]) prophs' -∗
        Φ w
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros "% % (#Hfull & Hpast_auth & Hmodel) HΦ".
    wp_apply (typed_strong_prophet_wp_resolve with "Hmodel"); first done.
    iApply wp_fupd. wp_apply (wp_wand with "HΦ") as "%w HΦ".
    iDestruct "HΦ" as "(%proph & % & HΦ)".
    iExists proph. iSplitR; first done.
    iMod (mono_list_update_app [proph] with "Hpast_auth") as "Hpast_auth".
    iIntros "!> %prophs' -> Hpid".
    iApply ("HΦ" with "[//]").
    rewrite (assoc _ _ [_]). iSteps.
  Qed.
End typed_strong_prophet.

#[global] Opaque wise_strong_prophet_model.
#[global] Opaque wise_strong_prophet_snapshot.
#[global] Opaque wise_strong_prophet_lb.

Class WiseProphetG Σ `{zoo_G : !ZooG Σ} prophet := {
  #[local] wise_prophet_G_full_G :: AgreeG Σ (leibnizO (list (val * prophet.(typed_prophet_type)))) ;
  #[local] wise_prophet_G_past_G :: MonoListG Σ (val * prophet.(typed_prophet_type)) ;
}.

Definition wise_prophet_Σ prophet := #[
  agree_Σ (leibnizO (list (val * prophet.(typed_prophet_type)))) ;
  mono_list_Σ (val * prophet.(typed_prophet_type))
].
#[global] Instance subG_wise_prophet_Σ Σ `{zoo_G : !ZooG Σ} prophet :
  subG (wise_prophet_Σ prophet) Σ →
  WiseProphetG Σ prophet.
Proof.
  solve_inG.
Qed.

Section typed_prophet.
  Context (prophet : typed_prophet).
  Context `{wise_prophet_G : WiseProphetG Σ prophet}.

  Definition wise_prophet_name :=
    wise_strong_prophet_name.
  Implicit Types γ : wise_prophet_name.

  #[local] Instance wise_prophet_strong_prophet_G :
    WiseStrongProphetG Σ prophet.
  Proof.
    split; apply _.
  Qed.

  Definition wise_prophet_model pid γ past prophs : iProp Σ :=
    ∃ spast sprophs,
    ⌜past = spast.*2⌝ ∗
    ⌜prophs = sprophs.*2⌝ ∗
    wise_strong_prophet_model prophet pid γ spast sprophs.

  Definition wise_prophet_snapshot γ past prophs : iProp Σ :=
    ∃ spast sprophs,
    ⌜past = spast.*2⌝ ∗
    ⌜prophs = sprophs.*2⌝ ∗
    wise_strong_prophet_snapshot prophet γ spast sprophs.

  Definition wise_prophet_lb γ lb : iProp Σ :=
    ∃ slb,
    ⌜lb = slb.*2⌝ ∗
    wise_strong_prophet_lb prophet γ slb.

  #[global] Instance wise_prophet_model_timeless pid γ past prophs :
    Timeless (wise_prophet_model pid γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophet_snapshot_timeless γ past prophs :
    Timeless (wise_prophet_snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophet_lb_timeless γ lb :
    Timeless (wise_prophet_lb γ lb).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophet_snapshot_persistent γ past prophs :
    Persistent (wise_prophet_snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophet_lb_persistent γ lb :
    Persistent (wise_prophet_lb γ lb).
  Proof.
    apply _.
  Qed.

  Lemma wise_prophet_model_exclusive pid γ1 past1 prophs1 γ2 past2 prophs2 :
    wise_prophet_model pid γ1 past1 prophs1 -∗
    wise_prophet_model pid γ2 past2 prophs2 -∗
    False.
  Proof.
    iIntros "(%spast1 & %sprophs1 & _ & _ & Hmodel1) (%spast2 & %sprophs2 & _ & _ & Hmodel2)".
    iApply (wise_strong_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma wise_prophet_snapshot_get pid γ past prophs :
    wise_prophet_model pid γ past prophs ⊢
    wise_prophet_snapshot γ past prophs.
  Proof.
    iIntros "(%spast & %sprophs & -> & -> & Hmodel)".
    iSteps.
    iApply (wise_strong_prophet_snapshot_get with "Hmodel").
  Qed.
  Lemma wise_prophet_snapshot_valid pid γ past prophs past' prophs' :
    wise_prophet_model pid γ past prophs -∗
    wise_prophet_snapshot γ past' prophs' -∗
      ∃ past'',
      ⌜past = past' ++ past''⌝ ∗
      ⌜prophs' = past'' ++ prophs⌝.
  Proof.
    iIntros "(%spast & %sprophs & -> & -> & Hmodel) (%spast' & %sprophs' & -> & -> & Hsnapshot)".
    iDestruct (wise_strong_prophet_snapshot_valid with "Hmodel Hsnapshot") as "(%spast'' & -> & ->)".
    list_simplifier. iSteps.
  Qed.

  Lemma wise_prophet_lb_get pid γ past prophs :
    wise_prophet_model pid γ past prophs -∗
    wise_prophet_lb γ prophs.
  Proof.
    iIntros "(%spast & %sprophs & -> & -> & Hmodel)".
    iStep.
    iApply (wise_strong_prophet_lb_get with "Hmodel").
  Qed.
  Lemma wise_prophet_lb_valid pid γ past prophs lb :
    wise_prophet_model pid γ past prophs -∗
    wise_prophet_lb γ lb -∗
      ∃ past1 past2,
      ⌜past = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophs⌝.
  Proof.
    iIntros "(%spast & %sprophs & -> & -> & Hmodel) (%slb & -> & Hlb)".
    iDestruct (wise_strong_prophet_lb_valid with "Hmodel Hlb") as "(%spast1 & %spast2 & -> & ->)".
    list_simplifier. iSteps.
  Qed.

  Lemma wise_prophet_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid γ prophs,
      RET #pid;
      wise_prophet_model pid γ [] prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wise_strong_prophet_wp_proph prophet with "[//]") as "%pid %γ %sprophs Hmodel".
    iApply "HΦ".
    iExists [], sprophs. iSteps.
  Qed.

  Lemma wise_prophet_wp_resolve proph e v E pid γ past prophs Φ :
    Atomic e →
    to_val e = None →
    v = prophet.(typed_prophet_to_val) proph →
    wise_prophet_model pid γ past prophs -∗
    WP e @ E {{ w,
      ∀ prophs',
      ⌜prophs = proph :: prophs'⌝ -∗
      wise_prophet_model pid γ (past ++ [proph]) prophs' -∗
      Φ w
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros (? ? ->) "(%spast & %sprophs & -> & -> & Hmodel) HΦ".
    wp_apply (wise_strong_prophet_wp_resolve with "Hmodel"); first done.
    wp_apply (wp_wand with "HΦ") as "%w HΦ".
    iExists (w, proph). iSplit; first iSteps. iIntros "%sprophs' -> Hmodel".
    iApply ("HΦ" with "[//]"). iExists (spast ++ [(w, proph)]), sprophs'. iFrame.
    list_simplifier. iSteps.
  Qed.
End typed_prophet.

#[global] Opaque wise_prophet_model.
#[global] Opaque wise_prophet_snapshot.
#[global] Opaque wise_prophet_lb.
