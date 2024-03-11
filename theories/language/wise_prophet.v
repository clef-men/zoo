From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  lib.agree
  lib.mono_list.
From zebre.language Require Export
  typed_prophet.
From zebre.language Require Import
  notations
  diaframe.

Record wise_strong_prophet `{zebre_G : !ZebreG Σ} := {
  wise_strong_prophet_type : Type ;
  wise_strong_prophet_to_val : wise_strong_prophet_type → val * val ;

  wise_strong_prophet_name : Type ;
  #[global] wise_strong_prophet_name_eq_dec ::
    EqDecision wise_strong_prophet_name ;
  #[global] wise_strong_prophet_name_countable ::
    Countable wise_strong_prophet_name ;

  wise_strong_prophet_model : prophecy_id → wise_strong_prophet_name → list wise_strong_prophet_type → list wise_strong_prophet_type → iProp Σ ;
  wise_strong_prophet_lb : wise_strong_prophet_name → list wise_strong_prophet_type → iProp Σ ;

  #[global] wise_strong_prophet_model_timeless p γ past prophs ::
    Timeless (wise_strong_prophet_model p γ past prophs) ;
  #[global] wise_strong_prophet_lb_timeless γ lb ::
    Timeless (wise_strong_prophet_lb γ lb) ;
  #[global] wise_strong_prophet_lb_persistent γ lb ::
    Persistent (wise_strong_prophet_lb γ lb) ;

  wise_strong_prophet_model_exclusive p γ1 past1 prophs1 γ2 past2 prophs2 :
    wise_strong_prophet_model p γ1 past1 prophs1 -∗
    wise_strong_prophet_model p γ2 past2 prophs2 -∗
    False ;

  wise_strong_prophet_lb_get p γ past prophs :
    wise_strong_prophet_model p γ past prophs -∗
    wise_strong_prophet_lb γ prophs ;
  wise_strong_prophet_model_lb_valid p γ past prophs lb :
    wise_strong_prophet_model p γ past prophs -∗
    wise_strong_prophet_lb γ lb -∗
    ⌜∃ past1 past2, past = past1 ++ past2 ∧ lb = past2 ++ prophs⌝ ;

  wise_strong_prophet_wp_proph E :
    {{{ True }}}
      Proph @ E
    {{{ p γ prophs,
      RET #p;
      wise_strong_prophet_model p γ [] prophs
    }}} ;

  wise_strong_prophet_wp_resolve e v E p γ past prophs Φ :
    Atomic StronglyAtomic e →
    to_val e = None →
    wise_strong_prophet_model p γ past prophs -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = wise_strong_prophet_to_val proph⌝ ∗
        ∀ prophs',
        ⌜prophs = proph :: prophs'⌝ -∗
        wise_strong_prophet_model p γ (past ++ [proph]) prophs' -∗
        Φ w
    }} -∗
    WP Resolve e #p v @ E {{ Φ }} ;
}.
#[global] Arguments wise_strong_prophet _ {_} : assert.
#[global] Arguments Build_wise_strong_prophet {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ : assert.
#[global] Opaque wise_strong_prophet_model.
#[global] Opaque wise_strong_prophet_lb.

Class WiseStrongProphetG Σ `{zebre_G : !ZebreG Σ} spec := {
  #[local] wise_strong_prophet_G_full_G :: AgreeG Σ (leibnizO (list spec.(typed_strong_prophet_spec_type))) ;
  #[local] wise_strong_prophet_G_past_G :: MonoListG Σ spec.(typed_strong_prophet_spec_type) ;
}.

Definition wise_strong_prophet_Σ spec := #[
  agree_Σ (leibnizO (list spec.(typed_strong_prophet_spec_type))) ;
  mono_list_Σ spec.(typed_strong_prophet_spec_type)
].
#[global] Instance subG_wise_strong_prophet_Σ Σ `{zebre_G : !ZebreG Σ} spec :
  subG (wise_strong_prophet_Σ spec) Σ →
  WiseStrongProphetG Σ spec.
Proof.
  solve_inG.
Qed.

Section make_wise_prophet_G.
  Context `{zebre_G : !ZebreG Σ} spec `{wise_prophet_G : !WiseStrongProphetG Σ spec}.

  Definition make_wise_strong_prophet_typed_prophet :=
    make_typed_strong_prophet spec.

  Record make_wise_strong_prophet_name := {
    make_wise_strong_prophet_name_full : gname ;
    make_wise_strong_prophet_name_past : gname ;
  }.
  #[local] Instance make_wise_strong_prophet_name_eq_dec : EqDecision make_wise_strong_prophet_name :=
    ltac:(solve_decision).
  #[local] Instance make_wise_strong_prophet_name_countable :
    Countable make_wise_strong_prophet_name.
  Proof.
    pose encode γ := (
      γ.(make_wise_strong_prophet_name_full),
      γ.(make_wise_strong_prophet_name_past)
    ).
    pose decode := λ '(γ_full, γ_past), {|
      make_wise_strong_prophet_name_full := γ_full ;
      make_wise_strong_prophet_name_past := γ_past ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  Program Definition make_wise_strong_prophet := {|
    wise_strong_prophet_type :=
      spec.(typed_strong_prophet_spec_type) ;
    wise_strong_prophet_to_val :=
      spec.(typed_strong_prophet_spec_to_val) ;

    wise_strong_prophet_model p γ past prophs := (
      agree_on γ.(make_wise_strong_prophet_name_full) (past ++ prophs) ∗
      mono_list_auth γ.(make_wise_strong_prophet_name_past) (DfracOwn 1) past ∗
      make_wise_strong_prophet_typed_prophet.(typed_strong_prophet_model) p prophs
    )%I ;
    wise_strong_prophet_lb γ lb := (
      ∃ past_lb,
      agree_on γ.(make_wise_strong_prophet_name_full) (past_lb ++ lb) ∗
      mono_list_lb γ.(make_wise_strong_prophet_name_past) past_lb
    )%I ;
  |}.
  Next Obligation.
    iIntros "* (_ & _ & Hmodel1) (_ & _ & Hmodel2)".
    iApply (typed_strong_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.
  Next Obligation.
    iIntros "* (#Hfull & Hpast_auth & Hmodel)".
    iStep.
    iApply (mono_list_lb_get with "Hpast_auth").
  Qed.
  Next Obligation.
    iIntros "* (#Hfull & Hpast_auth & Hmodel) (%past1 & #Hfull' & #Hpast_lb)".
    iDestruct (agree_on_agree_L with "Hfull Hfull'") as %Hfull.
    iDestruct (mono_list_lb_valid with "Hpast_auth Hpast_lb") as %(past2 & ->).
    iPureIntro. rewrite -assoc in Hfull. naive_solver.
  Qed.
  Next Obligation.
    iIntros "* _ HΦ".
    iApply wp_fupd. wp_apply (make_wise_strong_prophet_typed_prophet.(typed_strong_prophet_wp_proph) with "[//]") as "%p %prophs Hp".
    iMod (agree_alloc (agree_G := wise_strong_prophet_G_full_G) prophs) as "(%γ_full & #Hfull)".
    iMod (mono_list_alloc []) as "(%γ_past & Hpast_auth)".
    set γ := {|
      make_wise_strong_prophet_name_full := γ_full ;
      make_wise_strong_prophet_name_past := γ_past ;
    |}.
    iApply ("HΦ" $! p γ).
    iSteps.
  Qed.
  Next Obligation.
    iIntros "* % % (#Hfull & Hpast_auth & Hmodel) HΦ".
    wp_apply (typed_strong_prophet_wp_resolve with "Hmodel"); first done.
    iApply wp_fupd. wp_apply (wp_wand with "HΦ") as "%w HΦ".
    iDestruct "HΦ" as "(%proph & % & HΦ)".
    iExists proph. iSplitR; first done.
    iMod (mono_list_update_app [proph] with "Hpast_auth") as "Hpast_auth".
    iIntros "!> %prophs' -> Hp".
    iApply ("HΦ" with "[//]").
    list_simplifier. iSteps.
  Qed.
End make_wise_prophet_G.

Record wise_prophet `{zebre_G : !ZebreG Σ} := {
  wise_prophet_type : Type ;
  wise_prophet_to_val : wise_prophet_type → val ;

  wise_prophet_name : Type ;
  #[global] wise_prophet_name_eq_dec ::
    EqDecision wise_prophet_name ;
  #[global] wise_prophet_name_countable ::
    Countable wise_prophet_name ;

  wise_prophet_model : prophecy_id → wise_prophet_name → list wise_prophet_type → list wise_prophet_type → iProp Σ ;
  wise_prophet_lb : wise_prophet_name → list wise_prophet_type → iProp Σ ;

  #[global] wise_prophet_model_timeless p γ past prophs ::
    Timeless (wise_prophet_model p γ past prophs) ;
  #[global] wise_prophet_lb_timeless γ lb ::
    Timeless (wise_prophet_lb γ lb) ;
  #[global] wise_prophet_lb_persistent γ lb ::
    Persistent (wise_prophet_lb γ lb) ;

  wise_prophet_model_exclusive p γ1 past1 prophs1 γ2 past2 prophs2 :
    wise_prophet_model p γ1 past1 prophs1 -∗
    wise_prophet_model p γ2 past2 prophs2 -∗
    False ;

  wise_prophet_lb_get p γ past prophs :
    wise_prophet_model p γ past prophs -∗
    wise_prophet_lb γ prophs ;
  wise_prophet_model_lb_valid p γ past prophs lb :
    wise_prophet_model p γ past prophs -∗
    wise_prophet_lb γ lb -∗
    ⌜∃ past1 past2, past = past1 ++ past2 ∧ lb = past2 ++ prophs⌝ ;

  wise_prophet_wp_proph E :
    {{{ True }}}
      Proph @ E
    {{{ p γ prophs,
      RET #p;
      wise_prophet_model p γ [] prophs
    }}} ;

  wise_prophet_wp_resolve proph e v E p γ past prophs Φ :
    Atomic StronglyAtomic e →
    to_val e = None →
    v = wise_prophet_to_val proph →
    wise_prophet_model p γ past prophs -∗
    WP e @ E {{ w,
      ∀ prophs',
      ⌜prophs = proph :: prophs'⌝ -∗
      wise_prophet_model p γ (past ++ [proph]) prophs' -∗
      Φ w
    }} -∗
    WP Resolve e #p v @ E {{ Φ }} ;
}.
#[global] Arguments wise_prophet _ {_} : assert.
#[global] Arguments Build_wise_prophet {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ : assert.
#[global] Opaque wise_prophet_model.
#[global] Opaque wise_prophet_lb.

Class WiseProphetG Σ `{zebre_G : !ZebreG Σ} spec := {
  #[local] wise_prophet_G_full_G :: AgreeG Σ (leibnizO (list (val * spec.(typed_prophet_spec_type)))) ;
  #[local] wise_prophet_G_past_G :: MonoListG Σ (val * spec.(typed_prophet_spec_type)) ;
}.

Definition wise_prophet_Σ spec := #[
  agree_Σ (leibnizO (list (val * spec.(typed_prophet_spec_type)))) ;
  mono_list_Σ (val * spec.(typed_prophet_spec_type))
].
#[global] Instance subG_wise_prophet_Σ Σ `{zebre_G : !ZebreG Σ} spec :
  subG (wise_prophet_Σ spec) Σ →
  WiseProphetG Σ spec.
Proof.
  solve_inG.
Qed.

Section make_wise_prophet.
  Context `{zebre_G : !ZebreG Σ} spec `{wise_prophet_G : !WiseProphetG Σ spec}.

  #[local] Program Definition make_wise_prophet_strong_prophet_spec := {|
    typed_strong_prophet_spec_type :=
      val * spec.(typed_prophet_spec_type) ;
    typed_strong_prophet_spec_of_val w v :=
      match spec.(typed_prophet_spec_of_val) v with
      | None => None
      | Some proph => Some (w, proph)
      end ;
    typed_strong_prophet_spec_to_val '(w, proph) :=
      (w, spec.(typed_prophet_spec_to_val) proph) ;
  |}.
  Next Obligation.
    intros (w & proph) _w v [= -> ->].
    erewrite spec.(typed_prophet_spec_of_to_val); done.
  Qed.

  #[local] Instance make_wise_prophet_strong_prophet_G :
    WiseStrongProphetG Σ make_wise_prophet_strong_prophet_spec.
  Proof.
    split; apply _.
  Qed.

  #[local] Definition make_wise_prophet_strong_prophet :=
    make_wise_strong_prophet make_wise_prophet_strong_prophet_spec.

  Program Definition make_wise_prophet := {|
    wise_prophet_type :=
      spec.(typed_prophet_spec_type) ;
    wise_prophet_to_val :=
      spec.(typed_prophet_spec_to_val) ;

    wise_prophet_model p γ past prophs := (
      ∃ spast sprophs,
      ⌜past = spast.*2⌝ ∗
      ⌜prophs = sprophs.*2⌝ ∗
      make_wise_prophet_strong_prophet.(wise_strong_prophet_model) p γ spast sprophs
    )%I ;
    wise_prophet_lb γ lb := (
      ∃ slb,
      ⌜lb = slb.*2⌝ ∗
      make_wise_prophet_strong_prophet.(wise_strong_prophet_lb) γ slb
    )%I ;
  |}.
  Next Obligation.
    iIntros "* (%spast1 & %sprophs1 & _ & _ & Hmodel1) (%spast2 & %sprophs2 & _ & _ & Hmodel2)".
    iApply (wise_strong_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.
  Next Obligation.
    iIntros "* (%spast & %sprophs & -> & -> & Hmodel)".
    iStep.
    iApply (wise_strong_prophet_lb_get with "Hmodel").
  Qed.
  Next Obligation.
    iIntros "* (%spast & %sprophs & -> & -> & Hmodel) (%slb & -> & Hlb)".
    iDestruct (wise_strong_prophet_model_lb_valid with "Hmodel Hlb") as "(%spast1 & %spast2 & -> & ->)".
    list_simplifier. iSteps.
  Qed.
  Next Obligation.
    iIntros "* _ HΦ".
    wp_apply (make_wise_prophet_strong_prophet.(wise_strong_prophet_wp_proph) with "[//]") as "%p %γ %sprophs Hmodel".
    iApply "HΦ". iExists [], sprophs.
    iSteps.
  Qed.
  Next Obligation.
    iIntros "*" (? ? ->) "(%spast & %sprophs & -> & -> & Hmodel) HΦ".
    wp_apply (wise_strong_prophet_wp_resolve with "Hmodel"); first done.
    wp_apply (wp_wand with "HΦ") as "%w HΦ".
    iExists (w, proph). iSplit; first iSteps. iIntros "%sprophs' -> Hmodel".
    iApply ("HΦ" with "[//]"). iExists (spast ++ [(w, proph)]), sprophs'. iFrame.
    list_simplifier. iSteps.
  Qed.
End make_wise_prophet.
