From zebra Require Import
  prelude.
From zebra.language Require Export
  rules.
From zebra.language Require Import
  notations
  diaframe.

Record typed_strong_prophet_spec := {
  typed_strong_prophet_spec_type : Type ;
  typed_strong_prophet_spec_of_val : val → val → option typed_strong_prophet_spec_type ;
  typed_strong_prophet_spec_to_val : typed_strong_prophet_spec_type → val * val ;

  typed_strong_prophet_spec_of_to_val proph w v :
    (w, v) = typed_strong_prophet_spec_to_val proph →
    typed_strong_prophet_spec_of_val w v = Some proph ;
}.
#[global] Arguments Build_typed_strong_prophet_spec {_ _ _} _ : assert.

Record typed_strong_prophet `{zebra_G : !ZebraG Σ} := {
  typed_strong_prophet_type : Type ;
  typed_strong_prophet_to_val : typed_strong_prophet_type → val * val ;

  typed_strong_prophet_model : prophecy_id → list typed_strong_prophet_type → iProp Σ ;

  #[global] typed_strong_prophet_model_timeless p prophs ::
    Timeless (typed_strong_prophet_model p prophs) ;

  typed_strong_prophet_model_exclusive p prophs1 prophs2 :
    typed_strong_prophet_model p prophs1 -∗
    typed_strong_prophet_model p prophs2 -∗
    False ;

  typed_strong_prophet_wp_proph E :
    {{{ True }}}
      Proph @ E
    {{{ p prophs, RET #p; typed_strong_prophet_model p prophs }}} ;

  typed_strong_prophet_wp_resolve e v E p prophs Φ :
    Atomic StronglyAtomic e →
    to_val e = None →
    typed_strong_prophet_model p prophs -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = typed_strong_prophet_to_val proph⌝ ∗
        ∀ prophs',
        ⌜prophs = proph :: prophs'⌝ -∗
        typed_strong_prophet_model p prophs' -∗
        Φ w
    }} -∗
    WP Resolve e #p v @ E {{ Φ }} ;
}.
#[global] Arguments typed_strong_prophet _ {_} : assert.
#[global] Arguments Build_typed_strong_prophet {_ _ _ _ _ _} _ _ _ : assert.
#[global] Opaque typed_strong_prophet_model.

Section make_typed_strong_prophet.
  Context `{zebra_G : !ZebraG Σ} (spec : typed_strong_prophet_spec).

  #[local] Fixpoint make_typed_strong_prophet_process prophs :=
    match prophs with
    | [] =>
        []
    | (w, v) :: prophs =>
        match spec.(typed_strong_prophet_spec_of_val) w v with
        | None =>
            []
        | Some proph =>
            proph :: make_typed_strong_prophet_process prophs
        end
    end.

  Program Definition make_typed_strong_prophet := {|
    typed_strong_prophet_type :=
      spec.(typed_strong_prophet_spec_type) ;
    typed_strong_prophet_to_val :=
      spec.(typed_strong_prophet_spec_to_val) ;

    typed_strong_prophet_model p prophs := (
      ∃ pvs,
      ⌜prophs = make_typed_strong_prophet_process pvs⌝ ∗
      proph p pvs
    )%I ;
  |}.
  Next Obligation.
    iSteps.
  Qed.
  Next Obligation.
    iIntros "* _ HΦ".
    wp_apply (wp_proph with "[//]").
    iSteps.
  Qed.
  Next Obligation.
    iIntros "* % % (%pvs & %Hprophs & Hp) HΦ".
    wp_apply (wp_resolve with "Hp"); first done.
    wp_apply (wp_wand with "HΦ") as "%w (%proph & % & HΦ) %pvs' -> Hp".
    rewrite /= (typed_strong_prophet_spec_of_to_val _ proph) // in Hprophs.
    iSteps.
  Qed.
End make_typed_strong_prophet.

Record typed_prophet_spec := {
  typed_prophet_spec_type : Type ;
  typed_prophet_spec_of_val : val → option typed_prophet_spec_type ;
  typed_prophet_spec_to_val : typed_prophet_spec_type → val ;

  typed_prophet_spec_of_to_val proph v :
    v = typed_prophet_spec_to_val proph →
    typed_prophet_spec_of_val v = Some proph ;
}.
#[global] Arguments Build_typed_prophet_spec {_ _ _} _ : assert.

Record typed_prophet `{zebra_G : !ZebraG Σ} := {
  typed_prophet_type : Type ;
  typed_prophet_to_val : typed_prophet_type → val ;

  typed_prophet_model : prophecy_id → list typed_prophet_type → iProp Σ ;

  #[global] typed_prophet_model_timeless p prophs ::
    Timeless (typed_prophet_model p prophs) ;

  typed_prophet_model_exclusive p prophs1 prophs2 :
    typed_prophet_model p prophs1 -∗
    typed_prophet_model p prophs2 -∗
    False ;

  typed_prophet_wp_proph E :
    {{{ True }}}
      Proph @ E
    {{{ p prophs, RET #p; typed_prophet_model p prophs }}} ;

  typed_prophet_wp_resolve proph e v E p prophs Φ :
    Atomic StronglyAtomic e →
    to_val e = None →
    v = typed_prophet_to_val proph →
    typed_prophet_model p prophs -∗
    WP e @ E {{ w,
      ∀ prophs',
      ⌜prophs = proph :: prophs'⌝ -∗
      typed_prophet_model p prophs' -∗
      Φ w
    }} -∗
    WP Resolve e #p v @ E {{ Φ }} ;
}.
#[global] Arguments typed_prophet _ {_} : assert.
#[global] Arguments Build_typed_prophet {_ _ _ _ _ _} _ _ _ : assert.
#[global] Opaque typed_prophet_model.

Section make_typed_prophet.
  Context `{zebra_G : !ZebraG Σ} (spec : typed_prophet_spec).

  #[local] Program Definition make_typed_prophet_strong_prophet_spec := {|
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

  #[local] Definition make_typed_prophet_strong_prophet :=
    make_typed_strong_prophet make_typed_prophet_strong_prophet_spec.

  Program Definition make_typed_prophet := {|
    typed_prophet_type :=
      spec.(typed_prophet_spec_type) ;
    typed_prophet_to_val :=
      spec.(typed_prophet_spec_to_val) ;

    typed_prophet_model p prophs := (
      ∃ sprophs,
      ⌜prophs = sprophs.*2⌝ ∗
      make_typed_prophet_strong_prophet.(typed_strong_prophet_model) p sprophs
    )%I ;
  |}.
  Next Obligation.
    iIntros "* (%sprophs1 & _ & Hmodel1) (%sprophs2 & _ & Hmodel2)".
    iApply (typed_strong_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.
  Next Obligation.
    iIntros "* _ HΦ".
    wp_apply (make_typed_prophet_strong_prophet.(typed_strong_prophet_wp_proph) with "[//]").
    iSteps.
  Qed.
  Next Obligation.
    iIntros "*" (? ? ->) "(%sprophs & -> & Hmodel) HΦ".
    wp_apply (typed_strong_prophet_wp_resolve with "Hmodel"); first done.
    wp_apply (wp_wand with "HΦ") as "%w HΦ".
    iExists (w, proph). iSteps.
  Qed.
End make_typed_prophet.

Record typed_prophet1_spec := {
  typed_prophet1_spec_type : Type ;
  typed_prophet1_spec_of_val : val → option typed_prophet1_spec_type ;
  typed_prophet1_spec_to_val : typed_prophet1_spec_type → val ;

  #[global] typed_prophet1_spec_type_inhabited ::
    Inhabited typed_prophet1_spec_type ;

  typed_prophet1_spec_of_to_val proph v :
    v = typed_prophet1_spec_to_val proph →
    typed_prophet1_spec_of_val v = Some proph ;
}.
#[global] Arguments Build_typed_prophet1_spec {_ _ _ _} _ : assert.

Program Coercion typed_prophet1_spec_of_prophet_spec spec := {|
  typed_prophet_spec_type :=
    spec.(typed_prophet1_spec_type) ;
  typed_prophet_spec_of_val :=
    spec.(typed_prophet1_spec_of_val) ;
  typed_prophet_spec_to_val :=
    spec.(typed_prophet1_spec_to_val) ;
|}.
Next Obligation.
  apply typed_prophet1_spec_of_to_val.
Qed.

Record typed_prophet1 `{zebra_G : !ZebraG Σ} := {
  typed_prophet1_type : Type ;
  typed_prophet1_to_val : typed_prophet1_type → val ;

  typed_prophet1_model : prophecy_id → typed_prophet1_type → iProp Σ ;

  #[global] typed_prophet1_model_timeless p proph ::
    Timeless (typed_prophet1_model p proph) ;

  typed_prophet1_model_exclusive p proph1 proph2 :
    typed_prophet1_model p proph1 -∗
    typed_prophet1_model p proph2 -∗
    False ;

  typed_prophet1_wp_proph E :
    {{{ True }}}
      Proph @ E
    {{{ p proph, RET #p; typed_prophet1_model p proph }}} ;

  typed_prophet1_wp_resolve proph e v E p proph' Φ :
    Atomic StronglyAtomic e →
    to_val e = None →
    v = typed_prophet1_to_val proph →
    typed_prophet1_model p proph' -∗
    WP e @ E {{ w, ⌜proph' = proph⌝ -∗ Φ w }} -∗
    WP Resolve e #p v @ E {{ Φ }} ;
}.
#[global] Arguments typed_prophet1 _ {_} : assert.
#[global] Arguments Build_typed_prophet1 {_ _ _ _ _ _} _ _ _ : assert.
#[global] Opaque typed_prophet1_model.

Section make_typed_prophet1.
  Context `{zebra_G : !ZebraG Σ} (spec : typed_prophet1_spec).

  #[local] Definition make_typed_prophet1_prophet :=
    make_typed_prophet spec.

  Program Definition make_typed_prophet1 := {|
    typed_prophet1_type :=
      spec.(typed_prophet_spec_type) ;
    typed_prophet1_to_val :=
      spec.(typed_prophet_spec_to_val) ;

    typed_prophet1_model p proph := (
      ∃ prophs,
      make_typed_prophet1_prophet.(typed_prophet_model) p prophs ∗
      ⌜if prophs is proph' :: _ then proph' = proph else True⌝
    )%I ;
  |}.
  Next Obligation.
    done.
  Qed.
  Next Obligation.
    iIntros "* (%prophs1 & Hmodel1 & _) (%prophs2 & Hmodel2 & _)".
    iApply (typed_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.
  Next Obligation.
    iIntros "* _ HΦ".
    wp_apply (make_typed_prophet1_prophet.(typed_prophet_wp_proph) with "[//]") as "%p %prophs Hmodel".
    destruct prophs as [| proph prophs'] eqn:Heq.
    1: iApply ("HΦ" $! p inhabitant).
    2: iApply ("HΦ" $! p proph).
    all: iSteps.
  Qed.
  Next Obligation.
    iIntros "*" (? ? ->) "(%prophs & Hmodel & %) HΦ".
    wp_apply (typed_prophet_wp_resolve with "Hmodel"); [done.. |].
    iSteps.
  Qed.
End make_typed_prophet1.
