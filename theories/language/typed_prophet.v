From zoo Require Import
  prelude.
From zoo.language Require Export
  wp.
From zoo.language Require Import
  notations
  diaframe.

Record typed_strong_prophet := {
  typed_strong_prophet_type : Type ;
  typed_strong_prophet_of_val : val → val → option typed_strong_prophet_type ;
  typed_strong_prophet_to_val : typed_strong_prophet_type → val * val ;

  typed_strong_prophet_of_to_val proph w v :
    (w, v) = typed_strong_prophet_to_val proph →
    typed_strong_prophet_of_val w v = Some proph ;
}.
#[global] Arguments Build_typed_strong_prophet {_ _ _} _ : assert.

Section typed_strong_prophet.
  Context (prophet : typed_strong_prophet).
  Context `{zoo_G : !ZooG Σ}.

  #[local] Fixpoint typed_strong_prophet_process prophs :=
    match prophs with
    | [] =>
        []
    | (w, v) :: prophs =>
        match prophet.(typed_strong_prophet_of_val) w v with
        | None =>
            []
        | Some proph =>
            proph :: typed_strong_prophet_process prophs
        end
    end.
  Definition typed_strong_prophet_model pid prophs : iProp Σ :=
    ∃ uprophs,
    ⌜prophs = typed_strong_prophet_process uprophs⌝ ∗
    prophet_model pid uprophs.

  #[global] Instance typed_strong_prophet_model_timeless pid prophs :
    Timeless (typed_strong_prophet_model pid prophs).
  Proof.
    apply _.
  Qed.

  Lemma typed_strong_prophet_model_exclusive pid prophs1 prophs2 :
    typed_strong_prophet_model pid prophs1 -∗
    typed_strong_prophet_model pid prophs2 -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma typed_strong_prophet_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid prophs,
      RET #pid;
      typed_strong_prophet_model pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wp_proph with "[//]").
    iSteps.
  Qed.

  Lemma typed_strong_prophet_wp_resolve e v E pid prophs Φ :
    Atomic e →
    to_val e = None →
    typed_strong_prophet_model pid prophs -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = prophet.(typed_strong_prophet_to_val) proph⌝ ∗
        ∀ prophs',
        ⌜prophs = proph :: prophs'⌝ -∗
        typed_strong_prophet_model pid prophs' -∗
        Φ w
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros "% % (%uprophs & %Hprophs & Hpid) HΦ".
    wp_apply (wp_resolve with "Hpid"); first done.
    wp_apply (wp_wand with "HΦ") as "%w (%proph & % & HΦ) %prophs' -> Hpid".
    rewrite /= (typed_strong_prophet_of_to_val _ proph) // in Hprophs.
    iSteps.
  Qed.
End typed_strong_prophet.

#[global] Opaque typed_strong_prophet_model.

Record typed_prophet := {
  typed_prophet_type : Type ;
  typed_prophet_of_val : val → option typed_prophet_type ;
  typed_prophet_to_val : typed_prophet_type → val ;

  typed_prophet_of_to_val proph v :
    v = typed_prophet_to_val proph →
    typed_prophet_of_val v = Some proph ;
}.
#[global] Arguments Build_typed_prophet {_ _ _} _ : assert.

Section typed_prophet.
  Context (prophet : typed_prophet).
  Context `{zoo_G : !ZooG Σ}.

  Program Definition typed_prophet_strong_prophet := {|
    typed_strong_prophet_type :=
      val * prophet.(typed_prophet_type) ;
    typed_strong_prophet_of_val w v :=
      match prophet.(typed_prophet_of_val) v with
      | None =>
          None
      | Some proph =>
          Some (w, proph)
      end ;
    typed_strong_prophet_to_val '(w, proph) :=
      (w, prophet.(typed_prophet_to_val) proph) ;
  |}.
  Next Obligation.
    intros (w & proph) _w v [= -> ->].
    erewrite typed_prophet_of_to_val; done.
  Qed.

  Definition typed_prophet_model pid prophs : iProp Σ :=
    ∃ sprophs,
    ⌜prophs = sprophs.*2⌝ ∗
    typed_strong_prophet_model typed_prophet_strong_prophet pid sprophs.

  #[global] Instance typed_prophet_model_timeless pid prophs :
    Timeless (typed_prophet_model pid prophs).
  Proof.
    apply _.
  Qed.

  Lemma typed_prophet_model_exclusive pid prophs1 prophs2 :
    typed_prophet_model pid prophs1 -∗
    typed_prophet_model pid prophs2 -∗
    False.
  Proof.
    iIntros "(%sprophs1 & _ & Hmodel1) (%sprophs2 & _ & Hmodel2)".
    iApply (typed_strong_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma typed_prophet_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid prophs,
      RET #pid;
      typed_prophet_model pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (typed_strong_prophet_wp_proph with "[//]").
    iSteps. done.
  Qed.

  Lemma typed_prophet_wp_resolve proph e v E pid prophs Φ :
    Atomic e →
    to_val e = None →
    v = prophet.(typed_prophet_to_val) proph →
    typed_prophet_model pid prophs -∗
    WP e @ E {{ w,
      ∀ prophs',
      ⌜prophs = proph :: prophs'⌝ -∗
      typed_prophet_model pid prophs' -∗
      Φ w
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros (? ? ->) "(%sprophs & -> & Hmodel) HΦ".
    wp_apply (typed_strong_prophet_wp_resolve with "Hmodel"); first done.
    wp_apply (wp_wand with "HΦ") as "%w HΦ".
    iExists (w, proph). iSteps.
  Qed.
End typed_prophet.

#[global] Opaque typed_prophet_model.

Coercion typed_prophet_strong_prophet : typed_prophet >-> typed_strong_prophet.

Record typed_prophet1 := {
  typed_prophet1_type : Type ;
  typed_prophet1_of_val : val → option typed_prophet1_type ;
  typed_prophet1_to_val : typed_prophet1_type → val ;

  #[global] typed_prophet1_type_inhabited ::
    Inhabited typed_prophet1_type ;

  typed_prophet1_of_to_val proph v :
    v = typed_prophet1_to_val proph →
    typed_prophet1_of_val v = Some proph ;
}.
#[global] Arguments Build_typed_prophet1 {_ _ _ _} _ : assert.

Section typed_prophet1.
  Context (prophet : typed_prophet1).
  Context `{zoo_G : !ZooG Σ}.

  Program Definition typed_prophet1_prophet prophet := {|
    typed_prophet_type :=
      prophet.(typed_prophet1_type) ;
    typed_prophet_of_val :=
      prophet.(typed_prophet1_of_val) ;
    typed_prophet_to_val :=
      prophet.(typed_prophet1_to_val) ;
  |}.
  Next Obligation.
    apply typed_prophet1_of_to_val.
  Qed.

  Definition typed_prophet1_model pid proph : iProp Σ :=
    ∃ prophs,
    typed_prophet_model (typed_prophet1_prophet prophet) pid prophs ∗
    ⌜if prophs is proph' :: _ then proph' = proph else True⌝.

  #[global] Instance typed_prophet1_model_timeless pid proph :
    Timeless (typed_prophet1_model pid proph).
  Proof.
    apply _.
  Qed.

  Lemma typed_prophet1_model_exclusive pid proph1 proph2 :
    typed_prophet1_model pid proph1 -∗
    typed_prophet1_model pid proph2 -∗
    False.
  Proof.
    iIntros "(%prophs1 & Hmodel1 & _) (%prophs2 & Hmodel2 & _)".
    iApply (typed_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma typed_prophet1_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid proph,
      RET #pid;
      typed_prophet1_model pid proph
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (typed_prophet_wp_proph with "[//]") as "%pid %prophs Hmodel".
    destruct prophs as [| proph prophs'] eqn:Heq.
    1: iApply ("HΦ" $! pid inhabitant).
    2: iApply ("HΦ" $! pid proph).
    all: iSteps.
  Qed.

  Lemma typed_prophet1_wp_resolve proph e v E pid proph' Φ :
    Atomic e →
    to_val e = None →
    v = prophet.(typed_prophet1_to_val) proph →
    typed_prophet1_model pid proph' -∗
    WP e @ E {{ w, ⌜proph' = proph⌝ -∗ Φ w }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros (? ? ->) "(%prophs & Hmodel & %) HΦ".
    wp_apply (typed_prophet_wp_resolve with "Hmodel"); [done.. |].
    iSteps.
  Qed.
End typed_prophet1.

#[global] Opaque typed_prophet1_model.

Coercion typed_prophet1_prophet : typed_prophet1 >-> typed_prophet.
