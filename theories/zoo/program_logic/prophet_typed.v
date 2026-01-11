From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  wp.
From zoo.diaframe Require Import
  diaframe.
From zoo Require Import
  options.

Record prophet_typed_strong := {
  prophet_typed_strong_type : Type ;
  prophet_typed_strong_of_val : val → val → option prophet_typed_strong_type ;
  prophet_typed_strong_to_val : prophet_typed_strong_type → val * val ;

  prophet_typed_strong_of_to_val proph w v :
    (w, v) = prophet_typed_strong_to_val proph →
    prophet_typed_strong_of_val w v = Some proph ;
}.
#[global] Arguments Build_prophet_typed_strong {_ _ _} _ : assert.

Section prophet_typed_strong.
  Context (prophet : prophet_typed_strong).
  Context `{zoo_G : !ZooG Σ}.

  #[local] Fixpoint prophet_typed_strong_process prophs :=
    match prophs with
    | [] =>
        []
    | (w, v) :: prophs =>
        match prophet.(prophet_typed_strong_of_val) w v with
        | None =>
            []
        | Some proph =>
            proph :: prophet_typed_strong_process prophs
        end
    end.
  Definition prophet_typed_strong_model pid prophs : iProp Σ :=
    ∃ uprophs,
    ⌜prophs = prophet_typed_strong_process uprophs⌝ ∗
    prophet_model' pid uprophs.
  #[local] Instance : CustomIpat "model" :=
    " ( %uprophs &
        %Hprophs &
        Hpid
      )
    ".

  #[global] Instance prophet_typed_strong_model_timeless pid prophs :
    Timeless (prophet_typed_strong_model pid prophs).
  Proof.
    apply _.
  Qed.

  Lemma prophet_typed_strong_model_exclusive pid prophs1 prophs2 :
    prophet_typed_strong_model pid prophs1 -∗
    prophet_typed_strong_model pid prophs2 -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma prophet_typed_strong_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid prophs,
      RET #pid;
      prophet_typed_strong_model pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wp_proph with "[//]").
    iSteps.
  Qed.

  Lemma prophet_typed_strong_wp_resolve e pid v prophs E Φ :
    Atomic e →
    to_val e = None →
    prophet_typed_strong_model pid prophs -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = prophet.(prophet_typed_strong_to_val) proph⌝ ∗
        ∀ prophs',
        ⌜prophs = proph :: prophs'⌝ -∗
        prophet_typed_strong_model pid prophs' -∗
        Φ w
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros "% % (:model) HΦ".
    wp_apply (wp_resolve with "Hpid"); first done.
    wp_apply (wp_wand with "HΦ") as "%w (%proph & % & HΦ) %prophs' -> Hpid".
    rewrite /= (prophet_typed_strong_of_to_val _ proph) // in Hprophs.
    iSteps.
  Qed.
End prophet_typed_strong.

#[global] Opaque prophet_typed_strong_model.

Record prophet_typed_strong_1 := {
  prophet_typed_strong_1_type : Type ;
  prophet_typed_strong_1_of_val : val → val → option prophet_typed_strong_1_type ;
  prophet_typed_strong_1_to_val : prophet_typed_strong_1_type → val * val ;

  #[global] prophet_typed_strong_1_type_inhabited ::
    Inhabited prophet_typed_strong_1_type ;

  prophet_typed_strong_1_of_to_val proph w v :
    (w, v) = prophet_typed_strong_1_to_val proph →
    prophet_typed_strong_1_of_val w v = Some proph ;
}.
#[global] Arguments Build_prophet_typed_strong_1 {_ _ _ _} _ : assert.

Section prophet_typed_strong_1.
  Context (prophet : prophet_typed_strong_1).
  Context `{zoo_G : !ZooG Σ}.

  Program Definition prophet_typed_strong_1_to_prophet := {|
    prophet_typed_strong_type :=
      prophet.(prophet_typed_strong_1_type) ;
    prophet_typed_strong_of_val :=
      prophet.(prophet_typed_strong_1_of_val) ;
    prophet_typed_strong_to_val :=
      prophet.(prophet_typed_strong_1_to_val) ;
  |}.
  Next Obligation.
    apply prophet_typed_strong_1_of_to_val.
  Qed.

  Definition prophet_typed_strong_1_model pid proph : iProp Σ :=
    ∃ prophs,
    prophet_typed_strong_model prophet_typed_strong_1_to_prophet pid prophs ∗
    ⌜if prophs is proph' :: _ then proph' = proph else True⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %prophs{} &
        Hmodel{} &
        %
      )
    ".

  #[global] Instance prophet_typed_strong_1_model_timeless pid proph :
    Timeless (prophet_typed_strong_1_model pid proph).
  Proof.
    apply _.
  Qed.

  Lemma prophet_typed_strong_1_model_exclusive pid proph1 proph2 :
    prophet_typed_strong_1_model pid proph1 -∗
    prophet_typed_strong_1_model pid proph2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_typed_strong_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_typed_strong_1_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid proph,
      RET #pid;
      prophet_typed_strong_1_model pid proph
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (prophet_typed_strong_wp_proph with "[//]") as "%pid %prophs Hmodel".
    destruct prophs as [| proph prophs'] eqn:Heq.
    1: iApply ("HΦ" $! pid inhabitant).
    2: iApply ("HΦ" $! pid proph).
    all: iSteps.
  Qed.

  Lemma prophet_typed_strong_1_wp_resolve e pid v proph E Φ :
    Atomic e →
    to_val e = None →
    prophet_typed_strong_1_model pid proph -∗
    WP e @ E {{ w,
      ∃ proph',
      ⌜(w, v) = prophet.(prophet_typed_strong_1_to_val) proph'⌝ ∗
      (⌜proph = proph'⌝ -∗ Φ w)
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros (? ?) "(:model) HΦ".
    wp_apply (prophet_typed_strong_wp_resolve with "Hmodel"); first done.
    iSteps.
  Qed.
End prophet_typed_strong_1.

#[global] Opaque prophet_typed_strong_1_model.

Coercion prophet_typed_strong_1_to_prophet : prophet_typed_strong_1 >-> prophet_typed_strong.

Record prophet_typed := {
  prophet_typed_type : Type ;
  prophet_typed_of_val : val → option prophet_typed_type ;
  prophet_typed_to_val : prophet_typed_type → val ;

  prophet_typed_of_to_val proph v :
    v = prophet_typed_to_val proph →
    prophet_typed_of_val v = Some proph ;
}.
#[global] Arguments Build_prophet_typed {_ _ _} _ : assert.

Section prophet_typed.
  Context (prophet : prophet_typed).
  Context `{zoo_G : !ZooG Σ}.

  Program Definition prophet_typed_to_strong := {|
    prophet_typed_strong_type :=
      val * prophet.(prophet_typed_type) ;
    prophet_typed_strong_of_val w v :=
      match prophet.(prophet_typed_of_val) v with
      | None =>
          None
      | Some proph =>
          Some (w, proph)
      end ;
    prophet_typed_strong_to_val '(w, proph) :=
      (w, prophet.(prophet_typed_to_val) proph) ;
  |}.
  Next Obligation.
    intros (w & proph) _w v [= -> ->].
    erewrite prophet_typed_of_to_val => //.
  Qed.

  Definition prophet_typed_model pid prophs : iProp Σ :=
    ∃ sprophs,
    ⌜prophs = sprophs.*2⌝ ∗
    prophet_typed_strong_model prophet_typed_to_strong pid sprophs.
  #[local] Instance : CustomIpat "model" :=
    " ( %sprophs{} &
        -> &
        Hmodel{}
      )
    ".

  #[global] Instance prophet_typed_model_timeless pid prophs :
    Timeless (prophet_typed_model pid prophs).
  Proof.
    apply _.
  Qed.

  Lemma prophet_typed_model_exclusive pid prophs1 prophs2 :
    prophet_typed_model pid prophs1 -∗
    prophet_typed_model pid prophs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_typed_strong_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_typed_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid prophs,
      RET #pid;
      prophet_typed_model pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (prophet_typed_strong_wp_proph with "[//]").
    iSteps. done.
  Qed.

  Lemma prophet_typed_wp_resolve proph e pid v prophs E Φ :
    Atomic e →
    to_val e = None →
    v = prophet.(prophet_typed_to_val) proph →
    prophet_typed_model pid prophs -∗
    WP e @ E {{ w,
      ∀ prophs',
      ⌜prophs = proph :: prophs'⌝ -∗
      prophet_typed_model pid prophs' -∗
      Φ w
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros (? ? ->) "(:model) HΦ".
    wp_apply (prophet_typed_strong_wp_resolve with "Hmodel"); first done.
    wp_apply (wp_wand with "HΦ") as "%w HΦ".
    iExists (w, proph). iSteps.
  Qed.
End prophet_typed.

#[global] Opaque prophet_typed_model.

Coercion prophet_typed_to_strong : prophet_typed >-> prophet_typed_strong.

Record prophet_typed_1 := {
  prophet_typed_1_type : Type ;
  prophet_typed_1_of_val : val → option prophet_typed_1_type ;
  prophet_typed_1_to_val : prophet_typed_1_type → val ;

  #[global] prophet_typed_1_type_inhabited ::
    Inhabited prophet_typed_1_type ;

  prophet_typed_1_of_to_val proph v :
    v = prophet_typed_1_to_val proph →
    prophet_typed_1_of_val v = Some proph ;
}.
#[global] Arguments Build_prophet_typed_1 {_ _ _ _} _ : assert.

Section prophet_typed_1.
  Context (prophet : prophet_typed_1).
  Context `{zoo_G : !ZooG Σ}.

  Program Definition prophet_typed_1_to_prophet := {|
    prophet_typed_type :=
      prophet.(prophet_typed_1_type) ;
    prophet_typed_of_val :=
      prophet.(prophet_typed_1_of_val) ;
    prophet_typed_to_val :=
      prophet.(prophet_typed_1_to_val) ;
  |}.
  Next Obligation.
    apply prophet_typed_1_of_to_val.
  Qed.

  Definition prophet_typed_1_model pid proph : iProp Σ :=
    ∃ prophs,
    prophet_typed_model prophet_typed_1_to_prophet pid prophs ∗
    ⌜if prophs is proph' :: _ then proph' = proph else True⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %prophs{} &
        Hmodel{} &
        %
      )
    ".

  #[global] Instance prophet_typed_1_model_timeless pid proph :
    Timeless (prophet_typed_1_model pid proph).
  Proof.
    apply _.
  Qed.

  Lemma prophet_typed_1_model_exclusive pid proph1 proph2 :
    prophet_typed_1_model pid proph1 -∗
    prophet_typed_1_model pid proph2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_typed_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_typed_1_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid proph,
      RET #pid;
      prophet_typed_1_model pid proph
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (prophet_typed_wp_proph with "[//]") as "%pid %prophs Hmodel".
    destruct prophs as [| proph prophs'] eqn:Heq.
    1: iApply ("HΦ" $! pid inhabitant).
    2: iApply ("HΦ" $! pid proph).
    all: iSteps.
  Qed.

  Lemma prophet_typed_1_wp_resolve proph e pid v proph' E Φ :
    Atomic e →
    to_val e = None →
    v = prophet.(prophet_typed_1_to_val) proph →
    prophet_typed_1_model pid proph' -∗
    WP e @ E {{ w, ⌜proph' = proph⌝ -∗ Φ w }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros (? ? ->) "(:model) HΦ".
    wp_apply (prophet_typed_wp_resolve with "Hmodel"); [done.. |].
    iSteps.
  Qed.
End prophet_typed_1.

#[global] Opaque prophet_typed_1_model.

Coercion prophet_typed_1_to_prophet : prophet_typed_1 >-> prophet_typed.
