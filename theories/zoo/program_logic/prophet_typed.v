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

Record prophet_typed :=
  { prophet_typed_type : Type
  ; prophet_typed_of_val : val → val → option $ option prophet_typed_type
  }.

Section prophet_typed.
  Context (prophet : prophet_typed).
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types uproph : val * val.
  Implicit Types uprophs : list (val * val).
  Implicit Types oproph : option prophet.(prophet_typed_type).
  Implicit Types proph : prophet.(prophet_typed_type).
  Implicit Types prophs : list prophet.(prophet_typed_type).

  #[local] Fixpoint prophet_typed_process uprophs :=
    match uprophs with
    | [] =>
        []
    | (w, v) :: uprophs =>
        match prophet.(prophet_typed_of_val) w v with
        | None =>
            []
        | Some None =>
            prophet_typed_process uprophs
        | Some (Some proph) =>
            proph :: prophet_typed_process uprophs
        end
    end.

  Definition prophet_typed_model pid prophs : iProp Σ :=
    ∃ uprophs,
    ⌜prophs = prophet_typed_process uprophs⌝ ∗
    prophet_model pid uprophs.
  #[local] Instance : CustomIpat "model" :=
    " ( %uprophs
      & %Hprophs
      & Hpid
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
    iSteps.
  Qed.

  Lemma prophet_typed_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{
      pid prophs
    , RET #pid;
      prophet_typed_model pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wp_proph with "[//]").
    iSteps.
  Qed.

  Lemma prophet_typed_wp_resolve e pid v prophs E Φ :
    Atomic e →
    to_val e = None →
    prophet_typed_model pid prophs -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed_of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          prophet_typed_model pid prophs -∗
          Φ w
      | Some proph =>
          ∀ prophs',
          ⌜prophs = proph :: prophs'⌝ -∗
          prophet_typed_model pid prophs' -∗
          Φ w
      end
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros "% % (:model) HΦ".
    wp_apply (wp_resolve with "Hpid"); first done.
    wp_apply (wp_wand with "HΦ") as "%w (%oproph & %Hoproph & HΦ) %prophs' -> Hpid".
    rewrite /= Hoproph in Hprophs.
    destruct oproph; iSteps.
  Qed.
End prophet_typed.

#[global] Opaque prophet_typed_model.

Record prophet_typed_1 :=
  { prophet_typed_1_type : Type
  ; prophet_typed_1_of_val : val → val → option $ option prophet_typed_1_type

  ; #[global] prophet_typed_1_type_inhabited ::
      Inhabited prophet_typed_1_type
  }.

Section prophet_typed_1.
  Context (prophet : prophet_typed_1).
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types oproph : option prophet.(prophet_typed_1_type).
  Implicit Types proph : prophet.(prophet_typed_1_type).
  Implicit Types prophs : list prophet.(prophet_typed_1_type).

  Definition prophet_typed_1_to_prophet :=
    {|prophet_typed_type :=
        prophet.(prophet_typed_1_type)
    ; prophet_typed_of_val :=
        prophet.(prophet_typed_1_of_val)
    |}.

  Definition prophet_typed_1_model pid proph : iProp Σ :=
    ∃ prophs,
    prophet_typed_model prophet_typed_1_to_prophet pid prophs ∗
    ⌜if prophs is proph' :: _ then proph' = proph else True⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %prophs{}
      & Hmodel{}
      & %
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
    {{{
      pid proph
    , RET #pid;
      prophet_typed_1_model pid proph
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (prophet_typed_wp_proph prophet_typed_1_to_prophet with "[//]") as "%pid %prophs Hmodel".
    destruct prophs as [| proph prophs'] eqn:Heq.
    1: iApply ("HΦ" $! pid inhabitant).
    2: iApply ("HΦ" $! pid proph).
    all: iSteps.
  Qed.

  Lemma prophet_typed_1_wp_resolve e pid v proph E Φ :
    Atomic e →
    to_val e = None →
    prophet_typed_1_model pid proph -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed_1_of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          Φ w
      | Some proph' =>
          ⌜proph = proph'⌝ -∗
          Φ w
      end
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros (? ?) "(:model) HΦ".
    wp_apply (prophet_typed_wp_resolve with "Hmodel"); first done.
    wp_apply (wp_wand with "HΦ") as (w) "(%oproph & %Hoproph & HΦ)".
    destruct oproph; iSteps.
  Qed.
End prophet_typed_1.

#[global] Opaque prophet_typed_1_model.

Coercion prophet_typed_1_to_prophet : prophet_typed_1 >-> prophet_typed.
