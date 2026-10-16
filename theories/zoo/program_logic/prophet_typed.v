Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Record prophet_typed :=
  { prophet_typed۰type : Type
  ; prophet_typed۰of_val : val → val → option $ option prophet_typed۰type
  }.

Zoo name :=
  { id : prophet_id
  }.

Section prophet_typed.
  Context (prophet : prophet_typed).
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type uproph : val * val.
  Implicit Type uprophs : list (val * val).
  Implicit Type oproph : option prophet.(prophet_typed۰type).
  Implicit Type proph : prophet.(prophet_typed۰type).
  Implicit Type prophs : list prophet.(prophet_typed۰type).

  #[local] Fixpoint prophet_typed۰process uprophs :=
    match uprophs with
    | [] =>
        []
    | (w, v) :: uprophs =>
        match prophet.(prophet_typed۰of_val) w v with
        | None =>
            []
        | Some None =>
            prophet_typed۰process uprophs
        | Some (Some proph) =>
            proph :: prophet_typed۰process uprophs
        end
    end.

  Please Definition prophet_typed۰model γ prophs : iProp Σ :=
    ∃ uprophs,
    ⌜prophs = prophet_typed۰process uprophs⌝ ∗
    prophet۰model γ.(prophet_typed۰name۰id) uprophs.
  #[local] Instance : CustomIpat "model" :=
    " ( %uprophs
      & %Hprophs
      & Hmodel
      )
    ".

  #[global] Instance prophet_typed۰modelｰtimeless γ prophs :
    Timeless (prophet_typed۰model γ prophs).
  Proof.
    apply _.
  Qed.

  Lemma prophet_typed۰modelｰexclusive γ prophs1 prophs2 :
    prophet_typed۰model γ prophs1 -∗
    prophet_typed۰model γ prophs2 -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma prophet_typedｰwpｰproph E :
    {{{
      True
    }}}
      𝗽𝗿𝗼𝗽𝗵
      @ E
    {{{
      γ prophs
    , RET γ;
      prophet_typed۰model γ prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰apply (wpｰproph with "[//]") as (prophs pid) "Hmodel".

    pose γ :=
      {|prophet_typed۰name۰id := pid
      |}.

    iApply ("HΦ" $! γ with "[$Hmodel //]").
  Qed.

  Lemma prophet_typedｰwpｰresolve e γ v prophs E Φ :
    Atomic e →
    expr۰to_val e = None →
    prophet_typed۰model γ prophs -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed۰of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          prophet_typed۰model γ prophs -∗
          Φ w
      | Some proph =>
          ∀ prophs',
          ⌜prophs = proph :: prophs'⌝ -∗
          prophet_typed۰model γ prophs' -∗
          Φ w
      end
    }} -∗
    WP 𝗿𝗲𝘀𝗼𝗹𝘃𝗲 e γ v @ E {{ Φ }}.
  Proof.
    iIntros "% % (:model) HΦ".

    wp۰apply (wpｰresolve with "Hmodel"). 1: done.
    wp۰apply (wpｰwand with "HΦ") as "%w (%oproph & %Hoproph & HΦ) %prophs' -> Hmodel".
    rewrite /= Hoproph in Hprophs.
    destruct oproph; iSteps.
  Qed.
End prophet_typed.

Please opacify.

Record prophet_typed₁ :=
  { prophet_typed₁۰type : Type
  ; prophet_typed₁۰of_val : val → val → option $ option prophet_typed₁۰type

  ; #[global] prophet_typed₁۰typeｰinhabited ::
      Inhabited prophet_typed₁۰type
  }.

Section prophet_typed₁.
  Context (prophet : prophet_typed₁).
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type oproph : option prophet.(prophet_typed₁۰type).
  Implicit Type proph : prophet.(prophet_typed₁۰type).
  Implicit Type prophs : list prophet.(prophet_typed₁۰type).

  Definition prophet_typed₁۰to_prophet :=
    {|prophet_typed۰type :=
        prophet.(prophet_typed₁۰type)
    ; prophet_typed۰of_val :=
        prophet.(prophet_typed₁۰of_val)
    |}.

  Please Definition prophet_typed₁۰model γ proph : iProp Σ :=
    ∃ prophs,
    prophet_typed۰model prophet_typed₁۰to_prophet γ prophs ∗
    ⌜if prophs is proph' :: _ then proph' = proph else True⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %prophs{}
      & Hmodel{}
      & %
      )
    ".

  #[global] Instance prophet_typed₁۰modelｰtimeless γ proph :
    Timeless (prophet_typed₁۰model γ proph).
  Proof.
    apply _.
  Qed.

  Lemma prophet_typed₁۰modelｰexclusive γ proph1 proph2 :
    prophet_typed₁۰model γ proph1 -∗
    prophet_typed₁۰model γ proph2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_typed۰modelｰexclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_typed₁ｰwpｰproph E :
    {{{
      True
    }}}
      𝗽𝗿𝗼𝗽𝗵
      @ E
    {{{
      γ proph
    , RET γ;
      prophet_typed₁۰model γ proph
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰apply (prophet_typedｰwpｰproph prophet_typed₁۰to_prophet with "[//]") as "%γ %prophs Hmodel".
    destruct prophs as [| proph prophs'] eqn:Heq.
    1: iApply ("HΦ" $! γ inhabitant).
    2: iApply ("HΦ" $! γ proph).
    all: iFrameSteps.
  Qed.

  Lemma prophet_typed₁ｰwpｰresolve e γ v proph E Φ :
    Atomic e →
    expr۰to_val e = None →
    prophet_typed₁۰model γ proph -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed₁۰of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          Φ w
      | Some proph' =>
          ⌜proph = proph'⌝ -∗
          Φ w
      end
    }} -∗
    WP 𝗿𝗲𝘀𝗼𝗹𝘃𝗲 e γ v @ E {{ Φ }}.
  Proof.
    iIntros (? ?) "(:model) HΦ".

    wp۰apply (prophet_typedｰwpｰresolve with "Hmodel"). 1: done.
    wp۰apply (wpｰwand with "HΦ") as (w) "(%oproph & %Hoproph & HΦ)".
    destruct oproph; iSteps.
  Qed.
End prophet_typed₁.

Please opacify.

Coercion prophet_typed₁۰to_prophet : prophet_typed₁ >-> prophet_typed.
