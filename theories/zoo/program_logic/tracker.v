Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_wise.
Require Import zoo.options.

Record tracker :=
  { tracker۰event : Type
  ; tracker۰event۰of_val : val → option tracker۰event
  }.
Implicit Type tracker : tracker.

#[local] Coercion tracker۰to_prophet tracker :=
  {|prophet_typed۰type :=
      tracker.(tracker۰event)
  ; prophet_typed۰of_val _ v :=
      Some <$> tracker.(tracker۰event۰of_val) v
  |}.

Zoo name :=
  { prophet : prophet_wise۰name
  }.

Zoo global tracker :=
  { prophet : prophet_wise tracker
  }.

Section tracker۰G.
  Context (tracker : tracker).
  Context `{tracker۰G : TrackerG Σ tracker}.

  Implicit Type ev : tracker.(tracker۰event).
  Implicit Type tr : list tracker.(tracker۰event).

  Please Definition tracker۰model γ tr : iProp Σ :=
    ∃ prophs,
    prophet_wise۰model tracker γ.(tracker۰name۰prophet) tr prophs.
  #[local] Instance : CustomIpat "model" :=
    " ( %prophs{}
      & Hmodel{}
      )
    ".

  #[global] Instance tracker۰modelｰtimeless γ tr :
    Timeless (tracker۰model γ tr).
  Proof.
    apply _.
  Qed.

  Lemma tracker۰modelｰexclusive γ tr1 tr2 :
    tracker۰model γ tr1 -∗
    tracker۰model γ tr2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_wise۰modelｰexclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma trackerｰwpｰproph E :
    {{{
      True
    }}}
      𝗽𝗿𝗼𝗽𝗵
      @ E
    {{{
      γ
    , RET γ;
      tracker۰model γ []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰apply (prophet_wiseｰwpｰproph with "[//]") as (γ۰prophet prophs) "Hmodel".

    pose γ :=
      {|tracker۰name۰prophet := γ۰prophet
      |}.

    iApply ("HΦ" $! γ with "[$]").
  Qed.

  Lemma trackerｰwpｰresolve {γ v} ev tr E Φ :
    tracker.(tracker۰event۰of_val) v = Some ev →
    tracker۰model γ tr -∗
    ( tracker۰model γ (tr ++ [ev]) -∗
      Φ ()%V
    ) -∗
    WP 𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 γ v @ E {{ Φ }}.
  Proof.
    iIntros "%Hv (:model) HΦ".

    wp۰apply (prophet_wiseｰwpｰresolve with "Hmodel"). 1: done.
    wp۰pures.
    iEval (rewrite /= Hv). iSteps.
  Qed.
End tracker۰G.

Please opacify.
