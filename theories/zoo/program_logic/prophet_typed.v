Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Record prophet_typed :=
  { prophet_typed۰type : Type
  ; prophet_typed۰of_val : val → val → option $ option prophet_typed۰type
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

  Definition prophet_typed۰model pid prophs : iProp Σ :=
    ∃ uprophs,
    ⌜prophs = prophet_typed۰process uprophs⌝ ∗
    prophet۰model pid uprophs.
  #[local] Instance : CustomIpat "model" :=
    " ( %uprophs
      & %Hprophs
      & Hpid
      )
    ".

  #[global] Instance prophet_typed۰model𑁒timeless pid prophs :
    Timeless (prophet_typed۰model pid prophs).
  Proof.
    apply _.
  Qed.

  Lemma prophet_typed۰model𑁒exclusive pid prophs1 prophs2 :
    prophet_typed۰model pid prophs1 -∗
    prophet_typed۰model pid prophs2 -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma prophet_typed𑁒wp𑁒proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{
      pid prophs
    , RET #pid;
      prophet_typed۰model pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰apply (wp𑁒proph with "[//]").
    iSteps.
  Qed.

  Lemma prophet_typed𑁒wp𑁒resolve e pid v prophs E Φ :
    Atomic e →
    to_val e = None →
    prophet_typed۰model pid prophs -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed۰of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          prophet_typed۰model pid prophs -∗
          Φ w
      | Some proph =>
          ∀ prophs',
          ⌜prophs = proph :: prophs'⌝ -∗
          prophet_typed۰model pid prophs' -∗
          Φ w
      end
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros "% % (:model) HΦ".
    wp۰apply (wp𑁒resolve with "Hpid"); first done.
    wp۰apply (wp𑁒wand with "HΦ") as "%w (%oproph & %Hoproph & HΦ) %prophs' -> Hpid".
    rewrite /= Hoproph in Hprophs.
    destruct oproph; iSteps.
  Qed.
End prophet_typed.

#[global] Opaque prophet_typed۰model.

Record prophet_typed₁ :=
  { prophet_typed₁۰type : Type
  ; prophet_typed₁۰of_val : val → val → option $ option prophet_typed₁۰type

  ; #[global] prophet_typed₁۰type𑁒inhabited ::
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

  Definition prophet_typed₁۰model pid proph : iProp Σ :=
    ∃ prophs,
    prophet_typed۰model prophet_typed₁۰to_prophet pid prophs ∗
    ⌜if prophs is proph' :: _ then proph' = proph else True⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %prophs{}
      & Hmodel{}
      & %
      )
    ".

  #[global] Instance prophet_typed₁۰model𑁒timeless pid proph :
    Timeless (prophet_typed₁۰model pid proph).
  Proof.
    apply _.
  Qed.

  Lemma prophet_typed₁۰model𑁒exclusive pid proph1 proph2 :
    prophet_typed₁۰model pid proph1 -∗
    prophet_typed₁۰model pid proph2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_typed۰model𑁒exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_typed₁𑁒wp𑁒proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{
      pid proph
    , RET #pid;
      prophet_typed₁۰model pid proph
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰apply (prophet_typed𑁒wp𑁒proph prophet_typed₁۰to_prophet with "[//]") as "%pid %prophs Hmodel".
    destruct prophs as [| proph prophs'] eqn:Heq.
    1: iApply ("HΦ" $! pid inhabitant).
    2: iApply ("HΦ" $! pid proph).
    all: iSteps.
  Qed.

  Lemma prophet_typed₁𑁒wp𑁒resolve e pid v proph E Φ :
    Atomic e →
    to_val e = None →
    prophet_typed₁۰model pid proph -∗
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
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros (? ?) "(:model) HΦ".
    wp۰apply (prophet_typed𑁒wp𑁒resolve with "Hmodel"); first done.
    wp۰apply (wp𑁒wand with "HΦ") as (w) "(%oproph & %Hoproph & HΦ)".
    destruct oproph; iSteps.
  Qed.
End prophet_typed₁.

#[global] Opaque prophet_typed₁۰model.

Coercion prophet_typed₁۰to_prophet : prophet_typed₁ >-> prophet_typed.
