Require Import zoo.prelude.
Require Import zoo.common.function.
Require Import zoo.base.
Require Export zoo.program_logic.prophet_wise.
Require Import zoo.options.

#[local] Definition prophetx prophet :=
  {|prophet_typed۰type :=
      nat * prophet.(prophet_typed۰type)
  ; prophet_typed۰of_val v1 v2 :=
      match v2 with
      | ValBlock _ _ [ValInt i; v2] =>
          oproph ← prophet.(prophet_typed۰of_val) v1 v2 ;
          match oproph with
          | None =>
              Some None
          | Some proph =>
              Some $ Some (₊i, proph)
          end
      | _ =>
          None
      end
  |}.

Class ProphetMultiG Σ `{zoo۰G : !ZooG Σ} prophet :=
  { #[local] prophet_multi۰G :: ProphetWiseG Σ (prophetx prophet)
  }.

Definition prophet_multi۰Σ prophet :=
  #[prophet_wise۰Σ (prophetx prophet)
  ].
#[global] Instance subG𑁒prophet_multi۰Σ Σ `{zoo۰G : !ZooG Σ} prophet :
  subG (prophet_multi۰Σ prophet) Σ →
  ProphetMultiG Σ prophet.
Proof.
  solve_inG.
Qed.

Section prophet_multi۰G.
  Context (prophet : prophet_typed).
  Context `{prophet_multi۰G : ProphetMultiG Σ prophet}.

  Notation prophetx := (
    prophetx prophet
  ).

  Implicit Type oproph : option prophet.(prophet_typed۰type).
  Implicit Type proph : prophet.(prophet_typed۰type).
  Implicit Type past prophs lb : list prophet.(prophet_typed۰type).
  Implicit Type pasts prophss : nat → list prophet.(prophet_typed۰type).
  Implicit Type iproph : nat * prophet.(prophet_typed۰type).
  Implicit Type ipast iprophs : list (nat * prophet.(prophet_typed۰type)).

  Definition prophet_multi۰name :=
    prophet_wise۰name.
  Implicit Type γ : prophet_multi۰name.

  #[global] Instance prophet_multi۰name𑁒eq_dec : EqDecision prophet_wise۰name :=
    ltac:(apply _).
  #[global] Instance prophet_multi۰name𑁒countable :
    Countable prophet_wise۰name.
  Proof.
    apply _.
  Qed.

  #[local] Definition untangle iprophs i :=
    (filter (λ iproph, iproph.1 = i) iprophs).*2.

  #[local] Lemma untangle𑁒cons iproph iprophs i :
    untangle (iproph :: iprophs) i = if decide (iproph.1 = i) then [iproph.2] ++ untangle iprophs i else untangle iprophs i.
  Proof.
    rewrite /untangle filter_cons //.
    case_decide; done.
  Qed.
  #[local] Lemma untangle𑁒cons𑁒True iproph iprophs i :
    iproph.1 = i →
    untangle (iproph :: iprophs) i = [iproph.2] ++ untangle iprophs i.
  Proof.
    intros <-.
    rewrite untangle𑁒cons decide_True //.
  Qed.
  #[local] Lemma untangle𑁒cons𑁒False iproph iprophs i :
    iproph.1 ≠ i →
    untangle (iproph :: iprophs) i = untangle iprophs i.
  Proof.
    intros Hiproph.
    rewrite untangle𑁒cons decide_False //.
  Qed.
  #[local] Lemma untangle𑁒app iprophs1 iprophs2 i :
    untangle (iprophs1 ++ iprophs2) i = untangle iprophs1 i ++ untangle iprophs2 i.
  Proof.
    rewrite /untangle filter_app fmap_app //.
  Qed.
  #[local] Lemma untangle𑁒snoc iprophs iproph i :
    untangle (iprophs ++ [iproph]) i = if decide (iproph.1 = i) then untangle iprophs i ++ [iproph.2] else untangle iprophs i.
  Proof.
    rewrite untangle𑁒app /untangle filter_cons filter_nil //.
    case_decide; rewrite ?right_id //.
  Qed.
  #[local] Lemma untangle𑁒snoc𑁒True iprophs iproph i :
    iproph.1 = i →
    untangle (iprophs ++ [iproph]) i = untangle iprophs i ++ [iproph.2].
  Proof.
    intros <-.
    rewrite untangle𑁒snoc decide_True //.
  Qed.
  #[local] Lemma untangle𑁒snoc𑁒False iprophs iproph i :
    iproph.1 ≠ i →
    untangle (iprophs ++ [iproph]) i = untangle iprophs i.
  Proof.
    intros Hiproph.
    rewrite untangle𑁒snoc decide_False //.
  Qed.

  Definition prophet_multi۰full γ i prophs : iProp Σ :=
    ∃ iprophs,
    ⌜prophs = untangle iprophs i⌝ ∗
    prophet_wise۰full prophetx γ iprophs.
  #[local] Instance : CustomIpat "full" :=
    " ( %iprophs{}
      & ->
      & Hfull{}
      )
    ".

  Definition prophet_multi۰model pid γ pasts prophss : iProp Σ :=
    ∃ ipast iprophs,
    ⌜pasts ≡ᶠ untangle ipast⌝ ∗
    ⌜prophss ≡ᶠ untangle iprophs⌝ ∗
    prophet_wise۰model prophetx pid γ ipast iprophs.
  #[local] Instance : CustomIpat "model" :=
    " ( %ipast{}
      & %iprophs{}
      & %Hpasts{}
      & %Hprophss{}
      & Hmodel{}
      )
    ".

  Definition prophet_multi۰snapshot γ i past prophs : iProp Σ :=
    ∃ ipast iprophs,
    ⌜past = untangle ipast i⌝ ∗
    ⌜prophs = untangle iprophs i⌝ ∗
    prophet_wise۰snapshot prophetx γ ipast iprophs.
  #[local] Instance : CustomIpat "snapshot" :=
    " ( %ipast{_{suff}}
      & %iprophs{_{suff}}
      & ->
      & ->
      & Hsnapshot
      )
    ".

  Definition prophet_multi۰lb γ i lb : iProp Σ :=
    ∃ past,
    prophet_multi۰snapshot γ i past lb.
  #[local] Instance : CustomIpat "lb" :=
    " ( %past
      & Hsnapshot
      )
    ".

  #[global] Instance prophet_multi۰full𑁒timeless γ i prophs :
    Timeless (prophet_multi۰full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰model𑁒timeless pid γ pasts prophss :
    Timeless (prophet_multi۰model pid γ pasts prophss).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰snapshot𑁒timeless γ i past prophs :
    Timeless (prophet_multi۰snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰lb𑁒timeless γ i lb :
    Timeless (prophet_multi۰lb γ i lb).
  Proof.
    apply _.
  Qed.

  #[global] Instance prophet_multi۰full𑁒persistent γ i prophs :
    Persistent (prophet_multi۰full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰snapshot𑁒persistent γ i past prophs :
    Persistent (prophet_multi۰snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰lb𑁒persistent γ i lb :
    Persistent (prophet_multi۰lb γ i lb).
  Proof.
    apply _.
  Qed.

  Lemma prophet_multi۰model𑁒exclusive pid γ1 pasts1 prophss1 γ2 pasts2 prophss2 :
    prophet_multi۰model pid γ1 pasts1 prophss1 -∗
    prophet_multi۰model pid γ2 pasts2 prophss2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_wise۰model𑁒exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_multi۰full𑁒get {pid γ pasts prophss} i :
    prophet_multi۰model pid γ pasts prophss ⊢
    prophet_multi۰full γ i (pasts i ++ prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (prophet_wise۰full𑁒get with "Hmodel") as "$".
    rewrite Hpasts Hprophss untangle𑁒app //.
  Qed.
  Lemma prophet_multi۰full𑁒get' {pid γ pasts prophss} i :
    prophet_multi۰model pid γ pasts prophss ⊢
      ∃ prophs,
      prophet_multi۰full γ i prophs.
  Proof.
    rewrite prophet_multi۰full𑁒get. iSteps.
  Qed.
  Lemma prophet_multi۰full𑁒valid pid γ pasts prophss i prophs :
    prophet_multi۰model pid γ pasts prophss -∗
    prophet_multi۰full γ i prophs -∗
    ⌜prophs = pasts i ++ prophss i⌝.
  Proof.
    iIntros "(:model =1) (:full =2)". simplify.
    iDestruct (prophet_wise۰full𑁒valid with "Hmodel1 Hfull2") as %->.
    rewrite Hpasts1 Hprophss1 untangle𑁒app //.
  Qed.
  Lemma prophet_multi۰full𑁒agree γ i prophs1 prophs2 :
    prophet_multi۰full γ i prophs1 -∗
    prophet_multi۰full γ i prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    iIntros "(:full =1) (:full =2)". simplify.
    iDestruct (prophet_wise۰full𑁒agree with "Hfull1 Hfull2") as %->.
    iSteps.
  Qed.

  Lemma prophet_multi۰snapshot𑁒get {pid γ pasts prophss} i :
    prophet_multi۰model pid γ pasts prophss ⊢
    prophet_multi۰snapshot γ i (pasts i) (prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (prophet_wise۰snapshot𑁒get with "Hmodel") as "$".
    iSteps.
  Qed.
  Lemma prophet_multi۰snapshot𑁒valid pid γ pasts prophss i past prophs :
    prophet_multi۰model pid γ pasts prophss -∗
    prophet_multi۰snapshot γ i past prophs -∗
      ∃ past',
      ⌜pasts i = past ++ past'⌝ ∗
      ⌜prophs = past' ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:snapshot suff=)".
    iDestruct (prophet_wise۰snapshot𑁒valid with "Hmodel Hsnapshot") as "(%ipast' & -> & ->)".
    iExists (untangle ipast' i). iSplit; iPureIntro.
    all: rewrite ?Hpasts ?Hprophss untangle𑁒app //.
  Qed.

  Lemma prophet_multi۰lb𑁒get {pid γ pasts prophss} i :
    prophet_multi۰model pid γ pasts prophss ⊢
    prophet_multi۰lb γ i (prophss i).
  Proof.
    rewrite (prophet_multi۰snapshot𑁒get i).
    iIntros "Hsnapshot".
    iExists _. iFrame.
  Qed.
  Lemma prophet_multi۰lb𑁒valid pid γ pasts prophss i lb :
    prophet_multi۰model pid γ pasts prophss -∗
    prophet_multi۰lb γ i lb -∗
      ∃ past1 past2,
      ⌜pasts i = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophss i⌝.
  Proof.
    iIntros "Hmodel (:lb)".
    iExists past.
    iApply (prophet_multi۰snapshot𑁒valid with "Hmodel Hsnapshot").
  Qed.

  Lemma prophet_multi𑁒wp𑁒proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{
      pid γ prophss
    , RET #pid;
      prophet_multi۰model pid γ (λ _, []) prophss
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰apply (prophet_wise𑁒wp𑁒proph prophetx with "[//]") as (pid γ iprophs) "Hmodel".
    iApply "HΦ".
    iExists [], iprophs. rewrite /funeq. iSteps.
  Qed.

  Lemma prophet_multi𑁒wp𑁒resolve e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    (0 ≤ i)%Z →
    prophet_multi۰model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed۰of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          prophet_multi۰model pid γ pasts prophss -∗
          Φ w
      | Some proph =>
          ∀ prophs,
          ⌜prophss ₊i = proph :: prophs⌝ -∗
          prophet_multi۰model pid γ (alter (.++ [proph]) ₊i pasts) (<[₊i := prophs]> prophss) -∗
          Φ w
      end
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros "% % %Hi (:model) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    wp۰apply (prophet_wise𑁒wp𑁒resolve with "Hmodel"); first done.
    wp۰apply (wp𑁒wand with "HΦ") as (w) "(%oproph & %Hoproph & HΦ)".
    iEval (rewrite /= Hoproph /=).
    destruct oproph as [proph |]. 2: iSteps.
    iExists (Some (i, proph)). iSplit.
    - iPureIntro. rewrite Nat2Z.id //.
    - iIntros "%iprophs' -> Hmodel".
      iApply ("HΦ" $! (untangle iprophs' i)).
      + iPureIntro. rewrite Hprophss untangle𑁒cons𑁒True //.
      + iExists _, _. iFrame. iSplit; iPureIntro; intros j.
        * rewrite fn𑁒lookup𑁒alter untangle𑁒snoc Hpasts /=.
          case_decide; subst; done.
        * rewrite fn𑁒lookup𑁒insert Hprophss untangle𑁒cons /=.
          case_decide; subst; done.
  Qed.
  Lemma prophet_multi𑁒wp𑁒resolve' e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    prophet_multi۰model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed۰of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          prophet_multi۰model pid γ pasts prophss -∗
          Φ w
      | Some proph =>
          ∀ prophs,
          ⌜prophss i = proph :: prophs⌝ -∗
          prophet_multi۰model pid γ (alter (.++ [proph]) i pasts) (<[i := prophs]> prophss) -∗
          Φ w
      end
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros "% % Hmodel HΦ".
    iApply (prophet_multi𑁒wp𑁒resolve with "Hmodel"); [done | lia |].
    rewrite Nat2Z.id. iSteps.
  Qed.
End prophet_multi۰G.

#[global] Opaque prophet_multi۰name.
#[global] Opaque prophet_multi۰full.
#[global] Opaque prophet_multi۰model.
#[global] Opaque prophet_multi۰snapshot.
#[global] Opaque prophet_multi۰lb.
