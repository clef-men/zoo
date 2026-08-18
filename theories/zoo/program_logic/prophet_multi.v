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
#[global] Instance subGｰprophet_multi۰Σ Σ `{zoo۰G : !ZooG Σ} prophet :
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

  #[global] Instance prophet_multi۰nameｰeq_dec : EqDecision prophet_wise۰name :=
    ltac:(apply _).
  #[global] Instance prophet_multi۰nameｰcountable :
    Countable prophet_wise۰name.
  Proof.
    apply _.
  Qed.

  #[local] Definition untangle iprophs i :=
    (filter (λ iproph, iproph.1 = i) iprophs).*2.

  #[local] Lemma untangleｰcons iproph iprophs i :
    untangle (iproph :: iprophs) i = if decide (iproph.1 = i) then [iproph.2] ++ untangle iprophs i else untangle iprophs i.
  Proof.
    rewrite /untangle filter_cons //.
    case_decide; done.
  Qed.
  #[local] Lemma untangleｰconsｰTrue iproph iprophs i :
    iproph.1 = i →
    untangle (iproph :: iprophs) i = [iproph.2] ++ untangle iprophs i.
  Proof.
    intros <-.
    rewrite untangleｰcons decide_True //.
  Qed.
  #[local] Lemma untangleｰconsｰFalse iproph iprophs i :
    iproph.1 ≠ i →
    untangle (iproph :: iprophs) i = untangle iprophs i.
  Proof.
    intros Hiproph.
    rewrite untangleｰcons decide_False //.
  Qed.
  #[local] Lemma untangleｰapp iprophs1 iprophs2 i :
    untangle (iprophs1 ++ iprophs2) i = untangle iprophs1 i ++ untangle iprophs2 i.
  Proof.
    rewrite /untangle filter_app fmap_app //.
  Qed.
  #[local] Lemma untangleｰsnoc iprophs iproph i :
    untangle (iprophs ++ [iproph]) i = if decide (iproph.1 = i) then untangle iprophs i ++ [iproph.2] else untangle iprophs i.
  Proof.
    rewrite untangleｰapp /untangle filter_cons filter_nil //.
    case_decide; rewrite ?right_id //.
  Qed.
  #[local] Lemma untangleｰsnocｰTrue iprophs iproph i :
    iproph.1 = i →
    untangle (iprophs ++ [iproph]) i = untangle iprophs i ++ [iproph.2].
  Proof.
    intros <-.
    rewrite untangleｰsnoc decide_True //.
  Qed.
  #[local] Lemma untangleｰsnocｰFalse iprophs iproph i :
    iproph.1 ≠ i →
    untangle (iprophs ++ [iproph]) i = untangle iprophs i.
  Proof.
    intros Hiproph.
    rewrite untangleｰsnoc decide_False //.
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

  #[global] Instance prophet_multi۰fullｰtimeless γ i prophs :
    Timeless (prophet_multi۰full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰modelｰtimeless pid γ pasts prophss :
    Timeless (prophet_multi۰model pid γ pasts prophss).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰snapshotｰtimeless γ i past prophs :
    Timeless (prophet_multi۰snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰lbｰtimeless γ i lb :
    Timeless (prophet_multi۰lb γ i lb).
  Proof.
    apply _.
  Qed.

  #[global] Instance prophet_multi۰fullｰpersistent γ i prophs :
    Persistent (prophet_multi۰full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰snapshotｰpersistent γ i past prophs :
    Persistent (prophet_multi۰snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi۰lbｰpersistent γ i lb :
    Persistent (prophet_multi۰lb γ i lb).
  Proof.
    apply _.
  Qed.

  Lemma prophet_multi۰modelｰexclusive pid γ1 pasts1 prophss1 γ2 pasts2 prophss2 :
    prophet_multi۰model pid γ1 pasts1 prophss1 -∗
    prophet_multi۰model pid γ2 pasts2 prophss2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_wise۰modelｰexclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_multi۰fullｰget {pid γ pasts prophss} i :
    prophet_multi۰model pid γ pasts prophss ⊢
    prophet_multi۰full γ i (pasts i ++ prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (prophet_wise۰fullｰget with "Hmodel") as "$".
    rewrite Hpasts Hprophss untangleｰapp //.
  Qed.
  Lemma prophet_multi۰fullｰget' {pid γ pasts prophss} i :
    prophet_multi۰model pid γ pasts prophss ⊢
      ∃ prophs,
      prophet_multi۰full γ i prophs.
  Proof.
    rewrite prophet_multi۰fullｰget. iSteps.
  Qed.
  Lemma prophet_multi۰fullｰvalid pid γ pasts prophss i prophs :
    prophet_multi۰model pid γ pasts prophss -∗
    prophet_multi۰full γ i prophs -∗
    ⌜prophs = pasts i ++ prophss i⌝.
  Proof.
    iIntros "(:model =1) (:full =2)". simp.
    iDestruct (prophet_wise۰fullｰvalid with "Hmodel1 Hfull2") as %->.
    rewrite Hpasts1 Hprophss1 untangleｰapp //.
  Qed.
  Lemma prophet_multi۰fullｰagree γ i prophs1 prophs2 :
    prophet_multi۰full γ i prophs1 -∗
    prophet_multi۰full γ i prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    iIntros "(:full =1) (:full =2)". simp.
    iDestruct (prophet_wise۰fullｰagree with "Hfull1 Hfull2") as %->.
    iSteps.
  Qed.

  Lemma prophet_multi۰snapshotｰget {pid γ pasts prophss} i :
    prophet_multi۰model pid γ pasts prophss ⊢
    prophet_multi۰snapshot γ i (pasts i) (prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (prophet_wise۰snapshotｰget with "Hmodel") as "$".
    iSteps.
  Qed.
  Lemma prophet_multi۰snapshotｰvalid pid γ pasts prophss i past prophs :
    prophet_multi۰model pid γ pasts prophss -∗
    prophet_multi۰snapshot γ i past prophs -∗
      ∃ past',
      ⌜pasts i = past ++ past'⌝ ∗
      ⌜prophs = past' ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:snapshot suff=)".
    iDestruct (prophet_wise۰snapshotｰvalid with "Hmodel Hsnapshot") as "(%ipast' & -> & ->)".
    iExists (untangle ipast' i). iSplit; iPureIntro.
    all: rewrite ?Hpasts ?Hprophss untangleｰapp //.
  Qed.

  Lemma prophet_multi۰lbｰget {pid γ pasts prophss} i :
    prophet_multi۰model pid γ pasts prophss ⊢
    prophet_multi۰lb γ i (prophss i).
  Proof.
    rewrite (prophet_multi۰snapshotｰget i).
    iIntros "Hsnapshot".
    iExists _. iFrame.
  Qed.
  Lemma prophet_multi۰lbｰvalid pid γ pasts prophss i lb :
    prophet_multi۰model pid γ pasts prophss -∗
    prophet_multi۰lb γ i lb -∗
      ∃ past1 past2,
      ⌜pasts i = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophss i⌝.
  Proof.
    iIntros "Hmodel (:lb)".
    iExists past.
    iApply (prophet_multi۰snapshotｰvalid with "Hmodel Hsnapshot").
  Qed.

  Lemma prophet_multiｰwpｰproph E :
    {{{
      True
    }}}
      Proph
      @ E
    {{{
      pid γ prophss
    , RET #pid;
      prophet_multi۰model pid γ (λ _, []) prophss
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰apply (prophet_wiseｰwpｰproph prophetx with "[//]") as (pid γ iprophs) "Hmodel".
    iApply "HΦ".
    iExists [], iprophs. rewrite /funeq. iSteps.
  Qed.

  Lemma prophet_multiｰwpｰresolve e pid i v γ pasts prophss E Φ :
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
    wp۰apply (prophet_wiseｰwpｰresolve with "Hmodel"); first done.
    wp۰apply (wpｰwand with "HΦ") as (w) "(%oproph & %Hoproph & HΦ)".
    iEval (rewrite /= Hoproph /=).
    destruct oproph as [proph |]. 2: iSteps.
    iExists (Some (i, proph)). iSplit.
    - iPureIntro. rewrite Nat2Z.id //.
    - iIntros "%iprophs' -> Hmodel".
      iApply ("HΦ" $! (untangle iprophs' i)).
      + iPureIntro. rewrite Hprophss untangleｰconsｰTrue //.
      + iExists _, _. iFrame. iSplit; iPureIntro; intros j.
        * rewrite fnｰlookupｰalter untangleｰsnoc Hpasts /=.
          case_decide; subst; done.
        * rewrite fnｰlookupｰinsert Hprophss untangleｰcons /=.
          case_decide; subst; done.
  Qed.
  Lemma prophet_multiｰwpｰresolve' e pid i v γ pasts prophss E Φ :
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
    iApply (prophet_multiｰwpｰresolve with "Hmodel"); [done | lia |].
    rewrite Nat2Z.id. iSteps.
  Qed.
End prophet_multi۰G.

#[global] Opaque prophet_multi۰name.
#[global] Opaque prophet_multi۰full.
#[global] Opaque prophet_multi۰model.
#[global] Opaque prophet_multi۰snapshot.
#[global] Opaque prophet_multi۰lb.
