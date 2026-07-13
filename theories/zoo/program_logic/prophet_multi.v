Require Import zoo.prelude.
Require Import zoo.common.function.
Require Import zoo.base.
Require Export zoo.program_logic.prophet_wise.
Require Import zoo.options.

#[local] Definition prophetx prophet :=
  {|prophet_typed_type :=
      nat * prophet.(prophet_typed_type)
  ; prophet_typed_of_val v1 v2 :=
      match v2 with
      | ValBlock _ _ [ValInt i; v2] =>
          oproph ← prophet.(prophet_typed_of_val) v1 v2 ;
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

Class ProphetMultiG Σ `{zoo_G : !ZooG Σ} prophet :=
  { #[local] prophet_multi_G :: ProphetWiseG Σ (prophetx prophet)
  }.

Definition prophet_multi_Σ prophet :=
  #[prophet_wise_Σ (prophetx prophet)
  ].
#[global] Instance subG_prophet_multi_Σ Σ `{zoo_G : !ZooG Σ} prophet :
  subG (prophet_multi_Σ prophet) Σ →
  ProphetMultiG Σ prophet.
Proof.
  solve_inG.
Qed.

Section prophet_multi_G.
  Context (prophet : prophet_typed).
  Context `{prophet_multi_G : ProphetMultiG Σ prophet}.

  Notation prophetx := (
    prophetx prophet
  ).

  Implicit Types oproph : option prophet.(prophet_typed_type).
  Implicit Types proph : prophet.(prophet_typed_type).
  Implicit Types past prophs lb : list prophet.(prophet_typed_type).
  Implicit Types pasts prophss : nat → list prophet.(prophet_typed_type).
  Implicit Types iproph : nat * prophet.(prophet_typed_type).
  Implicit Types ipast iprophs : list (nat * prophet.(prophet_typed_type)).

  Definition prophet_multi_name :=
    prophet_wise_name.
  Implicit Types γ : prophet_multi_name.

  #[global] Instance prophet_multi_name_eq_dec : EqDecision prophet_wise_name :=
    ltac:(apply _).
  #[global] Instance prophet_multi_name_countable :
    Countable prophet_wise_name.
  Proof.
    apply _.
  Qed.

  #[local] Definition untangle iprophs i :=
    (filter (λ iproph, iproph.1 = i) iprophs).*2.

  #[local] Lemma untangle_cons iproph iprophs i :
    untangle (iproph :: iprophs) i = if decide (iproph.1 = i) then [iproph.2] ++ untangle iprophs i else untangle iprophs i.
  Proof.
    rewrite /untangle filter_cons //.
    case_decide; done.
  Qed.
  #[local] Lemma untangle_cons_True iproph iprophs i :
    iproph.1 = i →
    untangle (iproph :: iprophs) i = [iproph.2] ++ untangle iprophs i.
  Proof.
    intros <-.
    rewrite untangle_cons decide_True //.
  Qed.
  #[local] Lemma untangle_cons_False iproph iprophs i :
    iproph.1 ≠ i →
    untangle (iproph :: iprophs) i = untangle iprophs i.
  Proof.
    intros Hiproph.
    rewrite untangle_cons decide_False //.
  Qed.
  #[local] Lemma untangle_app iprophs1 iprophs2 i :
    untangle (iprophs1 ++ iprophs2) i = untangle iprophs1 i ++ untangle iprophs2 i.
  Proof.
    rewrite /untangle filter_app fmap_app //.
  Qed.
  #[local] Lemma untangle_snoc iprophs iproph i :
    untangle (iprophs ++ [iproph]) i = if decide (iproph.1 = i) then untangle iprophs i ++ [iproph.2] else untangle iprophs i.
  Proof.
    rewrite untangle_app /untangle filter_cons filter_nil //.
    case_decide; rewrite ?right_id //.
  Qed.
  #[local] Lemma untangle_snoc_True iprophs iproph i :
    iproph.1 = i →
    untangle (iprophs ++ [iproph]) i = untangle iprophs i ++ [iproph.2].
  Proof.
    intros <-.
    rewrite untangle_snoc decide_True //.
  Qed.
  #[local] Lemma untangle_snoc_False iprophs iproph i :
    iproph.1 ≠ i →
    untangle (iprophs ++ [iproph]) i = untangle iprophs i.
  Proof.
    intros Hiproph.
    rewrite untangle_snoc decide_False //.
  Qed.

  Definition prophet_multi_full γ i prophs : iProp Σ :=
    ∃ iprophs,
    ⌜prophs = untangle iprophs i⌝ ∗
    prophet_wise_full prophetx γ iprophs.
  #[local] Instance : CustomIpat "full" :=
    " ( %iprophs{}
      & ->
      & Hfull{}
      )
    ".

  Definition prophet_multi_model pid γ pasts prophss : iProp Σ :=
    ∃ ipast iprophs,
    ⌜pasts ≡ᶠ untangle ipast⌝ ∗
    ⌜prophss ≡ᶠ untangle iprophs⌝ ∗
    prophet_wise_model prophetx pid γ ipast iprophs.
  #[local] Instance : CustomIpat "model" :=
    " ( %ipast{}
      & %iprophs{}
      & %Hpasts{}
      & %Hprophss{}
      & Hmodel{}
      )
    ".

  Definition prophet_multi_snapshot γ i past prophs : iProp Σ :=
    ∃ ipast iprophs,
    ⌜past = untangle ipast i⌝ ∗
    ⌜prophs = untangle iprophs i⌝ ∗
    prophet_wise_snapshot prophetx γ ipast iprophs.
  #[local] Instance : CustomIpat "snapshot" :=
    " ( %ipast{_{suff}}
      & %iprophs{_{suff}}
      & ->
      & ->
      & Hsnapshot
      )
    ".

  Definition prophet_multi_lb γ i lb : iProp Σ :=
    ∃ past,
    prophet_multi_snapshot γ i past lb.
  #[local] Instance : CustomIpat "lb" :=
    " ( %past
      & Hsnapshot
      )
    ".

  #[global] Instance prophet_multi_full_timeless γ i prophs :
    Timeless (prophet_multi_full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_model_timeless pid γ pasts prophss :
    Timeless (prophet_multi_model pid γ pasts prophss).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_snapshot_timeless γ i past prophs :
    Timeless (prophet_multi_snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_lb_timeless γ i lb :
    Timeless (prophet_multi_lb γ i lb).
  Proof.
    apply _.
  Qed.

  #[global] Instance prophet_multi_full_persistent γ i prophs :
    Persistent (prophet_multi_full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_snapshot_persistent γ i past prophs :
    Persistent (prophet_multi_snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_lb_persistent γ i lb :
    Persistent (prophet_multi_lb γ i lb).
  Proof.
    apply _.
  Qed.

  Lemma prophet_multi_model_exclusive pid γ1 pasts1 prophss1 γ2 pasts2 prophss2 :
    prophet_multi_model pid γ1 pasts1 prophss1 -∗
    prophet_multi_model pid γ2 pasts2 prophss2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_wise_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_multi_full_get {pid γ pasts prophss} i :
    prophet_multi_model pid γ pasts prophss ⊢
    prophet_multi_full γ i (pasts i ++ prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (prophet_wise_full_get with "Hmodel") as "$".
    rewrite Hpasts Hprophss untangle_app //.
  Qed.
  Lemma prophet_multi_full_get' {pid γ pasts prophss} i :
    prophet_multi_model pid γ pasts prophss ⊢
      ∃ prophs,
      prophet_multi_full γ i prophs.
  Proof.
    rewrite prophet_multi_full_get. iSteps.
  Qed.
  Lemma prophet_multi_full_valid pid γ pasts prophss i prophs :
    prophet_multi_model pid γ pasts prophss -∗
    prophet_multi_full γ i prophs -∗
    ⌜prophs = pasts i ++ prophss i⌝.
  Proof.
    iIntros "(:model =1) (:full =2)". simplify.
    iDestruct (prophet_wise_full_valid with "Hmodel1 Hfull2") as %->.
    rewrite Hpasts1 Hprophss1 untangle_app //.
  Qed.
  Lemma prophet_multi_full_agree γ i prophs1 prophs2 :
    prophet_multi_full γ i prophs1 -∗
    prophet_multi_full γ i prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    iIntros "(:full =1) (:full =2)". simplify.
    iDestruct (prophet_wise_full_agree with "Hfull1 Hfull2") as %->.
    iSteps.
  Qed.

  Lemma prophet_multi_snapshot_get {pid γ pasts prophss} i :
    prophet_multi_model pid γ pasts prophss ⊢
    prophet_multi_snapshot γ i (pasts i) (prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (prophet_wise_snapshot_get with "Hmodel") as "$".
    iSteps.
  Qed.
  Lemma prophet_multi_snapshot_valid pid γ pasts prophss i past prophs :
    prophet_multi_model pid γ pasts prophss -∗
    prophet_multi_snapshot γ i past prophs -∗
      ∃ past',
      ⌜pasts i = past ++ past'⌝ ∗
      ⌜prophs = past' ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:snapshot suff=)".
    iDestruct (prophet_wise_snapshot_valid with "Hmodel Hsnapshot") as "(%ipast' & -> & ->)".
    iExists (untangle ipast' i). iSplit; iPureIntro.
    all: rewrite ?Hpasts ?Hprophss untangle_app //.
  Qed.

  Lemma prophet_multi_lb_get {pid γ pasts prophss} i :
    prophet_multi_model pid γ pasts prophss ⊢
    prophet_multi_lb γ i (prophss i).
  Proof.
    rewrite (prophet_multi_snapshot_get i).
    iIntros "Hsnapshot".
    iExists _. iFrame.
  Qed.
  Lemma prophet_multi_lb_valid pid γ pasts prophss i lb :
    prophet_multi_model pid γ pasts prophss -∗
    prophet_multi_lb γ i lb -∗
      ∃ past1 past2,
      ⌜pasts i = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophss i⌝.
  Proof.
    iIntros "Hmodel (:lb)".
    iExists past.
    iApply (prophet_multi_snapshot_valid with "Hmodel Hsnapshot").
  Qed.

  Lemma prophet_multi_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{
      pid γ prophss
    , RET #pid;
      prophet_multi_model pid γ (λ _, []) prophss
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (prophet_wise_wp_proph prophetx with "[//]") as (pid γ iprophs) "Hmodel".
    iApply "HΦ".
    iExists [], iprophs. rewrite /funeq. iSteps.
  Qed.

  Lemma prophet_multi_wp_resolve e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    (0 ≤ i)%Z →
    prophet_multi_model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed_of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          prophet_multi_model pid γ pasts prophss -∗
          Φ w
      | Some proph =>
          ∀ prophs,
          ⌜prophss ₊i = proph :: prophs⌝ -∗
          prophet_multi_model pid γ (alter (.++ [proph]) ₊i pasts) (<[₊i := prophs]> prophss) -∗
          Φ w
      end
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros "% % %Hi (:model) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    wp_apply (prophet_wise_wp_resolve with "Hmodel"); first done.
    wp_apply (wp_wand with "HΦ") as (w) "(%oproph & %Hoproph & HΦ)".
    iEval (rewrite /= Hoproph /=).
    destruct oproph as [proph |]. 2: iSteps.
    iExists (Some (i, proph)). iSplit.
    - iPureIntro. rewrite Nat2Z.id //.
    - iIntros "%iprophs' -> Hmodel".
      iApply ("HΦ" $! (untangle iprophs' i)).
      + iPureIntro. rewrite Hprophss untangle_cons_True //.
      + iExists _, _. iFrame. iSplit; iPureIntro; intros j.
        * rewrite function.fn_lookup_alter untangle_snoc Hpasts /=.
          case_decide; subst; done.
        * rewrite function.fn_lookup_insert Hprophss untangle_cons /=.
          case_decide; subst; done.
  Qed.
  Lemma prophet_multi_wp_resolve' e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    prophet_multi_model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed_of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          prophet_multi_model pid γ pasts prophss -∗
          Φ w
      | Some proph =>
          ∀ prophs,
          ⌜prophss i = proph :: prophs⌝ -∗
          prophet_multi_model pid γ (alter (.++ [proph]) i pasts) (<[i := prophs]> prophss) -∗
          Φ w
      end
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros "% % Hmodel HΦ".
    iApply (prophet_multi_wp_resolve with "Hmodel"); [done | lia |].
    rewrite Nat2Z.id. iSteps.
  Qed.
End prophet_multi_G.

#[global] Opaque prophet_multi_name.
#[global] Opaque prophet_multi_full.
#[global] Opaque prophet_multi_model.
#[global] Opaque prophet_multi_snapshot.
#[global] Opaque prophet_multi_lb.
