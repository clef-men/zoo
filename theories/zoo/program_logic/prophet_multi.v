From zoo Require Import
  prelude.
From zoo.common Require Import
  function.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  prophet_wise.
From zoo.diaframe Require Import
  diaframe.
From zoo Require Import
  options.

#[local] Program Definition prophetx prophet := {|
  prophet_typed_strong_type :=
    nat * prophet.(prophet_typed_strong_type) ;
  prophet_typed_strong_of_val v1 v2 :=
    match v2 with
    | ValBlock _ _ [ValInt i; v2] =>
        proph ← prophet.(prophet_typed_strong_of_val) v1 v2 ;
        Some (₊i, proph)
    | _ =>
        None
    end ;
  prophet_typed_strong_to_val '(i, proph) :=
    let '(v1, v2) := prophet.(prophet_typed_strong_to_val) proph in
    (v1, (ValNat i, v2)%V)
|}.
Solve Obligations of prophetx with
  try done.
Next Obligation.
  intros prophet (i, proph) ? ? => /=.
  destruct (prophet.(prophet_typed_strong_to_val) proph) as (v1, v2) eqn:Heq.
  intros [= -> ->].
  erewrite prophet.(prophet_typed_strong_of_to_val); last done.
  rewrite Nat2Z.id //.
Qed.

Class ProphetMultiStrongG Σ `{zoo_G : !ZooG Σ} prophet := {
  #[local] prophet_multi_strong_G :: ProphetWiseStrongG Σ (prophetx prophet) ;
}.

Definition prophet_multi_strong_Σ prophet := #[
  prophet_wise_strong_Σ (prophetx prophet)
].
#[global] Instance subG_prophet_multi_strong_Σ Σ `{zoo_G : !ZooG Σ} prophet :
  subG (prophet_multi_strong_Σ prophet) Σ →
  ProphetMultiStrongG Σ prophet.
Proof.
  solve_inG.
Qed.

Section prophet_multi_G.
  Context (prophet : prophet_typed_strong).
  Context `{prophet_multi_G : ProphetMultiStrongG Σ prophet}.

  Notation prophetx := (
    prophetx prophet
  ).

  Implicit Types prophs : list (prophet.(prophet_typed_strong_type)).
  Implicit Types ipast iprophs : list (nat * prophet.(prophet_typed_strong_type)).
  Implicit Types pasts prophss : nat → list prophet.(prophet_typed_strong_type).

  Definition prophet_multi_strong_name :=
    prophet_wise_strong_name.
  Implicit Types γ : prophet_multi_strong_name.

  #[global] Instance prophet_multi_strong_name_eq_dec : EqDecision prophet_wise_strong_name :=
    ltac:(apply _).
  #[global] Instance prophet_multi_strong_name_countable :
    Countable prophet_wise_strong_name.
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

  Definition prophet_multi_strong_full γ i prophs : iProp Σ :=
    ∃ iprophs,
    ⌜prophs = untangle iprophs i⌝ ∗
    prophet_wise_strong_full prophetx γ iprophs.
  #[local] Instance : CustomIpat "full" :=
    " ( %iprophs{} &
        -> &
        Hfull{}
      )
    ".

  Definition prophet_multi_strong_model pid γ pasts prophss : iProp Σ :=
    ∃ ipast iprophs,
    ⌜pasts ≡ᶠ untangle ipast⌝ ∗
    ⌜prophss ≡ᶠ untangle iprophs⌝ ∗
    prophet_wise_strong_model prophetx pid γ ipast iprophs.
  #[local] Instance : CustomIpat "model" :=
    " ( %ipast{} &
        %iprophs{} &
        %Hpasts{} &
        %Hprophss{} &
        Hmodel{}
      )
    ".

  Definition prophet_multi_strong_snapshot γ i past prophs : iProp Σ :=
    ∃ ipast iprophs,
    ⌜past = untangle ipast i⌝ ∗
    ⌜prophs = untangle iprophs i⌝ ∗
    prophet_wise_strong_snapshot prophetx γ ipast iprophs.
  #[local] Instance : CustomIpat "snapshot" :=
    " ( %ipast{_{suff}} &
        %iprophs{_{suff}} &
        -> &
        -> &
        Hsnapshot
      )
    ".

  Definition prophet_multi_strong_lb γ i lb : iProp Σ :=
    ∃ past,
    prophet_multi_strong_snapshot γ i past lb.
  #[local] Instance : CustomIpat "lb" :=
    " ( %past &
        Hsnapshot
      )
    ".

  #[global] Instance prophet_multi_strong_full_timeless γ i prophs :
    Timeless (prophet_multi_strong_full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_strong_model_timeless pid γ pasts prophss :
    Timeless (prophet_multi_strong_model pid γ pasts prophss).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_strong_snapshot_timeless γ i past prophs :
    Timeless (prophet_multi_strong_snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_strong_lb_timeless γ i lb :
    Timeless (prophet_multi_strong_lb γ i lb).
  Proof.
    apply _.
  Qed.

  #[global] Instance prophet_multi_strong_full_persistent γ i prophs :
    Persistent (prophet_multi_strong_full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_strong_snapshot_persistent γ i past prophs :
    Persistent (prophet_multi_strong_snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_multi_strong_lb_persistent γ i lb :
    Persistent (prophet_multi_strong_lb γ i lb).
  Proof.
    apply _.
  Qed.

  Lemma prophet_multi_strong_model_exclusive pid γ1 pasts1 prophss1 γ2 pasts2 prophss2 :
    prophet_multi_strong_model pid γ1 pasts1 prophss1 -∗
    prophet_multi_strong_model pid γ2 pasts2 prophss2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_wise_strong_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_multi_strong_full_get {pid γ pasts prophss} i :
    prophet_multi_strong_model pid γ pasts prophss ⊢
    prophet_multi_strong_full γ i (pasts i ++ prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (prophet_wise_strong_full_get with "Hmodel") as "$".
    rewrite Hpasts Hprophss untangle_app //.
  Qed.
  Lemma prophet_multi_strong_full_get' {pid γ pasts prophss} i :
    prophet_multi_strong_model pid γ pasts prophss ⊢
      ∃ prophs,
      prophet_multi_strong_full γ i prophs.
  Proof.
    rewrite prophet_multi_strong_full_get. iSteps.
  Qed.
  Lemma prophet_multi_strong_full_valid pid γ pasts prophss i prophs :
    prophet_multi_strong_model pid γ pasts prophss -∗
    prophet_multi_strong_full γ i prophs -∗
    ⌜prophs = pasts i ++ prophss i⌝.
  Proof.
    iIntros "(:model =1) (:full =2)". simplify.
    iDestruct (prophet_wise_strong_full_valid with "Hmodel1 Hfull2") as %->.
    rewrite Hpasts1 Hprophss1 untangle_app //.
  Qed.
  Lemma prophet_multi_strong_full_agree γ i prophs1 prophs2 :
    prophet_multi_strong_full γ i prophs1 -∗
    prophet_multi_strong_full γ i prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    iIntros "(:full =1) (:full =2)". simplify.
    iDestruct (prophet_wise_strong_full_agree with "Hfull1 Hfull2") as %->.
    iSteps.
  Qed.

  Lemma prophet_multi_strong_snapshot_get {pid γ pasts prophss} i :
    prophet_multi_strong_model pid γ pasts prophss ⊢
    prophet_multi_strong_snapshot γ i (pasts i) (prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (prophet_wise_strong_snapshot_get with "Hmodel") as "$".
    iSteps.
  Qed.
  Lemma prophet_multi_strong_snapshot_valid pid γ pasts prophss i past prophs :
    prophet_multi_strong_model pid γ pasts prophss -∗
    prophet_multi_strong_snapshot γ i past prophs -∗
      ∃ past',
      ⌜pasts i = past ++ past'⌝ ∗
      ⌜prophs = past' ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:snapshot suff=)".
    iDestruct (prophet_wise_strong_snapshot_valid with "Hmodel Hsnapshot") as "(%ipast' & -> & ->)".
    iExists (untangle ipast' i). iSplit; iPureIntro.
    all: rewrite ?Hpasts ?Hprophss untangle_app //.
  Qed.

  Lemma prophet_multi_strong_lb_get {pid γ pasts prophss} i :
    prophet_multi_strong_model pid γ pasts prophss ⊢
    prophet_multi_strong_lb γ i (prophss i).
  Proof.
    rewrite (prophet_multi_strong_snapshot_get i).
    iIntros "Hsnapshot".
    iExists _. iFrame.
  Qed.
  Lemma prophet_multi_strong_lb_valid pid γ pasts prophss i lb :
    prophet_multi_strong_model pid γ pasts prophss -∗
    prophet_multi_strong_lb γ i lb -∗
      ∃ past1 past2,
      ⌜pasts i = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophss i⌝.
  Proof.
    iIntros "Hmodel (:lb)".
    iExists past.
    iApply (prophet_multi_strong_snapshot_valid with "Hmodel Hsnapshot").
  Qed.

  Lemma prophet_multi_strong_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid γ prophss,
      RET #pid;
      prophet_multi_strong_model pid γ (λ _, []) prophss
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (prophet_wise_strong_wp_proph prophetx with "[//]") as (pid γ iprophs) "Hmodel".
    iApply "HΦ".
    iExists [], iprophs. rewrite /funeq. iSteps.
  Qed.

  Lemma prophet_multi_strong_wp_resolve e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    (0 ≤ i)%Z →
    prophet_multi_strong_model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = prophet.(prophet_typed_strong_to_val) proph⌝ ∗
        ∀ prophs,
        ⌜prophss ₊i = proph :: prophs⌝ -∗
        prophet_multi_strong_model pid γ (alter (.++ [proph]) ₊i pasts) (<[₊i := prophs]> prophss) -∗
        Φ w
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros "% % %Hi (:model) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    wp_apply (prophet_wise_strong_wp_resolve with "Hmodel"); first done.
    wp_apply (wp_wand with "HΦ") as (w) "(%proph & %Hproph & HΦ)".
    iExists (i, proph). iSplit.
    - iPureIntro. rewrite /= -Hproph //.
    - iIntros "%iprophs' -> Hmodel".
      iApply ("HΦ" $! (untangle iprophs' i)).
      + iPureIntro. rewrite Hprophss untangle_cons_True //.
      + iExists _, _. iFrame. iSplit; iPureIntro; intros j.
        * rewrite function.fn_lookup_alter untangle_snoc Hpasts /=.
          case_decide; subst; done.
        * rewrite function.fn_lookup_insert Hprophss untangle_cons /=.
          case_decide; subst; done.
  Qed.
  Lemma prophet_multi_strong_wp_resolve' e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    prophet_multi_strong_model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = prophet.(prophet_typed_strong_to_val) proph⌝ ∗
        ∀ prophs,
        ⌜prophss i = proph :: prophs⌝ -∗
        prophet_multi_strong_model pid γ (alter (.++ [proph]) i pasts) (<[i := prophs]> prophss) -∗
        Φ w
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros "% % Hmodel HΦ".
    iApply (prophet_multi_strong_wp_resolve with "Hmodel"); [done | lia |].
    rewrite Nat2Z.id. iSteps.
  Qed.
End prophet_multi_G.

#[global] Opaque prophet_multi_strong_name.
#[global] Opaque prophet_multi_strong_full.
#[global] Opaque prophet_multi_strong_model.
#[global] Opaque prophet_multi_strong_snapshot.
#[global] Opaque prophet_multi_strong_lb.

Class ProphetMultiG Σ `{zoo_G : !ZooG Σ} prophet := {
  #[local] prophet_multi_G :: ProphetMultiStrongG Σ prophet ;
}.

Definition prophet_multi_Σ prophet := #[
  prophet_multi_strong_Σ prophet
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

  Implicit Types spasts sprophss : nat → list (val * prophet.(prophet_typed_type)).

  Definition prophet_multi_name :=
    prophet_multi_strong_name.
  Implicit Types γ : prophet_multi_name.

  Definition prophet_multi_full γ i prophs : iProp Σ :=
    ∃ sprophs,
    ⌜prophs = sprophs.*2⌝ ∗
    prophet_multi_strong_full prophet γ i sprophs.
  #[local] Instance : CustomIpat "full" :=
    " ( %sprophs{} &
        -> &
        Hfull{}
      )
    ".

  Definition prophet_multi_model pid γ pasts prophss : iProp Σ :=
    ∃ spasts sprophss,
    ⌜pasts ≡ᶠ fmap snd ∘ spasts⌝ ∗
    ⌜prophss ≡ᶠ fmap snd ∘ sprophss⌝ ∗
    prophet_multi_strong_model prophet pid γ spasts sprophss.
  #[local] Instance : CustomIpat "model" :=
    " ( %spasts{} &
        %sprophss{} &
        %Hpasts{} &
        %Hprophss{} &
        Hmodel{}
      )
    ".

  Definition prophet_multi_snapshot γ i past prophs : iProp Σ :=
    ∃ spast sprophs,
    ⌜past = spast.*2⌝ ∗
    ⌜prophs = sprophs.*2⌝ ∗
    prophet_multi_strong_snapshot prophet γ i spast sprophs.
  #[local] Instance : CustomIpat "snapshot" :=
    " ( %spast{} &
        %sprophs{} &
        -> &
        -> &
        Hsnapshot
      )
    ".

  Definition prophet_multi_lb γ i lb : iProp Σ :=
    ∃ slb,
    ⌜lb = slb.*2⌝ ∗
    prophet_multi_strong_lb prophet γ i slb.
  #[local] Instance : CustomIpat "lb" :=
    " ( %slb &
        -> &
        Hlb
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
    iApply (prophet_multi_strong_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_multi_full_get {pid γ pasts prophss} i :
    prophet_multi_model pid γ pasts prophss ⊢
    prophet_multi_full γ i (pasts i ++ prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (prophet_multi_strong_full_get with "Hmodel") as "$".
    rewrite Hpasts Hprophss fmap_app //.
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
    iDestruct (prophet_multi_strong_full_valid with "Hmodel1 Hfull2") as %->.
    rewrite Hpasts1 Hprophss1 fmap_app //.
  Qed.
  Lemma prophet_multi_full_agree γ i prophs1 prophs2 :
    prophet_multi_full γ i prophs1 -∗
    prophet_multi_full γ i prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    iIntros "(:full =1) (:full =2)". simplify.
    iDestruct (prophet_multi_strong_full_agree with "Hfull1 Hfull2") as %->.
    iSteps.
  Qed.

  Lemma prophet_multi_snapshot_get {pid γ pasts prophss} i :
    prophet_multi_model pid γ pasts prophss ⊢
    prophet_multi_snapshot γ i (pasts i) (prophss i).
  Proof.
    iIntros "(:model)".
    iSteps.
    iApply (prophet_multi_strong_snapshot_get with "Hmodel").
  Qed.
  Lemma prophet_multi_snapshot_valid pid γ pasts prophss i past prophs :
    prophet_multi_model pid γ pasts prophss -∗
    prophet_multi_snapshot γ i past prophs -∗
      ∃ past',
      ⌜pasts i = past ++ past'⌝ ∗
      ⌜prophs = past' ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:snapshot =')".
    iDestruct (prophet_multi_strong_snapshot_valid with "Hmodel Hsnapshot") as "(%spast'' & %Heq & ->)".
    iExists spast''.*2. iSplit; iPureIntro.
    all: rewrite ?Hpasts ?Hprophss /= ?Heq fmap_app //.
  Qed.

  Lemma prophet_multi_lb_get {pid γ pasts prophss} i :
    prophet_multi_model pid γ pasts prophss -∗
    prophet_multi_lb γ i (prophss i).
  Proof.
    iIntros "(:model)".
    iStep.
    iApply (prophet_multi_strong_lb_get with "Hmodel").
  Qed.
  Lemma prophet_multi_lb_valid pid γ pasts prophss i lb :
    prophet_multi_model pid γ pasts prophss -∗
    prophet_multi_lb γ i lb -∗
      ∃ past1 past2,
      ⌜pasts i = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:lb)".
    iDestruct (prophet_multi_strong_lb_valid with "Hmodel Hlb") as "(%spast1 & %spast2 & %Heq & ->)".
    iExists spast1.*2, spast2.*2. iSplit; iPureIntro.
    all: rewrite ?Hpasts ?Hprophss /= ?Heq fmap_app //.
  Qed.

  Lemma prophet_multi_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid γ prophss,
      RET #pid;
      prophet_multi_model pid γ (λ _, []) prophss
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (prophet_multi_strong_wp_proph prophet with "[//]") as "%pid %γ %sprophss Hmodel".
    iApply "HΦ".
    iExists (λ _, []), sprophss. rewrite /funeq. iSteps.
  Qed.

  Lemma prophet_multi_wp_resolve proph e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    (0 ≤ i)%Z →
    v = prophet.(prophet_typed_to_val) proph →
    prophet_multi_model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∀ prophs,
      ⌜prophss ₊i = proph :: prophs⌝ -∗
      prophet_multi_model pid γ (alter (.++ [proph]) ₊i pasts) (<[₊i := prophs]> prophss) -∗
      Φ w
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros (? ? Hi ->) "(:model) HΦ".
    wp_apply (prophet_multi_strong_wp_resolve with "Hmodel"); [done.. |].
    wp_apply (wp_wand with "HΦ") as "%w HΦ".
    iExists (w, proph). iStep. iIntros "%sprophs %Heq Hmodel".
    iApply ("HΦ" with "[%]").
    { rewrite Hprophss /= Heq //. }
    iExists _, _. iFrame. iSplit; iPureIntro; intros j.
    - rewrite /= !function.fn_lookup_alter /=.
      case_decide; last done. rewrite fmap_app Hpasts //.
    - rewrite /= !function.fn_lookup_insert /=.
      case_decide; done.
  Qed.
  Lemma prophet_multi_wp_resolve' proph e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    v = prophet.(prophet_typed_to_val) proph →
    prophet_multi_model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∀ prophs,
      ⌜prophss i = proph :: prophs⌝ -∗
      prophet_multi_model pid γ (alter (.++ [proph]) i pasts) (<[i := prophs]> prophss) -∗
      Φ w
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros "% % % Hmodel HΦ".
    iApply (prophet_multi_wp_resolve with "Hmodel"); [done | lia | done |].
    rewrite Nat2Z.id. iSteps.
  Qed.
End prophet_multi_G.

#[global] Opaque prophet_multi_name.
#[global] Opaque prophet_multi_full.
#[global] Opaque prophet_multi_model.
#[global] Opaque prophet_multi_snapshot.
#[global] Opaque prophet_multi_lb.
