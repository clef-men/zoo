From zoo Require Import
  prelude.
From zoo.common Require Import
  function.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  wise_prophet.
From zoo.diaframe Require Import
  diaframe.
From zoo Require Import
  options.

#[local] Program Definition prophetx prophet := {|
  typed_strong_prophet_type :=
    nat * prophet.(typed_strong_prophet_type) ;
  typed_strong_prophet_of_val v1 v2 :=
    match v2 with
    | ValBlock _ _ [ValInt i; v2] =>
        proph ← prophet.(typed_strong_prophet_of_val) v1 v2 ;
        Some (₊i, proph)
    | _ =>
        None
    end ;
  typed_strong_prophet_to_val '(i, proph) :=
    let '(v1, v2) := prophet.(typed_strong_prophet_to_val) proph in
    (v1, (ValNat i, v2)%V)
|}.
Solve Obligations of prophetx with
  try done.
Next Obligation.
  intros prophet (i, proph) ? ? => /=.
  destruct (prophet.(typed_strong_prophet_to_val) proph) as (v1, v2) eqn:Heq.
  intros [= -> ->].
  erewrite prophet.(typed_strong_prophet_of_to_val); last done.
  rewrite Nat2Z.id //.
Qed.

Class WiseStrongProphetsG Σ `{zoo_G : !ZooG Σ} prophet := {
  #[local] wise_strong_prophets_G :: WiseStrongProphetG Σ (prophetx prophet) ;
}.

Definition wise_strong_prophets_Σ prophet := #[
  wise_strong_prophet_Σ (prophetx prophet)
].
#[global] Instance subG_wise_strong_prophets_Σ Σ `{zoo_G : !ZooG Σ} prophet :
  subG (wise_strong_prophets_Σ prophet) Σ →
  WiseStrongProphetsG Σ prophet.
Proof.
  solve_inG.
Qed.

Section wise_prophets_G.
  Context (prophet : typed_strong_prophet).
  Context `{wise_prophets_G : WiseStrongProphetsG Σ prophet}.

  Notation prophetx := (
    prophetx prophet
  ).

  Implicit Types prophs : list (prophet.(typed_strong_prophet_type)).
  Implicit Types ipast iprophs : list (nat * prophet.(typed_strong_prophet_type)).
  Implicit Types pasts prophss : nat → list prophet.(typed_strong_prophet_type).

  Definition wise_strong_prophets_name :=
    wise_strong_prophet_name.
  Implicit Types γ : wise_strong_prophets_name.

  #[global] Instance wise_strong_prophets_name_eq_dec : EqDecision wise_strong_prophet_name :=
    ltac:(apply _).
  #[global] Instance wise_strong_prophets_name_countable :
    Countable wise_strong_prophet_name.
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

  Definition wise_strong_prophets_full γ i prophs : iProp Σ :=
    ∃ iprophs,
    ⌜prophs = untangle iprophs i⌝ ∗
    wise_strong_prophet_full prophetx γ iprophs.
  #[local] Instance : CustomIpatFormat "full" :=
    "(
      %iprophs{_{suff}} &
      -> &
      Hfull
    )".

  Definition wise_strong_prophets_model pid γ pasts prophss : iProp Σ :=
    ∃ ipast iprophs,
    ⌜pasts ≡ᶠ untangle ipast⌝ ∗
    ⌜prophss ≡ᶠ untangle iprophs⌝ ∗
    wise_strong_prophet_model prophetx pid γ ipast iprophs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %ipast{} &
      %iprophs{} &
      %Hpasts{} &
      %Hprophss{} &
      Hmodel{}
    )".

  Definition wise_strong_prophets_snapshot γ i past prophs : iProp Σ :=
    ∃ ipast iprophs,
    ⌜past = untangle ipast i⌝ ∗
    ⌜prophs = untangle iprophs i⌝ ∗
    wise_strong_prophet_snapshot prophetx γ ipast iprophs.
  #[local] Instance : CustomIpatFormat "snapshot" :=
    "(
      %ipast{_{suff}} &
      %iprophs{_{suff}} &
      -> &
      -> &
      Hsnapshot
    )".

  Definition wise_strong_prophets_lb γ i lb : iProp Σ :=
    ∃ past,
    wise_strong_prophets_snapshot γ i past lb.
  #[local] Instance : CustomIpatFormat "lb" :=
    "(
      %past &
      Hsnapshot
    )".

  #[global] Instance wise_strong_prophets_full_timeless γ i prophs :
    Timeless (wise_strong_prophets_full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophets_model_timeless pid γ pasts prophss :
    Timeless (wise_strong_prophets_model pid γ pasts prophss).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophets_snapshot_timeless γ i past prophs :
    Timeless (wise_strong_prophets_snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophets_lb_timeless γ i lb :
    Timeless (wise_strong_prophets_lb γ i lb).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophets_full_persistent γ i prophs :
    Persistent (wise_strong_prophets_full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophets_snapshot_persistent γ i past prophs :
    Persistent (wise_strong_prophets_snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_strong_prophets_lb_persistent γ i lb :
    Persistent (wise_strong_prophets_lb γ i lb).
  Proof.
    apply _.
  Qed.

  Lemma wise_strong_prophets_model_exclusive pid γ1 pasts1 prophss1 γ2 pasts2 prophss2 :
    wise_strong_prophets_model pid γ1 pasts1 prophss1 -∗
    wise_strong_prophets_model pid γ2 pasts2 prophss2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (wise_strong_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma wise_strong_prophets_full_get {pid γ pasts prophss} i :
    wise_strong_prophets_model pid γ pasts prophss ⊢
    wise_strong_prophets_full γ i (pasts i ++ prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (wise_strong_prophet_full_get with "Hmodel") as "$".
    rewrite Hpasts Hprophss untangle_app //.
  Qed.
  Lemma wise_strong_prophets_full_valid pid γ pasts prophss i prophs :
    wise_strong_prophets_model pid γ pasts prophss -∗
    wise_strong_prophets_full γ i prophs -∗
    ⌜prophs = pasts i ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:full suff=)".
    iDestruct (wise_strong_prophet_full_valid with "Hmodel Hfull") as %->.
    rewrite Hpasts Hprophss untangle_app //.
  Qed.

  Lemma wise_strong_prophets_snapshot_get {pid γ pasts prophss} i :
    wise_strong_prophets_model pid γ pasts prophss ⊢
    wise_strong_prophets_snapshot γ i (pasts i) (prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (wise_strong_prophet_snapshot_get with "Hmodel") as "$".
    iSteps.
  Qed.
  Lemma wise_strong_prophets_snapshot_valid pid γ pasts prophss i past prophs :
    wise_strong_prophets_model pid γ pasts prophss -∗
    wise_strong_prophets_snapshot γ i past prophs -∗
      ∃ past',
      ⌜pasts i = past ++ past'⌝ ∗
      ⌜prophs = past' ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:snapshot suff=)".
    iDestruct (wise_strong_prophet_snapshot_valid with "Hmodel Hsnapshot") as "(%ipast' & -> & ->)".
    iExists (untangle ipast' i). iSplit; iPureIntro.
    all: rewrite ?Hpasts ?Hprophss untangle_app //.
  Qed.

  Lemma wise_strong_prophets_lb_get {pid γ pasts prophss} i :
    wise_strong_prophets_model pid γ pasts prophss ⊢
    wise_strong_prophets_lb γ i (prophss i).
  Proof.
    rewrite (wise_strong_prophets_snapshot_get i).
    iIntros "Hsnapshot".
    iExists _. iFrame.
  Qed.
  Lemma wise_strong_prophets_lb_valid pid γ pasts prophss i lb :
    wise_strong_prophets_model pid γ pasts prophss -∗
    wise_strong_prophets_lb γ i lb -∗
      ∃ past1 past2,
      ⌜pasts i = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophss i⌝.
  Proof.
    iIntros "Hmodel (:lb)".
    iExists past.
    iApply (wise_strong_prophets_snapshot_valid with "Hmodel Hsnapshot").
  Qed.

  Lemma wise_strong_prophets_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid γ prophss,
      RET #pid;
      wise_strong_prophets_model pid γ (λ _, []) prophss
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wise_strong_prophet_wp_proph prophetx with "[//]") as (pid γ iprophs) "Hmodel".
    iApply "HΦ".
    iExists [], iprophs. rewrite /funeq. iSteps.
  Qed.

  Lemma wise_strong_prophets_wp_resolve e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    (0 ≤ i)%Z →
    wise_strong_prophets_model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = prophet.(typed_strong_prophet_to_val) proph⌝ ∗
        ∀ prophs,
        ⌜prophss ₊i = proph :: prophs⌝ -∗
        wise_strong_prophets_model pid γ (alter (.++ [proph]) ₊i pasts) (<[₊i := prophs]> prophss) -∗
        Φ w
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros "% % %Hi (:model) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    wp_apply (wise_strong_prophet_wp_resolve with "Hmodel"); first done.
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
End wise_prophets_G.

#[global] Opaque wise_strong_prophets_name.
#[global] Opaque wise_strong_prophets_full.
#[global] Opaque wise_strong_prophets_model.
#[global] Opaque wise_strong_prophets_snapshot.
#[global] Opaque wise_strong_prophets_lb.

Class WiseProphetsG Σ `{zoo_G : !ZooG Σ} prophet := {
  #[local] wise_prophets_G :: WiseStrongProphetsG Σ prophet ;
}.

Definition wise_prophets_Σ prophet := #[
  wise_strong_prophets_Σ prophet
].
#[global] Instance subG_wise_prophets_Σ Σ `{zoo_G : !ZooG Σ} prophet :
  subG (wise_prophets_Σ prophet) Σ →
  WiseProphetsG Σ prophet.
Proof.
  solve_inG.
Qed.

Section wise_prophets_G.
  Context (prophet : typed_prophet).
  Context `{wise_prophets_G : WiseProphetsG Σ prophet}.

  Definition wise_prophets_name :=
    wise_strong_prophets_name.
  Implicit Types γ : wise_prophets_name.

  Definition wise_prophets_full γ i prophs : iProp Σ :=
    ∃ sprophs,
    ⌜prophs = sprophs.*2⌝ ∗
    wise_strong_prophets_full prophet γ i sprophs.
  #[local] Instance : CustomIpatFormat "full" :=
    "(
      %sprophs{} &
      -> &
      Hfull
    )".

  Definition wise_prophets_model pid γ pasts prophss : iProp Σ :=
    ∃ spasts sprophss,
    ⌜pasts ≡ᶠ fmap snd ∘ spasts⌝ ∗
    ⌜prophss ≡ᶠ fmap snd ∘ sprophss⌝ ∗
    wise_strong_prophets_model prophet pid γ spasts sprophss.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %spasts{} &
      %sprophss{} &
      %Hpasts{} &
      %Hprophss{} &
      Hmodel{}
    )".

  Definition wise_prophets_snapshot γ i past prophs : iProp Σ :=
    ∃ spast sprophs,
    ⌜past = spast.*2⌝ ∗
    ⌜prophs = sprophs.*2⌝ ∗
    wise_strong_prophets_snapshot prophet γ i spast sprophs.
  #[local] Instance : CustomIpatFormat "snapshot" :=
    "(
      %spast{} &
      %sprophs{} &
      -> &
      -> &
      Hsnapshot
    )".

  Definition wise_prophets_lb γ i lb : iProp Σ :=
    ∃ slb,
    ⌜lb = slb.*2⌝ ∗
    wise_strong_prophets_lb prophet γ i slb.
  #[local] Instance : CustomIpatFormat "lb" :=
    "(
      %slb &
      -> &
      Hlb
    )".

  #[global] Instance wise_prophets_full_timeless γ i prophs :
    Timeless (wise_prophets_full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophets_model_timeless pid γ pasts prophss :
    Timeless (wise_prophets_model pid γ pasts prophss).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophets_snapshot_timeless γ i past prophs :
    Timeless (wise_prophets_snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophets_lb_timeless γ i lb :
    Timeless (wise_prophets_lb γ i lb).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophets_full_persistent γ i prophs :
    Persistent (wise_prophets_full γ i prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophets_snapshot_persistent γ i past prophs :
    Persistent (wise_prophets_snapshot γ i past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophets_lb_persistent γ i lb :
    Persistent (wise_prophets_lb γ i lb).
  Proof.
    apply _.
  Qed.

  Lemma wise_prophets_model_exclusive pid γ1 pasts1 prophss1 γ2 pasts2 prophss2 :
    wise_prophets_model pid γ1 pasts1 prophss1 -∗
    wise_prophets_model pid γ2 pasts2 prophss2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (wise_strong_prophets_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma wise_prophets_full_get {pid γ pasts prophss} i :
    wise_prophets_model pid γ pasts prophss ⊢
    wise_prophets_full γ i (pasts i ++ prophss i).
  Proof.
    iIntros "(:model)".
    iDestruct (wise_strong_prophets_full_get with "Hmodel") as "$".
    rewrite Hpasts Hprophss fmap_app //.
  Qed.
  Lemma wise_prophets_full_valid pid γ pasts prophss i prophs :
    wise_prophets_model pid γ pasts prophss -∗
    wise_prophets_full γ i prophs -∗
    ⌜prophs = pasts i ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:full suff=)".
    iDestruct (wise_strong_prophets_full_valid with "Hmodel Hfull") as %->.
    rewrite Hpasts Hprophss fmap_app //.
  Qed.

  Lemma wise_prophets_snapshot_get {pid γ pasts prophss} i :
    wise_prophets_model pid γ pasts prophss ⊢
    wise_prophets_snapshot γ i (pasts i) (prophss i).
  Proof.
    iIntros "(:model)".
    iSteps.
    iApply (wise_strong_prophets_snapshot_get with "Hmodel").
  Qed.
  Lemma wise_prophets_snapshot_valid pid γ pasts prophss i past prophs :
    wise_prophets_model pid γ pasts prophss -∗
    wise_prophets_snapshot γ i past prophs -∗
      ∃ past',
      ⌜pasts i = past ++ past'⌝ ∗
      ⌜prophs = past' ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:snapshot =')".
    iDestruct (wise_strong_prophets_snapshot_valid with "Hmodel Hsnapshot") as "(%spast'' & %Heq & ->)".
    iExists spast''.*2. iSplit; iPureIntro.
    all: rewrite ?Hpasts ?Hprophss /= ?Heq fmap_app //.
  Qed.

  Lemma wise_prophets_lb_get {pid γ pasts prophss} i :
    wise_prophets_model pid γ pasts prophss -∗
    wise_prophets_lb γ i (prophss i).
  Proof.
    iIntros "(:model)".
    iStep.
    iApply (wise_strong_prophets_lb_get with "Hmodel").
  Qed.
  Lemma wise_prophets_lb_valid pid γ pasts prophss i lb :
    wise_prophets_model pid γ pasts prophss -∗
    wise_prophets_lb γ i lb -∗
      ∃ past1 past2,
      ⌜pasts i = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophss i⌝.
  Proof.
    iIntros "(:model) (:lb)".
    iDestruct (wise_strong_prophets_lb_valid with "Hmodel Hlb") as "(%spast1 & %spast2 & %Heq & ->)".
    iExists spast1.*2, spast2.*2. iSplit; iPureIntro.
    all: rewrite ?Hpasts ?Hprophss /= ?Heq fmap_app //.
  Qed.

  Lemma wise_prophets_wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ pid γ prophss,
      RET #pid;
      wise_prophets_model pid γ (λ _, []) prophss
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wise_strong_prophets_wp_proph prophet with "[//]") as "%pid %γ %sprophss Hmodel".
    iApply "HΦ".
    iExists (λ _, []), sprophss. rewrite /funeq. iSteps.
  Qed.

  Lemma wise_prophets_wp_resolve proph e pid i v γ pasts prophss E Φ :
    Atomic e →
    to_val e = None →
    (0 ≤ i)%Z →
    v = prophet.(typed_prophet_to_val) proph →
    wise_prophets_model pid γ pasts prophss -∗
    WP e @ E {{ w,
      ∀ prophs,
      ⌜prophss ₊i = proph :: prophs⌝ -∗
      wise_prophets_model pid γ (alter (.++ [proph]) ₊i pasts) (<[₊i := prophs]> prophss) -∗
      Φ w
    }} -∗
    WP Resolve e #pid (#i, v)%V @ E {{ Φ }}.
  Proof.
    iIntros (? ? Hi ->) "(:model) HΦ".
    wp_apply (wise_strong_prophets_wp_resolve with "Hmodel"); [done.. |].
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
End wise_prophets_G.

#[global] Opaque wise_prophets_name.
#[global] Opaque wise_prophets_full.
#[global] Opaque wise_prophets_model.
#[global] Opaque wise_prophets_snapshot.
#[global] Opaque wise_prophets_lb.
