Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.function.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_nat.
Require Import zoo_std.option.
Require Export zoo_saturn.inf_queue_mpmc_1__code.
Require Import zoo_saturn.inf_queue_mpmc_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type front back : nat.
Implicit Type v : val.
Implicit Type vs hist : list val.
Implicit Type slot : optional val.
Implicit Type slots : nat → optional val.
Implicit Type η : gname.
Implicit Type ηs : list gname.

Class InfQueueMpmc1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] inf_queue_mpmc_1۰G۰inf_array۰G :: InfArrayG Σ
  ; #[local] inf_queue_mpmc_1۰G۰model۰G :: TwinsG Σ (leibnizO (list val))
  ; #[local] inf_queue_mpmc_1۰G۰history۰G :: MonoListG Σ val
  ; #[local] inf_queue_mpmc_1۰G۰consumer۰G :: SavedPredG Σ val
  ; #[local] inf_queue_mpmc_1۰G۰consumers۰G :: MonoListG Σ gname
  ; #[local] inf_queue_mpmc_1۰G۰token۰G :: OneshotG Σ () ()
  ; #[local] inf_queue_mpmc_1۰G۰tokens۰G :: MonoListG Σ gname
  }.

Definition inf_queue_mpmc_1۰Σ :=
  #[inf_array۰Σ
  ; twins۰Σ (leibnizO (list val))
  ; mono_list۰Σ val
  ; saved_pred۰Σ val
  ; mono_list۰Σ gname
  ; oneshot۰Σ () ()
  ; mono_list۰Σ gname
  ].
#[global] Instance subGｰinf_queue_mpmc_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG inf_queue_mpmc_1۰Σ Σ →
  InfQueueMpmc1G Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section inf_queue_mpmc_1۰G.
    Context `{inf_queue_mpmc_1۰G : InfQueueMpmc1G Σ}.

    Implicit Type t : location.
    Implicit Type Ψ : val → iProp Σ.

    Record inf_queue_mpmc_1۰name :=
      { inf_queue_mpmc_1۰name۰data : val
      ; inf_queue_mpmc_1۰name۰inv : namespace
      ; inf_queue_mpmc_1۰name۰model : gname
      ; inf_queue_mpmc_1۰name۰history : gname
      ; inf_queue_mpmc_1۰name۰consumers : gname
      ; inf_queue_mpmc_1۰name۰tokens : gname
      }.
    Implicit Type γ : inf_queue_mpmc_1۰name.

    #[global] Instance inf_queue_mpmc_1۰nameｰeq_dec : EqDecision inf_queue_mpmc_1۰name :=
      ltac:(solve_decision).
    #[global] Instance inf_queue_mpmc_1۰nameｰcountable :
      Countable inf_queue_mpmc_1۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      twins۰twin₁ γ_model (DfracOwn 1) vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(inf_queue_mpmc_1۰name۰model).
    #[local] Definition model₂' γ_model vs :=
      twins۰twin₂ γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(inf_queue_mpmc_1۰name۰model).

    #[local] Definition history۰auth' γ_history hist :=
      mono_list۰auth γ_history (DfracOwn 1) hist.
    #[local] Definition history۰auth γ :=
      history۰auth' γ.(inf_queue_mpmc_1۰name۰history).
    #[local] Definition history۰at γ i v :=
      mono_list۰at γ.(inf_queue_mpmc_1۰name۰history) i v.

    #[local] Definition consumers۰auth' γ_consumers i : iProp Σ :=
      ∃ ηs,
      mono_list۰auth γ_consumers (DfracOwn 1) ηs ∗
      ⌜length ηs = i⌝.
    #[local] Definition consumers۰auth γ i :=
      consumers۰auth' γ.(inf_queue_mpmc_1۰name۰consumers) i.
    #[local] Instance : CustomIpat "consumers۰auth" :=
      " ( %ηs{}
        & Hauth{}
        & %Hηs{}
        )
      ".
    #[local] Definition consumers۰at γ i Ψ : iProp Σ :=
      ∃ η,
      mono_list۰at γ.(inf_queue_mpmc_1۰name۰consumers) i η ∗
      saved_pred η Ψ.
    #[local] Instance : CustomIpat "consumers۰at" :=
      " ( %η{}
        & Hat{}
        & HΨ{}
        )
      ".
    #[local] Definition consumers۰lb γ i : iProp Σ :=
      ∃ ηs,
      ⌜length ηs = i⌝ ∗
      mono_list۰lb γ.(inf_queue_mpmc_1۰name۰consumers) ηs.
    #[local] Instance : CustomIpat "consumers۰lb" :=
      " ( %ηs{}
        & %Hηs{}
        & Hlb{}
        )
      ".

    #[local] Definition tokens۰auth' γ_tokens i : iProp Σ :=
      ∃ ηs,
      mono_list۰auth γ_tokens (DfracOwn 1) ηs ∗
      ⌜length ηs = i⌝.
    #[local] Definition tokens۰auth γ i :=
      tokens۰auth' γ.(inf_queue_mpmc_1۰name۰tokens) i.
    #[local] Instance : CustomIpat "tokens۰auth" :=
      " ( %ηs{}
        & Hauth{}
        & %Hηs{}
        )
      ".
    #[local] Definition tokens۰pending γ i : iProp Σ :=
      ∃ η,
      mono_list۰at γ.(inf_queue_mpmc_1۰name۰tokens) i η ∗
      oneshot۰pending η (DfracOwn 1) ().
    #[local] Instance : CustomIpat "tokens۰pending" :=
      " ( %η{}
        & Hat{}
        & Hpending{}
        )
      ".
    #[local] Definition tokens۰done γ i : iProp Σ :=
      ∃ η,
      mono_list۰at γ.(inf_queue_mpmc_1۰name۰tokens) i η ∗
      oneshot۰shot η ().
    #[local] Instance : CustomIpat "tokens۰done" :=
      " ( %η{}
        & Hat{}
        & Hshot{}
        )
      ".

    #[local] Definition consumer۰au γ Ψ : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(inf_queue_mpmc_1۰name۰inv), ∅ <{
        ∀∀ v vs',
        ⌜vs = v :: vs'⌝ ∗
        model₁ γ vs'
      , COMM
        Ψ v
      }>.

    #[local] Definition slot۰model γ i slot : iProp Σ :=
      match slot with
      | Something v =>
          history۰at γ i v
      | Anything =>
          tokens۰done γ i
      | Nothing =>
          True
      end.
    #[local] Definition inv۰inner t γ : iProp Σ :=
      ∃ front back hist slots,
      t.[front] ↦ #front ∗
      t.[back] ↦ #back ∗
      inf_array۰model γ.(inf_queue_mpmc_1۰name۰data) (optional۰to_val ∘ slots) ∗
      history۰auth γ hist ∗
      ⌜length hist = back⌝ ∗
      model₂ γ (drop front hist) ∗
      consumers۰auth γ front ∗
      tokens۰auth γ (front `max` back) ∗
      ( [∗ list] i ∈ seq 0 back,
          tokens۰pending γ i
        ∨ ∃ Ψ,
          consumers۰at γ i Ψ ∗
          ( tokens۰done γ i
          ∨ ∃ v,
            history۰at γ i v ∗
            Ψ v
          )
      ) ∗
      ( [∗ list] i ∈ seq back (front - back),
        ∃ Ψ,
        consumers۰at γ i Ψ ∗
        consumer۰au γ Ψ
      ) ∗
      (∀ i, slot۰model γ i (slots i)).
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %front{}
        & %back{}
        & %hist{}
        & %slots{}
        & Ht_front
        & Ht_back
        & >Hdata_model
        & >Hhistory_auth
        & >%Hhist{}
        & Hmodel₂
        & Hconsumers_auth
        & Htokens_auth
        & Hpast
        & Hwaiters
        & Hslots
        )
      ".
    Definition inv' t γ : iProp Σ :=
      t.[data] ↦□ γ.(inf_queue_mpmc_1۰name۰data) ∗
      inf_array۰inv γ.(inf_queue_mpmc_1۰name۰data) ∗
      inv γ.(inf_queue_mpmc_1۰name۰inv) (inv۰inner t γ).
    #[local] Instance : CustomIpat "inv'" :=
      " ( #Ht_data
        & #Hdata_inv
        & #Hinv
        )
      ".
    Definition inf_queue_mpmc_1۰inv t γ ι : iProp Σ :=
      ⌜ι = γ.(inf_queue_mpmc_1۰name۰inv)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & (:inv')
        )
      ".

    Definition inf_queue_mpmc_1۰model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    #[local] Instance tokens۰pendingｰtimeless γ i :
      Timeless (tokens۰pending γ i).
    Proof.
      apply _.
    Qed.
    #[local] Instance tokens۰doneｰtimeless γ i :
      Timeless (tokens۰done γ i).
    Proof.
      apply _.
    Qed.
    #[local] Instance slot۰modelｰtimeless γ i slot :
      Timeless (slot۰model γ i slot).
    Proof.
      rewrite /slot۰model. apply _.
    Qed.
    #[global] Instance inf_queue_mpmc_1۰modelｰtimeless γ vs :
      Timeless (inf_queue_mpmc_1۰model γ vs).
    Proof.
      apply _.
    Qed.

    #[local] Instance consumers۰atｰpersistent γ i Ψ :
      Persistent (consumers۰at γ i Ψ).
    Proof.
      apply _.
    Qed.
    #[local] Instance consumers۰lbｰpersistent γ i :
      Persistent (consumers۰lb γ i).
    Proof.
      apply _.
    Qed.
    #[local] Instance tokens۰doneｰpersistent γ i :
      Persistent (tokens۰done γ i).
    Proof.
      apply _.
    Qed.
    #[local] Instance slot۰modelｰpersistent γ i slot :
      Persistent (slot۰model γ i slot).
    Proof.
      rewrite /slot۰model. apply _.
    Qed.
    #[global] Instance inf_queue_mpmc_1۰invｰpersistent t γ ι :
      Persistent (inf_queue_mpmc_1۰inv t γ ι).
    Proof.
      apply _.
    Qed.

    #[local] Lemma modelｰalloc :
      ⊢ |==>
        ∃ γ_model,
        model₁' γ_model [] ∗
        model₂' γ_model [].
    Proof.
      apply twinsｰalloc'.
    Qed.
    #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₁ γ vs2 -∗
      False.
    Proof.
      apply twins۰twin₁ｰexclusive.
    Qed.
    #[local] Lemma modelｰagree γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      apply: twinsｰagreeｰL.
    Qed.
    #[local] Lemma modelｰupdate {γ vs1 vs2} vs :
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        model₁ γ vs ∗
        model₂ γ vs.
    Proof.
      apply twinsｰupdate.
    Qed.

    #[local] Lemma historyｰalloc :
      ⊢ |==>
        ∃ γ_history,
        history۰auth' γ_history [].
    Proof.
      apply mono_listｰalloc.
    Qed.
    #[local] Lemma history۰atｰvalid γ hist i v :
      history۰auth γ hist -∗
      history۰at γ i v -∗
      ⌜hist !! i = Some v⌝.
    Proof.
      apply mono_list۰atｰvalid.
    Qed.
    #[local] Lemma history۰atｰagree γ i v1 v2 :
      history۰at γ i v1 -∗
      history۰at γ i v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply mono_list۰atｰagree.
    Qed.
    #[local] Lemma history۰atｰget {γ hist} i v :
      hist !! i = Some v →
      history۰auth γ hist ⊢
      history۰at γ i v.
    Proof.
      apply mono_list۰atｰget.
    Qed.
    #[local] Lemma historyｰupdate {γ hist} v :
      history۰auth γ hist ⊢ |==>
        history۰auth γ (hist ++ [v]) ∗
        history۰at γ (length hist) v.
    Proof.
      iIntros "Hhistory_auth".
      iMod (mono_listｰupdateｰsnoc v with "Hhistory_auth") as "Hhistory_auth".
      iDestruct (mono_list۰atｰget with "Hhistory_auth") as "#Hhistory_at".
      { rewrite list_lookup_middle //. }
      iSteps.
    Qed.

    #[local] Lemma consumersｰalloc :
      ⊢ |==>
        ∃ γ_consumers,
        consumers۰auth' γ_consumers 0.
    Proof.
      iMod mono_listｰalloc as "(%γ_consumers & Hauth)".
      iExists _, []. iSteps.
    Qed.
    #[local] Lemma consumers۰atｰvalid γ i j Ψ :
      consumers۰auth γ i -∗
      consumers۰at γ j Ψ -∗
      ⌜j < i⌝.
    Proof.
      iIntros "(:consumers۰auth) (:consumers۰at)".
      iDestruct (mono_list۰atｰvalid with "Hauth Hat") as %?Hj%lookup_lt_Some.
      iSteps.
    Qed.
    #[local] Lemma consumers۰atｰagree γ i Ψ1 Ψ2 v :
      consumers۰at γ i Ψ1 -∗
      ▷ consumers۰at γ i Ψ2 -∗
      ▷ Ψ2 v -∗
      ▷^2 Ψ1 v.
    Proof.
      iIntros "(:consumers۰at =1) (:consumers۰at =2) HΨ !>".
      iDestruct (mono_list۰atｰagree with "Hat1 Hat2") as %<-.
      iDestruct (saved_predｰagree v with "HΨ1 HΨ2") as "Heq".
      iModIntro. iRewrite "Heq". iSteps.
    Qed.
    #[local] Lemma consumers۰lbｰvalid γ i j :
      consumers۰auth γ i -∗
      consumers۰lb γ j -∗
      ⌜j ≤ i⌝.
    Proof.
      iIntros "(:consumers۰auth =1) (:consumers۰lb =2)".
      iDestruct (mono_list۰lbｰvalid with "Hauth1 Hlb2") as %?%prefix_length.
      iSteps.
    Qed.
    #[local] Lemma consumers۰lbｰget γ i :
      consumers۰auth γ i ⊢
      consumers۰lb γ i.
    Proof.
      iIntros "(:consumers۰auth)".
      iDestruct (mono_list۰lbｰget with "Hauth") as "Hlb".
      iSteps.
    Qed.
    #[local] Lemma consumersｰupdate {γ i} Ψ :
      consumers۰auth γ i ⊢ |==>
        consumers۰auth γ ˖i ∗
        consumers۰at γ i Ψ.
    Proof.
      iIntros "(:consumers۰auth)".
      iMod (saved_predｰalloc Ψ) as "(%η & HΨ)".
      iMod (mono_listｰupdateｰsnoc with "Hauth") as "Hauth".
      iDestruct (mono_list۰atｰget with "Hauth") as "#Hat".
      { rewrite list_lookup_middle //. }
      iFrame. simp_length. iSteps.
    Qed.
    Opaque consumers۰auth'.
    Opaque consumers۰at.
    Opaque consumers۰lb.

    #[local] Lemma tokensｰalloc :
      ⊢ |==>
        ∃ γ_tokens,
        tokens۰auth' γ_tokens 0.
    Proof.
      iMod mono_listｰalloc as "(%γ_tokens & Hauth)".
      iExists _, []. iSteps.
    Qed.
    #[local] Lemma tokens۰pendingｰexclusive γ i :
      tokens۰pending γ i -∗
      tokens۰pending γ i -∗
      False.
    Proof.
      iIntros "(:tokens۰pending =1) (:tokens۰pending =2)".
      iDestruct (mono_list۰atｰagree with "Hat1 Hat2") as %<-.
      iApply (oneshot۰pendingｰexclusive with "Hpending1 Hpending2").
    Qed.
    #[local] Lemma tokens۰pendingｰdone γ i :
      tokens۰pending γ i -∗
      tokens۰done γ i -∗
      False.
    Proof.
      iIntros "(:tokens۰pending =1) (:tokens۰done =2)".
      iDestruct (mono_list۰atｰagree with "Hat1 Hat2") as %<-.
      iApply (oneshotｰpendingｰshot with "Hpending1 Hshot2").
    Qed.
    #[local] Lemma tokensｰupdate {γ} i :
      tokens۰auth γ i ⊢ |==>
        tokens۰auth γ ˖i ∗
        tokens۰pending γ i.
    Proof.
      iIntros "(:tokens۰auth)".
      iMod oneshotｰalloc as "(%η & Hpending)".
      iMod (mono_listｰupdateｰsnoc with "Hauth") as "Hauth".
      iDestruct (mono_list۰atｰget with "Hauth") as "#Hat".
      { rewrite list_lookup_middle //. }
      iFrame. simp_length. iSteps.
    Qed.
    #[local] Lemma tokens۰pendingｰupdate γ i :
      tokens۰pending γ i ⊢ |==>
      tokens۰done γ i.
    Proof.
      iIntros "(:tokens۰pending)".
      iMod (oneshotｰupdateｰshot with "Hpending") as "Hshot".
      iSteps.
    Qed.
    Opaque tokens۰auth'.
    Opaque tokens۰pending.
    Opaque tokens۰done.

    Lemma inf_queue_mpmc_1۰modelｰexclusive γ vs1 vs2 :
      inf_queue_mpmc_1۰model γ vs1 -∗
      inf_queue_mpmc_1۰model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    Lemma inf_queue_mpmc_1٠createｰspec ι :
      {{{
        True
      }}}
        inf_queue_mpmc_1٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        inf_queue_mpmc_1۰inv t γ ι ∗
        inf_queue_mpmc_1۰model γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰apply (inf_array٠createｰspec with "[//]") as (data) "(#Hdata_inv & Hdata_model)".
      wp۰block t as "Hmeta" "#Ht_data Ht_front Ht_back".

      iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iMod historyｰalloc as "(%γ_history & Hhistory_auth)".
      iMod consumersｰalloc as "(%γ_consumers & Hconsumers_auth)".
      iMod tokensｰalloc as "(%γ_tokens & Htokens_auth)".

      pose γ :=
        {|inf_queue_mpmc_1۰name۰data := data
        ; inf_queue_mpmc_1۰name۰inv := ι
        ; inf_queue_mpmc_1۰name۰model := γ_model
        ; inf_queue_mpmc_1۰name۰history := γ_history
        ; inf_queue_mpmc_1۰name۰consumers := γ_consumers
        ; inf_queue_mpmc_1۰name۰tokens := γ_tokens
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (λ _, Nothing). iSteps.
    Qed.

    Lemma inf_queue_mpmc_1٠sizeｰspec t γ ι :
      <<<
        inf_queue_mpmc_1۰inv t γ ι
      | ∀∀ vs,
        inf_queue_mpmc_1۰model γ vs
      >>>
        inf_queue_mpmc_1٠size #t @ ↑ι
      <<<
        inf_queue_mpmc_1۰model γ vs
      | RET #(length vs);
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp۰rec.

      wp۰bind (_.{front})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (consumers۰lbｰget with "Hconsumers_auth") as "#Hconsumers_lb1".
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰apply+ (prophet_typed₁ｰwpｰproph prophet_nat₁ with "[//]") as (pid proph) "Hproph".
      wp۰pures.

      wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰load.
      destruct_decide (proph = front1) as -> | Hproph.

      - destruct_decide (front2 = front1) as -> | ?.

        + iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΦ" with "Hmodel₁ [//]") as "HΦ".

          iSplitR "Hproph HΦ". { iFrameSteps. }
          iIntros "!> {%- Hhist2}".

          wp۰pures.

          wp۰bind (_.{front})%E.
          iInv "Hinv" as "(:inv۰inner =3)".
          wp۰load.
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iIntros "!> {%- Hhist2}".

          wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
          iSteps.
          rewrite length_drop Hhist2 Z2Nat.inj_sub; first lia.
          rewrite !Nat2Z.id //.

        + iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hconsumers_lb1") as %?.
          iDestruct (consumers۰lbｰget with "Hconsumers_auth") as "#Hconsumers_lb2".
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iModIntro.

          wp۰pures.

          wp۰bind (_.{front})%E.
          iInv "Hinv" as "(:inv۰inner =3)".
          wp۰load.
          iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hconsumers_lb2") as %?.
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iModIntro.

          wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
          iSteps.

      - iSplitR "Hproph HΦ". { iFrameSteps. }
        iIntros "!> {%- Hproph}".

        wp۰pures.

        wp۰bind (_.{front})%E.
        iInv "Hinv" as "(:inv۰inner =3)".
        wp۰load.
        iSplitR "Hproph HΦ". { iFrameSteps. }
        iIntros "!> {%- Hproph}".

        wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
        iSteps.
    Qed.

    Lemma inf_queue_mpmc_1٠is_emptyｰspec t γ ι :
      <<<
        inf_queue_mpmc_1۰inv t γ ι
      | ∀∀ vs,
        inf_queue_mpmc_1۰model γ vs
      >>>
        inf_queue_mpmc_1٠is_empty #t @ ↑ι
      <<<
        inf_queue_mpmc_1۰model γ vs
      | RET #(bool_decide (vs = []%list));
        True
      >>>.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp۰rec.

      awp۰apply (inf_queue_mpmc_1٠sizeｰspec with "Hinv").
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; iSteps.
      destruct vs; iSteps.
    Qed.

    Lemma inf_queue_mpmc_1٠is_empty_weakｰspec t γ ι :
      <<<
        inf_queue_mpmc_1۰inv t γ ι
      | ∀∀ vs,
        inf_queue_mpmc_1۰model γ vs
      >>>
        inf_queue_mpmc_1٠is_empty_weak #t @ ↑ι
      <<<
        ∃∃ b,
        ⌜if b then vs = [] else True⌝ ∗
        inf_queue_mpmc_1۰model γ vs
      | RET #b;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec.

      wp۰bind (_.{front})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (consumers۰lbｰget with "Hconsumers_auth") as "#Hconsumers_lb".
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰pures.

      wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰load.

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.

      destruct_decide (back2 ≤ front1) as Hif.

      - iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hconsumers_lb") as %?.
        iMod ("HΦ" $! true with "[$Hmodel₁]") as "HΦ".
        { iPureIntro. rewrite skipn_all2 //. 1: lia. }

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hif}".

        wp۰pures.
        rewrite bool_decide_eq_true_2. 1: lia.
        iSteps.

      - iMod ("HΦ" $! false with "[$Hmodel₁]") as "HΦ".

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hif}".

        wp۰pures.
        rewrite bool_decide_eq_false_2. 1: lia.
        iSteps.
    Qed.

    Lemma inf_queue_mpmc_1٠pushｰspec t γ ι v :
      <<<
        inf_queue_mpmc_1۰inv t γ ι
      | ∀∀ vs,
        inf_queue_mpmc_1۰model γ vs
      >>>
        inf_queue_mpmc_1٠push #t v @ ↑ι
      <<<
        inf_queue_mpmc_1۰model γ (vs ++ [v])
      | RET ();
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec. wp۰pures.

      wp۰bind (𝗳𝗮𝗮 _ _)%E.
      wp۰apply (wpｰwand (λ res,
        ∃ back,
        ⌜res = #back⌝ ∗
        history۰at γ back v ∗
        Φ ()%V
      )%I with "[HΦ]") as (res) "(%back & -> & #Hhistory_at & HΦ)".
      { iInv "Hinv" as "(:inv۰inner =1)".
        wp۰faa.

        iMod (historyｰupdate v with "Hhistory_auth") as "(History_auth & #Hhistory_at)".
        iEval (rewrite Hhist1) in "Hhistory_at".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %Hvs.
        iMod (modelｰupdate (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "Hmodel₁ [//]") as "$".

        destruct_decide (front1 ≤ back1) as Hback1.

        - rewrite Nat.max_r //.

          iMod (tokensｰupdate with "Htokens_auth") as "(Htokens_auth & Htokens_at)".
          iDestruct (big_sepLｰseqｰsnoc₂ with "Hpast [$Htokens_at]") as "Hpast".

          iSplitL.
          { iExists front1, ˖back1. iFrame.
            simp_length.
            rewrite Hvs drop_app_le; first lia.
            rewrite Nat.max_r; first lia.
            assert (front1 - ˖back1 = 0) as -> by lia.
            iSteps.
          }
          iSteps.

        - rewrite Nat.max_l; first lia.
          rewrite (nil_length_inv vs).
          { rewrite Hvs length_drop. lia. }
          assert (front1 - back1 = ˖(front1 - ˖back1)) as ->; first lia.
          destruct (Nat.lt_exists_pred 0 (front1 - back1)) as (δ & ? & _); first lia.
          iDestruct (big_sepLｰseqｰcons₁ with "Hwaiters") as "((%Ψ & #Hconsumers_at & HΨ) & Hwaiters)".

          iMod "HΨ" as "(% & Hmodel₁ & _ & HΨ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod (modelｰupdate [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΨ" with "[$Hmodel₁ //]") as "HΨ".

          iDestruct (big_sepLｰseqｰsnoc₂ with "Hpast [HΨ]") as "Hpast"; first iSteps.

          iSplitL.
          { iFrame.
            rewrite skipn_all2 length_app /=; first lia.
            rewrite Nat.max_l; first lia.
            iSteps.
          }
          iSteps.
      }

      wp۰load.

      awp۰apply (inf_array٠setｰspec with "Hdata_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =2)".
      iAaccIntro with "Hdata_model"; first auto with iFrame. iIntros "Hdata_model !>".
      iSplitL.
      { repeat iExists _.
        rewrite Nat2Z.id -(fnｰcomposeｰinsert _ _ _ (Something v)).
        iSteps.
        rewrite fnｰlookupｰinsert.
        case_decide; first subst; iSteps.
      }
      iSteps.
    Qed.

    #[local] Lemma inf_queue_mpmc_1٠pop₁ｰspec t γ front Ψ :
      {{{
        inv' t γ ∗
        consumers۰at γ front Ψ ∗
        tokens۰pending γ front
      }}}
        inf_queue_mpmc_1٠pop₁ #t #front
      {{{
        v
      , RET v;
        Ψ v
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & #Hconsumers_at & Htokens_pending) HΦ".

      iLöb as "HLöb".

      wp۰rec credit:"H£". wp۰load.

      awp۰apply (inf_array٠getｰspec with "Hdata_inv") without "Htokens_pending H£ HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =1)".
      iAaccIntro with "Hdata_model"; first auto with iFrame. iIntros "Hdata_model".
      iAssert (▷ slot۰model γ front (slots1 front))%I with "[Hslots]" as "#>Hslot"; first iSteps.
      iSplitL. { iFrameSteps. }
      iIntros "!> _ (Htokens_pending & H£ & HΦ) {%}".

      rewrite Nat2Z.id /=. destruct (slots1 front) as [| | v].

      - iStep 8.
        wp۰apply ("HLöb" with "Htokens_pending HΦ").

      - iDestruct (tokens۰pendingｰdone with "Htokens_pending Hslot") as %[].

      - wp۰load.

        awp۰apply (inf_array٠setｰspec with "Hdata_inv") without "H£"; first lia.
        iInv "Hinv" as "(:inv۰inner =2)".
        iAaccIntro with "Hdata_model"; first auto with iFrame. iIntros "Hdata_model".
        iDestruct (history۰atｰvalid with "Hhistory_auth Hslot") as %Hhist2_lookup.
        opose proof* lookup_lt_Some as Hfront; first done.
        iDestruct (big_sepLｰseqｰlookupｰacc' front with "Hpast") as "([>Htokens_pending_ | (%Ψ_ & Hconsumers_at_ & [>Htokens_done | (%v_ & >Hhistory_at & HΨ)])] & Hpast)"; first lia.
        { iDestruct (tokens۰pendingｰexclusive with "Htokens_pending Htokens_pending_") as %[]. }
        { iDestruct (tokens۰pendingｰdone with "Htokens_pending Htokens_done") as %[]. }
        iDestruct (history۰atｰagree with "Hslot Hhistory_at") as %<-.
        iDestruct (consumers۰atｰagree with "Hconsumers_at Hconsumers_at_ HΨ") as "HΨ".
        iMod (tokens۰pendingｰupdate with "Htokens_pending") as "#Htokens_done".
        iDestruct ("Hpast" with "[]") as "Hpast"; first iSteps.
        iSplitR "HΨ HΦ".
        { rewrite Nat2Z.id -(fnｰcomposeｰinsert _ _ _ Anything).
          iFrameSteps.
          rewrite fnｰlookupｰinsert.
          case_decide; first subst; iSteps.
        }
        iIntros "!> _ H£ {%}".

        iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
        iSteps.
    Qed.
    Lemma inf_queue_mpmc_1٠popｰspec t γ ι :
      <<<
        inf_queue_mpmc_1۰inv t γ ι
      | ∀∀ vs,
        inf_queue_mpmc_1۰model γ vs
      >>>
        inf_queue_mpmc_1٠pop #t @ ↑ι
      <<<
        ∃∃ v vs',
        ⌜vs = v :: vs'⌝ ∗
        inf_queue_mpmc_1۰model γ vs'
      | RET v;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec. wp۰pures.

      wp۰bind (𝗳𝗮𝗮 _ _)%E.
      wp۰apply (wpｰwand (λ res,
        ∃ front,
        ⌜res = #front⌝ ∗
        consumers۰at γ front Φ ∗
        tokens۰pending γ front
      )%I with "[HΦ]") as (res) "(%front & -> & Hconsumers_at & Htokens_pending)".
      { iInv "Hinv" as "(:inv۰inner)".
        wp۰faa.
        destruct_decide (front < back) as Hfront1.

        - rewrite Nat.max_r; first lia.
          destruct (lookup_lt_is_Some_2 hist front) as (v & Hhist_lookup); first lia.
          erewrite drop_S; last done.

          iDestruct (history۰atｰget with "Hhistory_auth") as "#Hhistory_at"; first done.
          iDestruct (big_sepLｰseqｰlookupｰacc front with "Hpast") as "([$ | (%Ψ & Hconsumers_at & _)] & Hpast)"; first lia; last first.
          { iDestruct (consumers۰atｰvalid with "Hconsumers_auth Hconsumers_at") as %?. lia. }
          iMod (consumersｰupdate Φ with "Hconsumers_auth") as "(Hconsumers_auth & #Hconsumers_at)".

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod (modelｰupdate (drop ˖front hist) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁ //] [//]") as "HΦ".

          iSplitL.
          { iFrameSteps.
            rewrite Nat.max_r //.
            assert (˖front - back = 0) as -> by lia.
            iSteps.
          }
          iSteps.

        - rewrite Nat.max_l; first lia.

          iMod (consumersｰupdate Φ with "Hconsumers_auth") as "(Hconsumers_auth & #Hconsumers_at)".
          iMod (tokensｰupdate with "Htokens_auth") as "(Htokens_auth & $)".
          iDestruct (big_sepLｰseqｰsnoc₂ with "Hwaiters [HΦ]") as "Hwaiters".
          { rewrite -Nat.le_add_sub; first lia.
            iSteps. rewrite /consumer۰au. iAuIntro.
            iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)".
            iAaccIntro with "Hmodel₁"; iSteps.
          }
          rewrite -Nat.sub_succ_l; first lia.

          iSplitL.
          { iFrameSteps.
            rewrite !skipn_all2; [lia.. |].
            rewrite Nat.max_l; first lia.
            iSteps.
          }
          iSteps.
      }

      wp۰apply+ (inf_queue_mpmc_1٠pop₁ｰspec with "[$Hconsumers_at $Htokens_pending]"); iSteps.
    Qed.

    Lemma inf_queue_mpmc_1٠try_popｰspec t γ ι :
      <<<
        inf_queue_mpmc_1۰inv t γ ι
      | ∀∀ vs,
        inf_queue_mpmc_1۰model γ vs
      >>>
        inf_queue_mpmc_1٠try_pop #t @ ↑ι
      <<<
        inf_queue_mpmc_1۰model γ (tail vs)
      | RET head vs;
        True
      >>>.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp۰rec. wp۰pures.
      awp۰apply (inf_queue_mpmc_1٠is_empty_weakｰspec with "Hinv").
      iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iSteps. iIntros "%b (%Hb & Hmodel)".
      destruct b.

      - rewrite {}Hb.
        iRight. iFrameSteps.

      - iLeft. iFrame. iIntros "!> HΦ !> _".

        awp۰apply+ (inf_queue_mpmc_1٠popｰspec with "Hinv").
        iApply (aaccｰaupdｰcommit with "HΦ"). 1: done. iIntros "%vs' Hmodel".
        iAaccIntro with "Hmodel"; iSteps.
    Qed.
  End inf_queue_mpmc_1۰G.

  #[global] Opaque inf_queue_mpmc_1۰inv.
  #[global] Opaque inf_queue_mpmc_1۰model.
End base.

Require zoo_saturn.inf_queue_mpmc_1__opaque.

Section inf_queue_mpmc_1۰G.
  Context `{inf_queue_mpmc_1۰G : InfQueueMpmc1G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition inf_queue_mpmc_1۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.inf_queue_mpmc_1۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition inf_queue_mpmc_1۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.inf_queue_mpmc_1۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  #[global] Instance inf_queue_mpmc_1۰modelｰtimeless t vs :
    Timeless (inf_queue_mpmc_1۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_queue_mpmc_1۰invｰpersistent t ι :
    Persistent (inf_queue_mpmc_1۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma inf_queue_mpmc_1۰modelｰexclusive t vs1 vs2 :
    inf_queue_mpmc_1۰model t vs1 -∗
    inf_queue_mpmc_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_queue_mpmc_1۰modelｰexclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma inf_queue_mpmc_1٠createｰspec ι :
    {{{
      True
    }}}
      inf_queue_mpmc_1٠create ()
    {{{
      t
    , RET t;
      inf_queue_mpmc_1۰inv t ι ∗
      inf_queue_mpmc_1۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.inf_queue_mpmc_1٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (metaｰset γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma inf_queue_mpmc_1٠sizeｰspec t ι :
    <<<
      inf_queue_mpmc_1۰inv t ι
    | ∀∀ vs,
      inf_queue_mpmc_1۰model t vs
    >>>
      inf_queue_mpmc_1٠size t @ ↑ι
    <<<
      inf_queue_mpmc_1۰model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_queue_mpmc_1٠sizeｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_queue_mpmc_1٠is_emptyｰspec t ι :
    <<<
      inf_queue_mpmc_1۰inv t ι
    | ∀∀ vs,
      inf_queue_mpmc_1۰model t vs
    >>>
      inf_queue_mpmc_1٠is_empty t @ ↑ι
    <<<
      inf_queue_mpmc_1۰model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_queue_mpmc_1٠is_emptyｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_queue_mpmc_1٠is_empty_weakｰspec t ι :
    <<<
      inf_queue_mpmc_1۰inv t ι
    | ∀∀ vs,
      inf_queue_mpmc_1۰model t vs
    >>>
      inf_queue_mpmc_1٠is_empty_weak t @ ↑ι
    <<<
      ∃∃ b,
      ⌜if b then vs = [] else True⌝ ∗
      inf_queue_mpmc_1۰model t vs
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_queue_mpmc_1٠is_empty_weakｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_queue_mpmc_1٠pushｰspec t ι v :
    <<<
      inf_queue_mpmc_1۰inv t ι
    | ∀∀ vs,
      inf_queue_mpmc_1۰model t vs
    >>>
      inf_queue_mpmc_1٠push t v @ ↑ι
    <<<
      inf_queue_mpmc_1۰model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_queue_mpmc_1٠pushｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_queue_mpmc_1٠popｰspec t ι :
    <<<
      inf_queue_mpmc_1۰inv t ι
    | ∀∀ vs,
      inf_queue_mpmc_1۰model t vs
    >>>
      inf_queue_mpmc_1٠pop t @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = v :: vs'⌝ ∗
      inf_queue_mpmc_1۰model t vs'
    | RET v;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_queue_mpmc_1٠popｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_queue_mpmc_1٠try_popｰspec t ι :
    <<<
      inf_queue_mpmc_1۰inv t ι
    | ∀∀ vs,
      inf_queue_mpmc_1۰model t vs
    >>>
      inf_queue_mpmc_1٠try_pop t @ ↑ι
    <<<
      inf_queue_mpmc_1۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_queue_mpmc_1٠try_popｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
End inf_queue_mpmc_1۰G.

#[global] Opaque inf_queue_mpmc_1۰inv.
#[global] Opaque inf_queue_mpmc_1۰model.
