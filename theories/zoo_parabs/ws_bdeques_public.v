Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_parabs.base.
Require Export zoo_parabs.ws_bdeques_public__code.
Require Import zoo_parabs.ws_bdeques_public__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v round : val.
Implicit Type vs ws : list val.
Implicit Type queue : ws_bdeque_2۰name.
Implicit Type queues : list ws_bdeque_2۰name.
Implicit Type vss : list (list val).
Implicit Type status : status.

#[local] Definition capacity :=
  val۰to_nat' ws_bdeques_public٠capacity.
#[local] Lemma ws_bdeques_public٠capacityｰunfold :
  ws_bdeques_public٠capacity = #capacity.
Proof.
  done.
Qed.
Opaque ws_bdeques_public٠capacity.
Opaque capacity.

Zoo name :=
  { 𝑞𝑢𝑒𝑢𝑒𝑠 : val
  ; queues : list ws_bdeque_2۰name
  }.

Zoo global :=
  { ws_bdeque : ws_bdeque_2
  }.

Section ws_bdeques_public۰G.
  Context `{ws_bdeques_public۰G : WsBdequesPublicG Σ}.

  Please Definition ws_bdeques_public۰inv γ ι sz : iProp Σ :=
    ⌜sz = length γ.(ws_bdeques_public۰name۰queues)⌝ ∗
    array۰model γ.(ws_bdeques_public۰name۰𝑞𝑢𝑒𝑢𝑒𝑠) Discard ((♯) <$> γ.(ws_bdeques_public۰name۰queues)) ∗
    [∗ list] queue ∈ γ.(ws_bdeques_public۰name۰queues),
      ws_bdeque_2۰inv queue ι capacity.
  #[local] Instance : CustomIpat "inv" :=
    " ( %Hqueues{}_length
      & #Hqueues{}
      & #Hqueues{}_inv
      )
    ".

  Please Definition ws_bdeques_public۰model γ vss : iProp Σ :=
    [∗ list] queue; vs ∈ γ.(ws_bdeques_public۰name۰queues); vss,
      ws_bdeque_2۰model queue vs.
  #[local] Instance : CustomIpat "model" :=
    " Hqueues{}_model
    ".

  Please Definition ws_bdeques_public۰owner γ i status ws : iProp Σ :=
    ∃ queue,
    ⌜γ.(ws_bdeques_public۰name۰queues) !! i = Some queue⌝ ∗
    ws_bdeque_2۰owner queue ws.
  #[local] Instance : CustomIpat "owner" :=
    " ( %queue{}
      & %Hqueues{}_lookup
      & Hqueue{}_owner
      )
    ".

  Zoo derive Timeless for ws_bdeques_public۰model.

  Zoo derive Persistent for ws_bdeques_public۰inv.

  Lemma ws_bdeques_public۰invｰagree γ ι1 sz1 ι2 sz2 :
    ws_bdeques_public۰inv γ ι1 sz1 -∗
    ws_bdeques_public۰inv γ ι2 sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)".
    iSteps.
  Qed.

  Lemma ws_bdeques_public۰ownerｰexclusive γ i status1 ws1 status2 ws2 :
    ws_bdeques_public۰owner γ i status1 ws1 -∗
    ws_bdeques_public۰owner γ i status2 ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simp.
    iApply (ws_bdeque_2۰ownerｰexclusive with "Hqueue1_owner Hqueue2_owner").
  Qed.

  Lemma ws_bdeques_publicｰinvｰmodel γ ι sz vss :
    ws_bdeques_public۰inv γ ι sz -∗
    ws_bdeques_public۰model γ vss -∗
    ⌜length vss = sz⌝.
  Proof.
    iIntros "(:inv) (:model)".
    iDestruct (big_sepL2_length with "Hqueues_model") as %<-.
    iSteps.
  Qed.
  Lemma ws_bdeques_publicｰinvｰowner γ ι sz i status ws :
    ws_bdeques_public۰inv γ ι sz -∗
    ws_bdeques_public۰owner γ i status ws -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)".
    iPureIntro. rewrite Hqueues_length. eapply lookup_lt_Some. done.
  Qed.

  Lemma ws_bdeques_publicｰmodelｰowner γ vss i status ws :
    ws_bdeques_public۰model γ vss -∗
    ws_bdeques_public۰owner γ i status ws -∗
      ∃ vs,
      ⌜vss !! i = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:model =1) (:owner =2)".
    iDestruct (big_sepL2_lookup_l with "Hqueues1_model") as "(%vs & $ & Hqueue2_model)"; first done.
    iApply (ws_bdeque_2ｰownerｰmodel with "Hqueue2_owner Hqueue2_model").
  Qed.

  Lemma ws_bdeques_public٠createｰspec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_bdeques_public٠create #sz
    {{{
      γ
    , RET γ;
      ws_bdeques_public۰inv γ ι ₊sz ∗
      ws_bdeques_public۰model γ (replicate ₊sz []) ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_bdeques_public۰owner γ i Nonblocked []
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.

    pose (Ψ (_ : val) (_ : nat) vs := (
      ∃ queues,
      ⌜vs = (♯) <$> queues⌝ ∗
      ( [∗ list] queue ∈ queues,
        ws_bdeque_2۰inv queue ι capacity
      ) ∗
      ( [∗ list] queue ∈ queues,
        ws_bdeque_2۰model queue []
      ) ∗
      ( [∗ list] queue ∈ queues,
        ws_bdeque_2۰owner queue []
      )
    )%I).
    iApply wpｰfupd.
    wp۰apply+ (array٠unsafe_initｰspec Ψ) as (t vs) "(%Hvs_length & Ht & (%queues & -> & Hinv & Hmodel & Howner))"; first done.
    { iSplit.
      - iIntros "!> %t".
        iExists []. iSteps.
      - iIntros "!> %t %i %vs _ _ (%queues & -> & Hinv & Hmodel & Howner)".
        wp۰apply+ (ws_bdeque_2٠createｰspec with "[//]") as (queue) "(Hqueue_inv & Hqueue_model & Hqueue_owner)"; first done.
        iExists (queues ++ [queue]).
        rewrite fmap_snoc !big_sepL_snoc. iFrameSteps.
    }
    iMod (array۰modelｰpersist with "Ht") as "#Ht".
    rewrite length_fmap in Hvs_length.

    pose γ :=
      {|ws_bdeques_public۰name۰𝑞𝑢𝑒𝑢𝑒𝑠 := t
      ; ws_bdeques_public۰name۰queues := queues
      |}.

    iApply ("HΦ" $! γ). iSplitL "Hinv"; last iSplitL "Hmodel".
    - iSteps. iPureIntro. simpl. lia.
    - rewrite /ws_bdeques_public۰model big_sepL2_replicate_r //.
    - rewrite big_sepLｰseqｰindex //.
      iApply (big_sepL_impl with "Howner").
      iSteps.
  Qed.

  Lemma ws_bdeques_public٠sizeｰspec γ ι sz :
    {{{
      ws_bdeques_public۰inv γ ι sz
    }}}
      ws_bdeques_public٠size γ
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (array٠sizeｰspec with "Hqueues") as "_".
    rewrite length_fmap -Hqueues_length.
    iApply ("HΦ" with "[//]").
  Qed.

  Lemma ws_bdeques_public٠blockｰspec γ ι sz i i_ ws :
    i = ⁺i_ →
    {{{
      ws_bdeques_public۰inv γ ι sz ∗
      ws_bdeques_public۰owner γ i_ Nonblocked ws
    }}}
      ws_bdeques_public٠block γ #i
    {{{
      RET ();
      ws_bdeques_public۰owner γ i_ Blocked ws
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ws_bdeques_public٠unblockｰspec γ ι sz i i_ ws :
    i = ⁺i_ →
    {{{
      ws_bdeques_public۰inv γ ι sz ∗
      ws_bdeques_public۰owner γ i_ Blocked ws
    }}}
      ws_bdeques_public٠unblock γ #i
    {{{
      RET ();
      ws_bdeques_public۰owner γ i_ Nonblocked ws
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ws_bdeques_public٠pushｰspec γ ι sz i i_ ws v :
    i = ⁺i_ →
    <<<
      ws_bdeques_public۰inv γ ι sz ∗
      ws_bdeques_public۰owner γ i_ Nonblocked ws
    | ∀∀ vss,
      ws_bdeques_public۰model γ vss
    >>>
      ws_bdeques_public٠push γ #i v
      @ ↑ι
    <<<
      ∃∃ b vs,
      ⌜vss !! i_ = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝ ∗
      if b then
        ws_bdeques_public۰model γ (<[i_ := vs ++ [v]]> vss)
      else
        ws_bdeques_public۰model γ vss
    | RET #b;
      if b then
        ws_bdeques_public۰owner γ i_ Nonblocked (vs ++ [v])
      else
        ws_bdeques_public۰owner γ i_ Nonblocked ws
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_getｰspec i_ with "Hqueues") as "_"; [lia | rewrite list_lookup_fmap Hqueues_lookup // | lia |].

    iDestruct (big_sepL_lookup with "Hqueues_inv") as "Hqueue_inv"; first done.
    awp۰apply+ (ws_bdeque_2٠pushｰspec with "[$Hqueue_inv $Hqueue_owner]").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vss (:model)".
    iDestruct (big_sepL2ｰlookupｰSomeｰl with "Hqueues_model") as %(vs & Hvss_lookup); first done.
    iDestruct (big_sepL2_insert_acc with "Hqueues_model") as "(Hqueue_model & Hqueues_model)"; [done.. |].
    iAaccIntro with "Hqueue_model".

    - iIntros "Hqueue_model".
      iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
      rewrite !list_insert_id //. iSteps.

    - iIntros "%b (%Hb & %Hsuffix & Hqueue_model)".
      iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
      rewrite list_insert_id //.
      iExists b, vs. subst b.
      case_bool_decide as Hvs.

      + iFrameSteps.

      + rewrite list_insert_id //. iFrameSteps.
  Qed.

  Lemma ws_bdeques_public٠popｰspec γ ι sz i i_ ws :
    i = ⁺i_ →
    <<<
      ws_bdeques_public۰inv γ ι sz ∗
      ws_bdeques_public۰owner γ i_ Nonblocked ws
    | ∀∀ vss,
      ws_bdeques_public۰model γ vss
    >>>
      ws_bdeques_public٠pop γ #i
      @ ↑ι
    <<<
      ∃∃ o ws',
      match o with
      | None =>
          ⌜vss !! i_ = Some []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_bdeques_public۰model γ vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i_ = Some (vs ++ [v])⌝ ∗
          ⌜vs ++ [v] `suffix_of` ws⌝ ∗
          ⌜ws' = vs⌝ ∗
          ws_bdeques_public۰model γ (<[i_ := vs]> vss)
      end
    | RET o;
      ws_bdeques_public۰owner γ i_ Nonblocked ws'
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_getｰspec i_ with "Hqueues") as "_"; [lia | rewrite list_lookup_fmap Hqueues_lookup // | lia |].

    iDestruct (big_sepL_lookup with "Hqueues_inv") as "Hqueue_inv"; first done.
    awp۰apply+ (ws_bdeque_2٠popｰspec with "[$Hqueue_inv $Hqueue_owner]").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vss (:model)".
    iDestruct (big_sepL2ｰlookupｰSomeｰl with "Hqueues_model") as %(vs & Hvss_lookup); first done.
    iDestruct (big_sepL2_insert_acc with "Hqueues_model") as "(Hqueue_model & Hqueues_model)"; [done.. |].
    iAaccIntro with "Hqueue_model".

    - iIntros "Hqueue_model".
      iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
      rewrite !list_insert_id //. iSteps.

    - iIntros "%o %ws' (%Hsuffix & Hqueue_model)".
      iExists o, ws'. iSplitL; last iSteps.
      destruct o as [v |].

      + iDestruct "Hqueue_model" as "(%vs' & -> & -> & Hqueue_model)".
        iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
        rewrite list_insert_id //. iSteps.

      + iDestruct "Hqueue_model" as "(-> & -> & Hqueue_model)".
        iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
        rewrite !list_insert_id //. iSteps.
  Qed.

  Lemma ws_bdeques_public٠steal_toｰspec γ ι (sz : nat) i i_ ws j :
    i = ⁺i_ →
    (0 ≤ j < sz)%Z →
    <<<
      ws_bdeques_public۰inv γ ι sz ∗
      ws_bdeques_public۰owner γ i_ Blocked ws
    | ∀∀ vss,
      ws_bdeques_public۰model γ vss
    >>>
      ws_bdeques_public٠steal_to γ #i #j
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_bdeques_public۰model γ vss
      | Some v =>
          ∃ vs,
          ⌜vss !! ₊j = Some (v :: vs)⌝ ∗
          ws_bdeques_public۰model γ (<[₊j := vs]> vss)
      end
    | RET o;
      ws_bdeques_public۰owner γ i_ Blocked ws
    >>>.
  Proof.
    iIntros (-> Hj) "%Φ ((:inv) & Howner) HΦ".

    wp۰rec.
    destruct (lookup_lt_is_Some_2 γ.(ws_bdeques_public۰name۰queues) ₊j) as (queue & Hqueues_lookup); first lia.
    wp۰apply+ (array٠unsafe_getｰspec ₊j with "Hqueues") as "_"; [lia | rewrite list_lookup_fmap Hqueues_lookup // | lia |].

    iDestruct (big_sepL_lookup with "Hqueues_inv") as "#Hqueue_inv"; first done.
    awp۰apply+ (ws_bdeque_2٠stealｰspec with "Hqueue_inv") without "Howner".
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vss (:model)".
    iDestruct (big_sepL2ｰlookupｰSomeｰl with "Hqueues_model") as %(vs & Hvss_lookup); first done.
    iDestruct (big_sepL2_insert_acc with "Hqueues_model") as "(Hqueue_model & Hqueues_model)"; [done.. |].
    iAaccIntro with "Hqueue_model".

    - iIntros "Hqueue_model".
      iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
      rewrite !list_insert_id //. iSteps.

    - iIntros "Hqueue_model !>". destruct vs as [| v vs].

      + iExists None. iSplitL; last iSteps.
        iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
        rewrite !list_insert_id //.

      + iExists (Some v). iSplitL; last iSteps.
        iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
        rewrite list_insert_id //. iSteps.
  Qed.
End ws_bdeques_public۰G.

Please opacify.

Section ws_bdeques_public۰G.
  Context `{ws_bdeques_public۰G : WsBdequesPublicG Σ}.

  #[local] Lemma ws_bdeques_public٠steal_as₁ｰspec γ ι (sz : nat) i i_ ws round (n : nat) :
    i = ⁺i_ →
    <<<
      ws_bdeques_public۰inv γ ι sz ∗
      ws_bdeques_public۰owner γ i_ Blocked ws ∗
      random۰round۰model' round (sz - 1) n
    | ∀∀ vss,
      ws_bdeques_public۰model γ vss
    >>>
      ws_bdeques_public٠steal_as₁ γ #sz #i round #n
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_bdeques_public۰model γ vss
      | Some v =>
          ∃ j vs,
          ⌜₊i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_bdeques_public۰model γ (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_bdeques_public۰owner γ i_ Blocked ws ∗
      random۰round۰model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner & Hround) HΦ".
    iDestruct (ws_bdeques_publicｰinvｰowner with "Hinv Howner") as %Hi.

    iLöb as "HLöb" forall (n).

    wp۰rec. wp۰pures.
    case_bool_decide as Hcase; wp۰pures.

    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! None with "Hmodel [$Howner Hround]"); first iSteps.

    - wp۰apply (random٠round٠nextｰspec' with "Hround") as (j) "(%Hj & Hround)"; first lia.
      wp۰pures.
      rewrite Nat2Z.id.
      pose k := (i_ + 1 + j) `mod` sz.
      assert ((i_ + 1 + j) `rem` sz = k)%Z as ->.
      { rewrite Z.rem_mod_nonneg; lia. }
      awp۰apply+ (ws_bdeques_public٠steal_toｰspec with "[$Hinv $Howner]") without "Hround"; [done | lia |].
      iApply (aaccｰaupd with "HΦ"); first done. iIntros "%vss Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([ v |]).

      + rewrite Nat2Z.id.
        iSteps as (vs Hlookup) "Hmodel". iExists (Some v). iSteps. iExists k. iSteps. iPureIntro.
        clear Hlookup. rewrite {}/k.
        destruct_decide (i_ + 1 + j < sz).
        * rewrite Nat.mod_small //. lia.
        * assert (i_ + 1 + j < sz * 2) as ?%Nat.Div0.div_lt_upper_bound by lia.
          assert ((i_ + 1 + j) `div` sz = 1) by lia.
          lia.

      + iSteps as "HΦ Howner Hround".
        assert (n - 1 = (n - 1)%nat)%Z as -> by lia.
        iSteps.
  Qed.
  Lemma ws_bdeques_public٠steal_asｰspec γ ι sz i i_ ws round :
    i = ⁺i_ →
    0 < sz →
    <<<
      ws_bdeques_public۰inv γ ι sz ∗
      ws_bdeques_public۰owner γ i_ Blocked ws ∗
      random۰round۰model' round (sz - 1) (sz - 1)
    | ∀∀ vss,
      ws_bdeques_public۰model γ vss
    >>>
      ws_bdeques_public٠steal_as γ #i round
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_bdeques_public۰model γ vss
      | Some v =>
          ∃ j vs,
          ⌜₊i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_bdeques_public۰model γ (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_bdeques_public۰owner γ i_ Blocked ws ∗
      random۰round۰model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Hsz %Φ (#Hinv & Hround) HΦ".

    wp۰rec.
    wp۰apply+ (ws_bdeques_public٠sizeｰspec with "Hinv") as "_".
    wp۰pures.
    assert (sz - 1 = (sz - 1)%nat)%Z as -> by lia.
    wp۰apply (ws_bdeques_public٠steal_as₁ｰspec with "[$Hinv $Hround] HΦ"); first done.
  Qed.
End ws_bdeques_public۰G.

Require zoo_parabs.ws_bdeques_public__opaque.
