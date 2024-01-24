From iris.algebra Require Import
  list.

From zebre Require Import
  prelude.
From zebre.common Require Import
  relations
  list.
From zebre.iris.base_logic Require Import
  lib.excl
  lib.auth_excl
  lib.auth_nat_max
  lib.mono_list.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  array.
From zebre.saturn Require Export
  base.
From zebre Require Import
  options.

Implicit Types i sz : nat.
Implicit Types l : loc.
Implicit Types v w t : val.
Implicit Types vs hist : list val.

#[local] Notation "'data'" :=
  0
( in custom zebre_field
).
#[local] Notation "'front'" :=
  1
( in custom zebre_field
).
#[local] Notation "'back'" :=
  2
( in custom zebre_field
).

Definition spsc_queue_create : val :=
  λ: "sz",
    { array_make "sz" &&None; #0; #0 }.

Definition spsc_queue_push : val :=
  λ: "t" "v",
    let: "data" := "t".{data} in
    let: "back" := "t".{back} in
    let: "front" := "t".{front} in
    if: "back" < "front" + array_size "data" then (
      array_cset "data" "back" (&Some "v") ;;
      "t" <-{back}- #1 + "back" ;;
      #false
    ) else (
      #true
    ).

Definition spsc_queue_pop : val :=
  λ: "t",
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    if: "front" < "back" then (
      let: "data" := "t".{data} in
      let: "res" := array_cget "data" "front" in
      array_cset "data" "front" &&None ;;
      "t" <-{front}- #1 + "front" ;;
      "res"
    ) else (
      &&None
    ).

Class SpscQueueG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] spsc_queue_G_model_G :: AuthExclG Σ (listO valO) ;
  #[local] spsc_queue_G_history_G :: MonoListG Σ val ;
  #[local] spsc_queue_G_ctl_G :: AuthNatMaxG Σ ;
  #[local] spsc_queue_G_region_G :: ExclG Σ unitO ;
}.

Definition spsc_queue_Σ := #[
  auth_excl_Σ (listO valO) ;
  mono_list_Σ val ;
  auth_nat_max_Σ ;
  excl_Σ unitO
].
Lemma subG_spsc_queue_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG spsc_queue_Σ Σ →
  SpscQueueG Σ.
Proof.
  solve_inG.
Qed.

Section spsc_queue_G.
  Context `{spsc_queue_G : SpscQueueG Σ}.

  Record spsc_queue_meta := {
    spsc_queue_meta_model : gname ;
    spsc_queue_meta_history : gname ;
    spsc_queue_meta_producer_ctl : gname ;
    spsc_queue_meta_producer_region : gname ;
    spsc_queue_meta_consumer_ctl : gname ;
    spsc_queue_meta_consumer_region : gname ;
  }.
  Implicit Types γ : spsc_queue_meta.

  #[local] Instance spsc_queue_meta_eq_dec : EqDecision spsc_queue_meta :=
    ltac:(solve_decision).
  #[local] Instance spsc_queue_meta_countable :
    Countable spsc_queue_meta.
  Proof.
    pose encode γ := (
      γ.(spsc_queue_meta_model),
      γ.(spsc_queue_meta_history),
      γ.(spsc_queue_meta_producer_ctl),
      γ.(spsc_queue_meta_producer_region),
      γ.(spsc_queue_meta_consumer_ctl),
      γ.(spsc_queue_meta_consumer_region)
    ).
    pose decode := λ '(γ_model, γ_history, γ_producer_ctl, γ_producer_region, γ_consumer_ctl, γ_consumer_region), {|
      spsc_queue_meta_model := γ_model ;
      spsc_queue_meta_history := γ_history ;
      spsc_queue_meta_producer_ctl := γ_producer_ctl ;
      spsc_queue_meta_producer_region := γ_producer_region ;
      spsc_queue_meta_consumer_ctl := γ_consumer_ctl ;
      spsc_queue_meta_consumer_region := γ_consumer_region ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition spsc_queue_model₁' γ_model vs :=
    auth_excl_frag γ_model vs.
  #[local] Definition spsc_queue_model₁ γ vs :=
    spsc_queue_model₁' γ.(spsc_queue_meta_model) vs.
  #[local] Definition spsc_queue_model₂' γ_model vs :=
    auth_excl_auth γ_model (DfracOwn 1) vs.
  #[local] Definition spsc_queue_model₂ γ vs :=
    spsc_queue_model₂' γ.(spsc_queue_meta_model) vs.

  #[local] Definition spsc_queue_history_auth' γ_history hist :=
    mono_list_auth γ_history 1 hist.
  #[local] Definition spsc_queue_history_auth γ hist :=
    spsc_queue_history_auth' γ.(spsc_queue_meta_history) hist.
  #[local] Definition spsc_queue_history_mapsto γ i v :=
    mono_list_mapsto γ.(spsc_queue_meta_history) i v.

  #[local] Definition spsc_queue_producer_ctl₁' γ_producer_ctl back :=
    auth_nat_max_auth γ_producer_ctl (DfracOwn (1/2)) back.
  #[local] Definition spsc_queue_producer_ctl₁ γ back :=
    spsc_queue_producer_ctl₁' γ.(spsc_queue_meta_producer_ctl) back.
  #[local] Definition spsc_queue_producer_ctl₂' γ_producer_ctl back :=
    auth_nat_max_auth γ_producer_ctl (DfracOwn (1/2)) back.
  #[local] Definition spsc_queue_producer_ctl₂ γ back :=
    spsc_queue_producer_ctl₂' γ.(spsc_queue_meta_producer_ctl) back.
  #[local] Definition spsc_queue_back_lb γ back :=
    auth_nat_max_lb γ.(spsc_queue_meta_producer_ctl) back.

  #[local] Definition spsc_queue_producer_region' γ_producer_region :=
    excl γ_producer_region ().
  #[local] Definition spsc_queue_producer_region γ :=
    spsc_queue_producer_region' γ.(spsc_queue_meta_producer_region).

  #[local] Definition spsc_queue_consumer_ctl₁' γ_consumer_ctl front :=
    auth_nat_max_auth γ_consumer_ctl (DfracOwn (1/2)) front.
  #[local] Definition spsc_queue_consumer_ctl₁ γ front :=
    spsc_queue_consumer_ctl₁' γ.(spsc_queue_meta_consumer_ctl) front.
  #[local] Definition spsc_queue_consumer_ctl₂' γ_consumer_ctl front :=
    auth_nat_max_auth γ_consumer_ctl (DfracOwn (1/2)) front.
  #[local] Definition spsc_queue_consumer_ctl₂ γ front :=
    spsc_queue_consumer_ctl₂' γ.(spsc_queue_meta_consumer_ctl) front.
  #[local] Definition spsc_queue_front_lb γ front :=
    auth_nat_max_lb γ.(spsc_queue_meta_consumer_ctl) front.

  #[local] Definition spsc_queue_consumer_region' γ_consumer_region :=
    excl γ_consumer_region ().
  #[local] Definition spsc_queue_consumer_region γ :=
    spsc_queue_consumer_region' γ.(spsc_queue_meta_consumer_region).

  #[local] Definition spsc_queue_inv_inner l γ sz data : iProp Σ :=
    ∃ front back vs hist,
    ⌜back = (front + length vs)%nat ∧ back ≤ front + sz⌝ ∗
    ⌜length hist = back ∧ vs = drop front hist⌝ ∗
    l.[front] ↦ #front ∗
    spsc_queue_consumer_ctl₂ γ front ∗
    l.[back] ↦ #back ∗
    spsc_queue_producer_ctl₂ γ back ∗
    spsc_queue_model₂ γ vs ∗
    spsc_queue_history_auth γ hist ∗
    ( array_cslice data sz front (DfracOwn 1) (&&Some <$> take 1 vs)
    ∨ spsc_queue_consumer_region γ
    ) ∗
    array_cslice data sz (S front) (DfracOwn 1) (&&Some <$> drop 1 vs) ∗
    ( array_cslice data sz back (DfracOwn 1) (if decide (back = front + sz) then [] else [&&None])
    ∨ spsc_queue_producer_region γ
    ) ∗
    array_cslice data sz (S back) (DfracOwn 1) (replicate (sz - (back - front) - 1) &&None).
  Definition spsc_queue_inv t ι sz : iProp Σ :=
    ∃ l γ data,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[data] ↦□ data ∗
    inv ι (spsc_queue_inv_inner l γ sz data).

  Definition spsc_queue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    spsc_queue_model₁ γ vs.

  Definition spsc_queue_producer t : iProp Σ :=
    ∃ l γ back,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    spsc_queue_producer_ctl₁ γ back ∗
    spsc_queue_producer_region γ.

  Definition spsc_queue_consumer t : iProp Σ :=
    ∃ l γ front,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    spsc_queue_consumer_ctl₁ γ front ∗
    spsc_queue_consumer_region γ.

  #[global] Instance spsc_queue_inv_persistent t ι sz :
    Persistent (spsc_queue_inv t ι sz).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_queue_model_timeless t vs :
    Timeless (spsc_queue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_queue_producer_timeless t :
    Timeless (spsc_queue_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_queue_consumer_timeless t :
    Timeless (spsc_queue_consumer t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma spsc_queue_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      spsc_queue_model₁' γ_model [] ∗
      spsc_queue_model₂' γ_model [].
  Proof.
    iMod (auth_excl_alloc' (auth_excl_G := spsc_queue_G_model_G) []) as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma spsc_queue_model_agree γ model1 model2 :
    spsc_queue_model₁ γ model1 -∗
    spsc_queue_model₂ γ model2 -∗
    ⌜model1 = model2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iSteps.
  Qed.
  #[local] Lemma spsc_queue_model_update {γ model1 model2} model :
    spsc_queue_model₁ γ model1 -∗
    spsc_queue_model₂ γ model2 ==∗
      spsc_queue_model₁ γ model ∗
      spsc_queue_model₂ γ model.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iMod (auth_excl_update' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
    iSteps.
  Qed.

  #[local] Lemma spsc_queue_history_alloc :
    ⊢ |==>
      ∃ γ_history,
      spsc_queue_history_auth' γ_history [].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma spsc_queue_history_mapsto_get {γ hist} i v :
    hist !! i = Some v →
    spsc_queue_history_auth γ hist ⊢
    spsc_queue_history_mapsto γ i v.
  Proof.
    setoid_rewrite mono_list_lb_get. apply mono_list_mapsto_get.
  Qed.
  #[local] Lemma spsc_queue_history_agree γ hist i v :
    spsc_queue_history_auth γ hist -∗
    spsc_queue_history_mapsto γ i v -∗
    ⌜hist !! i = Some v⌝.
  Proof.
    apply mono_list_auth_mapsto_lookup.
  Qed.
  #[local] Lemma spsc_queue_history_update {γ hist} v :
    spsc_queue_history_auth γ hist ⊢ |==>
    spsc_queue_history_auth γ (hist ++ [v]).
  Proof.
    apply mono_list_auth_update_app.
  Qed.

  #[local] Lemma spsc_queue_producer_ctl_alloc :
    ⊢ |==>
      ∃ γ_producer_ctl,
      spsc_queue_producer_ctl₁' γ_producer_ctl 0 ∗
      spsc_queue_producer_ctl₂' γ_producer_ctl 0.
  Proof.
    iMod auth_nat_max_alloc as "(%γ_producer_ctl & Hproducer_ctl₁ & Hproducer_ctl₂)".
    iSteps.
  Qed.
  #[local] Lemma spsc_queue_producer_ctl_agree γ back1 back2 :
    spsc_queue_producer_ctl₁ γ back1 -∗
    spsc_queue_producer_ctl₂ γ back2 -∗
    ⌜back1 = back2⌝.
  Proof.
    apply auth_nat_max_auth_agree.
  Qed.
  #[local] Lemma spsc_queue_producer_ctl_update {γ back1 back2} back :
    back1 ≤ back →
    spsc_queue_producer_ctl₁ γ back1 -∗
    spsc_queue_producer_ctl₂ γ back2 ==∗
      spsc_queue_producer_ctl₁ γ back ∗
      spsc_queue_producer_ctl₂ γ back.
  Proof.
    iIntros "%Hle Hproducer_ctl₁ Hproducer_ctl₂".
    iDestruct (auth_nat_max_auth_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %->.
    iCombine "Hproducer_ctl₁ Hproducer_ctl₂" as "Hproducer_ctl".
    iMod (auth_nat_max_update with "Hproducer_ctl") as "($ & $)"; done.
  Qed.
  #[local] Lemma spsc_queue_back_lb_get γ back :
    spsc_queue_producer_ctl₂ γ back ⊢
    spsc_queue_back_lb γ back.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma spsc_queue_back_lb_valid γ back1 back2 :
    spsc_queue_producer_ctl₂ γ back1 -∗
    spsc_queue_back_lb γ back2 -∗
    ⌜back2 ≤ back1⌝.
  Proof.
    apply auth_nat_max_valid.
  Qed.

  #[local] Lemma spsc_queue_producer_region_alloc :
    ⊢ |==>
      ∃ γ_producer_region,
      spsc_queue_producer_region' γ_producer_region.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma spsc_queue_producer_region_exclusive γ :
    spsc_queue_producer_region γ -∗
    spsc_queue_producer_region γ -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  #[local] Lemma spsc_queue_consumer_ctl_alloc :
    ⊢ |==>
      ∃ γ_consumer_ctl,
      spsc_queue_consumer_ctl₁' γ_consumer_ctl 0 ∗
      spsc_queue_consumer_ctl₂' γ_consumer_ctl 0.
  Proof.
    iMod auth_nat_max_alloc as "(%γ_consumer_ctl & Hconsumer_ctl₁ & Hconsumer_ctl₂)".
    iSteps.
  Qed.
  #[local] Lemma spsc_queue_consumer_ctl_agree γ front1 front2 :
    spsc_queue_consumer_ctl₁ γ front1 -∗
    spsc_queue_consumer_ctl₂ γ front2 -∗
    ⌜front1 = front2⌝.
  Proof.
    apply auth_nat_max_auth_agree.
  Qed.
  #[local] Lemma spsc_queue_consumer_ctl_update {γ front1 front2} front :
    front1 ≤ front →
    spsc_queue_consumer_ctl₁ γ front1 -∗
    spsc_queue_consumer_ctl₂ γ front2 ==∗
      spsc_queue_consumer_ctl₁ γ front ∗
      spsc_queue_consumer_ctl₂ γ front.
  Proof.
    iIntros "%Hle Hconsumer_ctl₁ Hconsumer_ctl₂".
    iDestruct (auth_nat_max_auth_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %->.
    iCombine "Hconsumer_ctl₁ Hconsumer_ctl₂" as "Hconsumer_ctl".
    iMod (auth_nat_max_update with "Hconsumer_ctl") as "($ & $)"; done.
  Qed.
  #[local] Lemma spsc_queue_front_lb_get γ front :
    spsc_queue_consumer_ctl₂ γ front ⊢
    spsc_queue_front_lb γ front.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma spsc_queue_front_lb_valid γ front1 front2 :
    spsc_queue_consumer_ctl₂ γ front1 -∗
    spsc_queue_front_lb γ front2 -∗
    ⌜front2 ≤ front1⌝.
  Proof.
    iIntros "Hconsumer_ctl₁ Hfront_lb".
    iApply (auth_nat_max_valid with "Hconsumer_ctl₁ Hfront_lb").
  Qed.

  #[local] Lemma spsc_queue_consumer_region_alloc :
    ⊢ |==>
      ∃ γ_consumer_region,
      spsc_queue_consumer_region' γ_consumer_region.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma spsc_queue_consumer_region_exclusive γ :
    spsc_queue_consumer_region γ -∗
    spsc_queue_consumer_region γ -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  Lemma spsc_queue_producer_exclusive t :
    spsc_queue_producer t -∗
    spsc_queue_producer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & %back & -> & #Hmeta & _ & Hproducer_region_1) (%_l & %_γ & %_back & %Heq & _Hmeta & _ & Hproducer_region_2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %->. iClear "_Hmeta".
    iApply (spsc_queue_producer_region_exclusive with "Hproducer_region_1 Hproducer_region_2").
  Qed.

  Lemma spsc_queue_consumer_exclusive t :
    spsc_queue_consumer t -∗
    spsc_queue_consumer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & %front & -> & #Hmeta & _ & Hconsumer_region_1) (%_l & %_γ & %_front & %Heq & _Hmeta & _ & Hconsumer_region_2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %->. iClear "_Hmeta".
    iApply (spsc_queue_consumer_region_exclusive with "Hconsumer_region_1 Hconsumer_region_2").
  Qed.

  #[local] Instance hint_array_cslice_nil t sz i dq :
    HINT ε₁ ✱ [- ; array_inv t sz] ⊫ [id]; array_cslice t sz i dq [] ✱ [emp].
  Proof.
    iSteps. rewrite array_cslice_nil. iSteps.
  Qed.

  Lemma spsc_queue_create_spec ι sz :
    (0 ≤ sz)%Z →
    {{{ True }}}
      spsc_queue_create #sz
    {{{ t,
      RET t;
      spsc_queue_inv t ι (Z.to_nat sz) ∗
      spsc_queue_model t [] ∗
      spsc_queue_producer t ∗
      spsc_queue_consumer t
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.
    iApply wp_fupd.
    wp_apply (array_make_spec with "[//]") as "%data Hdata_model"; first done.
    wp_record l as "Hmeta" "(Hdata & Hfront & Hback & _)".
    iMod (mapsto_persist with "Hdata") as "#Hdata".

    iMod spsc_queue_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod spsc_queue_history_alloc as "(%γ_history & Hhistory_auth)".
    iMod spsc_queue_producer_ctl_alloc as "(%γ_producer_ctl & Hproducer_ctl₁ & Hproducer_ctl₂)".
    iMod spsc_queue_producer_region_alloc as "(%γ_producer_region & Hproducer_region)".
    iMod spsc_queue_consumer_ctl_alloc as "(%γ_consumer_ctl & Hconsumer_ctl₁ & Hconsumer_ctl₂)".
    iMod spsc_queue_consumer_region_alloc as "(%γ_consumer_region & Hconsumer_region)".

    pose γ := {|
      spsc_queue_meta_model := γ_model ;
      spsc_queue_meta_history := γ_history ;
      spsc_queue_meta_producer_ctl := γ_producer_ctl ;
      spsc_queue_meta_producer_region := γ_producer_region ;
      spsc_queue_meta_consumer_ctl := γ_consumer_ctl ;
      spsc_queue_meta_consumer_region := γ_consumer_region ;
    |}.
    iMod (meta_set _ _ γ nroot with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hproducer_ctl₁ Hproducer_region Hconsumer_ctl₁ Hconsumer_region"; last iSteps.
    iStep 3. iApply inv_alloc. iExists 0, 0, [], []. iStep 7. rewrite Nat2Z.id.
    iDestruct (array_model_to_inv with "Hdata_model") as "#Hdata_size". rewrite replicate_length.
    iStep 4.
    destruct sz as [| sz]; first iSteps.
    iDestruct (array_model_to_cslice with "Hdata_model") as "Hdata_cslice".
    rewrite replicate_length -(take_drop 1 (replicate _ _)).
    iDestruct (array_cslice_app with "Hdata_cslice") as "(Hdata_back & Hdata_extra)".
    rewrite Nat.add_0_l take_replicate_add. iStep.
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  Lemma spsc_queue_push_spec t ι sz v :
    <<<
      spsc_queue_inv t ι sz ∗
      spsc_queue_producer t
    | ∀∀ vs,
      spsc_queue_model t vs
    >>>
      spsc_queue_push t v @ ↑ι
    <<<
      spsc_queue_model t (if decide (length vs = sz) then vs else vs ++ [v])
    | RET #(bool_decide (length vs = sz));
      spsc_queue_producer t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & %data & -> & #Hmeta & #Hdata & #Hinv) & (%_l & %_γ & %back & %Heq & #_Hmeta & Hproducer_ctl₁ & Hproducer_region)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_load. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%front1 & %_back & %vs1 & %hist1 & >(%Hback & %Hback_le) & >(%Hhist1_len & %Hvs1) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hdata_back & Hdata_extra)".
    wp_load.
    iDestruct (spsc_queue_producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
    iDestruct (array_cslice_to_inv with "Hdata_vs") as "#Hdata_inv".
    iSplitR "Hproducer_ctl₁ Hproducer_region HΦ"; first iSteps.
    iModIntro. clear.

    wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%front2 & %_back & %vs2 & %hist2 & >(%Hback & %Hback_le) & >(%Hhist2_len & %Hvs2) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hdata_back & Hdata_extra)".
    wp_load.
    iDestruct (spsc_queue_producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
    destruct (decide (back < front2 + sz)) as [Hbranch | Hbranch].

    - iDestruct (spsc_queue_front_lb_get with "Hconsumer_ctl₂") as "#Hfront_lb".
      iDestruct "Hdata_back" as "[Hdata_back | Hproducer_region']"; last first.
      { iDestruct (spsc_queue_producer_region_exclusive with "Hproducer_region Hproducer_region'") as %[]. }
      rewrite decide_False; first lia.
      iSplitR "Hproducer_ctl₁ Hdata_back HΦ"; first iSteps.
      iModIntro. clear- Hbranch.

      wp_smart_apply (array_size_spec_inv with "Hdata_inv") as "_".
      wp_pures. rewrite bool_decide_eq_true_2; first lia.
      wp_smart_apply (array_cset_spec with "Hdata_back") as "Hdata_back"; first done.
      wp_pures.

      wp_bind (_ <- _)%E.
      iInv "Hinv" as "(%front3 & %_back & %vs3 & %hist3 & >(%Hback & %Hback_le) & >(%Hhist3_len & %Hvs3) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hproducer_region & Hdata_extra)".
      wp_store.
      iDestruct (spsc_queue_producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
      iDestruct (spsc_queue_front_lb_valid with "Hconsumer_ctl₂ Hfront_lb") as %Hfront2.
      iDestruct "Hproducer_region" as "[Hdata_back' | Hproducer_region]".
      { rewrite decide_False; first lia.
        iDestruct (array_cslice_exclusive with "Hdata_back Hdata_back'") as %[]; [simpl; lia | done].
      }
      iMod (spsc_queue_producer_ctl_update (S back) with "Hproducer_ctl₁ Hproducer_ctl₂") as "(Hproducer_ctl₁ & Hproducer_ctl₂)"; first lia.
      iMod (spsc_queue_history_update v with "Hhistory_auth") as "Hhistory_auth".
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (spsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (spsc_queue_model_update (vs3 ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      rewrite decide_False; first lia.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      rewrite bool_decide_eq_false_2; first lia.
      iSplitR "Hproducer_ctl₁ Hproducer_region HΦ".
      { do 2 iModIntro. iExists front3, (S back), (vs3 ++ [v]), (hist3 ++ [v]). iFrame.
        iSplit. { rewrite app_length. iSteps. }
        iSplit. { rewrite app_length drop_app_le; first lia. iSteps. }
        iSplitL "Hback"; first iSteps.
        rewrite assoc. iSplitL "Hdata_front Hdata_vs Hdata_back".
        - destruct vs3 as [| v' vs3].
          + assert (front3 = back) as -> by naive_solver lia. iSteps.
          + iFrame. rewrite /= !drop_0 fmap_app.
            iApply (array_cslice_app_1 with "Hdata_vs Hdata_back").
            rewrite fmap_length. naive_solver lia.
        - case_decide.
          + assert (sz - (S back - front3) - 1 = 0) as -> by lia. iSteps.
          + iDestruct (array_cslice_app_2 [&&None] (replicate (sz - (S back - front3) - 1) &&None) with "Hdata_extra") as "(Hdata_back' & Hdata_extra)".
            { rewrite /= -replicate_S. f_equal. lia. }
            rewrite Nat.add_1_r. iSteps.
      }
      iModIntro. clear.

      iSteps.

    - iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (spsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      rewrite decide_True; [lia.. |]. rewrite bool_decide_eq_true_2; first lia.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "Hproducer_ctl₁ Hproducer_region HΦ"; first iSteps.
      iModIntro. clear- Hbranch.

      wp_smart_apply (array_size_spec_inv with "Hdata_inv").
      iSteps.
  Qed.

  Lemma spsc_queue_pop_spec t ι sz :
    <<<
      spsc_queue_inv t ι sz ∗
      spsc_queue_consumer t
    | ∀∀ vs,
      spsc_queue_model t vs
    >>>
      spsc_queue_pop t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          spsc_queue_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          spsc_queue_model t vs'
      end
    | RET o;
      spsc_queue_consumer t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & %data & -> & #Hmeta & #Hdata & #Hinv) & (%_l & %_γ & %front & %Heq & #_Hmeta & Hconsumer_ctl₁ & Hconsumer_region)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%_front & %back1 & %vs1 & %hist1 & >(%Hback1 & %Hback1_le) & >(%Hhist1_len & %Hvs1) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hdata_back & Hdata_extra)".
    wp_load.
    iDestruct (spsc_queue_consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
    iDestruct (array_cslice_to_inv with "Hdata_vs") as "#Hdata_inv".
    iSplitR "Hconsumer_ctl₁ Hconsumer_region HΦ".
    { iExists front, back1, vs1, hist1. iSteps. }
    iModIntro. clear.

    wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%_front & %back2 & %vs2 & %hist2 & >(%Hback2 & %Hback2_le) & >(%Hhist2_len & %Hvs2) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hdata_back & Hdata_extra)".
    wp_load.
    iDestruct (spsc_queue_consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
    destruct (decide (front < back2)) as [Hbranch | Hbranch].

    - destruct vs2 as [| v vs2]; first naive_solver lia.
      iDestruct (spsc_queue_back_lb_get with "Hproducer_ctl₂") as "#Hback_lb".
      iDestruct "Hdata_front" as "[Hdata_front | Hconsumer_region']"; last first.
      { iDestruct (spsc_queue_consumer_region_exclusive with "Hconsumer_region Hconsumer_region'") as %[]. }
      iDestruct (spsc_queue_history_mapsto_get front v with "Hhistory_auth") as "#Hhistory_mapsto".
      { rewrite -(take_drop front hist2) -Hvs2 lookup_app_r take_length; first lia.
        rewrite Nat.min_l; first lia.
        rewrite Nat.sub_diag //.
      }
      iSplitR "Hconsumer_ctl₁ Hdata_front HΦ".
      { iExists front, back2, (v :: vs2), hist2. iSteps. }
      iModIntro. clear- Hbranch.

      wp_pures. rewrite bool_decide_eq_true_2; first lia.
      wp_load.
      wp_smart_apply (array_cget_spec with "Hdata_front") as "Hdata_front"; first done.
      wp_smart_apply (array_cset_spec with "Hdata_front") as "Hdata_front"; first done.
      wp_pures.

      wp_bind (_ <- _)%E.
      iInv "Hinv" as "(%_front & %back3 & %vs3 & %hist3 & >(%Hback3 & %Hback3_le) & >(%Hhist3_len & %Hvs3) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hconsumer_region & Hdata_vs & Hdata_back & Hdata_extra)".
      wp_store.
      iDestruct (spsc_queue_consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
      iDestruct (spsc_queue_back_lb_valid with "Hproducer_ctl₂ Hback_lb") as %Hback2.
      destruct vs3 as [| _v vs3]; first naive_solver lia.
      iDestruct (spsc_queue_history_agree with "Hhistory_auth Hhistory_mapsto") as %Hhist3_lookup.
      assert (_v = v) as ->.
      { move: Hhist3_lookup.
        rewrite -(take_drop front hist3) -Hvs3 lookup_app_r take_length; first lia.
        rewrite Nat.min_l; first lia.
        rewrite Nat.sub_diag. naive_solver.
      }
      rewrite /= drop_0.
      iDestruct "Hconsumer_region" as "[Hdata_front' | Hconsumer_region]".
      { iDestruct (array_cslice_exclusive with "Hdata_front Hdata_front'") as %[]; [simpl; lia | done]. }
      iMod (spsc_queue_consumer_ctl_update (S front) with "Hconsumer_ctl₁ Hconsumer_ctl₂") as "(Hconsumer_ctl₁ & Hconsumer_ctl₂)"; first lia.
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (spsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (spsc_queue_model_update vs3 with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "Hconsumer_ctl₁ Hconsumer_region HΦ".
      { do 2 iModIntro. iExists (S front), back3, vs3, hist3. iFrame. simpl in *.
        iSplit; first iSteps.
        iSplit. { erewrite drop_S in Hvs3; last done. iSteps. }
        iSplitL "Hfront"; first iSteps.
        rewrite assoc. iSplitL "Hdata_vs".
        - rewrite -{1}(take_drop 1 vs3) fmap_app -array_cslice_app fmap_length take_length.
          destruct vs3; last rewrite Nat.add_1_r; iSteps.
        - iDestruct (array_cslice_shift with "Hdata_front") as "Hdata_front".
          case_decide as Hcase.
          + rewrite -Hcase decide_False; first lia.
            assert (sz - (back3 - S front) - 1 = 0) as -> by lia.
            iSteps.
          + rewrite decide_False; first lia.
            iFrame.
            iDestruct (array_cslice_app_1 with "Hdata_extra Hdata_front") as "Hdata_extra".
            { rewrite replicate_length. lia. }
            rewrite -replicate_S_end.
            assert (S (sz - (back3 - front) - 1) = sz - (back3 - S front) - 1) as -> by lia.
            iSteps.
      }
      iModIntro. clear.

      iSteps.

    - assert (front = back2) as <- by lia. clear Hbranch.
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (spsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      assert (length vs2 = 0) as ->%nil_length_inv by lia.
      iMod ("HΦ" $! None with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "Hconsumer_ctl₁ Hconsumer_region HΦ"; first iSteps.
      iModIntro. clear.

      iSteps.
  Qed.
End spsc_queue_G.

#[global] Opaque spsc_queue_create.
#[global] Opaque spsc_queue_push.
#[global] Opaque spsc_queue_pop.

#[global] Opaque spsc_queue_inv.
#[global] Opaque spsc_queue_model.
#[global] Opaque spsc_queue_producer.
#[global] Opaque spsc_queue_consumer.
