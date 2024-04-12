(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/65211c5176b632bd9ed268c0c608ac483f88a992/src_lockfree/spsc_queue.ml
*)

From iris.algebra Require Import
  list.

From zebre Require Import
  prelude.
From zebre.common Require Import
  relations
  list.
From zebre.iris.base_logic Require Import
  lib.excl
  lib.twins
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

Implicit Types b : bool.
Implicit Types i front front_cache back back_cache : nat.
Implicit Types l : location.
Implicit Types v w t data : val.
Implicit Types vs hist : list val.

#[local] Notation "'data'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'front'" := (
  in_type "t" 1
)(in custom zebre_field
).
#[local] Notation "'front_cache'" := (
  in_type "t" 2
)(in custom zebre_field
).
#[local] Notation "'back'" := (
  in_type "t" 3
)(in custom zebre_field
).
#[local] Notation "'back_cache'" := (
  in_type "t" 4
)(in custom zebre_field
).

Definition spsc_bqueue_create : val :=
  λ: "cap",
    { array_make "cap" §None; #0; #0; #0; #0 }.

#[local] Definition spsc_bqueue_push_aux : val :=
  λ: "t" "data" "back",
    let: "cap" := array_size "data" in
    let: "front_cache" := "t".{front_cache} in
    if: "back" < "front_cache" + "cap" then (
      #true
    ) else (
      let: "front" := "t".{front} in
      "t" <-{front_cache} "front" ;;
      "back" < "front" + "cap"
    ).
Definition spsc_bqueue_push : val :=
  λ: "t" "v",
    let: "data" := "t".{data} in
    let: "back" := "t".{back} in
    if: spsc_bqueue_push_aux "t" "data" "back" then (
      array_cset "data" "back" ‘Some{ "v" } ;;
      "t" <-{back} #1 + "back" ;;
      #false
    ) else (
      #true
    ).

#[local] Definition spsc_bqueue_pop_aux : val :=
  λ: "t" "front",
    let: "back_cache" := "t".{back_cache} in
    if: "front" < "back_cache" then (
      #true
    ) else (
      let: "back" := "t".{back} in
      "t" <-{back_cache} "back" ;;
      "front" < "back"
    ).
Definition spsc_bqueue_pop : val :=
  λ: "t",
    let: "front" := "t".{front} in
    if: spsc_bqueue_pop_aux "t" "front" then (
      let: "data" := "t".{data} in
      let: "res" := array_cget "data" "front" in
      array_cset "data" "front" §None ;;
      "t" <-{front} #1 + "front" ;;
      "res"
    ) else (
      §None
    ).

Class SpscBqueueG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] spsc_bqueue_G_model_G :: TwinsG Σ (listO valO) ;
  #[local] spsc_bqueue_G_history_G :: MonoListG Σ val ;
  #[local] spsc_bqueue_G_ctl_G :: AuthNatMaxG Σ ;
  #[local] spsc_bqueue_G_region_G :: ExclG Σ unitO ;
}.

Definition spsc_bqueue_Σ := #[
  twins_Σ (listO valO) ;
  mono_list_Σ val ;
  auth_nat_max_Σ ;
  excl_Σ unitO
].
Lemma subG_spsc_bqueue_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG spsc_bqueue_Σ Σ →
  SpscBqueueG Σ.
Proof.
  solve_inG.
Qed.

Section spsc_bqueue_G.
  Context `{spsc_bqueue_G : SpscBqueueG Σ}.

  Record spsc_bqueue_meta := {
    spsc_bqueue_meta_model : gname ;
    spsc_bqueue_meta_history : gname ;
    spsc_bqueue_meta_producer_ctl : gname ;
    spsc_bqueue_meta_producer_region : gname ;
    spsc_bqueue_meta_consumer_ctl : gname ;
    spsc_bqueue_meta_consumer_region : gname ;
  }.
  Implicit Types γ : spsc_bqueue_meta.

  #[local] Instance spsc_bqueue_meta_eq_dec : EqDecision spsc_bqueue_meta :=
    ltac:(solve_decision).
  #[local] Instance spsc_bqueue_meta_countable :
    Countable spsc_bqueue_meta.
  Proof.
    pose encode γ := (
      γ.(spsc_bqueue_meta_model),
      γ.(spsc_bqueue_meta_history),
      γ.(spsc_bqueue_meta_producer_ctl),
      γ.(spsc_bqueue_meta_producer_region),
      γ.(spsc_bqueue_meta_consumer_ctl),
      γ.(spsc_bqueue_meta_consumer_region)
    ).
    pose decode := λ '(γ_model, γ_history, γ_producer_ctl, γ_producer_region, γ_consumer_ctl, γ_consumer_region), {|
      spsc_bqueue_meta_model := γ_model ;
      spsc_bqueue_meta_history := γ_history ;
      spsc_bqueue_meta_producer_ctl := γ_producer_ctl ;
      spsc_bqueue_meta_producer_region := γ_producer_region ;
      spsc_bqueue_meta_consumer_ctl := γ_consumer_ctl ;
      spsc_bqueue_meta_consumer_region := γ_consumer_region ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition spsc_bqueue_model₁' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition spsc_bqueue_model₁ γ vs :=
    spsc_bqueue_model₁' γ.(spsc_bqueue_meta_model) vs.
  #[local] Definition spsc_bqueue_model₂' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition spsc_bqueue_model₂ γ vs :=
    spsc_bqueue_model₂' γ.(spsc_bqueue_meta_model) vs.

  #[local] Definition spsc_bqueue_history_auth' γ_history hist :=
    mono_list_auth γ_history (DfracOwn 1) hist.
  #[local] Definition spsc_bqueue_history_auth γ hist :=
    spsc_bqueue_history_auth' γ.(spsc_bqueue_meta_history) hist.
  #[local] Definition spsc_bqueue_history_elem γ i v :=
    mono_list_elem γ.(spsc_bqueue_meta_history) i v.

  #[local] Definition spsc_bqueue_producer_ctl₁' γ_producer_ctl back :=
    auth_nat_max_auth γ_producer_ctl (DfracOwn (1/2)) back.
  #[local] Definition spsc_bqueue_producer_ctl₁ γ back :=
    spsc_bqueue_producer_ctl₁' γ.(spsc_bqueue_meta_producer_ctl) back.
  #[local] Definition spsc_bqueue_producer_ctl₂' γ_producer_ctl back :=
    auth_nat_max_auth γ_producer_ctl (DfracOwn (1/2)) back.
  #[local] Definition spsc_bqueue_producer_ctl₂ γ back :=
    spsc_bqueue_producer_ctl₂' γ.(spsc_bqueue_meta_producer_ctl) back.
  #[local] Definition spsc_bqueue_back_lb γ back :=
    auth_nat_max_lb γ.(spsc_bqueue_meta_producer_ctl) back.

  #[local] Definition spsc_bqueue_producer_region' γ_producer_region :=
    excl γ_producer_region ().
  #[local] Definition spsc_bqueue_producer_region γ :=
    spsc_bqueue_producer_region' γ.(spsc_bqueue_meta_producer_region).

  #[local] Definition spsc_bqueue_consumer_ctl₁' γ_consumer_ctl front :=
    auth_nat_max_auth γ_consumer_ctl (DfracOwn (1/2)) front.
  #[local] Definition spsc_bqueue_consumer_ctl₁ γ front :=
    spsc_bqueue_consumer_ctl₁' γ.(spsc_bqueue_meta_consumer_ctl) front.
  #[local] Definition spsc_bqueue_consumer_ctl₂' γ_consumer_ctl front :=
    auth_nat_max_auth γ_consumer_ctl (DfracOwn (1/2)) front.
  #[local] Definition spsc_bqueue_consumer_ctl₂ γ front :=
    spsc_bqueue_consumer_ctl₂' γ.(spsc_bqueue_meta_consumer_ctl) front.
  #[local] Definition spsc_bqueue_front_lb γ front :=
    auth_nat_max_lb γ.(spsc_bqueue_meta_consumer_ctl) front.

  #[local] Definition spsc_bqueue_consumer_region' γ_consumer_region :=
    excl γ_consumer_region ().
  #[local] Definition spsc_bqueue_consumer_region γ :=
    spsc_bqueue_consumer_region' γ.(spsc_bqueue_meta_consumer_region).

  #[local] Definition spsc_bqueue_inv_inner l γ cap data : iProp Σ :=
    ∃ front back vs hist,
    ⌜back = (front + length vs)%nat ∧ back ≤ front + cap⌝ ∗
    ⌜length hist = back ∧ vs = drop front hist⌝ ∗
    l.[front] ↦ #front ∗
    spsc_bqueue_consumer_ctl₂ γ front ∗
    l.[back] ↦ #back ∗
    spsc_bqueue_producer_ctl₂ γ back ∗
    spsc_bqueue_model₂ γ vs ∗
    spsc_bqueue_history_auth γ hist ∗
    ( array_cslice data cap front (DfracOwn 1) ((λ v, ’Some{ v }) <$> take 1 vs)
    ∨ spsc_bqueue_consumer_region γ
    ) ∗
    array_cslice data cap (S front) (DfracOwn 1) ((λ v, ’Some{ v }) <$> drop 1 vs) ∗
    ( array_cslice data cap back (DfracOwn 1) (if decide (back = front + cap) then [] else [§None])
    ∨ spsc_bqueue_producer_region γ
    ) ∗
    array_cslice data cap (S back) (DfracOwn 1) (replicate (cap - (back - front) - 1) §None).
  Definition spsc_bqueue_inv t ι cap : iProp Σ :=
    ∃ l γ data,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[data] ↦□ data ∗
    inv ι (spsc_bqueue_inv_inner l γ cap data).

  Definition spsc_bqueue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    spsc_bqueue_model₁ γ vs.

  Definition spsc_bqueue_producer t : iProp Σ :=
    ∃ l γ front_cache back,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[front_cache] ↦ #front_cache ∗
    spsc_bqueue_producer_ctl₁ γ back ∗
    spsc_bqueue_producer_region γ ∗
    spsc_bqueue_front_lb γ front_cache.

  Definition spsc_bqueue_consumer t : iProp Σ :=
    ∃ l γ front back_cache,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[back_cache] ↦ #back_cache ∗
    spsc_bqueue_consumer_ctl₁ γ front ∗
    spsc_bqueue_consumer_region γ ∗
    spsc_bqueue_back_lb γ back_cache.

  #[global] Instance spsc_bqueue_inv_persistent t ι cap :
    Persistent (spsc_bqueue_inv t ι cap).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue_model_timeless t vs :
    Timeless (spsc_bqueue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue_producer_timeless t :
    Timeless (spsc_bqueue_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue_consumer_timeless t :
    Timeless (spsc_bqueue_consumer t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma spsc_bqueue_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      spsc_bqueue_model₁' γ_model [] ∗
      spsc_bqueue_model₂' γ_model [].
  Proof.
    iMod (twins_alloc' (twins_G := spsc_bqueue_G_model_G) []) as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma spsc_bqueue_model_agree γ model1 model2 :
    spsc_bqueue_model₁ γ model1 -∗
    spsc_bqueue_model₂ γ model2 -∗
    ⌜model1 = model2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (twins_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iSteps.
  Qed.
  #[local] Lemma spsc_bqueue_model_update {γ model1 model2} model :
    spsc_bqueue_model₁ γ model1 -∗
    spsc_bqueue_model₂ γ model2 ==∗
      spsc_bqueue_model₁ γ model ∗
      spsc_bqueue_model₂ γ model.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iMod (twins_update' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
    iSteps.
  Qed.

  #[local] Lemma spsc_bqueue_history_alloc :
    ⊢ |==>
      ∃ γ_history,
      spsc_bqueue_history_auth' γ_history [].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma spsc_bqueue_history_elem_get {γ hist} i v :
    hist !! i = Some v →
    spsc_bqueue_history_auth γ hist ⊢
    spsc_bqueue_history_elem γ i v.
  Proof.
    setoid_rewrite mono_list_lb_get. apply mono_list_elem_get.
  Qed.
  #[local] Lemma spsc_bqueue_history_agree γ hist i v :
    spsc_bqueue_history_auth γ hist -∗
    spsc_bqueue_history_elem γ i v -∗
    ⌜hist !! i = Some v⌝.
  Proof.
    apply mono_list_lookup.
  Qed.
  #[local] Lemma spsc_bqueue_history_update {γ hist} v :
    spsc_bqueue_history_auth γ hist ⊢ |==>
    spsc_bqueue_history_auth γ (hist ++ [v]).
  Proof.
    apply mono_list_update_app.
  Qed.

  #[local] Lemma spsc_bqueue_producer_ctl_alloc :
    ⊢ |==>
      ∃ γ_producer_ctl,
      spsc_bqueue_producer_ctl₁' γ_producer_ctl 0 ∗
      spsc_bqueue_producer_ctl₂' γ_producer_ctl 0.
  Proof.
    iMod auth_nat_max_alloc as "(%γ_producer_ctl & Hproducer_ctl₁ & Hproducer_ctl₂)".
    iSteps.
  Qed.
  #[local] Lemma spsc_bqueue_producer_ctl_agree γ back1 back2 :
    spsc_bqueue_producer_ctl₁ γ back1 -∗
    spsc_bqueue_producer_ctl₂ γ back2 -∗
    ⌜back1 = back2⌝.
  Proof.
    apply auth_nat_max_auth_agree.
  Qed.
  #[local] Lemma spsc_bqueue_producer_ctl_update {γ back1 back2} back :
    back1 ≤ back →
    spsc_bqueue_producer_ctl₁ γ back1 -∗
    spsc_bqueue_producer_ctl₂ γ back2 ==∗
      spsc_bqueue_producer_ctl₁ γ back ∗
      spsc_bqueue_producer_ctl₂ γ back.
  Proof.
    iIntros "%Hle Hproducer_ctl₁ Hproducer_ctl₂".
    iDestruct (auth_nat_max_auth_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %->.
    iCombine "Hproducer_ctl₁ Hproducer_ctl₂" as "Hproducer_ctl".
    iMod (auth_nat_max_update with "Hproducer_ctl") as "($ & $)"; done.
  Qed.
  #[local] Lemma spsc_bqueue_back_lb_get γ back :
    spsc_bqueue_producer_ctl₂ γ back ⊢
    spsc_bqueue_back_lb γ back.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma spsc_bqueue_back_lb_valid γ back1 back2 :
    spsc_bqueue_producer_ctl₂ γ back1 -∗
    spsc_bqueue_back_lb γ back2 -∗
    ⌜back2 ≤ back1⌝.
  Proof.
    apply auth_nat_max_lb_valid.
  Qed.

  #[local] Lemma spsc_bqueue_producer_region_alloc :
    ⊢ |==>
      ∃ γ_producer_region,
      spsc_bqueue_producer_region' γ_producer_region.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma spsc_bqueue_producer_region_exclusive γ :
    spsc_bqueue_producer_region γ -∗
    spsc_bqueue_producer_region γ -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  #[local] Lemma spsc_bqueue_consumer_ctl_alloc :
    ⊢ |==>
      ∃ γ_consumer_ctl,
      spsc_bqueue_consumer_ctl₁' γ_consumer_ctl 0 ∗
      spsc_bqueue_consumer_ctl₂' γ_consumer_ctl 0.
  Proof.
    iMod auth_nat_max_alloc as "(%γ_consumer_ctl & Hconsumer_ctl₁ & Hconsumer_ctl₂)".
    iSteps.
  Qed.
  #[local] Lemma spsc_bqueue_consumer_ctl_agree γ front1 front2 :
    spsc_bqueue_consumer_ctl₁ γ front1 -∗
    spsc_bqueue_consumer_ctl₂ γ front2 -∗
    ⌜front1 = front2⌝.
  Proof.
    apply auth_nat_max_auth_agree.
  Qed.
  #[local] Lemma spsc_bqueue_consumer_ctl_update {γ front1 front2} front :
    front1 ≤ front →
    spsc_bqueue_consumer_ctl₁ γ front1 -∗
    spsc_bqueue_consumer_ctl₂ γ front2 ==∗
      spsc_bqueue_consumer_ctl₁ γ front ∗
      spsc_bqueue_consumer_ctl₂ γ front.
  Proof.
    iIntros "%Hle Hconsumer_ctl₁ Hconsumer_ctl₂".
    iDestruct (auth_nat_max_auth_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %->.
    iCombine "Hconsumer_ctl₁ Hconsumer_ctl₂" as "Hconsumer_ctl".
    iMod (auth_nat_max_update with "Hconsumer_ctl") as "($ & $)"; done.
  Qed.
  #[local] Lemma spsc_bqueue_front_lb_get γ front :
    spsc_bqueue_consumer_ctl₂ γ front ⊢
    spsc_bqueue_front_lb γ front.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma spsc_bqueue_front_lb_valid γ front1 front2 :
    spsc_bqueue_consumer_ctl₂ γ front1 -∗
    spsc_bqueue_front_lb γ front2 -∗
    ⌜front2 ≤ front1⌝.
  Proof.
    iIntros "Hconsumer_ctl₁ Hfront_lb".
    iApply (auth_nat_max_lb_valid with "Hconsumer_ctl₁ Hfront_lb").
  Qed.

  #[local] Lemma spsc_bqueue_consumer_region_alloc :
    ⊢ |==>
      ∃ γ_consumer_region,
      spsc_bqueue_consumer_region' γ_consumer_region.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma spsc_bqueue_consumer_region_exclusive γ :
    spsc_bqueue_consumer_region γ -∗
    spsc_bqueue_consumer_region γ -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  Lemma spsc_bqueue_producer_exclusive t :
    spsc_bqueue_producer t -∗
    spsc_bqueue_producer t -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma spsc_bqueue_consumer_exclusive t :
    spsc_bqueue_consumer t -∗
    spsc_bqueue_consumer t -∗
    False.
  Proof.
    iSteps.
  Qed.

  #[local] Instance hint_array_cslice_nil t cap i dq :
    HINT ε₁ ✱ [- ; array_inv t cap] ⊫ [id]; array_cslice t cap i dq [] ✱ [emp].
  Proof.
    iSteps. rewrite array_cslice_nil. iSteps.
  Qed.

  Lemma spsc_bqueue_create_spec ι cap :
    (0 ≤ cap)%Z →
    {{{ True }}}
      spsc_bqueue_create #cap
    {{{ t,
      RET t;
      spsc_bqueue_inv t ι (Z.to_nat cap) ∗
      spsc_bqueue_model t [] ∗
      spsc_bqueue_producer t ∗
      spsc_bqueue_consumer t
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp_rec.
    iApply wp_fupd.
    wp_apply (array_make_spec with "[//]") as "%data Hdata_model"; first done.
    wp_record l as "Hmeta" "(Hdata & Hfront & Hfront_cache & Hback & Hback_cache & _)".
    iMod (pointsto_persist with "Hdata") as "#Hdata".

    iMod spsc_bqueue_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod spsc_bqueue_history_alloc as "(%γ_history & Hhistory_auth)".
    iMod spsc_bqueue_producer_ctl_alloc as "(%γ_producer_ctl & Hproducer_ctl₁ & Hproducer_ctl₂)".
    iMod spsc_bqueue_producer_region_alloc as "(%γ_producer_region & Hproducer_region)".
    iMod spsc_bqueue_consumer_ctl_alloc as "(%γ_consumer_ctl & Hconsumer_ctl₁ & Hconsumer_ctl₂)".
    iMod spsc_bqueue_consumer_region_alloc as "(%γ_consumer_region & Hconsumer_region)".

    pose γ := {|
      spsc_bqueue_meta_model := γ_model ;
      spsc_bqueue_meta_history := γ_history ;
      spsc_bqueue_meta_producer_ctl := γ_producer_ctl ;
      spsc_bqueue_meta_producer_region := γ_producer_region ;
      spsc_bqueue_meta_consumer_ctl := γ_consumer_ctl ;
      spsc_bqueue_meta_consumer_region := γ_consumer_region ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iDestruct (spsc_bqueue_back_lb_get γ with "Hproducer_ctl₂") as "#Hback_lb".
    iDestruct (spsc_bqueue_front_lb_get γ with "Hconsumer_ctl₂") as "#Hfront_lb".

    iApply "HΦ".
    iSplitL "Hdata_model Hfront Hback Hmodel₂ Hhistory_auth Hproducer_ctl₂ Hconsumer_ctl₂"; last iSteps.
    iStep 3. iApply inv_alloc. iExists 0, 0, [], []. iStep 7.
    iDestruct (array_model_to_inv with "Hdata_model") as "#Hdata_size". rewrite replicate_length.
    iStep 4.
    Z_to_nat cap. rewrite Nat2Z.id. destruct cap as [| cap]; first iSteps.
    iDestruct (array_model_to_cslice with "Hdata_model") as "Hdata_cslice".
    rewrite replicate_length -(take_drop 1 (replicate _ _)).
    iDestruct (array_cslice_app with "Hdata_cslice") as "(Hdata_back & Hdata_extra)".
    rewrite Nat.add_0_l take_replicate_add. iStep.
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  #[local] Definition spsc_bqueue_push_au l ι cap v Φ : iProp Σ :=
    AU <{
      ∃∃ vs,
      spsc_bqueue_model #l vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      spsc_bqueue_model #l (if decide (length vs = cap) then vs else vs ++ [v]),
    COMM
      spsc_bqueue_producer #l -∗
      Φ #(bool_decide (length vs = cap))
    }>.
  #[local] Lemma spsc_bqueue_push_aux_spec l ι γ cap data front_cache back v Ψ :
    {{{
      meta l nroot γ ∗
      inv ι (spsc_bqueue_inv_inner l γ cap data) ∗
      array_inv data cap ∗
      l.[front_cache] ↦ #front_cache ∗
      spsc_bqueue_producer_ctl₁ γ back ∗
      spsc_bqueue_front_lb γ front_cache ∗
      spsc_bqueue_push_au l ι cap v Ψ
    }}}
      spsc_bqueue_push_aux #l data #back
    {{{ b front_cache',
      RET #b;
      ⌜b = bool_decide (back < front_cache' + cap)⌝ ∗
      l.[front_cache] ↦ #front_cache' ∗
      spsc_bqueue_producer_ctl₁ γ back ∗
      spsc_bqueue_front_lb γ front_cache' ∗
      if b then
        spsc_bqueue_push_au l ι cap v Ψ
      else
        spsc_bqueue_producer #l -∗
        Ψ #true
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hdata_inv & Hfront_cache & Hproducer_ctl₁ & #Hfront_lb & HΨ) HΦ".

    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hdata_inv") as "_".
    wp_load. wp_pures.
    case_bool_decide as Hbranch1; wp_pures.

    - iSpecialize ("HΦ" $! true front_cache). rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - wp_bind (!_)%E.
      iInv "Hinv" as "(%front & %_back & %vs & %hist & >(%Hback & %Hback_le) & >(%Hhist_len & %Hvs) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hdata_back & Hdata_extra)".
      wp_load.
      iDestruct (spsc_bqueue_producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
      iClear "Hfront_lb". iDestruct (spsc_bqueue_front_lb_get with "Hconsumer_ctl₂") as "#Hfront_lb".
      destruct (decide (back < front + cap)) as [Hbranch2 | Hbranch2].

      + iSplitR "Hfront_cache Hproducer_ctl₁ HΨ HΦ"; first iSteps.
        iModIntro. clear- Hbranch2.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ front).
        rewrite !bool_decide_eq_true_2; [lia.. |]. iSteps.

      + iMod "HΨ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (spsc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
        rewrite decide_True; [lia.. |]. rewrite bool_decide_eq_true_2; first lia.
        iMod ("HΨ" with "[Hmodel₁]") as "HΨ"; first iSteps.
        iSplitR "Hfront_cache Hproducer_ctl₁ HΨ HΦ"; first iSteps.
        iModIntro. clear- Hbranch2.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ front).
        rewrite !bool_decide_eq_false_2; [lia.. |]. iSteps.
  Qed.
  Lemma spsc_bqueue_push_spec t ι cap v :
    <<<
      spsc_bqueue_inv t ι cap ∗
      spsc_bqueue_producer t
    | ∀∀ vs,
      spsc_bqueue_model t vs
    >>>
      spsc_bqueue_push t v @ ↑ι
    <<<
      spsc_bqueue_model t (if decide (length vs = cap) then vs else vs ++ [v])
    | RET #(bool_decide (length vs = cap));
      spsc_bqueue_producer t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & %data & -> & #Hmeta & #Hdata & #Hinv) & (%_l & %_γ & %front_cache & %back & %Heq & #_Hmeta & Hfront_cache & Hproducer_ctl₁ & Hproducer_region & #Hfront_lb)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_load. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%front1 & %_back & %vs1 & %hist1 & >(%Hback & %Hback_le) & >(%Hhist1_len & %Hvs1) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hdata_back & Hdata_extra)".
    wp_load.
    iDestruct (spsc_bqueue_producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
    iDestruct (array_cslice_to_inv with "Hdata_vs") as "#Hdata_inv".
    iSplitR "Hfront_cache Hproducer_ctl₁ Hproducer_region HΦ"; first iSteps.
    iModIntro. clear.

    iDestruct "Hfront_lb" as "-#Hfront_lb". wp_smart_apply (spsc_bqueue_push_aux_spec with "[$]") as (? front_cache') "(-> & Hfront_cache & Hproducer_ctl₁ & #Hfront_lb & HΦ)".
    case_bool_decide as Hbranch; last iSteps.

    iApply fupd_wp.
    iInv "Hinv" as "(%front2 & %_back & %vs2 & %hist2 & >(%Hback & %Hback_le) & >(%Hhist2_len & %Hvs2) & Hfront & >Hconsumer_ctl₂ & Hback & >Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & >Hdata_back & Hdata_extra)".
    iDestruct (spsc_bqueue_producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
    iDestruct "Hdata_back" as "[Hdata_back | Hproducer_region']"; last first.
    { iDestruct (spsc_bqueue_producer_region_exclusive with "Hproducer_region Hproducer_region'") as %[]. }
    iDestruct (spsc_bqueue_front_lb_valid with "Hconsumer_ctl₂ Hfront_lb") as %Hfront2.
    rewrite decide_False; first lia.
    iSplitR "Hfront_cache Hproducer_ctl₁ Hdata_back HΦ"; first iSteps.
    iModIntro. clear- Hbranch. iModIntro.

    wp_smart_apply (array_cset_spec with "Hdata_back") as "Hdata_back"; first done.
    wp_pures.

    wp_bind (_ <- _)%E.
    iInv "Hinv" as "(%front3 & %_back & %vs3 & %hist3 & >(%Hback & %Hback_le) & >(%Hhist3_len & %Hvs3) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hproducer_region & Hdata_extra)".
    wp_store.
    iDestruct (spsc_bqueue_producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
    iDestruct (spsc_bqueue_front_lb_valid with "Hconsumer_ctl₂ Hfront_lb") as %Hfront3_ge.
    iDestruct "Hproducer_region" as "[Hdata_back' | Hproducer_region]".
    { rewrite decide_False; first lia.
      iDestruct (array_cslice_exclusive with "Hdata_back Hdata_back'") as %[]; [simpl; lia | done].
    }
    iMod (spsc_bqueue_producer_ctl_update (S back) with "Hproducer_ctl₁ Hproducer_ctl₂") as "(Hproducer_ctl₁ & Hproducer_ctl₂)"; first lia.
    iMod (spsc_bqueue_history_update v with "Hhistory_auth") as "Hhistory_auth".
    iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (spsc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (spsc_bqueue_model_update (vs3 ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    rewrite decide_False; first lia.
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    rewrite bool_decide_eq_false_2; first lia.
    iSplitR "Hfront_cache Hproducer_ctl₁ Hproducer_region HΦ".
    { do 2 iModIntro. iExists front3, (S back), (vs3 ++ [v]), (hist3 ++ [v]). iFrame.
      iSplit. { rewrite app_length. iSteps. }
      iSplit. { rewrite Hvs3 app_length drop_app_le; first lia. iSteps. }
      iSplitL "Hback"; first iSteps.
      rewrite assoc. iSplitL "Hdata_front Hdata_vs Hdata_back".
      - destruct vs3 as [| v' vs3].
        + assert (front3 = back) as -> by naive_solver lia. iSteps.
        + iFrame. rewrite /= !drop_0 fmap_app.
          iApply (array_cslice_app_1 with "Hdata_vs Hdata_back").
          rewrite fmap_length. naive_solver lia.
      - case_decide.
        + assert (cap - (S back - front3) - 1 = 0) as -> by lia. iSteps.
        + iDestruct (array_cslice_app_2 [§None] (replicate (cap - (S back - front3) - 1) §None) with "Hdata_extra") as "(Hdata_back' & Hdata_extra)".
          { rewrite /= -replicate_S. f_equal. lia. }
          rewrite Nat.add_1_r. iSteps.
    }
    iModIntro. clear.

    iSteps.
  Qed.

  #[local] Definition spsc_bqueue_pop_au l ι Φ : iProp Σ :=
    AU <{
      ∃∃ vs,
      spsc_bqueue_model #l vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      spsc_bqueue_model #l (tail vs),
    COMM
      spsc_bqueue_consumer #l -∗
      Φ (head vs : val)
    }>.
  #[local] Lemma spsc_bqueue_pop_aux_spec l ι γ cap data front back_cache Ψ :
    {{{
      meta l nroot γ ∗
      inv ι (spsc_bqueue_inv_inner l γ cap data) ∗
      l.[back_cache] ↦ #back_cache ∗
      spsc_bqueue_consumer_ctl₁ γ front ∗
      spsc_bqueue_back_lb γ back_cache ∗
      spsc_bqueue_pop_au l ι Ψ
    }}}
      spsc_bqueue_pop_aux #l #front
    {{{ b back_cache',
      RET #b;
      ⌜b = bool_decide (front < back_cache')⌝ ∗
      l.[back_cache] ↦ #back_cache' ∗
      spsc_bqueue_consumer_ctl₁ γ front ∗
      spsc_bqueue_back_lb γ back_cache' ∗
      if b then
        spsc_bqueue_pop_au l ι Ψ
      else
        spsc_bqueue_consumer #l -∗
        Ψ None
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & Hback_cache & Hconsumer_ctl₁ & #Hback_lb & HΨ) HΦ".

    wp_rec.
    wp_load. wp_pures.
    case_bool_decide as Hbranch1; wp_pures.

    - iSpecialize ("HΦ" $! true back_cache). rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - wp_bind (!_)%E.
      iInv "Hinv" as "(%_front & %back & %vs & %hist & >(%Hback & %Hback_le) & >(%Hhist_len & %Hvs) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hdata_back & Hdata_extra)".
      wp_load.
      iDestruct (spsc_bqueue_consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
      iClear "Hback_lb". iDestruct (spsc_bqueue_back_lb_get with "Hproducer_ctl₂") as "#Hback_lb".
      destruct (decide (front < back)) as [Hbranch2 | Hbranch2].

      + iSplitR "Hback_cache Hconsumer_ctl₁ HΨ HΦ".
        { iExists front, back, vs, hist. iSteps. }
        iModIntro. clear- Hbranch2.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ back).
        rewrite !bool_decide_eq_true_2; [lia.. |]. iSteps.

      + assert (front = back) as <- by lia.
        iMod "HΨ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (spsc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
        assert (length vs = 0) as ->%nil_length_inv by lia.
        iMod ("HΨ" with "[Hmodel₁]") as "HΨ"; first iSteps.
        iSplitR "Hback_cache Hconsumer_ctl₁ HΨ HΦ"; first iSteps.
        iModIntro. clear- Hbranch2.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ front).
        rewrite !bool_decide_eq_false_2; [lia.. |]. iSteps.
  Qed.
  Lemma spsc_bqueue_pop_spec t ι cap :
    <<<
      spsc_bqueue_inv t ι cap ∗
      spsc_bqueue_consumer t
    | ∀∀ vs,
      spsc_bqueue_model t vs
    >>>
      spsc_bqueue_pop t @ ↑ι
    <<<
      spsc_bqueue_model t (tail vs)
    | RET head vs;
      spsc_bqueue_consumer t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & %data & -> & #Hmeta & #Hdata & #Hinv) & (%_l & %_γ & %front & %back_cache & %Heq & #_Hmeta & Hback_cache & Hconsumer_ctl₁ & Hconsumer_region & #Hback_lb)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%_front & %back1 & %vs1 & %hist1 & >(%Hback1 & %Hback1_le) & >(%Hhist1_len & %Hvs1) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hdata_front & Hdata_vs & Hdata_back & Hdata_extra)".
    wp_load.
    iDestruct (spsc_bqueue_consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
    iDestruct (array_cslice_to_inv with "Hdata_vs") as "#Hdata_inv".
    iSplitR "Hback_cache Hconsumer_ctl₁ Hconsumer_region HΦ".
    { iExists front, back1, vs1, hist1. iSteps. }
    iModIntro. clear.

    iDestruct "Hback_lb" as "-#Hback_lb". wp_smart_apply (spsc_bqueue_pop_aux_spec with "[$]") as (? back_cache') "(-> & Hback_cache & Hconsumer_ctl₁ & #Hback_lb & HΦ)".
    case_bool_decide as Hbranch; last iSteps.

    iApply fupd_wp.
    iInv "Hinv" as "(%_front & %back2 & %vs2 & %hist2 & >(%Hback2 & %Hback2_le) & >(%Hhist2_len & %Hvs2) & Hfront & >Hconsumer_ctl₂ & Hback & >Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & >Hdata_front & Hdata_vs & Hdata_back & Hdata_extra)".
    iDestruct (spsc_bqueue_consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
    iDestruct (spsc_bqueue_back_lb_valid with "Hproducer_ctl₂ Hback_lb") as %Hback2_ge.
    destruct vs2 as [| v vs2]; first naive_solver lia.
    iDestruct "Hdata_front" as "[Hdata_front | Hconsumer_region']"; last first.
    { iDestruct (spsc_bqueue_consumer_region_exclusive with "Hconsumer_region Hconsumer_region'") as %[]. }
    iDestruct (spsc_bqueue_history_elem_get front v with "Hhistory_auth") as "#Hhistory_elem".
    { rewrite -(take_drop front hist2) -Hvs2 lookup_app_r take_length; first lia.
      rewrite Nat.min_l; first lia.
      rewrite Nat.sub_diag //.
    }
    iSplitR "Hback_cache Hconsumer_ctl₁ Hdata_front HΦ".
    { iExists front, back2, (v :: vs2), hist2. iSteps. }
    iModIntro. clear- Hbranch. iModIntro.

    wp_load.
    wp_smart_apply (array_cget_spec with "Hdata_front") as "Hdata_front"; first done.
    wp_smart_apply (array_cset_spec with "Hdata_front") as "Hdata_front"; first done.
    wp_pures.

    wp_bind (_ <- _)%E.
    iInv "Hinv" as "(%_front & %back3 & %vs3 & %hist3 & >(%Hback3 & %Hback3_le) & >(%Hhist3_len & %Hvs3) & Hfront & Hconsumer_ctl₂ & Hback & Hproducer_ctl₂ & Hmodel₂ & Hhistory_auth & Hconsumer_region & Hdata_vs & Hdata_back & Hdata_extra)".
    wp_store.
    iDestruct (spsc_bqueue_consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
    iDestruct (spsc_bqueue_back_lb_valid with "Hproducer_ctl₂ Hback_lb") as %Hback2.
    destruct vs3 as [| _v vs3]; first naive_solver lia.
    iDestruct (spsc_bqueue_history_agree with "Hhistory_auth Hhistory_elem") as %Hhist3_lookup.
    assert (_v = v) as ->.
    { move: Hhist3_lookup.
      rewrite -(take_drop front hist3) -Hvs3 lookup_app_r take_length; first lia.
      rewrite Nat.min_l; first lia.
      rewrite Nat.sub_diag. naive_solver.
    }
    rewrite /= drop_0.
    iDestruct "Hconsumer_region" as "[Hdata_front' | Hconsumer_region]".
    { iDestruct (array_cslice_exclusive with "Hdata_front Hdata_front'") as %[]; [simpl; lia | done]. }
    iMod (spsc_bqueue_consumer_ctl_update (S front) with "Hconsumer_ctl₁ Hconsumer_ctl₂") as "(Hconsumer_ctl₁ & Hconsumer_ctl₂)"; first lia.
    iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (spsc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (spsc_bqueue_model_update vs3 with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "Hback_cache Hconsumer_ctl₁ Hconsumer_region HΦ".
    { do 2 iModIntro. iExists (S front), back3, vs3, hist3. iFrame. simpl in *.
      iSplit; first iSteps.
      iSplit. { erewrite drop_S in Hvs3; last done. naive_solver. }
      iSplitL "Hfront"; first iSteps.
      rewrite assoc. iSplitL "Hdata_vs".
      - rewrite -{1}(take_drop 1 vs3) fmap_app -array_cslice_app fmap_length take_length.
        destruct vs3; last rewrite Nat.add_1_r; iSteps.
      - iDestruct (array_cslice_shift with "Hdata_front") as "Hdata_front".
        case_decide as Hcase.
        + rewrite -Hcase decide_False; first lia.
          assert (cap - (back3 - S front) - 1 = 0) as -> by lia.
          iSteps.
        + rewrite decide_False; first lia.
          iFrame.
          iDestruct (array_cslice_app_1 with "Hdata_extra Hdata_front") as "Hdata_extra".
          { rewrite replicate_length. lia. }
          rewrite -replicate_S_end.
          assert (S (cap - (back3 - front) - 1) = cap - (back3 - S front) - 1) as -> by lia.
          iSteps.
    }
    iSteps.
  Qed.
End spsc_bqueue_G.

#[global] Opaque spsc_bqueue_create.
#[global] Opaque spsc_bqueue_push.
#[global] Opaque spsc_bqueue_pop.

#[global] Opaque spsc_bqueue_inv.
#[global] Opaque spsc_bqueue_model.
#[global] Opaque spsc_bqueue_producer.
#[global] Opaque spsc_bqueue_consumer.
