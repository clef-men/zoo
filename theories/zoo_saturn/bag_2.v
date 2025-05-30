From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  fin_map_dom
  fin_maps.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.mono_map
  lib.twins.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  xtchain.
From zoo_saturn Require Export
  base
  bag_2__code.
From zoo_saturn Require Import
  bag_2__types
  spmc_queue.
From zoo Require Import
  options.

Implicit Types l node 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 : location.
Implicit Types nodes : list location.
Implicit Types v t producer consumer : val.
Implicit Types o : option val.
Implicit Types vs ws : list val.
Implicit Types vss wss : gmap val (list val).

Class Bag2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] bag_2_G_spmc_queue_G :: SpmcQueueG Σ ;
  #[local] bag_2_G_queues_G :: MonoMapG Σ location val ;
  #[local] bag_2_G_model_G :: TwinsG Σ (leibnizO (gmap val (list val))) ;
}.

Definition bag_2_Σ := #[
  spmc_queue_Σ ;
  mono_map_Σ location val ;
  twins_Σ (leibnizO (gmap val (list val)))
].
#[global] Instance subG_bag_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG bag_2_Σ Σ →
  Bag2G Σ.
Proof.
  solve_inG.
Qed.

Record producer := {
  producer_queue : val ;
  producer_node : location ;
}.
Implicit Types 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : producer.

#[local] Coercion producer_to_val 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val :=
  ( 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_queue),
    #𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_node)
  ).

#[local] Lemma producer_eq_alt 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2 :
  𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1.(producer_queue) = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2.(producer_queue) →
  𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1.(producer_node) = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2.(producer_node) →
  𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1 = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2.
Proof.
  destruct 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1, 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2; naive_solver.
Qed.
#[local] Instance producer_to_val_inj :
  Inj (=) (=) producer_to_val.
Proof.
  intros [] []; naive_solver.
Qed.

Record descriptor := {
  descriptor_queue : val ;
  descriptor_vals : list val ;
}.
Implicit Types descr : descriptor.
Implicit Types descrs : gmap location descriptor.

#[local] Definition descriptor_update_vals descr f :=
  {|descriptor_queue := descr.(descriptor_queue) ;
    descriptor_vals := f descr.(descriptor_vals) ;
  |}.

#[local] Definition descriptor_to_producer descr node :=
  {|producer_queue := descr.(descriptor_queue) ;
    producer_node := node ;
  |}.

#[local] Lemma descriptor_to_producer_inj descr1 node1 descr2 node2 :
  descriptor_to_producer descr1 node1 = descriptor_to_producer descr2 node2 →
  node1 = node2.
Proof.
  naive_solver.
Qed.

Section bag_2_G.
  Context `{bag_2_G : Bag2G Σ}.

  Record metadata := {
    metadata_inv : namespace ;
    metadata_model : gname ;
    metadata_queues : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition queues_auth' γ_queues nodes descrs wss : iProp Σ :=
    mono_map_auth γ_queues (DfracOwn 1) (descriptor_queue <$> descrs) ∗
    ⌜dom descrs = list_to_set nodes⌝ ∗
    ⌜ map_Forall (λ node descr,
        wss !! (descriptor_to_producer descr node : val) = Some descr.(descriptor_vals)
      ) descrs
    ⌝.
  #[local] Instance : CustomIpatFormat "queues_auth" :=
    "(
      Hauth &
      %Hnodes &
      %Hdescrs
    )".
  #[local] Definition queues_auth γ :=
    queues_auth' γ.(metadata_queues).
  #[local] Definition queues_at' :=
    mono_map_at.
  #[local] Definition queues_at γ :=
    queues_at' γ.(metadata_queues).
  #[local] Definition queues_elem γ queue : iProp Σ :=
    match queue with
    | None =>
        True
    | Some queue =>
        ∃ node,
        queues_at γ node queue ∗
        spmc_queue_inv queue (γ.(metadata_inv).@"producer")
    end.
  #[local] Instance : CustomIpatFormat "queues_elem" :=
    "(
      %node &
      #Hqueues_at &
      #Hqueue_inv
    )".

  #[local] Definition model₁' γ_model vss :=
    twins_twin1 γ_model (DfracOwn 1) vss.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata_model).
  #[local] Definition model₂' γ_model vss :=
    twins_twin2 γ_model vss.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata_model).

  #[local] Definition descriptor_model γ node descr : iProp Σ :=
    ∃ o,
    node.[queue] ↦ o ∗
    ⌜from_option (.= descr.(descriptor_queue)) True o⌝ ∗
    spmc_queue_inv descr.(descriptor_queue) (γ.(metadata_inv).@"producer") ∗
    spmc_queue_model descr.(descriptor_queue) descr.(descriptor_vals).
  #[local] Instance : CustomIpatFormat "descriptor_model" :=
    "(
      %o{} &
      Hnode{}_queue &
      {>;}%Ho{} &
      {{inv}#Hqueue{}_inv;{inv}#Hqueue_inv;_} &
      {>;}Hqueue{}_model
    )".

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ nodes descrs wss,
    l.[producers] ↦ from_option #@{location} §Null (head nodes) ∗
    xtchain (Header §Node 2) DfracDiscarded nodes §Null ∗
    queues_auth γ nodes descrs wss ∗
    model₂ γ wss ∗
    [∗ map] node ↦ descr ∈ descrs,
      descriptor_model γ node descr.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %nodes{} &
      %descrs{} &
      %wss &
      Hl_producers &
      Hnodes{} &
      >Hqueues_auth &
      >Hmodel₂ &
      Hdescrs
    )".
  #[local] Definition inv' l γ :=
    inv (γ.(metadata_inv).@"inv") (inv_inner l γ).
  Definition bag_2_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata_inv)⌝ ∗
    meta l nroot γ ∗
    inv' l γ.
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      -> &
      #Hmeta &
      #Hinv
    )".

  Definition bag_2_model t vss : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vss.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l{;_} &
      %γ{;_} &
      %Heq{} &
      #Hmeta_{} &
      Hmodel₁
    )".

  Definition bag_2_producer t producer ws : iProp Σ :=
    ∃ l γ 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟,
    ⌜t = #l⌝ ∗
    ⌜producer = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟⌝ ∗
    meta l nroot γ ∗
    𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_node) ↦ₕ Header §Node 2 ∗
    queues_at γ 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_node) 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_queue) ∗
    spmc_queue_inv 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_queue) (γ.(metadata_inv).@"producer") ∗
    spmc_queue_producer 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_queue) ws.
  #[local] Instance : CustomIpatFormat "producer" :=
    "(
      %l{;_} &
      %γ{;_} &
      %𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟{} &
      %Ht_eq{} &
      {%Hproducer_eq{};->} &
      #Hmeta{_{};_} &
      #Hnode_header{_{}} &
      #Hqueues_at{_{}} &
      #Hqueue_inv{_{}} &
      Hqueue_producer{_{}}
    )".

  Definition bag_2_consumer t consumer : iProp Σ :=
    ∃ l γ 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 (queue : option val),
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜consumer = #𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟⌝ ∗
    𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟.[consumer_queue] ↦ queue ∗
    queues_elem γ queue.
  #[local] Instance : CustomIpatFormat "consumer" :=
    "(
      %l_ &
      %γ_ &
      %𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 &
      %queue &
      %Heq &
      Hmeta_ &
      -> &
      Hconsumer_queue &
      #Hqueues_elem
    )".

  #[local] Instance queues_auth_timeless γ nodes descrs wss :
    Timeless (queues_auth γ nodes descrs wss).
  Proof.
    apply _.
  Qed.
  #[global] Instance bag_2_model_timeless t vss :
    Timeless (bag_2_model t vss).
  Proof.
    apply _.
  Qed.
  #[global] Instance bag_2_inv_persistent t ι :
    Persistent (bag_2_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma queues_alloc :
    ⊢ |==>
      ∃ γ_queues,
      queues_auth' γ_queues [] ∅ ∅.
  Proof.
    iMod mono_map_alloc as "(%γ_queues & Hauth)".
    iSteps.
  Qed.
  #[local] Lemma queues_at_get {γ nodes descrs wss} i node :
    nodes !! i = Some node →
    queues_auth γ nodes descrs wss ⊢
      ∃ descr,
      ⌜descrs !! node = Some descr⌝ ∗
      queues_at γ node descr.(descriptor_queue).
  Proof.
    iIntros "%Hnodes_lookup (:queues_auth)".
    destruct (elem_of_dom_1 descrs node) as (descr & Hdescrs_lookup).
    { rewrite Hnodes elem_of_list_to_set elem_of_list_lookup. eauto. }
    iDestruct (mono_map_at_get with "Hauth") as "#Hat".
    { rewrite lookup_fmap_Some. eauto. }
    iSteps.
  Qed.
  #[local] Lemma queues_at_valid γ nodes descrs wss node queue :
    queues_auth γ nodes descrs wss -∗
    queues_at γ node queue -∗
      ∃ descr,
      ⌜descrs !! node = Some descr⌝ ∗
      ⌜descr.(descriptor_queue) = queue⌝ ∗
      ⌜wss !! (descriptor_to_producer descr node : val) = Some descr.(descriptor_vals)⌝.
  Proof.
    iIntros "(:queues_auth) Hat".
    iDestruct (mono_map_at_valid with "Hauth Hat") as %(descr & ? & Hdescrs_lookup)%lookup_fmap_Some.
    iSteps.
  Qed.
  #[local] Lemma queues_at_valid_producer γ nodes descrs wss 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 :
    queues_auth γ nodes descrs wss -∗
    queues_at γ 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_node) 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_queue) -∗
      ∃ descr,
      ⌜descrs !! 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_node) = Some descr⌝ ∗
      ⌜descr.(descriptor_queue) = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_queue)⌝ ∗
      ⌜wss !! (𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val) = Some descr.(descriptor_vals)⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (queues_at_valid with "Hauth Hat") as "(%descr & %Hdescrs_lookup & %Hdescr_queue & %Hwss_lookup)".
    rewrite (producer_eq_alt 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 (descriptor_to_producer descr 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_node))) //.
    iSteps.
  Qed.
  #[local] Lemma queues_insert {γ nodes descrs wss} node descr :
    descrs !! node = None →
    queues_auth γ nodes descrs wss ⊢ |==>
      queues_auth γ
        (node :: nodes)
        (<[node := descr]> descrs)
        (<[descriptor_to_producer descr node : val := descr.(descriptor_vals)]> wss) ∗
      queues_at γ node descr.(descriptor_queue).
  Proof.
    iIntros "%Hdescrs_lookup (:queues_auth)".
    iMod (mono_map_insert' node descr.(descriptor_queue) with "Hauth") as "(Hauth & Hat)".
    { rewrite lookup_fmap Hdescrs_lookup //. }
    rewrite -fmap_insert. iSteps; iPureIntro.
    - set_solver.
    - apply map_Forall_insert_2.
      + rewrite lookup_insert //.
      + eapply map_Forall_impl'; first done. move=> /= node' descr' Hdescrs_lookup' Hwss_lookup.
        destruct (decide (node' = node)) as [-> |].
        * simplify.
        * rewrite lookup_insert_ne //.
          intros ?%(inj _)%descriptor_to_producer_inj. done.
  Qed.
  #[local] Lemma queues_update {γ nodes descrs wss} node descr f :
    descrs !! node = Some descr →
    queues_auth γ nodes descrs wss ⊢
    queues_auth γ
      nodes
      (<[node := descriptor_update_vals descr f]> descrs)
      (<[descriptor_to_producer descr node : val := f descr.(descriptor_vals)]> wss).
  Proof.
    iIntros "%Hdescrs_lookup (:queues_auth)".
    rewrite /queues_auth /queues_auth'.
    rewrite fmap_insert /= -fmap_insert insert_id //.
    iFrame. iSplit; iPureIntro.
    - rewrite dom_insert_lookup_L //.
    - apply map_Forall_insert_2'.
      + rewrite lookup_insert //.
      + apply map_Forall_delete_lookup => node' descr' Hnode' Hdescrs_lookup'.
        rewrite lookup_insert_ne; first naive_solver.
        rewrite map_Forall_lookup in Hdescrs. auto.
  Qed.
  #[local] Lemma queues_update_producer {γ nodes descrs wss} 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 descr f :
    descrs !! 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_node) = Some descr →
    descr.(descriptor_queue) = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_queue) →
    queues_auth γ nodes descrs wss ⊢
    queues_auth γ
      nodes
      (<[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_node) := descriptor_update_vals descr f]> descrs)
      (<[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val := f descr.(descriptor_vals)]> wss).
  Proof.
    intros Hdescrs_lookup Hdescr_queue.
    rewrite (queues_update 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer_node) descr f) //.
    rewrite /descriptor_to_producer Hdescr_queue //.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model ∅ ∗
      model₂' γ_model ∅.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma model_agree γ vss1 vss2 :
    model₁ γ vss1 -∗
    model₂ γ vss2 -∗
    ⌜vss1 = vss2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma model_update {γ vss1 vss2} vss :
    model₁ γ vss1 -∗
    model₂ γ vss2 ==∗
      model₁ γ vss ∗
      model₂ γ vss.
  Proof.
    apply twins_update'.
  Qed.

  Opaque queues_auth'.

  Lemma bag_2_producer_valid t ι vss producer ws E :
    ↑ι ⊆ E →
    bag_2_inv t ι -∗
    bag_2_model t vss -∗
    bag_2_producer t producer ws ={E}=∗
      ∃ vs,
      ⌜vss !! producer = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "% (:inv) (:model =1) (:producer =2)". simplify.
    iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
    iDestruct (meta_agree with "Hmeta Hmeta_2") as %<-. iClear "Hmeta_2".

    iInv "Hinv" as "(:inv_inner)".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
    iDestruct (queues_at_valid_producer with "Hqueues_auth Hqueues_at_2") as %(descr & Hdescrs_lookup & Hdescr_queue & Hvss_lookup).
    iAssert (◇ ⌜descr.(descriptor_vals) `suffix_of` ws⌝)%I as "#>%".
    { iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor_model >)"; first done.
      rewrite Hdescr_queue.
      iApply (spmc_queue_producer_valid with "Hqueue_producer_2 Hqueue_model").
    }
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.
  Lemma bag_2_producer_exclusive t producer ws1 ws2 :
    bag_2_producer t producer ws1 -∗
    bag_2_producer t producer ws2 -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iApply (spmc_queue_producer_exclusive with "Hqueue_producer_1 Hqueue_producer_2").
  Qed.

  Lemma bag_2_create_spec ι :
    {{{
      True
    }}}
      bag_2_create ()
    {{{ t,
      RET t;
      bag_2_inv t ι ∗
      bag_2_model t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_block l as "Hmeta" "(Hl_producers & _)".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod queues_alloc as "(%γ_queues & Hqueues_auth)".

    pose γ := {|
      metadata_inv := ι ;
      metadata_model := γ_model ;
      metadata_queues := γ_queues ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. iStep 3. iApply inv_alloc. iFrame.
    iDestruct xtchain_nil as "$".
    rewrite big_sepM_empty. iSteps.
  Qed.

  #[local] Lemma bag_2_add_producer_0_spec l γ (queue : val) :
    <<<
      meta l nroot γ ∗
      inv' l γ ∗
      spmc_queue_inv queue (γ.(metadata_inv).@"producer") ∗
      spmc_queue_model queue []
    | ∀∀ vss,
      model₁ γ vss
    >>>
      bag_2_add_producer_0 #l (Some queue) @ ↑γ.(metadata_inv)
    <<<
      ∃∃ node,
      let 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 := {|
        producer_queue := queue ;
        producer_node := node ;
      |} in
      model₁ γ (<[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val := []]> vss)
    | RET #node;
      node ↦ₕ Header §Node 2 ∗
      queues_at γ node queue
    >>>.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hqueue_inv & Hqueue_model) HΦ".
    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (_.{producers})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iSplitR "Hqueue_model HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    wp_block node as "#Hnode_header" "_" "(Hnode_next & Hnode_queue & _)".
    iMod (pointsto_persist with "Hnode_next") as "#Hnode_next".
    wp_match. wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(:inv_inner =2)".
    wp_cas as Hcas; first iSteps.
    assert (head nodes1 = head nodes2) as ->.
    { destruct nodes1, nodes2; zoo_simpl; done. }
    iDestruct (xtchain_cons_2 with "Hnode_header [] Hnodes2") as "Hnodes"; first iSteps.

    iAssert ⌜descrs2 !! node = None⌝%I as %Hdescr2_lookup.
    { rewrite eq_None_not_Some. iIntros "(%descr' & %)".
      iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor_model =')"; first done.
      iApply (pointsto_exclusive with "Hnode_queue Hnode'_queue").
    }

    pose descr := {|
      descriptor_queue := queue ;
      descriptor_vals := [] ;
    |}.
    iMod (queues_insert node descr with "Hqueues_auth") as "(Hqueues_auth & #Hqueues_at)"; first done.
    iDestruct (big_sepM_insert_2 _ _ node descr with "[Hnode_queue Hqueue_model] Hdescrs") as "Hdescrs".
    { iExists (Some queue). iSteps. }

    iMod "HΦ" as "(%vss & Hmodel₁ & _ & HΦ)".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
    set vss' :=
      <[descriptor_to_producer descr node : val := []]> vss.
    iMod (model_update vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "Hmodel₁ [$Hnode_header $Hqueues_at]") as "HΦ".

    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma bag_2_add_producer_spec l γ (queue : val) :
    <<<
      meta l nroot γ ∗
      inv' l γ ∗
      spmc_queue_inv queue (γ.(metadata_inv).@"producer") ∗
      spmc_queue_model queue []
    | ∀∀ vss,
      model₁ γ vss
    >>>
      bag_2_add_producer #l queue @ ↑γ.(metadata_inv)
    <<<
      ∃∃ node,
      let 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 := {|
        producer_queue := queue ;
        producer_node := node ;
      |} in
      model₁ γ (<[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val := []]> vss)
    | RET #node;
      node ↦ₕ Header §Node 2 ∗
      queues_at γ node queue
    >>>.
  Proof.
    iIntros "%Φ H HΦ".

    wp_rec.
    wp_smart_apply (bag_2_add_producer_0_spec with "H HΦ").
  Qed.
  Lemma bag_2_create_producer_spec t ι :
    <<<
      bag_2_inv t ι
    | ∀∀ vss,
      bag_2_model t vss
    >>>
      bag_2_create_producer t @ ↑ι
    <<<
      ∃∃ producer,
      bag_2_model t (<[producer := []]> vss)
    | RET producer;
      bag_2_producer t producer []
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.
    wp_apply (spmc_queue_create_spec with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model & Hqueue_producer)".

    awp_smart_apply (bag_2_add_producer_spec with "[$Hmeta $Hinv $Hqueue_inv $Hqueue_model]") without "Hqueue_producer".
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vss (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hmodel₁"; iSteps.
  Qed.

  Lemma bag_2_close_producer_spec t ι producer ws :
    {{{
      bag_2_inv t ι ∗
      bag_2_producer t producer ws
    }}}
      bag_2_close_producer producer
    {{{
      RET ();
      bag_2_producer t producer ws
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ". injection Ht_eq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_match.

    iInv "Hinv" as "(:inv_inner)".
    iDestruct (queues_at_valid_producer with "Hqueues_auth Hqueues_at") as %(descr & Hdescrs_lookup & Hdescr_queue & Hwss_lookup).
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor_model >) & Hdescrs)"; first done.
    wp_store.
    iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs".
    { iExists None. rewrite Hdescr_queue. iSteps. }
    iSplitR "Hqueue_producer HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma bag_2_create_consumer_spec t ι :
    {{{
      bag_2_inv t ι
    }}}
      bag_2_create_consumer t
    {{{ consumer,
      RET consumer;
      bag_2_consumer t consumer
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.
    wp_block 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 as "(Hconsumer_queue & _)".
    iSteps. iExists None. iSteps.
  Qed.

  Lemma bag_2_push_spec t ι producer ws v :
    <<<
      bag_2_inv t ι ∗
      bag_2_producer t producer ws
    | ∀∀ vss,
      bag_2_model t vss
    >>>
      bag_2_push producer v @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! producer = Some vs⌝ ∗
      bag_2_model t (<[producer := vs ++ [v]]> vss)
    | RET ();
      bag_2_producer t producer (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ". injection Ht_eq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec.

    awp_smart_apply (spmc_queue_push_spec with "[$Hqueue_inv $Hqueue_producer]").
    iInv "Hinv" as "(:inv_inner)".
    iDestruct (queues_at_valid_producer with "Hqueues_auth Hqueues_at") as %(descr & Hdescrs_lookup & Hdescr_queue & Hwss_lookup). rewrite -Hdescr_queue.
    iDestruct (big_sepM_insert_acc with "Hdescrs") as "((:descriptor_model >) & Hdescrs)"; first done.
    iAaccIntro with "Hqueue_model"; iIntros "Hqueue_model".
    { iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.
      rewrite insert_id //. iFrameSteps.
    }
    iDestruct (queues_update_producer 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 descr (.++ [v]) with "Hqueues_auth") as "Hqueues_auth"; [done.. |].
    set descr' :=
      descriptor_update_vals descr (.++ [v]).
    iDestruct ("Hdescrs" $! descr' with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.

    iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
    set vss' :=
      <[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val := descr.(descriptor_vals) ++ [v]]> vss.
    iMod (model_update vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "HΦ". { iFrameSteps. }
    rewrite Hdescr_queue. iSteps.
  Qed.

  #[local] Lemma bag_2_pop_0_spec l γ 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 (queue : option val) nodes :
    <<<
      meta l nroot γ ∗
      inv' l γ ∗
      𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟.[consumer_queue] ↦ queue ∗
      queues_elem γ queue ∗
      xtchain (Header §Node 2) DfracDiscarded nodes §Null ∗
      [∗ list] node ∈ nodes,
        ∃ queue,
        queues_at γ node queue
    | ∀∀ vss,
      model₁ γ vss
    >>>
      bag_2_pop_0 #𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 (from_option #@{location} §Null%V $ head nodes) @ ↑γ.(metadata_inv)
    <<<
      ∃∃ o,
      match o with
      | None =>
          model₁ γ vss
      | Some v =>
          ∃ producer vs,
          ⌜vss !! producer = Some (v :: vs)⌝ ∗
          model₁ γ (<[producer := vs]> vss)
      end
    | queue : option val,
      RET o;
      𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟.[consumer_queue] ↦ queue ∗
      queues_elem γ queue
    >>>.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & Hconsumer_queue & #Hqueues_elem & Hnodes & Hqueues_ats) HΦ".

    iLöb as "HLöb" forall (nodes).

    wp_rec.
    destruct nodes as [| node nodes].

    - wp_pures.

      iMod "HΦ" as "(%vss & Hmodel₁ & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel₁") as "HΦ".

      iSteps.

    - iDestruct (xtchain_cons' with "Hnodes") as "-#(#Hnode_header & #Hnode_next & #Hnodes)".
      iDestruct (big_sepL_cons_1 with "Hqueues_ats") as "-#((%queue0 & #Hqueues_at) & #Hqueues_ats)".
      wp_match.

      wp_bind (_.{queue})%E.
      iInv "Hinv" as "(:inv_inner =1)".
      iDestruct (queues_at_valid with "Hqueues_auth Hqueues_at") as "#(%descr & %Hdescrs1_lookup & %Hdescr_queue & _)".
      iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor_model =0 > inv=) & Hdescrs)"; first done.
      wp_load.
      iSplitR "Hconsumer_queue HΦ". { iFrameSteps. }
      rewrite Hdescr_queue. iIntros "!>".

      destruct o0 as [queue0_ |]; wp_pures.

      + rewrite Ho0 Hdescr_queue. clear.

        awp_smart_apply (spmc_queue_pop_spec with "Hqueue0_inv") without "Hconsumer_queue".
        iInv "Hinv" as "(:inv_inner =2)".
        iDestruct (queues_at_valid with "Hqueues_auth Hqueues_at") as "(%descr & %Hdescrs_lookup & %Hdescr_queue & %Hwss_lookup)".
        iDestruct (big_sepM_insert_acc with "Hdescrs") as "((:descriptor_model >) & Hdescrs)"; first done.
        rewrite -Hdescr_queue.
        iAaccIntro with "Hqueue_model"; iIntros "Hqueue_model".
        { iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.
          rewrite insert_id //. iFrameSteps.
        }
        destruct descr.(descriptor_vals) as [| v vs] eqn:Hdescr_vals => /=.

        * iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs".
          { rewrite -Hdescr_vals. iFrameSteps. }
          rewrite insert_id //.
          iSplitR "HΦ". { iFrameSteps. }
          iIntros "{%} !> _ Hconsumer_queue".

          wp_load.
          wp_apply ("HLöb" $! nodes with "Hconsumer_queue Hnodes [$] HΦ").

        * iMod "HΦ" as "(%vss & Hmodel₁ & _ & HΦ)".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
          set vss' :=
            <[descriptor_to_producer descr node : val := vs]> vss.
          iMod (model_update vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ"; first iSteps.

          iDestruct (queues_update node descr (const vs) with "Hqueues_auth") as "Hqueues_auth"; first done.
          set descr' :=
            descriptor_update_vals descr (const vs).
          iDestruct ("Hdescrs" $! descr' with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iFrameSteps.

          iSplitR "HΦ". { iFrameSteps. }
          iSteps. iExists (Some _). iSteps.

      + wp_load.
        wp_apply ("HLöb" $! nodes with "Hconsumer_queue Hnodes [$] HΦ").
  Qed.
  #[local] Lemma bag_2_pop_1_spec t ι consumer :
    <<<
      bag_2_inv t ι ∗
      bag_2_consumer t consumer
    | ∀∀ vss,
      bag_2_model t vss
    >>>
      bag_2_pop_1 t consumer @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          bag_2_model t vss
      | Some v =>
          ∃ producer vs,
          ⌜vss !! producer = Some (v :: vs)⌝ ∗
          bag_2_model t (<[producer := vs]> vss)
      end
    | RET o;
      bag_2_consumer t consumer
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_pures.

    wp_bind (_.{producers})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iDestruct "Hnodes" as "#Hnodes".

    iAssert (
      [∗ list] node ∈ nodes,
        ∃ queue,
        queues_at γ node queue
    )%I as "#queues_ats".
    { iApply big_sepL_forall. iIntros "%i %node %Hnodes_lookup".
      iDestruct (queues_at_get with "Hqueues_auth") as "(%descr & %Hdescrs_lookup & #Hqueues_at)"; first done.
      iSteps.
    }

    iSplitR "Hconsumer_queue HΦ". { iFrameSteps. }
    iIntros "{%} !>".

    awp_smart_apply (bag_2_pop_0_spec with "[- HΦ]"); first iFrameSteps.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vss (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%o Hmodel₁ !>".
    iExists o. destruct o as [v |]; last iSteps.
    iDestruct "Hmodel₁" as "(%producer & %vs & %Hvss_lookup & Hmodel₁)".
    iSteps.
  Qed.
  Lemma bag_2_pop_spec t ι consumer :
    <<<
      bag_2_inv t ι ∗
      bag_2_consumer t consumer
    | ∀∀ vss,
      bag_2_model t vss
    >>>
      bag_2_pop t consumer @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          bag_2_model t vss
      | Some v =>
          ∃ producer vs,
          ⌜vss !! producer = Some (v :: vs)⌝ ∗
          bag_2_model t (<[producer := vs]> vss)
      end
    | RET o;
      bag_2_consumer t consumer
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    destruct queue as [queue |].

    - iDestruct "Hqueues_elem" as "(:queues_elem)".
      awp_smart_apply (spmc_queue_pop_spec with "Hqueue_inv") without "Hconsumer_queue".
      iInv "Hinv" as "(:inv_inner)".
      iDestruct (queues_at_valid with "Hqueues_auth Hqueues_at") as "(%descr & %Hdescrs_lookup & %Hdescr_queue & %Hwss_lookup)".
      iDestruct (big_sepM_insert_acc with "Hdescrs") as "((:descriptor_model >) & Hdescrs)"; first done.
      rewrite -Hdescr_queue.
      iAaccIntro with "Hqueue_model"; iIntros "Hqueue_model".
      { iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.
        rewrite insert_id //. iFrameSteps.
      }
      destruct descr.(descriptor_vals) as [| v vs] eqn:Hdescr_vals => /=.

      + iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs".
        { rewrite -Hdescr_vals. iFrameSteps. }
        rewrite insert_id //.
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "{%} !> _ Hconsumer_queue".

        wp_smart_apply (bag_2_pop_1_spec with "[- HΦ] HΦ").
        { iSplitR; iSteps. iExists (Some _). iSteps. }

      + iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
        set vss' :=
          <[descriptor_to_producer descr node : val := vs]> vss.
        iMod (model_update vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ"; first iSteps.

        iDestruct (queues_update node descr (const vs) with "Hqueues_auth") as "Hqueues_auth"; first done.
        set descr' :=
          descriptor_update_vals descr (const vs).
        iDestruct ("Hdescrs" $! descr' with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iFrameSteps.

        iSplitR "HΦ". { iFrameSteps. }
        iSteps. iExists (Some _). iSteps.

    - wp_smart_apply (bag_2_pop_1_spec with "[- HΦ] HΦ").
      { iSplitR; iSteps. iExists None. iSteps. }
  Qed.
End bag_2_G.

#[global] Opaque bag_2_create.
#[global] Opaque bag_2_create_producer.
#[global] Opaque bag_2_close_producer.
#[global] Opaque bag_2_create_consumer.
#[global] Opaque bag_2_push.
#[global] Opaque bag_2_pop.

#[global] Opaque bag_2_inv.
#[global] Opaque bag_2_model.
#[global] Opaque bag_2_producer.
#[global] Opaque bag_2_consumer.
