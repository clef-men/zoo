Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.fin_maps.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.mono_gmap.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.xtchain.
Require Export zoo_saturn.bag_2__code.
Require Import zoo_saturn.bag_2__types.
Require Import zoo_saturn.spmc_queue.
Require Import zoo.options.

Implicit Type l node 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 : location.
Implicit Type nodes : list location.
Implicit Type v t producer consumer : val.
Implicit Type o : option val.
Implicit Type vs ws : list val.
Implicit Type vss wss : gmap val (list val).

Class Bag2G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] bag_2۰G۰spmc_queue۰G :: SpmcQueueG Σ
  ; #[local] bag_2۰G۰queues۰G :: MonoGmapG Σ location val
  ; #[local] bag_2۰G۰model۰G :: TwinsG Σ (leibnizO (gmap val (list val)))
  }.

Definition bag_2۰Σ :=
  #[spmc_queue۰Σ
  ; mono_gmap۰Σ location val
  ; twins۰Σ (leibnizO (gmap val (list val)))
  ].
#[global] Instance subG𑁒bag_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG bag_2۰Σ Σ →
  Bag2G Σ.
Proof.
  solve_inG.
Qed.

Record producer :=
  { producer۰queue : val
  ; producer۰node : location
  }.
Implicit Type 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : producer.

#[local] Coercion producer۰to_val 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val :=
  ( 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰queue),
    #𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰node)
  ).

#[local] Lemma producer𑁒eq𑁒alt 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2 :
  𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1.(producer۰queue) = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2.(producer۰queue) →
  𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1.(producer۰node) = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2.(producer۰node) →
  𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1 = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2.
Proof.
  destruct 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟1, 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟2; naive_solver.
Qed.
#[local] Instance producer۰to_val𑁒inj :
  Inj (=) (=) producer۰to_val.
Proof.
  intros [] []; naive_solver.
Qed.

Record descriptor :=
  { descriptor۰queue : val
  ; descriptor۰vals : list val
  }.
Implicit Type descr : descriptor.
Implicit Type descrs : gmap location descriptor.

#[local] Definition descriptor۰update_vals descr f :=
  {|descriptor۰queue := descr.(descriptor۰queue)
  ; descriptor۰vals := f descr.(descriptor۰vals)
  |}.

#[local] Definition descriptor۰to_producer descr node :=
  {|producer۰queue := descr.(descriptor۰queue)
  ; producer۰node := node
  |}.

#[local] Lemma descriptor۰to_producer𑁒inj descr1 node1 descr2 node2 :
  descriptor۰to_producer descr1 node1 = descriptor۰to_producer descr2 node2 →
  node1 = node2.
Proof.
  naive_solver.
Qed.

Section bag_2۰G.
  Context `{bag_2۰G : Bag2G Σ}.

  Record metadata :=
    { metadata۰inv : namespace
    ; metadata۰model : gname
    ; metadata۰queues : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadata𑁒eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata𑁒countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition queues۰auth' γ_queues nodes descrs wss : iProp Σ :=
    mono_gmap۰auth γ_queues (DfracOwn 1) (descriptor۰queue <$> descrs) ∗
    ⌜dom descrs = list_to_set nodes⌝ ∗
    ⌜ map_Forall (λ node descr,
        wss !! (descriptor۰to_producer descr node : val) = Some descr.(descriptor۰vals)
      ) descrs
    ⌝.
  #[local] Instance : CustomIpat "queues۰auth" :=
    " ( Hauth
      & %Hnodes
      & %Hdescrs
      )
    ".
  #[local] Definition queues۰auth γ :=
    queues۰auth' γ.(metadata۰queues).
  #[local] Definition queues۰at' :=
    mono_gmap۰at.
  #[local] Definition queues۰at γ :=
    queues۰at' γ.(metadata۰queues).
  #[local] Definition queues۰elem γ queue : iProp Σ :=
    match queue with
    | None =>
        True
    | Some queue =>
        ∃ node,
        queues۰at γ node queue ∗
        spmc_queue۰inv queue (γ.(metadata۰inv).@"producer")
    end.
  #[local] Instance : CustomIpat "queues۰elem" :=
    " ( %node
      & #Hqueues_at
      & #Hqueue_inv
      )
    ".

  #[local] Definition model₁' γ_model vss :=
    twins۰twin₁ γ_model (DfracOwn 1) vss.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata۰model).
  #[local] Definition model₂' γ_model vss :=
    twins۰twin₂ γ_model vss.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata۰model).

  #[local] Definition descriptor۰model γ node descr : iProp Σ :=
    ∃ o,
    node.[queue] ↦ o ∗
    ⌜from_option (.= descr.(descriptor۰queue)) True o⌝ ∗
    spmc_queue۰inv descr.(descriptor۰queue) (γ.(metadata۰inv).@"producer") ∗
    spmc_queue۰model descr.(descriptor۰queue) descr.(descriptor۰vals).
  #[local] Instance : CustomIpat "descriptor۰model" :=
    " ( %o{}
      & Hnode{}_queue
      & {>;}%Ho{}
      & {{inv}#Hqueue{}_inv;{inv}#Hqueue_inv;_}
      & {>;}Hqueue{}_model
      )
    ".

  #[local] Definition inv۰inner l γ : iProp Σ :=
    ∃ nodes descrs wss,
    l.[producers] ↦ from_option #@{location} §Null (head nodes) ∗
    xtchain (Header §Node 2) DfracDiscarded nodes §Null ∗
    queues۰auth γ nodes descrs wss ∗
    model₂ γ wss ∗
    [∗ map] node ↦ descr ∈ descrs,
      descriptor۰model γ node descr.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %nodes{}
      & %descrs{}
      & %wss
      & Hl_producers
      & Hnodes{}
      & >Hqueues_auth
      & >Hmodel₂
      & Hdescrs
      )
    ".
  #[local] Definition inv' l γ :=
    inv (γ.(metadata۰inv).@"inv") (inv۰inner l γ).
  Definition bag_2۰inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata۰inv)⌝ ∗
    l ↪ γ ∗
    inv' l γ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l
      & %γ
      & ->
      & ->
      & #Hmeta
      & #Hinv
      )
    ".

  Definition bag_2۰model t vss : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    model₁ γ vss.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & Hmodel₁{_{}}
      )
    ".

  Definition bag_2۰producer t producer ws : iProp Σ :=
    ∃ l γ 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟,
    ⌜t = #l⌝ ∗
    ⌜producer = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟⌝ ∗
    l ↪ γ ∗
    𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰node) ↦ₕ Header §Node 2 ∗
    queues۰at γ 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰node) 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰queue) ∗
    spmc_queue۰inv 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰queue) (γ.(metadata۰inv).@"producer") ∗
    spmc_queue۰producer 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰queue) ws.
  #[local] Instance : CustomIpat "producer" :=
    " ( %l{;_}
      & %γ{;_}
      & %𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟{}
      & %Ht_eq{}
      & {%Hproducer_eq{};->}
      & #Hmeta{_{};_}
      & #Hnode_header{_{}}
      & #Hqueues_at{_{}}
      & #Hqueue_inv{_{}}
      & Hqueue_producer{_{}}
      )
    ".

  Definition bag_2۰consumer t consumer : iProp Σ :=
    ∃ l γ 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 (queue : option val),
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    ⌜consumer = #𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟⌝ ∗
    𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟.[consumer_queue] ↦ queue ∗
    queues۰elem γ queue.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_}
      & %γ{;_}
      & %𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟{}
      & %queue{}
      & %Heq{}
      & Hmeta_{}
      & {%Hconsumer_eq{};->}
      & Hconsumer_queue{_{}}
      & #Hqueues_elem{_{}}
      )
    ".

  #[local] Instance queues۰auth𑁒timeless γ nodes descrs wss :
    Timeless (queues۰auth γ nodes descrs wss).
  Proof.
    apply _.
  Qed.
  #[global] Instance bag_2۰model𑁒timeless t vss :
    Timeless (bag_2۰model t vss).
  Proof.
    apply _.
  Qed.

  #[global] Instance bag_2۰inv𑁒persistent t ι :
    Persistent (bag_2۰inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma queues𑁒alloc :
    ⊢ |==>
      ∃ γ_queues,
      queues۰auth' γ_queues [] ∅ ∅.
  Proof.
    iMod mono_gmap𑁒alloc as "(%γ_queues & Hauth)".
    iSteps.
  Qed.
  #[local] Lemma queues۰at𑁒get {γ nodes descrs wss} i node :
    nodes !! i = Some node →
    queues۰auth γ nodes descrs wss ⊢
      ∃ descr,
      ⌜descrs !! node = Some descr⌝ ∗
      queues۰at γ node descr.(descriptor۰queue).
  Proof.
    iIntros "%Hnodes_lookup (:queues۰auth)".
    destruct (elem_of𑁒dom₁ descrs node) as (descr & Hdescrs_lookup).
    { rewrite Hnodes elem_of_list_to_set list_elem_of_lookup. eauto. }
    iDestruct (mono_gmap۰at𑁒get with "Hauth") as "#Hat".
    { rewrite lookup_fmap_Some. eauto. }
    iSteps.
  Qed.
  #[local] Lemma queues۰at𑁒valid γ nodes descrs wss node queue :
    queues۰auth γ nodes descrs wss -∗
    queues۰at γ node queue -∗
      ∃ descr,
      ⌜descrs !! node = Some descr⌝ ∗
      ⌜descr.(descriptor۰queue) = queue⌝ ∗
      ⌜wss !! (descriptor۰to_producer descr node : val) = Some descr.(descriptor۰vals)⌝.
  Proof.
    iIntros "(:queues۰auth) Hat".
    iDestruct (mono_gmap۰at𑁒valid with "Hauth Hat") as %(descr & ? & Hdescrs_lookup)%lookup_fmap_Some.
    iSteps.
  Qed.
  #[local] Lemma queues۰at𑁒valid𑁒producer γ nodes descrs wss 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 :
    queues۰auth γ nodes descrs wss -∗
    queues۰at γ 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰node) 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰queue) -∗
      ∃ descr,
      ⌜descrs !! 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰node) = Some descr⌝ ∗
      ⌜descr.(descriptor۰queue) = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰queue)⌝ ∗
      ⌜wss !! (𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val) = Some descr.(descriptor۰vals)⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (queues۰at𑁒valid with "Hauth Hat") as "(%descr & %Hdescrs_lookup & %Hdescr_queue & %Hwss_lookup)".
    rewrite (producer𑁒eq𑁒alt 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 (descriptor۰to_producer descr 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰node))) //.
    iSteps.
  Qed.
  #[local] Lemma queues𑁒insert {γ nodes descrs wss} node descr :
    descrs !! node = None →
    queues۰auth γ nodes descrs wss ⊢ |==>
      queues۰auth γ
        (node :: nodes)
        (<[node := descr]> descrs)
        (<[descriptor۰to_producer descr node : val := descr.(descriptor۰vals)]> wss) ∗
      queues۰at γ node descr.(descriptor۰queue).
  Proof.
    iIntros "%Hdescrs_lookup (:queues۰auth)".
    iMod (mono_gmap𑁒insert' node descr.(descriptor۰queue) with "Hauth") as "(Hauth & Hat)".
    { rewrite lookup_fmap Hdescrs_lookup //. }
    rewrite -fmap_insert. iSteps; iPureIntro.
    - set_solver.
    - apply map_Forall_insert_2.
      + rewrite lookup_insert_eq //.
      + eapply map_Forall𑁒impl'; first done. move=> /= node' descr' Hdescrs_lookup' Hwss_lookup.
        destruct_decide (node' = node) as -> | ?.
        * simplify.
        * rewrite lookup_insert_ne //.
          intros ?%(inj _)%descriptor۰to_producer𑁒inj. done.
  Qed.
  #[local] Lemma queues𑁒update {γ nodes descrs wss} node descr f :
    descrs !! node = Some descr →
    queues۰auth γ nodes descrs wss ⊢
    queues۰auth γ
      nodes
      (<[node := descriptor۰update_vals descr f]> descrs)
      (<[descriptor۰to_producer descr node : val := f descr.(descriptor۰vals)]> wss).
  Proof.
    iIntros "%Hdescrs_lookup (:queues۰auth)".
    rewrite /queues۰auth /queues۰auth'.
    rewrite fmap_insert /= -fmap_insert insert_id //.
    iFrame. iSplit; iPureIntro.
    - rewrite dom_insert_lookup_L //.
    - apply map_Forall𑁒insert₂'.
      + rewrite lookup_insert_eq //.
      + apply map_Forall𑁒delete𑁒lookup => node' descr' Hnode' Hdescrs_lookup'.
        rewrite lookup_insert_ne; first naive_solver.
        rewrite map_Forall_lookup in Hdescrs. auto.
  Qed.
  #[local] Lemma queues𑁒update𑁒producer {γ nodes descrs wss} 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 descr f :
    descrs !! 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰node) = Some descr →
    descr.(descriptor۰queue) = 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰queue) →
    queues۰auth γ nodes descrs wss ⊢
    queues۰auth γ
      nodes
      (<[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰node) := descriptor۰update_vals descr f]> descrs)
      (<[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val := f descr.(descriptor۰vals)]> wss).
  Proof.
    intros Hdescrs_lookup Hdescr_queue.
    rewrite (queues𑁒update 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟.(producer۰node) descr f) //.
    rewrite /descriptor۰to_producer Hdescr_queue //.
  Qed.

  #[local] Lemma model𑁒alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model ∅ ∗
      model₂' γ_model ∅.
  Proof.
    apply twins𑁒alloc'.
  Qed.
  #[local] Lemma model₁𑁒exclusive γ vss1 vss2 :
    model₁ γ vss1 -∗
    model₁ γ vss2 -∗
    False.
  Proof.
    apply twins۰twin₁𑁒exclusive.
  Qed.
  #[local] Lemma model𑁒agree γ vss1 vss2 :
    model₁ γ vss1 -∗
    model₂ γ vss2 -∗
    ⌜vss1 = vss2⌝.
  Proof.
    apply: twins𑁒agree𑁒L.
  Qed.
  #[local] Lemma model𑁒update {γ vss1 vss2} vss :
    model₁ γ vss1 -∗
    model₂ γ vss2 ==∗
      model₁ γ vss ∗
      model₂ γ vss.
  Proof.
    apply twins𑁒update.
  Qed.

  Opaque queues۰auth'.

  Lemma bag_2۰model𑁒exclusive t vss1 vss2 :
    bag_2۰model t vss1 -∗
    bag_2۰model t vss2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁𑁒exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma bag_2۰producer𑁒valid t ι vss producer ws E :
    ↑ι ⊆ E →
    bag_2۰inv t ι -∗
    bag_2۰model t vss -∗
    bag_2۰producer t producer ws ={E}=∗
      ∃ vs,
      ⌜vss !! producer = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "% (:inv) (:model =1) (:producer =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
    iDestruct (meta𑁒agree with "Hmeta Hmeta_2") as %<-. iClear "Hmeta_2".

    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (model𑁒agree with "Hmodel₁_1 Hmodel₂") as %<-.
    iDestruct (queues۰at𑁒valid𑁒producer with "Hqueues_auth Hqueues_at_2") as %(descr & Hdescrs_lookup & Hdescr_queue & Hvss_lookup).
    iAssert (◇ ⌜descr.(descriptor۰vals) `suffix_of` ws⌝)%I as "#>%".
    { iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor۰model >)"; first done.
      rewrite Hdescr_queue.
      iApply (spmc_queue۰producer𑁒valid with "Hqueue_producer_2 Hqueue_model").
    }
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.
  Lemma bag_2۰producer𑁒exclusive t1 t2 producer ws1 ws2 :
    bag_2۰producer t1 producer ws1 -∗
    bag_2۰producer t2 producer ws2 -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iApply (spmc_queue۰producer𑁒exclusive with "Hqueue_producer_1 Hqueue_producer_2").
  Qed.

  Lemma bag_2۰consumer𑁒exclusive t1 t2 consumer :
    bag_2۰consumer t1 consumer -∗
    bag_2۰consumer t2 consumer -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simplify.
    iApply (pointsto𑁒exclusive with "Hconsumer_queue_1 Hconsumer_queue_2").
  Qed.

  Lemma bag_2٠create𑁒spec ι :
    {{{
      True
    }}}
      bag_2٠create ()
    {{{
      t
    , RET t;
      bag_2۰inv t ι ∗
      bag_2۰model t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰block l as "Hmeta" "(Hl_producers & _)".

    iMod model𑁒alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod queues𑁒alloc as "(%γ_queues & Hqueues_auth)".

    pose γ :=
      {|metadata۰inv := ι
      ; metadata۰model := γ_model
      ; metadata۰queues := γ_queues
      |}.
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. iStep 3. iApply inv_alloc. iFrame.
    iDestruct xtchain𑁒nil as "$".
    rewrite big_sepM_empty. iSteps.
  Qed.

  #[local] Lemma bag_2٠add_producer₀𑁒spec l γ (queue : val) :
    <<<
      l ↪ γ ∗
      inv' l γ ∗
      spmc_queue۰inv queue (γ.(metadata۰inv).@"producer") ∗
      spmc_queue۰model queue []
    | ∀∀ vss,
      model₁ γ vss
    >>>
      bag_2٠add_producer₀ #l (Some queue) @ ↑γ.(metadata۰inv)
    <<<
      ∃∃ node,
      let 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 :=
        {|producer۰queue := queue
        ; producer۰node := node
        |}
      in
      model₁ γ (<[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val := []]> vss)
    | RET #node;
      node ↦ₕ Header §Node 2 ∗
      queues۰at γ node queue
    >>>.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hqueue_inv & Hqueue_model) HΦ".
    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (_.{producers})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iSplitR "Hqueue_model HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    wp۰block node as "#Hnode_header" "_" "(Hnode_next & Hnode_queue & _)".
    iMod (pointsto𑁒persist with "Hnode_next") as "#Hnode_next".
    wp۰match. wp۰pures.

    wp۰bind (CAS _ _ _).
    iInv "Hinv" as "(:inv۰inner =2)".
    wp۰cas as Hcas; first iSteps.
    assert (head nodes1 = head nodes2) as ->.
    { destruct nodes1, nodes2; zoo_simplify; done. }
    iDestruct (xtchain𑁒cons₂ with "Hnode_header [] Hnodes2") as "Hnodes"; first iSteps.

    iAssert ⌜descrs2 !! node = None⌝%I as %Hdescr2_lookup.
    { rewrite eq_None_not_Some. iIntros "(%descr' & %)".
      iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor۰model =')"; first done.
      iApply (pointsto𑁒exclusive with "Hnode_queue Hnode'_queue").
    }

    pose descr :=
      {|descriptor۰queue := queue
      ; descriptor۰vals := []
      |}.
    iMod (queues𑁒insert node descr with "Hqueues_auth") as "(Hqueues_auth & #Hqueues_at)"; first done.
    iDestruct (big_sepM_insert_2 _ _ node descr with "[Hnode_queue Hqueue_model] Hdescrs") as "Hdescrs".
    { iExists (Some queue). iSteps. }

    iMod "HΦ" as "(%vss & Hmodel₁ & _ & HΦ)".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %<-.
    set vss' :=
      <[descriptor۰to_producer descr node : val := []]> vss.
    iMod (model𑁒update vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "Hmodel₁ [$Hnode_header $Hqueues_at]") as "HΦ".

    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma bag_2٠add_producer𑁒spec l γ (queue : val) :
    <<<
      l ↪ γ ∗
      inv' l γ ∗
      spmc_queue۰inv queue (γ.(metadata۰inv).@"producer") ∗
      spmc_queue۰model queue []
    | ∀∀ vss,
      model₁ γ vss
    >>>
      bag_2٠add_producer #l queue @ ↑γ.(metadata۰inv)
    <<<
      ∃∃ node,
      let 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 :=
        {|producer۰queue := queue
        ; producer۰node := node
        |}
      in
      model₁ γ (<[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val := []]> vss)
    | RET #node;
      node ↦ₕ Header §Node 2 ∗
      queues۰at γ node queue
    >>>.
  Proof.
    iIntros "%Φ H HΦ".

    wp۰rec.
    wp۰apply+ (bag_2٠add_producer₀𑁒spec with "H HΦ").
  Qed.
  Lemma bag_2٠create_producer𑁒spec t ι :
    <<<
      bag_2۰inv t ι
    | ∀∀ vss,
      bag_2۰model t vss
    >>>
      bag_2٠create_producer t @ ↑ι
    <<<
      ∃∃ producer,
      bag_2۰model t (<[producer := []]> vss)
    | RET producer;
      bag_2۰producer t producer []
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    wp۰apply (spmc_queue٠create𑁒spec with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model & Hqueue_producer)".

    awp۰apply+ (bag_2٠add_producer𑁒spec with "[$Hmeta $Hinv $Hqueue_inv $Hqueue_model]") without "Hqueue_producer".
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vss (:model)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hmodel₁"; iSteps.
  Qed.

  Lemma bag_2٠close_producer𑁒spec t ι producer ws :
    {{{
      bag_2۰inv t ι ∗
      bag_2۰producer t producer ws
    }}}
      bag_2٠close_producer producer
    {{{
      RET ();
      bag_2۰producer t producer ws
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ". injection Ht_eq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰match.

    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (queues۰at𑁒valid𑁒producer with "Hqueues_auth Hqueues_at") as %(descr & Hdescrs_lookup & Hdescr_queue & Hwss_lookup).
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model >) & Hdescrs)"; first done.
    wp۰store.
    iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs".
    { iExists None. rewrite Hdescr_queue. iSteps. }
    iSplitR "Hqueue_producer HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma bag_2٠create_consumer𑁒spec t ι :
    {{{
      bag_2۰inv t ι
    }}}
      bag_2٠create_consumer t
    {{{
      consumer
    , RET consumer;
      bag_2۰consumer t consumer
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    wp۰block 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 as "(Hconsumer_queue & _)".
    iSteps. iExists None. iSteps.
  Qed.

  Lemma bag_2٠push𑁒spec t ι producer ws v :
    <<<
      bag_2۰inv t ι ∗
      bag_2۰producer t producer ws
    | ∀∀ vss,
      bag_2۰model t vss
    >>>
      bag_2٠push producer v @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! producer = Some vs⌝ ∗
      bag_2۰model t (<[producer := vs ++ [v]]> vss)
    | RET ();
      bag_2۰producer t producer (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ". injection Ht_eq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec.

    awp۰apply+ (spmc_queue٠push𑁒spec with "[$Hqueue_inv $Hqueue_producer]").
    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (queues۰at𑁒valid𑁒producer with "Hqueues_auth Hqueues_at") as %(descr & Hdescrs_lookup & Hdescr_queue & Hwss_lookup). rewrite -Hdescr_queue.
    iDestruct (big_sepM_insert_acc with "Hdescrs") as "((:descriptor۰model >) & Hdescrs)"; first done.
    iAaccIntro with "Hqueue_model"; iIntros "Hqueue_model".
    { iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.
      rewrite insert_id //. iFrameSteps.
    }
    iDestruct (queues𑁒update𑁒producer 𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 descr (.++ [v]) with "Hqueues_auth") as "Hqueues_auth"; [done.. |].
    set descr' :=
      descriptor۰update_vals descr (.++ [v]).
    iDestruct ("Hdescrs" $! descr' with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.

    iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %<-.
    set vss' :=
      <[𝑝𝑟𝑜𝑑𝑢𝑐𝑒𝑟 : val := descr.(descriptor۰vals) ++ [v]]> vss.
    iMod (model𑁒update vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "HΦ". { iFrameSteps. }
    rewrite Hdescr_queue. iSteps.
  Qed.

  #[local] Lemma bag_2٠pop₀𑁒spec l γ 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 (queue : option val) nodes :
    <<<
      l ↪ γ ∗
      inv' l γ ∗
      𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟.[consumer_queue] ↦ queue ∗
      queues۰elem γ queue ∗
      xtchain (Header §Node 2) DfracDiscarded nodes §Null ∗
      [∗ list] node ∈ nodes,
        ∃ queue,
        queues۰at γ node queue
    | ∀∀ vss,
      model₁ γ vss
    >>>
      bag_2٠pop₀ #𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 (from_option #@{location} §Null%V $ head nodes) @ ↑γ.(metadata۰inv)
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
      queues۰elem γ queue
    >>>.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & Hconsumer_queue & #Hqueues_elem & Hnodes & Hqueues_ats) HΦ".

    iLöb as "HLöb" forall (nodes).

    wp۰rec.
    destruct nodes as [| node nodes].

    - wp۰pures.

      iMod "HΦ" as "(%vss & Hmodel₁ & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel₁") as "HΦ".

      iSteps.

    - iDestruct (xtchain𑁒cons' with "Hnodes") as "-#(#Hnode_header & #Hnode_next & #Hnodes)".
      iDestruct (big_sepL𑁒cons₁ with "Hqueues_ats") as "-#((%queue0 & #Hqueues_at) & #Hqueues_ats)".
      wp۰match.

      wp۰bind (_.{queue})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (queues۰at𑁒valid with "Hqueues_auth Hqueues_at") as "#(%descr & %Hdescrs1_lookup & %Hdescr_queue & _)".
      iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model =0 > inv=) & Hdescrs)"; first done.
      wp۰load.
      iSplitR "Hconsumer_queue HΦ". { iFrameSteps. }
      rewrite Hdescr_queue. iIntros "!>".

      destruct o0 as [queue0_ |]; wp۰pures.

      + rewrite Ho0 Hdescr_queue. clear.

        awp۰apply+ (spmc_queue٠pop𑁒spec with "Hqueue0_inv") without "Hconsumer_queue".
        iInv "Hinv" as "(:inv۰inner =2)".
        iDestruct (queues۰at𑁒valid with "Hqueues_auth Hqueues_at") as "(%descr & %Hdescrs_lookup & %Hdescr_queue & %Hwss_lookup)".
        iDestruct (big_sepM_insert_acc with "Hdescrs") as "((:descriptor۰model >) & Hdescrs)"; first done.
        rewrite -Hdescr_queue.
        iAaccIntro with "Hqueue_model"; iIntros "Hqueue_model".
        { iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.
          rewrite insert_id //. iFrameSteps.
        }
        destruct descr.(descriptor۰vals) as [| v vs] eqn:Hdescr_vals => /=.

        * iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs".
          { rewrite -Hdescr_vals. iFrameSteps. }
          rewrite insert_id //.
          iSplitR "HΦ". { iFrameSteps. }
          iIntros "{%} !> _ Hconsumer_queue".

          wp۰load.
          wp۰apply ("HLöb" $! nodes with "Hconsumer_queue Hnodes [$] HΦ").

        * iMod "HΦ" as "(%vss & Hmodel₁ & _ & HΦ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %<-.
          set vss' :=
            <[descriptor۰to_producer descr node : val := vs]> vss.
          iMod (model𑁒update vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ"; first iSteps.

          iDestruct (queues𑁒update node descr (const vs) with "Hqueues_auth") as "Hqueues_auth"; first done.
          set descr' :=
            descriptor۰update_vals descr (const vs).
          iDestruct ("Hdescrs" $! descr' with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iFrameSteps.

          iSplitR "HΦ". { iFrameSteps. }
          iSteps. iExists (Some _). iSteps.

      + wp۰load.
        wp۰apply ("HLöb" $! nodes with "Hconsumer_queue Hnodes [$] HΦ").
  Qed.
  #[local] Lemma bag_2٠pop₁𑁒spec t ι consumer :
    <<<
      bag_2۰inv t ι ∗
      bag_2۰consumer t consumer
    | ∀∀ vss,
      bag_2۰model t vss
    >>>
      bag_2٠pop₁ t consumer @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          bag_2۰model t vss
      | Some v =>
          ∃ producer vs,
          ⌜vss !! producer = Some (v :: vs)⌝ ∗
          bag_2۰model t (<[producer := vs]> vss)
      end
    | RET o;
      bag_2۰consumer t consumer
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰pures.

    wp۰bind (_.{producers})%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iDestruct "Hnodes" as "#Hnodes".

    iAssert (
      [∗ list] node ∈ nodes,
        ∃ queue,
        queues۰at γ node queue
    )%I as "#queues۰ats".
    { iApply big_sepL_forall. iIntros "%i %node %Hnodes_lookup".
      iDestruct (queues۰at𑁒get with "Hqueues_auth") as "(%descr & %Hdescrs_lookup & #Hqueues_at)"; first done.
      iSteps.
    }

    iSplitR "Hconsumer_queue HΦ". { iFrameSteps. }
    iIntros "{%} !>".

    awp۰apply+ (bag_2٠pop₀𑁒spec with "[- HΦ]"); first iFrameSteps.
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vss (:model)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%o Hmodel₁ !>".
    iExists o. destruct o as [v |]; last iSteps.
    iDestruct "Hmodel₁" as "(%producer & %vs & %Hvss_lookup & Hmodel₁)".
    iSteps.
  Qed.
  Lemma bag_2٠pop𑁒spec t ι consumer :
    <<<
      bag_2۰inv t ι ∗
      bag_2۰consumer t consumer
    | ∀∀ vss,
      bag_2۰model t vss
    >>>
      bag_2٠pop t consumer @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          bag_2۰model t vss
      | Some v =>
          ∃ producer vs,
          ⌜vss !! producer = Some (v :: vs)⌝ ∗
          bag_2۰model t (<[producer := vs]> vss)
      end
    | RET o;
      bag_2۰consumer t consumer
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    destruct queue as [queue |].

    - iDestruct "Hqueues_elem" as "(:queues۰elem)".
      awp۰apply+ (spmc_queue٠pop𑁒spec with "Hqueue_inv") without "Hconsumer_queue".
      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (queues۰at𑁒valid with "Hqueues_auth Hqueues_at") as "(%descr & %Hdescrs_lookup & %Hdescr_queue & %Hwss_lookup)".
      iDestruct (big_sepM_insert_acc with "Hdescrs") as "((:descriptor۰model >) & Hdescrs)"; first done.
      rewrite -Hdescr_queue.
      iAaccIntro with "Hqueue_model"; iIntros "Hqueue_model".
      { iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.
        rewrite insert_id //. iFrameSteps.
      }
      destruct descr.(descriptor۰vals) as [| v vs] eqn:Hdescr_vals => /=.

      + iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs".
        { rewrite -Hdescr_vals. iFrameSteps. }
        rewrite insert_id //.
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "{%} !> _ Hconsumer_queue".

        wp۰apply+ (bag_2٠pop₁𑁒spec with "[- HΦ] HΦ").
        { iSplitR; iSteps. iExists (Some _). iSteps. }

      + iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %<-.
        set vss' :=
          <[descriptor۰to_producer descr node : val := vs]> vss.
        iMod (model𑁒update vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ"; first iSteps.

        iDestruct (queues𑁒update node descr (const vs) with "Hqueues_auth") as "Hqueues_auth"; first done.
        set descr' :=
          descriptor۰update_vals descr (const vs).
        iDestruct ("Hdescrs" $! descr' with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iFrameSteps.

        iSplitR "HΦ". { iFrameSteps. }
        iSteps. iExists (Some _). iSteps.

    - wp۰apply+ (bag_2٠pop₁𑁒spec with "[- HΦ] HΦ").
      { iSplitR; iSteps. iExists None. iSteps. }
  Qed.
End bag_2۰G.

Require zoo_saturn.bag_2__opaque.

#[global] Opaque bag_2۰inv.
#[global] Opaque bag_2۰model.
#[global] Opaque bag_2۰producer.
#[global] Opaque bag_2۰consumer.
