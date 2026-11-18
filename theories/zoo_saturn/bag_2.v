Require Import zoo.prelude.
Require Import zoo.common.fin_maps.
Require Import zoo.iris.base_logic.lib.mono_gmap.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.xtchain.
Require Export zoo_saturn.bag_2__code.
Require Import zoo_saturn.bag_2__types.
Require Import zoo.options.

Implicit Type node 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 : location.
Implicit Type nodes : list location.
Implicit Type v consumer backoff : val.
Implicit Type vs ws : list val.

Zoo name :=
  { self : location
  ; inv : namespace
  ; model : gname
  ; queues : gname
  }.

Record bag_2۰producer۰name :=
  { bag_2۰producer۰name۰queue : queue_spmc۰name
  ; bag_2۰producer۰name۰node : location
  }.
Implicit Type producer : bag_2۰producer۰name.

Please derive Inhabited for bag_2۰producer۰name.
Please derive EqDecision for bag_2۰producer۰name.
Please derive Countable for bag_2۰producer۰name.

Implicit Type vss wss : gmap bag_2۰producer۰name (list val).

Coercion bag_2۰producer۰name۰to_val producer : val :=
  ( producer.(bag_2۰producer۰name۰queue)
  , #producer.(bag_2۰producer۰name۰node)
  ).
#[global] Instance bag_2۰producer۰nameｰto_val : ToVal bag_2۰producer۰name :=
  bag_2۰producer۰name۰to_val.

Zoo global :=
  { queue_spmc : queue_spmc
  ; queues : mono_gmap location queue_spmc۰name
  ; model : twins (leibnizO (gmap bag_2۰producer۰name (list val)))
  }.

#[local] Lemma producer۰nameｰeqｰalt producer1 producer2 :
  producer1.(bag_2۰producer۰name۰queue) = producer2.(bag_2۰producer۰name۰queue) →
  producer1.(bag_2۰producer۰name۰node) = producer2.(bag_2۰producer۰name۰node) →
  producer1 = producer2.
Proof.
  destruct producer1, producer2; naive.
Qed.

Record descriptor :=
  { descriptor۰queue : queue_spmc۰name
  ; descriptor۰vals : list val
  }.
Implicit Type descr : descriptor.
Implicit Type descrs : gmap location descriptor.

#[local] Definition descriptor۰update_vals descr f :=
  {|descriptor۰queue := descr.(descriptor۰queue)
  ; descriptor۰vals := f descr.(descriptor۰vals)
  |}.

#[local] Definition descriptor۰to_producer descr node :=
  {|bag_2۰producer۰name۰queue := descr.(descriptor۰queue)
  ; bag_2۰producer۰name۰node := node
  |}.

#[local] Lemma descriptor۰to_producerｰinj descr1 node1 descr2 node2 :
  descriptor۰to_producer descr1 node1 = descriptor۰to_producer descr2 node2 →
  node1 = node2.
Proof.
  naive.
Qed.

Section bag_2۰G.
  Context `{bag_2۰G : Bag2G Σ}.

  #[local] Definition queues۰auth' γ_queues nodes descrs wss : iProp Σ :=
    mono_gmap۰auth γ_queues (DfracOwn 1) (descriptor۰queue <$> descrs) ∗
    ⌜dom descrs = list_to_set nodes⌝ ∗
    ⌜ map_Forall (λ node descr,
        wss !! (descriptor۰to_producer descr node) = Some descr.(descriptor۰vals)
      ) descrs
    ⌝.
  #[local] Instance : CustomIpat "queues۰auth" :=
    " ( Hauth
      & %Hnodes
      & %Hdescrs
      )
    ".
  #[local] Definition queues۰auth γ :=
    queues۰auth' γ.(bag_2۰name۰queues).
  #[local] Definition queues۰at' :=
    mono_gmap۰at.
  #[local] Definition queues۰at γ :=
    queues۰at' γ.(bag_2۰name۰queues).
  #[local] Definition queues۰elem γ queue : iProp Σ :=
    match queue with
    | None =>
        True
    | Some queue =>
        ∃ node,
        queues۰at γ node queue ∗
        queue_spmc۰inv queue (γ.(bag_2۰name۰inv).@"producer")
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
    model₁' γ.(bag_2۰name۰model).
  #[local] Definition model₂' γ_model vss :=
    twins۰twin₂ γ_model vss.
  #[local] Definition model₂ γ :=
    model₂' γ.(bag_2۰name۰model).

  #[local] Definition descriptor۰model γ node descr : iProp Σ :=
    ∃ (o : option queue_spmc۰name),
    node.[queue] ↦ ((♯) <$> o : option val) ∗
    ⌜from_option (.= descr.(descriptor۰queue)) True o⌝ ∗
    queue_spmc۰inv descr.(descriptor۰queue) (γ.(bag_2۰name۰inv).@"producer") ∗
    queue_spmc۰model descr.(descriptor۰queue) descr.(descriptor۰vals).
  #[local] Instance : CustomIpat "descriptor۰model" :=
    " ( %o{}
      & Hnode{}_queue
      & {>;}%Ho{}
      & {{inv}#Hqueue{}_inv;{inv}#Hqueue_inv;_}
      & {>;}Hqueue{}_model
      )
    ".

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ nodes descrs wss,
    γ.(bag_2۰name۰self).[producers] ↦ from_option (#ˡ) §Null (head nodes) ∗
    xtchain (Header §Node 2) DfracDiscarded nodes §Null ∗
    queues۰auth γ nodes descrs wss ∗
    model₂ γ wss ∗
    [∗ map] node ↦ descr ∈ descrs,
      descriptor۰model γ node descr.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %nodes{}
      & %descrs{}
      & %wss
      & Ht_producers
      & Hnodes{}
      & >Hqueues_auth
      & >Hmodel₂
      & Hdescrs
      )
    ".
  #[local] Definition inv' γ :=
    inv (γ.(bag_2۰name۰inv).@"inv") (inv۰inner γ).
  Please Definition bag_2۰inv γ ι : iProp Σ :=
    ⌜ι = γ.(bag_2۰name۰inv)⌝ ∗
    inv' γ.
  #[local] Instance : CustomIpat "inv" :=
    " ( ->
      & #Hinv
      )
    ".

  Please Definition bag_2۰model :=
    model₁.
  #[local] Instance : CustomIpat "model" :=
    " Hmodel₁{_{}}
    ".

  Please Definition bag_2۰producer γ producer ws : iProp Σ :=
    producer.(bag_2۰producer۰name۰node) ↦ₕ Header §Node 2 ∗
    queues۰at γ producer.(bag_2۰producer۰name۰node) producer.(bag_2۰producer۰name۰queue) ∗
    queue_spmc۰inv producer.(bag_2۰producer۰name۰queue) (γ.(bag_2۰name۰inv).@"producer") ∗
    queue_spmc۰producer producer.(bag_2۰producer۰name۰queue) ws.
  #[local] Instance : CustomIpat "producer" :=
    " ( #Hnode_header{_{}}
      & #Hqueues_at{_{}}
      & #Hqueue_inv{_{}}
      & Hqueue_producer{_{}}
      )
    ".

  Please Definition bag_2۰consumer γ consumer : iProp Σ :=
    ∃ 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 (queue : option queue_spmc۰name),
    ⌜consumer = #𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟⌝ ∗
    𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟.[consumer_queue] ↦ ((♯) <$> queue : option val) ∗
    queues۰elem γ queue.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟{}
      & %queue{}
      & {%Hconsumer_eq{};->}
      & Hconsumer_queue{_{}}
      & #Hqueues_elem{_{}}
      )
    ".

  #[local] Zoo derive Timeless for queues۰auth.
  Zoo derive Timeless for bag_2۰model.

  Zoo derive Persistent for bag_2۰inv.

  #[local] Lemma queuesｰalloc :
    ⊢ |==>
      ∃ γ_queues,
      queues۰auth' γ_queues [] ∅ ∅.
  Proof.
    iMod mono_gmapｰalloc as "(%γ_queues & Hauth)".
    iSteps.
  Qed.
  #[local] Lemma queues۰atｰget {γ nodes descrs wss} i node :
    nodes !! i = Some node →
    queues۰auth γ nodes descrs wss ⊢
      ∃ descr,
      ⌜descrs !! node = Some descr⌝ ∗
      queues۰at γ node descr.(descriptor۰queue).
  Proof.
    iIntros "%Hnodes_lookup (:queues۰auth)".
    destruct (elem_ofｰdom₁ descrs node) as (descr & Hdescrs_lookup).
    { rewrite Hnodes elem_of_list_to_set list_elem_of_lookup. eauto. }
    iDestruct (mono_gmap۰atｰget with "Hauth") as "#Hat".
    { rewrite lookup_fmap_Some. eauto. }
    iSteps.
  Qed.
  #[local] Lemma queues۰atｰvalid γ nodes descrs wss node queue :
    queues۰auth γ nodes descrs wss -∗
    queues۰at γ node queue -∗
      ∃ descr,
      ⌜descrs !! node = Some descr⌝ ∗
      ⌜descr.(descriptor۰queue) = queue⌝ ∗
      ⌜wss !! (descriptor۰to_producer descr node) = Some descr.(descriptor۰vals)⌝.
  Proof.
    iIntros "(:queues۰auth) Hat".
    iDestruct (mono_gmap۰atｰvalid with "Hauth Hat") as %(descr & ? & Hdescrs_lookup)%lookup_fmap_Some.
    iSteps.
  Qed.
  #[local] Lemma queues۰atｰvalidｰproducer γ nodes descrs wss producer :
    queues۰auth γ nodes descrs wss -∗
    queues۰at γ producer.(bag_2۰producer۰name۰node) producer.(bag_2۰producer۰name۰queue) -∗
      ∃ descr,
      ⌜descrs !! producer.(bag_2۰producer۰name۰node) = Some descr⌝ ∗
      ⌜descr.(descriptor۰queue) = producer.(bag_2۰producer۰name۰queue)⌝ ∗
      ⌜wss !! producer = Some descr.(descriptor۰vals)⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (queues۰atｰvalid with "Hauth Hat") as "(%descr & %Hdescrs_lookup & %Hdescr_queue & %Hwss_lookup)".
    rewrite (producer۰nameｰeqｰalt producer (descriptor۰to_producer descr producer.(bag_2۰producer۰name۰node))) //.
    iSteps.
  Qed.
  #[local] Lemma queuesｰinsert {γ nodes descrs wss} node descr :
    descrs !! node = None →
    queues۰auth γ nodes descrs wss ⊢ |==>
      queues۰auth γ
        (node :: nodes)
        (<[node := descr]> descrs)
        (<[descriptor۰to_producer descr node := descr.(descriptor۰vals)]> wss) ∗
      queues۰at γ node descr.(descriptor۰queue).
  Proof.
    iIntros "%Hdescrs_lookup (:queues۰auth)".
    iMod (mono_gmapｰinsert' node descr.(descriptor۰queue) with "Hauth") as "(Hauth & Hat)".
    { rewrite lookup_fmap Hdescrs_lookup //. }
    rewrite -fmap_insert. iSteps; iPureIntro.
    - set_solver.
    - apply map_Forall_insert_2.
      + rewrite lookup_insert_eq //.
      + eapply map_Forallｰimpl'; first done. move=> /= node' descr' Hdescrs_lookup' Hwss_lookup.
        destruct_decide (node' = node) as -> | ?.
        * simp.
        * rewrite lookup_insert_ne //.
          intros ?%descriptor۰to_producerｰinj. done.
  Qed.
  #[local] Lemma queuesｰupdate {γ nodes descrs wss} node descr f :
    descrs !! node = Some descr →
    queues۰auth γ nodes descrs wss ⊢
    queues۰auth γ
      nodes
      (<[node := descriptor۰update_vals descr f]> descrs)
      (<[descriptor۰to_producer descr node := f descr.(descriptor۰vals)]> wss).
  Proof.
    iIntros "%Hdescrs_lookup (:queues۰auth)".
    rewrite /queues۰auth /queues۰auth'.
    rewrite fmap_insert /= -fmap_insert insert_id //.
    iFrame. iSplit; iPureIntro.
    - rewrite dom_insert_lookup_L //.
    - apply map_Forallｰinsert₂'.
      + rewrite lookup_insert_eq //.
      + apply map_Forallｰdeleteｰlookup => node' descr' Hnode' Hdescrs_lookup'.
        rewrite lookup_insert_ne; first naive.
        rewrite map_Forall_lookup in Hdescrs. auto.
  Qed.
  #[local] Lemma queuesｰupdateｰproducer {γ nodes descrs wss} producer descr f :
    descrs !! producer.(bag_2۰producer۰name۰node) = Some descr →
    descr.(descriptor۰queue) = producer.(bag_2۰producer۰name۰queue) →
    queues۰auth γ nodes descrs wss ⊢
    queues۰auth γ
      nodes
      (<[producer.(bag_2۰producer۰name۰node) := descriptor۰update_vals descr f]> descrs)
      (<[producer := f descr.(descriptor۰vals)]> wss).
  Proof.
    intros Hdescrs_lookup Hdescr_queue.
    rewrite (queuesｰupdate _ _ f) //.
    rewrite /descriptor۰to_producer Hdescr_queue.
    setoid_rewrite (producer۰nameｰeqｰalt _ producer) => //.
  Qed.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model ∅ ∗
      model₂' γ_model ∅.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ vss1 vss2 :
    model₁ γ vss1 -∗
    model₁ γ vss2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ vss1 vss2 :
    model₁ γ vss1 -∗
    model₂ γ vss2 -∗
    ⌜vss1 = vss2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ vss1 vss2} vss :
    model₁ γ vss1 -∗
    model₂ γ vss2 ==∗
      model₁ γ vss ∗
      model₂ γ vss.
  Proof.
    apply twinsｰupdate.
  Qed.

  Opaque queues۰auth'.

  Lemma bag_2۰modelｰexclusive γ vss1 vss2 :
    bag_2۰model γ vss1 -∗
    bag_2۰model γ vss2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma bag_2۰producerｰvalid γ ι vss producer ws E :
    ↑ι ⊆ E →
    bag_2۰inv γ ι -∗
    bag_2۰model γ vss -∗
    bag_2۰producer γ producer ws ={E}=∗
      ∃ vs,
      ⌜vss !! producer = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "% (:inv) (:model =1) (:producer =2)".

    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (modelｰagree with "Hmodel₁_1 Hmodel₂") as %<-.
    iDestruct (queues۰atｰvalidｰproducer with "Hqueues_auth Hqueues_at_2") as %(descr & Hdescrs_lookup & Hdescr_queue & Hvss_lookup).
    iAssert (◇ ⌜descr.(descriptor۰vals) `suffix_of` ws⌝)%I as "#>%".
    { iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor۰model >)"; first done.
      rewrite Hdescr_queue.
      iApply (queue_spmc۰producerｰvalid with "Hqueue_producer_2 Hqueue_model").
    }
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.
  Lemma bag_2۰producerｰexclusive γ1 γ2 producer ws1 ws2 :
    bag_2۰producer γ1 producer ws1 -∗
    bag_2۰producer γ2 producer ws2 -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)".
    iApply (queue_spmc۰producerｰexclusive with "Hqueue_producer_1 Hqueue_producer_2").
  Qed.

  Lemma bag_2۰consumerｰexclusive γ1 γ2 consumer :
    bag_2۰consumer γ1 consumer -∗
    bag_2۰consumer γ2 consumer -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simp.
    iApply (pointstoｰexclusive with "Hconsumer_queue_1 Hconsumer_queue_2").
  Qed.

  Lemma bag_2٠createｰspec ι :
    {{{
      True
    }}}
      bag_2٠create ()
    {{{
      γ
    , RET γ;
      bag_2۰inv γ ι ∗
      bag_2۰model γ ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰block t as "Ht_producers".

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod queuesｰalloc as "(%γ_queues & Hqueues_auth)".

    pose γ :=
      {|bag_2۰name۰self := t
      ; bag_2۰name۰inv := ι
      ; bag_2۰name۰model := γ_model
      ; bag_2۰name۰queues := γ_queues
      |}.

    iApply ("HΦ" $! γ).
    iSplitR "Hmodel₁"; last iSteps.
    iStep. iApply inv_alloc. iFrame.
    iDestruct xtchainｰnil as "$".
    iSteps.
  Qed.

  #[local] Lemma bag_2٠add_producer₁ｰspec γ (queue : queue_spmc۰name) backoff :
    <<<
      inv' γ ∗
      queue_spmc۰inv queue (γ.(bag_2۰name۰inv).@"producer") ∗
      queue_spmc۰model queue [] ∗
      backoff۰model backoff
    | ∀∀ vss,
      model₁ γ vss
    >>>
      bag_2٠add_producer₁ γ (Some (queue : val)) backoff
      @ ↑γ.(bag_2۰name۰inv)
    <<<
      ∃∃ node,
      let producer :=
        {|bag_2۰producer۰name۰queue := queue
        ; bag_2۰producer۰name۰node := node
        |}
      in
      model₁ γ (<[producer := []]> vss)
    | RET #node;
      node ↦ₕ Header §Node 2 ∗
      queues۰at γ node queue
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & #Hqueue_inv & Hqueue_model & Hbackoff) HΦ".

    iLöb as "HLöb" forall (backoff).

    wp۰rec. wp۰pures.

    wp۰bind (_.{producers})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iSplitR "Hqueue_model Hbackoff HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    wp۰block node as "#Hnode_next Hnode_queue" header:"#Hnode_header".
    wp۰match. wp۰pures.

    wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner =2)".
    wp۰cas as Hcas; first iSteps.
    assert (head nodes1 = head nodes2) as ->.
    { destruct nodes1, nodes2; zoo۰simp; done. }
    iDestruct (xtchainｰcons₂ with "Hnode_header [] Hnodes2") as "Hnodes"; first iSteps.

    iAssert ⌜descrs2 !! node = None⌝%I as %Hdescr2_lookup.
    { rewrite eq_None_not_Some. iIntros "(%descr' & %)".
      iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor۰model =')"; first done.
      iApply (pointstoｰexclusive with "Hnode_queue Hnode'_queue").
    }

    pose descr :=
      {|descriptor۰queue := queue
      ; descriptor۰vals := []
      |}.
    iMod (queuesｰinsert node descr with "Hqueues_auth") as "(Hqueues_auth & #Hqueues_at)"; first done.
    iDestruct (big_sepM_insert_2 _ _ node descr with "[Hnode_queue Hqueue_model] Hdescrs") as "Hdescrs".
    { iExists (Some queue). iSteps. }

    iMod "HΦ" as "(%vss & Hmodel₁ & _ & HΦ)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
    set vss' :=
      <[descriptor۰to_producer descr node := []]> vss.
    iMod (modelｰupdate vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "Hmodel₁ [$Hnode_header $Hqueues_at]") as "HΦ".

    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma bag_2٠add_producerｰspec γ (queue : queue_spmc۰name) :
    <<<
      inv' γ ∗
      queue_spmc۰inv queue (γ.(bag_2۰name۰inv).@"producer") ∗
      queue_spmc۰model queue []
    | ∀∀ vss,
      model₁ γ vss
    >>>
      bag_2٠add_producer γ queue
      @ ↑γ.(bag_2۰name۰inv)
    <<<
      ∃∃ node,
      let producer :=
        {|bag_2۰producer۰name۰queue := queue
        ; bag_2۰producer۰name۰node := node
        |}
      in
      model₁ γ (<[producer := []]> vss)
    | RET #node;
      node ↦ₕ Header §Node 2 ∗
      queues۰at γ node queue
    >>>.
  Proof.
    iIntros "%Φ (Hinv & Hqueue_inv & Hqueue_model) HΦ".

    wp۰rec.
    wp۰apply+ (bag_2٠add_producer₁ｰspec with "[- HΦ] HΦ"). 1: iFrameSteps.
  Qed.

  Lemma bag_2٠create_producerｰspec γ ι :
    <<<
      bag_2۰inv γ ι
    | ∀∀ vss,
      bag_2۰model γ vss
    >>>
      bag_2٠create_producer γ
      @ ↑ι
    <<<
      ∃∃ producer,
      bag_2۰model γ (<[producer := []]> vss)
    | RET producer;
      bag_2۰producer γ producer []
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    wp۰apply (queue_spmc٠createｰspec with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model & Hqueue_producer)".

    awp۰apply+ (bag_2٠add_producerｰspec with "[$Hinv $Hqueue_inv $Hqueue_model]") without "Hqueue_producer".
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vss (:model)".
    iAaccIntro with "Hmodel₁"; iSteps.
  Qed.

  Lemma bag_2٠close_producerｰspec γ ι producer ws :
    {{{
      bag_2۰inv γ ι ∗
      bag_2۰producer γ producer ws
    }}}
      bag_2٠close_producer producer
    {{{
      RET ();
      bag_2۰producer γ producer ws
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ".

    wp۰rec. wp۰match.

    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (queues۰atｰvalidｰproducer with "Hqueues_auth Hqueues_at") as %(descr & Hdescrs_lookup & Hdescr_queue & Hwss_lookup).
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model >) & Hdescrs)"; first done.
    wp۰store.
    iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs".
    { iExists None. rewrite Hdescr_queue. iSteps. }
    iSplitR "Hqueue_producer HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma bag_2٠create_consumerｰspec γ ι :
    {{{
      bag_2۰inv γ ι
    }}}
      bag_2٠create_consumer γ
    {{{
      consumer
    , RET consumer;
      bag_2۰consumer γ consumer
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    wp۰block 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 as "Hconsumer_queue".
    iSteps. iExists None. iSteps.
  Qed.

  Lemma bag_2٠pushｰspec γ ι producer ws v :
    <<<
      bag_2۰inv γ ι ∗
      bag_2۰producer γ producer ws
    | ∀∀ vss,
      bag_2۰model γ vss
    >>>
      bag_2٠push producer v
      @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! producer = Some vs⌝ ∗
      bag_2۰model γ (<[producer := vs ++ [v]]> vss)
    | RET ();
      bag_2۰producer γ producer (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ".

    wp۰rec.

    awp۰apply+ (queue_spmc٠pushｰspec with "[$Hqueue_inv $Hqueue_producer]").
    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (queues۰atｰvalidｰproducer with "Hqueues_auth Hqueues_at") as %(descr & Hdescrs_lookup & Hdescr_queue & Hwss_lookup). rewrite -Hdescr_queue.
    iDestruct (big_sepM_insert_acc with "Hdescrs") as "((:descriptor۰model >) & Hdescrs)"; first done.
    iAaccIntro with "Hqueue_model"; iIntros "Hqueue_model".
    { iDestruct ("Hdescrs" with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.
      rewrite insert_id //. iFrameSteps.
    }
    iApply (queuesｰupdateｰproducer producer descr (.++ [v])) in "Hqueues_auth"; [done.. |].
    set descr' :=
      descriptor۰update_vals descr (.++ [v]).
    iDestruct ("Hdescrs" $! descr' with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iSteps.

    iMod "HΦ" as "(%vss & (:model) & _ & HΦ)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
    set vss' :=
      <[producer := descr.(descriptor۰vals) ++ [v]]> vss.
    iMod (modelｰupdate vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "HΦ". { iFrameSteps. }
    rewrite Hdescr_queue. iSteps.
  Qed.

  #[local] Lemma bag_2٠pop₂ｰspec γ 𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 (queue : option queue_spmc۰name) nodes :
    <<<
      inv' γ ∗
      𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟.[consumer_queue] ↦ ((♯) <$> queue : option val) ∗
      queues۰elem γ queue ∗
      xtchain (Header §Node 2) DfracDiscarded nodes §Null ∗
      [∗ list] node ∈ nodes,
        ∃ queue,
        queues۰at γ node queue
    | ∀∀ vss,
      model₁ γ vss
    >>>
      bag_2٠pop₂ #𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟 (from_option (#ˡ) §Null%V $ head nodes)
      @ ↑γ.(bag_2۰name۰inv)
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
    | queue : option queue_spmc۰name,
      RET o;
      𝑐𝑜𝑛𝑠𝑢𝑚𝑒𝑟.[consumer_queue] ↦ ((♯) <$> queue : option val) ∗
      queues۰elem γ queue
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer_queue & #Hqueues_elem & Hnodes & Hqueues_ats) HΦ".

    iLöb as "HLöb" forall (nodes).

    wp۰rec.
    destruct nodes as [| node nodes].

    - wp۰pures.

      iMod "HΦ" as "(%vss & Hmodel₁ & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel₁") as "HΦ".

      iSteps.

    - iDestruct (xtchainｰcons' with "Hnodes") as "-#(#Hnode_header & #Hnode_next & #Hnodes)".
      iDestruct (big_sepLｰcons₁ with "Hqueues_ats") as "-#((%queue0 & #Hqueues_at) & #Hqueues_ats)".
      wp۰match.

      wp۰bind (_.{queue})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (queues۰atｰvalid with "Hqueues_auth Hqueues_at") as "#(%descr & %Hdescrs1_lookup & %Hdescr_queue & _)".
      iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model =0 > inv=) & Hdescrs)"; first done.
      wp۰load.
      iSplitR "Hconsumer_queue HΦ". { iFrameSteps. }
      rewrite Hdescr_queue. iIntros "!>".

      destruct o0 as [queue0_ |]; wp۰pures.

      + rewrite Ho0 Hdescr_queue. clear.

        awp۰apply+ (queue_spmc٠popｰspec with "Hqueue0_inv") without "Hconsumer_queue".
        iInv "Hinv" as "(:inv۰inner =2)".
        iDestruct (queues۰atｰvalid with "Hqueues_auth Hqueues_at") as "(%descr & %Hdescrs_lookup & %Hdescr_queue & %Hwss_lookup)".
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
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
          set vss' :=
            <[descriptor۰to_producer descr node := vs]> vss.
          iMod (modelｰupdate vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ"; first iSteps.

          iApply (queuesｰupdate node descr (const vs)) in "Hqueues_auth"; first done.
          set descr' :=
            descriptor۰update_vals descr (const vs).
          iDestruct ("Hdescrs" $! descr' with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iFrameSteps.

          iSplitR "HΦ". { iFrameSteps. }
          iSteps. iExists (Some _). iSteps.

      + wp۰load.
        wp۰apply ("HLöb" $! nodes with "Hconsumer_queue Hnodes [$] HΦ").
  Qed.
  #[local] Lemma bag_2٠pop₁ｰspec γ ι consumer :
    <<<
      bag_2۰inv γ ι ∗
      bag_2۰consumer γ consumer
    | ∀∀ vss,
      bag_2۰model γ vss
    >>>
      bag_2٠pop₁ γ consumer
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          bag_2۰model γ vss
      | Some v =>
          ∃ producer vs,
          ⌜vss !! producer = Some (v :: vs)⌝ ∗
          bag_2۰model γ (<[producer := vs]> vss)
      end
    | RET o;
      bag_2۰consumer γ consumer
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ".

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
      iDestruct (queues۰atｰget with "Hqueues_auth") as "(%descr & %Hdescrs_lookup & #Hqueues_at)"; first done.
      iSteps.
    }

    iSplitR "Hconsumer_queue HΦ". { iFrameSteps. }
    iIntros "{%} !>".

    awp۰apply+ (bag_2٠pop₂ｰspec with "[- HΦ]"); first iFrameSteps.
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vss (:model)".
    iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%o Hmodel₁ !>".
    iExists o. destruct o as [v |]; last iSteps.
    iDestruct "Hmodel₁" as "(%producer & %vs & %Hvss_lookup & Hmodel₁)".
    iSteps.
  Qed.
  Lemma bag_2٠popｰspec γ ι consumer :
    <<<
      bag_2۰inv γ ι ∗
      bag_2۰consumer γ consumer
    | ∀∀ vss,
      bag_2۰model γ vss
    >>>
      bag_2٠pop γ consumer
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          bag_2۰model γ vss
      | Some v =>
          ∃ producer vs,
          ⌜vss !! producer = Some (v :: vs)⌝ ∗
          bag_2۰model γ (<[producer := vs]> vss)
      end
    | RET o;
      bag_2۰consumer γ consumer
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ".

    wp۰rec. wp۰load.
    destruct queue as [queue |].

    - iDestruct "Hqueues_elem" as "(:queues۰elem)".
      awp۰apply+ (queue_spmc٠popｰspec with "Hqueue_inv") without "Hconsumer_queue".
      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (queues۰atｰvalid with "Hqueues_auth Hqueues_at") as "(%descr & %Hdescrs_lookup & %Hdescr_queue & %Hwss_lookup)".
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

        wp۰apply+ (bag_2٠pop₁ｰspec with "[- HΦ] HΦ").
        { iSplitR; iSteps. iExists (Some _). iSteps. }

      + iMod "HΦ" as "(%vss & (:model) & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
        set vss' :=
          <[descriptor۰to_producer descr node := vs]> vss.
        iMod (modelｰupdate vss' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ"; first iSteps.

        iApply (queuesｰupdate node descr (const vs)) in "Hqueues_auth"; first done.
        set descr' :=
          descriptor۰update_vals descr (const vs).
        iDestruct ("Hdescrs" $! descr' with "[Hnode_queue Hqueue_model]") as "Hdescrs"; first iFrameSteps.

        iSplitR "HΦ". { iFrameSteps. }
        iSteps. iExists (Some _). iSteps.

    - wp۰apply+ (bag_2٠pop₁ｰspec with "[- HΦ] HΦ").
      { iSplitR; iSteps. iExists None. iSteps. }
  Qed.
End bag_2۰G.

Require zoo_saturn.bag_2__opaque.

Please opacify.
