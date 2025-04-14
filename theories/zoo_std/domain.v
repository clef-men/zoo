From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list
  fin_maps.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  counter.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  domain__code.
From zoo_std Require Import
  option
  spsc_future
  dynarray_1.
From zoo Require Import
  options.

Implicit Types id : nat.
Implicit Types l : location.
Implicit Types t fn key : val.
Implicit Types keys : gset val.
Implicit Types vs : list (option val).
Implicit Types ws : gmap nat (option val).
Implicit Types ids : gmap val nat.

#[local] Notation "'id'" := (
  in_type "key" 0
)(in custom zoo_proj
).
#[local] Notation "'init'" := (
  in_type "key" 1
)(in custom zoo_proj
).

Definition domain_spawn : val :=
  fun: "fn" =>
    let: "t" := spsc_future_create () in
    Fork (
      let: "local" := dynarray_1_create () in
      SetLocal "local" ;;
      spsc_future_set "t" ("fn" ())
    ) ;;
    "t".

Definition domain_join : val :=
  spsc_future_get.

Definition domain_local_new : val :=
  fun: "fn" =>
    let: "id" := zoo_counter_incr () in
    ("id", "fn").

Definition domain_key_id : val :=
  fun: "key" =>
    "key".<id>.
Definition domain_key_init : val :=
  fun: "key" =>
    "key".<init> ().

Definition domain_local_get : val :=
  fun: "key" =>
    let: "local" := GetLocal in
    let: "id" := domain_key_id "key" in
    dynarray_1_grow "local" ("id" + #1) §None ;;
    match: dynarray_1_get "local" "id" with
    | None =>
        let: "v" := domain_key_init "key" in
        dynarray_1_set "local" "id" "v" ;;
        "v"
    | Some "v" =>
        "v"
    end.

Definition domain_local_set : val :=
  fun: "key" "v" =>
    let: "local" := GetLocal in
    let: "id" := domain_key_id "key" in
    dynarray_1_grow "local" ("id" + #1) §None ;;
    dynarray_1_set "local" "id" ‘Some( "v" ).

Class DomainG Σ `{zoo_G : !ZooG Σ} := {
  #[local] domain_G_future_G :: SpscFutureG Σ ;
  #[local] domain_G_locals_G :: ghost_mapG Σ nat (option val) ;
}.

Definition domain_Σ := #[
  spsc_future_Σ ;
  ghost_mapΣ nat (option val)
].
#[global] Instance subG_domain_Σ Σ `{zoo_G : !ZooG Σ} :
  subG domain_Σ Σ →
  DomainG Σ.
Proof.
  solve_inG.
Qed.

Section domain_G.
  Context `{domain_G : DomainG Σ}.

  Implicit Types Ψ : val → iProp Σ.

  #[local] Definition consistent vs ws :=
    map_oflatten (map_seq 0 vs) = map_oflatten ws.

  #[local] Definition local_auth γ :=
    ghost_map_auth γ 1.
  #[local] Definition local_at :=
    ghost_map_elem.

  Definition domain_model t Ψ : iProp Σ :=
    spsc_future_inv t Ψ ∗
    spsc_future_consumer t.

  #[local] Definition key_id key id : iProp Σ :=
    ∃ fn,
    ⌜key = (#id, fn)%V⌝ ∗
    zoo_counter_at id fn.
  #[local] Instance : CustomIpatFormat "key_id" :=
    "(
      %fn{} &
      %Heq{} &
      #Hcounter_at{}
    )".

  Definition domain_key key Ψ : iProp Σ :=
    ∃ id fn,
    ⌜key = (#id, fn)%V⌝ ∗
    zoo_counter_at id fn ∗
    □ WP fn () {{ Ψ }}.
  #[local] Instance : CustomIpatFormat "key" :=
    "(
      %id &
      %fn{} &
      -> &
      Hcounter_at &
      #Hfn{}
    )".
  Definition domain_key' key : iProp Σ :=
    ∃ Ψ,
    domain_key key Ψ.

  Definition domain_local tid keys : iProp Σ :=
    ∃ l γ vs ws ids,
    tid ↦ₗ□ #l ∗
    meta l (nroot.@"user") γ ∗
    dynarray_1_model #l (option_to_val <$> vs) ∗
    local_auth γ ws ∗
    ⌜dom ids = keys⌝ ∗
    ⌜map_img ids = dom ws⌝ ∗
    ([∗ map] key ↦ id ∈ ids, key_id key id) ∗
    ⌜consistent vs ws⌝.
  #[local] Instance : CustomIpatFormat "local" :=
    "(
      %l &
      %γ &
      %vs &
      %ws &
      %ids &
      #Hlocal &
      #Hl_meta &
      Hl &
      Hlocal_auth &
      %Hids_dom &
      %Hids_img &
      Hids &
      %Hconsistent
    )".

  Definition domain_local_init tid key : iProp Σ :=
    ∃ l γ id,
    tid ↦ₗ□ #l ∗
    meta l (nroot.@"user") γ ∗
    key_id key id ∗
    local_at γ id (DfracOwn 1) None.
  #[local] Instance : CustomIpatFormat "local_init" :=
    "(
      %l{}{_{suff}} &
      %γ{}{_{suff}} &
      %id{} &
      #Hlocal{}{_{suff}} &
      #Hl{}_meta{_{suff}} &
      #Hid{} &
      Hlocal_at{}
    )".

  Definition domain_local_pointsto tid key dq v : iProp Σ :=
    ∃ l γ id,
    tid ↦ₗ□ #l ∗
    meta l (nroot.@"user") γ ∗
    key_id key id ∗
    local_at γ id dq (Some v).
  #[local] Instance : CustomIpatFormat "local_pointsto" :=
    "(
      %l{}{_{suff}} &
      %γ{}{_{suff}} &
      %id{} &
      #Hlocal{}{_{suff}} &
      #Hl{}_meta{_{suff}} &
      #Hid{} &
      Hlocal_at{}
    )".
  Definition domain_local_pointstopred tid key Ψ : iProp Σ :=
      domain_local_init tid key ∗
      domain_key key Ψ
    ∨ ∃ v,
      domain_local_pointsto tid key (DfracOwn 1) v ∗
      Ψ v.
  #[local] Instance : CustomIpatFormat "local_pointstopred" :=
    "[(Hinit & Hkey) | (% & Hlocal_pointsto & HΨ)]".

  #[local] Lemma consistent_app_None vs ws n :
    consistent vs ws →
    consistent (vs ++ replicate n None) ws.
  Proof.
    intros Hconsistent.
    rewrite /consistent map_seq_app map_oflatten_union.
    { apply map_seq_app_disjoint. }
    setoid_rewrite map_oflatten_empty at 2.
    { rewrite right_id //. }
    intros id o (_ & (-> & _)%lookup_replicate)%lookup_map_seq_Some. done.
  Qed.
  #[local] Lemma consistent_lookup_None {vs ws} id o :
    consistent vs ws →
    ws !! id = None →
    vs !! id = Some o →
    o = None.
  Proof.
    destruct o as [v |]; last done.
    intros Hconsistent Hws_lookup%lookup_map_oflatten_None Hvs_lookup%(lookup_map_seq_Some_inv 0)%lookup_map_oflatten_Some_Some.
    simpl in Hvs_lookup. congruence.
  Qed.
  #[local] Lemma consistent_lookup_Some_None {vs ws} id :
    id < length vs →
    consistent vs ws →
    ws !! id = Some None →
    vs !! id = Some None.
  Proof.
    intros (o & Hvs_lookup)%lookup_lt_is_Some Hconsistent Hws_lookup%lookup_map_oflatten_Some_None.
    destruct o as [v |]; last done.
    rewrite (lookup_map_seq_Some_inv 0) /= in Hvs_lookup.
    apply lookup_map_oflatten_Some_Some in Hvs_lookup.
    congruence.
  Qed.
  #[local] Lemma consistent_lookup_Some_Some {vs ws} id v :
    consistent vs ws →
    ws !! id = Some (Some v) →
    vs !! id = Some (Some v).
  Proof.
    intros Hconsistent Hws_lookup%lookup_map_oflatten_Some_Some.
    rewrite -Hconsistent in Hws_lookup.
    apply lookup_map_oflatten_Some_inv in Hws_lookup.
    rewrite lookup_map_seq_Some Nat.sub_0_r in Hws_lookup.
    naive_solver.
  Qed.
  #[local] Lemma consistent_insert {vs ws} id :
    ws !! id = None →
    consistent vs ws →
    consistent vs (<[id := None]> ws).
  Proof.
    intros Hlookup Hconsistent.
    rewrite /consistent map_oflatten_insert //.
  Qed.
  #[local] Lemma consistent_update {vs ws} id w :
    id < length vs →
    consistent vs ws →
    consistent (<[id := Some w]> vs) (<[id := Some w]> ws).
  Proof.
    intros Hid Hconsistent.
    rewrite /consistent map_oflatten_update -insert_map_seq_0 // map_oflatten_update Hconsistent //.
  Qed.

  #[global] Instance domain_local_timeless tid keys :
    Timeless (domain_local tid keys).
  Proof.
    apply _.
  Qed.
  #[global] Instance domain_local_init_timeless tid key :
    Timeless (domain_local_init tid key).
  Proof.
    apply _.
  Qed.
  #[global] Instance domain_local_pointsto_timeless tid key dq v :
    Timeless (domain_local_pointsto tid key dq v).
  Proof.
    apply _.
  Qed.
  #[local] Instance key_id_persistent key id :
    Persistent (key_id key id).
  Proof.
    apply _.
  Qed.
  #[global] Instance domain_key_persistent key Ψ :
    Persistent (domain_key key Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance domain_local_pointsto_persistent tid key v :
    Persistent (domain_local_pointsto tid key DfracDiscarded v).
  Proof.
    apply _.
  Qed.

  #[local] Lemma local_alloc :
    ⊢ |==>
      ∃ γ,
      local_auth γ ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma local_at_valid γ ws id dq v :
    local_auth γ ws -∗
    local_at γ id dq v -∗
    ⌜ws !! id = Some v⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma local_insert {γ ws} id :
    ws !! id = None →
    local_auth γ ws ⊢ |==>
      local_auth γ (<[id := None]> ws) ∗
      local_at γ id (DfracOwn 1) None.
  Proof.
    intros.
    iApply ghost_map_insert; first done.
  Qed.
  #[local] Lemma local_update {γ ws id w} w' :
    local_auth γ ws -∗
    local_at γ id (DfracOwn 1) w ==∗
      local_auth γ (<[id := w']> ws) ∗
      local_at γ id (DfracOwn 1) w'.
  Proof.
    apply ghost_map_update.
  Qed.

  #[local] Lemma key_id_agree key id1 id2 :
    key_id key id1 -∗
    key_id key id2 -∗
    ⌜id1 = id2⌝.
  Proof.
    iIntros "(:key_id =1) (:key_id =2)". simplify.
    iSteps.
  Qed.
  #[local] Lemma key_id_inj key1 id1 key2 id2 :
    key1 ≠ key2 →
    key_id key1 id1 -∗
    key_id key2 id2 -∗
    ⌜id1 ≠ id2⌝.
  Proof.
    iIntros "% (:key_id =1) (:key_id =2) <-". simplify.
    iDestruct (zoo_counter_at_agree with "Hcounter_at1 Hcounter_at2") as %<-. done.
  Qed.

  #[local] Lemma domain_key_to_id key Ψ :
    domain_key key Ψ ⊢
      ∃ id,
      key_id key id.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma domain_key_id_spec key id :
    {{{
      key_id key id
    }}}
      domain_key_id key
    {{{
      RET #id;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma domain_key_init_spec key Ψ :
    {{{
      domain_key key Ψ
    }}}
      domain_key_init key
    {{{ v,
      RET v;
      Ψ v
    }}}.
  Proof.
    iSteps.
  Qed.

  Opaque key_id.

  Lemma domain_local_get_key {tid keys} key Ψ :
    key ∉ keys →
    domain_local tid keys -∗
    domain_key key Ψ ==∗
      domain_local tid (keys ∪ {[key]}) ∗
      domain_local_init tid key.
  Proof.
    iIntros "%Hkey (:local) Hkey".
    iDestruct (domain_key_to_id with "Hkey") as "(%id & #Hid) {Hkey}".
    assert (ids !! key = None) as Hids_lookup.
    { apply not_elem_of_dom. naive_solver. }
    iAssert ⌜id ∉ dom ws⌝%I as %Hws_lookup%not_elem_of_dom.
    { rewrite -Hids_img not_elem_of_map_img.
      iIntros "%key' %Hids_lookup'".
      iDestruct (big_sepM_lookup with "Hids") as "Hid'"; first done.
      iDestruct (key_id_inj with "Hid Hid'") as %?; congruence.
    }
    iMod (local_insert with "Hlocal_auth") as "(Hlocal_auth & Hlocal_at)"; first done.
    iDestruct (big_sepM_insert_2 with "Hid Hids") as "Hids".
    iFrameSteps; iPureIntro.
    { set_solver. }
    { rewrite map_img_insert_notin_L //. set_solver. }
    { apply (consistent_insert id) in Hconsistent; done. }
  Qed.

  #[global] Instance domain_local_pointsto_fractional tid key v :
    Fractional (λ q, domain_local_pointsto tid key (DfracOwn q) v).
  Proof.
    intros q1 q2. iSplit.
    - iIntros "(:local_pointsto)".
      iDestruct "Hlocal_at" as "(Hlocal_at1 & Hlocal_at2)".
      iSplitL "Hlocal_at1"; iFrame "#∗".
    - iIntros "((:local_pointsto =1) & (:local_pointsto =2))".
      iDestruct (thread_pointsto_agree with "Hlocal1 Hlocal2") as %[= <-]. iClear "Hlocal2".
      iDestruct (meta_agree with "Hl1_meta Hl2_meta") as %<-. iClear "Hl2_meta".
      iDestruct (key_id_agree with "Hid1 Hid2") as %<-. iClear "Hid2".
      iCombine "Hlocal_at1 Hlocal_at2" as "Hlocal_at".
      iFrame "#∗".
  Qed.
  #[global] Instance domain_local_pointsto_as_fractional tid key q v :
    AsFractional (domain_local_pointsto tid key (DfracOwn q) v) (λ q, domain_local_pointsto tid key (DfracOwn q) v)%I q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma domain_local_pointsto_valid tid key dq v :
    domain_local_pointsto tid key dq v ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "(:local_pointsto)".
    iApply (ghost_map_elem_valid with "Hlocal_at").
  Qed.
  Lemma domain_local_pointsto_combine tid key dq1 v1 dq2 v2 :
    domain_local_pointsto tid key dq1 v1 -∗
    domain_local_pointsto tid key dq2 v2 -∗
      ⌜v1 = v2⌝ ∗
      domain_local_pointsto tid key (dq1 ⋅ dq2) v1.
  Proof.
    iIntros "(:local_pointsto =1) (:local_pointsto =2)".
    iDestruct (thread_pointsto_agree with "Hlocal1 Hlocal2") as %[= <-]. iClear "Hlocal2".
    iDestruct (meta_agree with "Hl1_meta Hl2_meta") as %<-. iClear "Hl2_meta".
    iDestruct (key_id_agree with "Hid1 Hid2") as %<-. iClear "Hid2".
    iDestruct (ghost_map_elem_combine with "Hlocal_at1 Hlocal_at2") as "(Hlocal_at & %)". simplify.
    iStep. iFrame "#∗".
  Qed.
  Lemma domain_local_pointsto_valid_2 tid key dq1 v1 dq2 v2 :
    domain_local_pointsto tid key dq1 v1 -∗
    domain_local_pointsto tid key dq2 v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (domain_local_pointsto_combine with "H1 H2") as "($ & H)".
    iApply (domain_local_pointsto_valid with "H").
  Qed.
  Lemma domain_local_pointsto_agree tid key dq1 v1 dq2 v2 :
    domain_local_pointsto tid key dq1 v1 -∗
    domain_local_pointsto tid key dq2 v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (domain_local_pointsto_combine with "H1 H2") as "($ & _)".
  Qed.
  Lemma domain_local_pointsto_dfrac_ne tid1 key1 dq1 v1 tid2 key2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    domain_local_pointsto tid1 key1 dq1 v1 -∗
    domain_local_pointsto tid2 key2 dq2 v2 -∗
    ⌜tid1 ≠ tid2 ∨ key1 ≠ key2⌝.
  Proof.
    rewrite -not_and_r. iIntros "% H1 H2" ((-> & ->)).
    iDestruct (domain_local_pointsto_valid_2 with "H1 H2") as %?. naive_solver.
  Qed.
  Lemma domain_local_pointsto_ne tid1 key1 v1 tid2 key2 dq2 v2 :
    domain_local_pointsto tid1 key1 (DfracOwn 1) v1 -∗
    domain_local_pointsto tid2 key2 dq2 v2 -∗
    ⌜tid1 ≠ tid2 ∨ key1 ≠ key2⌝.
  Proof.
    intros.
    iApply domain_local_pointsto_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma domain_local_pointsto_exclusive tid key v1 dq2 v2 :
    domain_local_pointsto tid key (DfracOwn 1) v1 -∗
    domain_local_pointsto tid key dq2 v2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (domain_local_pointsto_ne with "H1 H2") as %?. naive_solver.
  Qed.
  Lemma domain_local_pointsto_persist tid key dq v :
    domain_local_pointsto tid key dq v ⊢ |==>
    domain_local_pointsto tid key DfracDiscarded v.
  Proof.
    iIntros "(:local_pointsto)".
    iMod (ghost_map_elem_persist with "Hlocal_at") as "Hlocal_at".
    iModIntro. iFrame "#∗".
  Qed.

  Lemma domain_spawn_spec Ψ fn :
    {{{
      ∀ tid,
      domain_local tid ∅ -∗
      WP fn () ∶ tid {{ Ψ }}
    }}}
      domain_spawn fn
    {{{ t,
      RET t;
      domain_model t Ψ
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    wp_rec.
    wp_apply (spsc_future_create_spec with "[//]") as (fut) "(#Hfut_inv & Hfut_producer & Hfut_consumer)".
    wp_smart_apply (wp_fork with "[Hfn Hfut_producer]"); last iSteps. iIntros "!> %tid %local Hlocal".
    wp_bind (dynarray_1_create ())%E. iApply wp_thread_id_mono.
    wp_apply (dynarray_1_create_spec' with "[//]") as (l) "(Hl & Hl_meta)".
    wp_smart_apply (wp_set_local with "Hlocal") as "Hlocal".

    iMod (thread_pointsto_persist with "Hlocal") as "#Hlocal".
    iMod local_alloc as "(%γ & Hlocal_auth)".
    iMod (meta_set γ with "Hl_meta") as "#Hl_meta"; first done.

    wp_smart_apply (wp_wand with "(Hfn [Hl Hlocal_auth])") as (res) "HΨ".
    { iExists l, γ, [], ∅, ∅. rewrite big_sepM_empty. iSteps. }
    iApply wp_thread_id_mono.
    wp_apply (spsc_future_set_spec with "[$Hfut_inv $Hfut_producer $HΨ]").
    iSteps.
  Qed.

  Lemma domain_join_spec t Ψ :
    {{{
      domain_model t Ψ
    }}}
      domain_join t
    {{{ v,
      RET v;
      Ψ v
    }}}.
  Proof.
    apply spsc_future_get_spec.
  Qed.

  Lemma domain_local_new_spec {fn} Ψ keys :
    {{{
      □ WP fn () {{ Ψ }}
      (* ([∗ set] key ∈ keys, domain_key' key) *)
    }}}
      domain_local_new fn
    {{{ key,
      RET key;
      domain_key key Ψ
      (* ⌜set_Forall (.≠ key) keys⌝ *)
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".

    (* iAssert ( *)
    (*   [∗ set] key ∈ keys, *)
    (*     ∃ id fn, *)
    (*     ⌜key = (#id, fn)%V⌝ ∗ *)
    (*     zoo_counter_at id fn *)
    (* )%I with "[Hkeys]" as "Hkeys". *)
    (* { iApply (big_sepS_impl with "Hkeys"). iIntros "!> %key %Hkey (%Ψ' & (:key ='))". *)
    (*   iSteps. *)
    (* } *)
    (* iAssert ( *)
    (*   ∃ ids, *)
    (*   [∗ map] key ↦ id ∈ ids, *)
    (*     ∃ fn, *)
    (*     ⌜key = (#id, fn)%V⌝ ∗ *)
    (*     zoo_counter_at id fn *)
    (* )%I with "[Hkeys]" as "(%ids & #Hids)". *)
    (* { admit. *)
    (* } *)

    wp_rec.
    wp_apply (zoo_counter_incr_spec ∅ fn) as (id) "(Hid & %_)".
    { rewrite big_sepS_empty //. }
    iSteps.
  Qed.

  Lemma domain_local_get_spec_init keys key Ψ tid :
    {{{
      domain_local tid keys ∗
      domain_key key Ψ ∗
      domain_local_init tid key
    }}}
      domain_local_get key ∶ tid
    {{{ v,
      RET v;
      domain_local_pointsto tid key (DfracOwn 1) v ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:local) & #Hkey & (:local_init suff=)) HΦ".
    iDestruct (thread_pointsto_agree with "Hlocal Hlocal_") as %[= <-]. iClear "Hlocal_".
    iDestruct (meta_agree with "Hl_meta Hl_meta_") as %<-. iClear "Hl_meta_".
    iDestruct (local_at_valid with "Hlocal_auth Hlocal_at") as %Hws_lookup.

    wp_rec.
    wp_apply (wp_get_local with "Hlocal") as "_".
    iApply wp_thread_id_mono.
    wp_smart_apply (domain_key_id_spec with "Hid") as "_".
    wp_smart_apply (dynarray_1_grow_spec with "Hl") as "Hl"; first lia.
    wp_smart_apply (dynarray_1_get_spec _ _ _ None with "Hl") as "Hl".
    { lia. }
    { rewrite Nat2Z.id -(fmap_replicate option_to_val _ None) -fmap_app list_lookup_fmap_Some.
      exists None. split; last done.
      eapply consistent_lookup_Some_None; last done.
      { simpl_length. lia. }
      apply consistent_app_None. done.
    }
    wp_smart_apply (domain_key_init_spec with "Hkey") as (v) "HΨ".
    iMod (local_update (Some v) with "Hlocal_auth Hlocal_at") as "(Hlocal_auth & Hlocal_at)".
    wp_smart_apply (dynarray_1_set_spec with "Hl") as "Hl".
    { simpl_length. lia. }
    iSteps.
  Qed.
  Lemma domain_local_get_spec_pointsto keys key dq v tid :
    {{{
      domain_local tid keys ∗
      domain_local_pointsto tid key dq v
    }}}
      domain_local_get key ∶ tid
    {{{
      RET v;
      domain_local_pointsto tid key dq v
    }}}.
  Proof.
    iIntros "%Φ ((:local) & (:local_pointsto suff=)) HΦ".
    iDestruct (thread_pointsto_agree with "Hlocal Hlocal_") as %[= <-]. iClear "Hlocal_".
    iDestruct (meta_agree with "Hl_meta Hl_meta_") as %<-. iClear "Hl_meta_".
    iDestruct (local_at_valid with "Hlocal_auth Hlocal_at") as %Hws_lookup.

    wp_rec.
    wp_apply (wp_get_local with "Hlocal") as "_".
    iApply wp_thread_id_mono.
    wp_smart_apply (domain_key_id_spec with "Hid") as "_".
    wp_smart_apply (dynarray_1_grow_spec with "Hl") as "Hl"; first lia.
    wp_smart_apply (dynarray_1_get_spec _ _ _ (Some v) with "Hl") as "Hl".
    { lia. }
    { rewrite Nat2Z.id -(fmap_replicate option_to_val _ None) -fmap_app list_lookup_fmap_Some.
      exists (Some v). split; last done.
      eapply consistent_lookup_Some_Some; last done.
      apply consistent_app_None. done.
    }
    iSteps.
  Qed.
  Lemma domain_local_get_spec_pointstopred keys key Ψ tid :
    {{{
      domain_local tid keys ∗
      domain_local_pointstopred tid key Ψ
    }}}
      domain_local_get key ∶ tid
    {{{ v,
      RET v;
      domain_local_pointsto tid key (DfracOwn 1) v ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (Hlocal & (:local_pointstopred)) HΦ".
    - wp_apply (domain_local_get_spec_init with "[$Hlocal $Hkey $Hinit] HΦ").
    - wp_apply (domain_local_get_spec_pointsto with "[$Hlocal $Hlocal_pointsto]").
      iSteps.
  Qed.

  Lemma domain_local_set_spec_init keys key Ψ v tid :
    {{{
      domain_local tid keys ∗
      domain_key key Ψ ∗
      domain_local_init tid key
    }}}
      domain_local_set key v ∶ tid
    {{{
      RET ();
      domain_local_pointsto tid key (DfracOwn 1) v
    }}}.
  Proof.
    iIntros "%Φ ((:local) & #Hkey & (:local_init suff=)) HΦ".
    iDestruct (thread_pointsto_agree with "Hlocal Hlocal_") as %[= <-]. iClear "Hlocal_".
    iDestruct (meta_agree with "Hl_meta Hl_meta_") as %<-. iClear "Hl_meta_".
    iDestruct (local_at_valid with "Hlocal_auth Hlocal_at") as %Hws_lookup.

    wp_rec.
    wp_smart_apply (wp_get_local with "Hlocal") as "_".
    iApply wp_thread_id_mono.
    wp_smart_apply (domain_key_id_spec with "Hid") as "_".
    wp_smart_apply (dynarray_1_grow_spec with "Hl") as "Hl"; first lia.
    iMod (local_update (Some v) with "Hlocal_auth Hlocal_at") as "(Hlocal_auth & Hlocal_at)".
    wp_smart_apply (dynarray_1_set_spec with "Hl") as "Hl".
    { simpl_length. lia. }
    iSteps.
  Qed.
  Lemma domain_local_set_spec_pointsto keys key w v tid :
    {{{
      domain_local tid keys ∗
      domain_local_pointsto tid key (DfracOwn 1) w
    }}}
      domain_local_set key v ∶ tid
    {{{
      RET ();
      domain_local_pointsto tid key (DfracOwn 1) v
    }}}.
  Proof.
    iIntros "%Φ ((:local) & (:local_pointsto suff=)) HΦ".
    iDestruct (thread_pointsto_agree with "Hlocal Hlocal_") as %[= <-]. iClear "Hlocal_".
    iDestruct (meta_agree with "Hl_meta Hl_meta_") as %<-. iClear "Hl_meta_".
    iDestruct (local_at_valid with "Hlocal_auth Hlocal_at") as %Hws_lookup.

    wp_rec.
    wp_smart_apply (wp_get_local with "Hlocal") as "_".
    iApply wp_thread_id_mono.
    wp_smart_apply (domain_key_id_spec with "Hid") as "_".
    wp_smart_apply (dynarray_1_grow_spec with "Hl") as "Hl"; first lia.
    iMod (local_update (Some v) with "Hlocal_auth Hlocal_at") as "(Hlocal_auth & Hlocal_at)".
    wp_smart_apply (dynarray_1_set_spec with "Hl") as "Hl".
    { simpl_length. lia. }
    iSteps.
  Qed.
  Lemma domain_local_set_spec_pointstopred keys key Ψ v tid :
    {{{
      domain_local tid keys ∗
      domain_local_pointstopred tid key Ψ
    }}}
      domain_local_set key v ∶ tid
    {{{
      RET ();
      domain_local_pointsto tid key (DfracOwn 1) v
    }}}.
  Proof.
    iIntros "%Φ (Hlocal & (:local_pointstopred)) HΦ".
    - wp_apply (domain_local_set_spec_init with "[$Hlocal $Hkey $Hinit] HΦ").
    - wp_apply (domain_local_set_spec_pointsto with "[$Hlocal $Hlocal_pointsto] HΦ").
  Qed.
End domain_G.

Axiom domain_yield_spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  ▷ Φ ()%V ⊢
  WP domain_yield () {{ Φ }}.

Axiom domain_self_index_spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  (∀ (i : nat), ▷ Φ #i) ⊢
  WP domain_self_index () {{ Φ }}.

Axiom domain_recommended_domain_count_spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  (∀ (i : nat), ▷ Φ #i) ⊢
  WP domain_recommended_domain_count () {{ Φ }}.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[global] Instance domain_yield_diaspec :
    DIASPEC
    {{
      True
    }}
      domain_yield ()%V
    {{
      RET ();
      True
    }}.
  Proof.
    iSteps.
    wp_apply domain_yield_spec.
    iSteps.
  Qed.

  #[global] Instance domain_self_index_diaspec :
    DIASPEC
    {{
      True
    }}
      domain_self_index ()%V
    {{ (i : nat),
      RET #i;
      True
    }}.
  Proof.
    iSteps.
    wp_apply domain_self_index_spec.
    iSteps.
  Qed.

  #[global] Instance domain_recommended_domain_count_diaspec :
    DIASPEC
    {{
      True
    }}
      domain_recommended_domain_count ()%V
    {{ (i : nat),
      RET #i;
      True
    }}.
  Proof.
    iSteps.
    wp_apply domain_recommended_domain_count_spec.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque domain_spawn.
#[global] Opaque domain_join.
#[global] Opaque domain_local_new.
#[global] Opaque domain_local_get.
#[global] Opaque domain_local_set.

#[global] Opaque domain_model.
#[global] Opaque domain_key.
#[global] Opaque domain_local.
#[global] Opaque domain_local_init.
#[global] Opaque domain_local_pointsto.
