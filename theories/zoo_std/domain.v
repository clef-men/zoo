Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.common.fin_maps.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Import zoo.program_logic.counter.
Require Export zoo_std.domain__code.
Require Import zoo_std.option.
Require Import zoo_std.ivar_2.
Require Import zoo_std.dynarray_1.
Require Import zoo.options.

Implicit Type id : nat.
Implicit Type l : location.
Implicit Type t fn key : val.
Implicit Type vs : list (option val).
Implicit Type ws : gmap nat (option val).
Implicit Type ids : gmap val nat.

#[local] Notation "'id'" := (
  in_type "key" 0
)(in custom zoo_proj
).
#[local] Notation "'init'" := (
  in_type "key" 1
)(in custom zoo_proj
).

Definition domain٠spawn : val :=
  fun: "fn" =>
    let: "t" := ivar_2٠create () in
    Fork (
      let: "local" := dynarray_1٠create () in
      SetLocal "local" ;;
      ivar_2٠set "t" ("fn" ())
    ) ;;
    "t".

Definition domain٠join : val :=
  ivar_2٠get.

Definition domain٠local_new : val :=
  fun: "fn" =>
    let: "id" := zoo_counter٠incr () in
    ("id", "fn").

Definition domain٠key۰id : val :=
  fun: "key" =>
    "key".<id>.
Definition domain٠key_init : val :=
  fun: "key" =>
    "key".<init> ().

Definition domain٠local_get : val :=
  fun: "key" =>
    let: "local" := GetLocal in
    let: "id" := domain٠key۰id "key" in
    dynarray_1٠grow "local" ("id" + 1) §None ;;
    match: dynarray_1٠get "local" "id" with
    | None =>
        let: "v" := domain٠key_init "key" in
        dynarray_1٠set "local" "id" ‘Some( "v" ) ;;
        "v"
    | Some "v" =>
        "v"
    end.

Definition domain٠local_set : val :=
  fun: "key" "v" =>
    let: "local" := GetLocal in
    let: "id" := domain٠key۰id "key" in
    dynarray_1٠grow "local" ("id" + 1) §None ;;
    dynarray_1٠set "local" "id" ‘Some( "v" ).

Class DomainG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] domain۰G۰ivar۰G :: Ivar2G Σ
  ; #[local] domain۰G۰locals۰G :: ghost_mapG Σ nat (option val)
  }.

Definition domain۰Σ :=
  #[ivar_2۰Σ
  ; ghost_mapΣ nat (option val)
  ].
#[global] Instance subG𑁒domain۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG domain۰Σ Σ →
  DomainG Σ.
Proof.
  solve_inG.
Qed.

Section consistent.
  #[local] Definition consistent vs ws :=
    map۰oflatten (map_seq 0 vs) = map۰oflatten ws.

  #[local] Lemma consistent𑁒app𑁒None vs ws n :
    consistent vs ws →
    consistent (vs ++ replicate n None) ws.
  Proof.
    intros Hconsistent.
    rewrite /consistent map_seq_app map۰oflatten𑁒union.
    { apply map_seq_app_disjoint. }
    setoid_rewrite map۰oflatten𑁒empty at 2.
    { rewrite right_id //. }
    intros id o (_ & (-> & _)%lookup_replicate)%lookup_map_seq_Some. done.
  Qed.
  #[local] Lemma consistent𑁒lookup𑁒None {vs ws} id o :
    consistent vs ws →
    ws !! id = None →
    vs !! id = Some o →
    o = None.
  Proof.
    destruct o as [v |]; last done.
    intros Hconsistent Hws_lookup%lookup𑁒map۰oflatten𑁒None Hvs_lookup%(lookup_map_seq_Some_inv 0)%lookup𑁒map۰oflatten𑁒Some𑁒Some.
    simpl in Hvs_lookup. congruence.
  Qed.
  #[local] Lemma consistent𑁒lookup𑁒Some𑁒None {vs ws} id :
    id < length vs →
    consistent vs ws →
    ws !! id = Some None →
    vs !! id = Some None.
  Proof.
    intros (o & Hvs_lookup)%lookup_lt_is_Some Hconsistent Hws_lookup%lookup𑁒map۰oflatten𑁒Some𑁒None.
    destruct o as [v |]; last done.
    rewrite (lookup_map_seq_Some_inv 0) /= in Hvs_lookup.
    apply lookup𑁒map۰oflatten𑁒Some𑁒Some in Hvs_lookup.
    congruence.
  Qed.
  #[local] Lemma consistent𑁒lookup𑁒Some𑁒Some {vs ws} id v :
    consistent vs ws →
    ws !! id = Some (Some v) →
    vs !! id = Some (Some v).
  Proof.
    intros Hconsistent Hws_lookup%lookup𑁒map۰oflatten𑁒Some𑁒Some.
    rewrite -Hconsistent in Hws_lookup.
    apply lookup𑁒map۰oflatten𑁒Some𑁒inv in Hws_lookup.
    rewrite lookup_map_seq_Some Nat.sub_0_r in Hws_lookup.
    naive_solver.
  Qed.
  #[local] Lemma consistent𑁒insert {vs ws} id :
    ws !! id = None →
    consistent vs ws →
    consistent vs (<[id := None]> ws).
  Proof.
    intros Hlookup Hconsistent.
    rewrite /consistent map۰oflatten𑁒insert //.
  Qed.
  #[local] Lemma consistent𑁒update {vs ws} id w :
    id < length vs →
    consistent vs ws →
    consistent (<[id := Some w]> vs) (<[id := Some w]> ws).
  Proof.
    intros Hid Hconsistent.
    rewrite /consistent map۰oflatten𑁒update -insert_map_seq_0 // map۰oflatten𑁒update Hconsistent //.
  Qed.
End consistent.

Opaque consistent.

Section domain۰G.
  Context `{domain۰G : DomainG Σ}.

  Implicit Type Ψ : val → iProp Σ.

  #[local] Definition local۰auth γ :=
    ghost_map_auth γ 1.
  #[local] Definition local۰at :=
    ghost_map_elem.

  Definition domain۰model t Ψ : iProp Σ :=
    ivar_2۰inv t Ψ (λ _, True)%I ∗
    ivar_2۰consumer t Ψ.
  #[local] Instance : CustomIpat "model" :=
    " ( #Hivar_inv
      & Hivar_consumer
      )
    ".

  #[local] Definition key۰id key id : iProp Σ :=
    ∃ fn,
    ⌜key = (#id, fn)%V⌝ ∗
    zoo_counter۰at id fn.
  #[local] Instance : CustomIpat "key۰id" :=
    " ( %fn{}
      & %Heq{}
      & #Hcounter_at{}
      )
    ".

  Definition domain۰key key Ψ : iProp Σ :=
    ∃ id fn,
    ⌜key = (#id, fn)%V⌝ ∗
    zoo_counter۰at id fn ∗
    □ WP fn () {{ Ψ }}.
  #[local] Instance : CustomIpat "key" :=
    " ( %id
      & %fn{}
      & ->
      & Hcounter_at
      & #Hfn{}
      )
    ".
  Definition domain۰key' key : iProp Σ :=
    ∃ Ψ,
    domain۰key key Ψ.

  Definition domain۰local tid keys : iProp Σ :=
    ∃ l γ vs ws ids,
    tid ↦ₗ□ #l ∗
    l ↪[nroot.@"user"] γ ∗
    dynarray_1۰model #l (option۰to_val <$> vs) ∗
    local۰auth γ ws ∗
    ⌜dom ids = keys⌝ ∗
    ⌜map_img ids = dom ws⌝ ∗
    ([∗ map] key ↦ id ∈ ids, key۰id key id) ∗
    ⌜consistent vs ws⌝.
  #[local] Instance : CustomIpat "local" :=
    " ( %l
      & %γ
      & %vs
      & %ws
      & %ids
      & #Hlocal
      & #Hl_meta
      & Hl
      & Hlocal_auth
      & %Hids_dom
      & %Hids_img
      & Hids
      & %Hconsistent
      )
    ".

  Definition domain۰local_init tid key : iProp Σ :=
    ∃ l γ id,
    tid ↦ₗ□ #l ∗
    l ↪[nroot.@"user"] γ ∗
    key۰id key id ∗
    local۰at γ id (DfracOwn 1) None.
  #[local] Instance : CustomIpat "local_init" :=
    " ( %l{}{_{suff}}
      & %γ{}{_{suff}}
      & %id{}
      & #Hlocal{}{_{suff}}
      & #Hl{}_meta{_{suff}}
      & #Hid{}
      & Hlocal_at{}
      )
    ".

  Definition domain۰local_pointsto tid key dq v : iProp Σ :=
    ∃ l γ id,
    tid ↦ₗ□ #l ∗
    l ↪[nroot.@"user"] γ ∗
    key۰id key id ∗
    local۰at γ id dq (Some v).
  #[local] Instance : CustomIpat "local_pointsto" :=
    " ( %l{}{_{suff}}
      & %γ{}{_{suff}}
      & %id{}
      & #Hlocal{}{_{suff}}
      & #Hl{}_meta{_{suff}}
      & #Hid{}
      & Hlocal_at{}
      )
    ".
  Definition domain۰local_pointstopred tid key Ψ : iProp Σ :=
      domain۰local_init tid key ∗
      domain۰key key Ψ
    ∨ ∃ v,
      domain۰local_pointsto tid key (DfracOwn 1) v ∗
      Ψ v.
  #[local] Instance : CustomIpat "local_pointstopred" :=
    " [ ( Hinit
        & Hkey
        )
      | ( %
        & Hlocal_pointsto
        & HΨ
        )
      ]
    ".

  #[global] Instance domain۰local𑁒timeless tid keys :
    Timeless (domain۰local tid keys).
  Proof.
    apply _.
  Qed.
  #[global] Instance domain۰local_init𑁒timeless tid key :
    Timeless (domain۰local_init tid key).
  Proof.
    apply _.
  Qed.
  #[global] Instance domain۰local_pointsto𑁒timeless tid key dq v :
    Timeless (domain۰local_pointsto tid key dq v).
  Proof.
    apply _.
  Qed.

  #[local] Instance key۰id𑁒persistent key id :
    Persistent (key۰id key id).
  Proof.
    apply _.
  Qed.
  #[global] Instance domain۰key𑁒persistent key Ψ :
    Persistent (domain۰key key Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance domain۰local_pointsto𑁒persistent tid key v :
    Persistent (domain۰local_pointsto tid key DfracDiscarded v).
  Proof.
    apply _.
  Qed.

  #[local] Lemma local𑁒alloc :
    ⊢ |==>
      ∃ γ,
      local۰auth γ ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma local۰at𑁒valid γ ws id dq v :
    local۰auth γ ws -∗
    local۰at γ id dq v -∗
    ⌜ws !! id = Some v⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma local𑁒insert {γ ws} id :
    ws !! id = None →
    local۰auth γ ws ⊢ |==>
      local۰auth γ (<[id := None]> ws) ∗
      local۰at γ id (DfracOwn 1) None.
  Proof.
    intros.
    iApply ghost_map_insert; first done.
  Qed.
  #[local] Lemma local𑁒update {γ ws id w} w' :
    local۰auth γ ws -∗
    local۰at γ id (DfracOwn 1) w ==∗
      local۰auth γ (<[id := w']> ws) ∗
      local۰at γ id (DfracOwn 1) w'.
  Proof.
    apply ghost_map_update.
  Qed.

  #[local] Lemma key۰id𑁒agree key id1 id2 :
    key۰id key id1 -∗
    key۰id key id2 -∗
    ⌜id1 = id2⌝.
  Proof.
    iIntros "(:key۰id =1) (:key۰id =2)". simplify.
    iSteps.
  Qed.
  #[local] Lemma key۰id𑁒inj key1 id1 key2 id2 :
    key1 ≠ key2 →
    key۰id key1 id1 -∗
    key۰id key2 id2 -∗
    ⌜id1 ≠ id2⌝.
  Proof.
    iIntros "% (:key۰id =1) (:key۰id =2) <-". simplify.
    iDestruct (zoo_counter۰at𑁒agree with "Hcounter_at1 Hcounter_at2") as %<-. done.
  Qed.

  #[local] Lemma domain۰key𑁒to𑁒id key Ψ :
    domain۰key key Ψ ⊢
      ∃ id,
      key۰id key id.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma domain٠key۰id𑁒spec key id :
    {{{
      key۰id key id
    }}}
      domain٠key۰id key
    {{{
      RET #id;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma domain٠key_init𑁒spec key Ψ :
    {{{
      domain۰key key Ψ
    }}}
      domain٠key_init key
    {{{
      v
    , RET v;
      Ψ v
    }}}.
  Proof.
    iSteps.
  Qed.

  Opaque key۰id.

  Lemma domain۰local𑁒get𑁒key {tid keys} key Ψ :
    key ∉ keys →
    domain۰local tid keys -∗
    domain۰key key Ψ ==∗
      domain۰local tid (keys ∪ {[key]}) ∗
      domain۰local_init tid key.
  Proof.
    iIntros "%Hkey (:local) Hkey".
    iDestruct (domain۰key𑁒to𑁒id with "Hkey") as "(%id & #Hid) {Hkey}".
    assert (ids !! key = None) as Hids_lookup.
    { apply not_elem_of_dom. naive_solver. }
    iAssert ⌜id ∉ dom ws⌝%I as %Hws_lookup%not_elem_of_dom.
    { rewrite -Hids_img not_elem_of_map_img.
      iIntros "%key' %Hids_lookup'".
      iDestruct (big_sepM_lookup with "Hids") as "Hid'"; first done.
      iDestruct (key۰id𑁒inj with "Hid Hid'") as %?; congruence.
    }
    iMod (local𑁒insert with "Hlocal_auth") as "(Hlocal_auth & Hlocal_at)"; first done.
    iDestruct (big_sepM_insert_2 with "Hid Hids") as "Hids".
    iFrameSteps; iPureIntro.
    { set_solver. }
    { rewrite map_img_insert_notin_L //. set_solver. }
    { apply (consistent𑁒insert id) in Hconsistent; done. }
  Qed.

  #[global] Instance domain۰local_pointsto𑁒fractional tid key v :
    Fractional (λ q, domain۰local_pointsto tid key (DfracOwn q) v).
  Proof.
    intros q1 q2. iSplit.
    - iIntros "(:local_pointsto)".
      iDestruct "Hlocal_at" as "(Hlocal_at1 & Hlocal_at2)".
      iSplitL "Hlocal_at1"; iFrame "#∗".
    - iIntros "((:local_pointsto =1) & (:local_pointsto =2))".
      iDestruct (local_pointsto𑁒agree with "Hlocal1 Hlocal2") as %[= <-]. iClear "Hlocal2".
      iDestruct (meta𑁒agree with "Hl1_meta Hl2_meta") as %<-. iClear "Hl2_meta".
      iDestruct (key۰id𑁒agree with "Hid1 Hid2") as %<-. iClear "Hid2".
      iCombine "Hlocal_at1 Hlocal_at2" as "Hlocal_at".
      iFrame "#∗".
  Qed.
  #[global] Instance domain۰local_pointsto𑁒as_fractional tid key q v :
    AsFractional (domain۰local_pointsto tid key (DfracOwn q) v) (λ q, domain۰local_pointsto tid key (DfracOwn q) v)%I q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma domain۰local_pointsto𑁒valid tid key dq v :
    domain۰local_pointsto tid key dq v ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "(:local_pointsto)".
    iApply (ghost_map_elem_valid with "Hlocal_at").
  Qed.
  Lemma domain۰local_pointsto𑁒combine tid key dq1 v1 dq2 v2 :
    domain۰local_pointsto tid key dq1 v1 -∗
    domain۰local_pointsto tid key dq2 v2 -∗
      ⌜v1 = v2⌝ ∗
      domain۰local_pointsto tid key (dq1 ⋅ dq2) v1.
  Proof.
    iIntros "(:local_pointsto =1) (:local_pointsto =2)".
    iDestruct (local_pointsto𑁒agree with "Hlocal1 Hlocal2") as %[= <-]. iClear "Hlocal2".
    iDestruct (meta𑁒agree with "Hl1_meta Hl2_meta") as %<-. iClear "Hl2_meta".
    iDestruct (key۰id𑁒agree with "Hid1 Hid2") as %<-. iClear "Hid2".
    iDestruct (ghost_map_elem_combine with "Hlocal_at1 Hlocal_at2") as "(Hlocal_at & %)". simplify.
    iStep. iFrame "#∗".
  Qed.
  Lemma domain۰local_pointsto𑁒valid𑁒2 tid key dq1 v1 dq2 v2 :
    domain۰local_pointsto tid key dq1 v1 -∗
    domain۰local_pointsto tid key dq2 v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (domain۰local_pointsto𑁒combine with "H1 H2") as "($ & H)".
    iApply (domain۰local_pointsto𑁒valid with "H").
  Qed.
  Lemma domain۰local_pointsto𑁒agree tid key dq1 v1 dq2 v2 :
    domain۰local_pointsto tid key dq1 v1 -∗
    domain۰local_pointsto tid key dq2 v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (domain۰local_pointsto𑁒combine with "H1 H2") as "($ & _)".
  Qed.
  Lemma domain۰local_pointsto𑁒dfrac𑁒ne tid1 key1 dq1 v1 tid2 key2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    domain۰local_pointsto tid1 key1 dq1 v1 -∗
    domain۰local_pointsto tid2 key2 dq2 v2 -∗
    ⌜tid1 ≠ tid2 ∨ key1 ≠ key2⌝.
  Proof.
    rewrite -not_and_r. iIntros "% H1 H2" ((-> & ->)).
    iDestruct (domain۰local_pointsto𑁒valid𑁒2 with "H1 H2") as %?. naive_solver.
  Qed.
  Lemma domain۰local_pointsto𑁒ne tid1 key1 v1 tid2 key2 dq2 v2 :
    domain۰local_pointsto tid1 key1 (DfracOwn 1) v1 -∗
    domain۰local_pointsto tid2 key2 dq2 v2 -∗
    ⌜tid1 ≠ tid2 ∨ key1 ≠ key2⌝.
  Proof.
    intros.
    iApply domain۰local_pointsto𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma domain۰local_pointsto𑁒exclusive tid key v1 dq2 v2 :
    domain۰local_pointsto tid key (DfracOwn 1) v1 -∗
    domain۰local_pointsto tid key dq2 v2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (domain۰local_pointsto𑁒ne with "H1 H2") as %?. naive_solver.
  Qed.
  Lemma domain۰local_pointsto𑁒persist tid key dq v :
    domain۰local_pointsto tid key dq v ⊢ |==>
    domain۰local_pointsto tid key DfracDiscarded v.
  Proof.
    iIntros "(:local_pointsto)".
    iMod (ghost_map_elem_persist with "Hlocal_at") as "Hlocal_at".
    iModIntro. iFrame "#∗".
  Qed.

  Lemma domain٠spawn𑁒spec Ψ fn :
    {{{
      ∀ tid,
      domain۰local tid ∅ -∗
      WP fn () ∶ tid {{ Ψ }}
    }}}
      domain٠spawn fn
    {{{
      t
    , RET t;
      domain۰model t Ψ
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    wp۰rec.
    wp۰apply (ivar_2٠create𑁒spec with "[//]") as (ivar) "(#Hivar_inv & Hivar_producer & Hivar_consumer)".
    wp۰apply+ (wp𑁒fork with "[Hfn Hivar_producer]"); last iSteps. iIntros "!> %tid %local Hlocal".
    wp۰bind (dynarray_1٠create ())%E. iApply wp𑁒thread_id_mono.
    wp۰apply (dynarray_1٠create𑁒spec' with "[//]") as (l) "(Hl & Hl_meta)".
    wp۰apply+ (wp𑁒set_local with "Hlocal") as "Hlocal".

    iMod (local_pointsto𑁒persist with "Hlocal") as "#Hlocal".
    iMod local𑁒alloc as "(%γ & Hlocal_auth)".
    iMod (meta𑁒set γ with "Hl_meta") as "#Hl_meta"; first done.

    wp۰apply+ (wp𑁒wand with "(Hfn [Hl Hlocal_auth])") as (res) "HΨ".
    { iExists l, γ, [], ∅, ∅. rewrite big_sepM_empty. iSteps. }
    iApply wp𑁒thread_id_mono.
    wp۰apply (ivar_2٠set𑁒spec with "[$Hivar_inv $Hivar_producer $HΨ //]").
    iSteps.
  Qed.

  Lemma domain٠join𑁒spec t Ψ :
    {{{
      domain۰model t Ψ
    }}}
      domain٠join t
    {{{
      v
    , RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    iApply wp𑁒fupd.
    wp۰apply (ivar_2٠get𑁒spec with "Hivar_inv") as (v) "(H£ & Hivar_result & Hivar_synchronized)".
    iMod (ivar_2𑁒inv𑁒result𑁒consumer' with "H£ Hivar_inv Hivar_result Hivar_synchronized Hivar_consumer") as "(HΨ & _)".
    iSteps.
  Qed.

  Lemma domain٠local_new𑁒spec {fn} Ψ keys :
    {{{
      □ WP fn () {{ Ψ }} ∗
      [∗ list] key ∈ keys, domain۰key' key
    }}}
      domain٠local_new fn
    {{{
      key
    , RET key;
      domain۰key key Ψ ∗
      ⌜Forall (.≠ key) keys⌝
    }}}.
  Proof.
    iIntros "%Φ (#Hfn & Hkeys) HΦ".

    iAssert (
      [∗ list] key ∈ keys,
        ∃ id,
        ( ∃ fn,
          ⌜key = (#id, fn)%V⌝
        ) ∗
        ( ∃ fn,
          zoo_counter۰at id fn
        )
    )%I with "[Hkeys]" as "Hkeys".
    { iApply (big_sepL_impl with "Hkeys").
      iSteps.
    }
    iDestruct (big_sepL𑁒exists with "Hkeys") as "(%ids & % & Hkeys)".
    iDestruct (big_sepL2_sep with "Hkeys") as "(Hkeys & Hids)".
    iDestruct (big_sepL2_const_sepL_r with "Hids") as "(_ & Hids)".

    wp۰rec.
    wp۰apply (zoo_counter٠incr𑁒spec ids fn with "Hids") as (id) "(Hid & %Hids)".
    iSteps.
    rewrite Forall_lookup. iIntros "%i %key %Hkeys_lookup ->".
    iDestruct (big_sepL2_lookup_l with "Hkeys") as "(%id' & %Hids_lookup & %fn' & %)"; first done. simplify.
    eapply Forall_lookup_1 in Hids; done.
  Qed.

  Lemma domain٠local_get𑁒spec𑁒init keys key Ψ tid :
    {{{
      domain۰local tid keys ∗
      domain۰key key Ψ ∗
      domain۰local_init tid key
    }}}
      domain٠local_get key ∶ tid
    {{{
      v
    , RET v;
      domain۰local tid keys ∗
      domain۰local_pointsto tid key (DfracOwn 1) v ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:local) & #Hkey & (:local_init suff=)) HΦ".
    iDestruct (local_pointsto𑁒agree with "Hlocal Hlocal_") as %[= <-]. iClear "Hlocal_".
    iDestruct (meta𑁒agree with "Hl_meta Hl_meta_") as %<-. iClear "Hl_meta_".
    iDestruct (local۰at𑁒valid with "Hlocal_auth Hlocal_at") as %Hws_lookup.

    wp۰rec.
    wp۰apply (wp𑁒get_local with "Hlocal") as "_".
    iApply wp𑁒thread_id_mono.
    wp۰apply+ (domain٠key۰id𑁒spec with "Hid") as "_".
    wp۰apply+ (dynarray_1٠grow𑁒spec with "Hl") as "Hl"; first lia.

    iEval (simpl_length) in "Hl".
    iEval (rewrite -(fmap_replicate option۰to_val _ None) -fmap_app) in "Hl".

    wp۰apply+ (dynarray_1٠get𑁒spec _ _ _ None with "Hl") as "Hl".
    { lia. }
    { rewrite Nat2Z.id list_lookup_fmap_Some.
      exists None. split; first done.
      eapply consistent𑁒lookup𑁒Some𑁒None; last done.
      { simpl_length. lia. }
      apply consistent𑁒app𑁒None. done.
    }
    wp۰apply+ (domain٠key_init𑁒spec with "Hkey") as (v) "HΨ".
    iMod (local𑁒update (Some v) with "Hlocal_auth Hlocal_at") as "(Hlocal_auth & Hlocal_at)".
    wp۰apply+ (dynarray_1٠set𑁒spec with "Hl") as "Hl".
    { simpl_length. lia. }
    wp۰pures.

    iApply "HΦ".
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ (Some _)).
    iFrameSteps; iPureIntro.
    { rewrite dom_insert_lookup_L //. }
    { apply consistent𑁒update.
      { simpl_length. lia. }
      { apply consistent𑁒app𑁒None. done. }
    }
  Qed.
  Lemma domain٠local_get𑁒spec𑁒pointsto keys key dq v tid :
    {{{
      domain۰local tid keys ∗
      domain۰local_pointsto tid key dq v
    }}}
      domain٠local_get key ∶ tid
    {{{
      RET v;
      domain۰local tid keys ∗
      domain۰local_pointsto tid key dq v
    }}}.
  Proof.
    iIntros "%Φ ((:local) & (:local_pointsto suff=)) HΦ".
    iDestruct (local_pointsto𑁒agree with "Hlocal Hlocal_") as %[= <-]. iClear "Hlocal_".
    iDestruct (meta𑁒agree with "Hl_meta Hl_meta_") as %<-. iClear "Hl_meta_".
    iDestruct (local۰at𑁒valid with "Hlocal_auth Hlocal_at") as %Hws_lookup.

    wp۰rec.
    wp۰apply (wp𑁒get_local with "Hlocal") as "_".
    iApply wp𑁒thread_id_mono.
    wp۰apply+ (domain٠key۰id𑁒spec with "Hid") as "_".
    wp۰apply+ (dynarray_1٠grow𑁒spec with "Hl") as "Hl"; first lia.

    iEval (simpl_length) in "Hl".
    iEval (rewrite -(fmap_replicate option۰to_val _ None) -fmap_app) in "Hl".

    wp۰apply+ (dynarray_1٠get𑁒spec _ _ _ (Some v) with "Hl") as "Hl".
    { lia. }
    { rewrite Nat2Z.id list_lookup_fmap_Some.
      exists (Some v). split; first done.
      eapply consistent𑁒lookup𑁒Some𑁒Some; last done.
      apply consistent𑁒app𑁒None. done.
    }
    wp۰pures.

    iApply "HΦ".
    iFrameSteps. iPureIntro.
    apply consistent𑁒app𑁒None. done.
  Qed.
  Lemma domain٠local_get𑁒spec𑁒pointstopred keys key Ψ tid :
    {{{
      domain۰local tid keys ∗
      domain۰local_pointstopred tid key Ψ
    }}}
      domain٠local_get key ∶ tid
    {{{
      v
    , RET v;
      domain۰local tid keys ∗
      domain۰local_pointsto tid key (DfracOwn 1) v ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (Hlocal & (:local_pointstopred)) HΦ".
    - wp۰apply (domain٠local_get𑁒spec𑁒init with "[$Hlocal $Hkey $Hinit] HΦ").
    - wp۰apply (domain٠local_get𑁒spec𑁒pointsto with "[$Hlocal $Hlocal_pointsto]") as "(Hlocal & Hlocal_pointsto)".
      iApply ("HΦ" with "[$]").
  Qed.

  Lemma domain٠local_set𑁒spec𑁒init keys key Ψ v tid :
    {{{
      domain۰local tid keys ∗
      domain۰key key Ψ ∗
      domain۰local_init tid key
    }}}
      domain٠local_set key v ∶ tid
    {{{
      RET ();
      domain۰local tid keys ∗
      domain۰local_pointsto tid key (DfracOwn 1) v
    }}}.
  Proof.
    iIntros "%Φ ((:local) & #Hkey & (:local_init suff=)) HΦ".
    iDestruct (local_pointsto𑁒agree with "Hlocal Hlocal_") as %[= <-]. iClear "Hlocal_".
    iDestruct (meta𑁒agree with "Hl_meta Hl_meta_") as %<-. iClear "Hl_meta_".
    iDestruct (local۰at𑁒valid with "Hlocal_auth Hlocal_at") as %Hws_lookup.

    wp۰rec.
    wp۰apply+ (wp𑁒get_local with "Hlocal") as "_".
    iApply wp𑁒thread_id_mono.
    wp۰apply+ (domain٠key۰id𑁒spec with "Hid") as "_".
    wp۰apply+ (dynarray_1٠grow𑁒spec with "Hl") as "Hl"; first lia.

    iEval (simpl_length) in "Hl".
    iEval (rewrite -(fmap_replicate option۰to_val _ None) -fmap_app) in "Hl".

    iMod (local𑁒update (Some v) with "Hlocal_auth Hlocal_at") as "(Hlocal_auth & Hlocal_at)".
    wp۰apply+ (dynarray_1٠set𑁒spec with "Hl") as "Hl".
    { simpl_length. lia. }

    iApply "HΦ".
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ (Some _)).
    iFrameSteps; iPureIntro.
    { rewrite dom_insert_lookup_L //. }
    { apply consistent𑁒update.
      { simpl_length. lia. }
      { apply consistent𑁒app𑁒None. done. }
    }
  Qed.
  Lemma domain٠local_set𑁒spec𑁒pointsto keys key w v tid :
    {{{
      domain۰local tid keys ∗
      domain۰local_pointsto tid key (DfracOwn 1) w
    }}}
      domain٠local_set key v ∶ tid
    {{{
      RET ();
      domain۰local tid keys ∗
      domain۰local_pointsto tid key (DfracOwn 1) v
    }}}.
  Proof.
    iIntros "%Φ ((:local) & (:local_pointsto suff=)) HΦ".
    iDestruct (local_pointsto𑁒agree with "Hlocal Hlocal_") as %[= <-]. iClear "Hlocal_".
    iDestruct (meta𑁒agree with "Hl_meta Hl_meta_") as %<-. iClear "Hl_meta_".
    iDestruct (local۰at𑁒valid with "Hlocal_auth Hlocal_at") as %Hws_lookup.

    wp۰rec.
    wp۰apply+ (wp𑁒get_local with "Hlocal") as "_".
    iApply wp𑁒thread_id_mono.
    wp۰apply+ (domain٠key۰id𑁒spec with "Hid") as "_".
    wp۰apply+ (dynarray_1٠grow𑁒spec with "Hl") as "Hl"; first lia.

    iEval (simpl_length) in "Hl".
    iEval (rewrite -(fmap_replicate option۰to_val _ None) -fmap_app) in "Hl".

    iMod (local𑁒update (Some v) with "Hlocal_auth Hlocal_at") as "(Hlocal_auth & Hlocal_at)".
    wp۰apply+ (dynarray_1٠set𑁒spec with "Hl") as "Hl".
    { simpl_length. lia. }

    iApply "HΦ".
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ (Some _)).
    iFrameSteps; iPureIntro.
    { rewrite dom_insert_lookup_L //. }
    { apply consistent𑁒update.
      { simpl_length. lia. }
      { apply consistent𑁒app𑁒None. done. }
    }
  Qed.
  Lemma domain٠local_set𑁒spec𑁒pointstopred keys key Ψ v tid :
    {{{
      domain۰local tid keys ∗
      domain۰local_pointstopred tid key Ψ
    }}}
      domain٠local_set key v ∶ tid
    {{{
      RET ();
      domain۰local tid keys ∗
      domain۰local_pointsto tid key (DfracOwn 1) v
    }}}.
  Proof.
    iIntros "%Φ (Hlocal & (:local_pointstopred)) HΦ".
    - wp۰apply (domain٠local_set𑁒spec𑁒init with "[$Hlocal $Hkey $Hinit] HΦ").
    - wp۰apply (domain٠local_set𑁒spec𑁒pointsto with "[$Hlocal $Hlocal_pointsto] HΦ").
  Qed.
End domain۰G.

Axiom domain٠yield𑁒spec : ∀ `{zoo۰G : !ZooG Σ} Φ,
  ▷ Φ ()%V ⊢
  WP domain٠yield () {{ Φ }}.

Axiom domain٠self_index𑁒spec : ∀ `{zoo۰G : !ZooG Σ} Φ,
  (∀ (i : nat), ▷ Φ #i) ⊢
  WP domain٠self_index () {{ Φ }}.

Axiom domain٠recommended_domain_count𑁒spec : ∀ `{zoo۰G : !ZooG Σ} Φ,
  (∀ (i : nat), ▷ Φ #i) ⊢
  WP domain٠recommended_domain_count () {{ Φ }}.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[global] Instance domain٠yield𑁒diaspec :
    DIASPEC
    {{
      True
    }}
      domain٠yield ()%V
    {{
      RET ();
      True
    }}.
  Proof.
    iSteps.
    wp۰apply domain٠yield𑁒spec.
    iSteps.
  Qed.

  #[global] Instance domain٠self_index𑁒diaspec :
    DIASPEC
    {{
      True
    }}
      domain٠self_index ()%V
    {{ (i : nat),
      RET #i;
      True
    }}.
  Proof.
    iSteps.
    wp۰apply domain٠self_index𑁒spec.
    iSteps.
  Qed.

  #[global] Instance domain٠recommended_domain_count𑁒diaspec :
    DIASPEC
    {{
      True
    }}
      domain٠recommended_domain_count ()%V
    {{ (i : nat),
      RET #i;
      True
    }}.
  Proof.
    iSteps.
    wp۰apply domain٠recommended_domain_count𑁒spec.
    iSteps.
  Qed.
End zoo۰G.

#[global] Opaque domain٠spawn.
#[global] Opaque domain٠join.
#[global] Opaque domain٠local_new.
#[global] Opaque domain٠local_get.
#[global] Opaque domain٠local_set.
#[global] Opaque domain٠yield.
#[global] Opaque domain٠self_index.
#[global] Opaque domain٠recommended_domain_count.

#[global] Opaque domain۰model.
#[global] Opaque domain۰key.
#[global] Opaque domain۰local.
#[global] Opaque domain۰local_init.
#[global] Opaque domain۰local_pointsto.
