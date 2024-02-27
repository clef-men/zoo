(* Based on:
   https://gitlab.com/basile.clement/store/-/blob/main/src/store.ml?ref_type=heads
*)

From iris.base_logic Require Import
  lib.ghost_map.

From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  lib.mono_map.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  assert
  lst.
From zebre Require Import
  options.

Implicit Types l r node cnode base root dst : loc.
Implicit Types nodes : list loc.
Implicit Types v t s : val.
Implicit Types σ : gmap loc val.

#[local] Notation "'gen'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'root'" := (
  in_type "t" 1
)(in custom zebre_field
).

#[local] Notation "'ref_gen'" := (
  in_type "ref" 0
)(in custom zebre_field
).
#[local] Notation "'ref_value'" := (
  in_type "ref" 1
)(in custom zebre_field
).

#[local] Notation "'snap_store'" := (
  in_type "snap" 0
)(in custom zebre_proj
).
#[local] Notation "'snap_gen'" := (
  in_type "snap" 1
)(in custom zebre_proj
).
#[local] Notation "'snap_root'" := (
  in_type "snap" 2
)(in custom zebre_proj
).

#[local] Notation "'Root'" := (
  in_type "descr" 0
)(in custom zebre_tag
).
#[local] Notation "'Diff'" := (
  in_type "descr" 1
)(in custom zebre_tag
).

Definition pstore_create : val :=
  λ: <>,
    { #0; ref §Root }.

Definition pstore_ref : val :=
  λ: "t" "v",
    { #0; "v" }.

Definition pstore_get : val :=
  λ: "t" "r",
    "r".{ref_value}.

Definition pstore_set : val :=
  λ: "t" "r" "v",
    let: "g_t" := "t".{gen} in
    let: "g_r" := "r".{ref_gen} in
    if: "g_t" = "g_r" then (
      "r" <-{ref_value} "v"
    ) else (
      let: "root" := ref §Root in
      "t".{root} <- ‘Diff{ "r", "g_r", "r".{ref_value}, "root" } ;;
      "r" <-{ref_gen} "g_t" ;;
      "r" <-{ref_value} "v" ;;
      "t" <-{root} "root"
    ).

Definition pstore_capture : val :=
  λ: "t",
    let: "g" := "t".{gen} in
    "t" <-{gen} #1 + "g" ;;
    ("t", "g", "t".{root}).

#[local] Definition pstore_reroot_aux : val :=
  rec: "pstore_reroot_aux" "node" :=
    match: !"node" with
    | Root =>
        ()
    | Diff "r" "v" "gen" "node'" =>
        "pstore_reroot_opt_aux" "node'" ;;
        "node'" <- ‘Diff{ "r", "r".{ref_gen}, "r".{ref_value}, "node" } ;;
        "r" <-{ref_gen} "gen" ;;
        "r" <-{ref_value} "v"
    end.
#[local] Definition pstore_reroot : val :=
  λ: "node",
    match: !"node" with
    | Root =>
        ()
    | Diff <> <> <> <> =>
        pstore_reroot_aux "node" ;;
        "node" <- §Root
    end.

Definition pstore_restore : val :=
  λ: "t" "s",
    if: "t" ≠ "s".<snap_store> then (
      Fail
    ) else (
      let: "root" := "s".<snap_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> <> =>
          pstore_reroot "root" ;;
          "t" <-{gen} #1 + "s".<snap_gen> ;;
          "t" <-{root} "root"
      end
    ).

Module raw.
  #[local] Definition generation :=
    nat.
  Implicit Types g : generation.

  #[local] Definition store :=
    gmap loc (generation * val).
  Implicit Types ς : store.
  Implicit Types data : generation * val.

  #[local] Definition descriptor : Set :=
    generation * store.
  Implicit Types descr : descriptor.
  Implicit Types descrs : gmap loc descriptor.

  Class PstoreG Σ `{zebre_G : !ZebreG Σ} := {
    #[local] pstore_G_nodes_G :: ghost_mapG Σ loc descriptor ;
  }.

  Definition pstore_Σ := #[
    ghost_mapΣ loc descriptor
  ].
  #[global] Instance subG_pstore_Σ Σ `{zebre_G : !ZebreG Σ} :
    subG pstore_Σ Σ →
    PstoreG Σ.
  Proof.
    solve_inG.
  Qed.

  Section pstore_G.
    Context `{pstore_G : PstoreG Σ}.

    #[local] Definition store_on σ0 ς :=
      ς ∪ (pair 0 <$> σ0).
    #[local] Definition store_generation g ς :=
      map_Forall (λ r data, data.1 ≤ g) ς.

    #[local] Definition descriptor_wf σ0 descr :=
      dom descr.2 ⊆ dom σ0 ∧
      store_generation descr.1 descr.2.

    #[local] Definition delta : Set :=
      loc * (generation * val).
    Implicit Types δ : delta.
    Implicit Types δs : list delta.

    #[local] Definition deltas_apply δs ς :=
      list_to_map δs ∪ ς.
    #[local] Fixpoint deltas_chain node nodes δs dst : iProp Σ :=
      match nodes, δs with
      | [], [] =>
          ⌜node = dst⌝
      | node' :: nodes, δ :: δs =>
          node ↦ ’Diff{ #δ.1, #δ.2.1, δ.2.2, #node' } ∗
          deltas_chain node' nodes δs dst
      | _, _ =>
          False
      end.

    #[local] Definition edge : Set :=
      loc * (list loc * list delta).
    Implicit Types edg : edge.
    Implicit Types edgs : gmap loc edge.

    #[local] Definition descriptors_auth γ descrs :=
      ghost_map_auth γ 1 descrs.
    #[local] Definition descriptors_elem γ cnode descr :=
      ghost_map_elem γ cnode DfracDiscarded descr.

    #[local] Definition cnode_model is_base γ σ0 cnode descr edg ς : iProp Σ :=
      let node := edg.1 in
      let nodes := edg.2.1 in
      let δs := edg.2.2 in
      ⌜descriptor_wf σ0 descr⌝ ∗
      descriptors_elem γ cnode descr ∗
      ⌜NoDup δs.*1⌝ ∗
      ⌜ if is_base is Some g then
          Forall (λ δ, ∃ data, ς !! δ.1 = Some data ∧ data.1 = g) δs
        else
          0 < length δs
      ⌝ ∗
      ⌜store_on σ0 descr.2 = store_on σ0 $ deltas_apply δs ς⌝ ∗
      deltas_chain cnode nodes δs node.
    Definition pstore_model t σ0 σ : iProp Σ :=
      ∃ l γ g root ς,
      ⌜t = #l⌝ ∗
      ⌜σ = snd <$> ς⌝ ∗
      meta l (nroot.@"impl") γ ∗
      l.[gen] ↦ #g ∗
      l.[root] ↦ #root ∗
      root ↦ §Root ∗
      ( [∗ map] r ↦ data ∈ store_on σ0 ς,
        r.[ref_gen] ↦ #data.1 ∗
        r.[ref_value] ↦ data.2
      ) ∗
      ⌜descriptor_wf σ0 (g, ς)⌝ ∗
      if decide (g = 0) then
        descriptors_auth γ ∅
      else
        ∃ descrs edgs base descr nodes δs,
        descriptors_auth γ descrs ∗
        (* base cnode *)
        ⌜descrs !! base = Some descr⌝ ∗
        ⌜descr.1 < g⌝ ∗
        cnode_model (Some g) γ σ0 base descr (root, (nodes, δs)) ς ∗
        (* other cnodes *)
        ( [∗ map] cnode ↦ descr; edg ∈ delete base descrs; edgs,
          ∃ descr',
          ⌜descrs !! edg.1 = Some descr'⌝ ∗
          cnode_model None γ σ0 cnode descr edg descr'.2
        ).

    Definition pstore_snapshot_model s t σ : iProp Σ :=
      ∃ l γ g node descr,
      ⌜t = #l ∧ s = (t, #g, #node)%V⌝ ∗
      meta l (nroot.@"impl") γ ∗
      descriptors_elem γ node descr ∗
      ⌜descr.1 ≤ g⌝.

    #[global] Instance pstore_model_timeless t σ0 σ :
      Timeless (pstore_model t σ0 σ).
    Proof.
    Admitted.
    #[global] Instance pstore_snapshot_persistent s t σ :
      Persistent (pstore_snapshot_model s t σ).
    Proof.
      apply _.
    Qed.

    #[local] Lemma store_on_dom σ0 ς :
      dom (store_on σ0 ς) = dom σ0 ∪ dom ς.
    Proof.
      set_solver.
    Qed.
    #[local] Lemma store_on_dom' σ0 ς :
      dom ς ⊆ dom σ0 →
      dom (store_on σ0 ς) = dom σ0.
    Proof.
      set_solver.
    Qed.
    #[local] Lemma store_on_lookup {σ0 ς} r data :
      store_on σ0 ς !! r = Some data ↔
          ς !! r = Some data
        ∨ ς !! r = None ∧
          data.1 = 0 ∧
          σ0 !! r = Some data.2.
    Proof.
      destruct data as (g, v).
      rewrite lookup_union_Some_raw lookup_fmap_Some. naive_solver.
    Qed.
    #[local] Lemma store_on_lookup' {σ0 ς} r data :
      ς !! r = Some data →
      store_on σ0 ς !! r = Some data.
    Proof.
      apply lookup_union_Some_l.
    Qed.
    #[local] Lemma store_on_insert r data σ0 ς :
      store_on σ0 (<[r := data]> ς) = <[r := data]> (store_on σ0 ς).
    Proof.
      rewrite insert_union_l //.
    Qed.
    #[local] Lemma store_on_insert_support r v σ0 ς :
      σ0 !! r = None →
      dom ς ⊆ dom σ0 →
      store_on (<[r := v]> σ0) ς = <[r := (0, v)]> (store_on σ0 ς).
    Proof.
      intros Hr%not_elem_of_dom Hς_dom.
      assert (ς !! r = None).
      { apply not_elem_of_dom. set_solver. }
      rewrite insert_union_r // -fmap_insert //.
    Qed.

    #[local] Lemma deltas_apply_nil ς :
      deltas_apply [] ς = ς.
    Proof.
      rewrite /deltas_apply list_to_map_nil left_id //.
    Qed.
    #[local] Lemma deltas_apply_cons δ δs ς :
      deltas_apply (δ :: δs) ς = <[δ.1 := δ.2]> (deltas_apply δs ς).
    Proof.
      destruct δ as (r, data).
      rewrite /deltas_apply list_to_map_cons insert_union_l //.
    Qed.
    #[local] Lemma deltas_apply_singleton δ ς :
      deltas_apply [δ] ς = <[δ.1 := δ.2]> ς.
    Proof.
      rewrite deltas_apply_cons deltas_apply_nil //.
    Qed.
    #[local] Lemma deltas_apply_app δs1 δs2 ς :
      deltas_apply (δs1 ++ δs2) ς = deltas_apply δs1 (deltas_apply δs2 ς).
    Proof.
      rewrite /deltas_apply list_to_map_app assoc //.
    Qed.
    #[local] Lemma deltas_apply_snoc δs δ ς :
      deltas_apply (δs ++ [δ]) ς = deltas_apply δs (<[δ.1 := δ.2]> ς).
    Proof.
      rewrite deltas_apply_app deltas_apply_singleton //.
    Qed.
    #[local] Lemma deltas_apply_snoc' δs r data ς :
      deltas_apply (δs ++ [(r, data)]) ς = deltas_apply δs (<[r := data]> ς).
    Proof.
      apply (deltas_apply_snoc _ (r, data)).
    Qed.
    #[local] Lemma deltas_apply_dom δs ς :
      dom (deltas_apply δs ς) = list_to_set δs.*1 ∪ dom ς.
    Proof.
      rewrite dom_union_L. f_equal. apply dom_list_to_map_L.
    Qed.
    #[local] Lemma deltas_apply_lookup r data δs ς :
      NoDup δs.*1 →
      (r, data) ∈ δs →
      deltas_apply δs ς !! r = Some data.
    Proof.
      intros Hδs_nodup Hδ.
      apply lookup_union_Some_l, elem_of_list_to_map_1; done.
    Qed.
    #[local] Lemma deltas_apply_lookup_ne r δs ς :
      NoDup δs.*1 →
      r ∉ δs.*1 →
      deltas_apply δs ς !! r = ς !! r.
    Proof.
      intros Hδs_nodup Hr.
      apply lookup_union_r, not_elem_of_list_to_map_1. done.
    Qed.
    #[local] Lemma deltas_apply_permutation {δs1} δs2 ς :
      NoDup δs1.*1 →
      δs1 ≡ₚ δs2 →
      deltas_apply δs1 ς = deltas_apply δs2 ς.
    Proof.
      intros. rewrite /deltas_apply (list_to_map_proper _ δs2) //.
    Qed.

    #[local] Lemma deltas_chain_nil_inv node nodes dst :
      deltas_chain node nodes [] dst ⊢
      ⌜nodes = [] ∧ node = dst⌝.
    Proof.
      destruct nodes; iSteps.
    Qed.
    #[local] Lemma deltas_chain_cons_inv node nodes δ δs dst :
      deltas_chain node nodes (δ :: δs) dst ⊢
        ∃ node' nodes',
        ⌜nodes = node' :: nodes'⌝ ∗
        node ↦ ’Diff{ #δ.1, #δ.2.1, δ.2.2, #node' } ∗
        deltas_chain node' nodes' δs dst.
    Proof.
      destruct nodes; iSteps.
    Qed.
    #[local] Lemma deltas_chain_snoc {node nodes δs dst} r g v dst' :
      deltas_chain node nodes δs dst -∗
      dst ↦ ’Diff{ #r, #g, v, #dst' } -∗
      deltas_chain node (nodes ++ [dst']) (δs ++ [(r, (g, v))]) dst'.
    Proof.
      iInduction nodes as [] "IH" forall (node δs); destruct δs; iSteps.
    Qed.

    #[local] Definition descriptors_alloc root :
      ⊢ |==>
        ∃ γ,
        descriptors_auth γ ∅.
    Proof.
      iMod ghost_map_alloc as "(%γ & Hauth & _)".
      iSteps.
    Qed.
    #[local] Lemma descriptors_insert {γ descrs} cnode descr :
      descrs !! cnode = None →
      descriptors_auth γ descrs ⊢ |==>
        descriptors_auth γ (<[cnode := descr]> descrs) ∗
        descriptors_elem γ cnode descr.
    Proof.
      iIntros "%Hdescrs_lookup Hauth".
      iMod (ghost_map_insert with "Hauth") as "($ & Helem)"; first done.
      iApply (ghost_map_elem_persist with "Helem").
    Qed.

    Lemma pstore_model_valid t σ0 σ :
      pstore_model t σ0 σ ⊢
      ⌜dom σ ⊆ dom σ0⌝.
    Proof.
      iIntros "(%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & _)".
      rewrite dom_fmap //.
    Qed.

    Lemma pstore_create_spec :
      {{{ True }}}
        pstore_create ()
      {{{ t,
        RET t;
        (∃ l, ⌜t = #l⌝ ∗ meta_token l (↑nroot.@"user")) ∗
        pstore_model t ∅ ∅
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".
      wp_rec.
      wp_alloc root as "Hroot".
      wp_record l as "Hmeta" "(Hl_gen & Hl_root & _)".
      iMod (descriptors_alloc root) as "(%γ & Hauth)".
      iDestruct (meta_token_difference _ (↑nroot.@"user") with "Hmeta") as "(Hmeta_user & Hmeta)"; first done.
      iDestruct (meta_token_difference _ (↑nroot.@"impl") with "Hmeta") as "(Hmeta & _)"; first solve_ndisj.
      iMod (meta_set with "Hmeta") as "Hmeta"; first done.
      iApply "HΦ".
      iStep. iExists l, γ, 0, root, ∅. iFrame. rewrite big_sepM_empty. iSteps.
    Qed.

    Lemma pstore_ref_spec t σ0 σ v :
      {{{
        pstore_model t σ0 σ
      }}}
        pstore_ref t v
      {{{ r,
        RET #r;
        ⌜σ0 !! r = None⌝ ∗
        pstore_model t (<[r := v]> σ0) σ
      }}}.
    Proof.
      iIntros "%Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".
      wp_rec. wp_record r as "(Hr_gen & Hr_value & _)".
      iAssert ⌜σ0 !! r = None⌝%I as %Hr.
      { rewrite -not_elem_of_dom. iIntros "%Hr".
        iDestruct (big_sepM_lookup with "Hς") as "(_Hr_gen & _)".
        { apply lookup_lookup_total_dom. rewrite store_on_dom' //. }
        iDestruct (pointsto_ne with "Hr_gen _Hr_gen") as %?. done.
      }
      iApply "HΦ".
      iSplitR; first iSteps. iExists l, γ, g, root, ς. iFrame "#∗". iStep 2.
      iSplitL "Hς Hr_gen Hr_value".
      { rewrite store_on_insert_support //.
        iApply (big_sepM_insert_2 with "[Hr_gen Hr_value] Hς").
        iSteps.
      }
      iSplitR. { iPureIntro. split; [set_solver | done]. }
      case_decide as Hg; first iSteps.
      iStep 3 as (descrs edgs base descr nodes δs Hdescrs_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs_gen Hδs) "Helem_base Hδs Hdescrs".
      iExists edgs, nodes, δs. iSteps.
      { iPureIntro. set_solver. }
      { iPureIntro.
        rewrite !store_on_insert_support //; last congruence.
        apply (f_equal dom) in Hδs. set_solver.
      } {
        iClear "Helem_base". clear dependent descr nodes δs.
        iApply (big_sepM2_impl with "Hdescrs"). iIntros "!> !>" (cnode descr (cnode' & (nodes & δs))) "%Hdescrs_lookup %Hedgs_lookup (%descr' & %Hdescrs_lookup' & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_nodup & %Hδs_length & %Hδs' & Hδs'))".
        simpl in *.
        iSteps; iPureIntro; first set_solver.
        rewrite !store_on_insert_support //; last congruence.
        apply (f_equal dom) in Hδs'. set_solver.
      }
    Qed.

    Lemma pstore_get_spec {t σ0 σ r} v :
      (σ ∪ σ0) !! r = Some v →
      {{{
        pstore_model t σ0 σ
      }}}
        pstore_get t #r
      {{{
        RET v;
        pstore_model t σ0 σ
      }}}.
    Proof.
      iIntros "%Hσ_lookup %Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".
      wp_rec.
      assert (∃ g_r, store_on σ0 ς !! r = Some (g_r, v)) as (g_r & Hς_lookup).
      { setoid_rewrite store_on_lookup.
        apply lookup_union_Some_raw in Hσ_lookup as [Hσ_lookup | (Hσ_lookup & Hσ0_lookup)].
        - apply lookup_fmap_Some in Hσ_lookup as ((g_r & _v) & ? & Hς_lookup).
          naive_solver.
        - rewrite lookup_fmap fmap_None in Hσ_lookup.
          naive_solver.
      }
      iDestruct (big_sepM_lookup_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
      wp_load.
      iSteps.
    Qed.

    Lemma pstore_set_spec t σ0 σ r v :
      r ∈ dom σ0 →
      {{{
        pstore_model t σ0 σ
      }}}
        pstore_set t #r v
      {{{
        RET ();
        pstore_model t σ0 (<[r := v]> σ)
      }}}.
    Proof.
      iIntros "%Hr %Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".
      pose proof Hr as (w0 & Hσ0_lookup)%elem_of_dom.
      wp_rec. wp_load.
      assert (∃ g_r w, store_on σ0 ς !! r = Some (g_r, w) ∧ g_r ≤ g) as (g_r & w & Hς_lookup & Hg_r).
      { setoid_rewrite store_on_lookup.
        destruct (ς !! r) as [(g_r, w) |] eqn:Hς_lookup.
        - exists g_r, w. split; first naive_solver.
          opose proof* map_Forall_lookup_1; done.
        - exists 0, w0. split; first naive_solver. lia.
      }
      iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
      wp_load. wp_pures.
      destruct (decide (g = 0)) as [-> | Hg].
      - assert (g_r = 0) as -> by lia.
        rewrite bool_decide_eq_true_2 //. wp_pures.
        wp_store.
        iDestruct ("Hς" $! (0, v) with "[$Hr_gen $Hr_value]") as "Hς".
        iApply "HΦ".
        iExists l, γ, 0, root, (<[r := (0, v)]> ς). iFrame "#∗". iStep.
        iSplitR. { rewrite fmap_insert //. }
        iSplitL. { rewrite insert_union_l //. }
        iPureIntro. split; first set_solver. apply map_Forall_insert_2; done.
      - destruct (decide (g = g_r)) as [<- | Hcase].
        + rewrite bool_decide_eq_true_2 //.
          wp_store.
          iDestruct ("Hς" $! (g, v) with "[$Hr_gen $Hr_value]") as "Hς".
          iApply "HΦ".
          iExists l, γ, g, root, (<[r := (g, v)]> ς). iFrame "#∗". iStep.
          iSplitR. { rewrite fmap_insert //. }
          iSplitL "Hς". { rewrite insert_union_l //. }
          iSplitR. { iPureIntro. split; first set_solver. apply map_Forall_insert_2; done. }
          rewrite decide_False //.
          iStep 3 as (descrs edgs base descr nodes δs Hdescrs_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs_gen Hδs) "Helem_base Hδs Hdescrs". iSteps; iPureIntro.
          { eapply Forall_impl; first done. intros (r' & (g' & v')) H.
            destruct (decide (r = r')) as [<- | Hr'].
            - rewrite lookup_insert. naive_solver.
            - rewrite lookup_insert_ne //.
          } {
            clear Hδs_gen. generalize dependent ς.
            induction δs as [| (r' & (g' & v')) δs IH] using rev_ind.
            all: intros ς Hς_dom Hς_gen Hς_lookup Hδs.
            - exfalso.
              rewrite deltas_apply_nil in Hδs.
              rewrite -Hδs store_on_lookup in Hς_lookup.
              destruct Hς_lookup as [Hstore_lookup |]; last naive_solver.
              opose proof* (map_Forall_lookup_1 _ descr.2); [done.. |].
              naive_solver lia.
            - rewrite deltas_apply_snoc /=.
              destruct (decide (r = r')) as [<- | Hr'].
              + rewrite deltas_apply_snoc /= in Hδs.
                rewrite insert_insert //.
              + rewrite insert_commute //.
                apply IH; simpl.
                * rewrite fmap_app NoDup_app in Hδs_nodup. naive_solver.
                * rewrite dom_insert union_subseteq singleton_subseteq_l.
                  split; last done.
                  apply (f_equal dom) in Hδs.
                  rewrite store_on_dom' // store_on_dom in Hδs.
                  rewrite Hδs deltas_apply_dom. set_solver.
                * apply map_Forall_insert_2; last done.
                  trans descr.1; last lia.
                  assert (store_on σ0 descr.2 !! r' = Some (g', v')) as [Hstore_lookup | (_ & ? & _)]%store_on_lookup; last lia.
                  { rewrite Hδs.
                    apply store_on_lookup', deltas_apply_lookup; first done.
                    set_solver.
                  }
                  eapply map_Forall_lookup_1 in Hstore_gen; done.
                * rewrite /store_on -insert_union_l lookup_insert_ne //.
                * rewrite deltas_apply_snoc // in Hδs.
          }
        + rewrite bool_decide_eq_false_2; first naive_solver. wp_pures.
          wp_alloc root' as "Hroot'". do 2 wp_load. do 4 wp_store.
          iDestruct ("Hς" $! (g, v) with "[$Hr_gen $Hr_value]") as "Hς".
          iApply "HΦ".
          iExists l, γ, g, root', (<[r := (g, v)]> ς). iFrame "#∗". iStep.
          iSplitR. { rewrite fmap_insert //. }
          iSplitL "Hς". { rewrite insert_union_l //. }
          iSplitR. { iPureIntro. split; first set_solver. apply map_Forall_insert_2; done. }
          rewrite decide_False //.
          iStep 3 as (descrs edgs base descr nodes δs Hdescrs_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs_gen Hδs) "Helem_base Hδs Hdescrs".
          assert (r ∉ δs.*1) as Hr_notin_δs.
          { intros (i & ((? & data) & -> & Hδs_lookup)%list_lookup_fmap_inv)%elem_of_list_lookup.
            opose proof* Forall_lookup_1 as H; [done.. |].
            apply store_on_lookup in Hς_lookup. naive_solver.
          }
          assert (store_on σ0 descr.2 !! r = Some (g_r, w)) as Hstore_lookup.
          { rewrite Hδs store_on_lookup deltas_apply_lookup_ne //.
            rewrite store_on_lookup // in Hς_lookup.
          }
          iExists edgs, (nodes ++ [root']), (δs ++ [(r, (g_r, w))]). iFrame. iSteps; [iPureIntro.. |].
          { rewrite fmap_app NoDup_app. split_and!; first done.
            - set_solver.
            - apply NoDup_singleton.
          } {
            rewrite Forall_app Forall_singleton. split.
            - rewrite Forall_forall => δ Hδ. rewrite lookup_insert_ne.
              { rewrite elem_of_list_fmap in Hr_notin_δs. naive_solver. }
              rewrite Forall_forall in Hδs_gen. naive_solver.
            - rewrite lookup_insert. naive_solver.
          } {
            rewrite deltas_apply_snoc insert_insert -deltas_apply_snoc'.
            rewrite (deltas_apply_permutation ((r, (g_r, w)) :: δs)).
            { rewrite fmap_app NoDup_app. split_and!; first done.
              - set_solver.
              - apply NoDup_singleton.
            } {
              solve_Permutation.
            }
            rewrite deltas_apply_cons store_on_insert -Hδs insert_id //.
          } {
            iApply (deltas_chain_snoc with "Hδs Hroot").
          }
    Qed.

    Lemma pstore_capture_spec t σ0 σ :
      {{{
        pstore_model t σ0 σ
      }}}
        pstore_capture t
      {{{ s,
        RET s;
        pstore_model t σ0 σ ∗
        pstore_snapshot_model s t σ
      }}}.
    Proof.
      iIntros "%Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".
      wp_rec. wp_load. wp_store. wp_load. wp_pures.
      iApply "HΦ".
      case_decide as Hg; first subst.
      - pose descr := (0, ς).
        iMod (descriptors_insert root descr with "Hmodel") as "(Hauth & #Helem)"; first done.
        iSplitL; last iSteps.
        iExists l, γ, 1, root, ς. iFrame "#∗". iStep 2. iSplitR.
        { iPureIntro. split; first set_solver.
          eapply map_Forall_impl; first done. naive_solver.
        }
        iStep. iExists ∅, root, descr, [], []. iSplitR.
        { iPureIntro. rewrite lookup_insert //. }
        iSteps.
        { rewrite NoDup_nil //. }
        { rewrite deltas_apply_nil //. }
        rewrite insert_empty delete_singleton.
        iApply (big_sepM2_empty with "[//]").
      - iDestruct "Hmodel" as "(%descrs & %edgs & %base & %descr & %nodes & %δs & Hauth & %Hdescrs_lookup_base & %Hgen & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs_gen & %Hδs & Hδs) & Hdescrs)".
        destruct δs as [| δ δs]; simpl.
        + iDestruct (deltas_chain_nil_inv with "Hδs") as %(-> & <-).
          iSplitL; iSteps.
          { iPureIntro. eapply map_Forall_impl; first done. naive_solver lia. }
          rewrite decide_False; first lia.
          iSteps. iExists []. iSteps.
        + iAssert ⌜edgs !! base = None⌝%I as %Hedgs_lookup_base.
          { rewrite -eq_None_ne_Some. iIntros "%edg %Hedgs_lookup".
            iDestruct (big_sepM2_lookup_r with "Hdescrs") as "(%descr' & %Hdescrs_lookup & _)"; first done.
            rewrite lookup_delete // in Hdescrs_lookup.
          }
          iAssert ⌜descrs !! root = None⌝%I as %Hdescrs_lookup_root.
          { destruct (decide (root = base)) as [-> | Hcase].
            - iDestruct (deltas_chain_cons_inv with "Hδs") as "(%node & %nodes' & -> & Hbase & _)".
              iDestruct (pointsto_ne with "Hroot Hbase") as %?. done.
            - rewrite -eq_None_ne_Some. iIntros "%descr' %Hdescrs_lookup".
              iDestruct (big_sepM2_lookup_l with "Hdescrs") as ((cnode' & (nodes' & δs'))) "(_ & %descr'' & _ & _ & _ & _ & %Hδs'_length & _ & Hδs') /=".
              { rewrite lookup_delete_Some //. }
              destruct δs' as [| δ' δs']; first naive_solver lia.
              iDestruct (deltas_chain_cons_inv with "Hδs'") as "(%node & %nodes'' & -> & _Hroot & _)".
              iDestruct (pointsto_ne with "Hroot _Hroot") as %?. done.
          }
          pose root_descr := (g, ς).
          iMod (descriptors_insert root root_descr with "Hauth") as "(Hauth & #Helem_root)"; first done.
          iSplitL; last iSteps.
          iExists l, γ, (S g), root, ς. iFrame "#∗". iSteps as (_ | _) "" | "".
          { iPureIntro. eapply map_Forall_impl; first done. naive_solver. }
          iExists root, root_descr. iSplitR.
          { rewrite lookup_insert //. }
          set edg := (root, (nodes, δ :: δs)).
          iExists (<[base := edg]> edgs), [], []. iSteps.
          { rewrite NoDup_nil //. }
          { rewrite deltas_apply_nil //. }
          rewrite delete_insert //.
          iApply big_sepM2_delete_l; first done.
          iExists edg. iSteps.
          { rewrite lookup_insert //. }
          iExists root_descr. iSteps.
          { iPureIntro. rewrite lookup_insert //. }
          rewrite delete_insert //.
          iClear "Helem_base". clear dependent descr nodes δs.
          iApply (big_sepM2_impl with "Hdescrs"). iIntros "!>" (cnode descr (cnode' & (nodes & δs))) "%Hdescrs_lookup %Hedgs_lookup_cnode (%descr' & %Hdescrs_lookup' & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_nodup & %Hδs_length & %Hδs' & Hδs'))".
          simpl in *.
          iExists descr'. iSteps.
          rewrite lookup_insert_ne //. congruence.
    Qed.

    Lemma pstore_restore_spec t σ0 σ s σ' :
      {{{
        pstore_model t σ0 σ ∗
        pstore_snapshot_model s t σ'
      }}}
        pstore_restore t s
      {{{
        RET ();
        pstore_model t σ0 σ'
      }}}.
    Proof.
    Admitted.
  End pstore_G.

  #[global] Opaque pstore_model.
  #[global] Opaque pstore_snapshot_model.
End raw.

#[global] Opaque pstore_create.
#[global] Opaque pstore_ref.
#[global] Opaque pstore_get.
#[global] Opaque pstore_set.
#[global] Opaque pstore_capture.
#[global] Opaque pstore_restore.

Class PstoreG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] pstore_G_raw_G :: raw.PstoreG Σ ;
  #[local] pstore_G_support_G :: MonoMapG Σ loc val ;
}.

Definition pstore_Σ := #[
  raw.pstore_Σ ;
  mono_map_Σ loc val
].
Lemma subG_pstore_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG pstore_Σ Σ →
  PstoreG Σ.
Proof.
  solve_inG.
Qed.

Section pstore_G.
  Context `{pstore_G : PstoreG Σ}.

  Definition pstore_model t σ : iProp Σ :=
    ∃ l γ σ0 ς,
    ⌜t = #l⌝ ∗
    ⌜σ ⊆ ς ∪ σ0⌝ ∗
    meta l (nroot.@"user") γ ∗
    mono_map_auth γ σ0 ∗
    raw.pstore_model t σ0 ς.

  Definition pstore_snapshot_model s t σ : iProp Σ :=
    ∃ l γ σ0 ς,
    ⌜t = #l⌝ ∗
    ⌜σ ⊆ ς ∪ σ0⌝ ∗
    meta l (nroot.@"user") γ ∗
    mono_map_lb γ σ0 ∗
    raw.pstore_snapshot_model s t ς.

  #[global] Instance pstore_model_timeless t σ :
    Timeless (pstore_model t σ).
  Proof.
    apply _.
  Qed.
  #[global] Instance pstore_snapshot_persistent s t σ :
    Persistent (pstore_snapshot_model s t σ).
  Proof.
    apply _.
  Qed.

  Lemma pstore_create_spec :
    {{{ True }}}
      pstore_create ()
    {{{ t,
      RET t;
      pstore_model t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd.
    wp_apply (raw.pstore_create_spec with "[//]") as (t) "((%l & -> & Hmeta) & Ht)".
    iMod mono_map_alloc as "(%γ & Hauth)".
    iMod (meta_set with "Hmeta") as "Hmeta"; first done.
    iSteps. iExists ∅, ∅. iSteps.
  Qed.

  Lemma pstore_ref_spec t σ v :
    {{{
      pstore_model t σ
    }}}
      pstore_ref t v
    {{{ r,
      RET #r;
      ⌜σ !! r = None⌝ ∗
      pstore_model t (<[r := v]> σ)
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (raw.pstore_model_valid with "Ht") as %Hς_dom.
    iApply wp_fupd.
    wp_apply (raw.pstore_ref_spec with "Ht") as (r) "(%Hσ0_lookup & Ht)".
    assert (ς !! r = None) as Hς_lookup.
    { rewrite -!not_elem_of_dom in Hσ0_lookup |- *. set_solver. }
    assert (σ !! r = None) as Hσ_lookup.
    { eapply lookup_weaken_None; last done. apply lookup_union_None_2; done. }
    iMod (mono_map_insert with "Hauth") as "Hauth"; first done.
    iApply "HΦ".
    iStep. iExists l, γ, (<[r := v]> σ0), ς. iSteps. iPureIntro.
    rewrite -insert_union_r //. apply insert_mono. done.
  Qed.

  Lemma pstore_get_spec {t σ r} v :
    σ !! r = Some v →
    {{{
      pstore_model t σ
    }}}
      pstore_get t #r
    {{{
      RET v;
      pstore_model t σ
    }}}.
  Proof.
    iIntros "%Hσ_lookup %Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    wp_apply (raw.pstore_get_spec with "Ht") as "Ht".
    { eapply lookup_weaken; done. }
    iSteps.
  Qed.

  Lemma pstore_set_spec t σ r v :
    r ∈ dom σ →
    {{{
      pstore_model t σ
    }}}
      pstore_set t #r v
    {{{
      RET ();
      pstore_model t (<[r := v]> σ)
    }}}.
  Proof.
    iIntros "%Hr %Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (raw.pstore_model_valid with "Ht") as %Hς_dom.
    wp_apply (raw.pstore_set_spec with "Ht") as "Ht".
    { apply subseteq_dom in Hσ. set_solver. }
    iApply "HΦ".
    iExists l, γ, σ0, (<[r := v]> ς). iSteps. iPureIntro.
    rewrite -insert_union_l. apply insert_mono. done.
  Qed.

  Lemma pstore_capture_spec t σ :
    {{{
      pstore_model t σ
    }}}
      pstore_capture t
    {{{ s,
      RET s;
      pstore_model t σ ∗
      pstore_snapshot_model s t σ
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iMod (mono_map_lb_get with "Hauth") as "(Hauth & #Hlb)".
    wp_apply (raw.pstore_capture_spec with "Ht") as (s) "(Ht & Hs)".
    iSteps.
  Qed.

  Lemma pstore_restore_spec t σ s σ' :
    {{{
      pstore_model t σ ∗
      pstore_snapshot_model s t σ'
    }}}
      pstore_restore t s
    {{{
      RET ();
      pstore_model t σ'
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) & (%_l & %_γ & %σ0' & %ς' & %Heq & %Hσ' & _Hmeta & #Hlb & Hs)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_apply (raw.pstore_restore_spec with "[$Ht $Hs]") as "Ht".
    iDestruct (mono_map_lb_valid with "Hauth Hlb") as %Hσ0'.
    iApply "HΦ".
    iExists l, γ, σ0, ς'. iSteps. iPureIntro.
    trans (ς' ∪ σ0'); first done. apply map_union_mono_l. done.
  Qed.
End pstore_G.

#[global] Opaque pstore_model.
#[global] Opaque pstore_snapshot_model.
