(* Based on:
   https://gitlab.com/basile.clement/store/-/blob/main/src/store.ml?ref_type=heads
*)

From iris.base_logic Require Import
  lib.ghost_map.

From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  lib.mono_map_.
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

Definition store_create : val :=
  λ: <>,
    { #0; ref §Root }.

Definition store_ref : val :=
  λ: "t" "v",
    { #0; "v" }.

Definition store_get : val :=
  λ: "t" "r",
    "r".{ref_value}.

Definition store_set : val :=
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

Definition store_capture : val :=
  λ: "t",
    let: "g" := "t".{gen} in
    "t" <-{gen} #1 + "g" ;;
    ("t", "g", "t".{root}).

#[local] Definition store_collect : val :=
  rec: "store_collect" "node" "acc" :=
    match: !"node" with
    | Root =>
        ("node", "acc")
    | Diff <> <> <> "node'" =>
        "store_collect" "node'" ‘Cons{ "node", "acc" }
    end.
#[local] Definition store_revert : val :=
  rec: "store_revert" "node" "seg" :=
    match: "seg" with
    | Nil =>
        "node" <- §Root
    | Cons "node'" "seg" =>
        match: !"node'" with
        | Root =>
            Fail
        | Diff "r" "g" "v" "node_" =>
            assert ("node_" = "node") ;;
            "node" <- ‘Diff{ "r", "r".{ref_gen}, "r".{ref_value}, "node'" } ;;
            "r" <-{ref_gen} "g" ;;
            "r" <-{ref_value} "v" ;;
            "store_revert" "node'" "seg"
        end
    end.
#[local] Definition store_reroot : val :=
  λ: "node",
    let: "root", "nodes" := store_collect "node" §Nil in
    store_revert "root" "nodes".

Definition store_restore : val :=
  λ: "t" "s",
    if: "t" ≠ "s".<snap_store> then (
      Fail
    ) else (
      let: "root" := "s".<snap_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> <> =>
          store_reroot "root" ;;
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
  Implicit Types descr base_descr : descriptor.

  Class StoreG Σ `{zebre_G : !ZebreG Σ} := {
    #[local] store_G_nodes_G :: ghost_mapG Σ loc descriptor ;
  }.

  Definition store_Σ := #[
    ghost_mapΣ loc descriptor
  ].
  #[global] Instance subG_store_Σ Σ `{zebre_G : !ZebreG Σ} :
    subG store_Σ Σ →
    StoreG Σ.
  Proof.
    solve_inG.
  Qed.

  Section store_G.
    Context `{store_G : StoreG Σ}.

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

    #[local] Definition cnodes_auth γ cnodes :=
      ghost_map_auth γ 1 cnodes.
    #[local] Definition cnodes_elem γ cnode descr :=
      ghost_map_elem γ cnode DfracDiscarded descr.

    #[local] Definition cnode_model is_base γ σ0 cnode descr node ς : iProp Σ :=
      ⌜descriptor_wf σ0 descr⌝ ∗
      cnodes_elem γ cnode descr ∗
      ( ∃ nodes δs,
        ⌜NoDup δs.*1⌝ ∗
        ⌜ if is_base is Some g then
            Forall (λ δ, ∃ data, ς !! δ.1 = Some data ∧ data.1 = g) δs
          else
            0 < length δs
        ⌝ ∗
        ⌜store_on σ0 descr.2 = store_on σ0 $ deltas_apply δs ς⌝ ∗
        deltas_chain cnode nodes δs node
      ).
    Definition store_model t σ0 σ : iProp Σ :=
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
        cnodes_auth γ ∅
      else
        ∃ cnodes base base_descr,
        cnodes_auth γ cnodes ∗
        (* base cnode *)
        ⌜cnodes !! base = Some base_descr⌝ ∗
        ⌜base_descr.1 < g⌝ ∗
        cnode_model (Some g) γ σ0 base base_descr root ς ∗
        (* other cnodes *)
        ( [∗ map] cnode ↦ descr ∈ delete base cnodes,
          ∃ cnode' descr',
          ⌜cnodes !! cnode' = Some descr'⌝ ∗
          cnode_model None γ σ0 cnode descr cnode' descr'.2
        ).

    Definition store_snapshot_model s t σ : iProp Σ :=
      ∃ l γ g node descr,
      ⌜t = #l ∧ s = (t, #g, #node)%V⌝ ∗
      meta l (nroot.@"impl") γ ∗
      cnodes_elem γ node descr ∗
      ⌜descr.1 ≤ g⌝.

    #[global] Instance store_model_timeless t σ0 σ :
      Timeless (store_model t σ0 σ).
    Proof.
    Admitted.
    #[global] Instance store_snapshot_persistent s t σ :
      Persistent (store_snapshot_model s t σ).
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

    #[local] Definition cnodes_alloc root :
      ⊢ |==>
        ∃ γ,
        cnodes_auth γ ∅.
    Proof.
      iMod ghost_map_alloc as "(%γ & Hcnodes_auth & _)".
      iSteps.
    Qed.
    #[local] Lemma cnodes_insert {γ cnodes} cnode descr :
      cnodes !! cnode = None →
      cnodes_auth γ cnodes ⊢ |==>
        cnodes_auth γ (<[cnode := descr]> cnodes) ∗
        cnodes_elem γ cnode descr.
    Proof.
      iIntros "%Hcnodes_lookup Hcnodes_auth".
      iMod (ghost_map_insert with "Hcnodes_auth") as "($ & Hcnodes_elem)"; first done.
      iApply (ghost_map_elem_persist with "Hcnodes_elem").
    Qed.

    Lemma store_model_valid t σ0 σ :
      store_model t σ0 σ ⊢
      ⌜dom σ ⊆ dom σ0⌝.
    Proof.
      iIntros "(%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & _)".
      rewrite dom_fmap //.
    Qed.

    Lemma store_create_spec :
      {{{ True }}}
        store_create ()
      {{{ t,
        RET t;
        (∃ l, ⌜t = #l⌝ ∗ meta_token l (↑nroot.@"user")) ∗
        store_model t ∅ ∅
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".
      wp_rec.
      wp_alloc root as "Hroot".
      wp_record l as "Hmeta" "(Hl_gen & Hl_root & _)".
      iMod (cnodes_alloc root) as "(%γ & Hcnodes_auth)".
      iDestruct (meta_token_difference _ (↑nroot.@"user") with "Hmeta") as "(Hmeta_user & Hmeta)"; first done.
      iDestruct (meta_token_difference _ (↑nroot.@"impl") with "Hmeta") as "(Hmeta & _)"; first solve_ndisj.
      iMod (meta_set with "Hmeta") as "Hmeta"; first done.
      iApply "HΦ".
      iStep. iExists l, γ, 0, root, ∅. iFrame. rewrite big_sepM_empty. iSteps.
    Qed.

    Lemma store_ref_spec t σ0 σ v :
      {{{
        store_model t σ0 σ
      }}}
        store_ref t v
      {{{ r,
        RET #r;
        ⌜σ0 !! r = None⌝ ∗
        store_model t (<[r := v]> σ0) σ
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
      iStep 3 as (cnodes base base_descr _ Hbase_gen (Hbase_store_dom & Hbase_store_gen) nodes δs Hδs_nodup Hδs_gen Hδs) "Hcnodes_elem_base Hδs Hcnodes". iSteps.
      { iPureIntro. set_solver. }
      { iPureIntro.
        rewrite !store_on_insert_support //; last congruence.
        apply (f_equal dom) in Hδs. set_solver.
      } {
        iApply (big_sepM_impl with "Hcnodes"). iIntros "!> !> %cnode %descr %Hcnodes_lookup (%cnode' & %descr' & %Hcnodes_lookup' & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Hcnodes_elem_cnode & (%nodes' & %δs' & %Hδs'_nodup & %Hδs'_length & %Hδs' & Hδs')))".
        iExists cnode', descr'. iSteps; iPureIntro; first set_solver.
        rewrite !store_on_insert_support //; last congruence.
        apply (f_equal dom) in Hδs'. set_solver.
      }
    Qed.

    Lemma store_get_spec {t σ0 σ r} v :
      (σ ∪ σ0) !! r = Some v →
      {{{
        store_model t σ0 σ
      }}}
        store_get t #r
      {{{
        RET v;
        store_model t σ0 σ
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

    Lemma store_set_spec t σ0 σ r v :
      r ∈ dom σ0 →
      {{{
        store_model t σ0 σ
      }}}
        store_set t #r v
      {{{
        RET ();
        store_model t σ0 (<[r := v]> σ)
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
          iStep 3 as (cnodes base base_descr _ Hbase_gen (Hbase_store_dom & Hbase_store_gen) nodes δs Hδs_nodup Hδs_gen Hδs) "Hcnodes_elem Hδs $". iSteps; iPureIntro.
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
              destruct Hς_lookup as [Hbase_store_lookup |]; last naive_solver.
              opose proof* (map_Forall_lookup_1 _ base_descr.2); [done.. |].
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
                  trans base_descr.1; last lia.
                  assert (store_on σ0 base_descr.2 !! r' = Some (g', v')) as [Hbase_store_lookup | (_ & ? & _)]%store_on_lookup; last lia.
                  { rewrite Hδs.
                    apply store_on_lookup', deltas_apply_lookup; first done.
                    set_solver.
                  }
                  eapply map_Forall_lookup_1 in Hbase_store_gen; done.
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
          iStep 3 as (cnodes base base_descr _ Hbase_gen (Hbase_store_dom & Hbase_store_gen) nodes δs Hδs_nodup Hδs_gen Hδs) "Hcnodes_elem Hδs $". iStep 2.
          assert (r ∉ δs.*1) as Hr_notin_δs.
          { intros (i & ((? & data) & -> & Hδs_lookup)%list_lookup_fmap_inv)%elem_of_list_lookup.
            opose proof* Forall_lookup_1 as H; [done.. |].
            apply store_on_lookup in Hς_lookup. naive_solver.
          }
          assert (store_on σ0 base_descr.2 !! r = Some (g_r, w)) as Hbase_store_lookup.
          { rewrite Hδs store_on_lookup deltas_apply_lookup_ne //.
            rewrite store_on_lookup // in Hς_lookup.
          }
          iExists (nodes ++ [root']), (δs ++ [(r, (g_r, w))]). iSteps; [iPureIntro.. |].
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
            }
            { solve_Permutation. }
            rewrite deltas_apply_cons store_on_insert -Hδs insert_id //.
          } {
            iApply (deltas_chain_snoc with "Hδs Hroot").
          }
    Qed.

    Lemma store_capture_spec t σ0 σ :
      {{{
        store_model t σ0 σ
      }}}
        store_capture t
      {{{ s,
        RET s;
        store_model t σ0 σ ∗
        store_snapshot_model s t σ
      }}}.
    Proof.
      iIntros "%Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".
      wp_rec. wp_load. wp_store. wp_load. wp_pures.
      iApply "HΦ".
      case_decide as Hg; first subst.
      - pose descr := (0, ς).
        iMod (cnodes_insert root descr with "Hmodel") as "(Hcnodes_auth & #Hcnodes_elem)"; first done.
        iSplitL; last iSteps.
        iExists l, γ, 1, root, ς. iFrame "#∗". iStep 2. iSplitR.
        { iPureIntro. split; first set_solver.
          eapply map_Forall_impl; first done. naive_solver.
        }
        iStep. iExists root, descr. iSplitR.
        { iPureIntro. rewrite lookup_insert //. }
        iStep. iSplitL.
        { iStep 2. iExists [], []. iSteps.
          - rewrite NoDup_nil //.
          - rewrite deltas_apply_nil //.
        }
        rewrite insert_empty delete_singleton.
        iApply (big_sepM_empty with "[//]").
      - iDestruct "Hmodel" as "(%cnodes & %base & %base_descr & Hcnodes_auth & %Hcnodes_lookup_base & %Hbase_gen & ((%Hbase_store_dom & %Hbase_store_gen) & #Hcnodes_elem_base & %nodes & %δs & %Hδs_nodup & %Hδs_gen & %Hδs & Hδs) & Hcnodes)".
        destruct δs as [| δ δs].
        + iDestruct (deltas_chain_nil_inv with "Hδs") as %(-> & <-).
          iSplitL; iSteps.
          { iPureIntro. eapply map_Forall_impl; first done. naive_solver lia. }
          rewrite decide_False; first lia.
          iSteps. iExists []. iSteps.
        + iAssert ⌜cnodes !! root = None⌝%I as %Hcnodes_lookup_root.
          { destruct (decide (root = base)) as [-> | Hcase].
            - iDestruct (deltas_chain_cons_inv with "Hδs") as "(%node & %nodes' & -> & Hbase & _)".
              iDestruct (pointsto_ne with "Hroot Hbase") as %?. done.
            - rewrite -eq_None_ne_Some. iIntros "%descr %Hcnodes_lookup".
              iDestruct (big_sepM_lookup with "Hcnodes") as "(%cnode' & %descr' & _ & _ & _ & %nodes' & %δs' & _ & %Hδs'_length & _ & Hδs')".
              { rewrite lookup_delete_Some //. }
              destruct δs' as [| δ' δs']; first naive_solver lia.
              iDestruct (deltas_chain_cons_inv with "Hδs'") as "(%node & %nodes'' & -> & _Hroot & _)".
              iDestruct (pointsto_ne with "Hroot _Hroot") as %?. done.
          }
          pose root_descr := (g, ς).
          iMod (cnodes_insert root root_descr with "Hcnodes_auth") as "(Hcnodes_auth & #Hcnodes_elem_root)"; first done.
          iSplitL; last iSteps.
          iExists l, γ, (S g), root, ς. iFrame "#∗". iSteps as (_ | _) "" | "".
          { iPureIntro. eapply map_Forall_impl; first done. naive_solver. }
          iExists root, root_descr. iSplitR.
          { rewrite lookup_insert //. }
          iStep. iSplitR.
          { iStep 2. iExists [], []. iSteps; iPureIntro.
            - rewrite NoDup_nil //.
            - rewrite deltas_apply_nil //.
          }
        rewrite delete_insert //. iApply big_sepM_delete; first done.
        iSteps. iExists root, root_descr. iSteps.
        { iPureIntro. rewrite lookup_insert //. }
        iApply (big_sepM_impl with "Hcnodes"). iIntros "!> !> %cnode %descr %Hcnodes_lookup_cnode (%cnode' & %descr' & %Hcnodes_lookup_cnode' & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Hcnodes_elem_cnode & %nodes' & %δs' & %Hδs'_nodup & %Hδs'_length & %Hδs' & Hδs'))".
        iSteps. iExists cnode', descr'. iSteps. iPureIntro.
        rewrite lookup_insert_ne //. congruence.
    Qed.

    Lemma store_restore_spec t σ0 σ s σ' :
      {{{
        store_model t σ0 σ ∗
        store_snapshot_model s t σ'
      }}}
        store_restore t s
      {{{
        RET ();
        store_model t σ0 σ'
      }}}.
    Proof.
    Admitted.
  End store_G.

  #[global] Opaque store_model.
  #[global] Opaque store_snapshot_model.
End raw.

#[global] Opaque store_create.
#[global] Opaque store_ref.
#[global] Opaque store_get.
#[global] Opaque store_set.
#[global] Opaque store_capture.
#[global] Opaque store_restore.

Class StoreG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] store_G_raw_G :: raw.StoreG Σ ;
  #[local] store_G_support_G :: MonoMapG Σ loc val ;
}.

Definition store_Σ := #[
  raw.store_Σ ;
  mono_map_Σ loc val
].
Lemma subG_store_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG store_Σ Σ →
  StoreG Σ.
Proof.
  solve_inG.
Qed.

Section store_G.
  Context `{store_G : StoreG Σ}.

  Definition store_model t σ : iProp Σ :=
    ∃ l γ σ0 ς,
    ⌜t = #l⌝ ∗
    ⌜σ ⊆ ς ∪ σ0⌝ ∗
    meta l (nroot.@"user") γ ∗
    mono_map_auth γ σ0 ∗
    raw.store_model t σ0 ς.

  Definition store_snapshot_model s t σ : iProp Σ :=
    ∃ l γ σ0 ς,
    ⌜t = #l⌝ ∗
    ⌜σ ⊆ ς ∪ σ0⌝ ∗
    meta l (nroot.@"user") γ ∗
    mono_map_lb γ σ0 ∗
    raw.store_snapshot_model s t ς.

  (* #[global] Instance store_model_timeless t σ : *)
  (*   Timeless (store_model t σ). *)
  (* Proof. *)
  (*   apply _. *)
  (* Qed. *)
  #[global] Instance store_snapshot_persistent s t σ :
    Persistent (store_snapshot_model s t σ).
  Proof.
    apply _.
  Qed.

  Lemma store_create_spec :
    {{{ True }}}
      store_create ()
    {{{ t,
      RET t;
      store_model t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd.
    wp_apply (raw.store_create_spec with "[//]") as (t) "((%l & -> & Hmeta) & Ht)".
    iMod mono_map_alloc as "(%γ & Hauth)".
    iMod (meta_set with "Hmeta") as "Hmeta"; first done.
    iSteps. iExists ∅, ∅. iSteps.
  Qed.

  Lemma store_ref_spec t σ v :
    {{{
      store_model t σ
    }}}
      store_ref t v
    {{{ r,
      RET #r;
      ⌜σ !! r = None⌝ ∗
      store_model t (<[r := v]> σ)
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (raw.store_model_valid with "Ht") as %Hς_dom.
    iApply wp_fupd.
    wp_apply (raw.store_ref_spec with "Ht") as (r) "(%Hσ0_lookup & Ht)".
    assert (ς !! r = None) as Hς_lookup.
    { rewrite -!not_elem_of_dom in Hσ0_lookup |- *. set_solver. }
    assert (σ !! r = None) as Hσ_lookup.
    { eapply lookup_weaken_None; last done. apply lookup_union_None_2; done. }
    iMod (mono_map_insert with "Hauth") as "Hauth"; first done.
    iApply "HΦ".
    iStep. iExists l, γ, (<[r := v]> σ0), ς. iSteps. iPureIntro.
    rewrite -insert_union_r //. apply insert_mono. done.
  Qed.

  Lemma store_get_spec {t σ r} v :
    σ !! r = Some v →
    {{{
      store_model t σ
    }}}
      store_get t #r
    {{{
      RET v;
      store_model t σ
    }}}.
  Proof.
    iIntros "%Hσ_lookup %Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    wp_apply (raw.store_get_spec with "Ht") as "Ht".
    { eapply lookup_weaken; done. }
    iSteps.
  Qed.

  Lemma store_set_spec t σ r v :
    r ∈ dom σ →
    {{{
      store_model t σ
    }}}
      store_set t #r v
    {{{
      RET ();
      store_model t (<[r := v]> σ)
    }}}.
  Proof.
    iIntros "%Hr %Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (raw.store_model_valid with "Ht") as %Hς_dom.
    wp_apply (raw.store_set_spec with "Ht") as "Ht".
    { apply subseteq_dom in Hσ. set_solver. }
    iApply "HΦ".
    iExists l, γ, σ0, (<[r := v]> ς). iSteps. iPureIntro.
    rewrite -insert_union_l. apply insert_mono. done.
  Qed.

  Lemma store_capture_spec t σ :
    {{{
      store_model t σ
    }}}
      store_capture t
    {{{ s,
      RET s;
      store_model t σ ∗
      store_snapshot_model s t σ
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (mono_map_lb_get with "Hauth") as "#Hlb".
    wp_apply (raw.store_capture_spec with "Ht") as (s) "(Ht & Hs)".
    iSteps.
  Qed.

  Lemma store_restore_spec t σ s σ' :
    {{{
      store_model t σ ∗
      store_snapshot_model s t σ'
    }}}
      store_restore t s
    {{{
      RET ();
      store_model t σ'
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) & (%_l & %_γ & %σ0' & %ς' & %Heq & %Hσ' & _Hmeta & #Hlb & Hs)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_apply (raw.store_restore_spec with "[$Ht $Hs]") as "Ht".
    iDestruct (mono_map_valid with "Hauth Hlb") as %Hσ0'.
    iApply "HΦ".
    iExists l, γ, σ0, ς'. iSteps. iPureIntro.
    trans (ς' ∪ σ0'); first done. apply map_union_mono_l. done.
  Qed.
End store_G.

#[global] Opaque store_model.
#[global] Opaque store_snapshot_model.
