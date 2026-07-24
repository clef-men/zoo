Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.fin_maps.
Require Import zoo.common.list.
Require Import zoo.common.treemap.
Require Import zoo.iris.base_logic.lib.mono_gmap.
Require Import zoo.base.
Require Import zoo_std.assert.
Require Import zoo_std.list.
Require Export zoo_persistent.sstore_2__code.
Require Import zoo_persistent.sstore_2__types.
Require Import zoo.options.

Implicit Type l r node cnode base root dst : location.
Implicit Type nodes : list location.
Implicit Type v t s : val.
Implicit Type σ σ₀ : gmap location val.

Module base.
  #[local] Definition generation :=
    nat.
  Implicit Type g : generation.

  #[local] Notation "data '.(gen)'" := (
    fst data
  )(at level 2,
    left associativity,
    format "data .(gen)"
  ) : stdpp_scope.
  #[local] Notation "data '.(val)'" := (
    snd data
  )(at level 2,
    left associativity,
    format "data .(val)"
  ) : stdpp_scope.

  #[local] Definition store :=
    gmap location (generation * val).
  Implicit Type ς : store.
  Implicit Type data : generation * val.

  Record descriptor := Descriptor
    { descriptor۰gen : generation
    ; descriptor۰store : store
    }.
  Add Printing Constructor descriptor.
  Implicit Type descr : descriptor.
  Implicit Type cnodes : gmap location descriptor.

  Class Sstore2G Σ `{zoo۰G : !ZooG Σ} :=
    { #[local] sstore_2۰G۰nodes۰G :: ghost_mapG Σ location descriptor
    }.

  Definition sstore_2۰Σ :=
    #[ghost_mapΣ location descriptor
    ].
  #[global] Instance subG𑁒sstore_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
    subG sstore_2۰Σ Σ →
    Sstore2G Σ.
  Proof.
    solve_inG.
  Qed.

  Section sstore_2۰G.
    Context `{sstore_2۰G : Sstore2G Σ}.

    #[local] Definition metadata :=
      gname.
    Implicit Type γ : metadata.

    #[local] Definition store۰on σ₀ ς :=
      ς ∪ (pair 0 <$> σ₀).
    #[local] Definition store۰generation g ς :=
      map_Forall (λ r data, data.(gen) ≤ g) ς.

    #[local] Definition descriptor۰wf σ₀ descr :=
      dom descr.(descriptor۰store) ⊆ dom σ₀ ∧
      store۰generation descr.(descriptor۰gen) descr.(descriptor۰store).

    Record delta := Delta
      { delta۰ref : location
      ; delta۰gen : generation
      ; delta۰val : val
      ; delta۰node : location
      }.
    Add Printing Constructor delta.
    Implicit Type δ : delta.
    Implicit Type δs : list delta.
    Implicit Type path : list (list delta).

    #[local] Notation "δ '.(delta۰data)'" := (
      pair δ.(delta۰gen) δ.(delta۰val)
    )(at level 2,
      left associativity,
      format "δ .(delta۰data)"
    ) : stdpp_scope.

    #[local] Definition delta۰patch δ :=
      (δ.(delta۰ref), δ.(delta۰data)).

    #[local] Definition deltas۰apply δs ς :=
      list_to_map (delta۰patch <$> δs) ∪ ς.
    #[local] Fixpoint deltas۰chain node δs dst : iProp Σ :=
      match δs with
      | [] =>
          ⌜node = dst⌝
      | δ :: δs =>
          node ↦ᵣ ‘Diff( #δ.(delta۰ref), #δ.(delta۰gen), δ.(delta۰val), #δ.(delta۰node) ) ∗
          deltas۰chain δ.(delta۰node) δs dst
      end.

    #[local] Definition edge : Set :=
      location * list delta.
    Implicit Type ϵ : edge.
    Implicit Type ϵs : gmap location edge.

    #[local] Definition cnodes۰auth γ cnodes :=
      ghost_map_auth γ 1 cnodes.
    #[local] Definition cnodes۰elem γ cnode descr :=
      ghost_map_elem γ cnode DfracDiscarded descr.

    #[local] Definition cnode۰model γ σ₀ cnode descr ϵ ς : iProp Σ :=
      let cnode' := ϵ.1 in
      let δs := ϵ.2 in
      ⌜descriptor۰wf σ₀ descr⌝ ∗
      cnodes۰elem γ cnode descr ∗
      ⌜NoDup $ delta۰ref <$> δs⌝ ∗
      ⌜store۰on σ₀ descr.(descriptor۰store) = store۰on σ₀ $ deltas۰apply δs ς⌝ ∗
      deltas۰chain cnode δs cnode'.
    Definition sstore_2۰model t σ₀ σ : iProp Σ :=
      ∃ l γ g root ς,
      ⌜t = #l⌝ ∗
      ⌜σ = snd <$> ς⌝ ∗
      l ↪[nroot.@"impl"] γ ∗
      l.[gen] ↦ #g ∗
      l.[root] ↦ #root ∗
      root ↦ᵣ §Root ∗
      ( [∗ map] r ↦ data ∈ store۰on σ₀ ς,
        r.[ref_gen] ↦ #data.(gen) ∗
        r.[ref_value] ↦ data.(val)
      ) ∗
      ⌜descriptor۰wf σ₀ (Descriptor g ς)⌝ ∗
      if decide (g = 0) then
        cnodes۰auth γ ∅
      else
        ∃ cnodes ϵs base descr δs,
        ⌜treemap۰rooted ϵs base⌝ ∗
        cnodes۰auth γ cnodes ∗
        (* [base] cnode *)
        ⌜cnodes !! base = Some descr⌝ ∗
        ⌜descr.(descriptor۰gen) < g⌝ ∗
        cnode۰model γ σ₀ base descr (root, δs) ς ∗
        ⌜δs = [] → ς = descr.(descriptor۰store)⌝ ∗
        ⌜Forall (λ δ, ∃ data, ς !! δ.(delta۰ref) = Some data ∧ data.(gen) = g) δs⌝ ∗
        (* other cnodes *)
        [∗ map] cnode ↦ descr; ϵ ∈ delete base cnodes; ϵs,
          ∃ descr',
          ⌜cnodes !! ϵ.1 = Some descr'⌝ ∗
          cnode۰model γ σ₀ cnode descr ϵ descr'.(descriptor۰store).

    Definition sstore_2۰snapshot s t σ : iProp Σ :=
      ∃ l γ g cnode descr,
      ⌜t = #l⌝ ∗
      ⌜s = (t, #g, #cnode)%V⌝ ∗
      ⌜σ = snd <$> descr.(descriptor۰store)⌝ ∗
      ⌜descr.(descriptor۰gen) ≤ g⌝ ∗
      l ↪[nroot.@"impl"] γ ∗
      cnodes۰elem γ cnode descr.

    #[local] Instance deltas۰chain𑁒timeless node δs dst :
      Timeless (deltas۰chain node δs dst).
    Proof.
      move: node. induction δs; apply _.
    Qed.
    #[global] Instance sstore_2۰model𑁒timeless t σ₀ σ :
      Timeless (sstore_2۰model t σ₀ σ).
    Proof.
      rewrite /Timeless. iIntros "(%l & %γ & %g & H)".
      iExists l, γ, g.
      case_decide; iApply (timeless with "H").
    Qed.

    #[global] Instance sstore_2۰snapshot𑁒persistent s t σ :
      Persistent (sstore_2۰snapshot s t σ).
    Proof.
      apply _.
    Qed.

    #[local] Lemma store۰on𑁒dom σ₀ ς :
      dom (store۰on σ₀ ς) = dom σ₀ ∪ dom ς.
    Proof.
      set_solver.
    Qed.
    #[local] Lemma store۰on𑁒dom' σ₀ ς :
      dom ς ⊆ dom σ₀ →
      dom (store۰on σ₀ ς) = dom σ₀.
    Proof.
      set_solver.
    Qed.
    #[local] Lemma store۰on𑁒lookup {σ₀ ς} r data :
      store۰on σ₀ ς !! r = Some data ↔
          ς !! r = Some data
        ∨ ς !! r = None ∧
          data.(gen) = 0 ∧
          σ₀ !! r = Some data.(val).
    Proof.
      destruct data as (g, v).
      rewrite lookup_union_Some_raw lookup_fmap_Some. naive_solver.
    Qed.
    #[local] Lemma store۰on𑁒lookup' {σ₀ ς} r data :
      ς !! r = Some data →
      store۰on σ₀ ς !! r = Some data.
    Proof.
      apply lookup_union_Some_l.
    Qed.
    #[local] Lemma store۰on𑁒insert r data σ₀ ς :
      store۰on σ₀ (<[r := data]> ς) = <[r := data]> (store۰on σ₀ ς).
    Proof.
      rewrite insert_union_l //.
    Qed.
    #[local] Lemma store۰on𑁒insert𑁒support r v σ₀ ς :
      σ₀ !! r = None →
      dom ς ⊆ dom σ₀ →
      store۰on (<[r := v]> σ₀) ς = <[r := (0, v)]> (store۰on σ₀ ς).
    Proof.
      intros Hr%not_elem_of_dom Hς_dom.
      assert (ς !! r = None).
      { apply not_elem_of_dom. set_solver. }
      rewrite insert_union_r // -fmap_insert //.
    Qed.
    #[local] Lemma store۰on𑁒deltas۰apply σ₀ δs ς :
      store۰on σ₀ (deltas۰apply δs ς) = deltas۰apply δs (store۰on σ₀ ς).
    Proof.
      rewrite /deltas۰apply assoc //.
    Qed.

    #[local] Lemma store۰generation𑁒le {g ς} g' :
      g ≤ g' →
      store۰generation g ς →
      store۰generation g' ς.
    Proof.
      intros Hg Hς_gen.
      eapply map_Forall_impl; first done.
      naive_solver lia.
    Qed.
    #[local] Lemma store۰generation𑁒insert g ς r data :
      store۰generation g ς →
      data.(gen) ≤ g →
      store۰generation g (<[r := data]> ς).
    Proof.
      intros Hς_gen ?.
      apply map_Forall_insert_2; done.
    Qed.

    #[local] Lemma deltas۰apply𑁒nil ς :
      deltas۰apply [] ς = ς.
    Proof.
      rewrite /deltas۰apply list_to_map_nil left_id //.
    Qed.
    #[local] Lemma deltas۰apply𑁒cons δ δs ς :
      deltas۰apply (δ :: δs) ς = <[δ.(delta۰ref) := δ.(delta۰data)]> (deltas۰apply δs ς).
    Proof.
      destruct δ as (r, gen, v, node).
      rewrite /deltas۰apply list_to_map_cons insert_union_l //.
    Qed.
    #[local] Lemma deltas۰apply𑁒singleton δ ς :
      deltas۰apply [δ] ς = <[δ.(delta۰ref) := δ.(delta۰data)]> ς.
    Proof.
      rewrite deltas۰apply𑁒cons deltas۰apply𑁒nil //.
    Qed.
    #[local] Lemma deltas۰apply𑁒app δs1 δs2 ς :
      deltas۰apply (δs1 ++ δs2) ς = deltas۰apply δs1 (deltas۰apply δs2 ς).
    Proof.
      rewrite /deltas۰apply fmap_app list_to_map_app assoc //.
    Qed.
    #[local] Lemma deltas۰apply𑁒snoc δs δ ς :
      deltas۰apply (δs ++ [δ]) ς = deltas۰apply δs (<[δ.(delta۰ref) := δ.(delta۰data)]> ς).
    Proof.
      rewrite deltas۰apply𑁒app deltas۰apply𑁒singleton //.
    Qed.
    #[local] Lemma deltas۰apply𑁒snoc' δs r g v node ς :
      deltas۰apply (δs ++ [Delta r g v node]) ς = deltas۰apply δs (<[r := (g, v)]> ς).
    Proof.
      apply (deltas۰apply𑁒snoc _ (Delta r g v node)).
    Qed.
    #[local] Lemma deltas۰apply𑁒dom δs ς :
      dom (deltas۰apply δs ς) = list_to_set (delta۰ref <$> δs) ∪ dom ς.
    Proof.
      rewrite dom_union_L dom_list_to_map_L -list_fmap_compose //.
    Qed.
    #[local] Lemma deltas۰apply𑁒lookup δs δ r data ς :
      NoDup (delta۰ref <$> δs) →
      δ ∈ δs →
      r = δ.(delta۰ref) →
      data = δ.(delta۰data) →
      deltas۰apply δs ς !! r = Some data.
    Proof.
      intros Hδs_nodup Hδ -> ->.
      apply lookup_union_Some_l, elem_of_list_to_map_1.
      - rewrite -list_fmap_compose //.
      - rewrite list_elem_of_fmap. eauto.
    Qed.
    #[local] Lemma deltas۰apply𑁒lookup' δs r data ς :
      NoDup (delta۰ref <$> δs) →
      (r, data) ∈ delta۰patch <$> δs →
      deltas۰apply δs ς !! r = Some data.
    Proof.
      intros Hδs_nodup ((_r, g, v, node) & [= ] & Hδ)%list_elem_of_fmap.
      eapply deltas۰apply𑁒lookup; done.
    Qed.
    #[local] Lemma deltas۰apply۰lookup𑁒ne r δs ς :
      NoDup (delta۰ref <$> δs) →
      r ∉ (delta۰ref <$> δs) →
      deltas۰apply δs ς !! r = ς !! r.
    Proof.
      intros Hδs_nodup Hr.
      apply lookup_union_r, not_elem_of_list_to_map_1.
      rewrite -list_fmap_compose //.
    Qed.
    #[local] Lemma deltas۰apply𑁒permutation δs1 δs2 ς :
      NoDup (delta۰ref <$> δs1) →
      δs1 ≡ₚ δs2 →
      deltas۰apply δs1 ς = deltas۰apply δs2 ς.
    Proof.
      intros. rewrite /deltas۰apply (list_to_map_proper _ (delta۰patch <$> δs2)) //.
      { rewrite -list_fmap_compose //. }
      { f_equiv. done. }
    Qed.

    #[local] Lemma deltas۰chain𑁒cons src δ δs dst :
      src ↦ᵣ ‘Diff( #δ.(delta۰ref), #δ.(delta۰gen), δ.(delta۰val), #δ.(delta۰node) ) -∗
      deltas۰chain δ.(delta۰node) δs dst -∗
        deltas۰chain src (δ :: δs) dst.
    Proof.
      iSteps.
    Qed.
    #[local] Lemma deltas۰chain𑁒nil𑁒inv src dst :
      deltas۰chain src [] dst ⊢
      ⌜src = dst⌝.
    Proof.
      iSteps.
    Qed.
    #[local] Lemma deltas۰chain𑁒cons𑁒inv src δ δs dst :
      deltas۰chain src (δ :: δs) dst ⊢
        src ↦ᵣ ‘Diff( #δ.(delta۰ref), #δ.(delta۰gen), δ.(delta۰val), #δ.(delta۰node) ) ∗
        deltas۰chain δ.(delta۰node) δs dst.
    Proof.
      iSteps.
    Qed.
    #[local] Lemma deltas۰chain𑁒snoc {src δs dst} r g v dst' :
      deltas۰chain src δs dst -∗
      dst ↦ᵣ ‘Diff( #r, #g, v, #dst' ) -∗
      deltas۰chain src (δs ++ [Delta r g v dst']) dst'.
    Proof.
      iInduction δs as [] "IH" forall (src); iSteps.
    Qed.
    #[local] Lemma deltas۰chain𑁒app₁ src δs1 δs2 dst :
      deltas۰chain src (δs1 ++ δs2) dst ⊢
        let node := default src $ delta۰node <$> last δs1 in
        deltas۰chain src δs1 node ∗
        deltas۰chain node δs2 dst.
    Proof.
      iIntros "Hδs".
      iInduction δs1 as [| δ1 δs1] "IH" forall (src); first iSteps.
      iDestruct "Hδs" as "(Hsrc & Hδs)".
      iDestruct ("IH" with "Hδs") as "(Hδs1 & Hδs2)".
      destruct δs1 as [| δ1' δs1]; first iSteps.
      rewrite last_cons_cons.
      assert (is_Some (last (δ1' :: δs1))) as (? & Heq).
      { rewrite last_is_Some //. }
      rewrite -> Heq in *. iSteps.
    Qed.
    #[local] Lemma deltas۰chain𑁒app₂ src δs1 node δs2 dst :
      deltas۰chain src δs1 node -∗
      deltas۰chain node δs2 dst -∗
      deltas۰chain src (δs1 ++ δs2) dst.
    Proof.
      iIntros "Hδs1 Hδs2".
      iInduction δs1 as [] "IH" forall (src); last iSteps.
      iDestruct "Hδs1" as %<-. iSteps.
    Qed.
    #[local] Lemma deltas۰chain𑁒snoc𑁒inv src δs δ dst :
      deltas۰chain src (δs ++ [δ]) dst ⊢
        let node := default src $ delta۰node <$> last δs in
        ⌜δ.(delta۰node) = dst⌝ ∗
        deltas۰chain src δs node ∗
        node ↦ᵣ ‘Diff( #δ.(delta۰ref), #δ.(delta۰gen), δ.(delta۰val), #dst ).
    Proof.
      rewrite deltas۰chain𑁒app₁. iSteps.
    Qed.
    #[local] Lemma deltas۰chain𑁒lookup {src δs dst} i δ :
      δs !! i = Some δ →
      deltas۰chain src δs dst ⊢
        deltas۰chain src (take ˖i δs) δ.(delta۰node) ∗
        deltas۰chain δ.(delta۰node) (drop ˖i δs) dst.
    Proof.
      iIntros "%δs_lookup Hδs".
      rewrite -{1}(take_drop ˖i δs).
      iDestruct (deltas۰chain𑁒app₁ with "Hδs") as "Hδs".
      rewrite {2 3}(take_S_r δs i δ) // last_snoc //.
    Qed.
    #[local] Lemma deltas۰chain𑁒lookup' {src δs dst} i δ :
      δs !! i = Some δ →
      deltas۰chain src δs dst ⊢
        ∃ node,
        ⌜ if i is 0 then
            node = src
          else
            ∃ δ',
            δs !! pred i = Some δ' ∧
            δ'.(delta۰node) = node
        ⌝ ∗
        deltas۰chain src (take i δs) node ∗
        node ↦ᵣ ‘Diff( #δ.(delta۰ref), #δ.(delta۰gen), δ.(delta۰val), #δ.(delta۰node) ) ∗
        deltas۰chain δ.(delta۰node) (drop ˖i δs) dst.
    Proof.
      iIntros "%Hδs_lookup Hδs".
      iDestruct (deltas۰chain𑁒lookup with "Hδs") as "(Hδs1 & Hδs2)"; first done.
      rewrite (take_S_r δs i δ) //.
      destruct i; simpl; first iSteps.
      iDestruct (deltas۰chain𑁒snoc𑁒inv with "Hδs1") as "(_ & Hδs1 & Hδ)".
      opose proof* (lookup_lt_is_Some_2 δs i) as (δ' & Hδs_lookup').
      { apply lookup_lt_Some in Hδs_lookup. lia. }
      rewrite {2 3}(take_S_r δs i δ') // last_snoc.
      iSteps.
    Qed.

    #[local] Definition cnodes𑁒alloc root :
      ⊢ |==>
        ∃ γ,
        cnodes۰auth γ ∅.
    Proof.
      iMod ghost_map_alloc as "(%γ & Hauth & _)".
      iSteps.
    Qed.
    #[local] Definition cnodes𑁒lookup γ cnodes cnode descr :
      cnodes۰auth γ cnodes -∗
      cnodes۰elem γ cnode descr -∗
      ⌜cnodes !! cnode = Some descr⌝.
    Proof.
      apply ghost_map_lookup.
    Qed.
    #[local] Lemma cnodes𑁒insert {γ cnodes} cnode descr :
      cnodes !! cnode = None →
      cnodes۰auth γ cnodes ⊢ |==>
        cnodes۰auth γ (<[cnode := descr]> cnodes) ∗
        cnodes۰elem γ cnode descr.
    Proof.
      iIntros "%Hcnodes_lookup Hauth".
      iMod (ghost_map_insert with "Hauth") as "($ & Helem)"; first done.
      iApply (ghost_map_elem_persist with "Helem").
    Qed.

    Lemma sstore_2۰model𑁒valid t σ₀ σ :
      sstore_2۰model t σ₀ σ ⊢
      ⌜dom σ ⊆ dom σ₀⌝.
    Proof.
      iIntros "(%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & _)".
      rewrite dom_fmap //.
    Qed.
    Lemma sstore_2۰model𑁒exclusive t σ₀1 σ1 σ₀2 σ2 :
      sstore_2۰model t σ₀1 σ1 -∗
      sstore_2۰model t σ₀2 σ2 -∗
      False.
    Proof.
      iIntros "(%l1 & %γ1 & %g1 & %root1 & %ς1 & %Heq1 & -> & _ & Hl_gen_1 & _) (%l2 & %γ2 & %g2 & %root2 & %ς2 & %Heq2 & -> & _ & Hl_gen_2 & _)". simplify.
      iApply (pointsto𑁒exclusive with "Hl_gen_1 Hl_gen_2").
    Qed.

    Lemma sstore_2٠create𑁒spec :
      {{{
        True
      }}}
        sstore_2٠create ()
      {{{
        t
      , RET t;
        (∃ l, ⌜t = #l⌝ ∗ meta_token l (↑nroot.@"user")) ∗
        sstore_2۰model t ∅ ∅
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰ref root as "Hroot".
      wp۰block l as "Hmeta" "(Hl_gen & Hl_root & _)".

      iMod (cnodes𑁒alloc root) as "(%γ & Hauth)".

      iDestruct (meta_token𑁒difference (↑nroot.@"user") with "Hmeta") as "(Hmeta_user & Hmeta)"; first done.
      iDestruct (meta_token𑁒difference (↑nroot.@"impl") with "Hmeta") as "(Hmeta & _)"; first solve_ndisj.
      iMod (meta𑁒set γ with "Hmeta") as "Hmeta"; first done.

      iApply "HΦ".
      iStep. iExists l, γ, 0, root, ∅. iFrame. rewrite big_sepM_empty. iSteps.
    Qed.

    Lemma sstore_2٠ref𑁒spec t σ₀ σ v :
      {{{
        sstore_2۰model t σ₀ σ
      }}}
        sstore_2٠ref t v
      {{{
        r
      , RET #r;
        ⌜σ₀ !! r = None⌝ ∗
        sstore_2۰model t (<[r := v]> σ₀) σ
      }}}.
    Proof.
      iIntros "%Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".

      wp۰rec. wp۰block r as "(Hr_gen & Hr_value & _)".
      iAssert ⌜σ₀ !! r = None⌝%I as %Hr.
      { rewrite -not_elem_of_dom. iIntros "%Hr".
        iDestruct (big_sepM_lookup with "Hς") as "(_Hr_gen & _)".
        { apply lookup_lookup_total_dom. rewrite store۰on𑁒dom' //. }
        iApply (pointsto𑁒exclusive with "Hr_gen _Hr_gen").
      }
      iApply "HΦ".
      iSplitR; first iSteps. iExists l, γ, g, root, ς. iFrame "#∗". iStep 2.
      iSplitL "Hς Hr_gen Hr_value".
      { rewrite store۰on𑁒insert𑁒support //.
        iApply (big_sepM_insert_2 with "[Hr_gen Hr_value] Hς").
        iSteps.
      }
      iSplitR. { iPureIntro. split; [set_solver | done]. }
      case_decide as [-> | Hg]. 1: iSteps.
      iDecompose "Hmodel" as (cnodes ϵs base descr δs Hϵs Hcnodes_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hcnodes".
      iSteps; try iPureIntro.
      { rewrite /descriptor۰wf. set_solver. }
      { rewrite !store۰on𑁒insert𑁒support //; last congruence.
        apply (f_equal dom) in Hδs. set_solver.
      } {
        iClear "Helem_base". clear dependent descr δs.
        iApply (big_sepM2_impl with "Hcnodes"). iIntros "!> !>" (cnode descr (cnode' & δs)) "%Hcnodes_lookup %Hϵs_lookup (%descr' & %Hcnodes_lookup' & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_nodup & %Hδs' & Hδs'))".
        simpl in *.
        iSteps; iPureIntro.
        - rewrite /descriptor۰wf. set_solver.
        - rewrite !store۰on𑁒insert𑁒support //; last congruence.
          apply (f_equal dom) in Hδs'. set_solver.
      }
    Qed.

    Lemma sstore_2٠get𑁒spec {t σ₀ σ r} v :
      (σ ∪ σ₀) !! r = Some v →
      {{{
        sstore_2۰model t σ₀ σ
      }}}
        sstore_2٠get t #r
      {{{
        RET v;
        sstore_2۰model t σ₀ σ
      }}}.
    Proof.
      iIntros "%Hσ_lookup %Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".

      wp۰rec.
      assert (∃ g_r, store۰on σ₀ ς !! r = Some (g_r, v)) as (g_r & Hς_lookup).
      { setoid_rewrite store۰on𑁒lookup.
        apply lookup_union_Some_raw in Hσ_lookup as [Hσ_lookup | (Hσ_lookup & Hσ₀_lookup)].
        - apply lookup_fmap_Some in Hσ_lookup as ((g_r & _v) & ? & Hς_lookup).
          naive_solver.
        - rewrite lookup𑁒fmap𑁒None in Hσ_lookup.
          naive_solver.
      }
      iDestruct (big_sepM_lookup_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
      wp۰load.
      iSteps.
    Qed.

    Lemma sstore_2٠set𑁒spec t σ₀ σ r v :
      r ∈ dom σ₀ →
      {{{
        sstore_2۰model t σ₀ σ
      }}}
        sstore_2٠set t #r v
      {{{
        RET ();
        sstore_2۰model t σ₀ (<[r := v]> σ)
      }}}.
    Proof.
      iIntros "%Hr %Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".
      pose proof Hr as (w0 & Hσ₀_lookup)%elem_of_dom.

      wp۰rec. wp۰load.
      assert (∃ g_r w, store۰on σ₀ ς !! r = Some (g_r, w) ∧ g_r ≤ g) as (g_r & w & Hς_lookup & Hg_r).
      { setoid_rewrite store۰on𑁒lookup.
        destruct (ς !! r) as [(g_r, w) |] eqn:Hς_lookup.
        - exists g_r, w. split; first naive_solver.
          opose proof* map_Forall_lookup_1; done.
        - exists 0, w0. split; first naive_solver. lia.
      }
      iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
      wp۰load. wp۰pures.
      destruct_decide (g = 0) as -> | Hg.

      - assert (g_r = 0) as -> by lia.
        rewrite bool_decide_eq_true_2 //. wp۰pures.
        wp۰store.
        iDestruct ("Hς" $! (0, v) with "[$Hr_gen $Hr_value]") as "Hς".
        iApply "HΦ".
        iExists l, γ, 0, root, (<[r := (0, v)]> ς). iFrame "#∗". iStep.
        iSplitR. { rewrite fmap_insert //. }
        iSplitL. { rewrite insert_union_l //. }
        iPureIntro. split; first set_solver. apply map_Forall_insert_2; done.

      - destruct_decide (g = g_r) as <- | Hcase.

        + rewrite bool_decide_eq_true_2 //.
          wp۰store.
          iDestruct ("Hς" $! (g, v) with "[$Hr_gen $Hr_value]") as "Hς".
          iApply "HΦ".
          iExists l, γ, g, root, (<[r := (g, v)]> ς). iFrame "#∗". iStep.
          iSplitR. { rewrite fmap_insert //. }
          iSplitL "Hς". { rewrite insert_union_l //. }
          iSplitR. { iPureIntro. split; first set_solver. apply map_Forall_insert_2; done. }
          rewrite decide_False //.
          iDecompose "Hmodel" as (cnodes ϵs base descr δs Hϵs Hcnodes_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hcnodes".
          iSteps; iPureIntro.
          { clear Hδs_nil Hδs_gen. generalize dependent ς.
            induction δs as [| (r', g', v', node') δs IH] using rev_ind.
            all: intros ς Hς_dom Hς_gen Hς_lookup Hδs.
            - exfalso.
              rewrite deltas۰apply𑁒nil in Hδs.
              rewrite -Hδs store۰on𑁒lookup in Hς_lookup.
              destruct Hς_lookup as [Hstore_lookup |]; last naive_solver.
              opose proof* (map_Forall_lookup_1 _ descr.(descriptor۰store)); [done.. |].
              naive_solver lia.
            - rewrite deltas۰apply𑁒snoc /=.
              destruct_decide (r = r') as <- | Hr'.
              + rewrite deltas۰apply𑁒snoc /= in Hδs.
                rewrite insert_insert_eq //.
              + rewrite insert_insert_ne //.
                apply IH; simpl.
                * rewrite fmap_app NoDup_app in Hδs_nodup. naive_solver.
                * rewrite dom_insert union_subseteq singleton_subseteq_l.
                  split; last done.
                  apply (f_equal dom) in Hδs.
                  rewrite store۰on𑁒dom' // store۰on𑁒dom in Hδs.
                  rewrite Hδs deltas۰apply𑁒dom. set_solver.
                * apply map_Forall_insert_2; last done.
                  trans descr.(descriptor۰gen); last lia.
                  assert (store۰on σ₀ descr.(descriptor۰store) !! r' = Some (g', v')) as [Hstore_lookup | (_ & ? & _)]%store۰on𑁒lookup.
                  { rewrite Hδs.
                    apply store۰on𑁒lookup', deltas۰apply𑁒lookup'; first done.
                    rewrite fmap_app. set_solver.
                  }
                  -- eapply map_Forall_lookup_1 in Hstore_gen; done.
                  -- simpl in *. lia.
                * rewrite /store۰on -insert_union_l lookup_insert_ne //.
                * rewrite deltas۰apply𑁒snoc // in Hδs.
          } {
            intros ->. specialize (Hδs_nil eq_refl) as ->.
            exfalso.
            apply store۰on𑁒lookup in Hς_lookup as [].
            - opose proof* map_Forall_lookup_1; [done.. |].
              naive_solver lia.
            - naive_solver lia.
          } {
            eapply Forall_impl; first done. intros (r', g', v', node) H.
            destruct_decide (r = r') as <- | Hr'.
            - rewrite lookup_insert_eq. naive_solver.
            - rewrite lookup_insert_ne //.
          }

        + rewrite bool_decide_eq_false_2; first naive_solver. wp۰pures.
          wp۰ref root' as "Hroot'". do 2 wp۰load. do 4 wp۰store.
          iDestruct ("Hς" $! (g, v) with "[$Hr_gen $Hr_value]") as "Hς".
          iApply "HΦ".
          iExists l, γ, g, root', (<[r := (g, v)]> ς). iFrame "#∗". iStep.
          iSplitR. { rewrite fmap_insert //. }
          iSplitL "Hς". { rewrite insert_union_l //. }
          iSplitR. { iPureIntro. split; first set_solver. apply map_Forall_insert_2; done. }
          rewrite decide_False //.
          iDecompose "Hmodel" as (cnodes ϵs base descr δs Hϵs Hcnodes_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hcnodes".
          assert (r ∉ delta۰ref <$> δs) as Hr_notin_δs.
          { intros (i & ((?, ?, ?, ?) & -> & Hδs_lookup)%list_lookup_fmap_Some_1)%list_elem_of_lookup.
            opose proof* Forall_lookup_1 as H; [done.. |].
            apply store۰on𑁒lookup in Hς_lookup. naive_solver.
          }
          assert (store۰on σ₀ descr.(descriptor۰store) !! r = Some (g_r, w)) as Hstore_lookup.
          { rewrite Hδs store۰on𑁒lookup deltas۰apply۰lookup𑁒ne //.
            rewrite store۰on𑁒lookup // in Hς_lookup.
          }
          iDestruct (deltas۰chain𑁒snoc with "Hδs Hroot") as "Hδs".
          iExists _, _, _, _, (δs ++ [Delta r g_r w root']). iSteps; iPureIntro.
          { rewrite fmap_app NoDup_app. split_and!; first done.
            - set_solver.
            - apply NoDup_singleton.
          } {
            rewrite deltas۰apply𑁒snoc insert_insert_eq. cbn.
            erewrite <- deltas۰apply𑁒snoc'.
            rewrite (deltas۰apply𑁒permutation _ (Delta r g_r w root' :: δs)).
            { rewrite fmap_app NoDup_app. split_and!; first done.
              - cbn. set_solver.
              - apply NoDup_singleton.
            } {
              solve_Permutation.
            }
            rewrite deltas۰apply𑁒cons store۰on𑁒insert -Hδs insert_id //.
          } {
            intros []%symmetry%app_cons_not_nil.
          } {
            rewrite Forall_app Forall_singleton. split.
            - rewrite Forall_forall => δ Hδ. rewrite lookup_insert_ne.
              { rewrite list_elem_of_fmap in Hr_notin_δs. naive_solver. }
              rewrite Forall_forall in Hδs_gen. naive_solver.
            - rewrite lookup_insert_eq. naive_solver.
          }
    Qed.

    Lemma sstore_2٠capture𑁒spec t σ₀ σ :
      {{{
        sstore_2۰model t σ₀ σ
      }}}
        sstore_2٠capture t
      {{{
        s
      , RET s;
        sstore_2۰model t σ₀ σ ∗
        sstore_2۰snapshot s t σ
      }}}.
    Proof.
      iIntros "%Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".

      wp۰rec. wp۰load. wp۰store. wp۰load. wp۰pures.
      iApply "HΦ".
      case_decide as [-> | Hg].

      - pose descr := Descriptor 0 ς.
        iMod (cnodes𑁒insert root descr with "Hmodel") as "(Hauth & #Helem)"; first done.
        iSplitL; last first.
        { iSteps. iExists (Descriptor 0 ς). iSteps. }
        iExists l, γ, 1, root, ς. iFrame "#∗". iStep 2. iSplitR.
        { iPureIntro. split; first set_solver.
          eapply map_Forall_impl; first done. naive_solver.
        }
        iExists ∅, []. iSteps; try iPureIntro.
        { apply treemap۰rooted𑁒empty. }
        { rewrite lookup_insert_eq //. }
        { rewrite NoDup_nil //. }
        { rewrite deltas۰apply𑁒nil //. }
        rewrite delete_insert_eq.
        iApply (big_sepM2_empty with "[//]").

      - iDecompose "Hmodel" as (cnodes ϵs base descr δs Hϵs Hcnodes_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hcnodes".
        destruct δs as [| δ δs]; simpl.

        + specialize (Hδs_nil eq_refl) as ->.
          iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs") as %<-.
          iSplitL; iSteps.
          { iPureIntro. split; first done.
            eapply map_Forall_impl => //. naive_solver lia.
          }
          rewrite decide_False; first lia.
          iSteps.

        + iAssert ⌜ϵs !! base = None⌝%I as %Hϵs_lookup_base.
          { rewrite -eq_None_ne_Some. iIntros "%ϵ %Hϵs_lookup".
            iDestruct (big_sepM2_lookup_r with "Hcnodes") as "(%descr' & %Hcnodes_lookup & _)"; first done.
            rewrite lookup_delete_eq // in Hcnodes_lookup.
          }
          iAssert ⌜cnodes !! root = None⌝%I as %Hcnodes_lookup_root.
          { destruct_decide (root = base) as -> | Hcase.
            - iDestruct (deltas۰chain𑁒cons𑁒inv with "Hδs") as "(Hbase & _)".
              iDestruct (pointsto𑁒exclusive with "Hroot Hbase") as %[].
            - rewrite -eq_None_ne_Some. iIntros "%descr' %Hcnodes_lookup".
              iDestruct (big_sepM2_lookup_l with "Hcnodes") as ((cnode' & δs')) "(%Hϵs_lookup_root & %descr'' & _ & _ & _ & _ & _ & Hδs') /=".
              { rewrite lookup_delete_Some //. }
              destruct δs' as [| δ' δs'].
              + iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs'") as %<-.
                opose proof* treemap۰rooted𑁒acyclic as []; done.
              + iDestruct (deltas۰chain𑁒cons𑁒inv with "Hδs'") as "(_Hroot & _)".
                iApply (pointsto𑁒exclusive with "Hroot _Hroot").
          }
          iAssert ⌜ϵs !! root = None⌝%I as %Hϵs_lookup_root.
          { iDestruct (big_sepM2_lookup_iff with "Hcnodes") as %H.
            iPureIntro.
            rewrite eq_None_not_Some -{}H. intros (_ & [])%lookup_delete_is_Some. congruence.
          }
          pose descr_root := Descriptor g ς.
          iMod (cnodes𑁒insert root descr_root with "Hauth") as "(Hauth & #Helem_root)"; first done.
          iSplitL; last first.
          { iSteps. iExists descr_root. iSteps. }
          iExists l, γ, ˖g, root, ς. iFrame "#∗". iStep 3.
          iSplitR; first iSteps.
          set ϵ := (root, δ :: δs).
          iExists (<[base := ϵ]> ϵs), []. iSteps; try iPureIntro.
          { eapply treemap۰rooted𑁒lift; [done.. | congruence]. }
          { rewrite lookup_insert_eq //. }
          { rewrite NoDup_nil //. }
          { rewrite deltas۰apply𑁒nil //. }
          rewrite delete_insert_id //.
          iApply big_sepM2_delete_l; first done.
          iExists ϵ. iSteps.
          { rewrite lookup_insert_eq //. }
          iExists descr_root. iSteps.
          { iPureIntro. rewrite lookup_insert_eq //. }
          rewrite delete_insert_id //.
          iClear "Helem_base". clear dependent descr δs.
          iApply (big_sepM2_impl with "Hcnodes"). iIntros "!>" (cnode descr (cnode' & δs)) "%Hcnodes_lookup %Hϵs_lookup_cnode (%descr' & %Hcnodes_lookup' & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_nodup & %Hδs' & Hδs'))".
          simpl in *.
          iExists descr'. iSteps.
          rewrite lookup_insert_ne //. congruence.
    Qed.

    #[local] Definition collect۰inv γ σ₀ root ς cnodes ϵs base descr δs : iProp Σ :=
      root ↦ᵣ §Root ∗
      ( [∗ map] r ↦ data ∈ store۰on σ₀ ς,
        r.[ref_gen] ↦ #data.(gen) ∗
        r.[ref_value] ↦ data.(val)
      ) ∗
      ⌜treemap۰rooted ϵs base⌝ ∗
      cnodes۰auth γ cnodes ∗
      (* [base] cnode *)
      ⌜cnodes !! base = Some descr⌝ ∗
      cnode۰model γ σ₀ base descr (root, δs) ς ∗
      ⌜δs = [] → ς = descr.(descriptor۰store)⌝ ∗
      (* other cnodes *)
      [∗ map] cnode ↦ descr; ϵ ∈ delete base cnodes; ϵs,
        ∃ descr',
        ⌜cnodes !! ϵ.1 = Some descr'⌝ ∗
        cnode۰model γ σ₀ cnode descr ϵ descr'.(descriptor۰store).
    #[local] Lemma sstore_2٠collect𑁒spec𑁒base𑁒chain {γ σ₀ root ς cnodes ϵs base descr δs} i δ node acc :
      δs !! i = Some δ →
      δ.(delta۰node) = node →
      {{{
        collect۰inv γ σ₀ root ς cnodes ϵs base descr δs
      }}}
        sstore_2٠collect #node acc
      {{{
        acc'
      , RET (#root, acc');
        collect۰inv γ σ₀ root ς cnodes ϵs base descr δs ∗
        plist۰model acc' acc $ tail $
          (λ δ, #δ.(delta۰node)) <$> reverse (drop i δs)
      }}}.
    Proof.
      iLöb as "HLöb" forall (i δ node acc).

      iIntros "%Hδs_lookup %Hnode %Φ (Hroot & Hς & %Hϵs & Hauth & %Hcnodes_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hcnodes) HΦ".
      simpl in *.

      wp۰rec.
      iDestruct (deltas۰chain𑁒lookup i δ with "Hδs") as "(Hδs1 & Hδs2)"; first done.
      rewrite Hnode.
      destruct (drop ˖i δs) as [| δ' δs'] eqn:Hdrop_δs.

      - iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs2") as %->.
        iDestruct (deltas۰chain𑁒app₂ with "Hδs1 Hδs2") as "Hδs".
        rewrite -Hdrop_δs take_drop (drop_S δs δ i) // Hdrop_δs /=.
        wp۰load.
        iSteps.

      - iDestruct (deltas۰chain𑁒cons𑁒inv with "Hδs2") as "(Hδ' & Hδs2)".
        wp۰load.
        assert (δs !! ˖i = Some δ') as Hδs_lookup'.
        { rewrite -(take_drop ˖i δs) Hdrop_δs lookup_app_r length_take; first lia.
          rewrite Nat.min_l.
          { apply lookup_lt_Some in Hδs_lookup. lia. }
          rewrite Nat.sub_diag //.
        }
        assert (drop ˖˖i δs = δs') as Hdrop_δs'.
        { erewrite drop_S in Hdrop_δs => //. congruence. }
        wp۰apply+ ("HLöb" $! ˖i δ' with "[//] [//] [- HΦ]") as (acc') "(Hinv & %Hacc')".
        { iDestruct (deltas۰chain𑁒cons with "Hδ' Hδs2") as "Hδs2".
          iDestruct (deltas۰chain𑁒app₂ with "Hδs1 Hδs2") as "Hδs".
          rewrite -Hdrop_δs take_drop. iSteps.
        }
        iSteps. iPureIntro.
        rewrite /plist۰model' Hacc' -plist۰to_val𑁒singleton plist۰to_val𑁒app. f_equal.
        rewrite (drop_S δs δ i) // reverse_cons fmap_app /= Hnode tail𑁒app //.
        rewrite Hdrop_δs reverse_cons fmap_app /=.
        symmetry. apply app_cons_not_nil.
    Qed.
    #[local] Definition collect𑁒specification γ σ₀ root ς cnodes ϵs base descr δs : iProp Σ :=
      ∀ cnode descr_cnode path acc,
      {{{
        ⌜cnodes !! cnode = Some descr_cnode⌝ ∗
        ⌜treemap۰path ϵs base cnode path⌝ ∗
        collect۰inv γ σ₀ root ς cnodes ϵs base descr δs
      }}}
        sstore_2٠collect #cnode acc
      {{{
        acc'
      , RET (#root, acc');
        collect۰inv γ σ₀ root ς cnodes ϵs base descr δs ∗
        plist۰model acc' acc $ tail $
          ((λ δ, #δ.(delta۰node)) <$> reverse δs) ++
          ((λ δ, #δ.(delta۰node)) <$> reverse (concat path)) ++
          [ #cnode]
      }}}.
    #[local] Lemma sstore_2٠collect𑁒spec𑁒chain {γ σ₀ root ς cnodes ϵs base descr δs} cnode ϵ i 𝝳 node path acc :
      ϵs !! cnode = Some ϵ →
      ϵ.2 !! i = Some 𝝳 →
      𝝳.(delta۰node) = node →
      treemap۰path ϵs base ϵ.1 path →
      {{{
        collect۰inv γ σ₀ root ς cnodes ϵs base descr δs ∗
        collect𑁒specification γ σ₀ root ς cnodes ϵs base descr δs
      }}}
        sstore_2٠collect #node acc
      {{{
        acc'
      , RET (#root, acc');
        collect۰inv γ σ₀ root ς cnodes ϵs base descr δs ∗
        plist۰model acc' acc $ tail $
          ((λ δ, #δ.(delta۰node)) <$> reverse δs) ++
          ((λ δ, #δ.(delta۰node)) <$> reverse (concat path)) ++
          ((λ δ, #δ.(delta۰node)) <$> reverse (drop i ϵ.2))
      }}}.
    Proof.
      destruct ϵ as (cnode', 𝝳s).

      iLöb as "HLöb" forall (i 𝝳 node acc).

      iIntros "%Hϵs_lookup %H𝝳s_lookup %Hnode %Hpath %Φ ((Hroot & Hς & %Hϵs & Hauth & %Hcnodes_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hcnodes) & #Hspec) HΦ".
      simpl in *.

      iAssert (∃ descr, ⌜delete base cnodes !! cnode = Some descr⌝)%I as "(%descr_cnode & %Hcnodes_lookup)".
      { iDestruct (big_sepM2_lookup_r with "Hcnodes") as "(% & % & _)"; first done.
        iSteps.
      }
      iDestruct (big_sepM2_lookup_acc with "Hcnodes") as "((%descr_cnode' & %Hcnodes_lookup' & (%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %H𝝳s_nodup & %H𝝳s & H𝝳s) & Hcnodes)"; [done.. |].
      iDestruct (deltas۰chain𑁒lookup i 𝝳 with "H𝝳s") as "(H𝝳s1 & H𝝳s2)"; first done.
      rewrite Hnode /=.
      destruct (drop ˖i 𝝳s) as [| 𝝳' 𝝳s'] eqn:Hdrop_𝝳s.

      - iDestruct (deltas۰chain𑁒nil𑁒inv with "H𝝳s2") as %->.
        iDestruct (deltas۰chain𑁒app₂ with "H𝝳s1 H𝝳s2") as "H𝝳s".
        rewrite -Hdrop_𝝳s take_drop (drop_S 𝝳s 𝝳 i) // Hdrop_𝝳s /=.
        wp۰apply ("Hspec" with "[- HΦ]") as (acc') "(Hinv & %Hacc')"; first iSteps.
        rewrite Hnode. iSteps.

      - iDestruct (deltas۰chain𑁒cons𑁒inv with "H𝝳s2") as "(H𝝳' & H𝝳s2)".
        wp۰rec. wp۰load.
        assert (𝝳s !! ˖i = Some 𝝳') as H𝝳s_lookup'.
        { rewrite -(take_drop ˖i 𝝳s) Hdrop_𝝳s lookup_app_r length_take; first lia.
          rewrite Nat.min_l.
          { apply lookup_lt_Some in H𝝳s_lookup. lia. }
          rewrite Nat.sub_diag //.
        }
        assert (drop ˖˖i 𝝳s = 𝝳s') as Hdrop_𝝳s'.
        { erewrite drop_S in Hdrop_𝝳s => //. congruence. }
        wp۰apply+ ("HLöb" $! ˖i 𝝳' with "[//] [//] [//] [//] [- HΦ]") as (acc') "(Hinv & %Hacc')".
        { iDestruct (deltas۰chain𑁒cons with "H𝝳' H𝝳s2") as "H𝝳s2".
          iDestruct (deltas۰chain𑁒app₂ with "H𝝳s1 H𝝳s2") as "H𝝳s".
          iFrame "Hspec".
          rewrite -Hdrop_𝝳s take_drop. iSteps.
        }
        iSteps. iPureIntro.
        rewrite /plist۰model' Hacc' -plist۰to_val𑁒singleton plist۰to_val𑁒app. f_equal.
        rewrite (drop_S 𝝳s 𝝳 i) // reverse_cons fmap_app /= Hnode 2!(assoc _ _ _ [_]) -tail𑁒app //.
        rewrite Hdrop_𝝳s reverse_cons fmap_app /= 2!assoc.
        symmetry. apply app_cons_not_nil.
    Qed.
    #[local] Lemma sstore_2٠collect𑁒spec {γ σ₀ root ς cnodes ϵs base descr δs} cnode descr_cnode path acc :
      cnodes !! cnode = Some descr_cnode →
      treemap۰path ϵs base cnode path →
      {{{
        collect۰inv γ σ₀ root ς cnodes ϵs base descr δs
      }}}
        sstore_2٠collect #cnode acc
      {{{
        acc'
      , RET (#root, acc');
        collect۰inv γ σ₀ root ς cnodes ϵs base descr δs ∗
        plist۰model acc' acc $ tail $
          ((λ δ, #δ.(delta۰node)) <$> reverse δs) ++
          ((λ δ, #δ.(delta۰node)) <$> reverse (concat path)) ++
          [ #cnode]
      }}}.
    Proof.
      iLöb as "HLöb" forall (cnode descr_cnode path acc).

      iIntros "%Hcnodes_lookup %Hpath %Φ (Hroot & Hς & %Hϵs & Hauth & %Hcnodes_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hcnodes) HΦ".
      simpl in *.

      wp۰rec.
      destruct_decide (cnode = base) as -> | Hcnode.

      - apply treemap۰path𑁒is_nil in Hpath as ->; last done.
        destruct δs as [| δ δs].

        + iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs") as %<-.
          iSteps.

        + iDestruct (deltas۰chain𑁒cons𑁒inv with "Hδs") as "(Hδ & Hδs)".
          wp۰load.
          iDestruct (deltas۰chain𑁒cons with "Hδ Hδs") as "Hδs".
          wp۰apply+ (sstore_2٠collect𑁒spec𑁒base𑁒chain (δs := δ :: δs) 0 δ with "[- HΦ]") as (acc') "(Hinv & %Hacc')"; [done.. | iFrameSteps |].
          iSteps. iPureIntro.
          rewrite /plist۰model' Hacc' -plist۰to_val𑁒singleton plist۰to_val𑁒app. f_equal.
          rewrite -tail𑁒app // reverse_cons fmap_app.
          symmetry. apply app_cons_not_nil.

      - apply treemap۰path𑁒is_cons in Hpath as (cnode' & 𝝳s & path' & -> & Hϵs_lookup & Hpath'); [| done..].
        assert (delete base cnodes !! cnode = Some descr_cnode) as Hdelete_cnodes_lookup.
        { rewrite lookup_delete_ne //. }
        iDestruct (big_sepM2_lookup_acc with "Hcnodes") as "((%descr_cnode' & %Hcnodes_lookup' & (%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %H𝝳s_nodup & %H𝝳s & H𝝳s) & Hcnodes)"; [done.. |].
        destruct 𝝳s as [| 𝝳 𝝳s].

        + iDestruct (deltas۰chain𑁒nil𑁒inv with "H𝝳s") as %[= <-].
          opose proof* treemap۰rooted𑁒acyclic as []; done.

        + iDestruct (deltas۰chain𑁒cons𑁒inv with "H𝝳s") as "(H𝝳 & H𝝳s)".
          wp۰load.
          iDestruct (deltas۰chain𑁒cons with "H𝝳 H𝝳s") as "H𝝳s".
          wp۰apply+ (sstore_2٠collect𑁒spec𑁒chain cnode _ 0 𝝳 with "[- HΦ]") as (acc') "(Hinv & %Hacc')"; [done.. | |].
          { iSplitL; first iFrameSteps.
            iClear "Helem_cnode". clear.
            iIntros "%cnode %descr_cnode %path %acc !> %Φ (%Hcnodes_lookup & %Hpath & Hinv) HΦ".
            wp۰apply ("HLöb" with "[//] [//] Hinv HΦ").
          }
          iSteps. iPureIntro.
          rewrite /plist۰model' Hacc' -plist۰to_val𑁒singleton plist۰to_val𑁒app. f_equal.
          rewrite !reverse_cons reverse_app !fmap_app !assoc -tail𑁒app //.
          symmetry. apply app_cons_not_nil.
    Qed.

    #[local] Definition revert۰pre₁ γ σ₀ root ς cnodes ϵs base descr δs : iProp Σ :=
      ∃ v_root,
      root ↦ᵣ v_root ∗
      ( [∗ map] r ↦ data ∈ store۰on σ₀ ς,
        r.[ref_gen] ↦ #data.(gen) ∗
        r.[ref_value] ↦ data.(val)
      ) ∗
      ⌜treemap۰rooted ϵs base⌝ ∗
      cnodes۰auth γ cnodes ∗
      (* [base] cnode *)
      ⌜cnodes !! base = Some descr⌝ ∗
      cnode۰model γ σ₀ base descr (root, δs) ς ∗
      ⌜δs = [] → ς = descr.(descriptor۰store)⌝ ∗
      (* other cnodes *)
      [∗ map] cnode ↦ descr; ϵ ∈ delete base cnodes; ϵs,
        ∃ descr',
        ⌜cnodes !! ϵ.1 = Some descr'⌝ ∗
        cnode۰model γ σ₀ cnode descr ϵ descr'.(descriptor۰store).
    #[local] Definition revert۰pre₂ γ σ₀ ς cnodes ϵs base descr_base δs_base cnode descr_cnode δs_cnode node : iProp Σ :=
      ∃ v_node,
      node ↦ᵣ v_node ∗
      ( [∗ map] r ↦ data ∈ store۰on σ₀ ς,
        r.[ref_gen] ↦ #data.(gen) ∗
        r.[ref_value] ↦ data.(val)
      ) ∗
      ⌜treemap۰rooted ϵs base⌝ ∗
      cnodes۰auth γ cnodes ∗
      (* [base] cnode *)
      ⌜cnodes !! base = Some descr_base⌝ ∗
      cnode۰model γ σ₀ base descr_base (node, δs_base) ς ∗
      (* [cnode] cnode *)
      ⌜cnodes !! cnode = Some descr_cnode⌝ ∗
      cnode۰model γ σ₀ cnode descr_cnode (node, δs_cnode) ς ∗
      (* other cnodes *)
      [∗ map] cnode ↦ descr; ϵ ∈ delete base $ delete cnode cnodes; delete cnode ϵs,
        ∃ descr',
        ⌜cnodes !! ϵ.1 = Some descr'⌝ ∗
        cnode۰model γ σ₀ cnode descr ϵ descr'.(descriptor۰store).
    #[local] Definition revert۰post γ σ₀ cnodes ϵs base descr : iProp Σ :=
      base ↦ᵣ §Root ∗
      ( [∗ map] r ↦ data ∈ store۰on σ₀ descr.(descriptor۰store),
        r.[ref_gen] ↦ #data.(gen) ∗
        r.[ref_value] ↦ data.(val)
      ) ∗
      ⌜treemap۰rooted ϵs base⌝ ∗
      cnodes۰auth γ cnodes ∗
      (* [base] cnode *)
      cnode۰model γ σ₀ base descr (base, []) descr.(descriptor۰store) ∗
      (* other cnodes *)
      [∗ map] cnode ↦ descr; ϵ ∈ delete base cnodes; ϵs,
        ∃ descr',
        ⌜cnodes !! ϵ.1 = Some descr'⌝ ∗
        cnode۰model γ σ₀ cnode descr ϵ descr'.(descriptor۰store).
    #[local] Lemma sstore_2٠revert𑁒spec𑁒aux {γ σ₀ ς cnodes ϵs base descr_base δs_base cnode descr_cnode δs_cnode node} base' descr_base' path δs acc :
      cnodes !! base' = Some descr_base' →
      treemap۰path ϵs cnode base' path →
      ϵs !! cnode = Some (base, δs) →
      0 < length δs_cnode →
      NoDup (delta۰ref <$> δs_cnode ++ δs_base) →
      list۰model' acc $ tail $
        ((λ δ, #δ.(delta۰node)) <$> reverse δs_cnode) ++
        ((λ δ, #δ.(delta۰node)) <$> reverse (concat path)) ++
        [ #base'] →
      {{{
        revert۰pre₂ γ σ₀ ς cnodes ϵs base descr_base δs_base cnode descr_cnode δs_cnode node
      }}}
        sstore_2٠revert #node acc
      {{{
        ϵs
      , RET ();
        revert۰post γ σ₀ cnodes ϵs base' descr_base'
      }}}.
    Proof.
      iLöb as "HLöb" forall (ς ϵs base descr_base δs_base cnode descr_cnode δs_cnode node path δs acc).

      iIntros (Hdescr_lookup_base' Hpath Hϵs_lookup_cnode Hδs_cnode_length Hnodup ->) "%Φ (%v_node & Hnode & Hς & %Hϵs & Hauth & %Hcnodes_lookup_base & ((%Hbase_store_dom & %Hbase_store_gen) & #Helem_base & %Hδs_base_nodup & %Hδs_base & Hδs_base) & %Hcnodes_lookup_cnode & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_cnode_nodup & %Hδs_cnode & Hδs_cnode) & Hcnodes) HΦ".

      destruct δs_cnode as [| (r1, g1, v1, _node) δs_cnode _] using rev_ind; first naive_solver lia.
      simpl in *.
      iDestruct (deltas۰chain𑁒snoc𑁒inv with "Hδs_cnode") as "(%Hnode & Hδs_cnode & Hδ)".
      simplify.

      wp۰rec.
      destruct δs_cnode as [| (r2, g2, v2, node') δs_cnode _] using rev_ind.

      - iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs_cnode") as %->.
        simpl in *.
        destruct path as [| δs_cnode path _] using rev_ind => /=.

        + apply treemap۰path𑁒nil𑁒inv in Hpath as <-.
          wp۰load.
          wp۰apply+ assert𑁒spec; first rewrite bool_decide_eq_true_2 //.
          assert (∃ data, store۰on σ₀ ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
          { apply elem_of_dom.
            apply (f_equal dom) in Hδs_cnode.
            set_solver.
          }
          iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
          do 2 wp۰load. do 3 wp۰store. wp۰pures. wp۰rec. wp۰store.
          iDestruct ("Hς" $! (_, _) with "[$Hr_gen $Hr_value]") as "Hς".
          rewrite deltas۰apply𑁒singleton store۰on𑁒insert in Hδs_cnode.
          rewrite -Hδs_cnode.
          set δs_base' := δs_base ++ [Delta r1 g1' v1' base'].
          opose proof* (treemap𑁒reroot𑁒rooted _ _ δs_base') as Hϵs'; [done.. |].
          iApply "HΦ".
          simplify. iSteps; try iPureIntro.
          { apply NoDup_nil_2. }
          { rewrite deltas۰apply𑁒nil //. }
          { rewrite -{2}(insert_id (delete base' cnodes) base descr_base).
            { rewrite lookup_delete_ne //.
              eapply (treemap۰rooted𑁒acyclic (tree := ϵs)); done.
            }
            rewrite -insert_delete_eq.
            iApply (big_sepM2_insert_2 with "[- Hcnodes] Hcnodes").
            iSteps; try iPureIntro.
            { rewrite /δs_base' -Permutation_cons_append //. }
            { rewrite Hδs_base (store۰on𑁒deltas۰apply _ _ descr_base'.(descriptor۰store)) Hδs_cnode.
              rewrite (deltas۰apply𑁒permutation δs_base' (δs_base ++ [Delta r1 g1' v1' base'])) //.
              { rewrite /δs_base' -Permutation_cons_append //. }
              rewrite deltas۰apply𑁒snoc insert_insert_eq insert_id // store۰on𑁒deltas۰apply //.
            } {
              iApply (deltas۰chain𑁒snoc with "Hδs_base Hnode").
            }
          }

        + pose proof Hpath as (cnode' & Hpath' & (? & Hϵs_lookup_cnode' & ->%treemap۰path𑁒nil𑁒inv)%treemap۰path𑁒cons𑁒inv)%treemap۰path𑁒app𑁒inv.
          rewrite concat_app reverse_app fmap_app /= right_id.
          assert (cnode' ≠ cnode).
          { eapply treemap۰rooted𑁒acyclic; done. }
          assert (cnode' ≠ base).
          { pose proof Hϵs as ?%treemap۰rooted𑁒root. congruence. }
          iDestruct (big_sepM2_delete_r with "Hcnodes") as "(%descr_cnode' & %Hcnodes_lookup_cnode' & (%descr_cnode_ & %Hcnodes_lookup_cnode_ & ((%descr_cnode_dom' & %descr_cnode_gen') & #Helem_cnode' & %Hδs_cnode'_nodup & %Hδs_cnode' & Hδs_cnode')) & Hcnodes)".
          { rewrite lookup_delete_ne //. }
          simpl in *.
          rewrite Hcnodes_lookup_cnode in Hcnodes_lookup_cnode_. injection Hcnodes_lookup_cnode_ as <-.
          destruct δs_cnode as [| (r2, g2, v2, cnode_) δs_cnode _] using rev_ind.
          { iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs_cnode'") as %<-.
            opose proof* treemap۰rooted𑁒acyclic as []; done.
          }
          rewrite reverse_snoc. cbn.
          iDestruct (deltas۰chain𑁒snoc𑁒inv with "Hδs_cnode'") as "(%Hcnode & Hδs_cnode' & Hδ')".
          simpl in Hcnode. subst cnode_.
          wp۰load.
          iDestruct (deltas۰chain𑁒snoc with "Hδs_cnode' Hδ'") as "Hδs_cnode'".
          wp۰apply+ assert𑁒spec; first rewrite bool_decide_eq_true_2 //.
          assert (∃ data, store۰on σ₀ ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
          { apply elem_of_dom.
            apply (f_equal dom) in Hδs_cnode.
            set_solver.
          }
          iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
          do 2 wp۰load. do 3 wp۰store.
          iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
          rewrite deltas۰apply𑁒singleton store۰on𑁒insert in Hδs_cnode.
          rewrite -Hδs_cnode.
          set δs_base' := δs_base ++ [Delta r1 g1' v1' cnode].
          set ϵs' := treemap۰reroot ϵs base cnode δs_base'.
          opose proof* (treemap𑁒reroot𑁒rooted cnode _ δs_base') as Hϵs'; [done.. |].
          wp۰apply+ ("HLöb" $! _ ϵs' cnode descr_cnode [] cnode' descr_cnode' (δs_cnode ++ [_]) with "[] [] [] [] [] [] [- HΦ]"); try iPureIntro; try done.
          { eapply treemap𑁒reroot𑁒path; done. }
          { rewrite lookup_insert_ne // lookup_delete_ne //. }
          { simpl_length/=. lia. }
          { rewrite right_id //. }
          { rewrite reverse_snoc assoc //. }
          iSteps; try iPureIntro.
          { apply NoDup_nil_2. }
          { rewrite deltas۰apply𑁒nil //. }
          { do 2 rewrite lookup_delete_ne // in Hcnodes_lookup_cnode'. }
          { rewrite (delete_delete _ cnode' base) (delete_delete _ cnode cnode') delete_insert_ne //.
            rewrite -{2}(insert_delete_id (delete cnode' $ delete cnode cnodes) base descr_base).
            { rewrite lookup_delete_ne // lookup_delete_ne //.
              eapply (treemap۰rooted𑁒acyclic (tree := ϵs)); done.
            }
            iApply (big_sepM2_insert_2 with "[- Hcnodes] Hcnodes").
            iSteps; try iPureIntro.
            { rewrite /δs_base' -Permutation_cons_append //. }
            { rewrite Hδs_base (store۰on𑁒deltas۰apply _ _ descr_cnode.(descriptor۰store)) Hδs_cnode.
              rewrite (deltas۰apply𑁒permutation δs_base' (δs_base ++ [Delta r1 g1' v1' cnode])) //.
              { rewrite /δs_base' -Permutation_cons_append //. }
              rewrite deltas۰apply𑁒snoc insert_insert_eq insert_id // store۰on𑁒deltas۰apply //.
            } {
              iApply (deltas۰chain𑁒snoc with "Hδs_base Hnode").
            }
          }

      - rewrite 2!reverse_snoc.
        iDestruct (deltas۰chain𑁒snoc𑁒inv with "Hδs_cnode") as "(_ & Hδs_cnode & Hδ')".
        rewrite !last_snoc. cbn.
        wp۰load.
        wp۰apply+ assert𑁒spec; first rewrite bool_decide_eq_true_2 //.
        assert (∃ data, store۰on σ₀ ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
        { apply elem_of_dom.
          rewrite deltas۰apply𑁒snoc in Hδs_cnode.
          apply (f_equal dom) in Hδs_cnode.
          set_solver.
        }
        iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
        do 2 wp۰load. do 3 wp۰store.
        iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
        rewrite -store۰on𑁒insert.
        iDestruct (deltas۰chain𑁒snoc with "Hδs_base Hnode") as "Hδs_base".
        iDestruct (deltas۰chain𑁒snoc with "Hδs_cnode Hδ'") as "Hδs_cnode".
        set ς' := <[r1 := (g1, v1)]> ς.
        set δs_base' := δs_base ++ [Delta r1 g1' v1' node'].
        set δs_cnode' := δs_cnode ++ [Delta r2 g2 v2 node'].
        wp۰apply+ ("HLöb" $! ς' _ base descr_base δs_base' cnode descr_cnode δs_cnode' with "[] [] [] [] [] [] [- HΦ]"); try iPureIntro; try done.
        { rewrite /δs_cnode'. simpl_length/=. lia. }
        { rewrite -assoc (comm _ [_]) assoc fmap_app in Hnodup.
          rewrite /δs_cnode' /δs_base' assoc fmap_app //.
        }
        { rewrite reverse_app //. }
        iSteps; try iPureIntro.
        { rewrite -assoc fmap_app in Hnodup.
          apply NoDup_app in Hnodup as (_ & _ & Hnodup).
          rewrite /δs_base' Permutation_app_comm //.
        } {
          rewrite deltas۰apply𑁒snoc insert_insert_eq store۰on𑁒deltas۰apply store۰on𑁒insert insert_id // -store۰on𑁒deltas۰apply //.
        } {
          rewrite -assoc fmap_app in Hnodup.
          apply NoDup_app in Hnodup as (Hnodup & _ & _).
          done.
        } {
          rewrite /ς' -(deltas۰apply𑁒snoc' _ _ _ _ node) //.
        }
    Qed.
    #[local] Lemma sstore_2٠revert𑁒spec {γ σ₀ root ς cnodes ϵs base descr_base δs} base' descr_base' path acc :
      cnodes !! base' = Some descr_base' →
      treemap۰path ϵs base base' path →
      list۰model' acc $ tail $
        ((λ δ, #δ.(delta۰node)) <$> reverse δs) ++
        ((λ δ, #δ.(delta۰node)) <$> reverse (concat path)) ++
        [ #base'] →
      {{{
        revert۰pre₁ γ σ₀ root ς cnodes ϵs base descr_base δs
      }}}
        sstore_2٠revert #root acc
      {{{
        ϵs
      , RET ();
        revert۰post γ σ₀ cnodes ϵs base' descr_base'
      }}}.
    Proof.
      iLöb as "HLöb" forall (root ς δs acc).

      iIntros (Hcnodes_lookup_base' Hpath ->) "%Φ (%v_root & Hroot & Hς & %Hϵs & Hauth & %Hcnodes_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hcnodes) HΦ".
      simpl in *.

      destruct δs as [| (r1, g1, v1, _root) δs _] using rev_ind.

      - iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs") as %<-.
        specialize (Hδs_nil eq_refl) as ->.
        destruct path as [| δs_cnode path _] using rev_ind => /=.

        + apply treemap۰path𑁒nil𑁒inv in Hpath as ->.
          assert (descr_base' = descr_base) as -> by congruence.
          wp۰rec.
          iSteps.

        + apply treemap۰path𑁒app𑁒inv in Hpath as (cnode & Hpath' & (? & Hϵs_lookup_cnode & ->%treemap۰path𑁒nil𑁒inv)%treemap۰path𑁒cons𑁒inv).
          iDestruct (big_sepM2_delete_r with "Hcnodes") as "(%descr_cnode & %Hcnodes_lookup_cnode & (%descr_base_ & %Hcnodes_lookup_base_ & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_cnode_nodup & %Hδs_cnode & Hδs_cnode)) & Hcnodes)"; first done.
          simpl in Hcnodes_lookup_base_. assert (descr_base_ = descr_base) as -> by congruence.
          assert (cnode ≠ base) as Hcnode.
          { intros ->.
            opose proof* treemap۰rooted𑁒acyclic as []; done.
          }
          iAssert ⌜0 < length δs_cnode⌝%I as %Hδs_cnode_length.
          { destruct δs_cnode; last iSteps.
            iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs_cnode") as %?. done.
          }
          rewrite lookup_delete_ne // in Hcnodes_lookup_cnode.
          rewrite delete_delete.
          wp۰apply (sstore_2٠revert𑁒spec𑁒aux (δs_base := []) (δs_cnode := δs_cnode) base' with "[- HΦ]"); try done.
          { rewrite right_id //. }
          { rewrite concat_app reverse_app fmap_app -assoc /= right_id //. }
          { iSteps. }

      - iDestruct (deltas۰chain𑁒snoc𑁒inv with "Hδs") as "(%Heq & Hδs & Hδ)".
        simpl in Heq. subst _root.
        rewrite reverse_snoc. cbn.
        wp۰rec.
        destruct δs as [| (r2, g2, v2, node) δs _] using rev_ind.

        + destruct path as [| δs_cnode path _] using rev_ind => /=.

          * apply treemap۰path𑁒nil𑁒inv in Hpath as ->.
            assert (descr_base' = descr_base) as -> by congruence.
            wp۰load.
            wp۰apply+ assert𑁒spec; first rewrite bool_decide_eq_true_2 //.
            assert (∃ data, store۰on σ₀ ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
            { apply elem_of_dom.
              rewrite deltas۰apply𑁒snoc in Hδs.
              apply (f_equal dom) in Hδs.
              set_solver.
            }
            iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
            do 2 wp۰load. do 3 wp۰store. wp۰pures. wp۰rec. wp۰store.
            iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
            rewrite deltas۰apply𑁒singleton store۰on𑁒insert in Hδs.
            rewrite -Hδs.
            iSteps; iPureIntro.
            { apply NoDup_nil_2. }
            { rewrite deltas۰apply𑁒nil //. }

          * apply treemap۰path𑁒app𑁒inv in Hpath as (cnode & Hpath' & (? & Hϵs_lookup_cnode & ->%treemap۰path𑁒nil𑁒inv)%treemap۰path𑁒cons𑁒inv).
            iDestruct (big_sepM2_delete_r with "Hcnodes") as "(%descr_cnode & %Hcnodes_lookup_cnode & (%descr_base_ & %Hcnodes_lookup_base_ & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_cnode_nodup & %Hδs_cnode & Hδs_cnode)) & Hcnodes)"; first done.
            simpl in Hcnodes_lookup_base_. assert (descr_base_ = descr_base) as -> by congruence.
            assert (cnode ≠ base) as Hcnode.
            { intros ->.
              opose proof* treemap۰rooted𑁒acyclic as []; done.
            }
            destruct δs_cnode as [| (r2, g2, v2, _base) δs_cnode' _] using rev_ind.
            { iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs_cnode") as %?. done. }
            iDestruct (deltas۰chain𑁒snoc𑁒inv with "Hδs_cnode") as "(%Heq & Hδs_cnode & Hδ')".
            simpl in Heq. subst _base.
            rewrite concat_app reverse_app fmap_app /= right_id reverse_app /=.
            wp۰load.
            iDestruct (deltas۰chain𑁒snoc with "Hδs_cnode Hδ'") as "Hδs_cnode". cbn.
            wp۰apply+ assert𑁒spec; first rewrite bool_decide_eq_true_2 //.
            assert (∃ data, store۰on σ₀ ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
            { apply elem_of_dom.
              rewrite deltas۰apply𑁒snoc in Hδs.
              apply (f_equal dom) in Hδs.
              set_solver.
            }
            iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
            do 2 wp۰load. do 3 wp۰store.
            iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
            rewrite lookup_delete_ne // in Hcnodes_lookup_cnode.
            rewrite deltas۰apply𑁒singleton store۰on𑁒insert in Hδs.
            rewrite -Hδs delete_delete.
            wp۰apply+ (sstore_2٠revert𑁒spec𑁒aux (δs_base := []) (δs_cnode := δs_cnode' ++ [_]) base' with "[- HΦ]"); try done.
            { simpl_length/=. lia. }
            { rewrite right_id //. }
            { rewrite reverse_app fmap_app -assoc //. }
            { iSteps; try iPureIntro.
              { apply NoDup_nil_2. }
              { rewrite deltas۰apply𑁒nil //. }
            }

        + rewrite last_snoc reverse_snoc /=.
          iDestruct (deltas۰chain𑁒snoc𑁒inv with "Hδs") as "(_ & Hδs & Hδ')".
          wp۰load.
          iDestruct (deltas۰chain𑁒snoc with "Hδs Hδ'") as "Hδs". cbn.
          wp۰apply+ assert𑁒spec; first rewrite bool_decide_eq_true_2 //.
          assert (∃ data, store۰on σ₀ ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
          { apply elem_of_dom.
            rewrite deltas۰apply𑁒snoc in Hδs.
            apply (f_equal dom) in Hδs.
            set_solver.
          }
          iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
          do 2 wp۰load. do 3 wp۰store.
          iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
          rewrite -store۰on𑁒insert.
          wp۰apply+ ("HLöb" $! node _ (δs ++ [Delta r2 g2 v2 node]) with "[%] [%] [%] [- HΦ]"); try done.
          { rewrite reverse_app fmap_app -assoc //. }
          { iSteps; iPureIntro.
            { rewrite fmap_app in Hδs_nodup.
              apply NoDup_app in Hδs_nodup as (Hnodup & _ & _).
              done.
            }
            { erewrite <- deltas۰apply𑁒snoc' => //. }
            { intros []%symmetry%app_cons_not_nil. }
          }
    Qed.

    #[local] Lemma sstore_2٠reroot𑁒spec {γ σ₀ root ς cnodes ϵs base descr δs} base' descr' path :
      cnodes !! base' = Some descr' →
      treemap۰path ϵs base base' path →
      {{{
        collect۰inv γ σ₀ root ς cnodes ϵs base descr δs
      }}}
        sstore_2٠reroot #base'
      {{{
        ϵs
      , RET ();
        revert۰post γ σ₀ cnodes ϵs base' descr'
      }}}.
    Proof.
      iIntros "%Hcnodes_lookup_base' %Hpath %Φ Hinv HΦ".

      wp۰rec.
      wp۰apply (sstore_2٠collect𑁒spec with "Hinv") as (acc) "(Hinv & %Hacc)"; [done.. |].
      wp۰apply+ (sstore_2٠revert𑁒spec with "[Hinv] HΦ"); [done.. | |].
      { rewrite list۰model'𑁒plist۰model' //. }
      iDestruct "Hinv" as "(Hroot & Hς & %Hϵs & Hauth & %Hcnodes_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hcnodes)".
      iSteps.
    Qed.

    Lemma sstore_2٠restore𑁒spec t σ₀ σ s σ' :
      {{{
        sstore_2۰model t σ₀ σ ∗
        sstore_2۰snapshot s t σ'
      }}}
        sstore_2٠restore t s
      {{{
        RET ();
        sstore_2۰model t σ₀ σ'
      }}}.
    Proof.
      iIntros "%Φ ((%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) & (%_l & %_γ & %g' & %base' & %descr' & %Heq & -> & -> & %Hg' & #_Hmeta & #Helem_base')) HΦ". injection Heq as <-.
      iDestruct (meta𑁒agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

      wp۰rec. wp۰pures. rewrite bool_decide_eq_true_2 //. wp۰pures.
      case_decide as [-> | Hg].
      { iDestruct (cnodes𑁒lookup with "Hmodel Helem_base'") as %[]%lookup_empty_Some. }
      iDecompose "Hmodel" as (cnodes ϵs base descr δs Hϵs Hcnodes_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hcnodes".
      iDestruct (cnodes𑁒lookup with "Hauth Helem_base'") as %Hcnodes_lookup_base'.
      destruct_decide (base' = root) as -> | Hbase'.

      - destruct_decide (root = base) as -> | Hroot; last first.
        { assert (delete base cnodes !! root = Some descr') as Hdelete_cnodes_lookup_root.
          { rewrite lookup_delete_ne //. }
          iAssert (∃ ϵ, ⌜ϵs !! root = Some ϵ⌝)%I as "(%ϵ & %Hϵs_lookup_root)".
          { iDestruct (big_sepM2_lookup_l with "Hcnodes") as "(% & % & _)"; first done.
            iSteps.
          }
          iDestruct (big_sepM2_lookup_acc with "Hcnodes") as "((%descr_root & %Hcnodes_lookup_root & (%Hroot_store_dom & %Hroot_store_gen) & #Helem_root & %Hδs'_nodup & %Hδs' & Hδs') & Hcnodes)"; [done.. |].
          destruct ϵ.2 as [| δ δs'] eqn:Hδ.
          { iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs'") as %?.
            opose proof* treemap۰rooted𑁒acyclic as []; done.
          }
          iDestruct (deltas۰chain𑁒cons𑁒inv with "Hδs'") as "(Hδ & Hδs')".
          iDestruct (pointsto𑁒exclusive with "Hroot Hδ") as %[].
        }
        assert (descr = descr') as <- by congruence.
        destruct δs as [| δ δs]; last first.
        { iDestruct (deltas۰chain𑁒cons𑁒inv with "Hδs") as "(Hδ & _)".
          iDestruct (pointsto𑁒exclusive with "Hroot Hδ") as %[].
        }
        specialize (Hδs_nil eq_refl) as ->.
        iSteps. rewrite decide_False //. iSteps.

      - destruct_decide (base' = base) as -> | Hbase'_.

        + assert (descr = descr') as <- by congruence.
          destruct δs as [| δ δs].
          { iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs") as %?. done. }
          iDestruct (deltas۰chain𑁒cons𑁒inv with "Hδs") as "(Hδ & Hδs)".
          wp۰load.
          iDestruct (deltas۰chain𑁒cons with "Hδ Hδs") as "Hδs".
          wp۰apply+ (sstore_2٠reroot𑁒spec with "[- Hl_gen Hl_root HΦ]") as (ϵs') "(Hbase & Hstore & %Hϵs' & Hauth & Hdescr & Hcnodes)"; first done.
          { apply treemap۰path𑁒nil. }
          { iFrame "#∗". iSteps. }
          do 2 wp۰store.
          iApply "HΦ".
          iExists l, γ, ˖g', base, descr.(descriptor۰store). unshelve iStep 8.
          { iPureIntro. split; first done.
            eapply store۰generation𑁒le; last done. naive_solver.
          }
          iExists cnodes, ϵs', base, descr, []. iSteps.

        + assert (delete base cnodes !! base' = Some descr') as Hdelete_cnodes_lookup_base'.
          { rewrite lookup_delete_ne //. }
          iAssert (∃ ϵ, ⌜ϵs !! base' = Some ϵ⌝)%I as "(%ϵ & %Hϵs_lookup_base')".
          { iDestruct (big_sepM2_lookup_l with "Hcnodes") as "(% & % & _)"; first done.
            iSteps.
          }
          iDestruct (big_sepM2_lookup_acc with "Hcnodes") as "((%descr_cnode & %Hcnodes_lookup_cnode & (%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs'_nodup & %Hδs' & Hδs') & Hcnodes)"; [done.. |].
          destruct ϵ.2 as [| δ δs'] eqn:Hδ.
          { iDestruct (deltas۰chain𑁒nil𑁒inv with "Hδs'") as %?.
            opose proof* treemap۰rooted𑁒acyclic as []; done.
          }
          iDestruct (deltas۰chain𑁒cons𑁒inv with "Hδs'") as "(Hδ & Hδs')".
          wp۰load. wp۰pures.
          iDestruct (deltas۰chain𑁒cons with "Hδ Hδs'") as "Hδs'".
          rewrite <- Hδ in *. clear Hδ δ δs'.
          opose proof* treemap۰rooted𑁒path as (path & Hpath); [done.. |].
          wp۰apply+ (sstore_2٠reroot𑁒spec (cnodes := cnodes) with "[- Hl_gen Hl_root HΦ]") as (ϵs') "(Hbase' & Hstore' & %Hϵs' & Hauth & Hdescr' & Hcnodes)"; [done.. | |].
          { iFrame "#∗". iSteps. }
          do 2 wp۰store.
          iApply "HΦ".
          iExists l, γ, ˖g', base', descr'.(descriptor۰store). unshelve iStep 8.
          { iPureIntro. split; first done.
            eapply store۰generation𑁒le; last done. naive_solver.
          }
          iExists cnodes, ϵs', base', descr', []. iSteps.
    Qed.
  End sstore_2۰G.

  #[global] Opaque sstore_2۰model.
  #[global] Opaque sstore_2۰snapshot.
End base.

Require zoo_persistent.sstore_2__opaque.

Class Sstore2G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] sstore_2۰G۰raw۰G :: base.Sstore2G Σ
  ; #[local] sstore_2۰G۰support۰G :: MonoGmapG Σ location val
  }.

Definition sstore_2۰Σ :=
  #[base.sstore_2۰Σ
  ; mono_gmap۰Σ location val
  ].
#[global] Instance subG𑁒sstore_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG sstore_2۰Σ Σ →
  Sstore2G Σ.
Proof.
  solve_inG.
Qed.

Section sstore_2۰G.
  Context `{sstore_2۰G : Sstore2G Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Type γ : metadata.

  Definition sstore_2۰model t σ : iProp Σ :=
    ∃ l γ σ₀ ς,
    ⌜t = #l⌝ ∗
    ⌜σ ⊆ ς ∪ σ₀⌝ ∗
    l ↪[nroot.@"user"] γ ∗
    mono_gmap۰auth γ (DfracOwn 1) σ₀ ∗
    base.sstore_2۰model t σ₀ ς.

  Definition sstore_2۰snapshot s t σ : iProp Σ :=
    ∃ l γ σ₀ ς,
    ⌜t = #l⌝ ∗
    ⌜σ ⊆ ς ∪ σ₀⌝ ∗
    l ↪[nroot.@"user"] γ ∗
    mono_gmap۰lb γ σ₀ ∗
    base.sstore_2۰snapshot s t ς.

  #[global] Instance sstore_2۰model𑁒timeless t σ :
    Timeless (sstore_2۰model t σ).
  Proof.
    apply _.
  Qed.

  #[global] Instance sstore_2۰snapshot𑁒persistent s t σ :
    Persistent (sstore_2۰snapshot s t σ).
  Proof.
    apply _.
  Qed.

  Lemma sstore_2۰model𑁒exclusive t σ1 σ2 :
    sstore_2۰model t σ1 -∗
    sstore_2۰model t σ2 -∗
    False.
  Proof.
    iIntros "(%l1 & %γ1 & %σ₀1 & %ς1 & %Heq1 & _ & _ & _ & Hmodel1) (%l2 & %γ2 & %σ₀2 & %ς2 & %Heq2 & _ & _ & _ & Hmodel2)".
    iApply (base.sstore_2۰model𑁒exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma sstore_2٠create𑁒spec :
    {{{
      True
    }}}
      sstore_2٠create ()
    {{{
      t
    , RET t;
      sstore_2۰model t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp𑁒fupd.
    wp۰apply (base.sstore_2٠create𑁒spec with "[//]") as (t) "((%l & -> & Hmeta) & Ht)".
    iMod mono_gmap𑁒alloc as "(%γ & Hauth)".
    iMod (meta𑁒set γ with "Hmeta") as "Hmeta"; first done.
    iSteps. iExists ∅, ∅. iSteps.
  Qed.

  Lemma sstore_2٠ref𑁒spec t σ v :
    {{{
      sstore_2۰model t σ
    }}}
      sstore_2٠ref t v
    {{{
      r
    , RET #r;
      ⌜σ !! r = None⌝ ∗
      sstore_2۰model t (<[r := v]> σ)
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %σ₀ & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (base.sstore_2۰model𑁒valid with "Ht") as %Hς_dom.
    iApply wp𑁒fupd.
    wp۰apply (base.sstore_2٠ref𑁒spec with "Ht") as (r) "(%Hσ₀_lookup & Ht)".
    assert (ς !! r = None) as Hς_lookup.
    { rewrite -!not_elem_of_dom in Hσ₀_lookup |- *. set_solver. }
    assert (σ !! r = None) as Hσ_lookup.
    { eapply lookup_weaken_None; last done. apply lookup_union_None_2; done. }
    iMod (mono_gmap𑁒insert with "Hauth") as "Hauth"; first done.
    iApply "HΦ".
    iStep. iExists l, γ, (<[r := v]> σ₀), ς. iSteps. iPureIntro.
    rewrite -insert_union_r //. apply insert_mono. done.
  Qed.

  Lemma sstore_2٠get𑁒spec {t σ r} v :
    σ !! r = Some v →
    {{{
      sstore_2۰model t σ
    }}}
      sstore_2٠get t #r
    {{{
      RET v;
      sstore_2۰model t σ
    }}}.
  Proof.
    iIntros "%Hσ_lookup %Φ (%l & %γ & %σ₀ & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    wp۰apply (base.sstore_2٠get𑁒spec with "Ht") as "Ht".
    { eapply lookup_weaken; done. }
    iSteps.
  Qed.

  Lemma sstore_2٠set𑁒spec t σ r v :
    r ∈ dom σ →
    {{{
      sstore_2۰model t σ
    }}}
      sstore_2٠set t #r v
    {{{
      RET ();
      sstore_2۰model t (<[r := v]> σ)
    }}}.
  Proof.
    iIntros "%Hr %Φ (%l & %γ & %σ₀ & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (base.sstore_2۰model𑁒valid with "Ht") as %Hς_dom.
    wp۰apply (base.sstore_2٠set𑁒spec with "Ht") as "Ht".
    { apply subseteq_dom in Hσ. set_solver. }
    iApply "HΦ".
    iExists l, γ, σ₀, (<[r := v]> ς). iSteps. iPureIntro.
    rewrite -insert_union_l. apply insert_mono. done.
  Qed.

  Lemma sstore_2٠capture𑁒spec t σ :
    {{{
      sstore_2۰model t σ
    }}}
      sstore_2٠capture t
    {{{
      s
    , RET s;
      sstore_2۰model t σ ∗
      sstore_2۰snapshot s t σ
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %σ₀ & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (mono_gmap۰lb𑁒get with "Hauth") as "#Hlb".
    wp۰apply (base.sstore_2٠capture𑁒spec with "Ht") as (s) "(Ht & Hs)".
    iSteps.
  Qed.

  Lemma sstore_2٠restore𑁒spec t σ s σ' :
    {{{
      sstore_2۰model t σ ∗
      sstore_2۰snapshot s t σ'
    }}}
      sstore_2٠restore t s
    {{{
      RET ();
      sstore_2۰model t σ'
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %σ₀ & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) & (%_l & %_γ & %σ₀' & %ς' & %Heq & %Hσ' & _Hmeta & #Hlb & Hs)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp۰apply (base.sstore_2٠restore𑁒spec with "[$Ht $Hs]") as "Ht".
    iDestruct (mono_gmap۰lb𑁒valid with "Hauth Hlb") as %Hσ₀'.
    iApply "HΦ".
    iExists l, γ, σ₀, ς'. iSteps. iPureIntro.
    trans (ς' ∪ σ₀'); first done. apply map_union_mono_l. done.
  Qed.
End sstore_2۰G.

#[global] Opaque sstore_2۰model.
#[global] Opaque sstore_2۰snapshot.
