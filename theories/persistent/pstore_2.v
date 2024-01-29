From zebre Require Import
  prelude.
From iris.algebra Require Import gmap.
From zebre.language Require Import
  notations
  diaframe.
From zebre.persistent Require Export
  base.
From zebre Require Import
  assert
  lst.
From zebre Require Import
  options.

From zebre.persistent Require Import
  map_agree.

Implicit Types l r : loc.
Implicit Types v t s : val.
Implicit Types σ : gmap loc val.

#[local] Notation "'snap_store'" :=
  0
( in custom zebre_proj
).
#[local] Notation "'snap_root'" :=
  1
( in custom zebre_proj
).

#[local] Notation "'Root'" :=
  ("descr", 0)
( in custom zebre_tag
).
#[local] Notation "'Diff'" :=
  ("descr", 1)
( in custom zebre_tag
).

Definition pstore_create : val :=
  λ: <>,
    ref (ref §Root).

Definition pstore_ref : val :=
  λ: "v",
    ref "v".

Definition pstore_get : val :=
  λ: "t" "r",
    !"r".

Definition pstore_set : val :=
  λ: "t" "r" "v",
    let: "root" := ref §Root in
    !"t" <- ‘Diff{ "r", !"r", "root" } ;;
    "r" <- "v" ;;
    "t" <- "root".

Definition pstore_capture : val :=
  λ: "t",
    ("t", !"t").

Definition pstore_collect : val :=
  rec: "pstore_collect" "node" "acc" :=
    match: !"node" with
    | Root =>
        ("node", "acc")
    | Diff <> <> "node'" =>
        "pstore_collect" "node'" ‘Cons{ "node", "acc" }
    end.
Definition pstore_revert : val :=
  rec: "pstore_revert" "node" "seg" :=
    match: "seg" with
    | Nil =>
        "node" <- §Root
    | Cons "node'" "seg" =>
        match: !"node'" with
        | Root =>
            Fail
        | Diff "r" "v" "node_" =>
            assert ("node_" = "node") ;;
            "node" <- ‘Diff{ "r", !"r", "node'" } ;;
            "r" <- "v" ;;
            "pstore_revert" "node'" "seg"
        end
    end.
Definition pstore_reroot : val :=
  λ: "node",
    let: "collect" := pstore_collect "node" §Nil in
    pstore_revert "collect".<0> "collect".<1>.

Definition pstore_restore : val :=
  λ: "t" "s",
    if: "t" ≠ "s".<snap_store> then (
      Fail
    ) else (
      let: "root" := "s".<snap_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> =>
          pstore_reroot "root" ;;
          "t" <- "root"
      end
    ).

Class PstoreG Σ `{zebre_G : !ZebreG Σ} := {
    pstore_G_map_G : map_agreeG Σ nat (loc * gmap loc val)%type;
}.

Definition pstore_Σ := #[
  map_agreeΣ nat (loc * gmap loc val)%type
].
#[global] Instance subG_pstore_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG pstore_Σ Σ →
  PstoreG Σ.
Proof.
  solve_inG.
Qed.

#[local] Existing Instance pstore_G_map_G.

(* Define [rtcl]: a rtc in a labeled transition system. *)
Section rtc_lab.
Context {A B:Type}.
Context (R:A -> B -> A -> Prop).

Inductive rtcl : A -> list B -> A -> Prop :=
| rtcl_refl : forall a, rtcl a [] a
| rtcl_l : forall a1 b a2 bs a3,
    R a1 b a2 ->
    rtcl a2 bs a3 ->
    rtcl a1 (b::bs) a3.

Lemma rtcl_r a1 b a2 bs a3 :
  rtcl a1 bs a2 ->
  R a2 b a3 ->
  rtcl a1 (bs++[b]) a3.
Proof.
  induction 1.
  { eauto using rtcl_refl,rtcl_l. }
  { intros. rewrite -app_comm_cons. eauto using rtcl_l. }
Qed.


Lemma rtcl_ind_r_weak (P : A -> list B → A → Prop)
  (Prefl : ∀ x, P x [] x) (Pstep : ∀ x bs y b z, rtcl x bs y → R y b z → P x bs y → P x (bs++[b]) z) :
  ∀ x bs z, rtcl x bs z → P x bs z.
Proof.
  cut (∀ y bs z, rtcl y bs z → ∀ x bs', rtcl x bs' y → P x bs' y → P x (bs'++bs) z).
  { intros. specialize (H x bs z H0 x nil). simpl in *. eauto using rtcl_refl. }
  { induction 1.
    { intros. rewrite right_id_L //. }
    { intros. rewrite cons_middle assoc_L. eauto using rtcl_r. } }
Qed.

Lemma rtcl_ind_r (P : list B -> A → Prop) (x : A)
  (Prefl : P nil x) (Pstep : ∀ bs y b z, rtcl x bs y → R y b z → P bs y → P (bs++[b]) z) :
  ∀ bs z, rtcl x bs z → P bs z.
Proof.
  intros bs z p. revert x bs z p Prefl Pstep.
  refine (rtcl_ind_r_weak _ _ _); eauto.
Qed.

Lemma rtcl_inv_r x bs z :
  rtcl x bs z → (x = z /\ bs = nil) ∨ ∃ bs' b y, bs = bs' ++ [b] /\ rtcl x bs' y ∧ R y b z.
Proof.
  revert bs z. apply rtcl_ind_r; eauto.
  intros ?????? [(->&->)|(bs'&b&y&->&?&?)]; right.
  { exists nil. eauto using rtcl_refl. }
  { exists (bs' ++ [b]). eauto. }
Qed.

End rtc_lab.

(* Define a labeled graph, as a set of edges. *)
Section Graph.
Definition graph (A B:Type) `{Countable A} `{Countable B} := gset (A*B*A).

Context `{Countable A} `{Countable B}.
Definition vertices (g:graph A B) : gset A :=
  set_fold (fun '(x,_,y) acc => {[x;y]} ∪ acc) ∅ g.

Lemma vertices_empty :
  vertices ∅ = ∅.
Proof. compute_done. Qed.

Definition vin {A B C:Type} (x:(A*B*C)) := match x with (a,_,_) => a end.
Definition vout {A B C:Type} (x:(A*B*C)) := match x with (_,_,c) => c end.

Lemma elem_of_vertices x (g:graph A B) :
  x ∈ vertices g <-> exists b y, ((x,b,y) ∈ g \/ (y,b,x) ∈ g).
Proof.
  apply set_fold_ind_L with (P := fun f g => x ∈ f  <-> exists b y, ((x,b,y) ∈ g \/ (y,b,x) ∈ g)).
  set_solver.
  intros ((?,?),?). set_solver.
Qed.

Lemma vertices_singleton (x:(A*B*A)) :
  vertices {[x]} = {[vin x; vout x]}.
Proof.
  rewrite /vertices set_fold_singleton. destruct x as ((?&?)&?); set_solver.
Qed.

Lemma vertices_union (g1 g2:graph A B) :
  vertices (g1 ∪ g2) = vertices g1 ∪ vertices g2.
Proof.
  revert g2. induction g1 using set_ind_L; intros g2.
  { rewrite /vertices set_fold_empty !left_id_L //. }
  replace ({[x]} ∪ X ∪ g2) with (X ∪ ({[x]} ∪ g2)) by set_solver.
  rewrite (union_comm_L _  X).
  rewrite !IHg1. rewrite -union_assoc_L. f_equal.
  destruct_decide (decide (x ∈ g2)).
  { replace ({[x]} ∪ g2) with g2 by set_solver.
    rewrite vertices_singleton.
    assert ({[vin x; vout x]} ⊆ vertices g2); last by set_solver.
    intros l Hl. apply elem_of_vertices.
    rewrite elem_of_union !elem_of_singleton in Hl. destruct x as ((?,?),?). set_solver. }
  rewrite {1}/vertices /set_fold. simpl.
  rewrite (foldr_permutation _ _ _ _ (x::elements g2)).
  { intros. destruct a1 as ((?,?),?),a2 as ((?,?),?); set_solver. }
  { by apply elements_union_singleton. }
  { simpl. rewrite vertices_singleton. destruct x as ((?,?),?). set_solver. }
Qed.


Definition edge (g:graph A B) x c y := (x,c,y) ∈ g.
Definition reachable (g:graph A B) x bs y := rtcl (edge g) x bs y.

Lemma reachable_weak g1 g2 x bs y :
  reachable g1 x bs y ->
  g1 ⊆ g2 ->
  reachable g2 x bs y.
Proof.
  induction 1; intros Hi. apply rtcl_refl. eapply rtcl_l.
  by apply Hi. by apply IHrtcl.
Qed.

Lemma reachable_inv_in_invertices g x1 ds x2 :
  reachable g x1 ds x2 ->
  (x1 = x2) \/ (x1 ∈ vertices g /\ x2 ∈ vertices g).
Proof.
  inversion 1. eauto. subst. right.
  split. apply elem_of_vertices. eauto.
  apply rtcl_inv_r in H3. destruct H3 as [(->&->)|(?&?&?&->&?&?)].
  all:apply elem_of_vertices; eauto.
Qed.

Lemma reachable_cycle_end_inv_aux g (r r':A) b ds x1 x2 :
  r ≠ r' ->
  x2 ≠ r' ->
  r' ∉ vertices g ->
  reachable ({[(r, b, r')]} ∪ g) x1 ds x2 ->
  reachable g x1 ds x2.
Proof.
  induction 4.
  { apply rtcl_refl. }
  { eapply rtcl_l with a2.
    { rewrite /edge elem_of_union elem_of_singleton in H4.
      destruct H4 as [|]; last done.
      inversion H4. subst. inversion H5. congruence. subst.
      exfalso. apply H3. apply elem_of_vertices. set_solver. }
    by eapply IHrtcl. }
Qed.

Lemma reachable_cycle_end_inv g (r r':A) b ds x :
  r ≠ r' ->
  r' ∉ vertices g ->
  reachable ({[(r, b, r')]} ∪ g) x ds x ->
  reachable g x ds x.
Proof.
  intros.
  destruct_decide (decide (x=r')).
  { subst. inversion H3. apply rtcl_refl. subst. exfalso. apply H2. apply elem_of_vertices. set_solver. }
  eapply reachable_cycle_end_inv_aux; last done. all:done.
Qed.

Lemma reachable_add_end (r r':A) b x ds g :
  r ≠ r' ->
  r' ∉ vertices g ->
  reachable ({[(r, b, r')]} ∪ g) x ds r' ->
  (ds = nil /\ x = r') \/ (exists ds', ds = ds' ++ [b] /\ reachable g x ds' r).
Proof.
  intros Hrr' Hr' Hreach. apply rtcl_inv_r in Hreach.
  destruct Hreach as [(->&->)|(bs'&b0&y&->&Hreach&Hedge)].
  { eauto. }
  right.
  assert (b0=b /\ y=r) as (->&->).
  { rewrite /edge elem_of_union elem_of_singleton in Hedge.
    destruct Hedge. naive_solver. exfalso. apply Hr', elem_of_vertices. eauto. }
  eexists. split; first done.
  eauto using reachable_cycle_end_inv_aux.
Qed.

Inductive path : A -> list (A*B*A) -> A -> Prop :=
| path_nil : forall a, path a [] a
| path_cons : forall a1 b a2 bs a3,
    path a2 bs a3 ->
    path a1 ((a1,b,a2)::bs) a3.

Definition proj1 {A B C:Type} (x:(A*B*C)) : A :=
  match x with (x,_,_) => x end.
Definition proj2 {A B C:Type} (x:(A*B*C)) : B :=
  match x with (_,x,_) => x end.
Definition proj3 {A B C:Type} (x:(A*B*C)) : C :=
  match x with (_,_,x) => x end.

Definition acyclic g := forall (r:A) ds, reachable g r ds r -> ds = nil.

Lemma reachable_path g a1 a2 ds :
  reachable g a1 ds a2 ->
  exists xs, path a1 xs a2 /\ (list_to_set xs ⊆ g) /\ (proj2 <$> xs = ds).
Proof.
  intros Hreach. induction Hreach.
  { exists nil. split_and !; try done. eauto using path_nil. }
  { destruct IHHreach as (xs&?&?&Hxs).
    exists ((a1,b,a2)::xs). split_and !.
    { eauto using path_cons. }
    { set_solver. }
    { rewrite fmap_cons Hxs //. } }
Qed.

Lemma reachable_path2 g a1 a2 xs :
  path a1 xs a2 ->
  list_to_set xs ⊆ g ->
  reachable g a1 (proj2 <$> xs) a2.
Proof.
  intros Hpath. revert g. induction Hpath.
  { intros. apply rtcl_refl. }
  { intros g Hg. simpl. apply rtcl_l with a2. set_solver.
    eapply IHHpath. set_solver. }
Qed.

Lemma path_app_inv a1 a2 xs ys :
  path a1 (xs ++ ys) a2 ->
  exists a, path a1 xs a /\ path a ys a2.
Proof.
  revert a1 ys a2. induction xs as [| ((?,?),?)].
  { eauto using path_nil. }
  { intros. rewrite -app_comm_cons in H1. inversion H1. subst.
    apply IHxs in H8. destruct H8 as (?&?&?).
    eauto using path_cons. }
Qed.

Lemma path_snoc_inv a1 a2 a3 a4 b xs :
  path a1 (xs ++ [(a2,b,a3)]) a4 ->
  path a1 xs a2 /\ a3 = a4.
Proof.
  intros Hpath. apply path_app_inv in Hpath. destruct Hpath as (?&?&Hpath).
  inversion Hpath. subst. inversion H8. naive_solver.
Qed.

End Graph.

Section pstore_G.
  Context `{pstore_G : PstoreG Σ}.

  Notation diff := (loc*val)%type. (* the loc and its old value. *)
  Notation graph_store := (graph loc diff).
  Notation map_model := (gmap loc (gmap loc val)).

  Definition apply_diffl (ds:list diff) (σ:gmap loc val) : gmap loc val :=
    foldr (fun '(l,v) σ => <[l:=v]> σ) σ ds.

  Record store_inv (M:map_model) (g:graph_store) (r:loc) (σ σr:gmap loc val) :=
    { si1 : dom M = vertices g ∪ {[r]};
      si2 : σ ⊆ σr;
      si3 : M !! r = Some σr ;
      si4 : forall r' ds σ',
        reachable g r' ds r -> M !! r' = Some σ' -> σ' ⊆ (apply_diffl ds σr)
    }.

  Definition locs_of_edges_in g (X:gset loc) :=
    forall r l v r', edge g r (l,v) r' -> l ∈ X.

  Record coherent (σ0 σr:gmap loc val) (g:graph_store) :=
    { coh1 : σr ⊆ σ0;
      coh2 : locs_of_edges_in g (dom σ0);
    }.

  Record graph_inv (g:graph_store) (r:loc) :=
    { gi1 : forall r', r' ∈ vertices g -> exists ds, reachable g r' ds r; (* Everyone can reach the root. *)
      gi2 : acyclic g (* acyclicity. *)
    }.

  Lemma gmap_included_insert `{Countable K} {V} (σ1 σ2:gmap K V) (l:K) (v:V) :
    σ1 ⊆ σ2 ->
    <[l:=v]>σ1 ⊆ <[l:=v]>σ2.
  Proof.
    intros ? l'. destruct_decide (decide (l=l')).
    { subst. rewrite !lookup_insert //. }
    { rewrite !lookup_insert_ne //. }
  Qed.

  Lemma gmap_included_insert_notin `{Countable K} {V} (σ1 σ2:gmap K V) (l:K) (v:V) :
    l ∉ dom σ1 ->
    σ1 ⊆ σ2 ->
    σ1 ⊆ <[l:=v]>σ2.
  Proof.
    intros ?? l'. destruct_decide (decide (l=l')).
    { subst. rewrite lookup_insert // not_elem_of_dom_1 //. }
    { rewrite !lookup_insert_ne //. }
  Qed.

  Lemma incl_dom_incl σ0 σ  :
    σ ⊆ σ0 ->
    dom σ ⊆ dom σ0.
  Proof.
    intros X1.
    intros l Hl. apply elem_of_dom in Hl. destruct Hl as (?&Hl).
    eapply map_subseteq_spec in X1; last done. by eapply elem_of_dom.
  Qed.

  Definition snap_inv (M:map_model) (C:gmap nat (loc * gmap loc val)) :=
    forall n l σ, C !! n = Some (l,σ) -> exists σ', M !! l = Some σ' /\ σ ⊆ σ'.

  #[local] Definition pstore_map_auth γ map :=
    @map_agree_auth _ _ _ _ _ pstore_G_map_G γ map.
  #[local] Definition pstore_map_elem γ n l σ :=
    @map_agree_elem _ _ _ _ _ pstore_G_map_G γ n (l,σ).

  #[local] Definition pstore (γ:gname) (t:val) (σ:gmap loc val) : iProp Σ :=
    ∃ (t0 r:loc) (σ0:gmap loc val) (* the global map, with all the points-to ever allocated *)
      (σr:gmap loc val) (* The largest model of the root *)
      (g:graph_store)
      (M:map_model)
      (C:gmap nat (loc * gmap loc val)),
    ⌜t=#t0 /\ store_inv M g r σ σr /\ coherent σ0 σr g /\ graph_inv g r /\ snap_inv M C⌝ ∗
    t0 ↦ #(LiteralLoc r) ∗
    r ↦ §Root ∗
    pstore_map_auth γ C ∗
    ([∗ map] l ↦ v ∈ σ0, l ↦ v) ∗
    ([∗ set] x ∈ g, let '(r,(l,v),r') := x in r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') }) .

  Definition open_inv : string :=
    "[%t0 [%r [%σ0 [%σr [%g [%M [%C ((->&%Hinv&%Hcoh&%Hgraph&%Hsnap)&Ht0&Hr&HC&Hσ0&Hg)]]]]]]]".

  Lemma pstore_create_spec :
    {{{ True }}}
      pstore_create ()
    {{{ t γ,
      RET t;
        pstore γ t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_alloc r as "Hroot".
    wp_alloc t0 as "Ht0".
    iMod (map_agree_alloc ∅) as "[%γ ?]".
    iApply "HΦ". iModIntro.
    iExists t0,r,∅,∅,∅,{[r := ∅]},∅. iFrame.
    rewrite !big_sepM_empty big_sepS_empty !right_id.
    iPureIntro. split_and!; first done.
    { constructor.
      { rewrite dom_singleton_L vertices_empty //. set_solver. }
      { set_solver. }
      { rewrite lookup_insert //. }
      { intros ??? Hr.
        inversion Hr.
        { subst. rewrite lookup_singleton //. set_solver. }
        { exfalso. subst. set_solver. } } }
    { constructor. set_solver.
      { intros ????. set_solver. } }
    { constructor.
      { intros ?. rewrite vertices_empty. set_solver. }
      { intros ??. inversion 1; subst. done. set_solver. } }
    { intros ??. set_solver. }
  Qed.

  Lemma use_locs_of_edges_in  g r ds r' X :
    locs_of_edges_in g X ->
    reachable g r ds r' ->
    (list_to_set ds.*1) ⊆ X.
  Proof.
    intros He.
    induction 1. set_solver.
    apply He in H. set_solver.
  Qed.

  Lemma dom_apply_diffl ds σ :
    dom (apply_diffl ds σ) = dom σ ∪ (list_to_set ds.*1).
  Proof.
    induction ds as [|(?&?)]; set_solver.
  Qed.

  Lemma apply_diffl_insert_ne ds l v σ :
    l ∉ ds.*1 ->
    apply_diffl ds (<[l:=v]> σ) = <[l:=v]> (apply_diffl ds σ).
  Proof.
    induction ds as [|(?&?)].
    { intros ?. reflexivity. }
    { intros. simpl. rewrite IHds. set_solver.
      rewrite insert_commute //. set_solver. }
  Qed.

  Lemma apply_diffl_app ds ds' σ :
    apply_diffl (ds++ds') σ = apply_diffl ds (apply_diffl ds' σ).
  Proof. rewrite /apply_diffl foldr_app //. Qed.

  Lemma pstore_ref_spec γ t σ v :
    {{{
      pstore γ t σ
    }}}
      pstore_ref v
    {{{ l,
      RET #l;
      ⌜σ !! l = None⌝ ∗
      pstore γ t (<[l := v]> σ)
    }}}.
  Proof.
    iIntros (ϕ) open_inv. iIntros "HΦ".

    wp_rec. wp_alloc l as "Hl".
    iApply "HΦ".

    iAssert ⌜σ0 !! l = None⌝%I as %Hl0.
    { rewrite -not_elem_of_dom. iIntros (Hl).
      apply elem_of_dom in Hl. destruct Hl.
      iDestruct (big_sepM_lookup with "Hσ0") as "Hl_"; first done.
      iDestruct (mapsto_ne with "Hl Hl_") as %?. done. }
    assert (σr !! l = None) as Hl.
    { eapply not_elem_of_dom. apply not_elem_of_dom in Hl0.
      intros ?. apply Hl0. destruct Hcoh. eapply incl_dom_incl; eauto. }
    assert (σ !! l = None).
    { eapply not_elem_of_dom. intros ?. apply not_elem_of_dom in Hl. apply Hl.
      destruct Hinv.
      eapply incl_dom_incl. 2:done. done. }
    iDestruct (mapsto_ne with "Hl Hr") as %Hlr.


    iModIntro. iStep.
    iExists t0,r, (<[l:=v]>σ0),(<[l := v]> σr),g,(<[r:=<[l:=v]>σr]>M),C.

    rewrite big_sepM_insert //. iFrame.
    iPureIntro. split_and !; eauto.
    { destruct Hinv as [X1 X2 X3 X4].
      constructor.
      { rewrite dom_insert_L; set_solver. }
      { eauto using gmap_included_insert. }
      { rewrite lookup_insert //. }
      { intros r' ds σ' Hr. destruct_decide (decide (r=r')).
        { subst. rewrite lookup_insert. eapply gi2 in Hr; eauto. set_solver. }
        { rewrite lookup_insert_ne //.
          intros Hreach. eapply X4 in Hreach; eauto.
          destruct Hcoh as [Z1 Z2].
          eapply use_locs_of_edges_in in Z2. 2:done.
          rewrite apply_diffl_insert_ne.
          { apply not_elem_of_dom in Hl0. set_solver. }
          apply gmap_included_insert_notin; last done.
          apply incl_dom_incl in Z1. apply incl_dom_incl in Hreach.
          rewrite dom_apply_diffl in Hreach.
          apply not_elem_of_dom in Hl0,Hl. set_solver. } } }
    { destruct Hcoh as [X1 X2].
      constructor.
      { eauto using gmap_included_insert. }
      { intros. rewrite dom_insert_L. intros ??. set_solver. } }
    { intros ? r' ? HC. apply Hsnap in HC. destruct HC as (?&?&?).
      destruct_decide (decide (r'=r)).
      { subst. eexists. rewrite lookup_insert. split; first done.
        destruct Hinv as [X1 X2 X3 X4]. specialize (X4 r nil _ (rtcl_refl _ _) H0).
        etrans. apply H1. etrans. apply X4. simpl.
        apply gmap_included_insert_notin; eauto. by apply not_elem_of_dom. }
      { eexists. rewrite lookup_insert_ne //. } }
  Qed.


  Lemma pstore_get_spec {γ t σ l} v :
    σ !! l = Some v →
    {{{
      pstore γ t σ
    }}}
      pstore_get t #l
    {{{
      RET v;
      pstore γ t σ
    }}}.
  Proof.
    iIntros (Hl ϕ) open_inv. iIntros "HΦ".
    wp_rec. iStep 4. iModIntro.

    iDestruct (big_sepM_lookup_acc _ _ l v with "[$]") as "(?&Hσ0)".
    { destruct Hcoh as [X1 X2].
      destruct Hinv as [Z1 Z2 Z3].
      assert (σ ⊆ σ0) as T. etrans; eauto.
      specialize (T l). rewrite Hl in T. destruct (σ0!!l); naive_solver. }

    iSteps.
  Qed.

  Lemma pstore_set_spec γ t σ l v :
    l ∈ dom σ →
    {{{
      pstore γ t σ
    }}}
      pstore_set t #l v
    {{{
      RET ();
      pstore γ t (<[l := v]> σ)
    }}}.
  Proof.
    iIntros (Hl Φ) open_inv. iIntros "HΦ".
    wp_rec. iStep 8. iModIntro.
    wp_alloc r' as "Hr'".

    assert (l ∈ dom σ0) as Hl0.
    { destruct Hcoh as [Z1 _]. destruct Hinv as [_ Z2]. apply incl_dom_incl in Z1,Z2. eauto. }
    apply elem_of_dom in Hl0. destruct Hl0 as (w&Hl0).

    iDestruct (big_sepM_insert_acc with "Hσ0") as "(?&Hσ0)". done.
    wp_load. wp_load. wp_store. iStep 4. iModIntro.
    wp_store. wp_store. iApply "HΦ".

    iSpecialize ("Hσ0" with "[$]").

    iAssert ⌜r ≠ r'⌝%I as %?.
    { iClear "Ht0". iDestruct (mapsto_ne with "[$][$]") as %?. done. }

    iAssert ⌜r' ∉ vertices g⌝%I as %Hr'.
    { iClear "Ht0". iIntros (Hr'). destruct Hgraph as [X1 X2].
      apply X1 in Hr'. destruct Hr' as (?&Hr'). inversion Hr'; subst.
      { done. }
      { destruct b. iDestruct (big_sepS_elem_of with "[$]") as "?". done.
        iDestruct (mapsto_ne with "[$][$]") as %?. congruence. } }

    iModIntro. iExists t0,r',(<[l:=v]> σ0),(<[l:=v]> σr),({[(r,(l,w),r')]} ∪ g), (<[r':=<[l:=v]> σr]>M),C.
    rewrite big_sepS_union.
    { apply disjoint_singleton_l. intros ?. apply Hr'.
      apply elem_of_vertices. eauto. }
    rewrite big_sepS_singleton. iFrame.
    iPureIntro.
    { split_and!; first done.
      { destruct Hinv as [X1 X2 X3 X4].
        constructor.
        { rewrite dom_insert_L vertices_union vertices_singleton //. set_solver. }
        { apply gmap_included_insert. done. }
        { rewrite lookup_insert //. }
        { intros x ds σ' Hreach.
          apply reachable_add_end in Hreach. 2,3:eauto.
          destruct Hreach as [(->&->)|(ds'&->&Hreach)].
          { rewrite lookup_insert. inversion 1. subst. simpl. eauto using gmap_included_insert. }
          rewrite lookup_insert_ne.
          { apply reachable_inv_in_invertices in Hreach. naive_solver. }
          intros Hx. specialize (X4 _ _ _ Hreach Hx). etrans. apply X4.
          rewrite apply_diffl_app. simpl. rewrite insert_insert.
          destruct Hcoh as [Z1 _ ]. rewrite insert_id //.
          assert (exists z, σr !! l = Some z) as (?&Hz).
          { apply elem_of_dom. eapply incl_dom_incl. done. done. }
          specialize (Z1 l). rewrite Hl0 Hz in Z1. naive_solver. } }
      { destruct Hcoh as [X1 X2].
        constructor.
        { eauto using gmap_included_insert. }
        { intros ?. set_solver. } }
      { destruct Hgraph as [X1 X2]. constructor.
        { rewrite vertices_union vertices_singleton. intros x.
          rewrite !elem_of_union !elem_of_singleton.
          intros [[-> | ->] | Hx].
          { exists [(l,w)]. simpl. eapply rtcl_l. 2:apply rtcl_refl. set_solver. }
          { exists nil. apply rtcl_refl. }
          { apply X1 in Hx. destruct Hx as (ds,Hx). exists (ds++[(l,w)]).
            eapply rtcl_r.
            { eapply reachable_weak; eauto. set_solver. }
            { set_solver. } } }
        { intros x ds Hreach. apply reachable_cycle_end_inv in Hreach; eauto. } }
      { intros ? r0 ? HC. apply Hsnap in HC. destruct HC as (?&HC&?).
        destruct_decide (decide (r0=r')).
        { exfalso. subst. destruct Hinv as [X1 X2 X3].
          assert (r' ∉ dom M) as F by set_solver. apply F. by eapply elem_of_dom. }
        rewrite lookup_insert_ne //. eauto. } }
  Qed.

  Definition pstore_snapshot γ t s σ : iProp Σ :=
    ∃ l n, ⌜s=ValTuple [t;#l]⌝ ∗ pstore_map_elem γ n l σ.

  #[global] Instance pstore_snapshot_persistent γ t s σ :
    Persistent (pstore_snapshot γ t s σ).
  Proof.
    apply _.
  Qed.

  Lemma pstore_capture_spec γ t σ :
    {{{
      pstore γ t σ
    }}}
      pstore_capture t
    {{{ s,
      RET s;
      pstore γ t σ ∗
      pstore_snapshot γ t s σ
    }}}.
  Proof.
    iIntros (Φ) open_inv. iIntros "HΦ".
    wp_rec. wp_load. do 5 iStep.

    iMod (map_agree_insert _ _ (fresh (dom C)) (r,σ) with "HC") as "(HC&Hsnap)".
    { apply not_elem_of_dom. apply is_fresh. }
    iModIntro.
    iSplitR "Hsnap". 2:iSteps.
    iExists _,_,_,_,_,_,_. iFrame.
    iPureIntro. split_and!; eauto.
    intros ? r' ? HC.
    destruct_decide (decide (n=fresh (dom C))).
    { subst. rewrite lookup_insert in HC. inversion HC. subst r' σ1.
      destruct Hinv as [X1 X2 X3 X4].
      assert (exists σ', M!! r = Some σ') as (σ',HM).
      { apply elem_of_dom. set_solver. }
      exists σ'. split; first done. naive_solver. }
    { rewrite lookup_insert_ne // in HC. eauto using Hsnap. }
  Qed.

  Definition fsts  (ys:list (loc*(loc*val)*loc)) : list val :=
    (fun '(x,_,_) => ValLiteral (LiteralLoc x)) <$> ys.

  Lemma pstore_collect_spec_aux r r' t' (xs:list val) (ys:list (loc*(loc*val)*loc)) (g:graph_store) :
    path r ys r' ->
    list_to_set ys ⊆ g ->
    {{{ r' ↦ §Root ∗
        lst_model t' xs ∗
        ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') })
    }}}
      pstore_collect #r t'
    {{{ t,
      RET (#r',t);
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') }) ∗
      lst_model t (rev_append (fsts ys) xs)
    }}}.
  Proof.
    iIntros (Hpath Hg Φ) "(Hr'&HL&Hg) HΦ".
    iInduction ys as [|] "IH" forall (r xs r' Hpath Hg t'); wp_rec.
    { inversion Hpath. subst. wp_load. simpl.
      iSteps. rewrite /lst_model //. }
    { inversion Hpath. subst.

      iDestruct (big_sepS_elem_of_acc _ _ (r,b,a2) with "[$]") as "(?&Hg)".
      { set_solver. } destruct b.
      wp_load.
      iSpecialize ("Hg" with "[$]").
      iDestruct (lst_model_Cons (ValLiteral (LiteralLoc r)) with "[$]") as "?".
      iSpecialize ("IH" with "[%][%][$][$][$]"). done. set_solver.
      iStep 19. iModIntro. iStep 3. iApply "IH". iModIntro. iIntros (?) "(?&?&?)".
      iApply ("HΦ"). iFrame. }
  Qed.

 Lemma pstore_collect_spec r r' (ys:list (loc*(loc*val)*loc)) (g:graph_store) :
   path r ys r' ->
   list_to_set ys ⊆ g ->
   {{{ r' ↦ §Root ∗
        ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') })
   }}}
     pstore_collect #r §Nil
   {{{ t,
      RET (#r',t);
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') }) ∗
      lst_model t (rev (fsts ys))
   }}}.
  Proof.
    iIntros (?? Φ) "(?&?) Hϕ".
    iDestruct lst_model_Nil as "?".
    iDestruct (pstore_collect_spec_aux with "[$]") as "Go". done. done.
    iApply "Go". rewrite -rev_alt //. Unshelve. apply _.
  Qed.

  Lemma apply_diffl_snoc_notin x xs σ :
    x.1 ∉ xs.*1 ->
    apply_diffl (xs ++ [x]) σ = apply_diffl (x::xs) σ.
  Proof.
    revert σ. induction xs; intros σ.
    { done. }
    rewrite -app_comm_cons =>?. destruct a. simpl.
    rewrite IHxs. set_solver. destruct x. simpl.
    rewrite insert_commute //. set_solver.
  Qed.

  Lemma apply_diffl_snoc xs l v σ :
    apply_diffl (xs ++ [(l,v)]) σ = apply_diffl xs (<[l:=v]> σ).
  Proof.
    revert σ. induction xs. done.
    intros σ. rewrite -app_comm_cons. simpl.
    rewrite IHxs //.
  Qed.

  Record revset (xs ys: list (loc*(loc*val)*loc)) σ :=
    { re1 :  forall r l r' v,
        (r,(l,v),r') ∈ xs -> (exists v', σ !! l = Some v' /\ (r',(l,v'),r) ∈ ys);
      re2 : forall r l r' v',
        σ !! l = Some v' ->
        (r',(l,v'),r) ∈ ys ->
        exists v, (r,(l,v),r') ∈ xs }.

  (* undo applied generated orig_store *)
  Inductive undo :
    list (loc*(loc*val)*loc) -> list (loc*(loc*val)*loc) -> gmap loc val -> Prop :=
  | undo_nil :
    forall σ, undo [] [] σ
  | undo_cons :
    forall σ r l v v' r' xs ys,
      σ !! l = Some v' ->
      undo xs ys (<[l:=v]> σ) ->
      undo (xs++[(r,(l,v),r')]) ((r',(l,v'),r)::ys) σ
  .

  Lemma use_path r (xs:list (loc*(loc*val)*loc)) r0 x r1 r':
    path r (xs ++ [(r0, x, r1)]) r' ->
    (r0, x, r1) ∈ (list_to_set xs : gset (loc*(loc*val)*loc)) ->
    exists ds, reachable (list_to_set (xs ++ [(r0, x, r1)])) r0 ds r0 /\ ds ≠ nil.
  Proof.
    revert r. induction xs; intros r. set_solver.
    rewrite -app_comm_cons. inversion 1. subst.
    rewrite list_to_set_cons.
    destruct_decide (decide ((r0, x, r1) = (r, b, a2))) as X.
    { inversion X. subst. intros _. clear IHxs.
      rewrite app_comm_cons in H. apply path_snoc_inv in H.
      destruct H as (?&?). subst a2.
      exists (proj2 <$> ((r, b, r') :: xs)). split.
      { eapply reachable_path2. done. set_solver. }
      { done. } }
    { intros ?. apply IHxs in H4. 2:set_solver.
      destruct H4 as (?&?&?). eexists. split; last done.
      eapply reachable_weak. done. set_solver. }
  Qed.

  Lemma acyclic_weak `{Countable A} `{Countable B} (g1 g2:graph A B) :
    acyclic g1 ->
    g2 ⊆ g1 ->
    acyclic g2.
  Proof.
    intros Hacy ? ???. eapply Hacy. by eapply reachable_weak.
  Qed.

  Lemma pstore_revert_spec_aux g1 r t g2 xs r' w σ σ0 :
    locs_of_edges_in g2 (dom σ) ->
    g2 = list_to_set xs ->
    acyclic g2 ->
    path r xs r' ->
    {{{
       lst_model t (fsts (rev xs)) ∗ r' ↦ w ∗
       ([∗ map] l0↦v0 ∈ σ, l0 ↦ v0) ∗
       ([∗ set] '(r, (l, v), r') ∈ g1, r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') }) ∗
       ([∗ set] '(r, (l, v), r') ∈ g2, r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') })
    }}}
      pstore_revert #r' t
    {{{ RET (); ∃ ys, ⌜undo xs ys σ⌝ ∗ r ↦ §Root ∗
        ([∗ set] '(r, (l, v), r') ∈ (g1 ∪ list_to_set ys), r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') }) ∗
        ([∗ map] l0↦v0 ∈ (apply_diffl (proj2 <$> xs) σ), l0 ↦ v0)
    }}}.
  Proof.
    iIntros (Hlocs Hg Hacy Hpath Φ) "(HL&Hr'&Hσ&Hg1&Hg2) HΦ".
    iInduction xs as [|((r0,(l,v)),r1) ] "IH" using rev_ind forall (t σ w r r' Hpath g1 g2 Hg Hlocs Hacy).
    { wp_rec. simpl.
      iStep 4. iModIntro.
      iApply (wp_lst_match_Nil with "[$]") .
      inversion Hpath. subst. wp_store. iModIntro.
      iApply "HΦ". iExists nil. rewrite right_id_L. iFrame.
      iPureIntro. eauto using undo_nil. }
    { wp_rec. simpl. rewrite rev_unit. simpl.
      iStep 4. iModIntro.
      iApply (wp_lst_match_Cons with "[$]") . done.
      iIntros (t') "HL". simpl.
      rewrite list_to_set_app_L list_to_set_cons list_to_set_nil right_id_L.
      assert ((r0, (l, v), r1) ∉ (list_to_set xs : gset (loc * diff * loc))).
      { intros ?. apply use_path in Hpath; last done. destruct Hpath as (?&Hpath&?).
        apply Hacy in Hpath. congruence. }
      iDestruct (big_sepS_union with "Hg2") as "(Hg2&?)".
      { set_solver. }
      rewrite big_sepS_singleton. wp_load. iStep 19. iModIntro.

      rewrite list_to_set_app_L list_to_set_cons list_to_set_nil right_id_L in Hlocs.
      assert (exists v', σ !! l = Some v') as (v',Hl).
      { apply elem_of_dom. eapply Hlocs. rewrite /edge.

        rewrite elem_of_union elem_of_singleton. right. reflexivity. }

      apply path_snoc_inv in Hpath. destruct Hpath as (?&->).
      wp_smart_apply assert_spec. rewrite bool_decide_eq_true_2 //.
      iStep 4. iModIntro.

      iDestruct (big_sepM_insert_acc with "Hσ") as "(?&Hσ)". done.
      wp_load. wp_store. wp_store. iStep 4. iModIntro.

      iSpecialize ("Hσ" with "[$]").
      iSpecialize ("IH" with "[%//][%//][%][%][$][$][$] Hg1 Hg2").
      { rewrite dom_insert_lookup_L //. intros x1 x2 x3 x4.
        specialize (Hlocs x1 x2 x3 x4). set_solver. }
      { eapply acyclic_weak; eauto. rewrite list_to_set_app. set_solver. }

      rewrite fmap_app -apply_diffl_snoc. simpl.
      iApply "IH". iModIntro.
      iIntros "[%ys (%Hundo&?&?&?)]". iApply "HΦ".
      iExists ((r',(l,v'),r0)::ys). iFrame.
      iSplitR.
      { iPureIntro. eauto using undo_cons. }
      rewrite list_to_set_cons.
      iAssert ⌜(r', (l, v'), r0) ∉ g1 ∪ list_to_set ys⌝%I as "%".
      { iIntros (?). iDestruct (big_sepS_elem_of with "[$]") as "?". done.
        iDestruct (mapsto_ne r' r' with "[$][$]") as "%". congruence. }
      replace (g1 ∪ ({[(r', (l, v'), r0)]} ∪ list_to_set ys)) with ({[(r', (l, v'), r0)]} ∪ ((g1 ∪ list_to_set ys))). 2:set_solver.
      iApply big_sepS_union. set_solver.
      iFrame. rewrite big_sepS_singleton //. }
  Qed.

  Lemma pstore_revert_spec r t g xs r' w σ σ0 :
    locs_of_edges_in g (dom σ) ->
    g = list_to_set xs ->
    acyclic g ->
    path r xs r' ->
    {{{
       lst_model t (fsts (rev xs)) ∗ r' ↦ w ∗
       ([∗ map] l0↦v0 ∈ σ, l0 ↦ v0) ∗
       ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') })
    }}}
      pstore_revert #r' t
    {{{ RET (); ∃ ys, ⌜undo xs ys σ⌝ ∗ r ↦ §Root ∗
        ([∗ set] '(r, (l, v), r') ∈ (list_to_set ys), r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') }) ∗
        ([∗ map] l0↦v0 ∈ (apply_diffl (proj2 <$> xs) σ), l0 ↦ v0)
    }}}.
  Proof.
    iIntros (???? Φ) "(?&?&?&?) HΦ".
    iApply (pstore_revert_spec_aux ∅ with "[-HΦ]"); try done.
    { rewrite big_sepS_empty. iFrame. }
    { iModIntro. iIntros "[% ?]". iApply "HΦ". iExists _. rewrite left_id_L //. }
  Qed.

  Lemma rev_fsts xs :
    rev (fsts xs) = fsts (rev xs).
  Proof.
    induction xs as [|((?,?),?)]; simpl; eauto.
    rewrite IHxs /fsts fmap_app //.
  Qed.

  Lemma pstore_reroot_spec r (xs:list (loc*(loc*val)*loc)) r' g σ :
    locs_of_edges_in g (dom σ) ->
    g = list_to_set xs ->
    acyclic g ->
    path r xs r' ->
    {{{
       r' ↦ §Root ∗
       ([∗ map] l0↦v0 ∈ σ, l0 ↦ v0) ∗
       ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') })
    }}}
      pstore_reroot #r
    {{{ RET ();
        ∃ ys, ⌜undo xs ys σ⌝ ∗ r ↦ §Root ∗
        ([∗ set] '(r, (l, v), r') ∈ (list_to_set ys), r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') }) ∗
        ([∗ map] l0↦v0 ∈ (apply_diffl (proj2 <$> xs) σ), l0 ↦ v0)
    }}}.
  Proof.
    iIntros (???? Φ) "(Hr'&Hσ&Hg) HΦ".
    wp_rec. wp_apply (pstore_collect_spec with "[$]"). done. set_solver.
    iIntros (?) "(?&?&?)".
    iStep 10. rewrite rev_fsts.
    iApply (pstore_revert_spec with "[-HΦ]"); try done. iFrame.
  Qed.

  Lemma locs_of_edges_weak g1 g2 X :
    locs_of_edges_in g1 X ->
    g2 ⊆ g1 ->
    locs_of_edges_in g2 X.
  Proof.
    intros Z ? a b c d ?. eapply (Z a b c d). set_solver.
  Qed.


  Lemma undo_vertices xs ys σ :
    undo xs ys σ ->
    vertices (list_to_set ys) = vertices (list_to_set xs).
  Proof.
    revert xs σ. induction ys; intros xs σ; inversion 1; subst. done.
    simpl. rewrite list_to_set_app_L !vertices_union !vertices_singleton. simpl.
    erewrite IHys; last done. rewrite vertices_empty. set_solver.
  Qed.

  Lemma pstore_restore_spec γ t σ s σ' :
    {{{
      pstore γ t σ ∗
      pstore_snapshot γ t s σ'
    }}}
      pstore_restore t s
    {{{
      RET ();
      pstore γ t σ'
    }}}.
  Proof.
    iIntros (Φ) "(HI&Hsnap) HΦ".
    iDestruct "HI" as open_inv.
    iDestruct "Hsnap" as "(%rs&%&->&Hsnap)".
    wp_rec. iStep 20.

    iDestruct (map_agree_lookup with "[$][$]") as "%Hrs".
    apply Hsnap in Hrs. destruct Hrs as (σ1&HMrs&?).

    destruct_decide (decide (rs=r)).
    { subst.
      subst.
      wp_load. iStep 9. iModIntro.
      iExists _,_,_,_,_,_,_. iFrame. iPureIntro. split_and!; eauto.
      { destruct Hinv as [X1 X2 X3 X4]. constructor; eauto. naive_solver. } }

    assert (rs ∈ vertices g) as Hrs.
    { destruct Hinv. apply elem_of_dom_2 in HMrs. set_solver. }

    eapply gi1 in Hrs; eauto. destruct Hrs as (ds,Hrs).
    inversion Hrs. congruence. subst. rename a2 into r'. destruct b.
    iDestruct (big_sepS_elem_of_acc with "[$]") as "(?&Hg)". done. simpl.
    wp_load. iStep 19. iModIntro.
    iSpecialize ("Hg" with "[$]").

    generalize Hrs. intros Hrsold.
    apply reachable_path in Hrsold.
    destruct Hrsold as (xs&Hpath&Hg&Hproj).
    rewrite (union_difference_L (list_to_set xs) g) //.
    iDestruct (big_sepS_union with "Hg") as "(Hxs&Hg)". set_solver.
    wp_apply (pstore_reroot_spec with "[Hr Hxs Hσ0]"). 2,4:done. 3:iFrame.
    { destruct Hcoh as [_ X]. eapply locs_of_edges_weak; eauto. }
    { destruct Hgraph. eapply acyclic_weak; eauto. }

    iIntros "[%ys (%Hundo&?&?&?)]".
    iStep 8. do 2 iModIntro.
    iApply "HΦ".
    iDestruct (big_sepS_union_2 with "[$][$]") as "?".

    iExists _,_,_,(apply_diffl (proj2 <$> xs) σ0),_,(<[rs:=apply_diffl (proj2 <$> xs) σ0]> M),_. iFrame.
    iPureIntro. split_and !.
    { done. }
    { destruct Hinv as [X1 X2 X3 X4]. constructor.
      { rewrite dom_insert_L X1. apply undo_vertices in Hundo.
        rewrite vertices_union Hundo -vertices_union -union_difference_L //.
        apply elem_of_dom_2 in X3,HMrs. apply reachable_inv_in_invertices in Hrs.
        set_solver. }
      { eapply X4 in Hrs; last done. rewrite Hproj. admit. }
      { rewrite lookup_insert //. }
      { admit. } }
    { destruct Hcoh as [X1 X2]. constructor. all:admit. }
    { admit. }
    { admit. }
  Qed.

End pstore_G.

#[global] Opaque pstore_create.
#[global] Opaque pstore_ref.
#[global] Opaque pstore_get.
#[global] Opaque pstore_set.
#[global] Opaque pstore_capture.
#[global] Opaque pstore_restore.

#[global] Opaque pstore.
#[global] Opaque pstore_snapshot.
