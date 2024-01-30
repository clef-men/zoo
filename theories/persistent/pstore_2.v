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

Implicit Types l : loc.
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

Inductive path (g:graph A B) : A -> list (A*B*A) -> A -> Prop :=
| path_nil : forall a, path g a [] a
| path_cons : forall a1 b a2 bs a3,
    (a1,b,a2) ∈ g ->
    path g a2 bs a3 ->
    path g a1 ((a1,b,a2)::bs) a3.

Definition proj1 {A B C:Type} (x:(A*B*C)) : A :=
  match x with (x,_,_) => x end.
Definition proj2 {A B C:Type} (x:(A*B*C)) : B :=
  match x with (_,x,_) => x end.
Definition proj3 {A B C:Type} (x:(A*B*C)) : C :=
  match x with (_,_,x) => x end.

Lemma reachable_path g a1 a2 ds :
  reachable g a1 ds a2 ->
  exists xs, path g a1 xs a2 /\ (proj2 <$> xs = ds).
Proof.
  intros Hreach. induction Hreach.
  { exists nil. split_and !; try done. eauto using path_nil. }
  { destruct IHHreach as (xs&?&Hxs).
    exists ((a1,b,a2)::xs). split_and !.
    { eauto using path_cons. }
    { set_solver. } }
Qed.

Lemma reachable_path2 g a1 a2 xs :
  path g a1 xs a2 ->
  reachable g a1 (proj2 <$> xs) a2.
Proof.
  induction 1.
  { intros. apply rtcl_refl. }
  { apply rtcl_l with a2. set_solver. done. }
Qed.

Lemma path_app_inv g a1 a2 xs ys :
  path g a1 (xs ++ ys) a2 ->
  exists a, path g a1 xs a /\ path g a ys a2.
Proof.
  revert a1 ys a2. induction xs as [| ((?,?),?)].
  { eauto using path_nil. }
  { intros. rewrite -app_comm_cons in H1. inversion H1. subst.
    apply IHxs in H9. destruct H9 as (?&?&?).
    eauto using path_cons. }
Qed.

Lemma path_snoc_inv g a1 a2 a3 a4 b xs :
  path g a1 (xs ++ [(a2,b,a3)]) a4 ->
  path g a1 xs a2 /\ a3 = a4 /\ (a2,b,a3) ∈ g.
Proof.
  intros Hpath. apply path_app_inv in Hpath. destruct Hpath as (?&?&Hpath).
  inversion Hpath. subst. inversion H9. naive_solver.
Qed.

Definition acyclic g := forall a xs, path g a xs a -> xs = nil.

Record rooted_dag g (r:A) :=
  { ti1 : forall a, a ∈ vertices g -> exists xs, path g a xs r;
    ti2 : acyclic g
  }.

Lemma rooted_dag_empty (r:A) :
    rooted_dag (∅ : graph A B) r.
Proof.
  constructor.
  { intros ?. rewrite vertices_empty. set_solver. }
  { intros ??. inversion 1; set_solver. }
Qed.

Lemma path_cycle_end_inv_aux g (r r':A) b ds x1 x2 :
  r ≠ r' ->
  x2 ≠ r' ->
  r' ∉ vertices g ->
  path ({[(r, b, r')]} ∪ g) x1 ds x2 ->
  path g x1 ds x2.
Proof.
  induction 4.
  { apply path_nil. }
  { eapply path_cons.
    { rewrite /edge elem_of_union elem_of_singleton in H4.
      destruct H4 as [|]; last done.
      inversion H4. subst. inversion H5. congruence. subst.
      exfalso. apply H3. apply elem_of_vertices. set_solver. }
    by eapply IHpath. }
Qed.

Lemma path_cycle_end_inv g (r r':A) b ds x :
  r ≠ r' ->
  r' ∉ vertices g ->
  path ({[(r, b, r')]} ∪ g) x ds x ->
  path g x ds x.
Proof.
  intros.
  destruct_decide (decide (x=r')).
  { subst. inversion H3. apply path_nil. subst. exfalso. apply H2. apply elem_of_vertices. set_solver. }
  eapply path_cycle_end_inv_aux; last done. all:done.
Qed.

Lemma path_r g a1 b a2 bs a3 :
  path g a1 bs a2 ->
  (a2,b,a3) ∈ g ->
  path g a1 (bs++[(a2,b,a3)]) a3.
Proof.
  induction 1.
  { intros. apply path_cons. done. apply path_nil. }
  { intros. rewrite -app_comm_cons. eauto using path_cons. }
Qed.

Lemma path_weak g1 g2 x bs y :
  path g1 x bs y ->
  g1 ⊆ g2 ->
  path g2 x bs y.
Proof.
  induction 1; intros Hi. apply path_nil. eapply path_cons.
  by apply Hi. by apply IHpath.
Qed.

Definition kindofinj (g:graph A B) :=
    forall r x1 r1 x2 r2,
    (r,x1,r1) ∈ g ->
    (r,x2,r2) ∈ g ->
    x1 = x2 /\ r1 = r2.

Lemma use_kindofinj g a1 xs ys a2 :
  acyclic g ->
  kindofinj g ->
  path g a1 xs a2 ->
  path g a1 ys a2 ->
  xs = ys.
Proof.
  intros Hacy Hinj Hpath. revert ys. induction Hpath; intros ys.
  { intros Hpath. apply Hacy in Hpath. done. }
  { inversion 1; subst.
    { exfalso.
      assert (path g a3 ((a3, b, a2)::bs) a3) as Z.
      { apply path_cons. done. eauto. }
      apply Hacy in Z. congruence. }
    destruct (Hinj _ _ _ _ _ H1 H3). subst.
    f_equal. eapply IHHpath. done. }
Qed.

Lemma rooted_dag_root_no_succ g r x r' :
  rooted_dag g r ->
  (r,x,r') ∉ g.
Proof.
  intros [X1 X2] Hg.
  assert (r' ∈ vertices g) as E4.
  { apply elem_of_vertices. set_solver. }
  apply X1 in E4. destruct E4 as (zs&?).
  assert (path g r ((r, x, r')::zs) r) as Hpath.
  { apply path_cons. set_solver. done. }
  eapply X2 in Hpath. congruence.
Qed.

Lemma rooted_dag_add (r r':A) g x:
  r ≠ r' ->
  r' ∉ vertices g ->
  rooted_dag g r ->
  rooted_dag ({[(r, x, r')]} ∪ g) r'.
Proof.
  intros Hne Hg Hroot. inversion Hroot as [X1 X2].
  constructor.
  { rewrite vertices_union vertices_singleton. intros a.
    rewrite !elem_of_union !elem_of_singleton.
    intros [[-> | ->] | Hx].
    { exists [(r, x, r')]. simpl. eapply path_cons. set_solver. apply path_nil. }
    { exists nil. apply path_nil. }
    { apply X1 in Hx. destruct Hx as (ds,Hx). exists (ds++[(r, x, r')]).
      eapply path_r.
      { eapply path_weak; eauto. set_solver. }
      { set_solver. } } }
  { intros ?? Hpath. apply  path_cycle_end_inv in Hpath; eauto. }
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
      si4 : forall r1 ds r2 σ1 σ2,
        reachable g r1 ds r2 -> M !! r1 = Some σ1 -> M !! r2 = Some σ2 -> σ1 ⊆ (apply_diffl ds σ2)
    }.

  Definition locs_of_edges_in g (X:gset loc) :=
    forall (r:loc) l v r', edge g r (l,v) r' -> l ∈ X.

  Record coherent (σ0 σr:gmap loc val) (g:graph_store) :=
    { coh1 : σr ⊆ σ0;
      coh2 : locs_of_edges_in g (dom σ0);
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

  Lemma extract_kindofinj g :
    ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(LiteralLoc l), v, #(LiteralLoc r') }) -∗
    ⌜kindofinj g⌝.
  Proof.
    iIntros "Hg" (???????).
    destruct_decide (decide (a0 = a2 ∧ a1 = a3)). done.
    rewrite (big_sepS_delete _ _ (a, a0, a1)). set_solver.
    rewrite (big_sepS_delete _ _ (a, a2, a3)). set_solver.
    iDestruct "Hg" as "(?&?&_)". destruct a0,a2.
    iDestruct (mapsto_ne with "[$][$]") as "%". congruence.
  Qed.

  (* NB our invariant asserts that g is indeed a rooted tree: a rooted DAG
     with unicity of paths. Indeed, from the set of pointsto we can extract [kindofinj],
     (see [extract_kindofinj]), and a DAG with kindofinj guarantees unicity of paths
     (see [use_kindofinj] ) *)

  #[local] Definition pstore (γ:gname) (t:val) (σ:gmap loc val) : iProp Σ :=
    ∃ (t0 r:loc) (σ0:gmap loc val) (* the global map, with all the points-to ever allocated *)
      (σr:gmap loc val) (* The largest model of the root *)
      (g:graph_store)
      (M:map_model)
      (C:gmap nat (loc * gmap loc val)),
    ⌜t=#t0 /\ store_inv M g r σ σr /\ coherent σ0 σr g /\ rooted_dag g r /\ snap_inv M C⌝ ∗
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
      { intros ????? Hr.
        rewrite !lookup_singleton_Some.
        inversion Hr; set_solver. } }
    { constructor. set_solver.
      { intros ????. set_solver. } }
    { eauto using rooted_dag_empty. }
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

    iAssert ⌜forall x y, (r,x,y) ∉ g⌝%I as "%Hrg".
    { iIntros (???). destruct a. iDestruct (big_sepS_elem_of with "Hg") as "?". done.
      iClear "Ht0 Hl".
      iDestruct (mapsto_ne with "[$][$]") as "%". congruence. }


    iModIntro. iStep.
    iExists t0,r, (<[l:=v]>σ0),(<[l := v]> σr),g,(<[r:=<[l:=v]>σr]>M),C.

    rewrite big_sepM_insert //. iFrame.
    iPureIntro. split_and !; eauto.
    { destruct Hinv as [X1 X2 X3 X4].
      constructor.
      { rewrite dom_insert_L; set_solver. }
      { eauto using gmap_included_insert. }
      { rewrite lookup_insert //. }
      { intros r1 ds r2 σ1 σ2 Hr. generalize Hr. intros Hreach.
        destruct_decide (decide (r1=r)).
        { subst. rewrite lookup_insert. inversion 1. subst.
          inversion Hr; subst.
          2:{ exfalso. set_solver. }
          rewrite lookup_insert. inversion 1. done. }
        { rewrite lookup_insert_ne //. intros Hr1.
          destruct_decide (decide (r2=r)).
          { subst. rewrite lookup_insert. inversion 1. subst.
            eapply X4 in Hr. 2,3:done.
            destruct Hcoh as [Z1 Z2].
            eapply use_locs_of_edges_in in Z2. 2:done.
            rewrite apply_diffl_insert_ne.
            { apply not_elem_of_dom in Hl0. set_solver. }
            apply gmap_included_insert_notin; last done.
            apply incl_dom_incl in Z1. apply incl_dom_incl in Hr.
            rewrite dom_apply_diffl in Hr.
            apply not_elem_of_dom in Hl0,Hl. set_solver. }
          { rewrite lookup_insert_ne //. eauto. } } } }
    { destruct Hcoh as [X1 X2].
      constructor.
      { eauto using gmap_included_insert. }
      { intros. rewrite dom_insert_L. intros ??. set_solver. } }
    { intros ? r' ? HC. apply Hsnap in HC. destruct HC as (?&?&?).
      destruct_decide (decide (r'=r)).
      { subst. eexists. rewrite lookup_insert. split; first done.
        destruct Hinv as [X1 X2 X3 X4].
        rewrite X3 in H0. inversion H0. subst.
        apply gmap_included_insert_notin; last done.
        apply incl_dom_incl in H1. intros X. apply H1 in X.
        apply not_elem_of_dom in Hl. done. }
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

    iAssert ⌜forall x y, (r,x,y) ∉ g⌝%I as "%Hrg".
    { iIntros (???). destruct a. iDestruct (big_sepS_elem_of with "Hg") as "?". done.
      iClear "Ht0 Hr'".
      iDestruct (mapsto_ne with "[$][$]") as "%". congruence. }

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
        { intros r1 ds r2 σ1 σ2 Hreach.
          destruct_decide (decide (r'=r1)).
          { subst. rewrite lookup_insert. inversion_clear 1.
            inversion Hreach. subst.
            2:{ exfalso. subst. rewrite /edge elem_of_union in H0.
                destruct H0. set_solver. apply Hr'. apply elem_of_vertices. set_solver. }
            rewrite lookup_insert. inversion 1. done. }
          rewrite lookup_insert_ne //. intros E1.
          destruct_decide (decide (r2=r')).
          { subst. rewrite lookup_insert. inversion 1. subst.
            apply reachable_add_end in Hreach. 2,3:eauto.
            destruct Hreach as [(->&->)|(ds'&->&Hreach)].
            { congruence. }
            specialize (X4 _ _ _ _ _ Hreach E1 X3). etrans. apply X4.
            rewrite apply_diffl_app. simpl. rewrite insert_insert.
            destruct Hcoh as [Z1 _ ]. rewrite insert_id //.
            assert (exists z, σr !! l = Some z) as (?&Hz).
            { apply elem_of_dom. eapply incl_dom_incl. done. done. }
            specialize (Z1 l). rewrite Hl0 Hz in Z1. naive_solver. }
          { rewrite lookup_insert_ne //. intros. eapply X4; eauto.
            apply reachable_cycle_end_inv_aux in Hreach; eauto. } } }
      { destruct Hcoh as [X1 X2].
        constructor.
        { eauto using gmap_included_insert. }
        { intros ?. set_solver. } }
      { eauto using rooted_dag_add. }
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

  Lemma pstore_collect_spec_aux (r r':loc) t' (xs:list val) (ys:list (loc*(loc*val)*loc)) (g:graph_store) :
    path g r ys r' ->
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
    iIntros (Hpath Φ) "(Hr'&HL&Hg) HΦ".
    iInduction ys as [|] "IH" forall (r xs r' Hpath t'); wp_rec.
    { inversion Hpath. subst. wp_load. simpl.
      iSteps. rewrite /lst_model //. }
    { inversion Hpath. subst.

      iDestruct (big_sepS_elem_of_acc _ _ (r,b,a2) with "[$]") as "(?&Hg)".
      { set_solver. } destruct b.
      wp_load.
      iSpecialize ("Hg" with "[$]").
      iDestruct (lst_model_Cons (ValLiteral (LiteralLoc r)) with "[$]") as "?".
      iSpecialize ("IH" with "[%//][$][$][$]").
      iStep 19. iModIntro. iStep 3. iApply "IH". iModIntro. iIntros (?) "(?&?&?)".
      iApply ("HΦ"). iFrame. }
  Qed.

 Lemma pstore_collect_spec (r r':loc) (ys:list (loc*(loc*val)*loc)) (g:graph_store) :
   path g r ys r' ->
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
    iIntros (? Φ) "(?&?) Hϕ".
    iDestruct lst_model_Nil as "?".
    iDestruct (pstore_collect_spec_aux with "[$]") as "Go". done.
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

  Lemma use_path r g (xs:list (loc*(loc*val)*loc)) r0 x r1 r':
    list_to_set xs ⊆ g ->
    path g r (xs ++ [(r0, x, r1)]) r' ->
    (r0, x, r1) ∈ (list_to_set xs : gset(loc*(loc*val)*loc) ) ->
    exists ds, path g r0 ds r0 /\ ds ≠ nil.
  Proof.
    revert r r0 r1 r' x. induction xs; intros r r0 r1 r' x ?.
    { set_solver. }
    rewrite -app_comm_cons. inversion 1. subst.
    rewrite list_to_set_cons.
    destruct_decide (decide ((r0, x, r1) = (r, b, a2))) as X.
    { inversion X. subst. intros _. clear IHxs.
      rewrite app_comm_cons in H0. apply path_snoc_inv in H0.
      destruct H0 as (?&?&?). subst a2.
      exists (((r, b, r') :: xs)). done. }
    { intros ?. apply IHxs in H6. 2,3:set_solver.
      destruct H6 as (?&?&?). eexists. split; last done.
      eapply path_weak. done. set_solver. }
  Qed.

  Lemma acyclic_weak `{Countable A} `{Countable B} (g1 g2:graph A B) :
    acyclic g1 ->
    g2 ⊆ g1 ->
    acyclic g2.
  Proof.
    intros Hacy ? ???. eapply Hacy. by eapply path_weak.
  Qed.

  Lemma pstore_revert_spec_aux g g1 r t g2 xs r' w σ σ0 :
    locs_of_edges_in g2 (dom σ) ->
    g2 = list_to_set xs ->
    acyclic g ->
    g2 ⊆ g ->
    path g r xs r' ->
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
    iIntros (Hlocs Hg Hacy Hsub Hpath Φ) "(HL&Hr'&Hσ&Hg1&Hg2) HΦ".
    iInduction xs as [|((r0,(l,v)),r1) ] "IH" using rev_ind forall (t σ w r r' g1 g2  Hpath Hg Hlocs Hacy Hsub).
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
      rewrite list_to_set_app_L in Hsub.
      assert ((r0, (l, v), r1) ∉ (list_to_set xs : gset (loc * diff * loc))).
      { intros ?. apply use_path in Hpath; last done. destruct Hpath as (?&Hpath&?).
        apply Hacy in Hpath. congruence. set_solver. }
      iDestruct (big_sepS_union with "Hg2") as "(Hg2&?)".
      { set_solver. }
      rewrite big_sepS_singleton. wp_load. iStep 19. iModIntro.

      rewrite list_to_set_app_L list_to_set_cons list_to_set_nil right_id_L in Hlocs.
      assert (exists v', σ !! l = Some v') as (v',Hl).
      { apply elem_of_dom. eapply Hlocs. rewrite /edge.

        rewrite elem_of_union elem_of_singleton. right. reflexivity. }

      apply path_snoc_inv in Hpath. destruct Hpath as (?&->&?).
      wp_smart_apply assert_spec. rewrite bool_decide_eq_true_2 //.
      iStep 4. iModIntro.

      iDestruct (big_sepM_insert_acc with "Hσ") as "(?&Hσ)". done.
      wp_load. wp_store. wp_store. iStep 4. iModIntro.

      iSpecialize ("Hσ" with "[$]").
      iSpecialize ("IH" with "[%//][%//][%][%//][%][$][$][$] Hg1 Hg2").
      { rewrite dom_insert_lookup_L //. intros x1 x2 x3 x4.
        specialize (Hlocs x1 x2 x3 x4). set_solver. }
      { set_solver. }

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
    path g r xs r' ->
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
    iApply (pstore_revert_spec_aux g ∅ with "[-HΦ]"); try done.
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
    path g r xs r' ->
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
    wp_rec. wp_apply (pstore_collect_spec with "[$]"). done.
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


  Lemma apply_diffl_included xs σ1 σ2 :
    σ1 ⊆ σ2 ->
    apply_diffl xs σ1 ⊆ apply_diffl xs σ2.
  Proof.
    revert σ1 σ2. induction xs as [|(?,?)]; intros;
      [ done | eauto using gmap_included_insert ].
  Qed.

  Lemma undo_same_fst_label xs ys σ r l v r' :
    undo xs ys σ ->
    (r, (l, v), r') ∈ (list_to_set ys :  gset (loc*(loc*val)*loc)) ->
    l ∈ (list_to_set (proj2 <$> xs).*1 : gset loc).
  Proof.
    revert xs σ. induction ys as [|(?,?)]. set_solver.
    intros xs σ. inversion 1. subst.
    simpl. rewrite !fmap_app list_to_set_app_L.
    destruct_decide (decide ((r, (l, v), r') = (r'0, (l1, v'), l0))) as Heq.
    { inversion Heq. subst. intros _. set_solver. }
    intros ?. simpl. apply elem_of_union. left. eapply IHys. done. set_solver.
  Qed.

  Lemma path_restrict  `{Countable A} `{Countable B} (g:graph A B) r xs r' :
    path g r xs r' ->
    path (list_to_set xs) r xs r'.
  Proof.
    induction 1.
    { apply path_nil. }
    { apply path_cons. set_solver.
      eapply path_weak. done. set_solver. }
  Qed.

  Lemma path_all_in `{Countable A} `{Countable B} (g:graph A B) a1 xs a2 :
    path g a1 xs a2 ->
    list_to_set xs ⊆ g.
  Proof.
    induction 1; simpl; set_solver.
  Qed.

  Lemma path_inv_r (g:gset (loc*(loc*val)*loc)) x bs z :
    path g x bs z ->
    (x = z /\ bs = nil) ∨ ∃ bs' b y, bs = bs' ++ [(y,b,z)] /\ path g x bs' y ∧ (y,b,z) ∈ g.
  Proof.
    induction 1.
    { naive_solver.  }
    right. destruct IHpath as [(->&->)|(bs'&b'&y&->&?&?)].
    { exists nil. eexists _,_. split; first done. split. eauto using path_nil. naive_solver. }
    { exists ((a1, b, a2) :: bs'). eexists _,_. rewrite app_comm_cons //. split_and !; try done.
      apply path_cons; eauto. }
  Qed.

  Definition diff_last {A:Type} (ys1 ys2:list A) :=
    match last ys1,last ys2 with Some x,Some y => x ≠ y | _,_ => True end.

  Lemma path_extract_suffix (g:gset (loc*(loc*val)*loc)) a1 a2 xs1 r xs2 :
    kindofinj g ->
    path g a1 xs1 r ->
    path g a2 xs2 r  ->
    exists ys1 ys2 xs,
      xs1 = ys1 ++ xs /\
      xs2 = ys2 ++ xs /\ diff_last ys1 ys2.
  Proof.
    intros Hinj.
    revert r a1 a2 xs2. induction xs1 using rev_ind; intros r a1 a2 xs2.
    { inversion 1. subst. intros. exists nil,xs2,nil.
      simpl. rewrite right_id_L. set_solver. }
    intros Hp1 Hp2. apply path_inv_r in Hp1.
    destruct Hp1 as [? | (bs'&b'&y&X1&X2&X3)].
    { destruct xs1; naive_solver. }
    apply app_inj_tail in X1. destruct X1 as (<-&->).

    apply path_inv_r in Hp2. destruct Hp2 as [(->&->) | (bs'&b&y'&->&?&?)].
    { exists (xs1 ++ [(y, b', r)]),nil,nil. rewrite right_id. split_and !; try done.
      unfold diff_last. destruct (last (xs1 ++ [(y, b', r)])); try done. }

    destruct_decide (decide (y'=y)); last first.
    { eexists _,_,nil. rewrite !right_id_L. split_and!; try done.
      unfold diff_last. rewrite !last_app. simpl. naive_solver. }
    subst.

    destruct (IHxs1 _ _ _ _ X2 H) as (ys1&ys2&xs&->&->&Hdiff).
    destruct (Hinj _ _ _ _ _ X3 H0) as (->&_).
    eexists _,_,(xs++[(y, b, r)]). rewrite !assoc_L. done.
  Qed.

  Lemma elem_of_middle {A:Type} (x:A) (xs:list A) :
    x ∈ xs ->
    exists (l1 l2:list A), xs = l1 ++ x::l2.
  Proof.
    intros Hx. apply elem_of_list_lookup_1 in Hx.
    destruct Hx as (?&?).
    eexists _,_. symmetry. eapply take_drop_middle. done.
  Qed.

  Lemma diff_last_app_middle {A:Type} x (l1' l2' l1 l2:list A) :
    diff_last (l1' ++ x :: l2') (l1 ++ x :: l2) ->
    diff_last (x :: l2') (x :: l2).
  Proof.
    unfold diff_last. rewrite !last_app !last_cons.
    destruct (last l2),(last l2'); eauto.
  Qed.

  Lemma list_case_r {A:Type} (l:list A) :
    l = nil \/ exists (l':list A) x, l = l' ++ [x].
  Proof.
    induction l using rev_ind.
    naive_solver. right.
    destruct IHl as [-> | (?&?&->)]; eauto.
  Qed.

  Lemma diff_last_irrefl {A:Type} (l:list A) :
    l ≠ nil ->
    ¬ (diff_last l l).
  Proof.
    destruct (list_case_r l) as [|(?&?&->)]. naive_solver.
    intros _. unfold diff_last.
    rewrite !last_app //. simpl. naive_solver.
  Qed.

  Lemma path_use_diff_last (g:gset (loc*(loc*val)*loc)) a1 a2 ys1 ys2 xs r :
    acyclic g ->
    kindofinj g ->
    path g a1 (ys1 ++ xs) r ->
    path g a2 (ys2 ++ xs) r  ->
    diff_last ys1 ys2 ->
    forall x, x ∈ ys2 -> x ∉ (ys1 ++ xs).
  Proof.
    intros Hacy Hroot Hp1 Hp2 Hdiff x Hx Hx'.
    apply elem_of_app in Hx'. destruct Hx' as [Hx'|Hx'].
    (* contradicts diff_last. *)
    { apply elem_of_middle in Hx,Hx'.
      destruct Hx as (l1&l2&->).
      destruct Hx' as (l1'&l2'&->).
      rewrite -!assoc_L in Hp1,Hp2.
      apply path_app_inv in Hp1,Hp2.
      destruct Hp1 as (x1&_&Hp1).
      destruct Hp2 as (x2&_&Hp2).
      rewrite -!app_comm_cons in Hp1,Hp2.
      assert (x1=proj1 x).
      { inversion Hp1. subst. done. }
      assert (x2=proj1 x).
      { inversion Hp2. subst. done. }
      subst.
      eapply use_kindofinj in Hp1; eauto.
      rewrite !app_comm_cons in Hp1.
      apply app_inv_tail in Hp1.
      apply diff_last_app_middle in Hdiff.
      rewrite Hp1 in Hdiff.
      eapply diff_last_irrefl; last done. done. }
    (* There is a loop. *)
    { apply elem_of_middle in Hx,Hx'.
      destruct Hx as (l1&l2&->).
      destruct Hx' as (l1'&l2'&->).
      rewrite -assoc_L in Hp2.
      apply path_app_inv in Hp2.
      destruct Hp2 as (?&_&Hp2).
      rewrite assoc_L  in Hp2.
      apply path_app_inv in Hp2.
      destruct Hp2 as (?&Hp2&Hp2').
      assert (x0 = proj1 x) as ->.
      { inversion Hp2. subst. done. }
      assert (x1 = proj1 x) as ->.
      { inversion Hp2'. subst. done. }
      rewrite -app_comm_cons in Hp2.
      eapply Hacy in Hp2. congruence. }
  Qed.

  Lemma path_middle (g:graph loc (loc*val)) x xs ys z :
    path g x (xs ++ ys) z ->
    exists y, path g x xs y /\ path g y ys z.
  Proof.
    revert g x ys z. induction xs; intros g x ys z.
    { simpl. eauto using path_nil. }
    inversion 1; simpl in *; subst.
    apply IHxs in H5. destruct H5 as (y,(?&?)).
    exists y. split; last done. eauto using path_cons.
  Qed.

  Definition undo_weak (xs ys:list (loc*(loc*val)*loc)) :=
    forall r x r', (r,x,r') ∈ xs -> exists x', (r',x',r) ∈ ys.

  Lemma path_app (g:graph loc (loc*val)) x3 x1 xs ys x2 :
    path g x1 xs x3 ->
    path g x3 ys x2 ->
    path g x1 (xs++ys) x2.
  Proof.
    intros Hp.
    revert x2 ys. induction Hp. eauto.
    intros. rewrite -app_comm_cons. apply path_cons. set_solver.
    eauto.
  Qed.

  Lemma use_undo ys2 us ys g r y :
    undo_weak (ys2 ++ us) ys ->
    path g r ys2 y ->
    exists zs, path (list_to_set ys) y zs r.
  Proof.
    intros Hundo Hpath.
    revert us ys Hundo. induction Hpath; intros us' ys Hundo.
    { exists nil. apply path_nil. }
    assert (exists b', (a2,b',a1) ∈ ys) as (b'&Hb').
    { eapply (Hundo _ b). set_solver. }
    assert (undo_weak (bs ++ us') ys) as Hundo'.
    { intros ????. eapply (Hundo _ x). set_solver. }
    apply IHHpath in Hundo'.
    destruct Hundo' as (π&?).
    exists (π ++ [(a2, b', a1)]). eapply path_app; first done.
    apply path_cons. 2:apply path_nil. set_solver.
  Qed.

  Lemma diff_last_comm {A:Type} (l1 l2:list A) :
    diff_last l1 l2 <-> diff_last l2 l1.
  Proof.
    unfold diff_last.
    destruct (last l1),(last l2); naive_solver.
  Qed.

  Lemma path_union_inv (g1: graph loc (loc*val)) g2 a1 xs a2 :
    path (g1 ∪ g2) a1 xs a2 ->
    path g1 a1 xs a2 \/ exists a' x xs1 xs2, path g1 a1 xs1 a' /\ x ∈ g2 /\ path (g1 ∪ g2) a' (x::xs2) a2 /\ xs=xs1++x::xs2.
  Proof.
    induction 1.
    left. eauto using path_nil.
    destruct IHpath as [|(x&?&?&?&?&?&?&->)].
    { destruct_decide (decide ((a1,b,a2) ∈ g1)).
      { left. apply path_cons; eauto. }
      { right. exists a1,(a1,b,a2),nil. eexists. split_and !. apply path_nil. set_solver.
        apply path_cons. set_solver. eauto. done. } }
    { right.
      destruct_decide (decide ((a1,b,a2) ∈ g1)).
      { eexists _,_,_,_. split_and !;eauto.
        2:{ rewrite app_comm_cons. reflexivity. }
        apply path_cons. set_solver. done. }
      eexists _,_,_,_. split_and !. apply path_nil.
      3:{ simpl. reflexivity. }
      set_solver. apply path_cons. set_solver. done. }
  Qed.

  Lemma use_undo_weak' xs ys g r y :
    undo_weak xs ys ->
    path g r xs y ->
    exists zs, path (list_to_set ys) y zs r /\ length xs = length zs.
  Proof.
    intros Hweak.
    induction 1.
    { exists nil. split. apply path_nil. done. }
    { destruct IHpath as (zs&Hzs&?).
      { intros ????. eapply Hweak. apply elem_of_cons. eauto. }
      destruct (Hweak a1 b a2) as (b'&Hb'). set_solver.
      exists (zs ++ [(a2, b', a1)]). split.
      { eapply path_app. done.
        apply path_cons. set_solver. apply path_nil. }
      { rewrite app_length. simpl. lia. } }
  Qed.

  Inductive undo0 :
    list (loc*(loc*val)*loc) -> list (loc*(loc*val)*loc) -> Prop :=
  | undo0_nil :
    undo0 [] []
  | undo0_cons :
    forall r x x' r' xs ys,
      undo0 xs ys  ->
      undo0 (xs++[(r,x,r')]) ((r',x',r)::ys).

  Lemma undo_undo0 xs ys σ :
    undo xs ys σ ->
    undo0 xs ys.
  Proof.
    induction 1; eauto using undo0_nil, undo0_cons.
  Qed.

  Lemma undo0_snoc ys xs a a' x x' :
    undo0 ys xs ->
    undo0 ((a,x,a') :: ys) (xs ++ [(a',x',a)]).
  Proof.
    induction 1.
    { apply (undo0_cons _ _ _ _ nil nil). apply undo0_nil. }
    rewrite -!app_comm_cons app_comm_cons. by apply undo0_cons.
  Qed.

  Lemma undo0_symm xs ys :
    undo0 xs ys -> undo0 ys xs.
  Proof.
    induction 1. eauto using undo0_nil.
    apply undo0_snoc. eauto.
  Qed.

  Lemma undo0_undo_weak xs ys :
    undo0 xs ys ->
    undo_weak xs ys.
  Proof.
    induction 1. intros ?. set_solver.
    intros ???. rewrite elem_of_app elem_of_list_singleton.
    intros [X|X].
    { apply IHundo0 in X. set_solver. }
    { set_solver. }
  Qed.

  Lemma use_undo' g r xs ys y :
    path g r xs y ->
    undo0 xs ys ->
    forall a b a', (a,b,a') ∈ ys -> a' = r \/ exists b' a'', (a',b',a'') ∈ ys.
  Proof.
    intros Hpath Hundo. generalize Hundo. intros Hundo'.
    apply undo0_symm in Hundo.
    apply undo0_undo_weak in Hundo.
    intros ??? Hys. apply Hundo in Hys. destruct Hys as (?&?).
    apply elem_of_middle in H. destruct H as (l1&l2&->).
    apply path_app_inv in Hpath. destruct Hpath as (r'&E1&E2).
    assert (r'=a') as ->.
    { inversion E2. subst. done. }
    apply path_inv_r in E1.
    destruct E1 as [|(?&?&?&->&Hpath&?)].
    naive_solver.
    apply undo0_undo_weak in Hundo'.
    destruct (Hundo' x2 x1 a'). set_solver. set_solver.
  Qed.

  Lemma path_cannot_escape (x:(loc * diff * loc)) (xs ys:list (loc * diff * loc)) (g1: graph loc (loc*val)) a a' r :
    (forall x l', ¬ (r,x,l') ∈ (g1 ∪ list_to_set ys)) ->
    kindofinj (g1 ∪ list_to_set ys) ->
    x ∈ (list_to_set ys : gset _) ->
    (forall a b a', (a,b,a') ∈ ys -> a' = r \/ exists b' a'', (a',b',a'') ∈ ys) ->
    path (g1 ∪ list_to_set ys) a (x :: xs) a' ->
    path (list_to_set ys) a (x::xs) a'.
  Proof.
    intros ? X1 X2 X3. remember (x::xs) as zs.
    revert a a' x xs Heqzs X1 X2 X3.
    induction zs; intros a0 a' x xs Heqzs X1 X2 X3. congruence.
    inversion 1. subst. inversion Heqzs. subst. apply path_cons. eauto.
    destruct xs as [|((?,?),?)].
    { inversion H6. subst. eauto using path_nil. }
    eapply IHzs; eauto. inversion H6. subst.
    apply elem_of_list_to_set in X2. apply X3 in X2.
    destruct X2 as [|(?&?&?)]. naive_solver.
    assert ((l, x, x0) ∈  g1 ∪ list_to_set ys) as Z. set_solver.
    destruct (X1 _ _ _ _ _ H9 Z). set_solver.
  Qed.

  Lemma path_in_seg_complete (r a a':loc) (x:(loc * diff * loc)) (xs0 xs1 ys: list (loc * diff * loc)) (g1:graph loc (loc*val)) :
    (forall x l', ¬ (r,x,l') ∈ (g1 ∪ list_to_set ys)) -> (* root has no succ *)
    kindofinj (g1 ∪ list_to_set ys) ->
    (forall a b a', (a,b,a') ∈ ys -> a' = r \/ exists b' a'', (a',b',a'') ∈ ys) -> (* ys is "closed "*)
    path (g1 ∪ list_to_set ys) a xs0 a' ->
    path (list_to_set ys) a' (x :: xs1) a ->
    exists zs, path (list_to_set ys) a zs a'.
  Proof.
    intros Hroot Hinj Hclosed Hp1 Hp2.
    inversion Hp1.
    { subst. exists nil. apply path_nil. }
    subst. eapply path_cannot_escape in Hp1; eauto.
    apply path_inv_r in Hp2.
    destruct Hp2 as [|(?&?&?&Heq&Hp2&Hys)].
    { exfalso. destruct xs1; naive_solver. }
    apply elem_of_list_to_set in Hys.
    apply Hclosed in Hys. destruct Hys as [->|(?&?&Hys)].
    { naive_solver. }
    assert ((a, x3, x4) ∈  g1 ∪ list_to_set ys) as Z. set_solver.
    destruct (Hinj _ _ _ _ _ H Z). set_solver.
  Qed.

  Lemma undo0_vertices xs ys :
    undo0 xs ys ->
    vertices (list_to_set ys) = vertices (list_to_set xs).
  Proof.
    revert xs. induction ys; intros xs; inversion 1; subst. done.
    simpl. rewrite list_to_set_app_L !vertices_union !vertices_singleton. simpl.
    erewrite IHys; last done. rewrite vertices_empty. set_solver.
  Qed.

  Lemma undo_preserves_rooted_dag g xs ys rs r :
    (forall x l', ¬ (rs,x,l') ∈ (list_to_set ys ∪ g ∖ list_to_set xs)) -> (* root has no succ *)
    kindofinj g ->
    kindofinj (list_to_set ys ∪ g ∖ list_to_set xs) ->
    path g rs xs r ->
    undo0 xs ys ->
    rooted_dag g r ->
    rooted_dag (list_to_set ys ∪ g ∖ list_to_set xs) rs.
  Proof.
    intros Hnr Hinj Hinj' Hpath Hundo Hroot. inversion Hroot as [X1 X2].
    assert (vertices (list_to_set ys ∪ g ∖ list_to_set xs) = vertices g) as Hvg.
    { apply undo0_vertices in Hundo.
      rewrite vertices_union Hundo -vertices_union -union_difference_L //.
      eauto using path_all_in. }

    constructor.
    { intros a. rewrite Hvg => Ha.
      apply X1 in Ha. destruct Ha as (zs&Ha).
      edestruct (path_extract_suffix g a rs) as (ys1&ys2&us&?&?&Hlast); eauto. subst.

      apply path_middle in Ha. destruct Ha as (y&Hy1&Hy2).
      apply path_middle in Hpath. destruct Hpath as (y'&Hy'1&Hy'2).
      assert (y'=y) as ->.
      { inversion Hy'2; subst; inversion Hy2; naive_solver. }
      edestruct use_undo as (zs&Hzs). eauto using undo0_undo_weak. done.
      exists (ys1++zs). eapply path_app.
      2:{ eapply path_weak. done. set_solver. }
      { clear X2. induction Hy1.
        { apply path_nil. }
        apply path_cons.
        { rewrite elem_of_union elem_of_difference. right. split. set_solver.
          apply not_elem_of_list_to_set.
          eapply path_use_diff_last. 1,2: eauto using ti2.
          3:{ apply diff_last_comm. done. }
          { eapply path_app; eauto. }
          { rewrite -app_comm_cons. eapply path_cons. done.
            eapply path_app; eauto. }
          { set_solver. } }
        { apply IHHy1; eauto.  unfold diff_last in *. rewrite last_cons in Hlast.
          destruct (last bs), (last ys2); try done. } } }
    { intros a zs Hzs. rewrite comm_L in Hzs.
      apply path_union_inv in Hzs. destruct Hzs as [Hsz|Hsz].
      (* The cycle is only in g, easy. *)
      { eapply X2. eapply path_weak. done. set_solver. }
      (* There is at least a vertex in ys.
         We are going to construct a cycle in ys, implying a cycle in xs. *)
      exfalso. destruct Hsz as (a'&x&l1&l2&E1&Hx&E2&->).

      apply path_cannot_escape with (r:=rs) in E2; last first.
      { eapply use_undo'; eauto using undo_undo0. }
      { done. }
      { rewrite comm_L //. }
      { set_solver. }

      eapply path_weak in E1.
      eapply path_in_seg_complete with (r:=rs) in E1; last first. done.
      { eapply use_undo'; eauto using undo_undo0. }
      { rewrite comm_L //. }
      { set_solver. }
      2:{ set_solver. }
      destruct E1 as (?&E1).

      assert (path (list_to_set ys) a (x0 ++ x::l2) a ) as Hcycle.
      { eapply path_app. done. done. }

      eapply use_undo_weak' with (ys:=xs) in Hcycle.
      2:{ apply undo0_symm in Hundo.
          apply undo0_undo_weak in Hundo. apply path_all_in in Hcycle.
          intros ????. eapply (Hundo _ x1); eauto. set_solver. }
      destruct Hcycle as (?&Hcycle&F).
      eapply path_weak in Hcycle. 2:eapply path_all_in; done.
      eapply ti2 in Hcycle; eauto. subst. destruct x0; simpl in *; lia. }
  Qed.

  Lemma undo_preserves_model g (M:map_model) (xs ys:list (loc* (loc*val)*loc)) (r1 r2:loc) ds σ1 σ2 rs σ0 r:
     dom M = vertices g ∪ {[r]} ->
    (forall r1 ds r2 σ1 σ2, reachable g r1 ds r2 -> M !! r1 = Some σ1 -> M !! r2 = Some σ2 -> σ1 ⊆ (apply_diffl ds σ2)) -> (* this is a part of _inv *)
    (forall x l', ¬ (rs,x,l') ∈ (list_to_set ys ∪ g ∖ list_to_set xs)) -> (* root has no succ *)
    kindofinj (g ∖ list_to_set xs ∪ list_to_set ys) ->
    path g rs xs r ->
    undo xs ys σ0 ->
    reachable (list_to_set ys ∪ g ∖ list_to_set xs) r1 ds r2 ->
    M !! r1 = Some σ1 →
    M !! r2 = Some σ2 →
    σ1 ⊆ apply_diffl ds σ2.
  Proof.
    intros Hdom Hinv Hroot Hinj' Hrs Hundo Hreach E1 E2. rewrite comm_L in Hreach.
    apply reachable_path in Hreach. destruct Hreach as (zs&Hpath&<-).
    apply path_union_inv in Hpath. destruct Hpath as [Hpath|Hpath].
    { eapply Hinv; eauto. eapply reachable_path2. eapply path_weak. done. set_solver. }

    destruct Hpath as (a'&x&l1&l2&X1&Hx&X2&Hzs).
    eapply path_cannot_escape with (r:=rs) in X2; eauto; last first.
    { eapply use_undo'; eauto using undo_undo0. }
    { set_solver. }

    assert (vertices (list_to_set ys ∪ g ∖ list_to_set xs) = vertices g) as Hvg.
    { apply undo_undo0, undo0_vertices in Hundo.
      rewrite vertices_union Hundo -vertices_union -union_difference_L //.
      eauto using path_all_in. }

    assert (a' ∈ dom M) as Ha'.
    { rewrite Hdom -Hvg elem_of_union. left. apply elem_of_vertices.
      inversion X2. set_solver. }
    apply elem_of_dom in Ha'. destruct Ha' as (σ',Ea').
    assert (σ1 ⊆ apply_diffl (proj2 <$> l1) σ').
    { apply reachable_path2 in X1.
      eapply reachable_weak in X1.
      eapply (Hinv _ _ _ _ _ X1 E1 Ea'). set_solver. }
    etrans. done. rewrite Hzs. rewrite fmap_app apply_diffl_app.
    apply apply_diffl_included. clear dependent σ1.
    Search apply_diffl.

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

    iDestruct (extract_kindofinj with "Hg") as "%".

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

    eapply ti1 in Hrs; eauto. destruct Hrs as (ds,Hrs).
    inversion Hrs. congruence. subst. rename a2 into r'. destruct b.
    iDestruct (big_sepS_elem_of_acc with "[$]") as "(?&Hg)". done. simpl.
    wp_load. iStep 19. iModIntro.
    iSpecialize ("Hg" with "[$]").

    remember ((rs, (l, v), r') :: bs) as xs.
    assert (list_to_set xs ⊆ g).
    { eauto using path_all_in. }

    rewrite (union_difference_L (list_to_set xs) g) //.

    iDestruct (big_sepS_union with "Hg") as "(Hxs&Hg)". set_solver.
    wp_apply (pstore_reroot_spec with "[Hr Hxs Hσ0]").
    4:{ eapply path_restrict. done. }
    2:done.
    { destruct Hcoh as [_ X]. eapply locs_of_edges_weak; eauto. }
    { eapply acyclic_weak; eauto using ti2. }
    { iFrame. }

    iIntros "[%ys (%Hundo&?&?&?)]".
    iStep 8. do 2 iModIntro.
    iApply "HΦ".
    iDestruct (big_sepS_union_2 with "[$][$]") as "Hs".

    remember ((rs, (l, v), r') :: bs) as xs.

    iDestruct (extract_kindofinj with "Hs") as "%".

    assert (({[(rs, (l, v), r')]} ∪ list_to_set bs) = (list_to_set xs : gset _)) as Hbs.
    { subst xs. reflexivity. }
    rewrite Hbs. rewrite Hbs in H5.

    iAssert ⌜forall x y, (rs,x,y) ∉ (list_to_set ys ∪ g ∖ list_to_set xs)⌝%I as "%".
    { iIntros (???). destruct a. iDestruct (big_sepS_elem_of with "Hs") as "?". done.
      iClear "H17".
      iDestruct (mapsto_ne with "[$][$]") as "%". congruence. }

    iExists _,_,_,σ1,_,M,_. iFrame.

    assert (vertices (list_to_set ys ∪ g ∖ list_to_set xs) = vertices g) as Hvg.
    { apply undo_undo0, undo0_vertices in Hundo.
      rewrite vertices_union Hundo -vertices_union -union_difference_L //. }

    assert (σ1 ⊆ apply_diffl (proj2 <$> xs) σ0).
    { destruct Hinv as [X1 X2 X3 X4].
      apply reachable_path2 in Hrs.
      eapply X4 in Hrs. 2,3:done. etrans. apply Hrs.
      destruct Hcoh. eauto using apply_diffl_included. }

    assert (rooted_dag (list_to_set ys ∪ g ∖ list_to_set xs) rs) as Hroot.
    { eapply undo_preserves_rooted_dag; eauto using undo_undo0. }

    iPureIntro. split_and !; try done.
    { destruct Hinv as [X1 X2 X3 X4]. constructor.
      { rewrite X1 Hvg.
        apply elem_of_dom_2 in X3,HMrs.
        apply reachable_path2,reachable_inv_in_invertices in Hrs.
        set_solver. }
      { by etrans. }
      { done. }
      { intros. eapply undo_preserves_model; eauto. rewrite comm_L //. } }
    { destruct Hcoh as [X1 X2]. constructor.
      { subst xs. simpl in *. done. }
      { replace (<[l:=v]> (foldr (λ '(l0, v0) σ2, <[l0:=v0]> σ2) σ0 (proj2 <$> bs))) with (apply_diffl (proj2 <$> xs) σ0).
        2:{ subst xs. reflexivity. }
        rewrite dom_apply_diffl. intros ???? Hedge.
        rewrite /edge elem_of_union in Hedge. rewrite elem_of_union.
        destruct Hedge as [Hedge|Hedge].
        { right. eauto using undo_same_fst_label. }
        { left. eapply (X2 r0). eapply elem_of_subseteq. 2:done. set_solver. } } }
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
