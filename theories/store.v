(* Based on:
   https://gitlab.com/basile.clement/store/-/blob/main/src/store.ml?ref_type=heads
*)

From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  lib.mono_set.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  assert
  lst.
From zebre Require Import
  options.

Implicit Types l : loc.
Implicit Types v t s : val.
Implicit Types σ : gmap loc val.

#[local] Notation "'snap_store'" := (
  in_type "snap" 0
)(in custom zebre_proj
).
#[local] Notation "'snap_root'" := (
  in_type "snap" 1
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

(* ------------------------------------------------------------------------ *)
(* Code. *)

Definition store_create : val :=
  λ: <>,
    ref (ref §Root).

Definition store_ref : val :=
  λ: "v",
    ref "v".

Definition store_get : val :=
  λ: "t" "r",
    !"r".

Definition store_set : val :=
  λ: "t" "r" "v",
    let: "root" := ref §Root in
    !"t" <- ‘Diff{ "r", !"r", "root" } ;;
    "r" <- "v" ;;
    "t" <- "root".

Definition store_capture : val :=
  λ: "t",
    ("t", !"t").

Definition store_collect : val :=
  rec: "store_collect" "node" "acc" :=
    match: !"node" with
    | Root =>
        ("node", "acc")
    | Diff <> <> "node'" =>
        "store_collect" "node'" ‘Cons{ "node", "acc" }
    end.
Definition store_revert : val :=
  rec: "store_revert" "node" "seg" :=
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
            "store_revert" "node'" "seg"
        end
    end.
Definition store_reroot : val :=
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
      | Diff <> <> <> =>
          store_reroot "root" ;;
          "t" <- "root"
      end
    ).

(* ------------------------------------------------------------------------ *)
(* Lemmas on maps and lists. *)

Section map.
  Context `{Countable K}.
  Context {V : Type}.

  Lemma gmap_included_insert (σ1 σ2:gmap K V) (l:K) (v:V) :
    σ1 ⊆ σ2 ->
    <[l:=v]>σ1 ⊆ <[l:=v]>σ2.
  Proof.
    intros ? l'. destruct_decide (decide (l=l')).
    { subst. rewrite !lookup_insert //. }
    { rewrite !lookup_insert_ne //. }
  Qed.

  Lemma gmap_included_insert_notin (σ1 σ2:gmap K V) (l:K) (v:V) :
    l ∉ dom σ1 ->
    σ1 ⊆ σ2 ->
    σ1 ⊆ <[l:=v]>σ2.
  Proof.
    intros ?? l'. destruct_decide (decide (l=l')).
    { subst. rewrite lookup_insert // not_elem_of_dom_1 //. }
    { rewrite !lookup_insert_ne //. }
  Qed.

  Lemma incl_dom_incl (σ1 σ2:gmap K V)  :
    σ1 ⊆ σ2 ->
    dom σ1 ⊆ dom σ2.
  Proof.
    intros X1.
    intros l Hl. apply elem_of_dom in Hl. destruct Hl as (?&Hl).
    eapply map_subseteq_spec in X1; last done. by eapply elem_of_dom.
  Qed.
End map.

Section list.
  Context {A : Type}.

  Lemma list_case_r (l:list A) :
    l = nil \/ exists (l':list A) x, l = l' ++ [x].
  Proof.
    induction l using rev_ind.
    naive_solver. right.
    destruct IHl as [-> | (?&?&->)]; eauto.
  Qed.

  Lemma elem_of_middle (x:A) (xs:list A) :
    x ∈ xs ->
    exists (l1 l2:list A), xs = l1 ++ x::l2.
  Proof.
    intros Hx. apply elem_of_list_lookup_1 in Hx.
    destruct Hx as (?&?).
    eexists _,_. symmetry. eapply take_drop_middle. done.
  Qed.
End list.

(* ------------------------------------------------------------------------ *)
(* Define a labeled graph as a set of edges. *)

Section graph.
  Definition graph (A B : Type) `{Countable A} `{Countable B} :=
    gset (A * B * A).

  Context `{Countable A} `{Countable B}.
  Definition vertices (g:graph A B) : gset A :=
    set_fold (fun '(x,_,y) acc => {[x;y]} ∪ acc) ∅ g.

  Lemma vertices_empty :
    vertices ∅ = ∅.
  Proof.
    compute_done.
  Qed.

  Definition proj1 {A B C:Type} (x:(A*B*C)) : A :=
    match x with (x,_,_) => x end.
  Definition proj2 {A B C:Type} (x:(A*B*C)) : B :=
    match x with (_,x,_) => x end.
  Definition proj3 {A B C:Type} (x:(A*B*C)) : C :=
    match x with (_,_,x) => x end.

  Lemma elem_of_vertices x (g:graph A B) :
    x ∈ vertices g <-> exists b y, ((x,b,y) ∈ g \/ (y,b,x) ∈ g).
  Proof.
    apply set_fold_ind_L with (P := fun f g => x ∈ f  <-> exists b y, ((x,b,y) ∈ g \/ (y,b,x) ∈ g)).
    set_solver.
    intros ((?,?),?). set_solver.
  Qed.

  Lemma vertices_singleton (x:(A*B*A)) :
    vertices {[x]} = {[proj1 x; proj3 x]}.
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
      assert ({[proj1 x; proj3 x]} ⊆ vertices g2); last by set_solver.
      intros l Hl. apply elem_of_vertices.
      rewrite elem_of_union !elem_of_singleton in Hl. destruct x as ((?,?),?). set_solver. }
    rewrite {1}/vertices /set_fold. simpl.
    rewrite (foldr_permutation _ _ _ _ (x::elements g2)).
    { intros. destruct a1 as ((?,?),?),a2 as ((?,?),?); set_solver. }
    { by apply elements_union_singleton. }
    { simpl. rewrite vertices_singleton. destruct x as ((?,?),?). set_solver. }
  Qed.

  Definition edge (g:graph A B) x c y :=
    (x,c,y) ∈ g.

  Inductive path (g:graph A B) : A -> list (A*B*A) -> A -> Prop :=
  | path_nil : forall a, path g a [] a
  | path_cons : forall a1 b a2 bs a3,
      (a1,b,a2) ∈ g ->
      path g a2 bs a3 ->
      path g a1 ((a1,b,a2)::bs) a3.

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

  Definition unaliased (g:graph A B) :=
      forall r x1 r1 x2 r2,
      (r,x1,r1) ∈ g ->
      (r,x2,r2) ∈ g ->
      x1 = x2 /\ r1 = r2.

  Lemma path_app (g:graph A B) x3 x1 xs ys x2 :
    path g x1 xs x3 ->
    path g x3 ys x2 ->
    path g x1 (xs++ys) x2.
  Proof.
    intros Hp.
    revert x2 ys. induction Hp. eauto.
    intros. rewrite -app_comm_cons. apply path_cons. set_solver.
    eauto.
  Qed.

  Definition all_uniq_path g :=
    forall a1 a2 xs ys, path g a1 xs a2 -> path g a1 ys a2 -> xs = ys.

  Lemma rooted_tree_impl_acyclic_unaliased g r :
    (forall a, a ∈ vertices g -> exists xs, path g a xs r) -> (* If every vertex can reach the root, *)
    all_uniq_path g -> (* then the property of uniq path *)
    acyclic g /\ unaliased g. (* implies acyclicity + unalising *)
  Proof.
    intros Hroot  Huniq. split.
    { intros ?? Hpath.
      assert (path g a (xs++xs) a) as Hloop.
      { by eapply path_app. }
      specialize (Huniq a a xs (xs++xs) Hpath Hloop).
      apply (@f_equal _ _ length) in Huniq. rewrite app_length in Huniq.
      assert (length xs = 0) by lia. destruct xs; simpl in *; try done; lia. }
    { intros ????? X1 X2.
      destruct (Hroot r1) as (xs1&Hxs1).
      { eapply elem_of_vertices. eauto. }
      destruct (Hroot r2) as (xs2&Hxs2).
      { eapply elem_of_vertices. eauto. }
      assert (path g r0 ((r0,x1,r1)::xs1) r) as Hp1. by eapply path_cons.
      assert (path g r0 ((r0,x2,r2)::xs2) r) as Hp2. by eapply path_cons.
      specialize (Huniq _ _ _ _ Hp1 Hp2). naive_solver. }
  Qed.

  Lemma acyclic_unaliased_impl_uniq_path g :
    acyclic g ->
    unaliased g ->
    all_uniq_path g.
  Proof.
    intros Hacy Hinj. intros ???? Hpath.
    revert ys. induction Hpath; intros ys.
    { intros Hpath. apply Hacy in Hpath. done. }
    { inversion 1; subst.
      { exfalso.
        assert (path g a3 ((a3, b, a2)::bs) a3) as Z.
        { apply path_cons. done. eauto. }
        apply Hacy in Z. congruence. }
      destruct (Hinj _ _ _ _ _ H1 H3). subst.
      f_equal. eapply IHHpath. done. }
  Qed.

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

  Lemma path_snoc g a1 b a2 bs a3 :
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
        eapply path_snoc.
        { eapply path_weak; eauto. set_solver. }
        { set_solver. } } }
    { intros ?? Hpath. apply  path_cycle_end_inv in Hpath; eauto. }
  Qed.

  Lemma acyclic_weak (g1 g2:graph A B) :
    acyclic g1 ->
    g2 ⊆ g1 ->
    acyclic g2.
  Proof.
    intros Hacy ? ???. eapply Hacy. by eapply path_weak.
  Qed.

  Lemma path_all_in (g:graph A B) a1 xs a2 :
    path g a1 xs a2 ->
    list_to_set xs ⊆ g.
  Proof.
    induction 1; simpl; set_solver.
  Qed.

  Lemma path_restrict (g:graph A B) r xs r' :
    path g r xs r' ->
    path (list_to_set xs) r xs r'.
  Proof.
    induction 1; eauto using path_nil.
    apply path_cons. set_solver.
    eapply path_weak. done. set_solver.
  Qed.

  Lemma path_inv_r (g:graph A B) x bs z :
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

  Lemma path_add_inv_r (r r':A) b x xs g :
    r ≠ r' ->
    r' ∉ vertices g ->
    path ({[(r, b, r')]} ∪ g) x xs r' ->
    (xs = nil /\ x = r') \/ (exists xs', xs = xs' ++ [(r, b, r')] /\ path g x xs' r).
  Proof.
    intros Hrr' Hr' Hreach. apply path_inv_r in Hreach.
    destruct Hreach as [(->&->)|(bs'&b0&y&->&Hreach&Hedge)].
    { eauto. }
    right.
    assert (b0=b /\ y=r) as (->&->).
    { rewrite /edge elem_of_union elem_of_singleton in Hedge.
      destruct Hedge. naive_solver. exfalso. apply Hr', elem_of_vertices. eauto. }
    eexists. split; first done.
    eauto using path_cycle_end_inv_aux.
  Qed.

  (* [mirror xs ys] asserts that, up-to labels, the path xs is the reverse of ys *)
  Inductive mirror :
    list (A*B*A) -> list (A*B*A) -> Prop :=
  | mirror_nil :
    mirror [] []
  | mirror_cons :
    forall r x x' r' xs ys,
      mirror xs ys  ->
      mirror (xs++[(r,x,r')]) ((r',x',r)::ys).

  Lemma mirror_snoc ys xs a a' x x' :
    mirror ys xs ->
    mirror ((a,x,a') :: ys) (xs ++ [(a',x',a)]).
  Proof.
    induction 1.
    { apply (mirror_cons _ _ _ _ nil nil). apply mirror_nil. }
    rewrite -!app_comm_cons app_comm_cons. by apply mirror_cons.
  Qed.

  Lemma mirror_symm xs ys :
    mirror xs ys -> mirror ys xs.
  Proof.
    induction 1. eauto using mirror_nil.
    apply mirror_snoc; eauto.
  Qed.

  Lemma use_mirror xs ys (g:graph A B) r y :
    mirror xs ys ->
    path g r xs y ->
    path (list_to_set ys) y ys r.
  Proof.
    intros Hu. revert r y. induction Hu; intros r0 y.
    { inversion 1. subst. apply path_nil. }
    intros Hp. apply path_snoc_inv in Hp. destruct Hp as (?&?&?). subst.
    apply path_cons. set_solver. eapply path_weak. apply IHHu; eauto. set_solver.
  Qed.

  Lemma mirror_vertices (xs ys:list (A*B*A)) :
    mirror xs ys ->
    vertices (list_to_set ys) = vertices (list_to_set xs).
  Proof.
    revert xs. induction ys; intros xs; inversion 1; subst. done.
    simpl. rewrite list_to_set_app_L !vertices_union !vertices_singleton. simpl.
    erewrite IHys; last done. rewrite vertices_empty. set_solver.
  Qed.

  Lemma mirror_same_length (xs ys:list (A*B*A)):
    mirror xs ys ->
    length xs = length ys.
  Proof. induction 1. done. rewrite app_length. simpl. lia. Qed.

  Lemma mirror_mirrored_edges xs ys r x r' :
    mirror xs ys ->
    (r,x,r') ∈ xs -> exists x', (r',x',r) ∈ ys.
  Proof.
    induction 1. intros ?. set_solver.
    rewrite elem_of_app elem_of_list_singleton.
    intros [X|X].
    { apply IHmirror in X. set_solver. }
    { set_solver. }
  Qed.

  Lemma path_middle (g:graph A B) x xs ys z :
    path g x (xs ++ ys) z ->
    exists y, path g x xs y /\ path g y ys z.
  Proof.
    revert g x ys z. induction xs; intros g x ys z.
    { simpl. eauto using path_nil. }
    inversion 1; simpl in *; subst.
    apply IHxs in H7. destruct H7 as (y,(?&?)).
    exists y. split; last done. eauto using path_cons.
  Qed.

  Lemma use_mirror_subset xs ys xs' g r y :
    xs' ⊆ xs ->
    mirror xs ys ->
    path g r xs' y ->
    exists zs, path (list_to_set ys) y zs r /\ length xs' = length zs.
  Proof.
    intros Hincl Hundo Hpath.
    induction Hpath.
    { exists nil. split. apply path_nil. done. }
    { destruct IHHpath as (zs&Hzs&?).
      { set_solver. }
      eapply (mirror_mirrored_edges _ _ a1 b a2) in Hundo. 2:set_solver.
      destruct Hundo as (b'&?).
      exists (zs ++ [(a2, b', a1)]). split.
      { eapply path_app. done.
        apply path_cons.  set_solver. apply path_nil. }
      { rewrite app_length. simpl. lia. } }
  Qed.

  Definition pathlike (ys:list (A*B*A)) r :=
    forall a b a', (a,b,a') ∈ ys -> a' = r \/ exists b' a'', (a',b',a'') ∈ ys.

  Lemma path_pathlike g r ys y :
    path g y ys r ->
    pathlike ys r.
  Proof.
    intros Hpath a b a' Hedge.
    apply elem_of_middle in Hedge. destruct Hedge as (?&?&->).
    rewrite cons_middle assoc_L in Hpath.
    apply path_app_inv in Hpath. destruct Hpath as (?&Hpath&Hp').
    apply path_snoc_inv in Hpath. destruct Hpath as (?&?&?). subst.
    inversion Hp'; set_solver.
  Qed.

  Lemma same_path g (xs:list (A*B*A)) a1 a2 a3 a4 :
    path g a1 xs a2 ->
    path g a3 xs a4 ->
    xs ≠ nil ->
    a1 = a3 /\ a2=a4.
  Proof.
    intros Hp1. revert a3 a4. induction Hp1.
    { intros. congruence. }
    intros a3' a4'. inversion 1. subst. intros _. destruct bs.
    { inversion Hp1; inversion H10. subst. done. }
    apply IHHp1 in H10. 2:done. naive_solver.
  Qed.

  Lemma path_ends_vertices g x1 xs x2 :
    path g x1 xs x2 ->
    (x1 = x2) \/ (x1 ∈ vertices g /\ x2 ∈ vertices g).
  Proof.
     inversion 1. eauto. subst. right.
     split. apply elem_of_vertices. eauto.
     apply path_inv_r in H3. destruct H3 as [(->&->)|(?&?&?&->&?&?)].
     all:apply elem_of_vertices; eauto.
  Qed.
End graph.

(* ------------------------------------------------------------------------ *)
(* Define apply_diffl, a function applying a list of diff. *)

Section adiffl.
  Notation diff := (
    (* loc and its old value *)
    loc*val
  )%type.

  Definition apply_diffl (ds:list diff) (σ:gmap loc val) : gmap loc val :=
    foldr (fun '(l,v) σ => <[l:=v]> σ) σ ds.

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
  Proof.
    rewrite /apply_diffl foldr_app //.
  Qed.

  Lemma apply_diffl_snoc xs l v σ :
    apply_diffl (xs ++ [(l,v)]) σ = apply_diffl xs (<[l:=v]> σ).
  Proof.
    rewrite apply_diffl_app //.
  Qed.

  Lemma apply_diffl_cons l v xs σ :
    apply_diffl ((l,v)::xs) σ = <[l:=v]> (apply_diffl xs σ).
  Proof.
    done.
  Qed.

  Lemma apply_diffl_included xs σ1 σ2 :
    σ1 ⊆ σ2 ->
    apply_diffl xs σ1 ⊆ apply_diffl xs σ2.
  Proof.
    revert σ1 σ2. induction xs as [|(?,?)]; intros;
      [ done | eauto using gmap_included_insert ].
  Qed.
End adiffl.

(* ------------------------------------------------------------------------ *)
(* Proof. *)

Class PstoreG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] store_G_set_G :: MonoSetG Σ (loc * gmap loc val)%type ;
}.

Definition store_Σ := #[
  mono_set_Σ (loc * gmap loc val)%type
].
#[global] Instance subG_store_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG store_Σ Σ →
  PstoreG Σ.
Proof.
  solve_inG.
Qed.

Section store_G.
  Context `{store_G : PstoreG Σ}.

  Notation diff := (
    (* loc and its old value. *)
    loc*val
  )%type.
  Notation graph_store := (
    graph loc diff
  ).
  Notation map_model := (
    gmap loc (gmap loc val)
  ).

  Definition correct_path_diff (M:map_model) (g:graph_store) :=
    forall r1 ds r2 σ1 σ2,
      path g r1 ds r2 -> M !! r1 = Some σ1 -> M !! r2 = Some σ2 ->
      σ1 = (apply_diffl (proj2 <$> ds) σ2).

  Record store_inv (M:map_model) (g:graph_store) (r:loc) (σ σ0:gmap loc val) :=
    { si1 : dom M = vertices g ∪ {[r]};
      si2 : σ ⊆ σ0;
      si3 : M !! r = Some σ0 ;
      si4 : correct_path_diff M g
    }.

  Definition locs_of_edges_in g (X:gset loc) :=
    forall (r:loc) l v r', edge g r (l,v) r' -> l ∈ X.

  Record coherent (M:map_model) (σ0:gmap loc val) (g:graph_store) :=
    { coh1 : forall r σ, M !! r = Some σ -> dom σ = dom σ0;
      coh2 : locs_of_edges_in g (dom σ0);
    }.

  Definition snap_inv (M:map_model) (C:gset (loc * gmap loc val)) :=
    forall l σ, (l,σ) ∈ C -> exists σ', M !! l = Some σ' /\ σ ⊆ σ'.

  #[local] Definition store_map_auth (γ:gname) (s:gset (loc*(gmap loc val))) :=
    mono_set_auth γ s.
  #[local] Definition store_map_elem γ l σ :=
    mono_set_elem γ (l,σ).

  Lemma extract_unaliased (g : graph_store) :
    ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : loc), v, #(r' : loc) }) -∗
    ⌜unaliased g⌝.
  Proof.
    iIntros "Hg" (???????).
    destruct_decide (decide (a0 = a2 ∧ a1 = a3)). done.
    rewrite (big_sepS_delete _ _ (a, a0, a1)). set_solver.
    rewrite (big_sepS_delete _ _ (a, a2, a3)). set_solver.
    iDestruct "Hg" as "(?&?&_)". destruct a0,a2.
    iDestruct (pointsto_ne with "[$][$]") as "%". congruence.
  Qed.

  (* NB our invariant asserts that g is indeed a rooted tree: a rooted DAG
     with unicity of paths. Indeed, from the set of pointsto we can extract [unaliased],
     (see [extract_unaliased]), and a DAG with unaliased guarantees unicity of paths
     (see [acyclic_unaliased_impl_uniq_path] ) *)

  #[local] Definition snapshosts_model (t0:loc) (M:map_model) : iProp Σ :=
    ∃ (γ:gname) (C:gset (loc * gmap loc val)), (* the model of snapshots *)
      ⌜snap_inv M C⌝ ∗ meta t0 nroot γ ∗ store_map_auth γ C.

  #[local] Definition store (t:val) (σ:gmap loc val) : iProp Σ :=
    ∃ (t0 r:loc)
      (σ0:gmap loc val) (* the global map, with all the points-to ever allocated *)
      (g:graph_store) (* the global graph *)
      (M:map_model), (* the map model, associating to each node its model *)
    ⌜t=#t0 /\ store_inv M g r σ σ0 /\ coherent M σ0 g /\ rooted_dag g r⌝ ∗
    t0 ↦ #r ∗
    r ↦ §Root ∗
    snapshosts_model t0 M ∗
    ([∗ map] l ↦ v ∈ σ0, l ↦ v) ∗
    ([∗ set] x ∈ g, let '(r,(l,v),r') := x in r ↦ ’Diff{ #(l : loc), v, #(r' : loc) }) .

  Definition open_inv : string :=
    "[%t0 [%r [%σ0 [%g [%M ((->&%Hinv&%Hcoh&%Hgraph)&Ht0&Hr&HC&Hσ0&Hg)]]]]]".

  Definition snapshot t s σ : iProp Σ :=
    ∃ γ (t0:loc) l, ⌜t=#t0 /\ s=ValTuple [t;#l]⌝ ∗ meta t0 nroot γ ∗ store_map_elem γ l σ.

  #[global] Instance snapshot_timeless t s σ :
    Timeless (snapshot t s σ).
  Proof.
    apply _.
  Qed.
  #[global] Instance snapshot_persistent t s σ :
    Persistent (snapshot t s σ).
  Proof.
    apply _.
  Qed.

  Lemma store_create_spec :
    {{{ True }}}
      store_create ()
    {{{ t,
      RET t;
        store t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_alloc r as "Hroot".
    wp_alloc t0 as "Hmeta" "Ht0".
    iMod (mono_set_alloc ∅) as "[%γ ?]".
    iMod (meta_set _ _ _ nroot with "Hmeta") as "Hmeta". set_solver.
    iApply "HΦ". iModIntro.
    iExists t0,r,∅,∅,{[r := ∅]}. iFrame.
    rewrite !big_sepM_empty big_sepS_empty !right_id.
    iSplitR.
    2:{ iExists γ,∅. iFrame. iPureIntro. intros ??. set_solver. }
    iPureIntro. split_and!; first done.
    { constructor.
      { rewrite dom_singleton_L vertices_empty //. set_solver. }
      { set_solver. }
      { rewrite lookup_insert //. }
      { intros ????? Hr.
        rewrite !lookup_singleton_Some.
        inversion Hr; set_solver. } }
    { constructor.
      { intros ??. rewrite lookup_singleton_Some. intros (->&->). reflexivity. }
      { intros ????. set_solver. } }
    { eauto using rooted_dag_empty. }
  Qed.

  Lemma use_locs_of_edges_in g r xs r' X :
    locs_of_edges_in g X ->
    path g r xs r' ->
    (list_to_set (proj2 <$> xs).*1) ⊆ X.
  Proof.
    intros He.
    induction 1. set_solver.
    apply He in H. set_solver.
  Qed.

  Lemma store_ref_spec t σ v :
    {{{
      store t σ
    }}}
      store_ref v
    {{{ l,
      RET #l;
      ⌜l ∉ dom σ⌝ ∗
      store t (<[l := v]> σ)
    }}}.
  Proof.
    iIntros (ϕ) open_inv. iIntros "HΦ".

    wp_rec. wp_alloc l as "Hl".
    iApply "HΦ".

    iAssert ⌜σ0 !! l = None⌝%I as %Hl0.
    { rewrite -not_elem_of_dom. iIntros (Hl).
      apply elem_of_dom in Hl. destruct Hl.
      iDestruct (big_sepM_lookup with "Hσ0") as "Hl_"; first done.
      iDestruct (pointsto_ne with "Hl Hl_") as %?. done. }
    assert (σ !! l = None).
    { eapply not_elem_of_dom. apply not_elem_of_dom in Hl0.  destruct Hinv as [_ X].
      apply incl_dom_incl in X. set_solver. }
    iDestruct (pointsto_ne with "Hl Hr") as %Hlr.

    iModIntro. iSplitR. iPureIntro. by eapply not_elem_of_dom.
    iExists t0,r, (<[l:=v]>σ0),g,((fun σ => <[l:=v]>σ)<$> M).

    rewrite big_sepM_insert //. iFrame "∗".
    iSplitR "HC".
    iPureIntro. split_and !; eauto.
    { destruct Hinv as [X1 X2 X3 X4].
      constructor.
      { rewrite dom_fmap_L; set_solver. }
      { eauto using gmap_included_insert. }
      { rewrite lookup_fmap X3 //. }
      { intros r1 ds r2 σ1 σ2 Hr. rewrite !lookup_fmap. generalize Hr. intros Hreach.
        intros Hr1 Hr2.
        destruct (M !! r1) eqn:Hor1. 2:simpl in *; congruence.
        inversion Hr1. subst.
        destruct (M !! r2) eqn:Hor2. 2:simpl in *; congruence.
        inversion Hr2. subst.
        destruct Hcoh as [Z1 Z2].
        eapply use_locs_of_edges_in in Z2. 2:done.
        rewrite apply_diffl_insert_ne.
        { apply not_elem_of_dom in Hl0. set_solver. }
        { f_equal. eauto. } } }
    { destruct Hcoh as [X1 X2].
      constructor.
      { intros r' ?. rewrite lookup_fmap. intros E.
        destruct (M !! r') eqn:Hor. 2:simpl in *; congruence.
        inversion E. subst. rewrite !dom_insert_L. set_solver. }
      { intros. rewrite dom_insert_L. intros ??. set_solver. } }
    { iDestruct "HC" as "[% [% (%Hsnap&?&?)]]".
      iExists _,_. iFrame. iPureIntro.
      intros r' ? HC. apply Hsnap in HC. destruct HC as (x&Hx&?).
      exists (<[l:=v]>x). rewrite lookup_fmap Hx. split. done.
      apply gmap_included_insert_notin; last done.
      apply incl_dom_incl in H0. intros X. apply H0 in X.
      destruct Hcoh as [X1 X2]. apply X1 in Hx.
      apply not_elem_of_dom in Hl0. set_solver. }
  Qed.

  Lemma store_get_spec {t σ l} v :
    σ !! l = Some v →
    {{{
      store t σ
    }}}
      store_get t #l
    {{{
      RET v;
      store t σ
    }}}.
  Proof.
    iIntros (Hl ϕ) open_inv. iIntros "HΦ".
    wp_rec. iStep 4. iModIntro.

    iDestruct (big_sepM_lookup_acc _ _ l v with "[$]") as "(?&Hσ0)".
    { destruct Hinv as [_ Hincl _ _].
      specialize (Hincl l). rewrite Hl in Hincl. destruct (σ0!!l); naive_solver. }

    iStep 8. iFrame. iSteps.
  Qed.

  Lemma store_set_spec t σ l v :
    l ∈ dom σ →
    {{{
      store t σ
    }}}
      store_set t #l v
    {{{
      RET ();
      store t (<[l := v]> σ)
    }}}.
  Proof.
    iIntros (Hl Φ) open_inv. iIntros "HΦ".
    wp_rec. iStep 8. iModIntro.
    wp_alloc r' as "Hr'".

    assert (exists w, σ0 !! l = Some w) as (w&Hl0).
    { apply elem_of_dom. destruct Hinv as [_ Hincl].
      apply incl_dom_incl in Hincl.
      set_solver. }

    iDestruct (big_sepM_insert_acc with "Hσ0") as "(?&Hσ0)". done.
    wp_load. wp_load. wp_store. iStep 4. iModIntro.
    wp_store. wp_store. iApply "HΦ".

    iSpecialize ("Hσ0" with "[$]").

    iAssert ⌜r ≠ r'⌝%I as %?.
    { iClear "Ht0". iDestruct (pointsto_ne with "[$][$]") as %?. done. }

    iAssert ⌜r' ∉ vertices g⌝%I as %Hr'.
    { iIntros (Hr'). destruct Hgraph as [X1 X2].
      apply X1 in Hr'. destruct Hr' as (?&Hr'). inversion Hr'; subst.
      { done. }
      { destruct b. iDestruct (big_sepS_elem_of with "[$]") as "?". done.
        iDestruct (pointsto_ne r' r' with "[$][$]") as %?. congruence. } }

    iModIntro. iExists t0,r',(<[l:=v]> σ0),({[(r,(l,w),r')]} ∪ g), (<[r':=<[l:=v]> σ0]>M).
    rewrite big_sepS_union.
    { apply disjoint_singleton_l. intros ?. apply Hr'.
      apply elem_of_vertices. eauto. }
    rewrite big_sepS_singleton. iFrame "#∗".

    iSplitR "HC".
    { iPureIntro.
      split_and!; first done.
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
            apply path_add_inv_r in Hreach; try done.
            destruct Hreach as [(->&->)|(ds'&->&Hreach)].
            { congruence. }
            specialize (X4 _ _ _ _ _ Hreach E1 X3).
            rewrite fmap_app apply_diffl_snoc insert_insert insert_id //. }
          { rewrite lookup_insert_ne //. intros. eapply X4; eauto.
            apply path_cycle_end_inv_aux in Hreach; eauto. } } }
      { destruct Hcoh as [X1 X2].
        constructor.
        { intros r0 ?. destruct_decide (decide (r0=r')).
          { subst. rewrite lookup_insert. inversion 1. done. }
          rewrite lookup_insert_ne //. intros HM.
          apply X1 in HM. rewrite dom_insert_lookup_L //. }
        { intros ?. set_solver. } }
      { eauto using rooted_dag_add. } }
    { iDestruct "HC" as "[% [% (%Hsnap&?&?)]]". iExists _,C. iFrame.
      iPureIntro.
      intros r0 ? HC. apply Hsnap in HC. destruct HC as (?&HC&?).
      destruct_decide (decide (r0=r')).
      { exfalso. subst. destruct Hinv as [X1 X2 X3].
        assert (r' ∉ dom M) as F by set_solver. apply F. by eapply elem_of_dom. }
      rewrite lookup_insert_ne //. eauto. }
  Qed.

  Lemma store_capture_spec t σ :
    {{{
      store t σ
    }}}
      store_capture t
    {{{ s,
      RET s;
      store t σ ∗
      snapshot t s σ
    }}}.
  Proof.
    iIntros (Φ) open_inv. iIntros "HΦ".
    wp_rec. wp_load. do 5 iStep.

    iDestruct "HC" as "[% [% (%Hsnap&#?&HC)]]".
    iMod (mono_set_insert' (r,σ) with "HC") as "(HC&Hsnap)".
    iModIntro.
    iSplitR "Hsnap". 2:iSteps.
    iExists _,_,_,_,_. iFrame.
    iSplitR "HC".
    { iPureIntro. split_and!; eauto. }
    iExists _,_. iFrame "#∗". iPureIntro.
    intros r' ? HC. rewrite elem_of_union elem_of_singleton in HC.
    destruct HC as [HC|HC]; last eauto.
    inversion HC. subst. destruct Hinv. eauto.
  Qed.

  Definition fsts  (ys:list (loc*(loc*val)*loc)) : list val :=
    (fun '(x,_,_) => ValLoc x) <$> ys.

  Lemma store_collect_spec_aux (r r':loc) t' (xs:list val) (ys:list (loc*(loc*val)*loc)) (g:graph_store) :
    lst_model' t' xs ->
    path g r ys r' ->
    {{{
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : loc), v, #(r' : loc) })
    }}}
      store_collect #r t'
    {{{ t,
      RET (#r',t);
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : loc), v, #(r' : loc) }) ∗
      lst_model t (rev_append (fsts ys) xs)
    }}}.
  Proof.
    iIntros (-> Hpath Φ) "(Hr'&Hg) HΦ".
    iInduction ys as [|] "IH" forall (r xs r' Hpath); wp_rec.
    { inversion Hpath. subst. iSteps. }
    { inversion Hpath. subst.
      iDestruct (big_sepS_elem_of_acc _ _ (r,b,a2) with "[$]") as "(?&Hg)".
      { set_solver. } destruct b.
      wp_load.
      iSpecialize ("Hg" with "[$]").
      iSpecialize ("IH" with "[%//][$][$][$]").
      iSteps.
    }
  Qed.

  Lemma store_collect_spec (r r':loc) (ys:list (loc*(loc*val)*loc)) (g:graph_store) :
    path g r ys r' ->
    {{{
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : loc), v, #(r' : loc) })
    }}}
      store_collect #r §Nil
    {{{ t,
      RET (#r',t);
      r' ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : loc), v, #(r' : loc) }) ∗
      lst_model t (rev (fsts ys))
    }}}.
  Proof.
    iIntros (? Φ) "(?&?) HΦ".
    iDestruct (store_collect_spec_aux with "[$]") as "Go"; [done.. |].
    rewrite -lst_to_val_nil.
    iApply "Go". rewrite -rev_alt //.
  Qed.

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

  (* [undo xs ys σ] asserts [mirror xs ys] and that [σ = apply_diffl (proj2 <$> ys ++ xs) σ],
     ie, ys undo the changes of xs *)
  Inductive undo :
    list (loc*(loc*val)*loc) -> list (loc*(loc*val)*loc) -> gmap loc val -> Prop :=
  | undo_nil :
    forall σ, undo [] [] σ
  | undo_cons :
    forall σ r l v v' r' xs ys,
      σ !! l = Some v' ->
      undo xs ys (<[l:=v]> σ) ->
      undo (xs++[(r,(l,v),r')]) ((r',(l,v'),r)::ys) σ.

  Lemma use_undo xs ys σ :
    undo xs ys σ ->
    σ = apply_diffl (proj2 <$> ys ++ xs) σ.
  Proof.
    induction 1.
    { done. }
    rewrite !assoc_L fmap_app apply_diffl_snoc.
    rewrite -app_comm_cons fmap_cons apply_diffl_cons.
    rewrite -IHundo insert_insert insert_id //.
  Qed.

  Lemma undo_mirror xs ys g :
    undo xs ys g ->
    mirror xs ys.
  Proof.
    induction 1; eauto using mirror_cons,mirror_nil.
  Qed.

  Lemma store_revert_spec_aux g g1 r t g2 xs r' w σ σ0 :
    lst_model' t (fsts (rev xs)) ->
    locs_of_edges_in g2 (dom σ) ->
    g2 = list_to_set xs ->
    acyclic g ->
    g2 ⊆ g ->
    path g r xs r' ->
    {{{
      r' ↦ w ∗
      ([∗ map] l0↦v0 ∈ σ, l0 ↦ v0) ∗
      ([∗ set] '(r, (l, v), r') ∈ g1, r ↦ ’Diff{ #(l : loc), v, #(r' : loc) }) ∗
      ([∗ set] '(r, (l, v), r') ∈ g2, r ↦ ’Diff{ #(l : loc), v, #(r' : loc) })
    }}}
      store_revert #r' t
    {{{
      RET ();
      ∃ ys,
      ⌜undo xs ys σ⌝ ∗
      r ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ (g1 ∪ list_to_set ys), r ↦ ’Diff{ #(l : loc), v, #(r' : loc) }) ∗
      ([∗ map] l0↦v0 ∈ (apply_diffl (proj2 <$> xs) σ), l0 ↦ v0)
    }}}.
  Proof.
    iIntros (-> Hlocs Hg Hacy Hsub Hpath Φ) "(Hr'&Hσ&Hg1&Hg2) HΦ".
    iInduction xs as [|((r0,(l,v)),r1) ] "IH" using rev_ind forall (σ w r r' g1 g2  Hpath Hg Hlocs Hacy Hsub).
    { wp_rec. simpl.
      iStep 4. iModIntro.
      inversion Hpath. subst. wp_store. iModIntro.
      iApply "HΦ". iExists nil. rewrite !right_id_L. iFrame.
      iPureIntro. eauto using undo_nil. }
    { wp_rec. simpl. rewrite rev_unit. simpl.
      iStep 4. iModIntro.
      rewrite Hg list_to_set_app_L list_to_set_cons list_to_set_nil right_id_L.
      rewrite Hg list_to_set_app_L in Hsub.
      assert ((r0, (l, v), r1) ∉ (list_to_set xs : gset (loc * diff * loc))).
      { intros ?. apply use_path in Hpath; last done. destruct Hpath as (?&Hpath&?).
        apply Hacy in Hpath. congruence. set_solver. }
      iDestruct (big_sepS_union with "Hg2") as "(Hg2&?)".
      { set_solver. }
      rewrite big_sepS_singleton. wp_load. iStep 4. iModIntro.

      rewrite Hg list_to_set_app_L list_to_set_cons list_to_set_nil right_id_L in Hlocs.
      assert (exists v', σ !! l = Some v') as (v',Hl).
      { apply elem_of_dom. eapply Hlocs. rewrite /edge.

        rewrite elem_of_union elem_of_singleton. right. reflexivity. }

      apply path_snoc_inv in Hpath. destruct Hpath as (?&->&?).
      wp_smart_apply assert_spec. rewrite bool_decide_eq_true_2 //.
      iStep 4. iModIntro.

      iDestruct (big_sepM_insert_acc with "Hσ") as "(?&Hσ)". done.
      wp_load. wp_store. wp_store. iStep 4. iModIntro.

      iSpecialize ("Hσ" with "[$]").
      iSpecialize ("IH" with "[%//][%//][%][%//][%][$][$] Hg1 Hg2").
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
        iDestruct (pointsto_ne r' r' with "[$][$]") as "%". congruence. }
      replace (g1 ∪ ({[(r', (l, v'), r0)]} ∪ list_to_set ys)) with ({[(r', (l, v'), r0)]} ∪ ((g1 ∪ list_to_set ys))). 2:set_solver.
      iApply big_sepS_union. set_solver.
      iFrame. rewrite big_sepS_singleton //. }
  Qed.

  Lemma store_revert_spec r t g xs r' w σ σ0 :
    lst_model' t (fsts (rev xs)) ->
    locs_of_edges_in g (dom σ) ->
    g = list_to_set xs ->
    acyclic g ->
    path g r xs r' ->
    {{{
      r' ↦ w ∗
      ([∗ map] l0↦v0 ∈ σ, l0 ↦ v0) ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : loc), v, #(r' : loc) })
    }}}
      store_revert #r' t
    {{{
      RET ();
      ∃ ys,
      ⌜undo xs ys σ⌝ ∗
      r ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ (list_to_set ys), r ↦ ’Diff{ #(l : loc), v, #(r' : loc) }) ∗
      ([∗ map] l0↦v0 ∈ (apply_diffl (proj2 <$> xs) σ), l0 ↦ v0)
    }}}.
  Proof.
    iIntros (->???? Φ) "(?&?&?) HΦ".
    iApply (store_revert_spec_aux g ∅ with "[-HΦ]"); try done.
    { rewrite big_sepS_empty. iFrame. }
    { iModIntro. iIntros "[% ?]". iApply "HΦ". iExists _. rewrite left_id_L //. }
  Qed.

  Lemma rev_fsts xs :
    rev (fsts xs) = fsts (rev xs).
  Proof.
    induction xs as [|((?,?),?)]; simpl; eauto.
    rewrite IHxs /fsts fmap_app //.
  Qed.

  Lemma store_reroot_spec r (xs:list (loc*(loc*val)*loc)) r' g σ :
    locs_of_edges_in g (dom σ) ->
    g = list_to_set xs ->
    acyclic g ->
    path g r xs r' ->
    {{{
      r' ↦ §Root ∗
      ([∗ map] l0↦v0 ∈ σ, l0 ↦ v0) ∗
      ([∗ set] '(r, (l, v), r') ∈ g, r ↦ ’Diff{ #(l : loc), v, #(r' : loc) })
    }}}
      store_reroot #r
    {{{
      RET ();
      ∃ ys,
      ⌜undo xs ys σ⌝ ∗
      r ↦ §Root ∗
      ([∗ set] '(r, (l, v), r') ∈ (list_to_set ys), r ↦ ’Diff{ #(l : loc), v, #(r' : loc) }) ∗
      ([∗ map] l0↦v0 ∈ (apply_diffl (proj2 <$> xs) σ), l0 ↦ v0)
    }}}.
  Proof.
    iIntros (???? Φ) "(Hr'&Hσ&Hg) HΦ".
    wp_rec. wp_apply (store_collect_spec with "[$]"). done.
    iIntros (?) "(?&?&%Heq)". rewrite {}Heq.
    wp_smart_apply (store_revert_spec with "[-HΦ]"); try done; first rewrite rev_fsts //.
    iSteps.
  Qed.

  Lemma locs_of_edges_weak g1 g2 X :
    locs_of_edges_in g1 X ->
    g2 ⊆ g1 ->
    locs_of_edges_in g2 X.
  Proof.
    intros Z ? a b c d ?. eapply (Z a b c d). set_solver.
  Qed.

  Lemma undo_same_fst_label xs ys r l v r' σ :
    undo xs ys σ ->
    (r, (l, v), r') ∈ (list_to_set ys :  gset (loc*(loc*val)*loc)) ->
    l ∈ (list_to_set (proj2 <$> xs).*1 : gset loc).
  Proof.
    revert xs σ. induction ys as [|(?,?)]. set_solver.
    intros xs σ. inversion 1. subst.
    simpl. rewrite !fmap_app list_to_set_app_L. simpl in *. subst.
    destruct_decide (decide ((r, (l, v), r') = (r'0, (l1, v'), l0))) as Heq.
    { inversion Heq. subst. intros _. set_solver. }
    intros ?. simpl. apply elem_of_union. left. eapply IHys. done. set_solver.
  Qed.

  Definition diff_last {A:Type} (ys1 ys2:list A) :=
    match last ys1, last ys2 with
    | Some x, Some y =>
        x ≠ y
    | _, _ =>
        True
    end.

  Lemma path_extract_suffix (g:gset (loc*(loc*val)*loc)) a1 a2 xs1 r xs2 :
    unaliased g ->
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

  Lemma diff_last_app_middle {A:Type} x (l1' l2' l1 l2:list A) :
    diff_last (l1' ++ x :: l2') (l1 ++ x :: l2) ->
    diff_last (x :: l2') (x :: l2).
  Proof.
    unfold diff_last. rewrite !last_app !last_cons.
    destruct (last l2),(last l2'); eauto.
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
    unaliased g ->
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
      eapply acyclic_unaliased_impl_uniq_path in Hp2; eauto.
      apply Hp2 in Hp1.
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

  Lemma path_cannot_escape (x:(loc * diff * loc)) (xs ys:list (loc * diff * loc)) (g1: graph loc (loc*val)) a a' r :
    (forall x l', ¬ (r,x,l') ∈ (g1 ∪ list_to_set ys)) ->
    unaliased (g1 ∪ list_to_set ys) ->
    x ∈ (list_to_set ys : gset _) ->
    pathlike ys r ->
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
    unaliased (g1 ∪ list_to_set ys) ->
    pathlike ys r ->
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

  Lemma undo_preserves_rooted_dag (g:graph loc (loc*val)) xs ys rs r :
    (forall x l', ¬ (rs,x,l') ∈ (list_to_set ys ∪ g ∖ list_to_set xs)) -> (* root has no succ *)
    unaliased g ->
    unaliased (list_to_set ys ∪ g ∖ list_to_set xs) ->
    path g rs xs r ->
    mirror xs ys ->
    rooted_dag g r ->
    rooted_dag (list_to_set ys ∪ g ∖ list_to_set xs) rs.
  Proof.
    intros Hnr Hinj Hinj' Hpath Hmirror Hroot. inversion Hroot as [X1 X2].
    assert (vertices (list_to_set ys ∪ g ∖ list_to_set xs) = vertices g) as Hvg.
    { apply mirror_vertices in Hmirror.
      rewrite vertices_union Hmirror -vertices_union -union_difference_L //.
      eauto using path_all_in. }

    constructor.
    { intros a. rewrite Hvg => Ha.
      apply X1 in Ha. destruct Ha as (zs&Ha).
      edestruct (path_extract_suffix g a rs) as (ys1&ys2&us&?&?&Hlast); eauto. subst.

      apply path_middle in Ha. destruct Ha as (y&Hy1&Hy2).
      apply path_middle in Hpath. destruct Hpath as (y'&Hy'1&Hy'2).
      assert (y'=y) as ->.
      { inversion Hy'2; subst; inversion Hy2; naive_solver. }
      eapply use_mirror_subset in Hmirror. 3:apply Hy'1. 2:set_solver.
      destruct Hmirror as (zs&Hzs&_).
      exists (ys1++zs). eapply path_app.
      2:{ eapply path_weak. done. set_solver. }
      clear X2. induction Hy1.
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
        destruct (last bs), (last ys2); try done. } }
    { intros a zs Hzs. rewrite comm_L in Hzs.
      apply path_union_inv in Hzs. destruct Hzs as [Hsz|Hsz].
      (* The cycle is only in g, easy. *)
      { eapply X2. eapply path_weak. done. set_solver. }
      (* There is at least a vertex in ys.
         We are going to construct a cycle in ys, implying a cycle in xs. *)
      exfalso. destruct Hsz as (a'&x&l1&l2&E1&Hx&E2&->).

      apply path_cannot_escape with (r:=rs) in E2; last first.
      { eapply path_pathlike. eapply use_mirror; eauto. }
      { done. }
      { rewrite comm_L //. }
      { set_solver. }

      eapply path_weak in E1.
      eapply path_in_seg_complete with (r:=rs) in E1; last first. done.
      { eapply path_pathlike. eapply use_mirror; eauto. }
      { rewrite comm_L //. }
      { set_solver. }
      2:{ set_solver. }
      destruct E1 as (?&E1).

      assert (path (list_to_set ys) a (x0 ++ x::l2) a ) as Hcycle.
      { eapply path_app. done. done. }

      eapply use_mirror_subset with (ys:=xs) in Hcycle.
      3:{ by apply mirror_symm. }
      2:{ apply path_all_in in Hcycle. set_solver. }
      destruct Hcycle as (?&Hcycle&F).
      eapply path_weak in Hcycle. 2:eapply path_all_in; done.
      eapply ti2 in Hcycle; eauto. subst. destruct x0; simpl in *; lia. }
  Qed.

  Lemma undo_app_inv xs ys1 ys2 σ :
    undo xs (ys1 ++ ys2) σ ->
    exists xs1 xs2, xs = xs2 ++ xs1 /\ undo xs2 ys2 (apply_diffl (proj2 <$> xs1) σ) /\ undo xs1 ys1 σ.
  Proof.
    revert xs ys2 σ. induction ys1; intros xs ys2 σ Hundo.
    { exists nil,xs. rewrite right_id_L. split; eauto using undo_nil. }
    rewrite -app_comm_cons in Hundo. inversion Hundo. subst.
    apply IHys1 in H4. destruct H4 as (xs1&xs2&->&?&?).
    eexists _,xs2. split_and !.
    { rewrite -assoc_L //. }
    { rewrite fmap_app apply_diffl_app. done. }
    { apply undo_cons. done. done. }
  Qed.

  Lemma construct_middlepoint (g:graph loc (loc*val)) a1 xs ys a2 a2' :
    unaliased g ->
    (forall x l', ¬ (a2,x,l') ∈ g) -> (* root has no succ *)
    path g a1 xs a2 ->
    path g a1 ys a2' ->
    exists zs, xs = ys ++ zs.
  Proof.
    intros Hinj Hroot Hpath. revert ys. induction Hpath; intros ys.
    { intros Hpath. inversion Hpath. eauto. subst. set_solver. }
    { intros X. inversion X; subst.
      { exists ((a2', b, a2) :: bs ). done. }
      destruct (Hinj _ _ _ _ _ H H0). subst.
      apply IHHpath in H1. destruct H1 as (?&?).
      eexists. rewrite -app_comm_cons H1 //.
      intros ??. apply Hroot. }
  Qed.


  Lemma undo_preserves_model g (M:map_model) (xs ys:list (loc* (loc*val)*loc)) rs σ0 r:
    dom M = vertices g ∪ {[r]} ->
    correct_path_diff M g ->
    (forall x l', ¬ (rs,x,l') ∈ (list_to_set ys ∪ g ∖ list_to_set xs)) -> (* root has no succ *)
    unaliased (g ∖ list_to_set xs ∪ list_to_set ys) ->
    path g rs xs r ->
    undo xs ys σ0 ->
    M !! r = Some σ0 ->
    correct_path_diff M (list_to_set ys ∪ g ∖ list_to_set xs).
  Proof.
    intros Hdom Hinv Hroot Hinj' Hrs Hundo E0.
    intros r1 zs r2 σ1 σ2 Hpath E1 E2. rewrite comm_L in Hpath.
    apply path_union_inv in Hpath. destruct Hpath as [Hpath|Hpath].

    (* If the path is entirely in g, easy. *)
    { eapply Hinv; eauto. eapply path_weak. done. set_solver. }

    assert (mirror xs ys) as Hmirror by eauto using undo_mirror.

    destruct Hpath as (a'&x&l1&l2&X1&Hx&X2&Hzs).
    eapply path_cannot_escape with (r:=rs) in X2; eauto; last first.
    { eapply path_pathlike. eapply use_mirror; eauto. }
    { set_solver. }

    (* otherwise the path includes a part in g, and a part in ys. *)

    assert (vertices (list_to_set ys ∪ g ∖ list_to_set xs) = vertices g) as Hvg.
    { apply mirror_vertices in Hmirror.
      rewrite vertices_union Hmirror -vertices_union -union_difference_L //.
      eauto using path_all_in. }

    assert (a' ∈ dom M) as Ha'.
    { rewrite Hdom -Hvg elem_of_union. left. apply elem_of_vertices.
      inversion X2. set_solver. }
    apply elem_of_dom in Ha'. destruct Ha' as (σ',Ea').
    assert (σ1 = (apply_diffl (proj2 <$> l1) σ')).
    { eapply path_weak in X1.
      eapply (Hinv _ _ _ _ _ X1 E1 Ea'). set_solver. }

    (* The part in g is preserved. *)

    etrans. done. rewrite Hzs. rewrite fmap_app apply_diffl_app.
    f_equal. clear dependent σ1 l1.

    (* XXX facto a lemma. *)
    assert (exists u1 u2, ys = u1 ++ (x::l2) ++ u2) as (u1&u2&Hys).
    { eapply use_mirror in Hrs. 2:done.
      apply elem_of_list_to_set, elem_of_middle in Hx.
      destruct Hx as (p1&p2&->).
      apply path_app_inv in Hrs. destruct Hrs as (?&Hp1&Hp2).
      inversion Hp2; inversion X2. subst. inversion H5. subst.
      eapply construct_middlepoint in H10. 4:apply H4.
      2:{ intros z1 z2 z3 z4 z5 ??. eapply (Hinj' z1 z2 z3 z4 z5); try done.
          all:apply elem_of_union; right. all:set_solver. }
      2:{ intros x l' X. eapply (Hroot x l').
          apply elem_of_union. left. set_solver. }
      destruct H10.
      eexists _,_. f_equal. rewrite -app_comm_cons. f_equal. done. }

    rewrite Hys assoc_L in Hundo. apply undo_app_inv in Hundo.
    destruct Hundo as (xs1&xs2&->&Hundo1&Hundo2).
    apply undo_app_inv in Hundo2.
    destruct Hundo2 as (xs4&xs3&->&Hundo2&Hundo3).

    eapply use_mirror in Hmirror. 2:done.
    rewrite {2}Hys in Hmirror.
    apply path_app_inv in Hmirror. destruct Hmirror as (n1&T1&T2).
    apply path_app_inv in T2. destruct T2 as (n2&T2&T3).
    edestruct (same_path (list_to_set ys) (x::l2) n1 n2 a') as (?&?); try done.
    subst n1 n2.

    assert (path g a' xs4 r) as R1.
    { eapply path_weak.
      eapply use_mirror. eapply mirror_symm. eauto using undo_mirror. done.
      apply path_all_in in Hrs. set_solver. }
    apply (Hinv _ _ _ σ' σ0) in R1; try done.

    assert (path g r2 xs3 a') as R2.
    { eapply path_weak.
      eapply use_mirror. eapply mirror_symm. eauto using undo_mirror. done.
      apply path_all_in in Hrs. set_solver. }
    eapply (Hinv _ _ _ σ2 σ') in R2; try done.
    rewrite R2. rewrite -apply_diffl_app -fmap_app.
    eapply use_undo. rewrite R1. done.
  Qed.

  Lemma use_snapshots_model γ (t0:loc) M r σ :
    meta t0 nroot γ -∗
    snapshosts_model t0 M -∗
    store_map_elem γ r σ -∗
    ⌜exists σ1, M !! r = Some σ1 /\ σ ⊆ σ1⌝.
  Proof.
    iIntros "Hmeta [%γ' [%C (%Hsnap&Hmeta'&HC)]] ?".
    iDestruct (meta_agree with "Hmeta' Hmeta") as "->".
    iDestruct (mono_set_elem_valid with "[$][$]") as "%Hrs".
    apply Hsnap in Hrs. destruct Hrs as (σ1&HMrs&?).
    eauto.
  Qed.

  Lemma store_restore_spec t σ s σ' :
    {{{
      store t σ ∗
      snapshot t s σ'
    }}}
      store_restore t s
    {{{
      RET ();
      store t σ'
    }}}.
  Proof.
    iIntros (Φ) "(HI&Hsnap) HΦ".
    iDestruct "HI" as open_inv.

    iDestruct "Hsnap" as "[%γ [%t0' [%rs ((%Eq&->)&Hmeta'&Hsnap)]]]".
    inversion Eq. subst t0'. clear Eq.

    iDestruct (use_snapshots_model with "[$][$][$]") as %(σ1&HMrs&?).

    wp_rec. iStep 20.

    iDestruct (extract_unaliased with "Hg") as "%".
    destruct_decide (decide (rs=r)).
    { subst.
      wp_load. iStep 4. iModIntro.
      iExists _,_,_,_,_. iFrame. iPureIntro. split_and!; eauto.
      { destruct Hinv as [X1 X2 X3 X4]. constructor; eauto. naive_solver. } }

    assert (rs ∈ vertices g) as Hrs.
    { destruct Hinv. apply elem_of_dom_2 in HMrs. set_solver. }

    eapply ti1 in Hrs; eauto. destruct Hrs as (ds,Hrs).
    inversion Hrs. congruence. subst. rename a2 into r'. destruct b.
    iDestruct (big_sepS_elem_of_acc with "[$]") as "(?&Hg)". done. simpl.
    wp_load. iStep 2. iModIntro.
    iSpecialize ("Hg" with "[$]").

    remember ((rs, (l, v), r') :: bs) as xs.
    assert (list_to_set xs ⊆ g).
    { eauto using path_all_in. }

    rewrite (union_difference_L (list_to_set xs) g) //.

    iDestruct (big_sepS_union with "Hg") as "(Hxs&Hg)". set_solver.
    wp_apply (store_reroot_spec with "[Hr Hxs Hσ0]").
    4:{ eapply path_restrict. done. }
    2:done.
    { destruct Hcoh as [_ X]. eapply locs_of_edges_weak; eauto. }
    { eapply acyclic_weak; eauto using ti2. }
    { iFrame. }

    iIntros "[%ys (%Hundo&?&?&?)]".
    assert (mirror xs ys) as Hmirror by eauto using undo_mirror.
    iStep 8. do 2 iModIntro.
    iApply "HΦ".
    iDestruct (big_sepS_union_2 with "[$][$]") as "Hs".

    remember ((rs, (l, v), r') :: bs) as xs.

    iDestruct (extract_unaliased with "Hs") as "%".

    assert (({[(rs, (l, v), r')]} ∪ list_to_set bs) = (list_to_set xs : gset _)) as Hbs.
    { subst xs. reflexivity. }
    rewrite Hbs. rewrite Hbs in H5.

    iAssert ⌜forall x y, (rs,x,y) ∉ (list_to_set ys ∪ g ∖ list_to_set xs)⌝%I as "%".
    { iIntros (???). destruct a. iDestruct (big_sepS_elem_of with "Hs") as "?". done.
      iDestruct (pointsto_ne rs rs with "[$][$]") as "%". congruence. }

    iExists _,_,_,_,M. iFrame.

    assert (vertices (list_to_set ys ∪ g ∖ list_to_set xs) = vertices g) as Hvg.
    { apply mirror_vertices in Hmirror.
      rewrite vertices_union Hmirror -vertices_union -union_difference_L //. }

    assert (σ1 = (apply_diffl (proj2 <$> xs) σ0)).
    { destruct Hinv as [X1 X2 X3 X4]. eauto. }

    assert (rooted_dag (list_to_set ys ∪ g ∖ list_to_set xs) rs) as Hroot.
    { eapply undo_preserves_rooted_dag; eauto. }

    iPureIntro. split_and !; try done.
    { destruct Hinv as [X1 X2 X3 X4]. constructor.
      { rewrite X1 Hvg.
        apply elem_of_dom_2 in X3,HMrs.
        apply path_ends_vertices in Hrs.
        set_solver. }
      { subst xs. set_solver. }
      { set_solver. }
      { intros. eapply undo_preserves_model; eauto. rewrite comm_L //. }
    } {
      rewrite /apply_diffl.
      replace (<[l:=v]> (foldr (λ '(l0, v0) σ2, <[l0:=v0]> σ2) σ0 (list_fmap (loc * diff * loc)%type diff proj2 bs))) with (apply_diffl (proj2 <$> xs) σ0).
      2:{ subst xs. reflexivity. }

      destruct Hcoh as [X1 X2]. constructor.
      { intros ???. rewrite dom_apply_diffl. apply X1 in H8.
        eapply use_locs_of_edges_in in Hrs. 2:done.
        set_solver.
      } {
        rewrite dom_apply_diffl. intros ???? Hedge.
        rewrite /edge elem_of_union in Hedge. rewrite elem_of_union.
        destruct Hedge as [Hedge|Hedge].
        { right. eauto using undo_same_fst_label. }
        { left. eapply (X2 r0). eapply elem_of_subseteq. 2:done. set_solver. }
    } }
  Qed.
End store_G.

#[global] Opaque store_create.
#[global] Opaque store_ref.
#[global] Opaque store_get.
#[global] Opaque store_set.
#[global] Opaque store_capture.
#[global] Opaque store_restore.

#[global] Opaque store.
#[global] Opaque snapshot.
