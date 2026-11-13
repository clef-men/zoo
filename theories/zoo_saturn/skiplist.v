Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_typed.
Require Import zoo_std.option.
Require Export zoo_saturn.skiplist__code.
Require Import zoo_saturn.skiplist__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v t key compare prevs curr : val.

(* ------------------------------------------------------------------------ *)
(* Validity of the comparison function. *)

Section skiplist۰valid.
  Context `{zoo۰G : !ZooG Σ}.

  (* Abstract keys: [key۰model key 𝑘𝑒𝑦] means that the key value [key]
     represents the abstract key [𝑘𝑒𝑦]. Abstract keys are ordered by the
     strict order [lt]. *)
  Context {Key : Type}.
  Context (key۰model : val → Key → iProp Σ).
  Context (lt : relation Key).

  Implicit Type 𝑘𝑒𝑦 : Key.

  (* A key value represents at most one abstract key. *)
  Definition skiplist۰valid۰functional : iProp Σ :=
    □ ∀ key 𝑘𝑒𝑦1 𝑘𝑒𝑦2,
      key۰model key 𝑘𝑒𝑦1 -∗
      key۰model key 𝑘𝑒𝑦2 -∗
      ⌜𝑘𝑒𝑦1 = 𝑘𝑒𝑦2⌝.

  (* [lt] is a strict order. *)
  Definition skiplist۰valid۰order : Prop :=
    StrictOrder lt.

  (* [compare] compares abstract keys according to [lt]: a negative result
     means [lt 𝑘𝑒𝑦1 𝑘𝑒𝑦2], zero means equality and a positive result means
     [lt 𝑘𝑒𝑦2 𝑘𝑒𝑦1]. *)
  Definition skiplist۰valid۰compare compare : iProp Σ :=
    □ ∀ key1 𝑘𝑒𝑦1 key2 𝑘𝑒𝑦2,
      key۰model key1 𝑘𝑒𝑦1 -∗
      key۰model key2 𝑘𝑒𝑦2 -∗
      WP compare key1 key2 {{ res,
        ∃ (cmp : Z),
        ⌜res = #cmp⌝ ∗
        ⌜(cmp < 0)%Z → lt 𝑘𝑒𝑦1 𝑘𝑒𝑦2⌝ ∗
        ⌜(cmp = 0)%Z → 𝑘𝑒𝑦1 = 𝑘𝑒𝑦2⌝ ∗
        ⌜(0 < cmp)%Z → lt 𝑘𝑒𝑦2 𝑘𝑒𝑦1⌝
      }}.

  Definition skiplist۰valid compare : iProp Σ :=
    skiplist۰valid۰functional ∗
    ⌜skiplist۰valid۰order⌝ ∗
    skiplist۰valid۰compare compare.
End skiplist۰valid.

(* ------------------------------------------------------------------------ *)
(* Nodes, links and slots. *)

(* An inserted node: its key, the abstract key it represents, its value, its
   array of successors, its height and the ghost name of its marks. *)
Record node Key := Node
  { node۰key : val
  ; node۰𝑘𝑒𝑦 : Key
  ; node۰value : val
  ; node۰nexts : val
  ; node۰height : nat
  ; node۰marks : gname
  }.
#[local] Arguments Node {_} _ _ _ _ _ _.
#[local] Arguments node۰key {_} _.
#[local] Arguments node۰𝑘𝑒𝑦 {_} _.
#[local] Arguments node۰value {_} _.
#[local] Arguments node۰nexts {_} _.
#[local] Arguments node۰height {_} _.
#[local] Arguments node۰marks {_} _.

#[local] Definition node۰to_val {Key} (node : node Key) :=
  ‘skiplist٠Node( node.(node۰key), node.(node۰value), node.(node۰nexts) )%V.
#[local] Arguments node۰to_val _ !_ / : assert.

(* A link is either [Null] or a node. *)
#[local] Definition link۰to_val {Key} (link : option (node Key)) :=
  match link with
  | None =>
      §skiplist٠Null%V
  | Some node =>
      node۰to_val node
  end.
#[local] Arguments link۰to_val _ !_ / : assert.

#[local] Definition link۰tag_null :=
  match §skiplist٠Null%V with
  | ValBlock _ tag _ =>
      tag
  | _ =>
      Tag0
  end.
#[local] Definition link۰tag_node :=
  match ‘skiplist٠Node( ()%V, ()%V, ()%V )%V with
  | ValBlock _ tag _ =>
      tag
  | _ =>
      Tag0
  end.

(* None of the branches [brs] matches a link value (same tag and same arity),
   so that a [match] on a link value takes its fallback branch. *)
#[local] Definition branches۰link۰fallback (brs : list branch) :=
  forallb (λ br, negb (br.1.(pattern۰tag) ≟ link۰tag_null && length br.1.(pattern۰fields) ≟ 0)) brs &&
  forallb (λ br, negb (br.1.(pattern۰tag) ≟ link۰tag_node && length br.1.(pattern۰fields) ≟ 3)) brs.
#[local] Arguments branches۰link۰fallback !_ / : assert.

(* This instance lets [wp۰pures] reduce a [match] on [link۰to_val link] when
   [link] is abstract. *)
#[local] Instance pureｰmatchｰlink {Key} (link : option (node Key)) x_fb e_fb brs :
  PureExec
    (branches۰link۰fallback brs = true)
    1
    (Match (Val $ link۰to_val link) x_fb e_fb brs)
    (subst' x_fb (link۰to_val link) e_fb).
Proof.
  intros (Hnull & Hnode)%andb_true_iff.
  destruct link as [node |].
  - apply pureｰmatch, exec۰matchｰfallback, Hnode.
  - apply pureｰmatch, exec۰matchｰfallback, Hnull.
Qed.

(* A slot of an array of successors: a possibly marked link. *)
#[local] Definition slot۰to_val {Key} (marked : bool) (link : option (node Key)) :=
  if marked then
    ‘skiplist٠Mark( link۰to_val link )%V
  else
    link۰to_val link.
#[local] Arguments slot۰to_val _ !_ _ / : assert.
#[local] Definition slot۰to_val' {Key} (slot : bool * option (node Key)) :=
  slot۰to_val slot.1 slot.2.

(* The physical state of an inserted node: its links (one per level) and the
   number of marked levels; levels are marked from the top. *)
Record status Key := Status
  { status۰links : list (option (node Key))
  ; status۰marked : nat
  }.
#[local] Arguments Status {_} _ _.
#[local] Arguments status۰links {_} _.
#[local] Arguments status۰marked {_} _.

(* A pending [remove]: the node it will try to mark and its key. *)
Record waiter Key := Waiter
  { waiter۰target : val
  ; waiter۰𝑘𝑒𝑦 : Key
  }.
#[local] Arguments Waiter {_} _ _.
#[local] Arguments waiter۰target {_} _.
#[local] Arguments waiter۰𝑘𝑒𝑦 {_} _.

(* ------------------------------------------------------------------------ *)
(* Pure invariant. *)

Section inv۰pure.
  Context {Key : Type} `{Countable Key}.
  Context (lt : relation Key).

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type node : node Key.
  Implicit Type nodes bottom : list (node Key).
  Implicit Type link : option (node Key).
  Implicit Type links roots : list (option (node Key)).
  Implicit Type status : status Key.
  Implicit Type statuses : list (status Key).
  Implicit Type waiter : waiter Key.
  Implicit Type m : gmap Key val.
  Implicit Type lvl : nat.

  #[local] Definition link۰wf nodes lvl link :=
    match link with
    | None =>
        True
    | Some node =>
        node ∈ nodes ∧
        lvl < node.(node۰height)
    end.

  #[local] Definition status۰wf nodes node status :=
    0 < node.(node۰height) ∧
    length status.(status۰links) = node.(node۰height) ∧
    status.(status۰marked) ≤ node.(node۰height) ∧
    ( ∀ lvl link,
      status.(status۰links) !! lvl = Some link →
      link۰wf nodes lvl link
    ).

  (* Whether level [lvl] of a node is marked. *)
  #[local] Definition status۰is_marked node status lvl :=
    bool_decide (node.(node۰height) - status.(status۰marked) ≤ lvl).

  #[local] Definition status۰vals node status :=
    imap (λ lvl, slot۰to_val (status۰is_marked node status lvl)) status.(status۰links).

  (* The links of the marked levels, from the top. *)
  #[local] Definition status۰frozen node status :=
    reverse (drop (node.(node۰height) - status.(status۰marked)) status.(status۰links)).

  #[local] Definition sorted bottom :=
    ∀ k node1 node2,
    bottom !! k = Some node1 →
    bottom !! S k = Some node2 →
    lt node1.(node۰𝑘𝑒𝑦) node2.(node۰𝑘𝑒𝑦).

  (* [nodes] are all the inserted nodes, [statuses] their states, [bottom] the
     nodes linked at level 0 (in order) and [roots] the links of the root. *)
  Record inv۰pure nodes statuses bottom roots m : Prop :=
    { inv۰pure۰length :
        length statuses = length nodes
    ; inv۰pure۰nodup :
        NoDup (node۰nexts <$> nodes)
    ; inv۰pure۰status i node status :
        nodes !! i = Some node →
        statuses !! i = Some status →
        status۰wf nodes node status
    ; inv۰pure۰roots lvl link :
        roots !! lvl = Some link →
        link۰wf nodes lvl link
    ; inv۰pure۰roots_head :
        roots !! 0 = Some (head bottom)
    ; inv۰pure۰bottom node :
        node ∈ bottom →
        node ∈ nodes
    ; inv۰pure۰bottom_links k node i status :
        bottom !! k = Some node →
        nodes !! i = Some node →
        statuses !! i = Some status →
        status.(status۰links) !! 0 = Some (bottom !! S k)
    ; inv۰pure۰sorted :
        sorted bottom
    ; inv۰pure۰unlinked i node status :
        nodes !! i = Some node →
        statuses !! i = Some status →
        status.(status۰marked) < node.(node۰height) →
        node ∈ bottom
    ; inv۰pure۰model 𝑘𝑒𝑦 v :
        m !! 𝑘𝑒𝑦 = Some v ↔
          ∃ i node status,
          nodes !! i = Some node ∧
          statuses !! i = Some status ∧
          status.(status۰marked) < node.(node۰height) ∧
          node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦 ∧
          node.(node۰value) = v
    }.

  (* A waiter is done when its target is marked at level 0. *)
  #[local] Definition waiter۰done nodes statuses waiter :=
    existsb
      ( λ '(node, status),
        bool_decide (
          node۰to_val node = waiter.(waiter۰target) ∧
          node.(node۰𝑘𝑒𝑦) = waiter.(waiter۰𝑘𝑒𝑦) ∧
          status.(status۰marked) = node.(node۰height)
        )
      )
      (zip nodes statuses).
End inv۰pure.

#[local] Arguments inv۰pure۰length {_ _ _ _ _ _ _ _ _}.
#[local] Arguments inv۰pure۰nodup {_ _ _ _ _ _ _ _ _}.
#[local] Arguments inv۰pure۰status {_ _ _ _ _ _ _ _ _}.
#[local] Arguments inv۰pure۰roots {_ _ _ _ _ _ _ _ _}.
#[local] Arguments inv۰pure۰roots_head {_ _ _ _ _ _ _ _ _}.
#[local] Arguments inv۰pure۰bottom {_ _ _ _ _ _ _ _ _}.
#[local] Arguments inv۰pure۰bottom_links {_ _ _ _ _ _ _ _ _}.
#[local] Arguments inv۰pure۰sorted {_ _ _ _ _ _ _ _ _}.
#[local] Arguments inv۰pure۰unlinked {_ _ _ _ _ _ _ _ _}.
#[local] Arguments inv۰pure۰model {_ _ _ _ _ _ _ _ _}.

(* ------------------------------------------------------------------------ *)
(* Pure invariant: lemmas. *)

(* The array of successors of the root or of an inserted node. *)
Variant prev :=
  | PrevRoot
  | PrevNode (i : nat).

Section inv۰pure.
  Context {Key : Type} `{Countable Key}.
  Context (lt : relation Key).

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type node pred succ : node Key.
  Implicit Type nodes bottom : list (node Key).
  Implicit Type link : option (node Key).
  Implicit Type links roots : list (option (node Key)).
  Implicit Type status : status Key.
  Implicit Type statuses : list (status Key).
  Implicit Type waiter : waiter Key.
  Implicit Type m : gmap Key val.
  Implicit Type lvl : nat.
  Implicit Type prev : prev.

  (* The slots of [prev]. *)
  #[local] Definition prev۰slots nodes statuses roots prev : list (bool * option (node Key)) :=
    match prev with
    | PrevRoot =>
        pair false <$> roots
    | PrevNode i =>
        match nodes !! i, statuses !! i with
        | Some node, Some status =>
            imap (λ lvl link, (status۰is_marked node status lvl, link)) status.(status۰links)
        | _, _ =>
            []
        end
    end.

  (* Set the link at level [lvl] of [prev]. *)
  #[local] Definition prev۰update statuses roots prev lvl link :=
    match prev with
    | PrevRoot =>
        (statuses, <[lvl := link]> roots)
    | PrevNode i =>
        ( alter (λ status, Status (<[lvl := link]> status.(status۰links)) status.(status۰marked)) i statuses
        , roots
        )
    end.

  (* [q] is the position in [bottom] of the successor of [prev] at level 0. *)
  #[local] Definition prev۰position nodes bottom prev q :=
    match prev with
    | PrevRoot =>
        q = 0
    | PrevNode i =>
        ∃ k node,
        nodes !! i = Some node ∧
        bottom !! k = Some node ∧
        q = S k
    end.

  #[local] Lemma sortedｰlt `{!StrictOrder lt} bottom k1 k2 node1 node2 :
    sorted lt bottom →
    k1 < k2 →
    bottom !! k1 = Some node1 →
    bottom !! k2 = Some node2 →
    lt node1.(node۰𝑘𝑒𝑦) node2.(node۰𝑘𝑒𝑦).
  Proof.
    intros Hsorted Hk Hlookup1.
    revert node2. induction Hk as [| k2 Hk IH]; intros node2 Hlookup2.
    - eapply Hsorted; done.
    - destruct (lookup_lt_is_Some_2 bottom k2) as (node & Hlookup).
      { apply lookup_lt_Some in Hlookup2. lia. }
      trans node.(node۰𝑘𝑒𝑦).
      + apply IH. done.
      + eapply Hsorted; done.
  Qed.
  #[local] Lemma sortedｰinj `{!StrictOrder lt} bottom k1 k2 node1 node2 :
    sorted lt bottom →
    bottom !! k1 = Some node1 →
    bottom !! k2 = Some node2 →
    node1.(node۰𝑘𝑒𝑦) = node2.(node۰𝑘𝑒𝑦) →
    k1 = k2.
  Proof.
    intros Hsorted Hlookup1 Hlookup2 Heq.
    destruct (Nat.lt_trichotomy k1 k2) as [Hk | [Hk | Hk]].
    - exfalso. apply (irreflexivity lt node1.(node۰𝑘𝑒𝑦)).
      rewrite {2}Heq. eapply sortedｰlt; done.
    - done.
    - exfalso. apply (irreflexivity lt node2.(node۰𝑘𝑒𝑦)).
      rewrite -{2}Heq. eapply sortedｰlt; done.
  Qed.
  #[local] Lemma sortedｰdelete `{!StrictOrder lt} bottom q :
    sorted lt bottom →
    sorted lt (delete q bottom).
  Proof.
    intros Hsorted k node1 node2 Hlookup1 Hlookup2.
    rewrite !list_lookup_delete in Hlookup1 Hlookup2.
    eapply sortedｰlt; [done | | done..].
    repeat case_decide; lia.
  Qed.

  #[local] Lemma lookupｰinsert_at {A} (l : list A) q x k :
    q ≤ length l →
    (take q l ++ x :: drop q l) !! k =
      if decide (k < q) then
        l !! k
      else if decide (k = q) then
        Some x
      else
        l !! (k - 1).
  Proof.
    intros Hq.
    assert (length (take q l) = q) as Hlength.
    { rewrite length_take. lia. }
    case_decide.
    - rewrite lookup_app_l; first lia.
      rewrite lookup_take_lt //.
    - rewrite lookup_app_r; first lia.
      rewrite Hlength.
      case_decide.
      + rewrite (_ : k - q = 0) //. lia.
      + rewrite (_ : k - q = S (k - 1 - q)); first lia.
        rewrite /= lookup_drop. f_equal. lia.
  Qed.

  Section inv۰pure.
    Context {nodes statuses bottom roots m}.
    Context (Hinv : inv۰pure lt nodes statuses bottom roots m).

    #[local] Lemma inv۰pureｰstatus_lookup i node :
      nodes !! i = Some node →
        ∃ status,
        statuses !! i = Some status.
    Proof.
      intros Hlookup.
      apply lookup_lt_is_Some_2.
      rewrite (inv۰pure۰length Hinv). eapply lookup_lt_Some. done.
    Qed.
    #[local] Lemma inv۰pureｰnode_lookup i status :
      statuses !! i = Some status →
        ∃ node,
        nodes !! i = Some node.
    Proof.
      intros Hlookup.
      apply lookup_lt_is_Some_2.
      rewrite -(inv۰pure۰length Hinv). eapply lookup_lt_Some. done.
    Qed.
    #[local] Lemma inv۰pureｰindex_inj i1 i2 node :
      nodes !! i1 = Some node →
      nodes !! i2 = Some node →
      i1 = i2.
    Proof.
      intros Hlookup1 Hlookup2.
      eapply NoDup_lookup; first apply (inv۰pure۰nodup Hinv).
      - rewrite list_lookup_fmap Hlookup1 //.
      - rewrite list_lookup_fmap Hlookup2 //.
    Qed.
    #[local] Lemma inv۰pureｰnexts_inj node1 node2 :
      node1 ∈ nodes →
      node2 ∈ nodes →
      node1.(node۰nexts) = node2.(node۰nexts) →
      node1 = node2.
    Proof.
      intros (i1 & Hlookup1)%list_elem_of_lookup (i2 & Hlookup2)%list_elem_of_lookup Heq.
      assert (i1 = i2) as <-.
      { eapply NoDup_lookup; first apply (inv۰pure۰nodup Hinv).
        - rewrite list_lookup_fmap Hlookup1 //.
        - rewrite list_lookup_fmap Hlookup2 /= -Heq //.
      }
      congruence.
    Qed.
    #[local] Lemma inv۰pureｰbottom_index node :
      node ∈ bottom →
        ∃ i status,
        nodes !! i = Some node ∧
        statuses !! i = Some status.
    Proof.
      intros (i & Hlookup)%(inv۰pure۰bottom Hinv)%list_elem_of_lookup.
      edestruct inv۰pureｰstatus_lookup; first done.
      naive.
    Qed.
    #[local] Lemma inv۰pureｰstatus_wf i node status :
      nodes !! i = Some node →
      statuses !! i = Some status →
      status۰wf nodes node status.
    Proof.
      apply (inv۰pure۰status Hinv).
    Qed.

    (* An unmarked level 0 is linked in [bottom]. *)
    #[local] Lemma inv۰pureｰprev0 prev link :
      prev۰slots nodes statuses roots prev !! 0 = Some (false, link) →
        ∃ q,
        prev۰position nodes bottom prev q ∧
        link = bottom !! q.
    Proof.
      destruct prev as [| i]; simpl.
      - rewrite list_lookup_fmap.
        intros (link' & Hlookup & [= ->])%fmap_Some.
        rewrite (inv۰pure۰roots_head Hinv) in Hlookup. injection Hlookup as <-.
        exists 0. split; first done.
        destruct bottom; done.
      - destruct (nodes !! i) as [node |] eqn:Hnodes_lookup; last done.
        destruct (statuses !! i) as [status |] eqn:Hstatuses_lookup; last done.
        rewrite list_lookup_imap.
        intros (link' & Hlinks_lookup & [= Hmarked ->])%fmap_Some.
        symmetry in Hmarked.
        rewrite /status۰is_marked bool_decide_eq_false in Hmarked.
        opose proof* (inv۰pure۰unlinked Hinv) as (k & Hk)%list_elem_of_lookup; [done.. | lia |].
        pose proof (inv۰pure۰bottom_links Hinv _ _ _ _ Hk Hnodes_lookup Hstatuses_lookup) as Hlinks_lookup'.
        exists (S k). split; first naive. congruence.
    Qed.

    (* If [𝑘𝑒𝑦] is in the model and all nodes before position [q] in
       [bottom] are smaller, then the node at position [q] is not greater. *)
    #[local] Lemma inv۰pureｰlocate `{!StrictOrder lt} 𝑘𝑒𝑦 v q :
      ( ∀ k,
        q = S k →
          ∃ pred,
          bottom !! k = Some pred ∧
          lt pred.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦
      ) →
      m !! 𝑘𝑒𝑦 = Some v →
        ∃ node,
        bottom !! q = Some node ∧
        ( node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦
        ∨ lt node.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦
        ).
    Proof.
      intros Hq (i & node & status & Hnodes_lookup & Hstatuses_lookup & Hmarked & <- & _)%(inv۰pure۰model Hinv).
      pose proof (inv۰pure۰unlinked Hinv _ _ _ Hnodes_lookup Hstatuses_lookup Hmarked) as (p & Hp)%list_elem_of_lookup.
      pose proof (inv۰pure۰sorted Hinv) as Hsorted.
      destruct (decide (q ≤ p)) as [Hle | Hlt].
      - destruct (lookup_lt_is_Some_2 bottom q) as (node' & Hnode').
        { apply lookup_lt_Some in Hp. lia. }
        exists node'. split; first done.
        destruct (decide (q = p)) as [-> | Hne].
        + left. congruence.
        + right. eapply (sortedｰlt _ q p); [done | lia | done..].
      - exfalso.
        destruct q as [| k]; first lia.
        destruct (Hq k) as (pred & Hpred & Hlt'); first done.
        eapply (irreflexivity lt node.(node۰𝑘𝑒𝑦)).
        destruct (decide (p = k)) as [-> | Hne].
        + congruence.
        + trans pred.(node۰𝑘𝑒𝑦); last done.
          eapply (sortedｰlt _ p k); [done | lia | done..].
    Qed.

    #[local] Lemma inv۰pureｰprev_position prev q 𝑘𝑒𝑦 :
      prev۰position nodes bottom prev q →
      ( ∀ i node,
        prev = PrevNode i →
        nodes !! i = Some node →
        lt node.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦
      ) →
      ∀ k,
      q = S k →
        ∃ pred,
        bottom !! k = Some pred ∧
        lt pred.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦.
    Proof.
      destruct prev as [| i]; simpl; first lia.
      intros (k' & node & Hnodes_lookup & Hbottom_lookup & ->) Hlt k [= <-].
      eauto.
    Qed.

    (* Updating an unmarked slot above level 0. *)
    #[local] Lemma inv۰pureｰset prev lvl link link' statuses' roots' :
      0 < lvl →
      prev۰slots nodes statuses roots prev !! lvl = Some (false, link) →
      link۰wf nodes lvl link' →
      prev۰update statuses roots prev lvl link' = (statuses', roots') →
      inv۰pure lt nodes statuses' bottom roots' m.
    Proof.
      intros Hlvl Hslots Hwf.
      destruct prev as [| i]; simpl in *.
      - intros [= <- <-].
        constructor; try apply Hinv.
        + intros lvl' link''.
          rewrite list_lookup_insert.
          case_decide as Hcase; last apply (inv۰pure۰roots Hinv).
          destruct Hcase as (<- & _).
          intros [= <-]. done.
        + rewrite list_lookup_insert_ne; first lia.
          apply (inv۰pure۰roots_head Hinv).
      - intros [= <- <-].
        destruct (nodes !! i) as [node |] eqn:Hnodes_lookup; last done.
        destruct (statuses !! i) as [status |] eqn:Hstatuses_lookup; last done.
        rewrite list_lookup_imap in Hslots.
        apply fmap_Some in Hslots as (link'' & Hlinks_lookup & _).
        constructor; try apply Hinv.
        + rewrite length_alter. apply Hinv.
        + intros j node' status'.
          destruct (decide (i = j)) as [<- | Hne].
          * rewrite list_lookup_alter_eq Hstatuses_lookup Hnodes_lookup.
            intros [= <-] [= <-].
            pose proof (inv۰pure۰status Hinv _ _ _ Hnodes_lookup Hstatuses_lookup) as (Hheight & Hlength & Hmarked & Hlinks).
            split_and!; simpl; try done.
            { rewrite length_insert //. }
            intros lvl' link'''.
            rewrite list_lookup_insert.
            case_decide as Hcase; last apply Hlinks.
            destruct Hcase as (<- & _).
            intros [= <-]. done.
          * rewrite list_lookup_alter_ne //.
            apply (inv۰pure۰status Hinv).
        + intros k node' j status'.
          destruct (decide (i = j)) as [<- | Hne].
          * rewrite list_lookup_alter_eq Hstatuses_lookup.
            intros Hbottom_lookup Hnodes_lookup' [= <-].
            rewrite /= list_lookup_insert_ne; first lia.
            eapply (inv۰pure۰bottom_links Hinv); done.
          * rewrite list_lookup_alter_ne //.
            apply (inv۰pure۰bottom_links Hinv).
        + intros j node' status'.
          destruct (decide (i = j)) as [<- | Hne].
          * rewrite list_lookup_alter_eq Hstatuses_lookup.
            intros Hnodes_lookup' [= <-].
            apply (inv۰pure۰unlinked Hinv _ _ _ Hnodes_lookup' Hstatuses_lookup).
          * rewrite list_lookup_alter_ne //.
            apply (inv۰pure۰unlinked Hinv).
        + intros 𝑘𝑒𝑦 v.
          rewrite (inv۰pure۰model Hinv).
          split.
          * intros (j & node' & status' & Hnodes_lookup' & Hstatuses_lookup' & Hmarked & Hkey & Hv).
            exists j, node'.
            destruct (decide (i = j)) as [<- | Hne].
            -- rewrite list_lookup_alter_eq Hstatuses_lookup' /=. naive.
            -- rewrite list_lookup_alter_ne //. naive.
          * intros (j & node' & status' & Hnodes_lookup' & Hstatuses_lookup' & Hmarked & Hkey & Hv).
            exists j, node'.
            destruct (decide (i = j)) as [<- | Hne].
            -- rewrite list_lookup_alter_eq Hstatuses_lookup in Hstatuses_lookup'.
               injection Hstatuses_lookup' as <-. naive.
            -- rewrite list_lookup_alter_ne // in Hstatuses_lookup'. naive.
    Qed.

    #[local] Lemma inv۰pureｰbottom_wf k :
      link۰wf nodes 0 (bottom !! k).
    Proof.
      destruct (bottom !! k) as [node |] eqn:Hlookup; last done.
      apply list_elem_of_lookup_2, (inv۰pure۰bottom Hinv) in Hlookup as Hnode.
      split; first done.
      apply list_elem_of_lookup in Hnode as (i & Hnodes_lookup).
      destruct (inv۰pureｰstatus_lookup i node) as (status & Hstatuses_lookup); first done.
      apply (inv۰pure۰status Hinv _ _ _ Hnodes_lookup Hstatuses_lookup).
    Qed.
    #[local] Lemma inv۰pureｰbottom_inj `{!StrictOrder lt} k1 k2 node :
      bottom !! k1 = Some node →
      bottom !! k2 = Some node →
      k1 = k2.
    Proof.
      intros Hlookup1 Hlookup2.
      eapply sortedｰinj; [apply (inv۰pure۰sorted Hinv) | done.. | done].
    Qed.
    #[local] Lemma inv۰pureｰbottom_delete q node node' :
      bottom !! q = Some node →
      node' ∈ bottom →
      node' ≠ node →
      node' ∈ delete q bottom.
    Proof.
      intros Hlookup (p & Hp)%list_elem_of_lookup Hne.
      destruct (Nat.lt_trichotomy p q) as [Hpq | [-> | Hpq]].
      - apply list_elem_of_lookup. exists p.
        rewrite list_lookup_delete_lt //.
      - congruence.
      - apply list_elem_of_lookup. exists (p - 1).
        rewrite list_lookup_delete_ge; first lia.
        rewrite (_ : S (p - 1) = p) //. lia.
    Qed.
  End inv۰pure.

  #[local] Lemma statusesｰalter_marked f i statuses :
    ( ∀ status,
      (f status).(status۰marked) = status.(status۰marked)
    ) →
    status۰marked <$> alter f i statuses = status۰marked <$> statuses.
  Proof.
    intros Hf.
    apply list_eq. intros j.
    rewrite !list_lookup_fmap list_lookup_alter.
    case_decide; subst; last done.
    destruct (statuses !! j); simpl; congruence.
  Qed.
  #[local] Lemma statusesｰmarked_lookup statuses1 statuses2 j status1 :
    status۰marked <$> statuses1 = status۰marked <$> statuses2 →
    statuses1 !! j = Some status1 →
      ∃ status2,
      statuses2 !! j = Some status2 ∧
      status2.(status۰marked) = status1.(status۰marked).
  Proof.
    intros Heq Hlookup1.
    assert ((status۰marked <$> statuses2) !! j = Some status1.(status۰marked)) as Hlookup2.
    { rewrite -Heq list_lookup_fmap Hlookup1 //. }
    rewrite list_lookup_fmap in Hlookup2.
    apply fmap_Some in Hlookup2 as (status2 & ? & ?). naive.
  Qed.

  (* Changing the links of the statuses without changing their marks, the
     model is preserved. *)
  #[local] Lemma inv۰pureｰmodel_marked nodes statuses1 statuses2 m :
    status۰marked <$> statuses1 = status۰marked <$> statuses2 →
    ( ∀ 𝑘𝑒𝑦 v,
      m !! 𝑘𝑒𝑦 = Some v ↔
        ∃ i node status,
        nodes !! i = Some node ∧
        statuses1 !! i = Some status ∧
        status.(status۰marked) < node.(node۰height) ∧
        node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦 ∧
        node.(node۰value) = v
    ) →
    ∀ 𝑘𝑒𝑦 v,
    m !! 𝑘𝑒𝑦 = Some v ↔
      ∃ i node status,
      nodes !! i = Some node ∧
      statuses2 !! i = Some status ∧
      status.(status۰marked) < node.(node۰height) ∧
      node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦 ∧
      node.(node۰value) = v.
  Proof.
    intros Heq Hm 𝑘𝑒𝑦 v.
    rewrite Hm.
    split.
    - intros (i & node & status1 & Hnodes_lookup & Hstatuses1_lookup & Hmarked & Hkey & Hv).
      destruct (statusesｰmarked_lookup statuses1 statuses2 i status1) as (status2 & ? & ?); [done.. |].
      exists i, node, status2. split_and!; try done. lia.
    - intros (i & node & status2 & Hnodes_lookup & Hstatuses2_lookup & Hmarked & Hkey & Hv).
      destruct (statusesｰmarked_lookup statuses2 statuses1 i status2) as (status1 & ? & ?); [done.. |].
      exists i, node, status1. split_and!; try done. lia.
  Qed.

  #[local] Lemma prev۰updateｰmarked statuses roots prev lvl link statuses' roots' :
    prev۰update statuses roots prev lvl link = (statuses', roots') →
    status۰marked <$> statuses' = status۰marked <$> statuses.
  Proof.
    destruct prev; intros [= <- <-]; first done.
    apply statusesｰalter_marked. done.
  Qed.

  Section inv۰pure.
    Context {nodes statuses bottom roots m}.
    Context (Hinv : inv۰pure lt nodes statuses bottom roots m).

    #[local] Lemma inv۰pureｰprev_slot prev lvl marked link :
      prev۰slots nodes statuses roots prev !! lvl = Some (marked, link) →
      link۰wf nodes lvl link.
    Proof.
      destruct prev as [| i]; simpl.
      - rewrite list_lookup_fmap.
        intros (link' & Hlookup & [= -> ->])%fmap_Some.
        eapply (inv۰pure۰roots Hinv). done.
      - destruct (nodes !! i) as [node |] eqn:Hnodes_lookup; last done.
        destruct (statuses !! i) as [status |] eqn:Hstatuses_lookup; last done.
        rewrite list_lookup_imap.
        intros (link' & Hlinks_lookup & [= -> ->])%fmap_Some.
        pose proof (inv۰pure۰status Hinv _ _ _ Hnodes_lookup Hstatuses_lookup) as (_ & _ & _ & Hlinks).
        eauto.
    Qed.

    (* Unlinking at level 0 the marked node following [prev]. *)
    #[local] Lemma inv۰pureｰunlink0 `{!StrictOrder lt} prev q node i status statuses' roots' :
      prev۰position nodes bottom prev q →
      bottom !! q = Some node →
      nodes !! i = Some node →
      statuses !! i = Some status →
      status.(status۰marked) = node.(node۰height) →
      prev۰update statuses roots prev 0 (bottom !! S q) = (statuses', roots') →
      inv۰pure lt nodes statuses' (delete q bottom) roots' m.
    Proof.
      intros Hprev Hbottom_lookup Hnodes_lookup Hstatuses_lookup Hmarked Hupdate.
      pose proof (inv۰pure۰sorted Hinv) as Hsorted.
      assert (
        ∀ j node' status',
        nodes !! j = Some node' →
        statuses !! j = Some status' →
        status'.(status۰marked) < node'.(node۰height) →
        node' ∈ delete q bottom
      ) as Hunlinked.
      { intros j node' status' Hnodes_lookup' Hstatuses_lookup' Hmarked'.
        eapply (inv۰pureｰbottom_delete Hinv); [done | | ].
        - eapply (inv۰pure۰unlinked Hinv); done.
        - intros ->.
          pose proof (inv۰pureｰindex_inj Hinv _ _ _ Hnodes_lookup Hnodes_lookup') as <-.
          assert (status' = status) as -> by congruence.
          lia.
      }
      destruct prev as [| i']; simpl in Hprev, Hupdate; injection Hupdate as <- <-.
      - subst q.
        constructor; try apply Hinv.
        + intros lvl link.
          rewrite list_lookup_insert.
          case_decide as Hcase.
          * destruct Hcase as (<- & _).
            intros [= <-]. apply (inv۰pureｰbottom_wf Hinv).
          * apply (inv۰pure۰roots Hinv).
        + rewrite list_lookup_insert decide_True.
          { split; first done.
            eapply lookup_lt_Some, (inv۰pure۰roots_head Hinv).
          }
          rewrite head_lookup list_lookup_delete_ge //.
        + intros node' ?%list_elem_of_delete_inv.
          apply (inv۰pure۰bottom Hinv). done.
        + intros k node' j status' Hlookup.
          rewrite list_lookup_delete_ge in Hlookup; first lia.
          rewrite list_lookup_delete_ge; first lia.
          apply (inv۰pure۰bottom_links Hinv _ _ _ _ Hlookup).
        + apply sortedｰdelete. done.
        + apply Hunlinked.
      - destruct Hprev as (k & pred & Hnodes_lookup' & Hbottom_lookup' & ->).
        constructor.
        + rewrite length_alter. apply Hinv.
        + apply Hinv.
        + intros j node' status'.
          destruct (decide (i' = j)) as [<- | Hne].
          * rewrite list_lookup_alter_eq.
            intros Hnodes_lookup'' (status'' & Hstatuses_lookup'' & ->)%fmap_Some.
            pose proof (inv۰pure۰status Hinv _ _ _ Hnodes_lookup'' Hstatuses_lookup'') as (Hheight & Hlength & Hmarked'' & Hlinks).
            split_and!; simpl; try done.
            { rewrite length_insert //. }
            intros lvl link.
            rewrite list_lookup_insert.
            case_decide as Hcase; last apply Hlinks.
            destruct Hcase as (<- & _).
            intros [= <-]. apply (inv۰pureｰbottom_wf Hinv).
          * rewrite list_lookup_alter_ne //.
            apply (inv۰pure۰status Hinv).
        + apply Hinv.
        + rewrite (inv۰pure۰roots_head Hinv) !head_lookup list_lookup_delete_lt //. lia.
        + intros node' ?%list_elem_of_delete_inv.
          apply (inv۰pure۰bottom Hinv). done.
        + intros k' node' j status' Hlookup Hnodes_lookup''.
          destruct (decide (i' = j)) as [<- | Hne].
          * rewrite list_lookup_alter_eq.
            intros (status'' & Hstatuses_lookup'' & ->)%fmap_Some.
            assert (node' = pred) as -> by congruence.
            rewrite list_lookup_delete in Hlookup.
            assert (k' = k) as ->.
            { case_decide.
              - eapply (inv۰pureｰbottom_inj Hinv); done.
              - opose proof* (inv۰pureｰbottom_inj Hinv (S k') k) as ?; [done.. | lia].
            }
            rewrite /= list_lookup_insert decide_True.
            { pose proof (inv۰pure۰status Hinv _ _ _ Hnodes_lookup'' Hstatuses_lookup'') as (? & -> & _). lia. }
            rewrite list_lookup_delete_ge //.
          * rewrite list_lookup_alter_ne //.
            intros Hstatuses_lookup''.
            rewrite list_lookup_delete in Hlookup.
            case_decide.
            -- rewrite (inv۰pure۰bottom_links Hinv _ _ _ _ Hlookup Hnodes_lookup'' Hstatuses_lookup'').
               rewrite list_lookup_delete.
               case_decide; first done.
               exfalso.
               assert (k' = k) as -> by lia.
               assert (node' = pred) as -> by congruence.
               pose proof (inv۰pureｰindex_inj Hinv _ _ _ Hnodes_lookup' Hnodes_lookup''). done.
            -- rewrite (inv۰pure۰bottom_links Hinv _ _ _ _ Hlookup Hnodes_lookup'' Hstatuses_lookup'').
               rewrite list_lookup_delete_ge //. lia.
        + apply sortedｰdelete. done.
        + intros j node' status' Hnodes_lookup''.
          destruct (decide (i' = j)) as [<- | Hne].
          * rewrite list_lookup_alter_eq.
            intros (status'' & Hstatuses_lookup'' & ->)%fmap_Some.
            apply (Hunlinked i' node' status''); done.
          * rewrite list_lookup_alter_ne //.
            apply Hunlinked. done.
        + apply inv۰pureｰmodel_marked with statuses.
          * symmetry. apply statusesｰalter_marked. done.
          * apply Hinv.
    Qed.

    #[local] Lemma inv۰pureｰprev_position_le prev q :
      prev۰position nodes bottom prev q →
      q ≤ length bottom.
    Proof.
      destruct prev as [| i]; simpl.
      - lia.
      - intros (k & node & _ & Hlookup & ->).
        apply lookup_lt_Some in Hlookup. lia.
    Qed.

    (* Inserting at level 0 a new node after [prev]. *)
    #[local] Lemma inv۰pureｰinsert0 `{!StrictOrder lt} prev q node status statuses' roots' :
      prev۰position nodes bottom prev q →
      ( ∀ k pred,
        q = S k →
        bottom !! k = Some pred →
        lt pred.(node۰𝑘𝑒𝑦) node.(node۰𝑘𝑒𝑦)
      ) →
      ( ∀ succ,
        bottom !! q = Some succ →
        lt node.(node۰𝑘𝑒𝑦) succ.(node۰𝑘𝑒𝑦)
      ) →
      node.(node۰nexts) ∉ node۰nexts <$> nodes →
      status۰wf nodes node status →
      status.(status۰marked) = 0 →
      status.(status۰links) !! 0 = Some (bottom !! q) →
      prev۰update statuses roots prev 0 (Some node) = (statuses', roots') →
        m !! node.(node۰𝑘𝑒𝑦) = None ∧
        inv۰pure lt
          (nodes ++ [node])
          (statuses' ++ [status])
          (take q bottom ++ node :: drop q bottom)
          roots'
          (<[node.(node۰𝑘𝑒𝑦) := node.(node۰value)]> m).
    Proof.
      intros Hprev Hpred Hsucc Hnexts (Hheight & Hlength & _ & Hlinks) Hmarked Hlink Hupdate.
      pose proof (inv۰pure۰sorted Hinv) as Hsorted.
      pose proof (inv۰pureｰprev_position_le prev q Hprev) as Hq.
      assert (node ∉ nodes) as Hnode.
      { intros Hnode. apply Hnexts, list_elem_of_fmap. eexists. split; done. }
      assert (∀ lvl link, link۰wf nodes lvl link → link۰wf (nodes ++ [node]) lvl link) as Hwf_mono.
      { intros lvl [node' |]; last done.
        rewrite /= elem_of_app.
        intros (? & ?). split; [left |]; done.
      }
      assert (∀ node' status', status۰wf nodes node' status' → status۰wf (nodes ++ [node]) node' status') as Hstatus_mono.
      { intros node' status' (? & ? & ? & Hlinks').
        split_and!; try done.
        intros lvl link Hlink'. apply Hwf_mono. eauto.
      }
      assert (m !! node.(node۰𝑘𝑒𝑦) = None) as Hm.
      { destruct (m !! node.(node۰𝑘𝑒𝑦)) as [v |] eqn:Hlookup; last done.
        exfalso.
        opose proof* (inv۰pureｰlocate Hinv node.(node۰𝑘𝑒𝑦) v q) as (succ & Hsucc_lookup & Hsucc'); [| done |].
        { intros k ->.
          destruct prev as [| i]; simpl in Hprev; first lia.
          destruct Hprev as (k' & pred & _ & Hpred_lookup & [= <-]).
          eauto.
        }
        specialize (Hsucc succ Hsucc_lookup).
        apply (irreflexivity lt node.(node۰𝑘𝑒𝑦)).
        destruct Hsucc' as [Hsucc' | Hsucc'].
        - rewrite -{2}Hsucc'. done.
        - trans succ.(node۰𝑘𝑒𝑦); done.
      }
      split; first done.
      assert (length statuses' = length nodes) as Hstatuses'_length.
      { destruct prev; injection Hupdate as <- <-; rewrite ?length_alter; apply Hinv. }
      assert (status۰marked <$> statuses' = status۰marked <$> statuses) as Hstatuses'_marked.
      { destruct prev; injection Hupdate as <- <-; first done.
        apply statusesｰalter_marked. done.
      }
      assert (
        ∀ j node' status',
        nodes !! j = Some node' →
        statuses' !! j = Some status' →
          ∃ status'',
          statuses !! j = Some status'' ∧
          status'.(status۰marked) = status''.(status۰marked) ∧
          status۰wf (nodes ++ [node]) node' status' ∧
          ( prev ≠ PrevNode j ∧
            status'.(status۰links) !! 0 = status''.(status۰links) !! 0
          ∨ prev = PrevNode j ∧
            status'.(status۰links) !! 0 = Some (Some node)
          )
      ) as Hstatuses'_lookup.
      { intros j node' status' Hnodes_lookup' Hstatuses'_lookup.
        destruct prev as [| i]; injection Hupdate as <- <-.
        - exists status'. split_and!; [done | done | | left; done].
          apply Hstatus_mono. eapply (inv۰pure۰status Hinv); done.
        - destruct (decide (i = j)) as [<- | Hne].
          + rewrite list_lookup_alter_eq in Hstatuses'_lookup.
            apply fmap_Some in Hstatuses'_lookup as (status'' & Hstatuses_lookup & ->).
            pose proof (inv۰pure۰status Hinv _ _ _ Hnodes_lookup' Hstatuses_lookup) as (Hheight' & Hlength' & Hmarked' & Hlinks').
            exists status''. split_and!; try done.
            * split_and!; simpl; try done.
              { rewrite length_insert //. }
              intros lvl link.
              rewrite list_lookup_insert.
              case_decide as Hcase.
              -- destruct Hcase as (<- & _).
                 intros [= <-]. rewrite /= elem_of_app list_elem_of_singleton.
                 split; [right | lia]; done.
              -- intros. apply Hwf_mono. eauto.
            * right. split; first done.
              rewrite /= list_lookup_insert decide_True //. lia.
          + rewrite list_lookup_alter_ne // in Hstatuses'_lookup.
            exists status'. split_and!; try done.
            * apply Hstatus_mono. eapply (inv۰pure۰status Hinv); done.
            * left. split; last done. congruence.
      }
      assert (
        ∀ j node',
        (nodes ++ [node]) !! j = Some node' →
          j < length nodes ∧
          nodes !! j = Some node'
        ∨ j = length nodes ∧
          node' = node
      ) as Hnodes'_lookup.
      { intros j node' [(? & ?) | (? & ?)]%lookup_snoc_Some; [left | right]; done. }
      assert (
        ∀ j status',
        j < length nodes →
        (statuses' ++ [status]) !! j = Some status' →
        statuses' !! j = Some status'
      ) as Hstatuses''_lookup.
      { intros j status' Hj. rewrite lookup_app_l //. lia. }
      assert (
        ∀ k' node',
        (take q bottom ++ node :: drop q bottom) !! k' = Some node' →
          k' = q ∧
          node' = node
        ∨ node' ≠ node ∧
          k' ≠ q ∧
          bottom !! (if decide (k' < q) then k' else k' - 1) = Some node'
      ) as Hbottom'_lookup_inv.
      { intros k' node' Hlookup.
        rewrite lookupｰinsert_at // in Hlookup.
        repeat case_decide; simplify_eq.
        - right. split_and!; try done; try lia.
          intros ->. apply Hnode, (inv۰pure۰bottom Hinv), list_elem_of_lookup_2 with k'. done.
        - left. split; done.
        - right. split_and!; try done; try lia.
          intros ->. apply Hnode, (inv۰pure۰bottom Hinv), list_elem_of_lookup_2 with (k' - 1). done.
      }
      constructor.
      - rewrite !length_app /=. lia.
      - rewrite fmap_app NoDup_app. split_and!.
        + apply Hinv.
        + set_solver.
        + apply NoDup_singleton.
      - intros j node' status' [(Hj & Hnodes_lookup') | (-> & ->)]%Hnodes'_lookup.
        + intros Hstatuses_lookup'%Hstatuses''_lookup; last done.
          destruct (Hstatuses'_lookup _ _ _ Hnodes_lookup' Hstatuses_lookup') as (status'' & _ & _ & ? & _).
          done.
        + rewrite lookup_app_r; first lia.
          rewrite Hstatuses'_length Nat.sub_diag.
          intros [= <-].
          apply Hstatus_mono. split_and!; [done | done | lia | done].
      - destruct prev as [| i]; injection Hupdate as <- <-.
        + intros lvl link.
          rewrite list_lookup_insert.
          case_decide as Hcase.
          * destruct Hcase as (<- & _).
            intros [= <-]. rewrite /= elem_of_app list_elem_of_singleton.
            split; [right | lia]; done.
          * intros. apply Hwf_mono. eapply (inv۰pure۰roots Hinv). done.
        + intros. apply Hwf_mono. eapply (inv۰pure۰roots Hinv). done.
      - destruct prev as [| i]; injection Hupdate as <- <-; simpl in Hprev.
        + subst q.
          rewrite list_lookup_insert decide_True //.
          split; first done.
          eapply lookup_lt_Some, (inv۰pure۰roots_head Hinv).
        + destruct Hprev as (k & pred & _ & Hpred_lookup & ->).
          rewrite (inv۰pure۰roots_head Hinv) !head_lookup lookupｰinsert_at //.
      - intros node' (k' & Hlookup)%list_elem_of_lookup.
        rewrite elem_of_app list_elem_of_singleton.
        apply Hbottom'_lookup_inv in Hlookup as [(_ & ->) | (_ & _ & Hlookup)].
        + right. done.
        + left. eapply (inv۰pure۰bottom Hinv), list_elem_of_lookup_2. done.
      - intros k' node' j status' Hbottom'_lookup Hnodes'_lookup'.
        apply Hbottom'_lookup_inv in Hbottom'_lookup as [(-> & ->) | (Hne & Hk' & Hbottom_lookup)].
        + apply Hnodes'_lookup in Hnodes'_lookup' as [(_ & Hnodes_lookup') | (-> & _)].
          { exfalso. apply Hnode. eapply list_elem_of_lookup_2. done. }
          rewrite lookup_app_r; first lia.
          rewrite Hstatuses'_length Nat.sub_diag.
          intros [= <-].
          rewrite Hlink lookupｰinsert_at // decide_False; first lia.
          rewrite decide_False; first lia.
          rewrite (_ : S q - 1 = q) //. lia.
        + apply Hnodes'_lookup in Hnodes'_lookup' as [(Hj & Hnodes_lookup') | (_ & ->)]; last done.
          intros Hstatuses_lookup'%Hstatuses''_lookup; last done.
          destruct (Hstatuses'_lookup _ _ _ Hnodes_lookup' Hstatuses_lookup') as (status'' & Hstatuses_lookup & _ & _ & [(Hprev' & Hlink') | (-> & Hlink')]).
          * destruct (decide (k' < q)) as [Hk'q | Hk'q].
            -- simpl in Hbottom_lookup.
               rewrite Hlink' (inv۰pure۰bottom_links Hinv _ _ _ _ Hbottom_lookup Hnodes_lookup' Hstatuses_lookup).
               rewrite lookupｰinsert_at //.
               destruct (decide (S k' < q)); first done.
               exfalso.
               destruct prev as [| i]; simpl in Hprev; first lia.
               destruct Hprev as (k & pred & Hpred_lookup & Hpred_lookup' & ->).
               assert (k = k') as -> by lia.
               assert (pred = node') as -> by congruence.
               pose proof (inv۰pureｰindex_inj Hinv _ _ _ Hpred_lookup Hnodes_lookup') as ->.
               done.
            -- simpl in Hbottom_lookup.
               rewrite Hlink' (inv۰pure۰bottom_links Hinv _ _ _ _ Hbottom_lookup Hnodes_lookup' Hstatuses_lookup).
               rewrite lookupｰinsert_at // decide_False; first lia.
               rewrite decide_False; first lia.
               rewrite (_ : S (k' - 1) = S k' - 1) //. lia.
          * rewrite Hlink'.
            destruct Hprev as (k & pred & Hpred_lookup & Hpred_lookup' & ->).
            assert (pred = node') as -> by congruence.
            destruct (decide (k' < S k)) as [Hk'q | Hk'q].
            -- simpl in Hbottom_lookup.
               assert (k = k') as <- by (eapply (inv۰pureｰbottom_inj Hinv); done).
               rewrite lookupｰinsert_at // decide_False; first lia.
               rewrite decide_True //.
            -- simpl in Hbottom_lookup.
               assert (k = k' - 1) as Hk by (eapply (inv۰pureｰbottom_inj Hinv); done).
               lia.
      - intros k' node1 node2 Hlookup1 Hlookup2.
        rewrite !lookupｰinsert_at // in Hlookup1 Hlookup2.
        repeat case_decide; simplify_eq; try lia.
        + eapply Hsorted; done.
        + eapply Hpred; done.
        + eapply Hsucc. rewrite (_ : q = S q - 1) //. lia.
        + rewrite (_ : S k' - 1 = S (k' - 1)) in Hlookup2; first lia.
          eapply Hsorted; done.
      - intros j node' status' [(Hj & Hnodes_lookup') | (-> & ->)]%Hnodes'_lookup.
        + intros Hstatuses_lookup'%Hstatuses''_lookup; last done.
          destruct (Hstatuses'_lookup _ _ _ Hnodes_lookup' Hstatuses_lookup') as (status'' & Hstatuses_lookup & -> & _).
          intros Hmarked'.
          pose proof (inv۰pure۰unlinked Hinv _ _ _ Hnodes_lookup' Hstatuses_lookup Hmarked') as Hnode'.
          rewrite -(take_drop q bottom) elem_of_app in Hnode'.
          rewrite elem_of_app elem_of_cons.
          destruct Hnode'; [left | right; right]; done.
        + intros. rewrite elem_of_app elem_of_cons. right. left. done.
      - intros 𝑘𝑒𝑦 v.
        rewrite lookup_insert_Some.
        split.
        + intros [(<- & <-) | (Hne & (j & node' & status'' & Hnodes_lookup' & Hstatuses_lookup & Hmarked' & Hkey & Hv)%(inv۰pure۰model Hinv))].
          * exists (length nodes), node, status.
            rewrite lookup_app_r // Nat.sub_diag.
            rewrite lookup_app_r; first lia.
            rewrite Hstatuses'_length Nat.sub_diag.
            split_and!; try done. lia.
          * destruct (statusesｰmarked_lookup statuses statuses' j status'') as (status' & Hstatuses'_lookup' & Hmarked''); [done.. |].
            exists j, node', status'.
            split_and!.
            -- apply lookup_app_l_Some. done.
            -- apply lookup_app_l_Some. done.
            -- lia.
            -- done.
            -- done.
        + intros (j & node' & status' & [(Hj & Hnodes_lookup') | (-> & ->)]%Hnodes'_lookup & Hstatuses_lookup' & Hmarked' & Hkey & Hv).
          * apply Hstatuses''_lookup in Hstatuses_lookup'; last done.
            destruct (Hstatuses'_lookup _ _ _ Hnodes_lookup' Hstatuses_lookup') as (status'' & Hstatuses_lookup & Hmarked'' & _).
            right.
            assert (m !! 𝑘𝑒𝑦 = Some v) as Hlookup.
            { apply (inv۰pure۰model Hinv). exists j, node', status''. split_and!; try done. lia. }
            split; last done.
            intros Heq. rewrite -Heq in Hlookup. congruence.
          * left. split; done.
    Qed.

    (* Marking level [lvl] of an inserted node. *)
    #[local] Lemma inv۰pureｰmark `{!StrictOrder lt} i node status lvl :
      nodes !! i = Some node →
      statuses !! i = Some status →
      lvl < node.(node۰height) →
      status.(status۰marked) = node.(node۰height) - S lvl →
      inv۰pure lt
        nodes
        (<[i := Status status.(status۰links) (S status.(status۰marked))]> statuses)
        bottom
        roots
        (if decide (lvl = 0) then delete node.(node۰𝑘𝑒𝑦) m else m).
    Proof.
      intros Hnodes_lookup Hstatuses_lookup Hlvl Hmarked.
      pose proof (inv۰pure۰status Hinv _ _ _ Hnodes_lookup Hstatuses_lookup) as (Hheight & Hlength & _ & Hlinks).
      assert (
        ∀ j status',
        <[i := Status status.(status۰links) (S status.(status۰marked))]> statuses !! j = Some status' →
          i = j ∧
          status' = Status status.(status۰links) (S status.(status۰marked))
        ∨ i ≠ j ∧
          statuses !! j = Some status'
      ) as Hstatuses'_lookup.
      { intros j status'.
        rewrite list_lookup_insert.
        case_decide as Hcase.
        - destruct Hcase as (<- & _). intros [= <-]. left. done.
        - intros Hstatuses_lookup'. right. split; last done.
          intros <-. apply Hcase. split; first done.
          eapply lookup_lt_Some. done.
      }
      constructor; try apply Hinv.
      - rewrite length_insert. apply Hinv.
      - intros j node' status' Hnodes_lookup' [(<- & ->) | (_ & Hstatuses_lookup')]%Hstatuses'_lookup.
        + assert (node' = node) as -> by congruence.
          split_and!; simpl; try done. lia.
        + eapply (inv۰pure۰status Hinv); done.
      - intros k node' j status' Hbottom_lookup Hnodes_lookup' [(<- & ->) | (_ & Hstatuses_lookup')]%Hstatuses'_lookup.
        + simpl. eapply (inv۰pure۰bottom_links Hinv _ _ i status); done.
        + eapply (inv۰pure۰bottom_links Hinv); done.
      - intros j node' status' Hnodes_lookup' [(<- & ->) | (_ & Hstatuses_lookup')]%Hstatuses'_lookup.
        + assert (node' = node) as -> by congruence.
          simpl. intros. eapply (inv۰pure۰unlinked Hinv); [done.. | lia].
        + eapply (inv۰pure۰unlinked Hinv); done.
      - intros 𝑘𝑒𝑦 v.
        case_decide as Hlvl0.
        + subst lvl.
          rewrite lookup_delete_Some (inv۰pure۰model Hinv).
          split.
          * intros (Hne & j & node' & status' & Hnodes_lookup' & Hstatuses_lookup' & Hmarked' & Hkey & Hv).
            exists j, node', status'.
            rewrite list_lookup_insert_ne; last done.
            intros <-. apply Hne. congruence.
          * intros (j & node' & status' & Hnodes_lookup' & [(<- & ->) | (Hne & Hstatuses_lookup')]%Hstatuses'_lookup & Hmarked' & Hkey & Hv).
            { exfalso. assert (node' = node) as -> by congruence. simpl in Hmarked'. lia. }
            split.
            -- intros Heq.
               apply Hne.
               opose proof* (inv۰pure۰unlinked Hinv i) as (k1 & Hk1)%list_elem_of_lookup; [done.. | lia |].
               opose proof* (inv۰pure۰unlinked Hinv j) as (k2 & Hk2)%list_elem_of_lookup; [done.. |].
               assert (k1 = k2) as <-.
               { eapply sortedｰinj; [apply (inv۰pure۰sorted Hinv) | done.. | congruence]. }
               assert (node' = node) as -> by congruence.
               eapply (inv۰pureｰindex_inj Hinv); done.
            -- naive.
        + rewrite (inv۰pure۰model Hinv).
          split.
          * intros (j & node' & status' & Hnodes_lookup' & Hstatuses_lookup' & Hmarked' & Hkey & Hv).
            destruct (decide (i = j)) as [<- | Hne].
            -- assert (node' = node) as -> by congruence.
               exists i, node, (Status status.(status۰links) (S status.(status۰marked))).
               rewrite list_lookup_insert decide_True.
               { split; first done. eapply lookup_lt_Some. done. }
               split_and!; simpl; try done. lia.
            -- exists j, node', status'.
               rewrite list_lookup_insert_ne //.
          * intros (j & node' & status' & Hnodes_lookup' & [(<- & ->) | (Hne & Hstatuses_lookup')]%Hstatuses'_lookup & Hmarked' & Hkey & Hv).
            -- assert (node' = node) as -> by congruence.
               exists i, node, status.
               split_and!; try done. lia.
            -- exists j, node', status'. done.
    Qed.
  End inv۰pure.

  #[local] Lemma inv۰pureｰcreate sz :
    0 < sz →
    inv۰pure lt [] [] [] (replicate sz None) ∅.
  Proof.
    intros Hsz.
    constructor; try done.
    - apply NoDup_nil_2.
    - intros lvl link (-> & _)%lookup_replicate. done.
    - rewrite lookup_replicate_2 //.
    - intros 𝑘𝑒𝑦 v. rewrite lookup_empty. split.
      + intros [=].
      + intros (i & node & status & Hlookup & _). done.
  Qed.

  #[local] Lemma waiter۰doneｰapp nodes statuses node status waiter :
    length statuses = length nodes →
    status.(status۰marked) ≠ node.(node۰height) →
    waiter۰done (nodes ++ [node]) (statuses ++ [status]) waiter = waiter۰done nodes statuses waiter.
  Proof.
    intros Hlength Hmarked.
    rewrite /waiter۰done zip_with_app // existsb_app /=.
    rewrite bool_decide_eq_false_2.
    { intros (_ & _ & ?). done. }
    destruct (existsb _ _); done.
  Qed.

  #[local] Lemma waiter۰doneｰmarked nodes statuses1 statuses2 waiter :
    status۰marked <$> statuses1 = status۰marked <$> statuses2 →
    waiter۰done nodes statuses1 waiter = waiter۰done nodes statuses2 waiter.
  Proof.
    revert statuses1 statuses2.
    induction nodes as [| node nodes IH]; intros [| status1 statuses1] [| status2 statuses2] Heq; try done.
    injection Heq as Hhead Htail.
    specialize (IH statuses1 statuses2 Htail).
    rewrite /waiter۰done /= in IH |- *.
    rewrite Hhead IH //.
  Qed.

  #[local] Lemma waiter۰doneｰspec nodes statuses waiter :
    length statuses = length nodes →
    waiter۰done nodes statuses waiter = true ↔
      ∃ i node status,
      nodes !! i = Some node ∧
      statuses !! i = Some status ∧
      node۰to_val node = waiter.(waiter۰target) ∧
      node.(node۰𝑘𝑒𝑦) = waiter.(waiter۰𝑘𝑒𝑦) ∧
      status.(status۰marked) = node.(node۰height).
  Proof.
    intros Hlength.
    rewrite /waiter۰done existsb_exists.
    split.
    - intros ((node, status) & Hin & Hb).
      apply list_elem_of_In, list_elem_of_lookup in Hin as (i & Hi).
      apply lookup_zip_with_Some in Hi as (node' & status' & [= <- <-] & Hnodes_lookup & Hstatuses_lookup).
      apply bool_decide_eq_true in Hb.
      exists i, node, status. naive.
    - intros (i & node & status & Hnodes_lookup & Hstatuses_lookup & H1 & H2 & H3).
      exists (node, status). split.
      + apply list_elem_of_In, list_elem_of_lookup. exists i.
        apply lookup_zip_with_Some. naive.
      + apply bool_decide_eq_true. naive.
  Qed.

  #[local] Lemma waiter۰doneｰmark_partial nodes statuses i node status marked waiter :
    length statuses = length nodes →
    nodes !! i = Some node →
    statuses !! i = Some status →
    status.(status۰marked) < node.(node۰height) →
    marked < node.(node۰height) →
    waiter۰done nodes (<[i := Status status.(status۰links) marked]> statuses) waiter = waiter۰done nodes statuses waiter.
  Proof.
    intros Hlength Hnodes_lookup Hstatuses_lookup Hmarked Hmarked'.
    apply Bool.eq_iff_eq_true.
    assert (length (<[i := Status status.(status۰links) marked]> statuses) = length nodes) as Hlength'.
    { rewrite length_insert //. }
    rewrite !waiter۰doneｰspec //.
    split.
    - intros (j & node' & status' & Hnodes_lookup' & Hstatuses_lookup' & Htarget & Hkey & Hmarked'').
      rewrite list_lookup_insert in Hstatuses_lookup'.
      case_decide as Hcase.
      + destruct Hcase as (<- & _).
        injection Hstatuses_lookup' as <-.
        assert (node' = node) as -> by congruence.
        simpl in Hmarked''. lia.
      + exists j, node', status'. done.
    - intros (j & node' & status' & Hnodes_lookup' & Hstatuses_lookup' & Htarget & Hkey & Hmarked'').
      exists j, node', status'. split_and!; try done.
      rewrite list_lookup_insert_ne //.
      intros <-.
      assert (node' = node) as -> by congruence.
      assert (status' = status) as -> by congruence.
      lia.
  Qed.

  #[local] Lemma waiter۰doneｰmark nodes statuses i node status waiter :
    length statuses = length nodes →
    nodes !! i = Some node →
    statuses !! i = Some status →
    status.(status۰marked) < node.(node۰height) →
      ( waiter۰done nodes (<[i := Status status.(status۰links) node.(node۰height)]> statuses) waiter = true →
          waiter۰done nodes statuses waiter = true
        ∨ waiter.(waiter۰target) = node۰to_val node ∧
          waiter.(waiter۰𝑘𝑒𝑦) = node.(node۰𝑘𝑒𝑦)
      ) ∧
      ( waiter۰done nodes statuses waiter = true →
        waiter۰done nodes (<[i := Status status.(status۰links) node.(node۰height)]> statuses) waiter = true
      ).
  Proof.
    intros Hlength Hnodes_lookup Hstatuses_lookup Hmarked.
    assert (length (<[i := Status status.(status۰links) node.(node۰height)]> statuses) = length nodes) as Hlength'.
    { rewrite length_insert //. }
    rewrite !waiter۰doneｰspec //.
    split.
    - intros (j & node' & status' & Hnodes_lookup' & Hstatuses_lookup' & Htarget & Hkey & Hmarked').
      rewrite list_lookup_insert in Hstatuses_lookup'.
      case_decide as Hcase.
      + destruct Hcase as (<- & _).
        right. split; congruence.
      + left. exists j, node', status'. done.
    - intros (j & node' & status' & Hnodes_lookup' & Hstatuses_lookup' & Htarget & Hkey & Hmarked').
      exists j, node', status'. split_and!; try done.
      rewrite list_lookup_insert_ne //.
      intros <-.
      assert (node' = node) as -> by congruence.
      assert (status' = status) as -> by congruence.
      lia.
  Qed.
End inv۰pure.

(* ------------------------------------------------------------------------ *)
(* Ghost state. *)

Record skiplist۰name :=
  { skiplist۰name۰compare : val
  ; skiplist۰name۰root : val
  ; skiplist۰name۰inv : namespace
  ; skiplist۰name۰model : gname
  ; skiplist۰name۰nodes : gname
  ; skiplist۰name۰waiters : gname
  }.
Implicit Type γ : skiplist۰name.

Please derive Inhabited for skiplist۰name.
Please derive EqDecision for skiplist۰name.
Please derive Countable for skiplist۰name.

Coercion skiplist۰name۰to_val γ : val :=
  ( γ.(skiplist۰name۰compare)
  , γ.(skiplist۰name۰root)
  ).
#[global] Instance skiplist۰nameｰto_val : ToVal skiplist۰name :=
  skiplist۰name۰to_val.

Zoo global Key `{Countable Key} :=
  { model : twins (leibnizO (gmap Key val))
  ; nodes : mono_list (node Key)
  ; marks : mono_list (option (node Key))
  ; waiters : ghost_map gname (waiter Key) : iris
  ; waiter۰post : saved_pred bool
  }.

(* A prophecy predicting the result of [find_node]. *)
#[local] Definition prophet_res :=
  {|prophet_typed₁۰type :=
      val
  ; prophet_typed₁۰of_val _ v :=
      Some $ Some v
  |}.

Section skiplist۰G.
  Context `{skiplist۰G : SkiplistG Σ Key}.
  Context (key۰model : val → Key → iProp Σ).
  Context `{key۰modelｰpersistent : !∀ key 𝑘𝑒𝑦, Persistent (key۰model key 𝑘𝑒𝑦)}.
  Context (lt : relation Key).

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type m : gmap Key val.
  Implicit Type node : node Key.
  Implicit Type nodes bottom : list (node Key).
  Implicit Type link : option (node Key).
  Implicit Type links roots : list (option (node Key)).
  Implicit Type status : status Key.
  Implicit Type statuses : list (status Key).
  Implicit Type waiter : waiter Key.
  Implicit Type waiters : gmap gname (waiter Key).
  Implicit Type η : gname.
  Implicit Type lvl : nat.
  Implicit Type prev : prev.
  Implicit Type Q : option val → iProp Σ.

  #[local] Definition model₁' (γ_model : gname) m :=
    twins۰twin₁ γ_model (DfracOwn 1) m.
  #[local] Definition model₁ γ :=
    model₁' γ.(skiplist۰name۰model).
  #[local] Definition model₂' (γ_model : gname) m :=
    twins۰twin₂ γ_model m.
  #[local] Definition model₂ γ :=
    model₂' γ.(skiplist۰name۰model).

  #[local] Definition nodes۰auth' (γ_nodes : gname) nodes :=
    mono_list۰auth γ_nodes (DfracOwn 1) nodes.
  #[local] Definition nodes۰auth γ :=
    nodes۰auth' γ.(skiplist۰name۰nodes).
  #[local] Definition nodes۰at γ i node :=
    mono_list۰at γ.(skiplist۰name۰nodes) i node.

  #[local] Definition marks۰auth node status :=
    mono_list۰auth node.(node۰marks) (DfracOwn 1) (status۰frozen node status).
  (* Level [lvl] of [node] is marked and its link is frozen to [link]. *)
  #[local] Definition marks۰at node lvl link :=
    mono_list۰at node.(node۰marks) (node.(node۰height) - S lvl) link.

  #[local] Definition waiters۰auth' (γ_waiters : gname) waiters :=
    ghost_map_auth γ_waiters (DfracOwn 1) waiters.
  #[local] Definition waiters۰auth γ :=
    waiters۰auth' γ.(skiplist۰name۰waiters).
  #[local] Definition waiters۰elem γ η waiter :=
    ghost_map_elem γ.(skiplist۰name۰waiters) η (DfracOwn 1) waiter.

  (* Persistent knowledge about an inserted node. *)
  #[local] Definition node۰at γ i node : iProp Σ :=
    nodes۰at γ i node ∗
    array۰inv node.(node۰nexts) node.(node۰height) ∗
    key۰model node.(node۰key) node.(node۰𝑘𝑒𝑦).
  #[local] Instance : CustomIpat "node۰at" :=
    " ( #Hnodes_at{_{}}
      & #Hnexts_inv{_{}}
      & #Hkey{_{}}
      )
    ".

  (* [link] is a valid link at level [lvl]. *)
  #[local] Definition link۰model γ lvl link : iProp Σ :=
    match link with
    | None =>
        True
    | Some node =>
        ∃ i,
        node۰at γ i node ∗
        ⌜lvl < node.(node۰height)⌝
    end.

  (* [prevs] is the array of successors of [prev]. *)
  #[local] Definition prev۰at γ prev prevs : iProp Σ :=
    match prev with
    | PrevRoot =>
        ⌜prevs = γ.(skiplist۰name۰root)⌝
    | PrevNode i =>
        ∃ node,
        nodes۰at γ i node ∗
        ⌜prevs = node.(node۰nexts)⌝
    end.

  (* [prevs] is the array of successors of [prev], which is either the root
     or a node whose key is smaller than [𝑘𝑒𝑦], and has a level [lvl]. *)
  #[local] Definition prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs : iProp Σ :=
    ∃ sz,
    array۰inv prevs sz ∗
    ⌜lvl < sz⌝ ∗
    match prev with
    | PrevRoot =>
        ⌜prevs = γ.(skiplist۰name۰root)⌝
    | PrevNode i =>
        ∃ node,
        node۰at γ i node ∗
        ⌜prevs = node.(node۰nexts)⌝ ∗
        ⌜lt node.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦⌝
    end.

  #[local] Definition nodes۰model nodes statuses : iProp Σ :=
    [∗ list] node; status ∈ nodes; statuses,
    array۰model node.(node۰nexts) (DfracOwn 1) (status۰vals node status) ∗
    marks۰auth node status.
  #[local] Definition nodes۰keys nodes : iProp Σ :=
    [∗ list] node ∈ nodes,
    key۰model node.(node۰key) node.(node۰𝑘𝑒𝑦).

  #[local] Definition waiter۰au γ 𝑘𝑒𝑦 (Ψ : bool → iProp Σ) : iProp Σ :=
    AU <{
      ∃∃ m,
      model₁ γ m
    }> @ ⊤ ∖ ↑γ.(skiplist۰name۰inv), ∅ <{
      model₁ γ (delete 𝑘𝑒𝑦 m)
    , COMM
      Ψ (bool_decide (𝑘𝑒𝑦 ∈ dom m))
    }>.
  #[local] Definition waiter۰model γ nodes statuses η waiter : iProp Σ :=
    ∃ Ψ,
    saved_pred η Ψ ∗
    if waiter۰done nodes statuses waiter then
      Ψ false
    else
      waiter۰au γ waiter.(waiter۰𝑘𝑒𝑦) Ψ.

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ nodes statuses bottom roots m waiters,
    model₂ γ m ∗
    nodes۰auth γ nodes ∗
    waiters۰auth γ waiters ∗
    array۰model γ.(skiplist۰name۰root) (DfracOwn 1) (link۰to_val <$> roots) ∗
    nodes۰model nodes statuses ∗
    nodes۰keys nodes ∗
    ⌜inv۰pure lt nodes statuses bottom roots m⌝ ∗
    ( [∗ map] η ↦ waiter ∈ waiters,
      waiter۰model γ nodes statuses η waiter
    ).

  #[local] Instance node۰atｰpersistent γ i node :
    Persistent (node۰at γ i node).
  Proof.
    apply _.
  Qed.
  #[local] Instance link۰modelｰpersistent γ lvl link :
    Persistent (link۰model γ lvl link).
  Proof.
    destruct link; apply _.
  Qed.
  #[local] Instance prev۰atｰpersistent γ prev prevs :
    Persistent (prev۰at γ prev prevs).
  Proof.
    destruct prev; apply _.
  Qed.
  #[local] Instance prevs۰modelｰpersistent γ 𝑘𝑒𝑦 lvl prev prevs :
    Persistent (prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs).
  Proof.
    destruct prev; apply _.
  Qed.
  #[local] Instance nodes۰keysｰpersistent nodes :
    Persistent (nodes۰keys nodes).
  Proof.
    apply _.
  Qed.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model ∅ ∗
      model₂' γ_model ∅.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ m1 m2 :
    model₁ γ m1 -∗
    model₁ γ m2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ m1 m2 :
    model₁ γ m1 -∗
    model₂ γ m2 -∗
    ⌜m1 = m2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (twinsｰagreeｰL with "Hmodel₁ Hmodel₂") as %?.
    iSteps.
  Qed.
  #[local] Lemma modelｰupdate {γ m1 m2} m :
    model₁ γ m1 -∗
    model₂ γ m2 ==∗
      model₁ γ m ∗
      model₂ γ m.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma nodesｰalloc :
    ⊢ |==>
      ∃ γ_nodes,
      nodes۰auth' γ_nodes [].
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma nodes۰atｰget {γ nodes} i node :
    nodes !! i = Some node →
    nodes۰auth γ nodes ⊢
    nodes۰at γ i node.
  Proof.
    apply mono_list۰atｰget.
  Qed.
  #[local] Lemma nodes۰atｰvalid γ nodes i node :
    nodes۰auth γ nodes -∗
    nodes۰at γ i node -∗
    ⌜nodes !! i = Some node⌝.
  Proof.
    apply mono_list۰atｰvalid.
  Qed.
  #[local] Lemma nodesｰupdate {γ nodes} node :
    nodes۰auth γ nodes ⊢ |==>
      nodes۰auth γ (nodes ++ [node]) ∗
      nodes۰at γ (length nodes) node.
  Proof.
    iIntros "Hauth".
    iMod (mono_listｰupdateｰsnoc node with "Hauth") as "Hauth".
    iDestruct (nodes۰atｰget (length nodes) node with "Hauth") as "#Hat".
    { rewrite lookup_snoc_Some. naive. }
    iSteps.
  Qed.

  #[local] Lemma marks۰atｰlookup node status lvl :
    length status.(status۰links) = node.(node۰height) →
    status.(status۰marked) ≤ node.(node۰height) →
    lvl < node.(node۰height) →
    status۰frozen node status !! (node.(node۰height) - S lvl) =
      if decide (node.(node۰height) - status.(status۰marked) ≤ lvl) then
        status.(status۰links) !! lvl
      else
        None.
  Proof.
    intros Hlength Hmarked Hlvl.
    rewrite /status۰frozen.
    case_decide.
    - rewrite reverse_lookup.
      { rewrite length_drop. lia. }
      rewrite lookup_drop length_drop.
      f_equal. lia.
    - apply lookup_ge_None.
      rewrite length_reverse length_drop. lia.
  Qed.
  #[local] Lemma marks۰atｰget node status lvl link :
    length status.(status۰links) = node.(node۰height) →
    status.(status۰marked) ≤ node.(node۰height) →
    status.(status۰links) !! lvl = Some link →
    node.(node۰height) - status.(status۰marked) ≤ lvl →
    marks۰auth node status ⊢
    marks۰at node lvl link.
  Proof.
    intros Hlength Hmarked Hlookup Hlvl.
    apply mono_list۰atｰget.
    assert (lvl < node.(node۰height)).
    { rewrite -Hlength. eapply lookup_lt_Some. done. }
    rewrite marks۰atｰlookup // decide_True //.
  Qed.
  #[local] Lemma marks۰atｰvalid node status lvl link :
    length status.(status۰links) = node.(node۰height) →
    status.(status۰marked) ≤ node.(node۰height) →
    lvl < node.(node۰height) →
    marks۰auth node status -∗
    marks۰at node lvl link -∗
      ⌜node.(node۰height) - status.(status۰marked) ≤ lvl⌝ ∗
      ⌜status.(status۰links) !! lvl = Some link⌝.
  Proof.
    iIntros "%Hlength %Hmarked %Hlvl Hauth Hat".
    iDestruct (mono_list۰atｰvalid with "Hauth Hat") as %Hlookup.
    rewrite marks۰atｰlookup // in Hlookup.
    case_decide; naive.
  Qed.
  #[local] Lemma marksｰupdate node status :
    length status.(status۰links) = node.(node۰height) →
    status.(status۰marked) < node.(node۰height) →
    marks۰auth node status ⊢ |==>
    marks۰auth node (Status status.(status۰links) (S status.(status۰marked))).
  Proof.
    iIntros "%Hlength %Hmarked Hauth".
    destruct (lookup_lt_is_Some_2 status.(status۰links) (node.(node۰height) - S status.(status۰marked))) as (link & Hlookup).
    { lia. }
    iMod (mono_listｰupdateｰsnoc link with "Hauth") as "Hauth".
    rewrite /marks۰auth /status۰frozen /=.
    rewrite (drop_S _ link (node.(node۰height) - S status.(status۰marked))) // reverse_cons.
    rewrite (_ : S (node.(node۰height) - S status.(status۰marked)) = node.(node۰height) - status.(status۰marked)) //. lia.
  Qed.

  #[local] Lemma waitersｰalloc :
    ⊢ |==>
      ∃ γ_waiters,
      waiters۰auth' γ_waiters ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma waiters۰elemｰvalid γ waiters η waiter :
    waiters۰auth γ waiters -∗
    waiters۰elem γ η waiter -∗
    ⌜waiters !! η = Some waiter⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma waitersｰinsert {γ waiters} η waiter :
    waiters !! η = None →
    waiters۰auth γ waiters ⊢ |==>
      waiters۰auth γ (<[η := waiter]> waiters) ∗
      waiters۰elem γ η waiter.
  Proof.
    iIntros "%Hlookup Hauth".
    iApply (ghost_map_insert with "Hauth"). done.
  Qed.
  #[local] Lemma waitersｰdelete γ waiters η waiter :
    waiters۰auth γ waiters -∗
    waiters۰elem γ η waiter ==∗
    waiters۰auth γ (delete η waiters).
  Proof.
    apply ghost_map_delete.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Accessing arrays of successors. *)

  #[local] Lemma imapｰinsert {A B} (f : nat → A → B) l i x :
    imap f (<[i := x]> l) = <[i := f i x]> (imap f l).
  Proof.
    apply list_eq. intros j.
    rewrite list_lookup_imap !list_lookup_insert length_imap list_lookup_imap.
    case_decide as Hcase; last done.
    destruct Hcase as (-> & _). done.
  Qed.

  #[local] Lemma node۰atｰget {γ nodes statuses bottom roots m} i node :
    inv۰pure lt nodes statuses bottom roots m →
    nodes !! i = Some node →
    nodes۰auth γ nodes -∗
    nodes۰model nodes statuses -∗
    ▷ nodes۰keys nodes -∗
      nodes۰auth γ nodes ∗
      nodes۰model nodes statuses ∗
      ▷ node۰at γ i node.
  Proof.
    iIntros "%Hinv %Hlookup Hnodes_auth Hnodes #Hnodes_keys".
    destruct (inv۰pureｰstatus_lookup lt Hinv i node) as (status & Hstatus); first done.
    pose proof (inv۰pure۰status Hinv _ _ _ Hlookup Hstatus) as (_ & Hlength & _).
    iDestruct (big_sepL2_lookup_acc with "Hnodes") as "((Hnexts & Hmarks) & Hnodes)"; [done.. |].
    iDestruct (array۰modelｰtoｰinv with "Hnexts") as "#Hnexts_inv".
    rewrite length_imap Hlength.
    iDestruct (nodes۰atｰget with "Hnodes_auth") as "#Hnodes_at"; first done.
    iFrame "Hnodes_auth".
    iSplitL. { iApply ("Hnodes" with "[$]"). }
    iNext. iFrame "#".
    iApply (big_sepL_lookup with "Hnodes_keys"). done.
  Qed.

  #[local] Lemma link۰modelｰget {γ nodes statuses bottom roots m} lvl link :
    inv۰pure lt nodes statuses bottom roots m →
    link۰wf nodes lvl link →
    nodes۰auth γ nodes -∗
    nodes۰model nodes statuses -∗
    ▷ nodes۰keys nodes -∗
      nodes۰auth γ nodes ∗
      nodes۰model nodes statuses ∗
      ▷ link۰model γ lvl link.
  Proof.
    iIntros "%Hinv %Hwf Hnodes_auth Hnodes #Hnodes_keys".
    destruct link as [node |]; last first.
    { iFrame. iModIntro. done. }
    destruct Hwf as ((i & Hlookup)%list_elem_of_lookup & Hlvl).
    iDestruct (node۰atｰget with "Hnodes_auth Hnodes Hnodes_keys") as "($ & $ & #Hnode_at)"; [done.. |].
    iNext. iExists i. iFrame "#". iPureIntro. done.
  Qed.

  #[local] Lemma nodes۰modelｰarray_inv {nodes statuses bottom roots m} node :
    inv۰pure lt nodes statuses bottom roots m →
    node ∈ nodes →
    nodes۰model nodes statuses ⊢
    array۰inv node.(node۰nexts) node.(node۰height).
  Proof.
    iIntros "%Hinv %Hnode Hnodes".
    apply list_elem_of_lookup in Hnode as (i & Hlookup).
    destruct (inv۰pureｰstatus_lookup lt Hinv i node) as (status & Hstatus); first done.
    pose proof (inv۰pure۰status Hinv _ _ _ Hlookup Hstatus) as (_ & Hlength & _).
    iDestruct (big_sepL2_lookup with "Hnodes") as "(Hnexts & _)"; [done.. |].
    iDestruct (array۰modelｰtoｰinv with "Hnexts") as "Hnexts_inv".
    rewrite length_imap Hlength //.
  Qed.

  (* Similar links are equal. *)
  #[local] Lemma link۰to_valｰsimilar {nodes statuses bottom roots m} lvl link node :
    inv۰pure lt nodes statuses bottom roots m →
    link۰wf nodes lvl link →
    node ∈ nodes →
    link۰to_val link ≈ node۰to_val node →
    array۰inv node.(node۰nexts) node.(node۰height) ⊢
    ⌜link = Some node⌝.
  Proof.
    iIntros "%Hinv %Hwf %Hnode %Hsimilar #Hnexts_inv".
    destruct link as [node' |]; last first.
    { exfalso. by eapply valｰsimilarｰblockｰempty₁. }
    destruct Hwf as (Hnode' & _).
    assert (node'.(node۰nexts) ≈ node.(node۰nexts)) as Hnexts.
    { cbn in Hsimilar. destruct Hsimilar as (_ & Hsimilar).
      rewrite /fmap /= in Hsimilar.
      destruct_and! Hsimilar. done.
    }
    iDestruct (array۰invｰsimilar _ _ node'.(node۰nexts) with "Hnexts_inv") as %Hnexts'; first done.
    rewrite (inv۰pureｰnexts_inj lt Hinv node' node) //.
  Qed.
  #[local] Lemma slot۰to_valｰsimilar {nodes statuses bottom roots m} lvl marked link node :
    inv۰pure lt nodes statuses bottom roots m →
    link۰wf nodes lvl link →
    node ∈ nodes →
    slot۰to_val marked link ≈ node۰to_val node →
    array۰inv node.(node۰nexts) node.(node۰height) ⊢
      ⌜marked = false⌝ ∗
      ⌜link = Some node⌝.
  Proof.
    iIntros "%Hinv %Hwf %Hnode %Hsimilar #Hnexts_inv".
    destruct marked.
    - exfalso.
      rewrite /node۰to_val in Hsimilar.
      destruct link; cbn in Hsimilar; destruct_and? Hsimilar; simplify_eq.
    - iDestruct (link۰to_valｰsimilar with "Hnexts_inv") as %->; done.
  Qed.

  (* A node unmarked at some level is in the model. *)
  #[local] Lemma inv۰pureｰlive {nodes statuses bottom roots m} i node status lvl :
    inv۰pure lt nodes statuses bottom roots m →
    nodes !! i = Some node →
    statuses !! i = Some status →
    status۰is_marked node status lvl = false →
    m !! node.(node۰𝑘𝑒𝑦) = Some node.(node۰value).
  Proof.
    rewrite /status۰is_marked bool_decide_eq_false.
    intros Hinv Hnodes_lookup Hstatuses_lookup Hlvl.
    apply (inv۰pure۰model Hinv).
    exists i, node, status. split_and!; try done. lia.
  Qed.

  #[local] Lemma prevs۰modelｰmono γ 𝑘𝑒𝑦 lvl1 lvl2 prev prevs :
    lvl2 ≤ lvl1 →
    prevs۰model γ 𝑘𝑒𝑦 lvl1 prev prevs ⊢
    prevs۰model γ 𝑘𝑒𝑦 lvl2 prev prevs.
  Proof.
    iIntros "%Hlvl (%sz & Hinv & %Hlvl1 & H)".
    iExists sz. iFrame. iPureIntro. lia.
  Qed.
  #[local] Lemma prevs۰modelｰprev_at γ 𝑘𝑒𝑦 lvl prev prevs :
    prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs ⊢
    prev۰at γ prev prevs.
  Proof.
    iIntros "(%sz & _ & _ & Hprev)".
    destruct prev as [| i]; first done.
    iDestruct "Hprev" as "(%node & (#Hnodes_at & _) & -> & _)".
    iExists node. iFrame "#". done.
  Qed.
  #[local] Lemma prevs۰modelｰlt γ 𝑘𝑒𝑦 lvl prev prevs nodes :
    nodes۰auth γ nodes -∗
    prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs -∗
    ⌜ ∀ i node,
      prev = PrevNode i →
      nodes !! i = Some node →
      lt node.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦
    ⌝.
  Proof.
    iIntros "Hnodes_auth (%sz & _ & _ & Hprev)".
    destruct prev as [| i].
    - iPureIntro. intros ? ? [=].
    - iDestruct "Hprev" as "(%node & (#Hnodes_at & _) & _ & %Hlt)".
      iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup.
      iPureIntro. intros ? node' [= <-] Hnodes_lookup'.
      assert (node' = node) as -> by congruence.
      done.
  Qed.

  #[local] Lemma statusｰset_vals node status lvl link :
    status۰is_marked node status lvl = false →
    status۰vals node (Status (<[lvl := link]> status.(status۰links)) status.(status۰marked)) =
    <[lvl := link۰to_val link]> (status۰vals node status).
  Proof.
    intros Hmarked.
    rewrite /status۰vals /= imapｰinsert.
    rewrite (_ : status۰is_marked node (Status (<[lvl := link]> status.(status۰links)) status.(status۰marked)) = status۰is_marked node status) //.
    rewrite Hmarked //.
  Qed.
  #[local] Lemma statusｰset_frozen node status lvl link :
    status۰is_marked node status lvl = false →
    status۰frozen node (Status (<[lvl := link]> status.(status۰links)) status.(status۰marked)) =
    status۰frozen node status.
  Proof.
    rewrite /status۰is_marked /status۰frozen bool_decide_eq_false /=.
    intros Hlvl.
    rewrite drop_insert_lt //. lia.
  Qed.

  #[local] Lemma prev۰slotsｰvals_node nodes statuses roots i node status :
    nodes !! i = Some node →
    statuses !! i = Some status →
    slot۰to_val' <$> prev۰slots nodes statuses roots (PrevNode i) = status۰vals node status.
  Proof.
    intros Hnodes_lookup Hstatuses_lookup.
    rewrite /= Hnodes_lookup Hstatuses_lookup fmap_imap //.
  Qed.
  #[local] Lemma prev۰slotsｰvals_root nodes statuses roots :
    slot۰to_val' <$> prev۰slots nodes statuses roots PrevRoot = link۰to_val <$> roots.
  Proof.
    rewrite /= -list_fmap_compose //.
  Qed.

  (* Accessing the array of successors of [prev]. *)
  #[local] Lemma prev۰acc {γ nodes statuses bottom roots m} prev prevs :
    inv۰pure lt nodes statuses bottom roots m →
    prev۰at γ prev prevs -∗
    nodes۰auth γ nodes -∗
    array۰model γ.(skiplist۰name۰root) (DfracOwn 1) (link۰to_val <$> roots) -∗
    nodes۰model nodes statuses -∗
      nodes۰auth γ nodes ∗
      array۰model prevs (DfracOwn 1) (slot۰to_val' <$> prev۰slots nodes statuses roots prev) ∗
      ( ( array۰model prevs (DfracOwn 1) (slot۰to_val' <$> prev۰slots nodes statuses roots prev) -∗
            array۰model γ.(skiplist۰name۰root) (DfracOwn 1) (link۰to_val <$> roots) ∗
            nodes۰model nodes statuses
        ) ∧
        ( ∀ lvl link link' statuses' roots',
          ⌜prev۰slots nodes statuses roots prev !! lvl = Some (false, link)⌝ -∗
          ⌜prev۰update statuses roots prev lvl link' = (statuses', roots')⌝ -∗
          array۰model prevs (DfracOwn 1) (<[lvl := link۰to_val link']> (slot۰to_val' <$> prev۰slots nodes statuses roots prev)) -∗
            array۰model γ.(skiplist۰name۰root) (DfracOwn 1) (link۰to_val <$> roots') ∗
            nodes۰model nodes statuses'
        )
      ).
  Proof.
    iIntros "%Hinv Hprev Hnodes_auth Hroot Hnodes".
    destruct prev as [| i].
    - iDestruct "Hprev" as %->.
      rewrite prev۰slotsｰvals_root.
      iFrame "Hnodes_auth Hroot". iSplit.
      + iIntros "$". iFrame.
      + iIntros "%lvl %link %link' %statuses' %roots' _ %Hupdate Hroot".
        injection Hupdate as <- <-.
        rewrite list_fmap_insert. iFrame.
    - iDestruct "Hprev" as "(%node & #Hnodes_at & ->)".
      iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup.
      destruct (inv۰pureｰstatus_lookup lt Hinv i node) as (status & Hstatuses_lookup); first done.
      rewrite (prev۰slotsｰvals_node _ _ _ i node status) //.
      iDestruct (big_sepL2_insert_acc with "Hnodes") as "((Hnexts & Hmarks) & Hnodes)"; [done.. |].
      iFrame "Hnodes_auth Hnexts". iSplit.
      + iIntros "Hnexts".
        iDestruct ("Hnodes" with "[$Hnexts $Hmarks]") as "Hnodes".
        rewrite !list_insert_id //.
        iFrame.
      + iIntros "%lvl %link %link' %statuses' %roots' %Hslots %Hupdate Hnexts".
        rewrite /= Hnodes_lookup Hstatuses_lookup list_lookup_imap in Hslots.
        apply fmap_Some in Hslots as (link'' & Hlinks_lookup & [= Hmarked _]).
        injection Hupdate as <- <-.
        rewrite -statusｰset_vals; first done.
        iDestruct ("Hnodes" with "[$Hnexts Hmarks]") as "Hnodes".
        { rewrite /marks۰auth statusｰset_frozen //. }
        rewrite list_insert_id //.
        assert (
          alter (λ status, Status (<[lvl := link']> status.(status۰links)) status.(status۰marked)) i statuses =
          <[i := Status (<[lvl := link']> status.(status۰links)) status.(status۰marked)]> statuses
        ) as ->.
        { rewrite list_insert_alter.
          apply list_eq. intros j.
          rewrite !list_lookup_alter.
          case_decide; last done.
          subst. rewrite Hstatuses_lookup //.
        }
        iFrame.
  Qed.

  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %nodes{}
      & %statuses{}
      & %bottom{}
      & %roots{}
      & %m{}
      & %waiters{}
      & >Hmodel₂
      & >Hnodes_auth
      & >Hwaiters_auth
      & >Hroot
      & >Hnodes
      & #Hnodes_keys
      & >%Hinv{}
      & Hwaiters
      )
    ".
  #[local] Definition inv' γ :=
    inv γ.(skiplist۰name۰inv) (inv۰inner γ).
  Please Definition skiplist۰inv γ ι : iProp Σ :=
    ∃ sz,
    ⌜ι = γ.(skiplist۰name۰inv)⌝ ∗
    ⌜0 < sz⌝ ∗
    array۰inv γ.(skiplist۰name۰root) sz ∗
    skiplist۰valid key۰model lt γ.(skiplist۰name۰compare) ∗
    inv' γ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %sz
      & ->
      & %Hsz
      & #Hroot_inv
      & #(#Hvalid_functional & %Hvalid_order & #Hvalid_compare)
      & #Hinv
      )
    ".

  Please Definition skiplist۰model γ m : iProp Σ :=
    model₁ γ m.
  #[local] Instance : CustomIpat "model" :=
    " Hmodel₁{_{}}
    ".

  Zoo derive Timeless for skiplist۰model.

  Zoo derive Persistent for skiplist۰inv.

  (* ------------------------------------------------------------------------ *)
  (* [random_height]. *)

  #[local] Definition random_height۰inv (x0 n x : Z) :=
    (0 ≤ n)%Z ∧
    (0 ≤ x)%Z ∧
    ( n = 0%Z ∧
      x = x0
    ∨ (1 ≤ x)%Z ∧
      (2 ^ n * x ≤ x0)%Z
    ).
  #[local] Lemma random_height۰invｰstep x0 n x (c k : Z) :
    c = (2 ^ k - 1)%Z →
    (0 < k)%Z →
    random_height۰inv x0 n x →
    (c < x)%Z →
    random_height۰inv x0 (n + k) (x ≫ k).
  Proof.
    intros -> Hk (Hn & Hx & Hinv) Hcase.
    rewrite Z.shiftr_div_pow2; first lia.
    assert (0 < 2 ^ k)%Z by lia.
    assert (1 ≤ x `div` 2 ^ k)%Z.
    { apply Z.div_le_lower_bound; lia. }
    split_and!; try lia.
    right. split; first lia.
    rewrite Z.pow_add_r; [lia.. |].
    assert (2 ^ k * (x `div` 2 ^ k) ≤ x)%Z by (apply Z.mul_div_le; lia).
    assert (2 ^ n * x ≤ x0)%Z.
    { destruct Hinv as [(-> & ->) | (_ & ?)]; last done. lia. }
    assert (0 ≤ 2 ^ n)%Z by lia.
    nia.
  Qed.

  #[local] Lemma skiplist٠random_heightｰspec (max_height : nat) :
    0 < max_height →
    {{{
      True
    }}}
      skiplist٠random_height #max_height
    {{{
      (height : nat)
    , RET #height;
      ⌜0 < height ≤ max_height⌝
    }}}.
  Proof.
    iIntros "%Hmax_height %Φ _ HΦ".

    iLöb as "HLöb".

    wp۰rec.
    wp۰apply+ random٠bitsｰspec as "%bits".
    wp۰pures.
    set x0 := Z.land bits (1 ≪ ⁺max_height - 1).
    assert (0 ≤ x0 < 2 ^ ⁺max_height)%Z as Hx0.
    { rewrite /x0 Z.shiftl_1_l.
      rewrite (_ : (2 ^ ⁺max_height - 1)%Z = Z.ones ⁺max_height).
      { rewrite Z.ones_equiv. lia. }
      rewrite Z.land_ones; first lia.
      apply Z.mod_pos_bound. lia.
    }
    wp۰apply+ (structeqｰspecｰabstract (v1 := #x0) (v2 := #1)) as ([]) "%Hb"; [done | done | done | |].
    { wp۰apply+ ("HLöb" with "HΦ"). }
    wp۰pures.
    assert (random_height۰inv x0 0 x0) as Hinv0.
    { split_and!; [lia | lia | left; done]. }

    wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
    wp۰apply (wpｰwand (λ v,
      ∃ n' x' : Z,
      ⌜v = (#n', #x')%V⌝ ∗
      ⌜random_height۰inv x0 n' x'⌝
    )%I with "[]") as "%v (%n1 & %x1 & -> & %Hinv1)".
    { wp۰pures.
      case_bool_decide as Hcase; wp۰pures; iModIntro; iExists _, _; (iSplit; first done); iPureIntro.
      - eapply (random_height۰invｰstep _ _ _ 65535 16); [done | lia | done | lia].
      - done.
    }

    wp۰pures.

    wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
    wp۰apply (wpｰwand (λ v,
      ∃ n' x' : Z,
      ⌜v = (#n', #x')%V⌝ ∗
      ⌜random_height۰inv x0 n' x'⌝
    )%I with "[]") as "%v (%n2 & %x2 & -> & %Hinv2)".
    { wp۰pures.
      case_bool_decide as Hcase; wp۰pures; iModIntro; iExists _, _; (iSplit; first done); iPureIntro.
      - eapply (random_height۰invｰstep _ _ _ 255 8); [done | lia | done | lia].
      - done.
    }

    wp۰pures.

    wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
    wp۰apply (wpｰwand (λ v,
      ∃ n' x' : Z,
      ⌜v = (#n', #x')%V⌝ ∗
      ⌜random_height۰inv x0 n' x'⌝
    )%I with "[]") as "%v (%n3 & %x3 & -> & %Hinv3)".
    { wp۰pures.
      case_bool_decide as Hcase; wp۰pures; iModIntro; iExists _, _; (iSplit; first done); iPureIntro.
      - eapply (random_height۰invｰstep _ _ _ 15 4); [done | lia | done | lia].
      - done.
    }

    wp۰pures.

    wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
    wp۰apply (wpｰwand (λ v,
      ∃ n' x' : Z,
      ⌜v = (#n', #x')%V⌝ ∗
      ⌜random_height۰inv x0 n' x'⌝
    )%I with "[]") as "%v (%n4 & %x4 & -> & %Hinv4)".
    { wp۰pures.
      case_bool_decide as Hcase; wp۰pures; iModIntro; iExists _, _; (iSplit; first done); iPureIntro.
      - eapply (random_height۰invｰstep _ _ _ 3 2); [done | lia | done | lia].
      - done.
    }

    wp۰pures.

    wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
    wp۰apply (wpｰwand (λ v,
      ∃ n' x' : Z,
      ⌜v = (#n', #x')%V⌝ ∗
      ⌜random_height۰inv x0 n' x'⌝
    )%I with "[]") as "%v (%n5 & %x5 & -> & %Hinv5)".
    { wp۰pures.
      case_bool_decide as Hcase; wp۰pures; iModIntro; iExists _, _; (iSplit; first done); iPureIntro.
      - eapply (random_height۰invｰstep _ _ _ 1 1); [done | lia | done | lia].
      - done.
    }

    wp۰pures.

    destruct Hinv5 as (Hn5 & Hx5 & [(-> & ->) | (Hx5' & Hle)]).
    - rewrite Z.sub_0_r.
      iApply ("HΦ" $! max_height). iPureIntro. lia.
    - assert (n5 < ⁺max_height)%Z.
      { apply (Z.pow_lt_mono_r_iff 2); [lia | lia |].
        assert (0 ≤ 2 ^ n5)%Z by lia.
        nia.
      }
      rewrite (_ : (⁺max_height - n5)%Z = ⁺₊(⁺max_height - n5)); first lia.
      iApply "HΦ". iPureIntro. lia.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (* [create]. *)

  Lemma skiplist۰modelｰexclusive γ m1 m2 :
    skiplist۰model γ m1 -∗
    skiplist۰model γ m2 -∗
    False.
  Proof.
    iIntros "Hmodel₁_1 Hmodel₁_2".
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma skiplist٠createｰspec ι (max_height : Z) compare :
    (0 < max_height)%Z →
    {{{
      skiplist۰valid key۰model lt compare
    }}}
      skiplist٠create #max_height compare
    {{{
      γ
    , RET γ;
      skiplist۰inv γ ι ∗
      skiplist۰model γ ∅
    }}}.
  Proof.
    iIntros "%Hmax_height %Φ #Hvalid HΦ".

    wp۰rec.
    wp۰apply+ (array٠makeｰspec with "[//]") as (root) "(_ & Hroot)".
    iDestruct (array۰modelｰtoｰinv with "Hroot") as "#Hroot_inv".
    wp۰pures.

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod nodesｰalloc as "(%γ_nodes & Hnodes_auth)".
    iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ :=
      {|skiplist۰name۰compare := compare
      ; skiplist۰name۰root := root
      ; skiplist۰name۰inv := ι
      ; skiplist۰name۰model := γ_model
      ; skiplist۰name۰nodes := γ_nodes
      ; skiplist۰name۰waiters := γ_waiters
      |}.

    iApply ("HΦ" $! γ).
    iSplitR "Hmodel₁"; last iFrameSteps.
    iExists ₊max_height.
    rewrite length_replicate.
    iFrame "#".
    iSplitR; first done.
    iSplitR; first (iPureIntro; lia).
    iApply inv_alloc. iNext.
    iExists [], [], [], (replicate ₊max_height None), ∅, ∅.
    rewrite fmap_replicate.
    iFrame.
    iSplitR. { rewrite /nodes۰model. done. }
    iSplitR. { rewrite /nodes۰keys. done. }
    iSplitR. { iPureIntro. apply inv۰pureｰcreate. lia. }
    iApply big_sepM_empty. done.
  Qed.

  #[local] Lemma nodes۰modelｰmarks_at {nodes statuses bottom roots m} i node status lvl link :
    inv۰pure lt nodes statuses bottom roots m →
    nodes !! i = Some node →
    statuses !! i = Some status →
    status۰is_marked node status lvl = true →
    status.(status۰links) !! lvl = Some link →
    nodes۰model nodes statuses ⊢
      nodes۰model nodes statuses ∗
      marks۰at node lvl link.
  Proof.
    iIntros "%Hinv %Hnodes_lookup %Hstatuses_lookup %Hmarked %Hlink Hnodes".
    pose proof (inv۰pure۰status Hinv _ _ _ Hnodes_lookup Hstatuses_lookup) as (_ & Hlength & Hmarked' & _).
    iDestruct (big_sepL2_lookup_acc with "Hnodes") as "((Hnexts & Hmarks) & Hnodes)"; [done.. |].
    iDestruct (marks۰atｰget with "Hmarks") as "#Hmarks_at"; [done.. | |].
    { apply bool_decide_eq_true in Hmarked. done. }
    iFrame "#".
    iApply ("Hnodes" with "[$]").
  Qed.
  #[local] Lemma nodes۰modelｰmarks_valid {nodes statuses bottom roots m} i node status lvl link :
    inv۰pure lt nodes statuses bottom roots m →
    nodes !! i = Some node →
    statuses !! i = Some status →
    lvl < node.(node۰height) →
    nodes۰model nodes statuses -∗
    marks۰at node lvl link -∗
      nodes۰model nodes statuses ∗
      ⌜status۰is_marked node status lvl = true⌝ ∗
      ⌜status.(status۰links) !! lvl = Some link⌝.
  Proof.
    iIntros "%Hinv %Hnodes_lookup %Hstatuses_lookup %Hlvl Hnodes #Hmarks_at".
    pose proof (inv۰pure۰status Hinv _ _ _ Hnodes_lookup Hstatuses_lookup) as (_ & Hlength & Hmarked' & _).
    iDestruct (big_sepL2_lookup_acc with "Hnodes") as "((Hnexts & Hmarks) & Hnodes)"; [done.. |].
    iDestruct (marks۰atｰvalid with "Hmarks Hmarks_at") as %(Hmarked & Hlink); [done.. |].
    iSplitL. { iApply ("Hnodes" with "[$]"). }
    iPureIntro. split; last done.
    apply bool_decide_eq_true. done.
  Qed.

  #[local] Lemma waiters۰modelｰmarked γ nodes statuses1 statuses2 waiters :
    status۰marked <$> statuses1 = status۰marked <$> statuses2 →
    ( [∗ map] η ↦ waiter ∈ waiters,
      waiter۰model γ nodes statuses1 η waiter
    ) ⊢
    [∗ map] η ↦ waiter ∈ waiters,
    waiter۰model γ nodes statuses2 η waiter.
  Proof.
    iIntros "%Heq Hwaiters".
    iApply (big_sepM_impl with "Hwaiters"). iIntros "!> %η %waiter _ (%Ψ & Hη & HΨ)".
    iExists Ψ. iFrame.
    rewrite (waiter۰doneｰmarked lt nodes statuses1 statuses2) //.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [find_node]. *)

  (* [find_node] linearizes when it finds an unmarked node with key [𝑘𝑒𝑦]
     (if [b] is false), or at a moment where [𝑘𝑒𝑦] is not in the model
     (if [b] is true, which is prophesied by the caller to mean that the
     result is [Null]). *)
  #[local] Definition find_node۰commit γ 𝑘𝑒𝑦 b (Q : option val → iProp Σ) : iProp Σ :=
    ∀ m,
    ⌜if b then m !! 𝑘𝑒𝑦 = None else is_Some (m !! 𝑘𝑒𝑦)⌝ -∗
    model₂ γ m ={⊤ ∖ ↑γ.(skiplist۰name۰inv)}=∗
      model₂ γ m ∗
      Q (m !! 𝑘𝑒𝑦).
  #[local] Definition find_node۰token γ 𝑘𝑒𝑦 b Q : iProp Σ :=
    ( if b then
          Q None
        ∨ find_node۰commit γ 𝑘𝑒𝑦 b Q
      else
        find_node۰commit γ 𝑘𝑒𝑦 b Q
    )%I.
  (* At level 0, when not committed yet, we know that the current link is a
     node whose key is not greater than [𝑘𝑒𝑦] (if [P] holds). *)
  #[local] Definition find_node۰token' γ 𝑘𝑒𝑦 b Q lvl (P : Prop) link : iProp Σ :=
    ( if b then
          Q None
        ∨ find_node۰commit γ 𝑘𝑒𝑦 b Q ∗
          ⌜ lvl = 0 →
            P →
              ∃ node,
              link = Some node ∧
              ( node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦
              ∨ lt node.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦
              )
          ⌝
      else
        find_node۰commit γ 𝑘𝑒𝑦 b Q
    )%I.

  (* The token after reading the successor [link] of [node] at level [lvl]. *)
  #[local] Definition find_node۰token'' γ 𝑘𝑒𝑦 b Q lvl node link : iProp Σ :=
    ( if b then
          Q None
        ∨ find_node۰commit γ 𝑘𝑒𝑦 b Q ∗
          ⌜ lvl = 0 →
              node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦
            ∨ lt node.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦
          ⌝ ∗
          ⌜ lvl = 0 →
            lt node.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦 →
              ∃ node',
              link = Some node' ∧
              ( node'.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦
              ∨ lt node'.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦
              )
          ⌝
      else if decide (node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦) then
        Q (Some node.(node۰value))
      else
        find_node۰commit γ 𝑘𝑒𝑦 b Q
    )%I.

  #[local] Definition node۰marked0 γ node : iProp Σ :=
    ∃ link,
    marks۰at node 0 link.
  #[local] Definition find_node۰excl γ (excl : option (node Key)) : iProp Σ :=
    match excl with
    | None =>
        True
    | Some node =>
        (∃ i, nodes۰at γ i node) ∗
        node۰marked0 γ node
    end.

  #[local] Instance find_node۰exclｰpersistent γ excl :
    Persistent (find_node۰excl γ excl).
  Proof.
    destruct excl; apply _.
  Qed.

  #[local] Definition find_node۰post γ 𝑘𝑒𝑦 b (excl : option (node Key)) Q res : iProp Σ :=
    ( ⌜res = §skiplist٠Null%V⌝ ∗
      (if b then Q None else True)
    ∨ ∃ i node,
      ⌜res = node۰to_val node⌝ ∗
      ⌜node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦⌝ ∗
      ⌜∀ node', excl = Some node' → node۰to_val node ≠ node۰to_val node'⌝ ∗
      node۰at γ i node ∗
      (if b then True else Q (Some node.(node۰value)))
    )%I.

  #[local] Lemma find_node۰tokenｰweaken γ 𝑘𝑒𝑦 b Q lvl P link :
    find_node۰token' γ 𝑘𝑒𝑦 b Q lvl P link ⊢
    find_node۰token γ 𝑘𝑒𝑦 b Q.
  Proof.
    rewrite /find_node۰token' /find_node۰token.
    destruct b; iIntros "Htoken"; last done.
    iDestruct "Htoken" as "[Htoken | (Htoken & _)]".
    - iLeft. done.
    - iRight. done.
  Qed.
  #[local] Lemma find_node۰tokenｰlvl γ 𝑘𝑒𝑦 b Q lvl P link :
    0 < lvl →
    find_node۰token γ 𝑘𝑒𝑦 b Q ⊢
    find_node۰token' γ 𝑘𝑒𝑦 b Q lvl P link.
  Proof.
    iIntros "%Hlvl Htoken".
    rewrite /find_node۰token' /find_node۰token.
    destruct b; last done.
    iDestruct "Htoken" as "[Htoken | Htoken]".
    - iLeft. done.
    - iRight. iFrame. iPureIntro. lia.
  Qed.

  (* At level 0, after reading [link], the successor of [prev] at position
     [q] in [bottom]. *)
  #[local] Lemma find_node۰tokenｰstep {γ nodes statuses bottom roots m} 𝑘𝑒𝑦 b Q q P link :
    StrictOrder lt →
    inv۰pure lt nodes statuses bottom roots m →
    link = bottom !! q →
    ( P →
      ∀ k,
      q = S k →
        ∃ pred,
        bottom !! k = Some pred ∧
        lt pred.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦
    ) →
    model₂ γ m -∗
    find_node۰token γ 𝑘𝑒𝑦 b Q ={⊤ ∖ ↑γ.(skiplist۰name۰inv)}=∗
      model₂ γ m ∗
      find_node۰token' γ 𝑘𝑒𝑦 b Q 0 P link.
  Proof.
    iIntros "%Horder %Hinv %Hlink %Hq Hmodel₂ Htoken".
    rewrite /find_node۰token' /find_node۰token.
    destruct b; last iFrameSteps.
    iDestruct "Htoken" as "[Htoken | Htoken]".
    { iFrameSteps. }
    destruct (m !! 𝑘𝑒𝑦) as [v |] eqn:Hlookup.
    - iFrame. iRight. iFrame. iPureIntro.
      intros _ HP.
      opose proof* (inv۰pureｰlocate lt Hinv 𝑘𝑒𝑦 v q) as (node & Hnode & Hnode'); [| done |].
      { apply Hq. done. }
      exists node. split; first congruence. done.
    - iMod ("Htoken" with "[//] Hmodel₂") as "(Hmodel₂ & HQ)".
      rewrite Hlookup. iFrame. done.
  Qed.

  #[local] Lemma skiplist٠find_node_1ｰfind_node_2ｰfind_nodeｰspec γ ι key 𝑘𝑒𝑦 b excl Q :
    ⊢ (
      ∀ lvl prev prevs curr,
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        find_node۰excl γ excl ∗
        prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs ∗
        ( ( ∃ v,
            ⌜curr = ‘skiplist٠Mark( v )%V⌝
          ) ∗
          find_node۰token γ 𝑘𝑒𝑦 b Q
        ∨ ∃ link,
          ⌜curr = link۰to_val link⌝ ∗
          link۰model γ lvl link ∗
          find_node۰token' γ 𝑘𝑒𝑦 b Q lvl True link
        )
      }}}
        skiplist٠find_node_1 γ key prevs #lvl curr
      {{{
        res
      , RET res;
        find_node۰post γ 𝑘𝑒𝑦 b excl Q res
      }}}
    ) ∧ (
      ∀ lvl prev prevs,
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        find_node۰excl γ excl ∗
        prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs ∗
        find_node۰token γ 𝑘𝑒𝑦 b Q
      }}}
        skiplist٠find_node_2 γ key prevs #lvl
      {{{
        res
      , RET res;
        find_node۰post γ 𝑘𝑒𝑦 b excl Q res
      }}}
    ) ∧ (
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        find_node۰excl γ excl ∗
        find_node۰token γ 𝑘𝑒𝑦 b Q
      }}}
        skiplist٠find_node γ key
      {{{
        res
      , RET res;
        find_node۰post γ 𝑘𝑒𝑦 b excl Q res
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHfind_node_1 & IHfind_node_2 & IHfind_node)".
    iSplit; last iSplit.

    { iIntros "%lvl %prev %prevs %curr !> %Φ (#Hskiplist & #Hkey & #Hexcl & #Hprevs & Hcurr) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".
      pose proof (Hvalid_order : StrictOrder lt) as Horder.
      iPoseProof "Hprevs" as "(%sz' & #Hprevs_inv & %Hlvl' & _)".
      iDestruct (prevs۰modelｰprev_at with "Hprevs") as "#Hprev_at".
      iDestruct "Hcurr" as "[((%v & ->) & Htoken) | (%link & -> & #Hlink & Htoken)]".

      - wp۰rec.
        wp۰apply+ ("IHfind_node" with "[$Hskiplist $Hkey $Hexcl $Htoken] HΦ").

      - destruct link as [node |]; last first.

        { wp۰rec.
          destruct lvl as [| lvl].

          - wp۰pures.
            iModIntro. iApply "HΦ". iLeft. iSplit; first done.
            rewrite /find_node۰token'. destruct b; last done.
            iDestruct "Htoken" as "[$ | (_ & %Hfact)]".
            exfalso. destruct (Hfact eq_refl I) as (? & [=] & _).

          - wp۰pures.
            rewrite (_ : (⁺˖lvl - 1)%Z = ⁺lvl); first lia.
            wp۰apply ("IHfind_node_2" with "[$Hskiplist $Hkey $Hexcl Htoken] HΦ").
            iSplitR. { iApply (prevs۰modelｰmono with "Hprevs"). lia. }
            iApply (find_node۰tokenｰweaken with "Htoken").
        }

        iDestruct "Hlink" as "(%i & (#Hnodes_at & #Hnexts_inv & #Hkey') & %Hlvl)".

        wp۰rec.

        awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Hnexts_inv") without "HΦ"; first lia.
        iInv "Hinv" as "(:inv۰inner =1)".
        iDestruct (prev۰acc (PrevNode i) with "[] Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hnexts & Hclose)"; first done.
        { iExists node. iFrame "#". done. }
        iAaccIntro with "Hnexts".
        { iIntros "Hnexts !>".
          iDestruct "Hclose" as "(Hclose & _)".
          iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
          iSplitR "Htoken"; last iSteps.
          iFrameSteps.
        }
        iIntros "%v (%Hlookup & Hnexts)".
        rewrite difference_empty_L.
        iDestruct "Hclose" as "(Hclose & _)".
        iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
        iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup.
        destruct (inv۰pureｰstatus_lookup lt Hinv1 i node) as (status & Hstatuses_lookup); first done.
        rewrite Nat2Z.id (prev۰slotsｰvals_node _ _ _ i node status) // /status۰vals list_lookup_imap in Hlookup.
        apply fmap_Some in Hlookup as (link & Hlinks_lookup & ->).
        pose proof (inv۰pure۰status Hinv1 _ _ _ Hnodes_lookup Hstatuses_lookup) as (Hheight & Hlength & Hmarked_le & Hlinks).
        pose proof (Hlinks _ _ Hlinks_lookup) as Hwf.
        iDestruct (link۰modelｰget with "Hnodes_auth Hnodes Hnodes_keys") as "(Hnodes_auth & Hnodes & Hlink)"; [done.. |].
        destruct (status۰is_marked node status lvl) eqn:Hmarked.

        + iDestruct (nodes۰modelｰmarks_at with "Hnodes") as "(Hnodes & #Hmarks_at)"; [done.. |].
          iSplitR "Htoken Hlink". { iFrameSteps. }
          iIntros "!> H£ HΦ {Hnodes_keys}".
          iMod (lc_fupd_elim_later with "H£ Hlink") as "#Hlink".

          awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Hprevs_inv") without "HΦ"; first lia.
          iInv "Hinv" as "(:inv۰inner =2)".
          iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup2.
          destruct (inv۰pureｰstatus_lookup lt Hinv2 i node) as (status2 & Hstatuses2_lookup); first done.
          iDestruct (nodes۰modelｰmarks_valid with "Hnodes Hmarks_at") as "(Hnodes & %Hmarked2 & %Hlinks2_lookup)"; [done.. |].
          pose proof (inv۰pure۰status Hinv2 _ _ _ Hnodes_lookup2 Hstatuses2_lookup) as (_ & _ & Hmarked2_le & Hlinks2).
          iDestruct (prev۰acc with "Hprev_at Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hprevs_model & Hclose)"; first done.
          iAaccIntro with "Hprevs_model".
          { iIntros "Hprevs_model !>".
            iDestruct "Hclose" as "(Hclose & _)".
            iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
            iSplitR "Htoken"; last iSteps.
            iFrameSteps.
          }
          iIntros "%b' %w (%Hlookup & %Hcas & Hprevs_model)".
          rewrite difference_empty_L.
          destruct b'.

          * rewrite Nat2Z.id list_lookup_fmap in Hlookup.
            apply fmap_Some in Hlookup as ((marked' & link') & Hslot & ->).
            pose proof (inv۰pureｰprev_slot lt Hinv2 _ _ _ _ Hslot) as Hwf'.
            iDestruct (slot۰to_valｰsimilar lvl marked' link' node Hinv2 Hwf' with "Hnexts_inv") as %(-> & ->).
            { eapply list_elem_of_lookup_2. done. }
            { exact Hcas. }
            destruct (prev۰update statuses2 roots2 prev lvl link) as (statuses' & roots') eqn:Hupdate.
            iDestruct "Hclose" as "(_ & Hclose)".
            iDestruct ("Hclose" with "[//] [//] [Hprevs_model]") as "(Hroot & Hnodes)".
            { rewrite Nat2Z.id //. }
            iDestruct (waiters۰modelｰmarked _ _ _ statuses' with "Hwaiters") as "Hwaiters".
            { symmetry. eapply prev۰updateｰmarked; done. }
            iDestruct (prevs۰modelｰlt with "Hnodes_auth Hprevs") as %Hprev_lt.
            iAssert (
              ∃ bottom',
              model₂ γ m2 ∗
              ⌜inv۰pure lt nodes2 statuses' bottom' roots' m2⌝ ∗
              find_node۰token' γ 𝑘𝑒𝑦 b Q lvl True link
            )%I with "[> Hmodel₂ Htoken]" as "(%bottom' & Hmodel₂ & %Hinv' & Htoken)".
            { iDestruct (find_node۰tokenｰweaken with "Htoken") as "Htoken".
              destruct lvl as [| lvl].
              - destruct (inv۰pureｰprev0 lt Hinv2 prev (Some node)) as (q & Hq & Hnode_q); first done.
                assert (status2.(status۰marked) = node.(node۰height)) as Hmarked0.
                { apply bool_decide_eq_true in Hmarked2. lia. }
                pose proof (inv۰pure۰bottom_links Hinv2 _ _ _ _ (eq_sym Hnode_q) Hnodes_lookup2 Hstatuses2_lookup) as Hlink_q.
                rewrite Hlinks2_lookup in Hlink_q. injection Hlink_q as ->.
                pose proof (inv۰pureｰunlink0 lt Hinv2 prev q node i status2 statuses' roots' Hq (eq_sym Hnode_q) Hnodes_lookup2 Hstatuses2_lookup Hmarked0 Hupdate) as Hinv'.
                iExists (delete q bottom2).
                iMod (find_node۰tokenｰstep with "Hmodel₂ Htoken") as "($ & $)"; [done | | | done].
                + rewrite list_lookup_delete_ge //.
                + intros _ k ->.
                  destruct prev as [| i']; simpl in Hq; first lia.
                  destruct Hq as (k' & pred & Hpred_lookup & Hpred_lookup' & [= ->]).
                  exists pred. split.
                  * rewrite list_lookup_delete_lt //. lia.
                  * eapply Hprev_lt; done.
              - iExists bottom2. iFrame.
                iSplitR.
                { iPureIntro. eapply (inv۰pureｰset lt Hinv2 prev ˖lvl (Some node) link); [lia | done | | done].
                  eapply Hlinks2. done.
                }
                iApply (find_node۰tokenｰlvl with "Htoken"). lia.
            }
            iSplitR "Htoken".
            { iIntros "!> !>". iExists nodes2, statuses', bottom', roots', m2, waiters2. iFrame "∗#%". }
            iIntros "!> _ HΦ".

            wp۰apply+ ("IHfind_node_1" with "[$Hskiplist $Hkey $Hexcl $Hprevs Htoken] HΦ").
            iRight. iExists link. iFrame "#∗". done.

          * iDestruct "Hclose" as "(Hclose & _)".
            iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
            iSplitR "Htoken". { iFrameSteps. }
            iIntros "!> _ HΦ".

            wp۰apply+ ("IHfind_node_2" with "[$Hskiplist $Hkey $Hexcl $Hprevs Htoken] HΦ").
            iApply (find_node۰tokenｰweaken with "Htoken").

        + pose proof (inv۰pureｰlive i node status lvl Hinv1 Hnodes_lookup Hstatuses_lookup Hmarked) as Hlive.
          iAssert ⌜
            ∀ node',
            excl = Some node' →
            node۰to_val node ≠ node۰to_val node'
          ⌝%I as %Hexcl.
          { destruct excl as [node' |]; last (iPureIntro; intros ? [=]).
            iDestruct "Hexcl" as "((%j & #Hnodes_at') & %link' & #Hmarks_at')".
            iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at'") as %Hnodes_lookup'.
            destruct (decide (i = j)) as [<- | Hne].
            - assert (node' = node) as -> by congruence.
              iDestruct (nodes۰modelｰmarks_valid with "Hnodes Hmarks_at'") as "(_ & %Hmarked0 & _)"; [done.. |].
              exfalso.
              rewrite /status۰is_marked bool_decide_eq_true in Hmarked0.
              rewrite /status۰is_marked bool_decide_eq_false in Hmarked.
              lia.
            - iPureIntro. intros ? [= <-] Heq.
              apply Hne. eapply (inv۰pureｰindex_inj lt Hinv1); first done.
              rewrite Hnodes_lookup'. f_equal. eapply (inv۰pureｰnexts_inj lt Hinv1).
              + eapply list_elem_of_lookup_2. done.
              + eapply list_elem_of_lookup_2. done.
              + rewrite /node۰to_val in Heq. congruence.
          }
          iAssert (
            model₂ γ m1 ∗
            find_node۰token'' γ 𝑘𝑒𝑦 b Q lvl node link
          )%I with "[> Hmodel₂ Htoken]" as "(Hmodel₂ & Htoken)".
          { rewrite /find_node۰token' /find_node۰token''.
            destruct b.
            - iDestruct "Htoken" as "[HQ | (Hcommit & %Hfact)]".
              { iFrame. done. }
              destruct lvl as [| lvl].
              + destruct (Hfact eq_refl I) as (node' & [= <-] & Hnode).
                destruct (inv۰pureｰprev0 lt Hinv1 (PrevNode i) link) as (q & Hq & Hlink_q).
                { rewrite /= Hnodes_lookup Hstatuses_lookup list_lookup_imap Hlinks_lookup /= Hmarked //. }
                iMod (find_node۰tokenｰstep _ true Q q (lt node.(node۰𝑘𝑒𝑦) 𝑘𝑒𝑦) with "Hmodel₂ [Hcommit]") as "($ & [HQ | (Hcommit & %Hfact')])"; [done | done | | iRight; done | |].
                * intros Hlt k ->.
                  destruct Hq as (k' & node' & Hnodes_lookup' & Hbottom_lookup & [= ->]).
                  exists node. split; last done. congruence.
                * iFrame. done.
                * iRight. iFrame. iPureIntro. split.
                  -- intros _. done.
                  -- intros _. apply Hfact'. done.
              + iFrame "Hmodel₂". iModIntro. iRight. iFrame. iPureIntro. split; lia.
            - case_decide as Hkey_eq.
              + iMod ("Htoken" with "[] Hmodel₂") as "($ & HQ)".
                { iPureIntro. rewrite -Hkey_eq Hlive. done. }
                rewrite -Hkey_eq Hlive. done.
              + iFrame. done.
          }
          iSplitR "Htoken Hlink". { iFrameSteps. }
          iIntros "!> H£ HΦ".
          iMod (lc_fupd_elim_later with "H£ Hlink") as "#Hlink".

          wp۰apply+ (wpｰwand with "(Hvalid_compare Hkey Hkey')") as (res) "(%cmp & -> & %Hcmp_lt & %Hcmp_eq & %Hcmp_gt)".
          wp۰pures.
          destruct (Z.lt_trichotomy 0 cmp) as [Hcmp | [<- | Hcmp]].

          * rewrite bool_decide_eq_true_2 //.
            wp۰apply+ ("IHfind_node_1" $! lvl (PrevNode i) with "[$Hskiplist $Hkey $Hexcl Htoken] HΦ").
            specialize (Hcmp_gt Hcmp).
            iSplitR.
            { iExists node.(node۰height). iFrame "#". iSplit; first done.
              iSplit; iPureIntro; done.
            }
            iRight. iExists link. iFrame "#". iSplit; first done.
            rewrite /find_node۰token'' /find_node۰token'.
            destruct b.
            -- iDestruct "Htoken" as "[HQ | (Hcommit & _ & %Hfact)]"; first iFrame.
               iRight. iFrame. iPureIntro.
               intros Hlvl0 _. apply Hfact; done.
            -- case_decide as Hkey_eq; last done.
               exfalso. rewrite Hkey_eq in Hcmp_gt. eapply (irreflexivity lt); done.

          * wp۰pures.
            iModIntro. iApply "HΦ". iRight. iExists i, node. iFrame "#".
            specialize (Hcmp_eq eq_refl).
            iSplit; first done. iSplit; first done. iSplit; first done.
            rewrite /find_node۰token''.
            destruct b; first done.
            rewrite decide_True //.

          * rewrite bool_decide_eq_false_2; first lia.
            wp۰pures.
            rewrite bool_decide_eq_false_2; first lia.
            specialize (Hcmp_lt Hcmp).
            destruct lvl as [| lvl].

            -- wp۰pures.
               iModIntro. iApply "HΦ". iLeft. iSplit; first done.
               rewrite /find_node۰token''.
               destruct b; last done.
               iDestruct "Htoken" as "[$ | (_ & %Hfact & _)]".
               exfalso.
               destruct (Hfact eq_refl) as [Heq | Hlt].
               ++ rewrite Heq in Hcmp_lt. eapply (irreflexivity lt); done.
               ++ eapply (irreflexivity lt). trans node.(node۰𝑘𝑒𝑦); done.

            -- wp۰pures.
               rewrite (_ : (⁺˖lvl - 1)%Z = ⁺lvl); first lia.
               wp۰apply ("IHfind_node_2" with "[$Hskiplist $Hkey $Hexcl Htoken] HΦ").
               iSplitR. { iApply (prevs۰modelｰmono with "Hprevs"). lia. }
               rewrite /find_node۰token'' /find_node۰token.
               destruct b.
               ++ iDestruct "Htoken" as "[$ | (Hcommit & _)]". iFrame.
               ++ case_decide as Hkey_eq; last done.
                  exfalso. rewrite Hkey_eq in Hcmp_lt. eapply (irreflexivity lt); done.
    }

    { iIntros "%lvl %prev %prevs !> %Φ (#Hskiplist & #Hkey & #Hexcl & #Hprevs & Htoken) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".
      pose proof (Hvalid_order : StrictOrder lt) as Horder.
      iPoseProof "Hprevs" as "(%sz' & #Hprevs_inv & %Hlvl & _)".
      iDestruct (prevs۰modelｰprev_at with "Hprevs") as "#Hprev_at".

      wp۰rec.
      awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Hprevs_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (prev۰acc with "Hprev_at Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hprevs_model & Hclose)"; first done.
      iAaccIntro with "Hprevs_model".
      { iIntros "Hprevs_model !>".
        iDestruct "Hclose" as "(Hclose & _)".
        iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
        iSplitR "Htoken"; last iSteps.
        iFrameSteps.
      }
      iIntros "%v (%Hlookup & Hprevs_model)".
      rewrite difference_empty_L.
      iDestruct "Hclose" as "(Hclose & _)".
      iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
      rewrite Nat2Z.id list_lookup_fmap in Hlookup.
      apply fmap_Some in Hlookup as ((marked & link) & Hslot & ->).
      pose proof (inv۰pureｰprev_slot lt Hinv1 _ _ _ _ Hslot) as Hwf.
      destruct marked.

      - iSplitR "Htoken". { iFrameSteps. }
        iIntros "!> _ HΦ".

        wp۰apply ("IHfind_node_1" with "[$Hskiplist $Hkey $Hexcl $Hprevs Htoken] HΦ").
        iLeft. iFrame. iSteps.

      - iDestruct (link۰modelｰget with "Hnodes_auth Hnodes Hnodes_keys") as "(Hnodes_auth & Hnodes & Hlink)"; [done.. |].
        iDestruct (prevs۰modelｰlt with "Hnodes_auth Hprevs") as %Hprev_lt.
        iAssert (
          model₂ γ m1 ∗
          find_node۰token' γ 𝑘𝑒𝑦 b Q lvl True link
        )%I with "[> Hmodel₂ Htoken]" as "(Hmodel₂ & Htoken)".
        { destruct lvl as [| lvl].
          - destruct (inv۰pureｰprev0 lt Hinv1 prev link) as (q & Hq & ->); first done.
            iApply (find_node۰tokenｰstep with "Hmodel₂ Htoken"); [done | done |].
            intros _. apply (inv۰pureｰprev_position lt Hinv1 prev q 𝑘𝑒𝑦); done.
          - iFrame. iApply (find_node۰tokenｰlvl with "Htoken"). lia.
        }
        iSplitR "Htoken Hlink". { iFrameSteps. }
        iIntros "!> H£ HΦ".
        iMod (lc_fupd_elim_later with "H£ Hlink") as "#Hlink".

        wp۰apply ("IHfind_node_1" with "[$Hskiplist $Hkey $Hexcl $Hprevs Htoken] HΦ").
        iRight. iFrame "#∗". done.
    }

    { iIntros "!> %Φ (#Hskiplist & #Hkey & #Hexcl & Htoken) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".

      wp۰rec.
      wp۰apply+ (array٠sizeｰspecｰinv with "Hroot_inv") as "_".
      wp۰pures.
      rewrite (_ : (⁺sz - 1)%Z = ⁺(sz - 1)); first lia.
      wp۰apply ("IHfind_node_2" $! (sz - 1) PrevRoot with "[$Hskiplist $Hkey $Hexcl $Htoken] HΦ").
      iExists sz. iFrame "#". iSplit; first (iPureIntro; lia). done.
    }
  Qed.

  #[local] Lemma skiplist٠find_nodeｰspec γ ι key 𝑘𝑒𝑦 b excl Q :
    {{{
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦 ∗
      find_node۰excl γ excl ∗
      find_node۰token γ 𝑘𝑒𝑦 b Q
    }}}
      skiplist٠find_node γ key
    {{{
      res
    , RET res;
      find_node۰post γ 𝑘𝑒𝑦 b excl Q res
    }}}.
  Proof.
    iDestruct (skiplist٠find_node_1ｰfind_node_2ｰfind_nodeｰspec γ ι key 𝑘𝑒𝑦 b excl Q) as "(_ & _ & H)".
    iApply "H".
  Qed.
  #[local] Lemma skiplist٠find_nodeｰspecｰcleanup γ ι key 𝑘𝑒𝑦 :
    {{{
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      skiplist٠find_node γ key
    {{{
      res
    , RET res;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hskiplist & #Hkey) HΦ".

    wp۰apply (skiplist٠find_nodeｰspec γ ι key 𝑘𝑒𝑦 false None (λ _, True)%I with "[$Hskiplist $Hkey]") as (res) "_".
    { iSplit; first done.
      iIntros "%m _ Hmodel₂ !>". iFrame.
    }
    iApply "HΦ". done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [find_node_resolved]. *)

  #[local] Definition node۰result o res :=
    match o with
    | None =>
        res = §skiplist٠Null%V
    | Some v =>
        ∃ key nexts,
        res = ‘skiplist٠Node( key, v, nexts )%V
    end.

  #[local] Lemma skiplist٠find_node_resolvedｰspec γ ι key 𝑘𝑒𝑦 :
    <<<
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      skiplist۰model γ m
    >>>
      skiplist٠find_node_resolved γ key
      @ ↑ι
    <<<
      skiplist۰model γ m
    | res,
      RET res;
      ⌜node۰result (m !! 𝑘𝑒𝑦) res⌝
    >>>.
  Proof.
    iIntros "%Φ (#Hskiplist & #Hkey) HΦ".
    iPoseProof "Hskiplist" as "(:inv)".
    set Ψ := (λ o, ∀ res, ⌜node۰result o res⌝ -∗ Φ res)%I.

    wp۰rec.
    wp۰apply+ (prophet_typed₁ｰwpｰproph prophet_res with "[//]") as (pid proph) "Hproph".
    wp۰apply+ (skiplist٠find_nodeｰspec γ _ key 𝑘𝑒𝑦 (bool_decide (proph = §skiplist٠Null%V)) None Ψ with "[$Hskiplist $Hkey HΦ]") as (res) "Hres".
    { iSplit; first done.
      iAssert (find_node۰commit γ 𝑘𝑒𝑦 (bool_decide (proph = §skiplist٠Null%V)) Ψ)%I with "[HΦ]" as "Hcommit".
      { iIntros "%m _ Hmodel₂".
        iMod "HΦ" as "(%m' & (:model) & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΦ" with "Hmodel₁") as "HΦ".
        iFrame. done.
      }
      rewrite /find_node۰token.
      case_bool_decide; last done.
      iRight. done.
    }
    wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
    wp۰pures.
    iExists (Some res). iSplitR; first done.
    iIntros "!> %Hproph". subst proph.
    rewrite /Ψ.
    iDestruct "Hres" as "[(-> & HΦ) | (%i & %node & -> & _ & _ & _ & HΦ)]".
    - rewrite bool_decide_eq_true_2 //.
      wp۰pures.
      iApply "HΦ". done.
    - rewrite bool_decide_eq_false_2 //.
      wp۰pures.
      iApply "HΦ". iPureIntro. eexists _, _. done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [find]. *)

  Lemma skiplist٠findｰspec γ ι key 𝑘𝑒𝑦 :
    <<<
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      skiplist۰model γ m
    >>>
      skiplist٠find γ key
      @ ↑ι
    <<<
      skiplist۰model γ m
    | RET m !! 𝑘𝑒𝑦;
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hskiplist & #Hkey) HΦ".

    wp۰rec.
    awp۰apply+ (skiplist٠find_node_resolvedｰspec with "[$Hskiplist $Hkey]").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%m Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    iFrame. iIntros "HΦ !> %res %Hres".
    destruct (m !! 𝑘𝑒𝑦) as [v |]; simpl in Hres.

    - destruct Hres as (key' & nexts & ->).
      wp۰pures.
      iApply "HΦ". done.

    - subst res.
      wp۰pures.
      iApply "HΦ". done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [mem]. *)

  Lemma skiplist٠memｰspec γ ι key 𝑘𝑒𝑦 :
    <<<
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      skiplist۰model γ m
    >>>
      skiplist٠mem γ key
      @ ↑ι
    <<<
      skiplist۰model γ m
    | RET #(bool_decide (𝑘𝑒𝑦 ∈ dom m));
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hskiplist & #Hkey) HΦ".

    wp۰rec.
    awp۰apply+ (skiplist٠find_node_resolvedｰspec with "[$Hskiplist $Hkey]").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%m Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    iFrame. iIntros "HΦ !> %res %Hres".
    destruct (m !! 𝑘𝑒𝑦) as [v |] eqn:Hlookup; simpl in Hres.

    - destruct Hres as (key' & nexts & ->).
      wp۰pures.
      rewrite bool_decide_eq_true_2.
      { apply elem_of_dom. done. }
      iApply "HΦ". done.

    - subst res.
      wp۰pures.
      rewrite bool_decide_eq_false_2.
      { apply not_elem_of_dom. done. }
      iApply "HΦ". done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [find_path]. *)

  (* The arrays [preds] and [succs] of [add]. *)
  #[local] Definition path۰model γ 𝑘𝑒𝑦 preds succs (height : nat) prevs_list links : iProp Σ :=
    array۰model preds (DfracOwn 1) prevs_list ∗
    array۰model succs (DfracOwn 1) (link۰to_val <$> links) ∗
    ⌜length prevs_list = height⌝ ∗
    ⌜length links = height⌝ ∗
    ( [∗ list] lvl ↦ prevs ∈ prevs_list,
      ∃ prev,
      prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs
    ) ∗
    ( [∗ list] lvl ↦ link ∈ links,
      link۰model γ lvl link
    ).
  #[local] Instance : CustomIpat "path۰model" :=
    " ( Hpreds
      & Hsuccs
      & %Hprevs_list_length
      & %Hlinks_length
      & #Hprevs_list
      & #Hlinks
      )
    ".

  (* [find_path] linearizes when it finds an unmarked node with key [𝑘𝑒𝑦] at
     level [low]. *)
  #[local] Definition find_path۰commit γ 𝑘𝑒𝑦 (R : iProp Σ) : iProp Σ :=
    ∀ m,
    ⌜is_Some (m !! 𝑘𝑒𝑦)⌝ -∗
    model₂ γ m ={⊤ ∖ ↑γ.(skiplist۰name۰inv)}=∗
      model₂ γ m ∗
      R.

  #[local] Definition find_path۰post γ 𝑘𝑒𝑦 preds succs height (low : nat) (R P : iProp Σ) res : iProp Σ :=
    ∃ b prevs_list links,
    ⌜res = #b⌝ ∗
    path۰model γ 𝑘𝑒𝑦 preds succs height prevs_list links ∗
    if b then
      R
    else
      P ∗
      ⌜ low = 0 →
        ∀ node,
        links !! 0 = Some (Some node) →
        lt 𝑘𝑒𝑦 node.(node۰𝑘𝑒𝑦)
      ⌝.

  #[local] Lemma path۰modelｰupdate γ 𝑘𝑒𝑦 preds succs height prevs_list links lvl prev prevs link :
    lvl < height →
    array۰model preds (DfracOwn 1) (<[lvl := prevs]> prevs_list) -∗
    array۰model succs (DfracOwn 1) (<[lvl := link۰to_val link]> (link۰to_val <$> links)) -∗
    ⌜length prevs_list = height⌝ -∗
    ⌜length links = height⌝ -∗
    ( [∗ list] lvl ↦ prevs ∈ prevs_list,
      ∃ prev,
      prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs
    ) -∗
    ( [∗ list] lvl ↦ link ∈ links,
      link۰model γ lvl link
    ) -∗
    prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs -∗
    link۰model γ lvl link -∗
    path۰model γ 𝑘𝑒𝑦 preds succs height (<[lvl := prevs]> prevs_list) (<[lvl := link]> links).
  Proof.
    iIntros "%Hlvl Hpreds Hsuccs %Hprevs_list_length %Hlinks_length #Hprevs_list #Hlinks #Hprevs #Hlink".
    rewrite /path۰model list_fmap_insert. iFrame.
    rewrite !length_insert.
    iSplit; first done. iSplit; first done.
    destruct (lookup_lt_is_Some_2 prevs_list lvl) as (prevs' & Hprevs_lookup); first lia.
    destruct (lookup_lt_is_Some_2 links lvl) as (link' & Hlinks_lookup); first lia.
    iSplit.
    - iDestruct (big_sepL_insert_acc with "Hprevs_list") as "(_ & H)"; first done.
      iApply "H". iExists prev. done.
    - iDestruct (big_sepL_insert_acc with "Hlinks") as "(_ & H)"; first done.
      iApply "H". done.
  Qed.

  #[local] Lemma skiplist٠find_path_1ｰfind_path_2ｰfind_pathｰspec γ ι key 𝑘𝑒𝑦 preds succs height (low : nat) (R P : iProp Σ) :
    ⊢ (
      ∀ lvl prev prevs curr prevs_list links,
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        □ (P -∗ find_path۰commit γ 𝑘𝑒𝑦 R) ∗
        ( ∃ sz,
          array۰inv γ.(skiplist۰name۰root) sz ∗
          ⌜low < sz⌝
        ) ∗
        ⌜low ≤ lvl⌝ ∗
        prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs ∗
        path۰model γ 𝑘𝑒𝑦 preds succs height prevs_list links ∗
        P ∗
        ( ( ∃ v,
            ⌜curr = ‘skiplist٠Mark( v )%V⌝
          )
        ∨ ∃ link,
          ⌜curr = link۰to_val link⌝ ∗
          link۰model γ lvl link
        )
      }}}
        skiplist٠find_path_1 γ key prevs preds succs #lvl #low curr
      {{{
        res
      , RET res;
        find_path۰post γ 𝑘𝑒𝑦 preds succs height low R P res
      }}}
    ) ∧ (
      ∀ lvl prev prevs prevs_list links,
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        □ (P -∗ find_path۰commit γ 𝑘𝑒𝑦 R) ∗
        ( ∃ sz,
          array۰inv γ.(skiplist۰name۰root) sz ∗
          ⌜low < sz⌝
        ) ∗
        ⌜low ≤ lvl⌝ ∗
        prevs۰model γ 𝑘𝑒𝑦 lvl prev prevs ∗
        path۰model γ 𝑘𝑒𝑦 preds succs height prevs_list links ∗
        P
      }}}
        skiplist٠find_path_2 γ key prevs preds succs #lvl #low
      {{{
        res
      , RET res;
        find_path۰post γ 𝑘𝑒𝑦 preds succs height low R P res
      }}}
    ) ∧ (
      ∀ prevs_list links,
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        □ (P -∗ find_path۰commit γ 𝑘𝑒𝑦 R) ∗
        ( ∃ sz,
          array۰inv γ.(skiplist۰name۰root) sz ∗
          ⌜low < sz⌝
        ) ∗
        path۰model γ 𝑘𝑒𝑦 preds succs height prevs_list links ∗
        P
      }}}
        skiplist٠find_path γ key preds succs #low
      {{{
        res
      , RET res;
        find_path۰post γ 𝑘𝑒𝑦 preds succs height low R P res
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHfind_path_1 & IHfind_path_2 & IHfind_path)".
    iSplit; last iSplit.

    { iIntros "%lvl %prev %prevs %curr %prevs_list %links !> %Φ (#Hskiplist & #Hkey & #Hconv & #Hroot_low & %Hlow & #Hprevs & Hpath & Hcommit & Hcurr) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".
      pose proof (Hvalid_order : StrictOrder lt) as Horder.
      iPoseProof "Hprevs" as "(%sz' & #Hprevs_inv & %Hlvl' & _)".
      iDestruct (prevs۰modelｰprev_at with "Hprevs") as "#Hprev_at".
      iDestruct "Hcurr" as "[(%v & ->) | (%link & -> & #Hlink)]".

      - wp۰rec.
        wp۰apply+ ("IHfind_path" with "[$Hskiplist $Hkey $Hconv $Hroot_low $Hpath $Hcommit] HΦ").

      - destruct link as [node |]; last first.

        { wp۰rec.
          iDestruct "Hpath" as "(:path۰model)".
          wp۰apply+ (array٠sizeｰspec with "Hpreds") as "Hpreds".
          wp۰pures.

          wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
          wp۰apply (wpｰwand (λ v,
            ⌜v = ()%V⌝ ∗
            ∃ prevs_list' links',
            path۰model γ 𝑘𝑒𝑦 preds succs height prevs_list' links' ∗
            ⌜lvl < height → links' !! lvl = Some None⌝
          )%I with "[Hpreds Hsuccs]") as "%v (-> & %prevs_list' & %links' & Hpath & %Hlinks'_lookup)".
          { case_bool_decide as Hlvl_height.
            - wp۰apply+ (array٠unsafe_setｰspec with "Hpreds") as "Hpreds"; first lia.
              wp۰apply+ (array٠unsafe_setｰspec with "Hsuccs") as "Hsuccs".
              { rewrite length_fmap. lia. }
              iDestruct (path۰modelｰupdate _ _ _ _ height _ _ lvl prev prevs None with "[Hpreds] [Hsuccs] [//] [//] Hprevs_list Hlinks Hprevs [//]") as "Hpath"; first lia.
              { rewrite Nat2Z.id //. }
              { rewrite Nat2Z.id //. }
              iSplit; first done.
              iExists _, _. iFrame "Hpath". iPureIntro. intros _.
              rewrite list_lookup_insert decide_True //. lia.
            - wp۰pures.
              iModIntro. iSplit; first done.
              iExists prevs_list, links. iFrame "∗#". iSplit; first done. iPureIntro. lia.
          }

          wp۰pures.
          case_bool_decide as Hlow'.

          - wp۰pures.
            destruct lvl as [| lvl]; first lia.
            rewrite (_ : (⁺˖lvl - 1)%Z = ⁺lvl); first lia.
            wp۰apply ("IHfind_path_2" with "[$Hskiplist $Hkey $Hconv $Hroot_low $Hpath $Hcommit] HΦ").
            iSplitR; first (iPureIntro; lia).
            iApply (prevs۰modelｰmono with "Hprevs"). lia.

          - wp۰pures.
            iDestruct "Hpath" as "(Hpreds & Hsuccs & %Hprevs_list'_length & %Hlinks'_length & #Hprevs_list' & #Hlinks')".
            iModIntro. iApply "HΦ".
            iExists false, prevs_list', links'. iFrame "∗#%". iSplit; first done.
            iPureIntro. intros -> node Hlookup.
            assert (lvl = 0) as -> by lia.
            destruct (decide (0 < height)).
            + rewrite Hlinks'_lookup // in Hlookup.
            + apply lookup_lt_Some in Hlookup. lia.
        }
        iDestruct "Hlink" as "(%i & (#Hnodes_at & #Hnexts_inv & #Hkey') & %Hlvl)".

        wp۰rec.

        awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Hnexts_inv") without "HΦ"; first lia.
        iInv "Hinv" as "(:inv۰inner =1)".
        iDestruct (prev۰acc (PrevNode i) with "[] Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hnexts & Hclose)"; first done.
        { iExists node. iFrame "#". done. }
        iAaccIntro with "Hnexts".
        { iIntros "Hnexts !>".
          iDestruct "Hclose" as "(Hclose & _)".
          iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
          iSplitR "Hcommit Hpath"; last iFrame.
          iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%".
        }
        iIntros "%v (%Hlookup & Hnexts)".
        rewrite difference_empty_L.
        iDestruct "Hclose" as "(Hclose & _)".
        iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
        iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup.
        destruct (inv۰pureｰstatus_lookup lt Hinv1 i node) as (status & Hstatuses_lookup); first done.
        rewrite Nat2Z.id (prev۰slotsｰvals_node _ _ _ i node status) // /status۰vals list_lookup_imap in Hlookup.
        apply fmap_Some in Hlookup as (link & Hlinks_lookup & ->).
        pose proof (inv۰pure۰status Hinv1 _ _ _ Hnodes_lookup Hstatuses_lookup) as (Hheight & Hlength & Hmarked_le & Hlinks).
        pose proof (Hlinks _ _ Hlinks_lookup) as Hwf.
        iDestruct (link۰modelｰget with "Hnodes_auth Hnodes Hnodes_keys") as "(Hnodes_auth & Hnodes & Hlink)"; [done.. |].
        destruct (status۰is_marked node status lvl) eqn:Hmarked.

        + iDestruct (nodes۰modelｰmarks_at with "Hnodes") as "(Hnodes & #Hmarks_at)"; [done.. |].
          iSplitR "Hcommit Hlink Hpath". { iFrameSteps. }
          iIntros "!> H£ HΦ {Hnodes_keys}".
          iMod (lc_fupd_elim_later with "H£ Hlink") as "#Hlink".

          awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Hprevs_inv") without "HΦ"; first lia.
          iInv "Hinv" as "(:inv۰inner =2)".
          iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup2.
          destruct (inv۰pureｰstatus_lookup lt Hinv2 i node) as (status2 & Hstatuses2_lookup); first done.
          iDestruct (nodes۰modelｰmarks_valid with "Hnodes Hmarks_at") as "(Hnodes & %Hmarked2 & %Hlinks2_lookup)"; [done.. |].
          pose proof (inv۰pure۰status Hinv2 _ _ _ Hnodes_lookup2 Hstatuses2_lookup) as (_ & _ & Hmarked2_le & Hlinks2).
          iDestruct (prev۰acc with "Hprev_at Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hprevs_model & Hclose)"; first done.
          iAaccIntro with "Hprevs_model".
          { iIntros "Hprevs_model !>".
            iDestruct "Hclose" as "(Hclose & _)".
            iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
            iSplitR "Hcommit Hpath"; last iFrame.
            iExists nodes2, statuses2, bottom2, roots2, m2, waiters2. iFrame "∗#%".
          }
          iIntros "%b' %w (%Hlookup & %Hcas & Hprevs_model)".
          rewrite difference_empty_L.
          destruct b'.

          * rewrite Nat2Z.id list_lookup_fmap in Hlookup.
            apply fmap_Some in Hlookup as ((marked' & link') & Hslot & ->).
            pose proof (inv۰pureｰprev_slot lt Hinv2 _ _ _ _ Hslot) as Hwf'.
            iDestruct (slot۰to_valｰsimilar lvl marked' link' node Hinv2 Hwf' with "Hnexts_inv") as %(-> & ->).
            { eapply list_elem_of_lookup_2. done. }
            { exact Hcas. }
            destruct (prev۰update statuses2 roots2 prev lvl link) as (statuses' & roots') eqn:Hupdate.
            iDestruct "Hclose" as "(_ & Hclose)".
            iDestruct ("Hclose" with "[//] [//] [Hprevs_model]") as "(Hroot & Hnodes)".
            { rewrite Nat2Z.id //. }
            iDestruct (waiters۰modelｰmarked _ _ _ statuses' with "Hwaiters") as "Hwaiters".
            { symmetry. eapply prev۰updateｰmarked; done. }
            assert (∃ bottom', inv۰pure lt nodes2 statuses' bottom' roots' m2) as (bottom' & Hinv').
            { destruct lvl as [| lvl].
              - destruct (inv۰pureｰprev0 lt Hinv2 prev (Some node)) as (q & Hq & Hnode_q); first done.
                assert (status2.(status۰marked) = node.(node۰height)) as Hmarked0.
                { apply bool_decide_eq_true in Hmarked2. lia. }
                pose proof (inv۰pure۰bottom_links Hinv2 _ _ _ _ (eq_sym Hnode_q) Hnodes_lookup2 Hstatuses2_lookup) as Hlink_q.
                rewrite Hlinks2_lookup in Hlink_q. injection Hlink_q as ->.
                exists (delete q bottom2).
                apply (inv۰pureｰunlink0 lt Hinv2 prev q node i status2 statuses' roots' Hq (eq_sym Hnode_q) Hnodes_lookup2 Hstatuses2_lookup Hmarked0 Hupdate).
              - exists bottom2.
                eapply (inv۰pureｰset lt Hinv2 prev ˖lvl (Some node) link); [lia | done | | done].
                eapply Hlinks2. done.
            }
            iSplitR "Hcommit Hpath".
            { iIntros "!> !>". iExists nodes2, statuses', bottom', roots', m2, waiters2. iFrame "∗#%". }
            iIntros "!> _ HΦ".

            wp۰apply+ ("IHfind_path_1" with "[$Hskiplist $Hkey $Hconv $Hroot_low $Hprevs $Hpath $Hcommit] HΦ").
            iSplitR; first done.
            iRight. iExists link. iFrame "#". done.

          * iDestruct "Hclose" as "(Hclose & _)".
            iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
            iSplitR "Hcommit Hpath". { iFrameSteps. }
            iIntros "!> _ HΦ".

            wp۰apply+ ("IHfind_path_2" with "[$Hskiplist $Hkey $Hconv $Hroot_low $Hprevs $Hpath $Hcommit] HΦ").
            done.

        + pose proof (inv۰pureｰlive i node status lvl Hinv1 Hnodes_lookup Hstatuses_lookup Hmarked) as Hlive.
          iAssert (
            model₂ γ m1 ∗
            if decide (lvl = low ∧ node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦) then R else P
          )%I with "[> Hmodel₂ Hcommit]" as "(Hmodel₂ & Hcommit)".
          { case_decide as Hcase.
            - destruct Hcase as (_ & Hkey_eq).
              iApply ("Hconv" with "Hcommit [] Hmodel₂").
              iPureIntro. rewrite -Hkey_eq Hlive. done.
            - iFrame. done.
          }
          iSplitR "Hcommit Hlink Hpath". { iFrameSteps. }
          iIntros "!> H£ HΦ".
          iMod (lc_fupd_elim_later with "H£ Hlink") as "#Hlink".

          wp۰apply+ (wpｰwand with "(Hvalid_compare Hkey Hkey')") as (res) "(%cmp & -> & %Hcmp_lt & %Hcmp_eq & %Hcmp_gt)".
          wp۰pures.
          destruct (decide (0 < cmp)%Z) as [Hcmp | Hcmp].

          * rewrite bool_decide_eq_true_2 //.
            wp۰apply+ ("IHfind_path_1" $! lvl (PrevNode i) with "[$Hskiplist $Hkey $Hconv $Hroot_low $Hpath Hcommit] HΦ").
            specialize (Hcmp_gt Hcmp).
            iSplitR; first done.
            iSplitR.
            { iExists node.(node۰height). iFrame "#". iSplit; first done.
              iSplit; iPureIntro; done.
            }
            iSplitL.
            { case_decide as Hcase; last done.
              destruct Hcase as (_ & Hkey_eq).
              exfalso. rewrite Hkey_eq in Hcmp_gt. eapply (irreflexivity lt); done.
            }
            iRight. iExists link. iFrame "#". done.

          * rewrite bool_decide_eq_false_2 //.
            wp۰pures.
            iDestruct "Hpath" as "(:path۰model)".
            wp۰apply+ (array٠sizeｰspec with "Hpreds") as "Hpreds".
            wp۰pures.

            wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
            wp۰apply (wpｰwand (λ v,
              ⌜v = ()%V⌝ ∗
              ∃ prevs_list' links',
              path۰model γ 𝑘𝑒𝑦 preds succs height prevs_list' links' ∗
              ⌜lvl < height → links' !! lvl = Some (Some node)⌝
            )%I with "[Hpreds Hsuccs]") as "%v (-> & %prevs_list' & %links' & Hpath & %Hlinks'_lookup)".
            { case_bool_decide as Hlvl_height.
              - wp۰apply+ (array٠unsafe_setｰspec with "Hpreds") as "Hpreds"; first lia.
                wp۰apply+ (array٠unsafe_setｰspec _ _ _ (link۰to_val (Some node)) with "Hsuccs") as "Hsuccs".
                { rewrite length_fmap. lia. }
                iDestruct (path۰modelｰupdate _ _ _ _ height _ _ lvl prev prevs (Some node) with "[Hpreds] [Hsuccs] [//] [//] Hprevs_list Hlinks Hprevs []") as "Hpath"; first lia.
                { rewrite Nat2Z.id //. }
                { rewrite Nat2Z.id //. }
                { iExists i. iFrame "#". done. }
                iSplit; first done.
                iExists _, _. iFrame "Hpath". iPureIntro. intros _.
                rewrite list_lookup_insert decide_True //. lia.
              - wp۰pures.
                iModIntro. iSplit; first done.
                iExists prevs_list, links. iFrame "∗#". iSplit; first done. iPureIntro. lia.
            }

            wp۰pures.
            case_bool_decide as Hlow'.

            -- wp۰pures.
               destruct lvl as [| lvl]; first lia.
               rewrite (_ : (⁺˖lvl - 1)%Z = ⁺lvl); first lia.
               wp۰apply ("IHfind_path_2" with "[$Hskiplist $Hkey $Hconv $Hroot_low $Hpath Hcommit] HΦ").
               iSplitR; first (iPureIntro; lia).
               iSplitR. { iApply (prevs۰modelｰmono with "Hprevs"). lia. }
               rewrite decide_False //. lia.

            -- assert (lvl = low) as <- by lia.
               wp۰pures.
               iDestruct "Hpath" as "(Hpreds & Hsuccs & %Hprevs_list'_length & %Hlinks'_length & #Hprevs_list' & #Hlinks')".
               iModIntro. iApply "HΦ".
               destruct (decide (cmp = 0)) as [-> | Hcmp0].
               ++ specialize (Hcmp_eq eq_refl).
                  rewrite decide_True //.
                  iExists true, prevs_list', links'. iFrame "∗#%". done.
               ++ assert (cmp < 0)%Z as Hcmp' by lia.
                  specialize (Hcmp_lt Hcmp').
                  rewrite bool_decide_eq_false_2 //.
                  rewrite decide_False.
                  { intros (_ & Hkey_eq). rewrite Hkey_eq in Hcmp_lt. eapply (irreflexivity lt); done. }
                  iExists false, prevs_list', links'. iFrame "∗#%". iSplit; first done.
                  iPureIntro. intros -> node' Hlookup.
                  assert (0 < height) by (apply lookup_lt_Some in Hlookup; lia).
                  rewrite Hlinks'_lookup in Hlookup; first lia.
                  injection Hlookup as <-. done.
    }

    { iIntros "%lvl %prev %prevs %prevs_list %links !> %Φ (#Hskiplist & #Hkey & #Hconv & #Hroot_low & %Hlow & #Hprevs & Hpath & Hcommit) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".
      iPoseProof "Hprevs" as "(%sz' & #Hprevs_inv & %Hlvl & _)".
      iDestruct (prevs۰modelｰprev_at with "Hprevs") as "#Hprev_at".

      wp۰rec.
      awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Hprevs_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (prev۰acc with "Hprev_at Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hprevs_model & Hclose)"; first done.
      iAaccIntro with "Hprevs_model".
      { iIntros "Hprevs_model !>".
        iDestruct "Hclose" as "(Hclose & _)".
        iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
        iSplitR "Hpath Hcommit"; last iFrame.
        iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%".
      }
      iIntros "%v (%Hlookup & Hprevs_model)".
      rewrite difference_empty_L.
      iDestruct "Hclose" as "(Hclose & _)".
      iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
      rewrite Nat2Z.id list_lookup_fmap in Hlookup.
      apply fmap_Some in Hlookup as ((marked & link) & Hslot & ->).
      pose proof (inv۰pureｰprev_slot lt Hinv1 _ _ _ _ Hslot) as Hwf.
      iDestruct (link۰modelｰget with "Hnodes_auth Hnodes Hnodes_keys") as "(Hnodes_auth & Hnodes & Hlink)"; [done.. |].
      iSplitR "Hpath Hcommit Hlink".
      { iIntros "!> !>". iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
      iIntros "!> H£ HΦ".
      iMod (lc_fupd_elim_later with "H£ Hlink") as "#Hlink".

      wp۰apply ("IHfind_path_1" with "[$Hskiplist $Hkey $Hconv $Hroot_low $Hprevs $Hpath $Hcommit] HΦ").
      iSplitR; first done.
      destruct marked.
      - iLeft. iExists _. done.
      - iRight. iExists link. iFrame "#". done.
    }

    { iIntros "%prevs_list %links !> %Φ (#Hskiplist & #Hkey & #Hconv & (%sz' & #Hroot_inv' & %Hlow) & Hpath & Hcommit) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".
      iDestruct (array۰invｰagree with "Hroot_inv Hroot_inv'") as %<-.

      wp۰rec.
      wp۰apply+ (array٠sizeｰspecｰinv with "Hroot_inv") as "_".
      wp۰pures.
      rewrite (_ : (⁺sz - 1)%Z = ⁺(sz - 1)); first lia.
      wp۰apply ("IHfind_path_2" $! (sz - 1) PrevRoot with "[$Hskiplist $Hkey $Hconv $Hpath $Hcommit] HΦ").
      iSplitR. { iExists sz. iFrame "#". done. }
      iSplitR; first (iPureIntro; lia).
      iExists sz. iFrame "#". iSplit; first (iPureIntro; lia). done.
    }
  Qed.

  #[local] Lemma skiplist٠find_pathｰspec γ ι key 𝑘𝑒𝑦 preds succs height (low : nat) R P prevs_list links :
    {{{
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦 ∗
      □ (P -∗ find_path۰commit γ 𝑘𝑒𝑦 R) ∗
      ( ∃ sz,
        array۰inv γ.(skiplist۰name۰root) sz ∗
        ⌜low < sz⌝
      ) ∗
      path۰model γ 𝑘𝑒𝑦 preds succs height prevs_list links ∗
      P
    }}}
      skiplist٠find_path γ key preds succs #low
    {{{
      res
    , RET res;
      find_path۰post γ 𝑘𝑒𝑦 preds succs height low R P res
    }}}.
  Proof.
    iDestruct (skiplist٠find_path_1ｰfind_path_2ｰfind_pathｰspec γ ι key 𝑘𝑒𝑦 preds succs height low R P) as "(_ & _ & H)".
    iApply "H".
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [update_lvls] and [update_nexts]. *)

  #[local] Lemma link۰modelｰwf γ nodes lvl link :
    nodes۰auth γ nodes -∗
    link۰model γ lvl link -∗
    ⌜link۰wf nodes lvl link⌝.
  Proof.
    iIntros "Hnodes_auth Hlink".
    destruct link as [node |]; last done.
    iDestruct "Hlink" as "(%i & (#Hnodes_at & _) & %Hlvl)".
    iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hlookup.
    iPureIntro. split; last done.
    eapply list_elem_of_lookup_2. done.
  Qed.
  #[local] Lemma slot۰to_valｰsimilarｰlink marked link1 link2 :
    slot۰to_val marked link1 ≈ link۰to_val link2 →
    marked = false.
  Proof.
    destruct marked; last done.
    rewrite /node۰to_val.
    intros Hsimilar. exfalso.
    destruct link1, link2; rewrite /= ?/node۰to_val in Hsimilar; cbn in Hsimilar; destruct_and? Hsimilar; simplify_eq; done.
  Qed.

  #[local] Lemma skiplist٠update_lvlsｰupdate_nextsｰspec γ ι key 𝑘𝑒𝑦 preds succs i node :
    ⊢ (
      ∀ lvl prevs_list links,
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        node۰at γ i node ∗
        ( ∃ sz,
          array۰inv γ.(skiplist۰name۰root) sz ∗
          ⌜node.(node۰height) ≤ sz⌝
        ) ∗
        ⌜0 < lvl ≤ node.(node۰height)⌝ ∗
        path۰model γ 𝑘𝑒𝑦 preds succs node.(node۰height) prevs_list links
      }}}
        skiplist٠update_lvls γ key preds succs node.(node۰nexts) (node۰to_val node) #lvl
      {{{
        RET true;
        True
      }}}
    ) ∧ (
      ∀ lvl lvl' prevs_list links,
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        node۰at γ i node ∗
        ( ∃ sz,
          array۰inv γ.(skiplist۰name۰root) sz ∗
          ⌜node.(node۰height) ≤ sz⌝
        ) ∗
        ⌜0 < lvl ≤ S lvl'⌝ ∗
        ⌜lvl' < node.(node۰height)⌝ ∗
        path۰model γ 𝑘𝑒𝑦 preds succs node.(node۰height) prevs_list links
      }}}
        skiplist٠update_nexts γ key preds succs node.(node۰nexts) (node۰to_val node) #lvl #lvl'
      {{{
        RET true;
        True
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHupdate_lvls & IHupdate_nexts)".
    iSplit.

    { iIntros "%lvl %prevs_list %links !> %Φ (#Hskiplist & #Hkey & #Hnode_at & #Hroot_bound & %Hlvl & Hpath) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".
      iPoseProof "Hnode_at" as "(#Hnodes_at & #Hnexts_inv & #Hnode_key)".
      iAssert (prev۰at γ (PrevNode i) node.(node۰nexts))%I as "#Hprev_at".
      { iExists node. iFrame "#". done. }

      wp۰rec.
      wp۰apply+ (array٠sizeｰspecｰinv with "Hnexts_inv") as "_".
      wp۰pures.
      destruct (decide (lvl = node.(node۰height))) as [-> | Hlvl'].

      - rewrite bool_decide_eq_true_2 //.
        awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Hnexts_inv") without "HΦ"; first lia.
        iInv "Hinv" as "(:inv۰inner =1)".
        iDestruct (prev۰acc with "Hprev_at Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hnexts & Hclose)"; first done.
        iAaccIntro with "Hnexts".
        { iIntros "Hnexts !>".
          iDestruct "Hclose" as "(Hclose & _)".
          iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
          iSplitR "Hpath"; last iFrame.
          iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%".
        }
        iIntros "%v (%Hlookup & Hnexts)".
        iDestruct "Hclose" as "(Hclose & _)".
        iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
        rewrite list_lookup_fmap in Hlookup.
        apply fmap_Some in Hlookup as ((marked & link) & _ & ->).
        iSplitR "Hpath".
        { iIntros "!> !>". iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
        iIntros "!> _ HΦ".

        wp۰rec.
        destruct marked; wp۰pures.

        + wp۰apply (skiplist٠find_nodeｰspecｰcleanup with "[$Hskiplist $Hkey]") as (res) "_".
          wp۰pures.
          iApply "HΦ". done.

        + iApply "HΦ". done.

      - rewrite bool_decide_eq_false_2; first lia.
        iDestruct "Hpath" as "(:path۰model)".
        destruct (lookup_lt_is_Some_2 links lvl) as (link & Hlinks_lookup); first lia.
        destruct (lookup_lt_is_Some_2 prevs_list lvl) as (prevs & Hprevs_lookup); first lia.
        iDestruct (big_sepL_lookup with "Hlinks") as "#Hlink"; first done.
        iDestruct (big_sepL_lookup with "Hprevs_list") as "(%prev & #Hprevs)"; first done.
        wp۰apply+ (array٠unsafe_getｰspec lvl with "Hsuccs") as "Hsuccs"; [lia | | lia |].
        { rewrite list_lookup_fmap Hlinks_lookup //. }
        wp۰apply+ (array٠unsafe_getｰspec lvl with "Hpreds") as "Hpreds"; [lia | done | lia |].
        iPoseProof "Hprevs" as "(%sz' & #Hprevs_inv & %Hlvl'' & _)".
        iDestruct (prevs۰modelｰprev_at with "Hprevs") as "#Hprev_at'".
        awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Hprevs_inv") without "HΦ"; first lia.
        iInv "Hinv" as "(:inv۰inner =1)".
        iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup.
        iDestruct (link۰modelｰwf with "Hnodes_auth Hlink") as %Hlink_wf.
        iDestruct (prev۰acc with "Hprev_at' Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hprevs_model & Hclose)"; first done.
        iAaccIntro with "Hprevs_model".
        { iIntros "Hprevs_model !>".
          iDestruct "Hclose" as "(Hclose & _)".
          iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
          iSplitR "Hpreds Hsuccs"; last iFrame.
          iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%".
        }
        iIntros "%b' %w (%Hlookup & %Hcas & Hprevs_model)".
        rewrite difference_empty_L.
        destruct b'.

        + rewrite Nat2Z.id list_lookup_fmap in Hlookup.
          apply fmap_Some in Hlookup as ((marked' & link') & Hslot & ->).
          assert (marked' = false) as -> by (eapply slot۰to_valｰsimilarｰlink; exact Hcas).
          destruct (prev۰update statuses1 roots1 prev lvl (Some node)) as (statuses' & roots') eqn:Hupdate.
          iDestruct "Hclose" as "(_ & Hclose)".
          iDestruct ("Hclose" with "[//] [//] [Hprevs_model]") as "(Hroot & Hnodes)".
          { rewrite Nat2Z.id //. }
          iDestruct (waiters۰modelｰmarked _ _ _ statuses' with "Hwaiters") as "Hwaiters".
          { symmetry. eapply prev۰updateｰmarked; done. }
          assert (inv۰pure lt nodes1 statuses' bottom1 roots' m1) as Hinv'.
          { eapply (inv۰pureｰset lt Hinv1 prev lvl link' (Some node)); [lia | done | | done].
            split; last lia.
            eapply list_elem_of_lookup_2. done.
          }
          iSplitR "Hpreds Hsuccs".
          { iIntros "!> !>". iExists nodes1, statuses', bottom1, roots', m1, waiters1. iFrame "∗#%". }
          iIntros "!> _ HΦ".

          wp۰pures.
          rewrite (_ : (⁺lvl + 1)%Z = ⁺˖lvl); first lia.
          wp۰apply ("IHupdate_lvls" with "[$Hskiplist $Hkey $Hnode_at $Hroot_bound Hpreds Hsuccs] HΦ").
          iSplitR; first (iPureIntro; lia).
          iFrame "∗#%".

        + iDestruct "Hclose" as "(Hclose & _)".
          iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
          iSplitR "Hpreds Hsuccs".
          { iIntros "!> !>". iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
          iIntros "!> _ HΦ".

          iDestruct "Hroot_bound" as "(%sz'' & #Hroot_inv' & %Hheight)".
          iDestruct (array۰invｰagree with "Hroot_inv Hroot_inv'") as %<-.
          wp۰apply+ (skiplist٠find_pathｰspec γ _ key 𝑘𝑒𝑦 preds succs node.(node۰height) lvl True%I (find_path۰commit γ 𝑘𝑒𝑦 True) prevs_list links with "[$Hskiplist $Hkey Hpreds Hsuccs]") as (res) "(%b & %prevs_list' & %links' & -> & Hpath & _)".
          { iFrame "∗#%". iSplitR; first (iIntros "!> $").
            iSplitR; first (iPureIntro; lia).
            iIntros "%m _ Hmodel₂ !>". iFrame.
          }
          wp۰apply+ (array٠sizeｰspecｰinv with "Hnexts_inv") as "_".
          wp۰pures.
          rewrite (_ : (⁺node.(node۰height) - 1)%Z = ⁺(node.(node۰height) - 1)); first lia.
          wp۰apply ("IHupdate_nexts" with "[$Hskiplist $Hkey $Hnode_at Hpath] HΦ").
          iFrame. iSplitR.
          { iExists sz. iFrame "#". done. }
          iPureIntro. lia.
    }

    { iIntros "%lvl %lvl' %prevs_list %links !> %Φ (#Hskiplist & #Hkey & #Hnode_at & #Hroot_bound & %Hlvl & %Hlvl' & Hpath) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".
      iPoseProof "Hnode_at" as "(#Hnodes_at & #Hnexts_inv & #Hnode_key)".
      iAssert (prev۰at γ (PrevNode i) node.(node۰nexts))%I as "#Hprev_at".
      { iExists node. iFrame "#". done. }

      wp۰rec. wp۰pures.
      destruct (decide (lvl' < lvl)) as [Hlt | Hge].

      - rewrite bool_decide_eq_true_2; first lia.
        wp۰apply+ ("IHupdate_lvls" with "[$Hskiplist $Hkey $Hnode_at $Hroot_bound $Hpath] HΦ").
        iPureIntro. lia.

      - rewrite bool_decide_eq_false_2; first lia.
        awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Hnexts_inv") without "HΦ"; first lia.
        iInv "Hinv" as "(:inv۰inner =1)".
        iDestruct (prev۰acc with "Hprev_at Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hnexts & Hclose)"; first done.
        iAaccIntro with "Hnexts".
        { iIntros "Hnexts !>".
          iDestruct "Hclose" as "(Hclose & _)".
          iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
          iSplitR "Hpath"; last iFrame.
          iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%".
        }
        iIntros "%v (%Hlookup & Hnexts)".
        iDestruct "Hclose" as "(Hclose & _)".
        iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
        rewrite list_lookup_fmap in Hlookup.
        apply fmap_Some in Hlookup as ((marked & before) & _ & ->).
        iSplitR "Hpath".
        { iIntros "!> !>". iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
        iIntros "!> _ HΦ {Hnodes_keys}".

        destruct marked.

        + wp۰apply+ (skiplist٠find_nodeｰspecｰcleanup with "[$Hskiplist $Hkey]") as (res) "_".
          wp۰pures.
          iApply "HΦ". done.

        + iDestruct "Hpath" as "(:path۰model)".
          destruct (lookup_lt_is_Some_2 links lvl') as (link & Hlinks_lookup); first lia.
          iDestruct (big_sepL_lookup with "Hlinks") as "#Hlink"; first done.
          wp۰apply+ (array٠unsafe_getｰspec lvl' with "Hsuccs") as "Hsuccs"; [lia | | lia |].
          { rewrite list_lookup_fmap Hlinks_lookup //. }
          wp۰equal as _ | _.

          * awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Hnexts_inv") without "HΦ"; first lia.
            iInv "Hinv" as "(:inv۰inner =2)".
            iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup.
            iDestruct (link۰modelｰwf with "Hnodes_auth Hlink") as %Hlink_wf.
            iDestruct (prev۰acc with "Hprev_at Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hnexts & Hclose)"; first done.
            iAaccIntro with "Hnexts".
            { iIntros "Hnexts !>".
              iDestruct "Hclose" as "(Hclose & _)".
              iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
              iSplitR "Hpreds Hsuccs"; last iFrame.
              iExists nodes2, statuses2, bottom2, roots2, m2, waiters2. iFrame "∗#%".
            }
            iIntros "%b' %w (%Hlookup & %Hcas & Hnexts)".
            rewrite difference_empty_L.
            destruct b'.

            -- rewrite Nat2Z.id list_lookup_fmap in Hlookup.
               apply fmap_Some in Hlookup as ((marked' & link') & Hslot & ->).
               assert (marked' = false) as -> by (eapply slot۰to_valｰsimilarｰlink; exact Hcas).
               destruct (prev۰update statuses2 roots2 (PrevNode i) lvl' link) as (statuses' & roots') eqn:Hupdate.
               iDestruct "Hclose" as "(_ & Hclose)".
               iDestruct ("Hclose" with "[//] [//] [Hnexts]") as "(Hroot & Hnodes)".
               { rewrite Nat2Z.id //. }
               iDestruct (waiters۰modelｰmarked _ _ _ statuses' with "Hwaiters") as "Hwaiters".
               { symmetry. eapply prev۰updateｰmarked; done. }
               assert (inv۰pure lt nodes2 statuses' bottom2 roots' m2) as Hinv'.
               { eapply (inv۰pureｰset lt Hinv2 (PrevNode i) lvl' link' link); [lia | done | done | done]. }
               iSplitR "Hpreds Hsuccs".
               { iIntros "!> !>". iExists nodes2, statuses', bottom2, roots', m2, waiters2. iFrame "∗#%". }
               iIntros "!> _ HΦ".

               wp۰pures.
               destruct lvl' as [| lvl']; first lia.
               rewrite (_ : (⁺˖lvl' - 1)%Z = ⁺lvl'); first lia.
               wp۰apply ("IHupdate_nexts" with "[$Hskiplist $Hkey $Hnode_at $Hroot_bound Hpreds Hsuccs] HΦ").
               iFrame "∗#%". iPureIntro. lia.

            -- iDestruct "Hclose" as "(Hclose & _)".
               iDestruct ("Hclose" with "Hnexts") as "(Hroot & Hnodes)".
               iSplitR "Hpreds Hsuccs".
               { iIntros "!> !>". iExists nodes2, statuses2, bottom2, roots2, m2, waiters2. iFrame "∗#%". }
               iIntros "!> _ HΦ".

               wp۰apply+ ("IHupdate_lvls" with "[$Hskiplist $Hkey $Hnode_at $Hroot_bound Hpreds Hsuccs] HΦ").
               iFrame "∗#%". iPureIntro. lia.

          * wp۰pures.
            destruct lvl' as [| lvl']; first lia.
            rewrite (_ : (⁺˖lvl' - 1)%Z = ⁺lvl'); first lia.
            wp۰apply ("IHupdate_nexts" with "[$Hskiplist $Hkey $Hnode_at $Hroot_bound Hpreds Hsuccs] HΦ").
            iFrame "∗#%". iPureIntro. lia.
    }
  Qed.

  #[local] Lemma skiplist٠update_lvlsｰspec γ ι key 𝑘𝑒𝑦 preds succs i node lvl prevs_list links :
    {{{
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦 ∗
      node۰at γ i node ∗
      ( ∃ sz,
        array۰inv γ.(skiplist۰name۰root) sz ∗
        ⌜node.(node۰height) ≤ sz⌝
      ) ∗
      ⌜0 < lvl ≤ node.(node۰height)⌝ ∗
      path۰model γ 𝑘𝑒𝑦 preds succs node.(node۰height) prevs_list links
    }}}
      skiplist٠update_lvls γ key preds succs node.(node۰nexts) (node۰to_val node) #lvl
    {{{
      RET true;
      True
    }}}.
  Proof.
    iDestruct (skiplist٠update_lvlsｰupdate_nextsｰspec γ ι key 𝑘𝑒𝑦 preds succs i node) as "(H & _)".
    iApply "H".
  Qed.

  #[local] Lemma waiters۰modelｰapp γ nodes statuses node status waiters :
    length statuses = length nodes →
    status.(status۰marked) ≠ node.(node۰height) →
    ( [∗ map] η ↦ waiter ∈ waiters,
      waiter۰model γ nodes statuses η waiter
    ) ⊢
    [∗ map] η ↦ waiter ∈ waiters,
    waiter۰model γ (nodes ++ [node]) (statuses ++ [status]) η waiter.
  Proof.
    iIntros "%Hlength %Hmarked Hwaiters".
    iApply (big_sepM_impl with "Hwaiters"). iIntros "!> %η %waiter _ (%Ψ & Hη & HΨ)".
    iExists Ψ. iFrame.
    rewrite waiter۰doneｰapp //.
  Qed.

  #[local] Lemma link۰to_valｰsimilarｰnull link :
    link۰to_val link ≈ §skiplist٠Null%V →
    link = None.
  Proof.
    destruct link as [node |]; last done.
    intros Hsimilar. exfalso.
    by eapply valｰsimilarｰblockｰempty₂.
  Qed.

  #[local] Lemma status۰valsｰunmarked node links :
    length links = node.(node۰height) →
    status۰vals node (Status links 0) = link۰to_val <$> links.
  Proof.
    intros Hlength.
    rewrite /status۰vals /=.
    apply list_eq. intros lvl.
    rewrite list_lookup_imap list_lookup_fmap.
    destruct (links !! lvl) as [link |] eqn:Hlookup; last done.
    apply lookup_lt_Some in Hlookup.
    rewrite /status۰is_marked bool_decide_eq_false_2 //. simpl. lia.
  Qed.

  #[local] Lemma nodes۰modelｰfresh nodes statuses nexts vs :
    0 < length vs →
    array۰model nexts (DfracOwn 1) vs -∗
    nodes۰model nodes statuses -∗
      array۰model nexts (DfracOwn 1) vs ∗
      nodes۰model nodes statuses ∗
      ⌜nexts ∉ node۰nexts <$> nodes⌝.
  Proof.
    iIntros "%Hvs Hnexts Hnodes".
    iAssert ⌜
      ∀ node,
      node ∈ nodes →
      nexts ≠ node.(node۰nexts)
    ⌝%I as %Hne.
    { iIntros "%node %Hnode".
      apply list_elem_of_lookup in Hnode as (i & Hlookup).
      iDestruct (big_sepL2_length with "Hnodes") as %Hlength.
      destruct (lookup_lt_is_Some_2 statuses i) as (status & Hstatus).
      { rewrite -Hlength. eapply lookup_lt_Some. done. }
      iDestruct (big_sepL2_lookup with "Hnodes") as "(Hnexts' & _)"; [done.. |].
      iApply (array۰modelｰne with "Hnexts Hnexts'"). done.
    }
    iFrame. iPureIntro.
    intros (node & -> & Hnode)%list_elem_of_fmap.
    apply (Hne node); done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [add]. *)

  #[local] Lemma links۰modelｰwf γ nodes links :
    nodes۰auth γ nodes -∗
    ( [∗ list] lvl ↦ link ∈ links,
      link۰model γ lvl link
    ) -∗
    ⌜ ∀ lvl link,
      links !! lvl = Some link →
      link۰wf nodes lvl link
    ⌝.
  Proof.
    iIntros "Hnodes_auth #Hlinks".
    iEval (rewrite bi.pure_forall). iIntros "%lvl".
    iEval (rewrite bi.pure_forall). iIntros "%link".
    iApply bi.pure_impl_2. iIntros "%Hlookup".
    iApply (link۰modelｰwf with "Hnodes_auth").
    iApply (big_sepL_lookup with "Hlinks"). done.
  Qed.

  #[local] Lemma skiplist٠add₁ｰspec γ ι key 𝑘𝑒𝑦 v (preds succs : val) height prevs_list links :
    0 < height →
    <<<
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦 ∗
      ( ∃ sz,
        array۰inv γ.(skiplist۰name۰root) sz ∗
        ⌜height ≤ sz⌝
      ) ∗
      path۰model γ 𝑘𝑒𝑦 preds succs height prevs_list links
    | ∀∀ m,
      skiplist۰model γ m
    >>>
      skiplist٠add₁ γ key v preds succs
      @ ↑ι
    <<<
      skiplist۰model γ (if decide (𝑘𝑒𝑦 ∈ dom m) then m else <[𝑘𝑒𝑦 := v]> m)
    | RET #(bool_decide (𝑘𝑒𝑦 ∉ dom m));
      True
    >>>.
  Proof.
    iIntros "%Hheight %Φ (#Hskiplist & #Hkey & #Hroot_bound & Hpath) HΦ".
    iPoseProof "Hskiplist" as "(:inv)".
    pose proof (Hvalid_order : StrictOrder lt) as Horder.
    iDestruct "Hroot_bound" as "(%sz' & #Hroot_inv' & %Hheight')".
    iDestruct (array۰invｰagree with "Hroot_inv Hroot_inv'") as %<-.

    iLöb as "HLöb" forall (prevs_list links).

    wp۰rec.
    iRevert "HΦ".
    match goal with
    | |- environments.envs_entails _ (bi_wand ?P _) =>
        set Pau := P
    end.
    iIntros "HΦ".
    wp۰apply+ (skiplist٠find_pathｰspec γ _ key 𝑘𝑒𝑦 preds succs height 0 (Φ false%V) Pau prevs_list links with "[$Hskiplist $Hkey $Hpath $HΦ]") as (res) "(%b & %prevs_list' & %links' & -> & Hpath & HΦ)".
    { iSplitR.
      - iIntros "!> HΦ %m %Hm Hmodel₂".
        iMod "HΦ" as "(%m' & (:model) & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
        { rewrite decide_True //. apply elem_of_dom. done. }
        iFrame.
        rewrite bool_decide_eq_false_2.
        { intros Hn. apply Hn, elem_of_dom. done. }
        iApply "HΦ". done.
      - iExists sz. iFrame "#". iPureIntro. lia.
    }
    destruct b.

    - wp۰pures. done.

    - iDestruct "HΦ" as "(HΦ & %Hbound)".
      specialize (Hbound eq_refl).
      wp۰pures.
      iDestruct "Hpath" as "(:path۰model)".
      wp۰apply+ (array٠sizeｰspec with "Hsuccs") as "Hsuccs".
      rewrite length_fmap Hlinks_length.
      wp۰apply+ (array٠initiｰspec (λ _ i vs,
        array۰model succs (DfracOwn 1) (link۰to_val <$> links') ∗
        ⌜vs = take i (link۰to_val <$> links')⌝
      )%I with "[Hsuccs]") as (nexts vs) "(_ & %Hvs_length & Hnexts & Hsuccs & %Hvs)".
      { iSplitL.
        - iIntros "!> %t !>". iFrame. done.
        - iIntros "!> %t %i %vs %Hi _ (Hsuccs & ->)".
          destruct (lookup_lt_is_Some_2 (link۰to_val <$> links') i) as (w & Hw).
          { rewrite length_fmap. lia. }
          wp۰apply+ (array٠unsafe_getｰspec with "Hsuccs"); [lia | done | lia |].
          iSteps. iPureIntro.
          rewrite (take_S_r _ _ w) //.
      }
      rewrite Nat2Z.id firstn_all2 in Hvs; first (rewrite length_fmap; lia).
      subst vs.
      iMod (mono_listｰalloc []) as "(%γ_marks & Hmarks)".
      set node := Node key 𝑘𝑒𝑦 v nexts height γ_marks.
      wp۰pures.
      destruct (lookup_lt_is_Some_2 links' 0) as (link0 & Hlink0); first lia.
      destruct (lookup_lt_is_Some_2 prevs_list' 0) as (prevs & Hprevs_lookup); first lia.
      iDestruct (big_sepL_lookup with "Hlinks") as "#Hlink0"; first done.
      iDestruct (big_sepL_lookup with "Hprevs_list") as "(%prev & #Hprevs)"; first done.
      wp۰apply+ (array٠unsafe_getｰspec 0 with "Hsuccs") as "Hsuccs"; [lia | | lia |].
      { rewrite list_lookup_fmap Hlink0 //. }
      wp۰apply+ (array٠unsafe_getｰspec 0 with "Hpreds") as "Hpreds"; [lia | done | lia |].
      iPoseProof "Hprevs" as "(%sz'' & #Hprevs_inv & %Hlvl'' & _)".
      iDestruct (prevs۰modelｰprev_at with "Hprevs") as "#Hprev_at".
      iDestruct (array۰modelｰtoｰinv with "Hnexts") as "#Hnexts_inv".

      awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Hprevs_inv") without "Hpreds Hsuccs"; first lia.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (links۰modelｰwf with "Hnodes_auth Hlinks") as %Hlinks_wf.
      iDestruct (nodes۰modelｰfresh with "Hnexts Hnodes") as "(Hnexts & Hnodes & %Hfresh)".
      { rewrite length_fmap. lia. }
      iDestruct (prevs۰modelｰlt with "Hnodes_auth Hprevs") as %Hprev_lt.
      assert (∀ node', link0 = Some node' → node' ∈ nodes1) as Hlink0_in.
      { intros node' ->. apply (Hlinks_wf 0 (Some node') Hlink0). }
      iDestruct (prev۰acc with "Hprev_at Hnodes_auth Hroot Hnodes") as "(Hnodes_auth & Hprevs_model & Hclose)"; first done.
      iAaccIntro with "Hprevs_model".
      { iIntros "Hprevs_model !>".
        iDestruct "Hclose" as "(Hclose & _)".
        iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
        iSplitR "HΦ Hnexts Hmarks"; last iFrame.
        iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%".
      }
      iIntros "%b' %w (%Hlookup & %Hcas & Hprevs_model)".
      rewrite difference_empty_L.
      destruct b'.

      + rewrite list_lookup_fmap in Hlookup.
        apply fmap_Some in Hlookup as ((marked' & link') & Hslot & ->).
        assert (marked' = false) as -> by (eapply slot۰to_valｰsimilarｰlink; exact Hcas).
        pose proof (inv۰pureｰprev_slot lt Hinv1 _ _ _ _ Hslot) as Hwf'.
        iAssert ⌜link' = link0⌝%I as %->.
        { destruct link0 as [node0 |].
          - iDestruct "Hlink0" as "(%j & (_ & #Hnexts0_inv & _) & _)".
            iApply (link۰to_valｰsimilar with "Hnexts0_inv"); [done | done | | exact Hcas].
            apply Hlink0_in. done.
          - iPureIntro. apply link۰to_valｰsimilarｰnull. exact Hcas.
        }
        destruct (inv۰pureｰprev0 lt Hinv1 prev link0) as (q & Hq & Hlink0_q); first done.
        destruct (prev۰update statuses1 roots1 prev 0 (Some node)) as (statuses' & roots') eqn:Hupdate.
        opose proof* (inv۰pureｰinsert0 lt Hinv1 prev q node (Status links' 0) statuses' roots') as (Hm & Hinv'); try done.
        { intros k pred -> Hpred.
          destruct prev as [| i]; simpl in Hq; first lia.
          destruct Hq as (k' & pred' & Hpred' & Hpred'' & [= ->]).
          assert (pred' = pred) as -> by congruence.
          eapply Hprev_lt; done.
        }
        { intros succ Hsucc. apply Hbound. rewrite Hlink0 Hlink0_q Hsucc //. }
        { split_and!; simpl; try done; lia. }
        { rewrite /= Hlink0 Hlink0_q //. }
        iDestruct "Hclose" as "(_ & Hclose)".
        iDestruct ("Hclose" with "[//] [//] [Hprevs_model]") as "(Hroot & Hnodes)".
        { done. }
        iMod (nodesｰupdate node with "Hnodes_auth") as "(Hnodes_auth & #Hnodes_at)".
        iMod "HΦ" as "(%m' & (:model) & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod (modelｰupdate (<[𝑘𝑒𝑦 := v]> m1) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
        { rewrite decide_False //. apply not_elem_of_dom. done. }
        iDestruct (waiters۰modelｰmarked _ _ _ statuses' with "Hwaiters") as "Hwaiters".
        { symmetry. eapply prev۰updateｰmarked; done. }
        iDestruct (waiters۰modelｰapp _ _ _ node (Status links' 0) with "Hwaiters") as "Hwaiters"; [| simpl; lia |].
        { destruct prev; injection Hupdate as <- <-; rewrite ?length_alter; apply Hinv1. }
        iSplitR "HΦ".
        { iIntros "!> !>".
          iExists (nodes1 ++ [node]), (statuses' ++ [Status links' 0]), _, roots', (<[𝑘𝑒𝑦 := v]> m1), waiters1.
          iFrame "∗#%".
          rewrite big_sepL2_singleton status۰valsｰunmarked; first done.
          rewrite /marks۰auth /status۰frozen /= Nat.sub_0_r drop_ge; first lia.
          iFrame.
        }
        iIntros "!> _ (Hpreds & Hsuccs)".

        wp۰apply+ (skiplist٠update_lvlsｰspec _ _ key 𝑘𝑒𝑦 preds succs (length nodes1) node 1 prevs_list' links' with "[Hpreds Hsuccs]") as "_".
        { rewrite length_fmap Hlinks_length.
          iFrame "∗#%".
          iSplit; iPureIntro; [done | simpl; lia].
        }
        assert (bool_decide (𝑘𝑒𝑦 ∉ dom m1) = true) as Heq.
        { apply bool_decide_eq_true_2, not_elem_of_dom. done. }
        iEval (rewrite Heq) in "HΦ".
        iApply "HΦ". done.

      + iDestruct "Hclose" as "(Hclose & _)".
        iDestruct ("Hclose" with "Hprevs_model") as "(Hroot & Hnodes)".
        iSplitR "HΦ Hnexts Hmarks".
        { iIntros "!> !>". iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
        iIntros "!> _ (Hpreds & Hsuccs)".

        wp۰apply+ ("HLöb" with "[Hpreds Hsuccs] HΦ").
        iFrame "∗#%".
  Qed.

  Lemma skiplist٠addｰspec γ ι key 𝑘𝑒𝑦 v :
    <<<
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      skiplist۰model γ m
    >>>
      skiplist٠add γ key v
      @ ↑ι
    <<<
      skiplist۰model γ (if decide (𝑘𝑒𝑦 ∈ dom m) then m else <[𝑘𝑒𝑦 := v]> m)
    | RET #(bool_decide (𝑘𝑒𝑦 ∉ dom m));
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hskiplist & #Hkey) HΦ".
    iPoseProof "Hskiplist" as "(:inv)".

    wp۰rec.
    wp۰apply+ (array٠sizeｰspecｰinv with "Hroot_inv") as "_".
    wp۰apply+ (skiplist٠random_heightｰspec with "[//]") as (height) "%Hheight"; first lia.
    wp۰apply+ (array٠makeｰspec with "[//]") as (preds) "(_ & Hpreds)".
    wp۰apply+ (array٠makeｰspec with "[//]") as (succs) "(_ & Hsuccs)".
    iEval (rewrite Nat2Z.id) in "Hpreds Hsuccs".
    wp۰apply+ (skiplist٠add₁ｰspec γ _ key 𝑘𝑒𝑦 v preds succs height (replicate height γ.(skiplist۰name۰root)) (replicate height None) with "[$Hskiplist $Hkey Hpreds Hsuccs] HΦ"); first lia.
    iSplitR. { iExists sz. iFrame "#". iPureIntro. lia. }
    rewrite /path۰model fmap_replicate. iFrame.
    rewrite !length_replicate.
    iSplit; first done. iSplit; first done.
    iSplit.
    - iApply big_sepL_intro. iIntros "!> %lvl %prevs %Hlookup".
      apply lookup_replicate in Hlookup as (-> & Hlvl).
      iExists PrevRoot, sz. iFrame "#". iPureIntro. split; [lia | done].
    - iApply big_sepL_intro. iIntros "!> %lvl %link %Hlookup".
      apply lookup_replicate in Hlookup as (-> & _). done.
  Qed.

  #[local] Lemma status۰valsｰmark node status lvl link :
    length status.(status۰links) = node.(node۰height) →
    status.(status۰marked) = node.(node۰height) - S lvl →
    lvl < node.(node۰height) →
    status.(status۰links) !! lvl = Some link →
    status۰vals node (Status status.(status۰links) (S status.(status۰marked))) =
    <[lvl := slot۰to_val true link]> (status۰vals node status).
  Proof.
    intros Hlength Hmarked Hlvl Hlink.
    apply list_eq. intros j.
    rewrite list_lookup_insert /status۰vals !list_lookup_imap length_imap /=.
    case_decide as Hcase.
    - destruct Hcase as (<- & _).
      rewrite Hlink /= /status۰is_marked bool_decide_eq_true_2 //. simpl. lia.
    - destruct (status.(status۰links) !! j) as [link' |] eqn:Hlookup; last done.
      apply lookup_lt_Some in Hlookup.
      assert (j ≠ lvl) by (intros ->; apply Hcase; split; [done | lia]).
      rewrite /= /status۰is_marked /=.
      repeat f_equal.
      apply bool_decide_ext. lia.
  Qed.

  #[local] Lemma waiters۰modelｰcommit γ nodes statuses statuses' waiters m (node : node Key) :
    ( ∀ waiter,
      waiter۰done nodes statuses' waiter = true →
        waiter۰done nodes statuses waiter = true
      ∨ waiter.(waiter۰target) = node۰to_val node ∧
        waiter.(waiter۰𝑘𝑒𝑦) = node.(node۰𝑘𝑒𝑦)
    ) →
    ( ∀ waiter,
      waiter۰done nodes statuses waiter = true →
      waiter۰done nodes statuses' waiter = true
    ) →
    m !! node.(node۰𝑘𝑒𝑦) = None →
    model₂ γ m -∗
    ( [∗ map] η ↦ waiter ∈ waiters,
      waiter۰model γ nodes statuses η waiter
    ) ={⊤ ∖ ↑γ.(skiplist۰name۰inv)}=∗
      model₂ γ m ∗
      [∗ map] η ↦ waiter ∈ waiters,
      waiter۰model γ nodes statuses' η waiter.
  Proof.
    iIntros "%Hdone' %Hdone %Hm Hmodel₂ Hwaiters".
    iInduction waiters as [| η waiter waiters Hη] "IH" using map_ind.
    { iFrame. rewrite !big_sepM_empty. done. }
    rewrite !big_sepM_insert //.
    iDestruct "Hwaiters" as "((%Ψ & #Hη & HΨ) & Hwaiters)".
    iAssert (
      model₂ γ m ∗
      waiter۰model γ nodes statuses' η waiter
    )%I with "[> Hmodel₂ HΨ]" as "(Hmodel₂ & $)".
    { rewrite /waiter۰model.
      destruct (waiter۰done nodes statuses' waiter) eqn:Hnew.
      - destruct (waiter۰done nodes statuses waiter) eqn:Hold.
        { iModIntro. iFrame "∗#". iExact "HΨ". }
        destruct (Hdone' waiter Hnew) as [Hold' | (Htarget & Hwaiter_key)]; first congruence.
        iMod "HΨ" as "(%m' & Hmodel₁ & _ & HΨ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "[Hmodel₁]") as "HΨ".
        { rewrite delete_id //. rewrite Hwaiter_key //. }
        iFrame "∗#".
        rewrite bool_decide_eq_false_2 //.
        rewrite Hwaiter_key. apply not_elem_of_dom. done.
      - destruct (waiter۰done nodes statuses waiter) eqn:Hold; last (iModIntro; iFrame "∗#"; iExact "HΨ").
        rewrite Hdone // in Hnew.
    }
    iApply ("IH" with "Hmodel₂ Hwaiters").
  Qed.

  #[local] Lemma waiters۰modelｰmark_partial γ nodes statuses i node status marked waiters :
    length statuses = length nodes →
    nodes !! i = Some node →
    statuses !! i = Some status →
    status.(status۰marked) < node.(node۰height) →
    marked < node.(node۰height) →
    ( [∗ map] η ↦ waiter ∈ waiters,
      waiter۰model γ nodes statuses η waiter
    ) ⊢
    [∗ map] η ↦ waiter ∈ waiters,
    waiter۰model γ nodes (<[i := Status status.(status۰links) marked]> statuses) η waiter.
  Proof.
    iIntros "%Hlength %Hnodes_lookup %Hstatuses_lookup %Hmarked %Hmarked' Hwaiters".
    iApply (big_sepM_impl with "Hwaiters"). iIntros "!> %η %waiter _ (%Ψ & Hη & HΨ)".
    iExists Ψ. iFrame.
    rewrite (waiter۰doneｰmark_partial lt nodes statuses i node status) //.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [remove]. *)

  #[local] Definition remove۰waiter γ η node 𝑘𝑒𝑦 (Ψ : bool → iProp Σ) : iProp Σ :=
    waiters۰elem γ η (Waiter (node۰to_val node) 𝑘𝑒𝑦) ∗
    saved_pred η Ψ.

  #[local] Lemma skiplist٠remove_1ｰremove_2ｰspec γ ι key 𝑘𝑒𝑦 i node η (Ψ : bool → iProp Σ) :
    node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦 →
    ⊢ (
      ∀ lvl succ,
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        node۰at γ i node ∗
        ⌜lvl < node.(node۰height)⌝ ∗
        ( ⌜S lvl = node.(node۰height)⌝
        ∨ ∃ link,
          marks۰at node (S lvl) link
        ) ∗
        ( ( ∃ v,
            ⌜succ = ‘skiplist٠Mark( v )%V⌝
          ) ∗
          ( ⌜lvl = 0⌝ ∗
            Ψ false
          ∨ ⌜0 < lvl⌝ ∗
            ( ∃ link,
              marks۰at node lvl link
            ) ∗
            remove۰waiter γ η node 𝑘𝑒𝑦 Ψ
          )
        ∨ ∃ link,
          ⌜succ = link۰to_val link⌝ ∗
          link۰model γ lvl link ∗
          remove۰waiter γ η node 𝑘𝑒𝑦 Ψ
        )
      }}}
        skiplist٠remove_1 γ key node.(node۰nexts) #lvl succ
      {{{
        (b : bool)
      , RET #b;
        Ψ b
      }}}
    ) ∧ (
      ∀ lvl,
      {{{
        skiplist۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        node۰at γ i node ∗
        ⌜lvl < node.(node۰height)⌝ ∗
        ( ⌜S lvl = node.(node۰height)⌝
        ∨ ∃ link,
          marks۰at node (S lvl) link
        ) ∗
        remove۰waiter γ η node 𝑘𝑒𝑦 Ψ
      }}}
        skiplist٠remove_2 γ key node.(node۰nexts) #lvl
      {{{
        (b : bool)
      , RET #b;
        Ψ b
      }}}
    ).
  Proof.
    intros Hkey_eq.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHremove_1 & IHremove_2)".
    iSplit.

    { iIntros "%lvl %succ !> %Φ (#Hskiplist & #Hkey & #Hnode_at & %Hlvl & #Hmarked_above & Hsucc) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".
      pose proof (Hvalid_order : StrictOrder lt) as Horder.
      iPoseProof "Hnode_at" as "(#Hnodes_at & #Hnexts_inv & #Hnode_key)".
      iDestruct "Hsucc" as "[((%v & ->) & [(-> & HΨ) | (%Hlvl0 & #Hmarked & Hwaiter)]) | (%link & -> & #Hlink & Hwaiter)]".

      - wp۰rec. wp۰pures.
        iApply "HΦ". done.

      - wp۰rec. wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰pures.
        destruct lvl as [| lvl]; first lia.
        rewrite (_ : (⁺˖lvl - 1)%Z = ⁺lvl); first lia.
        wp۰apply ("IHremove_2" with "[$Hskiplist $Hkey $Hnode_at $Hwaiter] HΦ").
        iSplit; first (iPureIntro; lia).
        iRight. done.

      - iDestruct "Hwaiter" as "(Hwaiters_elem & #Hη)".
        wp۰rec credit:"H£".

        awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Hnexts_inv") without "HΦ"; first lia.
        iInv "Hinv" as "(:inv۰inner =1)".
        iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup.
        destruct (inv۰pureｰstatus_lookup lt Hinv1 i node) as (status & Hstatuses_lookup); first done.
        pose proof (inv۰pure۰status Hinv1 _ _ _ Hnodes_lookup Hstatuses_lookup) as (Hheight & Hlength & Hmarked_le & Hlinks).
        iAssert (
          nodes۰model nodes1 statuses1 ∗
          ⌜node.(node۰height) - status.(status۰marked) ≤ S lvl⌝
        )%I with "[Hnodes]" as "(Hnodes & %Habove)".
        { iDestruct "Hmarked_above" as "[% | (%link' & Hmarks_at)]".
          - iFrame. iPureIntro. lia.
          - destruct (decide (S lvl < node.(node۰height))).
            + iDestruct (nodes۰modelｰmarks_valid with "Hnodes Hmarks_at") as "($ & %Hm & _)"; [done.. |].
              rewrite /status۰is_marked bool_decide_eq_true in Hm. iPureIntro. lia.
            + iFrame. iPureIntro. lia.
        }
        iAssert ⌜link۰wf nodes1 lvl link⌝%I as %Hlink_wf.
        { iApply (link۰modelｰwf with "Hnodes_auth Hlink"). }
        iDestruct (big_sepL2_insert_acc with "Hnodes") as "((Hnexts & Hmarks) & Hnodes)"; [done.. |].
        iAaccIntro with "Hnexts".
        { iIntros "Hnexts !>".
          iDestruct ("Hnodes" with "[$Hnexts $Hmarks]") as "Hnodes".
          rewrite !list_insert_id //.
          iSplitR "Hwaiters_elem H£"; last iFrame.
          iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%".
        }
        iIntros "%b %w (%Hlookup & %Hcas & Hnexts)".
        rewrite difference_empty_L.
        destruct b.

        + rewrite Nat2Z.id /status۰vals list_lookup_imap in Hlookup.
          apply fmap_Some in Hlookup as (link' & Hlinks_lookup & ->).
          assert (status۰is_marked node status lvl = false) as Hunmarked.
          { eapply slot۰to_valｰsimilarｰlink. exact Hcas. }
          rewrite Hunmarked in Hcas.
          iAssert ⌜link' = link⌝%I as %->.
          { destruct link as [node' |].
            - iDestruct "Hlink" as "(%j & (_ & #Hnexts'_inv & _) & _)".
              iApply (link۰to_valｰsimilar with "Hnexts'_inv"); [done | eapply Hlinks; done | | exact Hcas].
              apply Hlink_wf.
            - iPureIntro. apply link۰to_valｰsimilarｰnull. exact Hcas.
          }
          assert (status.(status۰marked) = node.(node۰height) - S lvl) as Hmarked.
          { rewrite /status۰is_marked bool_decide_eq_false in Hunmarked. lia. }
          iEval (rewrite Nat2Z.id -(status۰valsｰmark node status lvl link) //) in "Hnexts".
          iMod (marksｰupdate with "Hmarks") as "Hmarks"; [done | lia |].
          iDestruct ("Hnodes" with "[$Hnexts $Hmarks]") as "Hnodes".
          rewrite list_insert_id //.
          pose proof (inv۰pureｰmark lt Hinv1 i node status lvl Hnodes_lookup Hstatuses_lookup ltac:(lia) Hmarked) as Hinv'.
          iDestruct (nodes۰modelｰmarks_at i node (Status status.(status۰links) (S status.(status۰marked))) lvl link Hinv' Hnodes_lookup with "Hnodes") as "(Hnodes & #Hmarks_at)"; [| | done |].
          { rewrite list_lookup_insert decide_True //. split; first done. eapply lookup_lt_Some. done. }
          { rewrite /status۰is_marked bool_decide_eq_true /=. lia. }
          destruct lvl as [| lvl].

          * pose proof (inv۰pureｰlive i node status 0 Hinv1 Hnodes_lookup Hstatuses_lookup Hunmarked) as Hlive.
            iMod (lc_fupd_elim_later with "H£ Hwaiters") as "Hwaiters".
            iDestruct (waiters۰elemｰvalid with "Hwaiters_auth Hwaiters_elem") as %Hwaiters_lookup.
            iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ' & #Hη' & HΨ') & Hwaiters)"; first done.
            destruct (waiter۰done nodes1 statuses1 (Waiter (node۰to_val node) 𝑘𝑒𝑦)) eqn:Hdone.
            { exfalso.
              pose proof (inv۰pure۰length Hinv1) as Hlen.
              rewrite waiter۰doneｰspec // in Hdone.
              destruct Hdone as (j & node' & status' & Hnodes_lookup' & Hstatuses_lookup' & Htarget & _ & Hmarked').
              simpl in Htarget.
              assert (node' = node) as ->.
              { eapply (inv۰pureｰnexts_inj lt Hinv1).
                - eapply list_elem_of_lookup_2. done.
                - eapply list_elem_of_lookup_2. done.
                - rewrite /node۰to_val in Htarget. congruence.
              }
              pose proof (inv۰pureｰindex_inj lt Hinv1 _ _ _ Hnodes_lookup Hnodes_lookup') as <-.
              assert (status' = status) as -> by congruence.
              lia.
            }
            iMod "HΨ'" as "(%m' & Hmodel₁ & _ & HΨ')".
            iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
            iMod (modelｰupdate (delete 𝑘𝑒𝑦 m1) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
            iMod ("HΨ'" with "Hmodel₁") as "HΨ'".
            iMod (waitersｰdelete with "Hwaiters_auth Hwaiters_elem") as "Hwaiters_auth".
            iMod (waiters۰modelｰcommit _ nodes1 statuses1 (<[i := Status status.(status۰links) (S status.(status۰marked))]> statuses1) (delete η waiters1) (delete 𝑘𝑒𝑦 m1) node with "Hmodel₂ Hwaiters") as "(Hmodel₂ & Hwaiters)".
            { rewrite (_ : S status.(status۰marked) = node.(node۰height)); first lia.
              intros waiter. apply (waiter۰doneｰmark lt nodes1 statuses1 i node status); try done; first apply Hinv1. lia.
            }
            { rewrite (_ : S status.(status۰marked) = node.(node۰height)); first lia.
              intros waiter. apply (waiter۰doneｰmark lt nodes1 statuses1 i node status); try done; first apply Hinv1. lia.
            }
            { rewrite Hkey_eq lookup_delete_eq //. }
            iSplitR "HΨ'".
            { iIntros "!> !>".
              iExists nodes1, _, bottom1, roots1, (delete 𝑘𝑒𝑦 m1), (delete η waiters1).
              simpl in Hinv'. rewrite Hkey_eq in Hinv'.
              iFrame "∗#%".
            }
            iIntros "!> H£' HΦ".
            iDestruct (saved_predｰagree true with "Hη Hη'") as "Hagree".
            iMod (lc_fupd_elim_later with "H£' Hagree") as "Hagree'".
            rewrite bool_decide_eq_true_2.
            { apply elem_of_dom. rewrite -Hkey_eq Hlive. done. }
            iRewrite -"Hagree'" in "HΨ'".

            wp۰apply+ (skiplist٠find_nodeｰspecｰcleanup with "[$Hskiplist $Hkey]") as (res) "_".
            wp۰pures.
            iApply "HΦ". done.

          * iDestruct (waiters۰modelｰmark_partial _ _ _ i node status (S status.(status۰marked)) with "Hwaiters") as "Hwaiters"; [apply Hinv1 | done.. | lia | lia |].
            iSplitR "Hwaiters_elem".
            { iIntros "!> !>".
              iExists nodes1, _, bottom1, roots1, m1, waiters1.
              simpl in Hinv'.
              iFrame "∗#%".
            }
            iIntros "!> _ HΦ".

            wp۰pures.
            rewrite (_ : (⁺˖lvl - 1)%Z = ⁺lvl); first lia.
            wp۰apply ("IHremove_2" with "[$Hskiplist $Hkey $Hnode_at $Hwaiters_elem $Hη] HΦ").
            iSplit; first (iPureIntro; lia).
            iRight. iExists link. done.

        + iDestruct ("Hnodes" with "[$Hnexts $Hmarks]") as "Hnodes".
          rewrite !list_insert_id //.
          iSplitR "Hwaiters_elem".
          { iIntros "!> !>". iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
          iIntros "!> _ HΦ".

          wp۰apply+ ("IHremove_2" with "[$Hskiplist $Hkey $Hnode_at $Hwaiters_elem $Hη] HΦ").
          iSplit; first done.
          done.
    }

    { iIntros "%lvl !> %Φ (#Hskiplist & #Hkey & #Hnode_at & %Hlvl & #Hmarked_above & (Hwaiters_elem & #Hη)) HΦ".
      iPoseProof "Hskiplist" as "(:inv)".
      iPoseProof "Hnode_at" as "(#Hnodes_at & #Hnexts_inv & #Hnode_key)".

      wp۰rec credit:"H£".
      awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Hnexts_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup.
      destruct (inv۰pureｰstatus_lookup lt Hinv1 i node) as (status & Hstatuses_lookup); first done.
      pose proof (inv۰pure۰status Hinv1 _ _ _ Hnodes_lookup Hstatuses_lookup) as (Hheight & Hlength & Hmarked_le & Hlinks).
      iDestruct (big_sepL2_lookup_acc with "Hnodes") as "((Hnexts & Hmarks) & Hnodes)"; [done.. |].
      iAaccIntro with "Hnexts".
      { iIntros "Hnexts !>".
        iDestruct ("Hnodes" with "[$Hnexts $Hmarks]") as "Hnodes".
        iSplitR "Hwaiters_elem H£"; last iFrame.
        iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%".
      }
      iIntros "%v (%Hlookup & Hnexts)".
      rewrite difference_empty_L.
      rewrite Nat2Z.id /status۰vals list_lookup_imap in Hlookup.
      apply fmap_Some in Hlookup as (link & Hlinks_lookup & ->).
      destruct (status۰is_marked node status lvl) eqn:Hmarked.

      - iDestruct (marks۰atｰget node status lvl link with "Hmarks") as "#Hmarks_at"; [done.. | |].
        { rewrite /status۰is_marked bool_decide_eq_true in Hmarked. done. }
        iDestruct ("Hnodes" with "[$Hnexts $Hmarks]") as "Hnodes".
        destruct lvl as [| lvl].

        + iMod (lc_fupd_elim_later with "H£ Hwaiters") as "Hwaiters".
          iDestruct (waiters۰elemｰvalid with "Hwaiters_auth Hwaiters_elem") as %Hwaiters_lookup.
          iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ' & #Hη' & HΨ') & Hwaiters)"; first done.
          assert (waiter۰done nodes1 statuses1 (Waiter (node۰to_val node) 𝑘𝑒𝑦) = true) as Hdone.
          { pose proof (inv۰pure۰length Hinv1) as Hlen.
            rewrite waiter۰doneｰspec //.
            exists i, node, status. split_and!; try done.
            rewrite /status۰is_marked bool_decide_eq_true in Hmarked. lia.
          }
          rewrite /= Hdone.
          iMod (waitersｰdelete with "Hwaiters_auth Hwaiters_elem") as "Hwaiters_auth".
          iSplitR "HΨ'".
          { iIntros "!> !>". iExists nodes1, statuses1, bottom1, roots1, m1, (delete η waiters1). iFrame "∗#%". }
          iIntros "!> H£' HΦ".
          iDestruct (saved_predｰagree false with "Hη Hη'") as "Hagree".
          iMod (lc_fupd_elim_later with "H£' Hagree") as "Hagree'".
          iRewrite -"Hagree'" in "HΨ'".

          wp۰apply ("IHremove_1" with "[$Hskiplist $Hkey $Hnode_at HΨ'] HΦ").
          iSplit; first done. iSplit; first done.
          iLeft. iSplit; first iSteps.
          iLeft. iFrame. done.

        + iSplitR "Hwaiters_elem".
          { iIntros "!> !>". iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
          iIntros "!> _ HΦ".

          wp۰apply ("IHremove_1" with "[$Hskiplist $Hkey $Hnode_at Hwaiters_elem] HΦ").
          iSplit; first done. iSplit; first done.
          iLeft. iSplit; first iSteps.
          iRight. iFrame "∗#". iPureIntro. lia.

      - iDestruct ("Hnodes" with "[$Hnexts $Hmarks]") as "Hnodes".
        iDestruct (link۰modelｰget with "Hnodes_auth Hnodes Hnodes_keys") as "(Hnodes_auth & Hnodes & Hlink)"; [done | eapply Hlinks; done |].
        iSplitR "Hwaiters_elem Hlink".
        { iIntros "!> !>". iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
        iIntros "!> H£' HΦ".
        iMod (lc_fupd_elim_later with "H£' Hlink") as "#Hlink".

        wp۰apply ("IHremove_1" with "[$Hskiplist $Hkey $Hnode_at Hwaiters_elem] HΦ").
        iSplit; first done. iSplit; first done.
        iRight. iExists link. iFrame "∗#". done.
    }
  Qed.

  #[local] Lemma skiplist٠remove_2ｰspec γ ι key 𝑘𝑒𝑦 i node η Ψ lvl :
    node.(node۰𝑘𝑒𝑦) = 𝑘𝑒𝑦 →
    {{{
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦 ∗
      node۰at γ i node ∗
      ⌜lvl < node.(node۰height)⌝ ∗
      ( ⌜S lvl = node.(node۰height)⌝
      ∨ ∃ link,
        marks۰at node (S lvl) link
      ) ∗
      remove۰waiter γ η node 𝑘𝑒𝑦 Ψ
    }}}
      skiplist٠remove_2 γ key node.(node۰nexts) #lvl
    {{{
      (b : bool)
    , RET #b;
      Ψ b
    }}}.
  Proof.
    intros Hkey_eq.
    iDestruct (skiplist٠remove_1ｰremove_2ｰspec γ ι key 𝑘𝑒𝑦 i node η Ψ Hkey_eq) as "(_ & H)".
    iApply "H".
  Qed.

  Lemma skiplist٠removeｰspec γ ι key 𝑘𝑒𝑦 :
    <<<
      skiplist۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      skiplist۰model γ m
    >>>
      skiplist٠remove γ key
      @ ↑ι
    <<<
      skiplist۰model γ (delete 𝑘𝑒𝑦 m)
    | RET #(bool_decide (𝑘𝑒𝑦 ∈ dom m));
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hskiplist & #Hkey) HΦ".
    iPoseProof "Hskiplist" as "(:inv)".

    wp۰rec.
    wp۰apply+ (prophet_typed₁ｰwpｰproph prophet_res with "[//]") as (pid proph) "Hproph".
    destruct (decide (proph = §skiplist٠Null%V)) as [Hproph | Hproph].

    - wp۰apply+ (skiplist٠find_nodeｰspec γ _ key 𝑘𝑒𝑦 true None (λ _, Φ false%V) with "[$Hskiplist $Hkey HΦ]") as (res) "Hres".
      { iSplit; first done.
        rewrite /find_node۰token. iRight.
        iIntros "%m %Hm Hmodel₂".
        iMod "HΦ" as "(%m' & (:model) & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
        { rewrite delete_id //. }
        iFrame.
        rewrite bool_decide_eq_false_2.
        { apply not_elem_of_dom. done. }
        iApply "HΦ". done.
      }
      wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
      wp۰pures.
      iExists (Some res). iSplitR; first done.
      iIntros "!> %Heq". subst proph.
      iDestruct "Hres" as "[(-> & HΦ) | (%i & %node & -> & _)]".
      + wp۰pures. done.
      + done.

    - iAssert (
          ( ∃ j node link,
            ⌜node۰to_val node = proph⌝ ∗
            nodes۰at γ j node ∗
            marks۰at node 0 link
          )
        ∨ ∃ η,
          waiters۰elem γ η (Waiter proph 𝑘𝑒𝑦) ∗
          saved_pred η (λ b, True -∗ Φ #b)
      )%I with "[> HΦ]" as "[(%j & %node & %link & %Htarget & #Hnodes_at & #Hmarks_at) | (%η & Hwaiters_elem & #Hη)]".
      { iInv "Hinv" as "(:inv۰inner =1)" "Hclose".
        destruct (waiter۰done nodes1 statuses1 (Waiter proph 𝑘𝑒𝑦)) eqn:Hdone.
        - pose proof (inv۰pure۰length Hinv1) as Hlen.
          pose proof Hdone as Hdone'.
          rewrite waiter۰doneｰspec // in Hdone'.
          destruct Hdone' as (j & node & status & Hnodes_lookup & Hstatuses_lookup & Htarget & Hkey_eq & Hmarked).
          simpl in Htarget, Hkey_eq.
          pose proof (inv۰pure۰status Hinv1 _ _ _ Hnodes_lookup Hstatuses_lookup) as (Hheight & Hlength & _ & _).
          destruct (lookup_lt_is_Some_2 status.(status۰links) 0) as (link & Hlink); first lia.
          iDestruct (nodes۰modelｰmarks_at j node status 0 link Hinv1 with "Hnodes") as "(Hnodes & #Hmarks_at)"; [done.. | | done |].
          { rewrite /status۰is_marked bool_decide_eq_true. lia. }
          iDestruct (nodes۰atｰget j node with "Hnodes_auth") as "#Hnodes_at"; first done.
          iMod ("Hclose" with "[-]") as "_".
          { iNext. iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
          iModIntro. iLeft. iExists j, node, link. iFrame "#". done.
        - iMod (saved_predｰallocｰcofinite (dom waiters1) (λ b, True -∗ Φ #b)%I) as "(%η & %Hη & #Hη)".
          apply not_elem_of_dom in Hη.
          iMod (waitersｰinsert η (Waiter proph 𝑘𝑒𝑦) with "Hwaiters_auth") as "(Hwaiters_auth & Hwaiters_elem)"; first done.
          iMod ("Hclose" with "[-Hwaiters_elem]") as "_".
          { iNext. iExists nodes1, statuses1, bottom1, roots1, m1, (<[η := Waiter proph 𝑘𝑒𝑦]> waiters1).
            iFrame "∗#%".
            iApply big_sepM_insert; first done.
            iFrame.
            iExists (λ b, True -∗ Φ #b)%I. iFrame "#".
            rewrite Hdone. iExact "HΦ".
          }
          iModIntro. iRight. iExists η. iFrame "∗#".
      }

      + wp۰apply+ (skiplist٠find_nodeｰspec γ _ key 𝑘𝑒𝑦 false (Some node) (λ _, True)%I with "[$Hskiplist $Hkey]") as (res) "Hres".
        { iSplitR.
          - iSplitR; first iSteps.
            iExists link. done.
          - iIntros "%m _ Hmodel₂ !>". iFrame.
        }
        wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
        wp۰pures.
        iExists (Some res). iSplitR; first done.
        iIntros "!> %Heq". subst proph.
        iDestruct "Hres" as "[(-> & _) | (%i & %node' & -> & _ & %Hexcl & _)]".
        * done.
        * exfalso. apply (Hexcl node); done.

      + wp۰apply+ (skiplist٠find_nodeｰspec γ _ key 𝑘𝑒𝑦 false None (λ _, True)%I with "[$Hskiplist $Hkey]") as (res) "Hres".
        { iSplitR; first done.
          iIntros "%m _ Hmodel₂ !>". iFrame.
        }
        wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
        wp۰pures.
        iExists (Some res). iSplitR; first done.
        iIntros "!> %Heq". subst proph.
        iDestruct "Hres" as "[(-> & _) | (%i & %node & -> & %Hkey_eq & _ & #Hnode_at & _)]"; first done.
        iPoseProof "Hnode_at" as "(_ & #Hnexts_inv & _)".
        wp۰apply+ (array٠sizeｰspecｰinv with "Hnexts_inv") as "_".
        wp۰pures.
        iAssert ⌜0 < node.(node۰height)⌝%I with "[>]" as %Hheight.
        { iPoseProof "Hnode_at" as "(#Hnodes_at & _)".
          iInv "Hinv" as "(:inv۰inner =1)" "Hclose".
          iDestruct (nodes۰atｰvalid with "Hnodes_auth Hnodes_at") as %Hnodes_lookup.
          destruct (inv۰pureｰstatus_lookup lt Hinv1 i node) as (status & Hstatuses_lookup); first done.
          pose proof (inv۰pure۰status Hinv1 _ _ _ Hnodes_lookup Hstatuses_lookup) as (Hheight & _).
          iMod ("Hclose" with "[-]") as "_".
          { iNext. iExists nodes1, statuses1, bottom1, roots1, m1, waiters1. iFrame "∗#%". }
          done.
        }
        rewrite (_ : (⁺node.(node۰height) - 1)%Z = ⁺(node.(node۰height) - 1)); first lia.
        wp۰apply (skiplist٠remove_2ｰspec _ _ key 𝑘𝑒𝑦 i node η (λ b, True -∗ Φ #b)%I _ Hkey_eq with "[$Hskiplist $Hkey $Hnode_at $Hwaiters_elem $Hη]") as (b) "HΦ".
        { iSplit; first (iPureIntro; lia).
          iLeft. iPureIntro. lia.
        }
        iApply "HΦ". done.
  Qed.
End skiplist۰G.

Require zoo_saturn.skiplist__opaque.

Please opacify.
