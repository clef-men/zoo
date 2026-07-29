Require Import stdpp.namespaces.

Require Import iris.algebra.reservation_map.
Require Import iris.algebra.agree.
Require Import iris.algebra.frac.
Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Implicit Type η : gname.

Class GhostHeapG Σ L V `{Countable L} :=
  { #[local] ghost_heap۰G۰heap۰G :: ghost_mapG Σ L V
  ; #[local] ghost_heap۰G۰meta۰G :: ghost_mapG Σ L gname
  ; #[local] ghost_heap۰G۰meta_data۰G :: inG Σ (reservation_mapR $ agreeR positiveO)
  }.

Definition ghost_heap۰Σ L V `{Countable L} :=
  #[ghost_mapΣ L V
  ; ghost_mapΣ L gname
  ; GFunctor (reservation_mapR $ agreeR positiveO)
  ].
#[global] Instance subGｰghost_heap۰Σ Σ L V `{Countable L} :
  subG (ghost_heap۰Σ L V) Σ →
  GhostHeapG Σ L V.
Proof.
  solve_inG.
Qed.

Section ghost_heap۰G.
  Context `{ghost_heap۰G : GhostHeapG Σ L V}.

  Implicit Type l : L.
  Implicit Type v : V.
  Implicit Type σ : gmap L V.
  Implicit Type m : gmap L gname.

  Record ghost_heap۰name :=
    { ghost_heap۰name۰heap : gname
    ; ghost_heap۰name۰meta : gname
    }.
  Implicit Type γ : ghost_heap۰name.

  #[global] Instance ghost_heap۰nameｰeq_dec : EqDecision ghost_heap۰name :=
    ltac:(solve_decision).
  #[global] Instance ghost_heap۰nameｰcountable :
    Countable ghost_heap۰name.
  Proof.
    solve_countable.
  Qed.

  Definition ghost_heap۰auth γ σ : iProp Σ :=
    ∃ m,
    ⌜dom m ⊆ dom σ⌝ ∗
    ghost_map_auth γ.(ghost_heap۰name۰heap) 1 σ ∗
    ghost_map_auth γ.(ghost_heap۰name۰meta) 1 m.
  #[local] Instance : CustomIpat "auth" :=
    " ( %m
      & %Hdom
      & Hσ
      & Hm
      )
    ".

  Definition ghost_heap۰at γ l dq v :=
    ghost_map_elem γ.(ghost_heap۰name۰heap) l dq v.

  Definition ghost_heap۰meta_token γ l E : iProp Σ :=
    ∃ η,
    ghost_map_elem γ.(ghost_heap۰name۰meta) l DfracDiscarded η ∗
    own η (reservation_map_token E).
  #[local] Instance : CustomIpat "meta_token" :=
    " ( %η{}
      & #Hl{_{}}
      & Hη{}
      )
    ".

  Definition ghost_heap۰meta `{Countable A} γ l ι (x : A) : iProp Σ :=
    ∃ η,
    ghost_map_elem γ.(ghost_heap۰name۰meta) l DfracDiscarded η ∗
    own η (reservation_map_data (coPpick (↑ι)) $ to_agree $ encode x).
  #[local] Instance : CustomIpat "meta" :=
    " ( %η{}
      & #Hl{_{}}
      & Hη{}
      )
    ".

  #[global] Instance ghost_heap۰authｰtimeless γ σ :
    Timeless (ghost_heap۰auth γ σ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_heap۰atｰtimeless γ l dq v :
    Timeless (ghost_heap۰at γ l dq v).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_heap۰atｰpersistent γ l v :
    Persistent (ghost_heap۰at γ l DfracDiscarded v).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_heap۰atｰfractional γ l v :
    Fractional (λ q, ghost_heap۰at γ l (DfracOwn q) v)%I.
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_heap۰atｰas_fractional γ l q v :
    AsFractional (ghost_heap۰at γ l (DfracOwn q) v) (λ q, ghost_heap۰at γ l (DfracOwn q) v)%I q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_heap۰atｰvalid γ l dq v :
    ghost_heap۰at γ l dq v ⊢
    ⌜✓ dq⌝.
  Proof.
    apply bi.wand_entails', ghost_map_elem_valid.
  Qed.
  Lemma ghost_heap۰atｰcombine γ l dq1 v1 dq2 v2 :
    ghost_heap۰at γ l dq1 v1 -∗
    ghost_heap۰at γ l dq2 v2 -∗
      ⌜v1 = v2⌝ ∗
      ghost_heap۰at γ l (dq1 ⋅ dq2) v1.
  Proof.
    rewrite comm. apply ghost_map_elem_combine.
  Qed.
  Lemma ghost_heap۰atｰvalidｰ2 γ l dq1 v1 dq2 v2 :
    ghost_heap۰at γ l dq1 v1 -∗
    ghost_heap۰at γ l dq2 v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as "$".
  Qed.
  Lemma ghost_heap۰atｰagree γ l dq1 v1 dq2 v2 :
    ghost_heap۰at γ l dq1 v1 -∗
    ghost_heap۰at γ l dq2 v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ghost_map_elem_agree.
  Qed.
  Lemma ghost_heap۰atｰdfracｰne γ l1 dq1 v1 l2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_heap۰at γ l1 dq1 v1 -∗
    ghost_heap۰at γ l2 dq2 v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply ghost_map_elem_frac_ne.
  Qed.
  Lemma ghost_heap۰atｰne γ l1 v1 l2 dq2 v2 :
    ghost_heap۰at γ l1 (DfracOwn 1) v1 -∗
    ghost_heap۰at γ l2 dq2 v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply ghost_map_elem_ne.
  Qed.
  Lemma ghost_heap۰atｰexclusive γ l v1 dq2 v2 :
    ghost_heap۰at γ l (DfracOwn 1) v1 -∗
    ghost_heap۰at γ l dq2 v2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %?. done.
  Qed.
  Lemma ghost_heap۰atｰpersist γ l dq v :
    ghost_heap۰at γ l dq v ⊢ |==>
    ghost_heap۰at γ l DfracDiscarded v.
  Proof.
    apply bi.wand_entails', ghost_map_elem_persist.
  Qed.

  #[global] Instance ghost_heap۰atｰcombine_sep_gives γ l dq1 v1 dq2 v2 :
    CombineSepGives (ghost_heap۰at γ l dq1 v1) (ghost_heap۰at γ l dq2 v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝
  | 30.
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_heap۰atｰcombine_as γ l dq1 dq2 v1 v2 :
    CombineSepAs (ghost_heap۰at γ l dq1 v1) (ghost_heap۰at γ l dq2 v2) (ghost_heap۰at γ l (dq1 ⋅ dq2) v1)
  | 60.
  Proof.
    apply _.
  Qed.
  #[global] Instance frameｰghost_heap۰at p γ l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (ghost_heap۰at γ l (DfracOwn q1) v) (ghost_heap۰at γ l (DfracOwn q2) v) (ghost_heap۰at γ l (DfracOwn q) v)
  | 5.
  Proof.
    apply: frame_fractional.
  Qed.

  #[global] Instance ghost_heap۰meta_tokenｰtimeless γ l E :
    Timeless (ghost_heap۰meta_token γ l E).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_heap۰metaｰtimeless `{Countable A} γ l ι (x : A) :
    Timeless (ghost_heap۰meta γ l ι x).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_heap۰metaｰpersistent `{Countable A} γ l ι (x : A) :
    Persistent (ghost_heap۰meta γ l ι x).
  Proof.
    apply _.
  Qed.

  Lemma ghost_heap۰meta_tokenｰunion₁ γ l E1 E2 :
    E1 ## E2 →
    ghost_heap۰meta_token γ l (E1 ∪ E2) ⊢
      ghost_heap۰meta_token γ l E1 ∗
      ghost_heap۰meta_token γ l E2.
  Proof.
    intros ?.
    iIntros "(:meta_token)".
    iEval (rewrite reservation_map_token_union //) in "Hη".
    iDestruct "Hη" as "($ & $)".
    iSteps.
  Qed.
  Lemma ghost_heap۰meta_tokenｰunion₂ γ l E1 E2 :
    ghost_heap۰meta_token γ l E1 -∗
    ghost_heap۰meta_token γ l E2 -∗
    ghost_heap۰meta_token γ l (E1 ∪ E2).
  Proof.
    iIntros "(:meta_token =1) (:meta_token =2)".
    iCombine "Hl_1 Hl_2" gives %(_ & ->).
    iCombine "Hη1 Hη2" gives %?%reservation_map_token_valid_op.
    iSteps.
    iEval (rewrite reservation_map_token_union //).
    iEval (rewrite own_op).
    iFrame.
  Qed.
  Lemma ghost_heap۰meta_tokenｰunion γ l E1 E2 :
    E1 ## E2 →
    ghost_heap۰meta_token γ l (E1 ∪ E2) ⊣⊢
      ghost_heap۰meta_token γ l E1 ∗
      ghost_heap۰meta_token γ l E2.
  Proof.
    intros.
    iSplit.
    - iApply ghost_heap۰meta_tokenｰunion₁. 1: done.
    - iIntros "(H1 & H2)".
      iApply (ghost_heap۰meta_tokenｰunion₂ with "H1 H2").
  Qed.

  Lemma ghost_heap۰meta_tokenｰdifference γ l E1 E2 :
    E1 ⊆ E2 →
    ghost_heap۰meta_token γ l E2 ⊣⊢
      ghost_heap۰meta_token γ l E1 ∗
      ghost_heap۰meta_token γ l (E2 ∖ E1).
  Proof.
    intros.
    rewrite {1}(union_difference_L E1 E2) //.
    rewrite ghost_heap۰meta_tokenｰunion //. 1: set_solver.
  Qed.

  Lemma ghost_heap۰metaｰagree `{Countable A} γ l ι (x1 x2 : A) :
    ghost_heap۰meta γ l ι x1 -∗
    ghost_heap۰meta γ l ι x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    iIntros "(:meta =1) (:meta =2)".
    iCombine "Hl_1 Hl_2" gives %(_ & ->).
    iCombine "Hη1 Hη2" gives %Hvalid.
    iPureIntro. move: Hvalid.
    rewrite -reservation_map_data_op reservation_map_data_valid.
    move=> /to_agree_op_inv_L. naive_solver.
  Qed.
  Lemma ghost_heap۰metaｰset `{Countable A} γ E l (x : A) ι :
    ↑ι ⊆ E →
    ghost_heap۰meta_token γ l E ⊢ |==>
    ghost_heap۰meta γ l ι x.
  Proof.
    iIntros "% (:meta_token)".
    iFrame "#".
    iApply (own_update with "Hη").
    { apply reservation_map_alloc. 2: done.
      pose proof (coPpick_elem_of (↑ι) (nclose_non_empty _)). set_solver.
    }
  Qed.

  Lemma ghost_heapｰmetaｰmeta_tokenｰvalid `{Countable A} γ l (x : A) ι E :
    ghost_heap۰meta γ l ι x -∗
    ghost_heap۰meta_token γ l E -∗
    ⌜↑ι ⊈ E⌝.
  Proof.
    iIntros "(:meta =1) (:meta_token =2) %".
    iCombine "Hl_1 Hl_2" gives %(_ & <-).
    iCombine "Hη1 Hη2" gives %Hvalid.
    iPureIntro.
    rewrite reservation_map_valid_eq /= left_id_L right_id_L in Hvalid.
    destruct Hvalid as (_ & Hvalid).
    specialize (Hvalid (coPpick (↑ι))).
    rewrite lookup_singleton_eq in Hvalid.
    pose proof (coPpick_elem_of (↑ι) (nclose_non_empty _)). set_solver.
  Qed.
  Lemma ghost_heapｰmetaｰmeta_tokenｰvalid' `{Countable A} γ l (x : A) ι E :
    ↑ι ⊆ E →
    ghost_heap۰meta γ l ι x -∗
    ghost_heap۰meta_token γ l E -∗
    False.
  Proof.
    iIntros (?) "#Hmeta Htoken".
    iDestruct (ghost_heapｰmetaｰmeta_tokenｰvalid with "Hmeta Htoken") as %[] => //.
  Qed.

  #[global] Instance ghost_heapｰcombine_sep_givesｰmetaｰmeta_token₁ `{Countable A} γ l (x : A) ι E :
    CombineSepGives (ghost_heap۰meta γ l ι x) (ghost_heap۰meta_token γ l E) ⌜↑ι ⊈ E⌝.
  Proof.
    rewrite /CombineSepGives.
    iIntros "(#Hmeta & Htoken)".
    iDestruct (ghost_heapｰmetaｰmeta_tokenｰvalid with "Hmeta Htoken") as %?. auto.
  Qed.
  #[global] Instance ghost_heapｰcombine_sep_givesｰmetaｰmeta_token₂ `{Countable A} γ l (x : A) ι E :
    CombineSepGives (ghost_heap۰meta_token γ l E) (ghost_heap۰meta γ l ι x) ⌜↑ι ⊈ E⌝.
  Proof.
    rewrite /CombineSepGives.
    iIntros "(Htoken & #Hmeta)".
    iCombine "Hmeta Htoken" gives %?. auto.
  Qed.

  Lemma ghost_heapｰlookup γ σ l dq v :
    ghost_heap۰auth γ σ -∗
    ghost_heap۰at γ l dq v -∗
    ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "(:auth) Hl".
    iApply (ghost_map_lookup with "Hσ Hl").
  Qed.

  Lemma ghost_heapｰinsert {γ σ} l v :
    σ !! l = None →
    ghost_heap۰auth γ σ ⊢ |==>
      ghost_heap۰auth γ (<[l := v]> σ) ∗
      ghost_heap۰at γ l (DfracOwn 1) v ∗
      ghost_heap۰meta_token γ l ⊤.
  Proof.
    iIntros "%Hlookup (:auth)".
    iMod (ghost_map_insert l v with "Hσ") as "($ & $)". 1: done.
    iMod (own_alloc (reservation_map_token ⊤)) as "(%η & $)".
    { apply reservation_map_token_valid. }
    iMod (ghost_map_insert_persist l η with "Hm") as "($ & $)".
    { rewrite -!not_elem_of_dom in Hlookup |- *.
      set_solver.
    }
    iPureIntro. set_solver.
  Qed.
  Lemma ghost_heapｰinsertｰbig {γ σ1} σ2 :
    σ2 ##ₘ σ1 →
    ghost_heap۰auth γ σ1 ⊢ |==>
      ghost_heap۰auth γ (σ2 ∪ σ1) ∗
      ([∗ map] l ↦ v ∈ σ2, ghost_heap۰at γ l (DfracOwn 1) v) ∗
      ([∗ map] l ↦ _ ∈ σ2, ghost_heap۰meta_token γ l ⊤).
  Proof.
    iInduction σ2 as [| l v σ2 Hl] "IH" using map_ind forall (σ1).
    all: iIntros "% Hauth".
    - rewrite left_id_L. auto.
    - iMod ("IH" with "[%] Hauth") as "(Hauth & Hats & Hmeta_tokens)".
      { eapply map_disjoint_insert_l => //. }
      decompose_map_disjoint.
      iEval (rewrite !big_opM_insert //).
      iEval (rewrite -insert_union_l //).
      iMod (ghost_heapｰinsert l v with "Hauth") as "($ & $ & $)".
      { apply lookup_union_None => //. }
      iFrameSteps.
  Qed.

  Lemma ghost_heapｰupdate {γ σ l v1} v2 :
    ghost_heap۰auth γ σ -∗
    ghost_heap۰at γ l (DfracOwn 1) v1 ==∗
      ghost_heap۰auth γ (<[l := v2]> σ) ∗
      ghost_heap۰at γ l (DfracOwn 1) v2.
  Proof.
    iIntros "(:auth) Hl".
    iDestruct (ghost_map_lookup with "Hσ Hl") as %Hlookup.
    iMod (ghost_map_update with "Hσ Hl") as "($ & $)".
    iFrame. iPureIntro. set_solver.
  Qed.

  Lemma ghost_heapｰalloc σ :
    ⊢ |==>
      ∃ γ,
      ghost_heap۰auth γ σ ∗
      ([∗ map] l ↦ v ∈ σ, ghost_heap۰at γ l (DfracOwn 1) v) ∗
      ([∗ map] l ↦ _ ∈ σ, ghost_heap۰meta_token γ l ⊤).
  Proof.
    iMod (ghost_map_alloc_empty (K := L) (V := V)) as "(%γ_heap & Hσ)".
    iMod (ghost_map_alloc_empty (K := L) (V := gname)) as "(%γ_meta & Hm)".
    pose γ :=
      {|ghost_heap۰name۰heap := γ_heap
      ; ghost_heap۰name۰meta := γ_meta
      |}.
    iAssert (ghost_heap۰auth γ ∅) with "[$Hσ $Hm //]" as "Hauth".
    iMod (ghost_heapｰinsertｰbig with "Hauth") as "(Hauth & $ & $)". 1: set_solver.
    iEval (rewrite right_id_L) in "Hauth" => //.
  Qed.
End ghost_heap۰G.

#[global] Opaque ghost_heap۰auth.
#[global] Opaque ghost_heap۰at.
#[global] Opaque ghost_heap۰meta_token.
#[global] Opaque ghost_heap۰meta.
