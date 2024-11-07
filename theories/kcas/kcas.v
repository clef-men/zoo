From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.auth_mono
  lib.excl
  lib.saved_prop.
From zoo.language Require Import
  typed_prophet
  identifier
  notations
  diaframe.
From zoo_std Require Import
  lst.
From kcas Require Import
  kcas__types.
From kcas Require Export
  kcas__code.
From zoo Require Import
  options.

Implicit Types full : bool.
Implicit Types i : nat.
Implicit Types l loc casn : location.
Implicit Types gid : identifier.
Implicit Types v state cass : val.
Implicit Types waiters : gmap gname nat.

Axiom wp_equal : ∀ `{zoo_G : !ZooG Σ} v1 v2 E Φ,
  ▷ Φ #(bool_decide (v1 = v2)) ⊢
  WP v1 == v2 @ E {{ Φ }}.

#[local] Program Definition kcas_prophet := {|
  typed_prophet_type :=
    identifier * bool ;
  typed_prophet_of_val v :=
    match v with
    | ValTuple [ValProph gid; ValBool b] =>
        Some (gid, b)
    | _ =>
        None
    end ;
  typed_prophet_to_val '(gid, b) :=
    (#gid, #b)%V ;
|}.
Solve Obligations of kcas_prophet with
  try done.
Next Obligation.
  intros (gid & b) v ->. done.
Qed.
Implicit Types prophs : list kcas_prophet.(typed_prophet_type).

Definition kcas_loc_meta : Type :=
  gname.
Implicit Types γ : kcas_loc_meta.

Record kcas_descr := {
  kcas_descr_loc : location ;
  kcas_descr_meta : kcas_loc_meta ;
  kcas_descr_before : val ;
  kcas_descr_after : val ;
  kcas_descr_state : block_id ;
}.
Implicit Types descr : kcas_descr.

#[local] Instance kcas_descr_inhabited : Inhabited kcas_descr :=
populate {|
    kcas_descr_loc := inhabitant ;
    kcas_descr_meta := inhabitant ;
    kcas_descr_before := inhabitant ;
    kcas_descr_after := inhabitant ;
    kcas_descr_state := inhabitant ;
  |}.
#[local] Instance kcas_descr_eq_dec : EqDecision kcas_descr :=
  ltac:(solve_decision).
#[local] Instance kcas_descr_countable :
  Countable kcas_descr.
Proof.
  pose encode descr := (
    descr.(kcas_descr_loc),
    descr.(kcas_descr_meta),
    descr.(kcas_descr_before),
    descr.(kcas_descr_after),
    descr.(kcas_descr_state)
  ).
  pose decode := λ '(loc, γ, before, after, state), {|
    kcas_descr_loc := loc ;
    kcas_descr_meta := γ ;
    kcas_descr_before := before ;
    kcas_descr_after := after ;
    kcas_descr_state := state ;
  |}.
  refine (inj_countable' encode decode _). intros []. done.
Qed.

#[local] Definition kcas_state casn descr : val :=
  ‘0@descr.(kcas_descr_state)(
    #casn,
    descr.(kcas_descr_before),
    descr.(kcas_descr_after)
  ).

Inductive kcas_status :=
  | KcasUndetermined
  | KcasBefore
  | KcasAfter.
Implicit Types status : kcas_status.

Record kcas_casn_meta := {
  kcas_casn_meta_descrs : list kcas_descr ;
  kcas_casn_meta_prophet : prophet_id ;
  kcas_casn_meta_prophs : list kcas_prophet.(typed_prophet_type) ;
  kcas_casn_meta_undetermined : block_id ;
  kcas_casn_meta_post : gname ;
  kcas_casn_meta_lstatus : gname ;
  kcas_casn_meta_witnesses : list gname ;
  kcas_casn_meta_waiters : gname ;
  kcas_casn_meta_winning : gname ;
  kcas_casn_meta_owner : gname ;
}.
Implicit Types η : kcas_casn_meta.

#[local] Instance kcas_casn_meta_inhabited : Inhabited kcas_casn_meta :=
  populate {|
    kcas_casn_meta_descrs := inhabitant ;
    kcas_casn_meta_prophet := inhabitant ;
    kcas_casn_meta_prophs := inhabitant ;
    kcas_casn_meta_undetermined := inhabitant ;
    kcas_casn_meta_post := inhabitant ;
    kcas_casn_meta_lstatus := inhabitant ;
    kcas_casn_meta_witnesses := inhabitant ;
    kcas_casn_meta_waiters := inhabitant ;
    kcas_casn_meta_winning := inhabitant ;
    kcas_casn_meta_owner := inhabitant ;
  |}.
#[local] Instance kcas_casn_meta_eq_dec : EqDecision kcas_casn_meta :=
  ltac:(solve_decision).
#[local] Instance kcas_casn_meta_countable :
  Countable kcas_casn_meta.
Proof.
  pose encode η := (
    η.(kcas_casn_meta_descrs),
    η.(kcas_casn_meta_prophet),
    η.(kcas_casn_meta_prophs),
    η.(kcas_casn_meta_undetermined),
    η.(kcas_casn_meta_post),
    η.(kcas_casn_meta_lstatus),
    η.(kcas_casn_meta_witnesses),
    η.(kcas_casn_meta_waiters),
    η.(kcas_casn_meta_winning),
    η.(kcas_casn_meta_owner)
  ).
  pose decode := λ '(descrs, prophet, prophs, undetermined, post, lstatus, witnesses, waiters, winning, owner), {|
    kcas_casn_meta_descrs := descrs ;
    kcas_casn_meta_prophet := prophet ;
    kcas_casn_meta_prophs := prophs ;
    kcas_casn_meta_undetermined := undetermined ;
    kcas_casn_meta_post := post ;
    kcas_casn_meta_lstatus := lstatus ;
    kcas_casn_meta_witnesses := witnesses ;
    kcas_casn_meta_waiters := waiters ;
    kcas_casn_meta_winning := winning ;
    kcas_casn_meta_owner := owner ;
  |}.
  refine (inj_countable' encode decode _). intros []. done.
Qed.

#[local] Definition kcas_casn_meta_size η :=
  length η.(kcas_casn_meta_descrs).
#[local] Definition kcas_casn_meta_cass casn η :=
  (λ descr,
    (#descr.(kcas_descr_loc), kcas_state casn descr)%V
  ) <$> η.(kcas_casn_meta_descrs).
#[local] Definition kcas_casn_meta_outcome η :=
  hd inhabitant η.(kcas_casn_meta_prophs).
#[local] Definition kcas_casn_meta_winner η :=
  (kcas_casn_meta_outcome η).1.
#[local] Definition kcas_casn_meta_success η :=
  (kcas_casn_meta_outcome η).2.
#[local] Definition kcas_casn_meta_final η :=
  if kcas_casn_meta_success η then KcasAfter else KcasBefore.

#[local] Instance kcas_status_inhabited : Inhabited kcas_status :=
  populate KcasUndetermined.

#[local] Definition kcas_status_to_val casn η status : val :=
  match status with
  | KcasUndetermined =>
      ‘Undetermined@η.(kcas_casn_meta_undetermined)( lst_to_val $ kcas_casn_meta_cass casn η )
  | KcasBefore =>
      §Before
  | KcasAfter =>
      §After
  end.

Inductive kcas_lstatus :=
  | KcasRunning i
  | KcasFinished.
Implicit Types lstatus : kcas_lstatus.

#[local] Instance kcas_lstatus_inhabited : Inhabited kcas_lstatus :=
  populate KcasFinished.

Inductive kcas_lstep : kcas_lstatus → kcas_lstatus → Prop :=
  | kcas_lstep_incr i :
      kcas_lstep (KcasRunning i) (KcasRunning (S i))
  | kcas_lstep_finish i :
      kcas_lstep (KcasRunning i) KcasFinished.
#[local] Hint Constructors kcas_lstep : core.

#[local] Lemma kcas_lsteps_running0 lstatus :
  rtc kcas_lstep (KcasRunning 0) lstatus.
Proof.
  destruct lstatus as [i |].
  - induction i; first done.
    eapply rtc_r; [done | constructor].
  - apply rtc_once. done.
Qed.
#[local] Lemma kcas_lstep_finished lstatus :
  ¬ kcas_lstep KcasFinished lstatus.
Proof.
  inversion 1.
Qed.
#[local] Lemma kcas_lsteps_finished lstatus :
  rtc kcas_lstep KcasFinished lstatus →
  lstatus = KcasFinished.
Proof.
  inversion 1 as [| ? ? ? []] => //.
Qed.
#[local] Lemma kcas_lsteps_le lstatus1 i1 lstatus2 i2 :
  rtc kcas_lstep lstatus1 lstatus2 →
  lstatus1 = KcasRunning i1 →
  lstatus2 = KcasRunning i2 →
  i1 ≤ i2.
Proof.
  intros Hlsteps. move: i1. induction Hlsteps as [lstatus | lstatus1 ? lstatus2 Hlstep Hlsteps IH] => i1.
  - naive_solver.
  - intros -> ->. invert Hlstep.
    + specialize (IH (S i1)). lia.
    + apply kcas_lsteps_finished in Hlsteps as [=].
Qed.

#[local] Definition kcas_descr_final descr η :=
  if kcas_casn_meta_success η then
    descr.(kcas_descr_after)
  else
    descr.(kcas_descr_before).

Class KcasG Σ `{zoo_G : !ZooG Σ} := {
  #[local] kcas_G_model_G :: TwinsG Σ val_O ;
  #[local] kcas_G_saved_prop :: SavedPropG Σ ;
  #[local] kcas_G_lstatus_G :: AuthMonoG (A := leibnizO kcas_lstatus) Σ kcas_lstep ;
  #[local] kcas_G_witness_G :: ExclG Σ unitO ;
  #[local] kcas_G_waiters_G :: ghost_mapG Σ gname nat ;
  #[local] kcas_G_winning_G :: ExclG Σ unitO ;
  #[local] kcas_G_owner_G :: ExclG Σ unitO ;
}.

Definition kcas_Σ := #[
  twins_Σ val_O ;
  saved_prop_Σ ;
  auth_mono_Σ (A := leibnizO kcas_lstatus) kcas_lstep ;
  excl_Σ unitO ;
  ghost_mapΣ gname nat ;
  excl_Σ unitO ;
  excl_Σ unitO
].
#[global] Instance subG_kcas_Σ Σ `{zoo_G : !ZooG Σ} :
  subG kcas_Σ Σ →
  KcasG Σ.
Proof.
  solve_inG.
Qed.

Section kcas_G.
  Context `{kcas_G : KcasG Σ}.

  Implicit Types P Q : iProp Σ.

  #[local] Definition kcas_model₁ γ v :=
    twins_twin1 γ (DfracOwn 1) v.
  #[local] Definition kcas_model₂ γ v :=
    twins_twin2 γ v.

  #[local] Definition kcas_lstatus_auth' η_lstatus lstatus :=
    auth_mono_auth _ η_lstatus (DfracOwn 1) lstatus.
  #[local] Definition kcas_lstatus_auth η lstatus :=
    kcas_lstatus_auth' η.(kcas_casn_meta_lstatus) lstatus.
  #[local] Definition kcas_lstatus_lb η lstatus :=
    auth_mono_lb _ η.(kcas_casn_meta_lstatus) lstatus.

  #[local] Definition kcas_witness' η_witness :=
    excl η_witness ().
  #[local] Definition kcas_witness η i : iProp Σ :=
    ∃ η_witness,
    ⌜η.(kcas_casn_meta_witnesses) !! i = Some η_witness⌝ ∗
    kcas_witness' η_witness.

  #[local] Definition kcas_waiters_auth' η_waiters waiters :=
    ghost_map_auth η_waiters 1 waiters.
  #[local] Definition kcas_waiters_auth η waiters :=
    kcas_waiters_auth' η.(kcas_casn_meta_waiters) waiters.
  #[local] Definition kcas_waiters_elem η waiter i :=
    ghost_map_elem η.(kcas_casn_meta_waiters) waiter (DfracOwn 1) i.

  #[local] Definition kcas_winning' η_winning :=
    excl η_winning ().
  #[local] Definition kcas_winning η :=
    kcas_winning' η.(kcas_casn_meta_winning).

  #[local] Definition kcas_owner' η_owner :=
    excl η_owner ().
  #[local] Definition kcas_owner η :=
    kcas_owner' η.(kcas_casn_meta_owner).

  #[local] Definition kcas_au η ι P : iProp Σ :=
    AU <{
      ∃∃ vs,
      [∗ list] descr; v ∈ η.(kcas_casn_meta_descrs); vs,
        kcas_model₁ descr.(kcas_descr_meta) v
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ( ∃ i descr v,
        ⌜η.(kcas_casn_meta_descrs) !! i = Some descr⌝ ∗
        ⌜vs !! i = Some v⌝ ∗
        ⌜v ≠ descr.(kcas_descr_before)⌝ ∗
        [∗ list] descr; v ∈ η.(kcas_casn_meta_descrs); vs,
          kcas_model₁ descr.(kcas_descr_meta) v
      ) ∨ (
        ⌜Forall2 (λ v descr, v = descr.(kcas_descr_before)) vs η.(kcas_casn_meta_descrs)⌝ ∗
        [∗ list] descr ∈ η.(kcas_casn_meta_descrs),
          kcas_model₁ descr.(kcas_descr_meta) descr.(kcas_descr_after)
      )
    , COMM
      P
    }>.

  #[local] Definition kcas_waiter_au' η ι descr Q : iProp Σ :=
    AU <{
      ∃∃ v,
      kcas_model₁ descr.(kcas_descr_meta) v
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ⌜v = kcas_descr_final descr η⌝ ∗
      kcas_model₁ descr.(kcas_descr_meta) v
    , COMM
      Q
    }>.
  #[local] Definition kcas_waiter_au η ι i Q : iProp Σ :=
    ∃ descr,
    ⌜η.(kcas_casn_meta_descrs) !! i = Some descr⌝ ∗
    kcas_waiter_au' η ι descr Q.

  #[local] Definition kcas_casn_inv_inner casn η ι P : iProp Σ :=
    ∃ status lstatus waiters,
    casn.[status] ↦ kcas_status_to_val casn η status ∗
    kcas_lstatus_auth η lstatus ∗
    kcas_waiters_auth η waiters ∗
    match lstatus with
    | KcasRunning i =>
        ⌜status = KcasUndetermined⌝ ∗
        ( [∗ list] descr ∈ take i η.(kcas_casn_meta_descrs),
          kcas_model₂ descr.(kcas_descr_meta) descr.(kcas_descr_before)
        ) ∗
        ( [∗ list] j ∈ seq 0 (kcas_casn_meta_size η - i),
          kcas_witness η (i + j)
        ) ∗
        ( [∗ map] waiter ↦ j ∈ waiters,
          ∃ Q,
          saved_prop waiter Q ∗
          kcas_waiter_au η ι j Q
        ) ∗
        typed_prophet_model kcas_prophet η.(kcas_casn_meta_prophet) η.(kcas_casn_meta_prophs) ∗
        ( kcas_au η ι P ∗
          kcas_winning η
        ∨ identifier_model (kcas_casn_meta_winner η)
        )
    | KcasFinished =>
        ∃ prophs,
        ⌜status = kcas_casn_meta_final η⌝ ∗
        ( [∗ list] i ↦ descr ∈ η.(kcas_casn_meta_descrs),
            kcas_model₂ descr.(kcas_descr_meta) (kcas_descr_final descr η)
          ∨ kcas_witness η i
        ) ∗
        ( [∗ map] waiter ↦ i ∈ waiters,
          ∃ Q,
          saved_prop waiter Q ∗
          Q
        ) ∗
        typed_prophet_model kcas_prophet η.(kcas_casn_meta_prophet) prophs ∗
        kcas_winning η ∗
        identifier_model (kcas_casn_meta_winner η) ∗
        (kcas_owner η ∨ P)
    end.
  #[local] Definition kcas_casn_inv_pre ι
    (kcas_casn_inv' : location * kcas_casn_meta * option nat -d> iProp Σ)
    (kcas_loc_inv' : location -d> iProp Σ)
  : location * kcas_casn_meta * option nat -d> iProp Σ
  :=
    λ '(casn, η, i), (
      ∃ P,
      casn.[proph] ↦□ #η.(kcas_casn_meta_prophet) ∗
      saved_prop η.(kcas_casn_meta_post) P ∗
      ⌜NoDup (kcas_descr_loc <$> η.(kcas_casn_meta_descrs))⌝ ∗
      inv (ι.@"casn") (kcas_casn_inv_inner casn η ι P) ∗
      ( if i is Some i then
          [∗ list] j ↦ descr ∈ η.(kcas_casn_meta_descrs),
          if decide (j = i) then
            meta descr.(kcas_descr_loc) nroot descr.(kcas_descr_meta)
          else
            meta descr.(kcas_descr_loc) nroot descr.(kcas_descr_meta) ∗
            kcas_loc_inv' descr.(kcas_descr_loc)
        else
          [∗ list] descr ∈ η.(kcas_casn_meta_descrs),
          meta descr.(kcas_descr_loc) nroot descr.(kcas_descr_meta) ∗
          kcas_loc_inv' descr.(kcas_descr_loc)
      )
    )%I.
  #[local] Instance kcas_casn_inv_pre_contractive ι n :
    Proper (dist_later n ==> (≡{n}≡) ==> (≡{n}≡)) (kcas_casn_inv_pre ι).
  Proof.
    solve_proper.
  Qed.

  #[local] Definition kcas_loc_inv_inner'' full kcas_casn_inv' loc : iProp Σ :=
    ∃ casn η i descr,
    meta casn nroot η ∗
    ⌜η.(kcas_casn_meta_descrs) !! i = Some descr⌝ ∗
    ⌜loc = descr.(kcas_descr_loc)⌝ ∗
    loc ↦ᵣ kcas_state casn descr ∗
    kcas_lstatus_lb η (KcasRunning (S i)) ∗
    kcas_witness η i ∗
    kcas_casn_inv' (casn, η, if full then None else Some i).
  #[local] Definition kcas_loc_inv_inner' :=
    kcas_loc_inv_inner'' false.
  #[local] Definition kcas_loc_inv_pre ι
    (kcas_casn_inv' : location * kcas_casn_meta * option nat -d> iProp Σ)
    (kcas_loc_inv' : location -d> iProp Σ)
  : location -d> iProp Σ
  :=
    λ loc,
      inv (ι.@"loc") (kcas_loc_inv_inner' kcas_casn_inv' loc).
  #[local] Instance kcas_loc_inv_pre_contractive ι n :
    Proper (dist_later n ==> dist_later n ==> (≡{n}≡)) (kcas_loc_inv_pre ι).
  Proof.
    rewrite /kcas_loc_inv_pre /kcas_loc_inv_inner' /kcas_loc_inv_inner'' /curry.
    solve_contractive.
  Qed.

  #[local] Definition kcas_casn_inv'' ι :=
    fixpoint_A (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι).
  #[local] Definition kcas_casn_inv' ι casn η :=
    kcas_casn_inv'' ι (casn, η, None).
  #[local] Definition kcas_casn_inv casn ι : iProp Σ :=
    ∃ η,
    meta casn nroot η ∗
    kcas_casn_inv' ι casn η.

  #[local] Definition kcas_loc_inv' ι :=
    fixpoint_B (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι).
  #[local] Definition kcas_loc_inv_inner loc ι : iProp Σ :=
    kcas_loc_inv_inner'' true (kcas_casn_inv'' ι) loc.
  Definition kcas_loc_inv loc ι : iProp Σ :=
    ∃ γ,
    meta loc nroot γ ∗
    kcas_loc_inv' ι loc.

  Definition kcas_loc_model loc v : iProp Σ :=
    ∃ γ,
    meta loc nroot γ ∗
    kcas_model₁ γ v.

  #[local] Lemma kcas_casn_inv'_unfold ι casn η :
    kcas_casn_inv' ι casn η ⊣⊢
    kcas_casn_inv_pre ι (kcas_casn_inv'' ι) (kcas_loc_inv' ι) (casn, η, None).
  Proof.
    symmetry. apply (fixpoint_A_unfold (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι) _).
  Qed.

  #[local] Lemma kcas_loc_inv'_unfold loc ι :
    kcas_loc_inv' ι loc ⊣⊢
    inv (ι.@"loc") (kcas_loc_inv_inner' (kcas_casn_inv'' ι) loc).
  Proof.
    symmetry. apply (fixpoint_B_unfold (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι) _).
  Qed.
  #[local] Lemma kcas_loc_inv'_intro loc ι :
    inv (ι.@"loc") (kcas_loc_inv_inner' (kcas_casn_inv'' ι) loc) ⊢
    kcas_loc_inv' ι loc.
  Proof.
    setoid_rewrite <- (fixpoint_B_unfold (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι) _).
    iIntros "#Hloc_inv".
    iApply (inv_alter with "Hloc_inv"). iIntros "!> !> (%casn & %η & %i & %descr & Hcasn_meta & %Hdescrs_lookup & -> & Hloc & Hlstatus_lb & Hwitness & Hcasn_inv')".
    iFrame. iSteps.
  Qed.
  #[local] Lemma kcas_loc_inv'_elim loc γ ι :
    meta loc nroot γ -∗
    kcas_loc_inv' ι loc -∗
    inv (ι.@"loc") (kcas_loc_inv_inner loc ι).
  Proof.
    setoid_rewrite <- (fixpoint_B_unfold (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι) _).
    iIntros "#Hloc_meta #Hloc_inv".
    iApply (inv_alter with "Hloc_inv"). iIntros "!> !> (%casn & %η & %i & %descr & Hcasn_meta & %Hdescrs_lookup & -> & Hloc & Hlstatus_lb & Hwitness & Hcasn_inv')".
    iSplitL.
    - iFrame. iSteps.
      setoid_rewrite <- (fixpoint_A_unfold (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι) _).
      iDestruct "Hcasn_inv'" as "(%P & Hcasn_proph & Hpost & %Hlocs & Hcasn_inv & Hlocs_inv)".
      iSteps.
      iApply (big_sepL_impl with "Hlocs_inv"). iIntros "!> %i' %descr' %Hdescr_lookup' H".
      case_decide; last iSteps.
      simplify.
      iDestruct (meta_agree with "Hloc_meta H") as %->.
      setoid_rewrite <- (fixpoint_B_unfold (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι) _).
      iSteps.
    - iSteps.
      setoid_rewrite <- (fixpoint_A_unfold (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι) _).
      iSteps.
      iApply (big_sepL_impl with "[$]").
      iSteps.
      case_decide; iSteps.
  Qed.

  #[global] Instance kcas_loc_model_persistent loc ι :
    Timeless (kcas_loc_model loc ι).
  Proof.
    apply _.
  Qed.
  #[local] Instance kcas_casn_inv'_persistent casn η ι :
    Persistent (kcas_casn_inv' ι casn η).
  Proof.
    rewrite kcas_casn_inv'_unfold /kcas_casn_inv_pre.
    setoid_rewrite kcas_loc_inv'_unfold.
    apply _.
  Qed.
  #[local] Instance kcas_loc_inv'_persistent loc ι :
    Persistent (kcas_loc_inv' ι loc).
  Proof.
    rewrite kcas_loc_inv'_unfold.
    apply _.
  Qed.
  #[global] Instance kcas_loc_inv_persistent loc ι :
    Persistent (kcas_loc_inv loc ι).
  Proof.
    rewrite /kcas_loc_inv.
    apply _.
  Qed.

  #[local] Lemma kcas_model_alloc v :
    ⊢ |==>
      ∃ γ,
      kcas_model₁ γ v ∗
      kcas_model₂ γ v.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma kcas_model_agree γ v1 v2 :
    kcas_model₁ γ v1 -∗
    kcas_model₂ γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma kcas_model₂_exclusive γ v1 v2 :
    kcas_model₂ γ v1 -∗
    kcas_model₂ γ v2 -∗
    False.
  Proof.
    apply twins_twin2_exclusive.
  Qed.

  #[local] Lemma kcas_lstatus_alloc lstatus :
    ⊢ |==>
      ∃ η_lstatus,
      kcas_lstatus_auth' η_lstatus lstatus.
  Proof.
    apply: auth_mono_alloc.
  Qed.
  #[local] Lemma kcas_lstatus_lb_get η lstatus :
    kcas_lstatus_auth η lstatus ⊢
    kcas_lstatus_lb η lstatus.
  Proof.
    apply auth_mono_lb_get.
  Qed.
  #[local] Lemma kcas_lstatus_lb_get_running0 η lstatus :
    kcas_lstatus_auth η lstatus ⊢
    kcas_lstatus_lb η (KcasRunning 0).
  Proof.
    apply auth_mono_lb_get_mono, kcas_lsteps_running0.
  Qed.
  #[local] Lemma kcas_lstatus_lb_get_finished {η} lstatus :
    kcas_lstatus_auth η KcasFinished ⊢
    kcas_lstatus_lb η lstatus.
  Proof.
    destruct lstatus.
    - apply auth_mono_lb_get_mono'. done.
    - apply kcas_lstatus_lb_get.
  Qed.
  #[local] Lemma kcas_lstatus_finished η lstatus :
    kcas_lstatus_auth η lstatus -∗
    kcas_lstatus_lb η KcasFinished -∗
    ⌜lstatus = KcasFinished⌝.
  Proof.
    iIntros "Hlstatus_auth Hlstatus_lb".
    iDestruct (auth_mono_lb_valid with "Hlstatus_auth Hlstatus_lb") as %->%kcas_lsteps_finished.
    iSteps.
  Qed.
  #[local] Lemma kcas_lstatus_le η i1 i2 :
    kcas_lstatus_auth η (KcasRunning i1) -∗
    kcas_lstatus_lb η (KcasRunning i2) -∗
    ⌜i2 ≤ i1⌝.
  Proof.
    iIntros "Hlstatus_auth Hlstatus_lb".
    iDestruct (auth_mono_lb_valid with "Hlstatus_auth Hlstatus_lb") as %Hlsteps.
    iPureIntro. eapply kcas_lsteps_le; done.
  Qed.
  #[local] Lemma kcas_lstatus_update {η lstatus} lstatus' :
    kcas_lstep lstatus lstatus' →
    kcas_lstatus_auth η lstatus ⊢ |==>
    kcas_lstatus_auth η lstatus'.
  Proof.
    apply auth_mono_update'.
  Qed.

  #[local] Lemma kcas_witness_alloc :
    ⊢ |==>
      ∃ η_witness,
      kcas_witness' η_witness.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma kcas_witness_exclusive η i :
    kcas_witness η i -∗
    kcas_witness η i -∗
    False.
  Proof.
    iIntros "(%γ_witness & %Hlookup & Hexcl1) (%_γ_witness & %_Hlookup & Hexcl2)".
    simplify.
    iApply (excl_exclusive with "Hexcl1 Hexcl2").
  Qed.

  #[local] Lemma kcas_waiters_alloc :
    ⊢ |==>
      ∃ η_waiters,
      kcas_waiters_auth' η_waiters ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma kcas_waiters_insert {η waiters} i P :
    kcas_waiters_auth η waiters ⊢ |==>
      ∃ waiter,
      kcas_waiters_auth η (<[waiter := i]> waiters) ∗
      kcas_waiters_elem η waiter i ∗
      saved_prop waiter P.
  Proof.
    iIntros "Hwaiters_auth".
    iMod (saved_prop_alloc_cofinite (dom waiters)) as "(%waiter & %Hwaiter & #Hwaiter)".
    iMod (ghost_map_insert with "Hwaiters_auth") as "(Hwaiters_auth & Hwaiters_elem)".
    { apply not_elem_of_dom. done. }
    iSteps.
  Qed.
  #[local] Lemma kcas_waiters_lookup η waiters waiter i :
    kcas_waiters_auth η waiters -∗
    kcas_waiters_elem η waiter i -∗
    ⌜waiters !! waiter = Some i⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma kcas_waiters_delete η waiters waiter i :
    kcas_waiters_auth η waiters -∗
    kcas_waiters_elem η waiter i ==∗
    kcas_waiters_auth η (delete waiter waiters).
  Proof.
    apply ghost_map_delete.
  Qed.

  #[local] Lemma kcas_winning_alloc :
    ⊢ |==>
      ∃ η_winning,
      kcas_winning' η_winning.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma kcas_winning_exclusive η :
    kcas_winning η -∗
    kcas_winning η -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  #[local] Lemma kcas_owner_alloc :
    ⊢ |==>
      ∃ η_owner,
      kcas_owner' η_owner.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma kcas_owner_exclusive η :
    kcas_owner η -∗
    kcas_owner η -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  #[local] Lemma kcas_casn_wait {casn η ι P i} descr γ Q :
    η.(kcas_casn_meta_descrs) !! i = Some descr →
    descr.(kcas_descr_meta) = γ →
    inv (ι.@"casn") (kcas_casn_inv_inner casn η ι P) -∗
    kcas_witness η i -∗
    kcas_waiter_au' η ι descr Q -∗
      |={⊤ ∖ ↑ι.@"loc"}=>
      ∃ waiter,
      kcas_witness η i ∗
      saved_prop waiter Q ∗
      kcas_waiters_elem η waiter i.
  Proof.
    iIntros (Hdescrs_lookup <-) "#Hcasn_inv Hwitness H".
    iInv "Hcasn_inv" as "(%status & %lstatus & %waiters & Hcasn_status & Hlstatus_auth & >Hwaiters_auth & Hlstatus)".
    iMod (kcas_waiters_insert i Q with "Hwaiters_auth") as "(%waiter & Hwaiters_auth & Hwaiters_elem & #Hwaiter)".
    destruct lstatus as [j |].

    - iDestruct "Hlstatus" as "(>-> & Hmodels & Hwitnesses & Hwaiters & Hproph & Hau)".
      iDestruct (big_sepM_insert_2 _ _ waiter i with "[H] Hwaiters") as "Hwaiters"; first iSteps.
      iSplitR "Hwitness Hwaiters_elem". { do 2 iFrame. iSteps. }
      iModIntro.

      iFrame. iSteps.

    - iDestruct "Hlstatus" as "(%prophs & >-> & >Hmodels & Hwaiters & Hproph & Hwinning & Hwinner & HP)".
      iDestruct (big_sepL_lookup_acc with "Hmodels") as "([Hmodel₂ | _Hwitness] & Hmodels)"; first done; last first.
      { iDestruct (kcas_witness_exclusive with "Hwitness _Hwitness") as %[]. }
      iApply (fupd_mask_mono (⊤ ∖ ↑ι)); first solve_ndisj.
      iMod "H" as "(%v & Hmodel₁ & _ & H)".
      iDestruct (kcas_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("H" with "[$Hmodel₁ //]") as "HQ".
      iDestruct ("Hmodels" with "[Hmodel₂]") as "Hmodels"; first iSteps.
      iDestruct (big_sepM_insert_2 _ _ waiter i with "[HQ] Hwaiters") as "Hwaiters"; first iSteps.
      iSplitR "Hwitness Hwaiters_elem". { do 2 iFrame. iSteps. }
      iModIntro.

      iFrame. iSteps.
  Qed.
  #[local] Lemma kcas_casn_retrieve casn η ι P waiter Q i :
    inv (ι.@"casn") (kcas_casn_inv_inner casn η ι P) -∗
    kcas_lstatus_lb η KcasFinished -∗
    saved_prop waiter Q -∗
    kcas_waiters_elem η waiter i ={⊤}=∗
    ▷^2 Q.
  Proof.
    iIntros "#Hcasn_inv #Hlstatus_lb #Hwaiter Hwaiters_elem".
    iInv "Hcasn_inv" as "(%status & %lstatus & %waiters & Hcasn_status & >Hlstatus_auth & >Hwaiters_auth & Hlstatus)".
    iDestruct (kcas_lstatus_finished with "Hlstatus_auth Hlstatus_lb") as %->.
    iDestruct "Hlstatus" as "(%prophs & >-> & Hmodels & Hwaiters & Hproph & Hwinning & Hwinner & HP)".
    iDestruct (kcas_waiters_lookup with "Hwaiters_auth Hwaiters_elem") as %Hwaiters_lookup.
    iMod (kcas_waiters_delete with "Hwaiters_auth Hwaiters_elem") as "Hwaiters_auth".
    iDestruct (big_sepM_delete with "Hwaiters") as "((%_Q & _Hwaiter & HQ) & Hwaiters)"; first done.
    iDestruct (saved_prop_agree with "Hwaiter _Hwaiter") as "Heq".
    iSplitR "HQ Heq". { do 2 iFrame. iSteps. }
    iModIntro.

    do 3 iModIntro. iRewrite "Heq". iSteps.
  Qed.

  #[local] Lemma kcas_finish_spec_loser gid casn η ι (status : val) :
    status = §Before%V ∨ status = §After%V →
    gid ≠ kcas_casn_meta_winner η →
    {{{
      meta casn nroot η ∗
      kcas_casn_inv' ι casn η
    }}}
      kcas_finish #gid #casn status
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
  Admitted.
  #[local] Lemma kcas_finish_spec_winner_after gid casn η ι :
    gid = kcas_casn_meta_winner η →
    {{{
      meta casn nroot η ∗
      kcas_casn_inv' ι casn η ∗
      identifier_model gid ∗
      kcas_lstatus_lb η (KcasRunning (kcas_casn_meta_size η - 1))
    }}}
      kcas_finish #gid #casn §After
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
  Admitted.
  #[local] Lemma kcas_finish_spec_winner_before gid casn η ι P :
    gid = kcas_casn_meta_winner η →
    {{{
      meta casn nroot η ∗
      kcas_casn_inv' ι casn η ∗
      kcas_winning η ∗
      saved_prop η.(kcas_casn_meta_post) P ∗
      P
    }}}
      kcas_finish #gid #casn §Before
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
  Admitted.
  #[local] Lemma kcas_finish_spec_after gid casn η ι i :
    kcas_casn_meta_size η - 1 ≤ i →
    {{{
      meta casn nroot η ∗
      kcas_casn_inv' ι casn η ∗
      kcas_lstatus_lb η (KcasRunning i)
    }}}
      kcas_finish #gid #casn §After
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
  Admitted.

  #[local] Lemma kcas_determine_as_get_as_determine_spec ι :
    ⊢ (
      ∀ casn η cass i,
      {{{
        ⌜cass = lst_to_val (drop i (kcas_casn_meta_cass casn η))⌝ ∗
        meta casn nroot η ∗
        kcas_casn_inv' ι casn η ∗
        kcas_lstatus_lb η (KcasRunning i)
      }}}
        kcas_determine_as #casn cass
      {{{
        RET #(kcas_casn_meta_success η);
        kcas_lstatus_lb η KcasFinished
      }}}
    ) ∧ (
      ∀ state casn η descr,
      {{{
        ⌜state = kcas_state casn descr⌝ ∗
        ⌜descr ∈ η.(kcas_casn_meta_descrs)⌝ ∗
        meta casn nroot η ∗
        kcas_casn_inv' ι casn η
      }}}
        kcas_get_as state
      {{{
        RET kcas_descr_final descr η;
        kcas_lstatus_lb η KcasFinished ∗
        £ 1
      }}}
    ) ∧ (
      ∀ casn η,
      {{{
        meta casn nroot η ∗
        kcas_casn_inv' ι casn η
      }}}
        kcas_determine #casn
      {{{
        RET #(kcas_casn_meta_success η);
        kcas_lstatus_lb η KcasFinished
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(Hdetermine_as & Hget_as & Hdetermine)".
    repeat iSplit.

    { iIntros "%casn %η %cass %i !> %Φ (-> & #Hcasn_meta & #Hcasn_inv' & #Hlstatus_lb) HΦ".
      iDestruct (kcas_casn_inv'_unfold with "Hcasn_inv'") as "(%P & #Hcasn_proph & #Hpost & %Hlocs & #Hcasn_inv & #Hlocs_inv)".

      wp_recs credit:"H£".
      wp_smart_apply (wp_id with "[//]") as (gid) "Hgid".

      destruct (η.(kcas_casn_meta_descrs) !! i) as [descr |] eqn:Hdescrs_lookup.

      - apply lookup_lt_Some in Hdescrs_lookup as Hi.
        erewrite drop_S; last first.
        { apply list_lookup_fmap_Some. naive_solver. }
        iDestruct (big_sepL_lookup with "Hlocs_inv") as "(Hloc_meta & Hloc_inv')"; first done.
        iDestruct (kcas_loc_inv'_elim with "Hloc_meta Hloc_inv'") as "Hloc_inv".
        wp_pures.

        wp_bind (!_)%E.
        iInv "Hloc_inv" as "(%casn' & %η' & %i' & %descr' & #Hcasn'_meta & >%Hdescrs'_lookup & >%Hloc' & Hloc & #Hlstatus'_lb & Hwitness' & #Hcasn'_inv')".
        wp_load.
        iDestruct (kcas_casn_inv'_unfold with "Hcasn'_inv'") as "(%P' & #Hcasn'_proph & #Hpost' & %Hlocs' & #Hcasn'_inv & #Hlocs'_inv)".
        iAssert ⌜descr'.(kcas_descr_meta) = descr.(kcas_descr_meta)⌝%I as %Hmeta'.
        { iDestruct (big_sepL_lookup with "Hlocs_inv") as "(Hloc_meta_1 & _)"; first done.
          iDestruct (big_sepL_lookup with "Hlocs'_inv") as "(Hloc_meta_2 & _)"; first done.
          iEval (rewrite -Hloc') in "Hloc_meta_2".
          iApply (meta_agree with "Hloc_meta_2 Hloc_meta_1").
        }
        destruct (decide (casn' = casn)) as [-> | Hcasn'].

        + iDestruct (meta_agree with "Hcasn_meta Hcasn'_meta") as %<-. iClear "Hcasn'_meta".
          assert (i' = i) as ->.
          { eapply NoDup_lookup; first done.
            - rewrite list_lookup_fmap Hdescrs'_lookup //.
            - rewrite list_lookup_fmap Hdescrs_lookup -Hloc' //.
          }
          simplify.
          iSplitR "HΦ". { iFrame. iSteps. }
          iModIntro. clear.

          wp_equal as ? | _; first naive_solver.
          wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus'_lb //] HΦ").

        + destruct (decide (gid = kcas_casn_meta_winner η ∧ descr.(kcas_descr_before) ≠ kcas_descr_final descr' η')) as [(-> & Hfail) | Hok%not_and_r_alt].

          * iInv "Hcasn_inv" as "(%status & %lstatus & %waiters & Hcasn_status & Hlstatus_auth & Hwaiters_auth & Hlstatus)".
            destruct lstatus as [j |]; last first.
            { iDestruct "Hlstatus" as "(%prophs & _ & _ & _ & _ & _ & >_Hgid & _)".
              iDestruct (identifier_model_exclusive with "Hgid _Hgid") as %[].
            }
            iDestruct "Hlstatus" as "(>-> & Hmodels & Hwitnesses & Hwaiters & Hproph & [(Hau & Hwinning) | >_Hgid])"; last first.
            { iDestruct (identifier_model_exclusive with "Hgid _Hgid") as %[]. }
            iMod (lc_fupd_elim_later with "H£ Hau") as "Hau".
            iSplitR "Hloc Hwitness' Hau Hwinning HΦ". { do 2 iFrame. iSteps. }
            iModIntro. clear j waiters.

            iMod (kcas_casn_wait _ _ P with "Hcasn'_inv Hwitness' [Hau]") as "(%waiter & Hwitness' & #Hwaiter & Hwaiters'_elem)"; [solve_ndisj | done.. | |].
            { admit.
            }

            iSplitR "Hwinning Hwaiters'_elem HΦ". { do 2 iFrame. iSteps. }
            iModIntro.

            wp_equal as _ | ?; last naive_solver.

            iClear "Hlstatus'_lb".
            wp_smart_apply ("Hget_as" with "[$Hcasn'_meta $Hcasn'_inv']") as "(#Hlstatus'_lb & H£)".
            { iSteps. iPureIntro. eapply elem_of_list_lookup_2. done. }
            iMod (kcas_casn_retrieve with "Hcasn'_inv Hlstatus'_lb Hwaiter Hwaiters'_elem") as "HP".

            wp_smart_apply wp_equal.
            rewrite bool_decide_eq_false_2 //.
            wp_smart_apply (kcas_finish_spec_winner_before with "[$Hcasn_meta $Hcasn_inv' $Hwinning $Hpost $HP] HΦ"); first done.

          * iSplitR "Hgid HΦ". { iFrame. iSteps. }
            iModIntro.

            wp_equal as _ | ?; last naive_solver.

            iClear "Hlstatus'_lb".
            wp_smart_apply ("Hget_as" with "[$Hcasn'_meta $Hcasn'_inv']") as "(#Hlstatus'_lb & H£)".
            { iSteps. iPureIntro. eapply elem_of_list_lookup_2. done. }

            wp_smart_apply wp_equal.
            destruct Hok as [(Hgid & Hfail) | Hok%dec_stable].

            -- rewrite bool_decide_eq_false_2 //.
               wp_smart_apply (kcas_finish_spec_loser with "[$Hcasn_meta $Hcasn_inv'] HΦ"); auto.

            -- rewrite bool_decide_eq_true_2 //.
               wp_pures.

               wp_bind (_.{status})%E.
               iInv "Hcasn_inv" as "(%status & %lstatus & %waiters & Hcasn_status & Hlstatus_auth & Hwaiters_auth & Hlstatus)".
               wp_load.
               destruct lstatus as [j |].

               ++ iDestruct "Hlstatus" as "(-> & Hlstatus)".
                  iSplitR "HΦ". { do 2 iFrame. iSteps. }
                  iModIntro. clear waiters j.

                  wp_pures.

                  wp_bind (CAS _ _ _).
                  iInv "Hloc_inv" as "(%casn'' & %η'' & %i'' & %descr'' & #Hcasn''_meta & >%Hdescrs''_lookup & >%Hloc'' & Hloc & #Hlstatus''_lb & Hwitness'' & #Hcasn''_inv')".
                  wp_cas as _ | (_ & _ & [= -> _ _]).

                  ** iSplitR "HΦ". { iFrame. iSteps. }
                     iModIntro.

                     wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb] HΦ").
                     { iPureIntro.
                       erewrite (drop_S _ _ i); first done.
                       rewrite list_lookup_fmap Hdescrs_lookup //.
                    }

                  ** iDestruct (meta_agree with "Hcasn'_meta Hcasn''_meta") as %<-. iClear "Hcasn''_meta Hcasn''_inv' Hlstatus''_lb".
                     assert (i'' = i') as ->.
                     { eapply NoDup_lookup; first done.
                       - rewrite list_lookup_fmap Hdescrs''_lookup //.
                       - rewrite list_lookup_fmap Hdescrs'_lookup /=. congruence.
                     }
                     simplify.

                     iInv "Hcasn'_inv" as "(%status' & %lstatus' & %waiters' & Hcasn'_status & >Hlstatus'_auth & Hwaiters'_auth & Hlstatus')".
                     iDestruct (kcas_lstatus_finished with "Hlstatus'_auth Hlstatus'_lb") as %->.
                     iDestruct "Hlstatus'" as "(%prophs' & >-> & Hmodels' & Hwaiters' & Hproph' & Hwinning' & Hwinner' & HP')".
                     iDestruct (big_sepL_lookup_acc with "Hmodels'") as "([>Hmodel₂ | >Hwitness'] & Hmodels')"; first done; last first.
                     { iDestruct (kcas_witness_exclusive with "Hwitness'' Hwitness'") as %[]. }

                     iDestruct ("Hmodels'" with "[$Hwitness'']") as "Hmodels'".
                     iSplitR "Hloc Hmodel₂ HΦ". { do 2 iFrame. iSteps. }
                     iModIntro. clear waiters' prophs'.

                     iEval (rewrite Hmeta') in "Hmodel₂".
                     iInv "Hcasn_inv" as "(%status & %lstatus & %waiters & Hcasn_status & >Hlstatus_auth & Hwaiters_auth & Hlstatus)".
                     destruct lstatus as [j |]; last first.
                     { iDestruct "Hlstatus" as "(%prophs & >-> & Hmodels & Hwaiters & Hproph & Hwinning & Hwinner & HP)".
                       admit.
                     }
                     iDestruct "Hlstatus" as "(>-> & >Hmodels & >Hwitnesses & Hwaiters & Hproph & HP)".
                     iAssert ⌜j = i⌝%I as %->.
                     { destruct (Nat.lt_trichotomy j i) as [? | [-> | ?]].
                       - iDestruct (kcas_lstatus_le with "Hlstatus_auth Hlstatus_lb") as %?. lia.
                       - iSteps.
                       - iDestruct (big_sepL_lookup with "Hmodels") as "_Hmodel₂".
                         { apply lookup_take_Some. done. }
                         iDestruct (kcas_model₂_exclusive with "Hmodel₂ _Hmodel₂") as %[].
                     }
                     iMod (kcas_lstatus_update (KcasRunning (S i)) with "Hlstatus_auth") as "Hlstatus_auth"; first done.
                     iClear "Hlstatus_lb". iDestruct (kcas_lstatus_lb_get with "Hlstatus_auth") as "#Hlstatus_lb".
                     iEval (rewrite -Hok) in "Hmodel₂".
                     iDestruct (big_sepL_snoc_2 with "Hmodels Hmodel₂") as "Hmodels"; first done.
                     iEval (rewrite -take_S_r //) in "Hmodels".
                     rewrite -(Nat.succ_pred_pos (kcas_casn_meta_size η - i)).
                     { rewrite /kcas_casn_meta_size. lia. }
                     rewrite -cons_seq.
                     iDestruct "Hwitnesses" as "(Hwitness & Hwitnesses)".
                     iEval (rewrite Nat.add_0_r) in "Hwitness".
                     iDestruct (big_sepL_seq_shift_2 1 0 with "Hwitnesses") as "Hwitnesses".
                     iEval (setoid_rewrite Nat.add_1_r) in "Hwitnesses".
                     iEval (setoid_rewrite Nat.add_succ_r) in "Hwitnesses".
                     assert (Nat.pred (kcas_casn_meta_size η - i) = kcas_casn_meta_size η - S i) as -> by lia.
                     iSplitR "Hloc Hwitness HΦ". { do 2 iFrame. iSteps. }
                     iModIntro. clear waiters.

                     iSplitR "HΦ". { iFrame. iSteps. }
                     iModIntro.

                     wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //] HΦ").

               ++ iDestruct "Hlstatus" as "(%prophs & -> & Hlstatus)".
                  iClear "Hlstatus_lb". iDestruct (kcas_lstatus_lb_get with "Hlstatus_auth") as "#Hlstatus_lb".
                  iSplitR "HΦ". { do 2 iFrame. iSteps. }
                  iModIntro. clear waiters prophs.

                  rewrite /kcas_casn_meta_final.
                  destruct (kcas_casn_meta_success η); iSteps.

      - rewrite drop_lookup_None //.
        { rewrite list_lookup_fmap Hdescrs_lookup //. }
        wp_smart_apply (kcas_finish_spec_after with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb]").
        { rewrite lookup_ge_None in Hdescrs_lookup.
          rewrite /kcas_casn_meta_size. lia.
        }
        iSteps.
    }

    { iIntros "%state %casn %η %descr !> %Φ (-> & %Hdescr & #Hcasn_meta & #Hcasn_inv') HΦ".

      wp_recs credit:"H£".
      wp_smart_apply ("Hdetermine" with "[$Hcasn_meta $Hcasn_inv']") as "#Hlstatus_lb".
      rewrite /kcas_descr_final.
      destruct (kcas_casn_meta_success η); iSteps.
    }

    { iIntros "%casn %η !> %Φ (#Hcasn_meta & #Hcasn_inv') HΦ".
      iDestruct (kcas_casn_inv'_unfold with "Hcasn_inv'") as "(%P & #Hcasn_proph & #Hpost & %Hlocs & #Hcasn_inv & #Hlocs_inv)".

      wp_recs.

      wp_bind ((#casn).{status})%E.
      iInv "Hcasn_inv" as "(%status & %lstatus & %waiters & Hcasn_status & Hlstatus_auth & Hwaiters_auth & Hlstatus)".
      wp_load.
      destruct lstatus as [i |].

      - iDestruct "Hlstatus" as "(-> & Hlstatus)".
        iDestruct (kcas_lstatus_lb_get_running0 with "Hlstatus_auth") as "#Hlstatus_lb".
        iSplitR "HΦ". { do 2 iFrame. iSteps. }
        iModIntro. clear.

        wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //]").
        iSteps.

      - iDestruct "Hlstatus" as "(%prophs & -> & Hlstatus)".
        iDestruct (kcas_lstatus_lb_get with "Hlstatus_auth") as "#Hlstatus_lb".
        iSplitR "HΦ". { do 2 iFrame. iSteps. }
        iModIntro. clear.

        rewrite /kcas_casn_meta_final.
        destruct (kcas_casn_meta_success η); iSteps.
    }
  Admitted.
  #[local] Lemma kcas_determine_as_spec casn η ι cass i :
    cass = lst_to_val (drop i (kcas_casn_meta_cass casn η)) →
    {{{
      meta casn nroot η ∗
      kcas_casn_inv' ι casn η ∗
      kcas_lstatus_lb η (KcasRunning i)
    }}}
      kcas_determine_as #casn cass
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
    iDestruct kcas_determine_as_get_as_determine_spec as "(H & _)".
    iIntros (->) "%Φ (#Hcasn_meta & #Hcasn_inv' & #Hlstatus_lb) HΦ".
    wp_apply ("H" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //] HΦ").
  Qed.
  #[local] Lemma kcas_get_as_spec state casn η ι descr :
    state = kcas_state casn descr →
    descr ∈ η.(kcas_casn_meta_descrs) →
    {{{
      meta casn nroot η ∗
      kcas_casn_inv' ι casn η
    }}}
      kcas_get_as state
    {{{
      RET kcas_descr_final descr η;
      kcas_lstatus_lb η KcasFinished ∗
      £ 1
    }}}.
  Proof.
    iDestruct kcas_determine_as_get_as_determine_spec as "(_ & H & _)".
    iIntros (-> Hdescr) "%Φ (#Hcasn_meta & #Hcasn_inv') HΦ".
    wp_apply ("H" with "[$Hcasn_meta $Hcasn_inv' //] HΦ").
  Qed.
  #[local] Lemma kcas_determine_spec casn η ι :
    {{{
      meta casn nroot η ∗
      kcas_casn_inv' ι casn η
    }}}
      kcas_determine #casn
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
    iDestruct kcas_determine_as_get_as_determine_spec as "(_ & _ & H)".
    iIntros "%Φ (#Hcasn_meta & #Hcasn_inv') HΦ".
    wp_apply ("H" with "[$Hcasn_meta $Hcasn_inv' //] HΦ").
  Qed.

  Lemma kcas_make_spec ι v :
    {{{
      True
    }}}
      kcas_make v
    {{{ loc,
      RET #loc;
      kcas_loc_inv loc ι ∗
      kcas_loc_model loc v
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_apply (wp_id with "[//]") as (gid) "Hgid".
    wp_smart_apply (typed_prophet_wp_proph kcas_prophet with "[//]") as (pid prophs) "Hproph_model".
    wp_block casn as "Hcasn_meta" "(Hcasn_state & Hcasn_proph & _)".
    iMod (pointsto_persist with "Hcasn_proph") as "#Hcasn_proph".
    wp_reveal bid.
    wp_ref loc as "Hloc_meta" "Hloc".

    iMod kcas_model_alloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (meta_set _ _ γ with "Hloc_meta") as "#Hloc_meta"; first done.

    iMod (saved_prop_alloc True) as "(%η_post & #Hpost)".
    iMod (kcas_lstatus_alloc KcasFinished) as "(%η_lstatus & Hlstatus_auth)".
    iMod kcas_witness_alloc as "(%η_witness & Hwitness)".
    iMod kcas_waiters_alloc as "(%η_waiters & Hwaiters_auth)".
    iMod kcas_winning_alloc as "(%η_winning & Hwinning)".
    iMod kcas_owner_alloc as "(%η_owner & Howner)".

    pose descr := {|
      kcas_descr_loc := loc ;
      kcas_descr_meta := γ ;
      kcas_descr_before := v ;
      kcas_descr_after := v ;
      kcas_descr_state := bid ;
    |}.
    pose η := {|
      kcas_casn_meta_descrs := [descr] ;
      kcas_casn_meta_prophet := pid ;
      kcas_casn_meta_prophs := ((gid, true) :: prophs) ;
      kcas_casn_meta_undetermined := bid ;
      kcas_casn_meta_post := η_post ;
      kcas_casn_meta_lstatus := η_lstatus ;
      kcas_casn_meta_witnesses := [η_witness] ;
      kcas_casn_meta_waiters := η_waiters ;
      kcas_casn_meta_winning := η_winning ;
      kcas_casn_meta_owner := η_owner ;
    |}.
    iMod (meta_set _ _ η with "Hcasn_meta") as "#Hcasn_meta"; first done.

    iDestruct (kcas_lstatus_lb_get_finished (η := η) (KcasRunning 1) with "Hlstatus_auth") as "#Hlstatus_lb".

    iMod (inv_alloc _ _ (kcas_casn_inv_inner casn η ι True) with "[Hgid Hproph_model Hcasn_state Hmodel₂ Hlstatus_auth Hwaiters_auth Hwinning Howner]") as "#Hcasn_inv".
    { iExists KcasAfter, KcasFinished, ∅.
      setoid_rewrite big_sepM_empty. iSteps.
    }

    iAssert (|={⊤}=> kcas_loc_inv' ι loc)%I with "[Hloc Hwitness]" as ">#Hloc_inv'".
    { iApply kcas_loc_inv'_intro.
      iApply inv_alloc.
      iExists casn, η, 0, descr.
      setoid_rewrite <- (fixpoint_A_unfold (kcas_casn_inv_pre ι) (kcas_loc_inv_pre ι) _).
      iSteps. iPureIntro. apply NoDup_singleton.
    }

    iDestruct (kcas_casn_inv'_unfold with "[$Hcasn_inv]") as "#Hcasn_inv'".
    { iSteps. iPureIntro. apply NoDup_singleton. }

    iSteps.
  Qed.

  Lemma kcas_get_spec loc ι :
    <<<
      kcas_loc_inv loc ι
    | ∀∀ v,
      kcas_loc_model loc v
    >>>
      kcas_get #loc @ ↑ι
    <<<
      kcas_loc_model loc v
    | RET v;
      True
    >>>.
  Proof.
    iIntros "!> %Φ (%γ & #Hloc_meta & #Hloc_inv') HΦ".
    iDestruct (kcas_loc_inv'_elim with "Hloc_meta Hloc_inv'") as "#Hloc_inv".

    wp_rec credit:"H£1".

    wp_bind (!_)%E.
    iInv "Hloc_inv" as "(%casn & %η & %i & %descr & #Hcasn_meta & >%Hdescrs_lookup & >-> & Hloc & #Hlstatus_lb & Hwitness & #Hcasn_inv')".
    wp_load.
    iDestruct (kcas_casn_inv'_unfold with "Hcasn_inv'") as "(%P & #Hcasn_proph & #Hpost & %Hlocs & #Hcasn_inv & #Hlocs_inv)".
    iDestruct (big_sepL_lookup with "Hlocs_inv") as "(_Hloc_meta & _)"; first done.
    iDestruct (meta_agree with "Hloc_meta _Hloc_meta") as %->. iClear "_Hloc_meta".
    iMod (kcas_casn_wait _ _ (Φ (kcas_descr_final descr η)) with "Hcasn_inv Hwitness [HΦ]") as "(%waiter & Hwitness & #Hwaiter & Hwaiters_elem)"; [solve_ndisj | done.. | |].
    { rewrite /kcas_waiter_au'. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%v (%γ & _Hloc_meta & Hmodel₁)".
      iDestruct (meta_agree with "Hloc_meta _Hloc_meta") as %<-. iClear "_Hloc_meta".
      iAaccIntro with "Hmodel₁"; iSteps.
    }
    iSplitR "H£1 Hwaiters_elem". { iFrame. iSteps. }
    iModIntro. clear Hlocs.

    iApply wp_fupd. iClear "Hlstatus_lb".
    wp_apply (kcas_get_as_spec with "[$Hcasn_meta $Hcasn_inv']") as "(#Hlstatus_lb & H£2)"; first done.
    { eapply elem_of_list_lookup_2. done. }
    iMod (kcas_casn_retrieve with "Hcasn_inv Hlstatus_lb Hwaiter Hwaiters_elem") as "HΦ".
    iMod (lc_fupd_elim_later with "H£1 HΦ") as "HΦ".
    iApply (lc_fupd_elim_later with "H£2 HΦ").
  Qed.
End kcas_G.

#[global] Opaque kcas_make.
#[global] Opaque kcas_get.
#[global] Opaque kcas_cas.

#[global] Opaque kcas_loc_inv.
#[global] Opaque kcas_loc_model.
