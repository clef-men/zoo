From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.auth_mono
  lib.excl
  lib.saved_prop
  lib.mono_list.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  typed_prophet
  identifier.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  lst.
From zoo_kcas Require Import
  kcas_1__types.
From zoo_kcas Require Export
  kcas_1__code.
From zoo Require Import
  options.

Implicit Types b full : bool.
Implicit Types i : nat.
Implicit Types l loc casn : location.
Implicit Types casns : list location.
Implicit Types gid : identifier.
Implicit Types v state : val.
Implicit Types cas : location * (val * val).
Implicit Types cass : list (location * (val * val)).
Implicit Types helpers : gmap gname nat.

Axiom wp_equal : ∀ `{zoo_G : !ZooG Σ} v1 v2 E Φ,
  ▷ Φ #(bool_decide (v1 = v2)) ⊢
  WP v1 == v2 @ E {{ Φ }}.

#[local] Program Definition prophet := {|
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
Solve Obligations of prophet with
  try done.
Next Obligation.
  intros (gid & b) v ->. done.
Qed.
Implicit Types prophs : list prophet.(typed_prophet_type).

Record loc_metadata := {
  loc_metadata_model : gname ;
  loc_metadata_history : gname ;
}.
Implicit Types γ : loc_metadata.

#[local] Instance loc_metadata_inhabited : Inhabited loc_metadata :=
  populate {|
    loc_metadata_model := inhabitant ;
    loc_metadata_history := inhabitant ;
  |}.
#[local] Instance loc_metadata_eq_dec : EqDecision loc_metadata :=
  ltac:(solve_decision).
#[local] Instance loc_metadata_countable :
  Countable loc_metadata.
Proof.
  solve_countable.
Qed.

Record descriptor := {
  descriptor_loc : location ;
  descriptor_meta : loc_metadata ;
  descriptor_before : val ;
  descriptor_after : val ;
  descriptor_state : block_id ;
}.
Implicit Types descr : descriptor.
Implicit Types descrs : list descriptor.

#[local] Instance descriptor_inhabited : Inhabited descriptor :=
  populate {|
      descriptor_loc := inhabitant ;
      descriptor_meta := inhabitant ;
      descriptor_before := inhabitant ;
      descriptor_after := inhabitant ;
      descriptor_state := inhabitant ;
    |}.
#[local] Instance descriptor_eq_dec : EqDecision descriptor :=
  ltac:(solve_decision).
#[local] Instance descriptor_countable :
  Countable descriptor.
Proof.
  solve_countable.
Qed.

#[local] Definition state_to_val casn descr : val :=
  ‘0@descr.(descriptor_state)(
    #casn,
    descr.(descriptor_before),
    descr.(descriptor_after)
  ).

Inductive status :=
  | Undetermined
  | After
  | Before.
Implicit Types status : status.

Inductive final_status :=
  | FinalAfter
  | FinalBefore.
Implicit Types fstatus : final_status.

Definition final_status_to_bool fstatus :=
  if fstatus then true else false.
#[global] Arguments final_status_to_bool !_ : assert.
Definition final_status_of_bool b :=
  if b then FinalAfter else FinalBefore.
#[global] Arguments final_status_of_bool !_ : assert.
Definition final_status_to_val fstatus :=
  match fstatus with
  | FinalAfter =>
      §After
  | FinalBefore =>
      §Before
  end%V.
#[global] Arguments final_status_to_val !_ : assert.

#[local] Instance final_status_to_val_physical fstatus :
  ValPhysical (final_status_to_val fstatus).
Proof.
  destruct fstatus; done.
Qed.

#[local] Lemma final_status_to_of_bool b :
  final_status_to_bool (final_status_of_bool b) = b.
Proof.
  destruct b; done.
Qed.

Record metadata := {
  metadata_descrs : list descriptor ;
  metadata_prophet : prophet_id ;
  metadata_prophs : list prophet.(typed_prophet_type) ;
  metadata_undetermined : block_id ;
  metadata_post : gname ;
  metadata_lstatus : gname ;
  metadata_locks : list gname ;
  metadata_helpers : gname ;
  metadata_winning : gname ;
  metadata_owner : gname ;
}.
Implicit Types η : metadata.

#[local] Instance metadata_inhabited : Inhabited metadata :=
  populate {|
    metadata_descrs := inhabitant ;
    metadata_prophet := inhabitant ;
    metadata_prophs := inhabitant ;
    metadata_undetermined := inhabitant ;
    metadata_post := inhabitant ;
    metadata_lstatus := inhabitant ;
    metadata_locks := inhabitant ;
    metadata_helpers := inhabitant ;
    metadata_winning := inhabitant ;
    metadata_owner := inhabitant ;
  |}.
#[local] Instance metadata_eq_dec : EqDecision metadata :=
  ltac:(solve_decision).
#[local] Instance metadata_countable :
  Countable metadata.
Proof.
  solve_countable.
Qed.

#[local] Definition metadata_size η :=
  length η.(metadata_descrs).
#[local] Definition metadata_cass casn η :=
  (λ descr,
    (#descr.(descriptor_loc), state_to_val casn descr)%V
  ) <$> η.(metadata_descrs).
#[local] Definition metadata_outcome η :=
  hd inhabitant η.(metadata_prophs).
#[local] Definition metadata_winner η :=
  (metadata_outcome η).1.
#[local] Definition metadata_success η :=
  (metadata_outcome η).2.
#[local] Definition metadata_final η :=
  final_status_of_bool (metadata_success η).

#[local] Instance status_inhabited : Inhabited status :=
  populate Undetermined.

#[local] Definition status_to_val casn η status : val :=
  match status with
  | Undetermined =>
      ‘Undetermined@η.(metadata_undetermined)( lst_to_val $ metadata_cass casn η )
  | After =>
      §After
  | Before =>
      §Before
  end.

#[local] Instance status_to_val_physical casn η status :
  ValPhysical (status_to_val casn η status).
Proof.
  destruct status; done.
Qed.

Inductive lstatus :=
  | Running i
  | Finished.
Implicit Types lstatus : lstatus.

#[local] Instance lstatus_inhabited : Inhabited lstatus :=
  populate Finished.

Inductive lstep : lstatus → lstatus → Prop :=
  | lstep_incr i :
      lstep (Running i) (Running (S i))
  | lstep_finish i :
      lstep (Running i) Finished.
#[local] Hint Constructors lstep : core.

#[local] Lemma lsteps_running0 lstatus :
  rtc lstep (Running 0) lstatus.
Proof.
  destruct lstatus as [i |].
  - induction i; first done.
    eapply rtc_r; [done | constructor].
  - apply rtc_once. done.
Qed.
#[local] Lemma lstep_finished lstatus :
  ¬ lstep Finished lstatus.
Proof.
  inversion 1.
Qed.
#[local] Lemma lsteps_finished lstatus :
  rtc lstep Finished lstatus →
  lstatus = Finished.
Proof.
  inversion 1 as [| ? ? ? []] => //.
Qed.
#[local] Lemma lsteps_le lstatus1 i1 lstatus2 i2 :
  rtc lstep lstatus1 lstatus2 →
  lstatus1 = Running i1 →
  lstatus2 = Running i2 →
  i1 ≤ i2.
Proof.
  intros Hlsteps. move: i1. induction Hlsteps as [lstatus | lstatus1 ? lstatus2 Hlstep Hlsteps IH] => i1.
  - naive_solver.
  - intros -> ->. invert Hlstep.
    + specialize (IH (S i1)). lia.
    + apply lsteps_finished in Hlsteps as [=].
Qed.

#[local] Definition descriptor_final descr η :=
  if metadata_success η then
    descr.(descriptor_after)
  else
    descr.(descriptor_before).

Class KcasG Σ `{zoo_G : !ZooG Σ} := {
  #[local] kcas_G_model_G :: TwinsG Σ val_O ;
  #[local] kcas_G_saved_prop :: SavedPropG Σ ;
  #[local] kcas_G_lstatus_G :: AuthMonoG (A := leibnizO lstatus) Σ lstep ;
  #[local] kcas_G_history_G :: MonoListG Σ location ;
  #[local] kcas_G_lock_G :: ExclG Σ unitO ;
  #[local] kcas_G_helpers_G :: ghost_mapG Σ gname nat ;
  #[local] kcas_G_winning_G :: ExclG Σ unitO ;
  #[local] kcas_G_owner_G :: ExclG Σ unitO ;
}.

Definition kcas_Σ := #[
  twins_Σ val_O ;
  saved_prop_Σ ;
  auth_mono_Σ (A := leibnizO lstatus) lstep ;
  mono_list_Σ location ;
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

  #[local] Definition model₁' γ_model v :=
    twins_twin1 γ_model (DfracOwn 1) v.
  #[local] Definition model₁ γ v :=
    model₁' γ.(loc_metadata_model) v.
  #[local] Definition model₂' γ_model v :=
    twins_twin2 γ_model v.
  #[local] Definition model₂ γ v :=
    model₂' γ.(loc_metadata_model) v.

  #[local] Definition lstatus_auth' η_lstatus lstatus :=
    auth_mono_auth _ η_lstatus (DfracOwn 1) lstatus.
  #[local] Definition lstatus_auth η lstatus :=
    lstatus_auth' η.(metadata_lstatus) lstatus.
  #[local] Definition lstatus_lb η lstatus :=
    auth_mono_lb _ η.(metadata_lstatus) lstatus.

  #[local] Definition history_auth' γ_history casns : iProp Σ :=
    mono_list_auth γ_history (DfracOwn 1) casns ∗
    ⌜NoDup casns⌝ ∗
    [∗ list] casn ∈ removelast casns,
      ∃ η,
      meta casn nroot η ∗
      lstatus_lb η Finished.
  #[local] Definition history_auth γ casns :=
    history_auth' γ.(loc_metadata_history) casns.
  #[local] Definition history_lb γ casns : iProp Σ :=
    mono_list_lb γ.(loc_metadata_history) casns ∗
    ⌜NoDup casns⌝.
  #[local] Definition history_elem' γ_history casn : iProp Σ :=
    mono_list_elem γ_history casn.
  #[local] Definition history_elem γ casn :=
    history_elem' γ.(loc_metadata_history) casn.

  #[local] Definition lock' η_lock :=
    excl η_lock ().
  #[local] Definition lock η i : iProp Σ :=
    ∃ η_lock,
    ⌜η.(metadata_locks) !! i = Some η_lock⌝ ∗
    lock' η_lock.

  #[local] Definition helpers_auth' η_helpers helpers :=
    ghost_map_auth η_helpers 1 helpers.
  #[local] Definition helpers_auth η helpers :=
    helpers_auth' η.(metadata_helpers) helpers.
  #[local] Definition helpers_elem η helper i :=
    ghost_map_elem η.(metadata_helpers) helper (DfracOwn 1) i.

  #[local] Definition winning' η_winning :=
    excl η_winning ().
  #[local] Definition winning η :=
    winning' η.(metadata_winning).

  #[local] Definition owner' η_owner :=
    excl η_owner ().
  #[local] Definition owner η :=
    owner' η.(metadata_owner).

  #[local] Definition au η ι P : iProp Σ :=
    AU <{
      ∃∃ vs,
      [∗ list] descr; v ∈ η.(metadata_descrs); vs,
        model₁ descr.(descriptor_meta) v
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ( ∃ i descr v,
        ⌜η.(metadata_descrs) !! i = Some descr⌝ ∗
        ⌜vs !! i = Some v⌝ ∗
        ⌜descr.(descriptor_before) ≠ v⌝ ∗
        [∗ list] descr; v ∈ η.(metadata_descrs); vs,
          model₁ descr.(descriptor_meta) v
      ) ∨ (
        ⌜Forall2 (λ descr v, descr.(descriptor_before) = v) η.(metadata_descrs) vs⌝ ∗
        [∗ list] descr ∈ η.(metadata_descrs),
          model₁ descr.(descriptor_meta) descr.(descriptor_after)
      )
    , COMM
      P
    }>.

  #[local] Definition helper_au' η ι descr Q : iProp Σ :=
    AU <{
      ∃∃ v,
      model₁ descr.(descriptor_meta) v
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ⌜v = descriptor_final descr η⌝ ∗
      model₁ descr.(descriptor_meta) v
    , COMM
      Q
    }>.
  #[local] Definition helper_au η ι i Q : iProp Σ :=
    ∃ descr,
    ⌜η.(metadata_descrs) !! i = Some descr⌝ ∗
    helper_au' η ι descr Q.

  #[local] Definition casn_inv_inner casn η ι P : iProp Σ :=
    ∃ v_status lstatus helpers prophs,
    casn.[status] ↦ v_status ∗
    lstatus_auth η lstatus ∗
    helpers_auth η helpers ∗
    typed_prophet_model prophet η.(metadata_prophet) prophs ∗
    match lstatus with
    | Running i =>
        ⌜v_status = status_to_val casn η Undetermined⌝ ∗
        ⌜prophs = η.(metadata_prophs)⌝ ∗
        ( [∗ list] descr ∈ take i η.(metadata_descrs),
          model₂ descr.(descriptor_meta) descr.(descriptor_before) ∗
          history_elem descr.(descriptor_meta) casn
        ) ∗
        ( [∗ list] j ∈ seq 0 (metadata_size η - i),
          lock η (i + j)
        ) ∗
        ( [∗ map] helper ↦ j ∈ helpers,
          ∃ Q,
          ⌜j < i⌝ ∗
          saved_prop helper Q ∗
          helper_au η ι j Q
        ) ∗
        ( au η ι P ∗
          winning η
        ∨ identifier_model (metadata_winner η)
        )
    | Finished =>
        ⌜v_status = final_status_to_val (metadata_final η)⌝ ∗
        ( [∗ list] i ↦ descr ∈ η.(metadata_descrs),
          ( model₂ descr.(descriptor_meta) (descriptor_final descr η)
          ∨ lock η i
          ) ∗
          if metadata_success η then
            history_elem descr.(descriptor_meta) casn
          else
            True
        ) ∗
        ( [∗ map] helper ↦ _ ∈ helpers,
          ∃ Q,
          saved_prop helper Q ∗
          Q
        ) ∗
        winning η ∗
        identifier_model (metadata_winner η) ∗
        (owner η ∨ P)
    end.
  #[local] Instance : CustomIpatFormat "casn_inv_inner" :=
    "(
      %status{} &
      %lstatus{} &
      %helpers{} &
      %prophs{} &
      {>=}Hcasn{}_status &
      {>=}Hlstatus{}_auth &
      {>=}Hhelpers{}_auth &
      {>=}Hproph{} &
      Hlstatus{}
    )".
  #[local] Instance : CustomIpatFormat "casn_inv_inner_running" :=
    "(
      {>=}-> &
      {>=}-> &
      {>=}Hmodels₂ &
      {>=}Hlocks &
      Hhelpers &
      Hau
    )".
  #[local] Instance : CustomIpatFormat "casn_inv_inner_finished" :=
    "(
      {>=}-> &
      {>=}Hmodels{}₂ &
      Hhelpers{} &
      {>=}Hwinning{} &
      {>=}Hwinner{} &
      HP{}
    )".
  #[local] Definition casn_inv_pre ι
    (casn_inv' : location * metadata * option nat -d> iProp Σ)
    (loc_inv' : location * loc_metadata -d> iProp Σ)
  : location * metadata * option nat -d> iProp Σ
  :=
    λ '(casn, η, i), (
      ∃ P,
      casn.[proph] ↦□ #η.(metadata_prophet) ∗
      saved_prop η.(metadata_post) P ∗
      ⌜NoDup (descriptor_loc <$> η.(metadata_descrs))⌝ ∗
      inv (ι.@"casn") (casn_inv_inner casn η ι P) ∗
      ( if i is Some i then
          [∗ list] j ↦ descr ∈ η.(metadata_descrs),
          if decide (j = i) then
            meta descr.(descriptor_loc) nroot descr.(descriptor_meta)
          else
            meta descr.(descriptor_loc) nroot descr.(descriptor_meta) ∗
            loc_inv' (descr.(descriptor_loc), descr.(descriptor_meta))
        else
          [∗ list] descr ∈ η.(metadata_descrs),
          meta descr.(descriptor_loc) nroot descr.(descriptor_meta) ∗
          loc_inv' (descr.(descriptor_loc), descr.(descriptor_meta))
      )
    )%I.
  #[local] Instance : CustomIpatFormat "casn_inv" :=
    "(
      %P{} &
      Hcasn{}_proph &
      Hpost{} &
      %Hlocs{} &
      Hcasn{}_inv &
      Hlocs{}_inv
    )".
  #[local] Instance casn_inv_pre_contractive ι n :
    Proper (dist_later n ==> (≡{n}≡) ==> (≡{n}≡)) (casn_inv_pre ι).
  Proof.
    solve_proper.
  Qed.

  #[local] Definition loc_inv_inner'' full casn_inv' loc γ : iProp Σ :=
    ∃ casns casn η i descr,
    meta casn nroot η ∗
    ⌜η.(metadata_descrs) !! i = Some descr⌝ ∗
    ⌜loc = descr.(descriptor_loc)⌝ ∗
    loc ↦ᵣ state_to_val casn descr ∗
    lstatus_lb η (Running (S i)) ∗
    lock η i ∗
    history_auth γ (casns ++ [casn]) ∗
    casn_inv' (casn, η, if full then None else Some i).
  #[local] Instance : CustomIpatFormat "loc_inv_inner" :=
    "(
      %casns{} &
      %casn{} &
      %η{} &
      %i{} &
      %descr{} &
      {>=}{#}Hcasn{}_meta &
      {>=}%Hdescrs{}_lookup &
      {>=}{%Hloc{}=->} &
      {>=}Hloc &
      {>=}{#}Hlstatus{}_lb &
      {>=}Hlock{} &
      {>=}Hhistory_auth &
      {#}Hcasn{}_inv'
    )".
  #[local] Definition loc_inv_inner' :=
    loc_inv_inner'' false.
  #[local] Definition loc_inv_pre ι
    (casn_inv' : location * metadata * option nat -d> iProp Σ)
    (loc_inv' : location * loc_metadata -d> iProp Σ)
  : location * loc_metadata -d> iProp Σ
  :=
    λ '(loc, γ),
      inv (ι.@"loc") (loc_inv_inner' casn_inv' loc γ).
  #[local] Instance loc_inv_pre_contractive ι n :
    Proper (dist_later n ==> dist_later n ==> (≡{n}≡)) (loc_inv_pre ι).
  Proof.
    rewrite /loc_inv_pre /loc_inv_inner' /loc_inv_inner'' /curry.
    solve_contractive.
  Qed.

  #[local] Definition casn_inv'' ι :=
    fixpoint_A (casn_inv_pre ι) (loc_inv_pre ι).
  #[local] Definition casn_inv' ι casn η :=
    casn_inv'' ι (casn, η, None).
  #[local] Definition casn_inv casn ι : iProp Σ :=
    ∃ η,
    meta casn nroot η ∗
    casn_inv' ι casn η.

  #[local] Definition loc_inv' ι :=
    fixpoint_B (casn_inv_pre ι) (loc_inv_pre ι).
  #[local] Definition loc_inv_inner loc γ ι : iProp Σ :=
    loc_inv_inner'' true (casn_inv'' ι) loc γ.
  Definition kcas_loc_inv loc ι : iProp Σ :=
    ∃ γ,
    meta loc nroot γ ∗
    loc_inv' ι (loc, γ).

  Definition kcas_loc_model loc v : iProp Σ :=
    ∃ γ,
    meta loc nroot γ ∗
    model₁ γ v.

  #[local] Lemma casn_inv''_unfold ι casn (i : option nat) η :
    casn_inv'' ι (casn, η, i) ⊣⊢
    casn_inv_pre ι (casn_inv'' ι) (loc_inv' ι) (casn, η, i).
  Proof.
    symmetry. apply (fixpoint_A_unfold (casn_inv_pre ι) (loc_inv_pre ι) _).
  Qed.
  #[local] Lemma casn_inv'_unfold ι casn η :
    casn_inv' ι casn η ⊣⊢
    casn_inv_pre ι (casn_inv'' ι) (loc_inv' ι) (casn, η, None).
  Proof.
    apply casn_inv''_unfold.
  Qed.

  #[local] Lemma loc_inv'_unfold loc γ ι :
    loc_inv' ι (loc, γ) ⊣⊢
    inv (ι.@"loc") (loc_inv_inner' (casn_inv'' ι) loc γ).
  Proof.
    symmetry. apply (fixpoint_B_unfold (casn_inv_pre ι) (loc_inv_pre ι) (loc, γ)).
  Qed.
  #[local] Lemma loc_inv'_intro loc γ ι :
    inv (ι.@"loc") (loc_inv_inner' (casn_inv'' ι) loc γ) ⊢
    loc_inv' ι (loc, γ).
  Proof.
    setoid_rewrite <- (fixpoint_B_unfold (casn_inv_pre ι) (loc_inv_pre ι) _).
    iIntros "#Hloc_inv".
    iApply (inv_alter with "Hloc_inv"). iIntros "!> !> (:loc_inv_inner #=)".
    iFrame. iSteps.
  Qed.
  #[local] Lemma loc_inv'_elim loc γ ι :
    meta loc nroot γ -∗
    loc_inv' ι (loc, γ) -∗
    inv (ι.@"loc") (loc_inv_inner loc γ ι).
  Proof.
    setoid_rewrite <- (fixpoint_B_unfold (casn_inv_pre ι) (loc_inv_pre ι) _).
    iIntros "#Hloc_meta #Hloc_inv".
    iApply (inv_alter with "Hloc_inv"). iIntros "!> !> (:loc_inv_inner #=)".
    iSplitL.
    - iFrame. iSteps.
      setoid_rewrite <- (fixpoint_A_unfold (casn_inv_pre ι) (loc_inv_pre ι) _).
      iDestruct "Hcasn_inv'" as "(:casn_inv)".
      iSteps.
      iApply (big_sepL_impl with "Hlocs_inv"). iIntros "!> %i' %descr' %Hdescr_lookup' H".
      case_decide; last iSteps.
      simplify.
      iDestruct (meta_agree with "Hloc_meta H") as %->.
      setoid_rewrite <- (fixpoint_B_unfold (casn_inv_pre ι) (loc_inv_pre ι) _).
      iSteps.
    - iSteps.
      setoid_rewrite <- (fixpoint_A_unfold (casn_inv_pre ι) (loc_inv_pre ι) _).
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
  #[local] Instance loc_inv'_persistent loc γ ι :
    Persistent (loc_inv' ι (loc, γ)).
  Proof.
    rewrite loc_inv'_unfold.
    apply _.
  Qed.
  #[global] Instance kcas_loc_inv_persistent loc γ ι :
    Persistent (kcas_loc_inv loc ι).
  Proof.
    rewrite /kcas_loc_inv.
    apply _.
  Qed.
  #[local] Instance casn_inv''_persistent casn η (i : option nat) ι :
    Persistent (casn_inv'' ι (casn, η, i)).
  Proof.
    rewrite casn_inv''_unfold.
    apply _.
  Qed.
  #[local] Instance casn_inv'_persistent casn η ι :
    Persistent (casn_inv' ι casn η).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc v :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model v ∗
      model₂' γ_model v.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma model_agree γ v1 v2 :
    model₁ γ v1 -∗
    model₂ γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma model_update {γ v1 v2} v :
    model₁ γ v1 -∗
    model₂ γ v2 ==∗
      model₁ γ v ∗
      model₂ γ v.
  Proof.
    apply twins_update'.
  Qed.
  #[local] Lemma model₂_exclusive γ v1 v2 :
    model₂ γ v1 -∗
    model₂ γ v2 -∗
    False.
  Proof.
    apply twins_twin2_exclusive.
  Qed.

  #[local] Lemma lstatus_alloc lstatus :
    ⊢ |==>
      ∃ η_lstatus,
      lstatus_auth' η_lstatus lstatus.
  Proof.
    apply: auth_mono_alloc.
  Qed.
  #[local] Lemma lstatus_lb_get η lstatus :
    lstatus_auth η lstatus ⊢
    lstatus_lb η lstatus.
  Proof.
    apply auth_mono_lb_get.
  Qed.
  #[local] Lemma lstatus_lb_get_running0 η lstatus :
    lstatus_auth η lstatus ⊢
    lstatus_lb η (Running 0).
  Proof.
    apply auth_mono_lb_get_mono, lsteps_running0.
  Qed.
  #[local] Lemma lstatus_lb_get_finished {η} lstatus :
    lstatus_auth η Finished ⊢
    lstatus_lb η lstatus.
  Proof.
    destruct lstatus.
    - apply auth_mono_lb_get_mono'. done.
    - apply lstatus_lb_get.
  Qed.
  #[local] Lemma lstatus_finished η lstatus :
    lstatus_auth η lstatus -∗
    lstatus_lb η Finished -∗
    ⌜lstatus = Finished⌝.
  Proof.
    iIntros "Hlstatus_auth Hlstatus_lb".
    iDestruct (auth_mono_lb_valid with "Hlstatus_auth Hlstatus_lb") as %->%lsteps_finished.
    iSteps.
  Qed.
  #[local] Lemma lstatus_le η i1 i2 :
    lstatus_auth η (Running i1) -∗
    lstatus_lb η (Running i2) -∗
    ⌜i2 ≤ i1⌝.
  Proof.
    iIntros "Hlstatus_auth Hlstatus_lb".
    iDestruct (auth_mono_lb_valid with "Hlstatus_auth Hlstatus_lb") as %Hlsteps.
    iPureIntro. eapply lsteps_le; done.
  Qed.
  #[local] Lemma lstatus_update {η lstatus} lstatus' :
    lstep lstatus lstatus' →
    lstatus_auth η lstatus ⊢ |==>
    lstatus_auth η lstatus'.
  Proof.
    apply auth_mono_update'.
  Qed.

  #[local] Lemma history_alloc casn :
    ⊢ |==>
      ∃ γ_history,
      history_auth' γ_history [casn] ∗
      history_elem' γ_history casn.
  Proof.
    iMod (mono_list_alloc [casn]) as "(%γ_history & Hhistory_auth)".
    iDestruct (mono_list_elem_get with "Hhistory_auth") as "#Hhistory_elem".
    { apply elem_of_list_singleton. done. }
    iSteps. iPureIntro.
    apply NoDup_singleton.
  Qed.
  #[local] Lemma history_lb_get γ casns :
    history_auth γ casns ⊢
    history_lb γ casns.
  Proof.
    iIntros "(Hhistory_auth & %Hcasns & _)".
    iDestruct (mono_list_lb_get with "Hhistory_auth") as "#Hhistory_lb".
    iSteps.
  Qed.
  #[local] Lemma history_lb_valid_eq γ casns1 casn casns2 casns3 :
    history_auth γ (casns1 ++ [casn]) -∗
    history_lb γ (casns2 ++ casn :: casns3) -∗
      ⌜casns1 = casns2⌝ ∗
      ⌜casns3 = []⌝.
  Proof.
    iIntros "(Hhistory_auth & %Hcasns1 & _) (Hhistory_lb & %Hcasns2)".
    iDestruct (mono_list_lb_valid with "Hhistory_auth Hhistory_lb") as %(casns4 & Heq).
    iPureIntro.
    rewrite (assoc _ _ [casn] casns3) -assoc in Heq.
    destruct (nil_or_length_pos (casns3 ++ casns4)) as [Hcasns34 | Hcasns34].
    - rewrite Hcasns34 right_id in Heq.
      apply (inj (λ casns, casns ++ [casn])) in Heq.
      destruct casns3; done.
    - opose proof* (NoDup_lookup (casns1 ++ [casn])).
      { done. }
      { rewrite lookup_snoc_Some. right. done. }
      { erewrite Heq, lookup_app_l_Some; first done.
        rewrite lookup_snoc_Some. right. done.
      }
      apply (f_equal length) in Heq. rewrite 3!length_app in Heq. lia.
  Qed.
  #[local] Lemma history_lb_valid_ne γ casns1 casn1 casns2 casn2 :
    casn1 ≠ casn2 →
    history_auth γ (casns1 ++ [casn1]) -∗
    history_lb γ (casns2 ++ [casn2]) -∗
      ∃ casns3,
      history_lb γ (casns2 ++ [casn2] ++ casns3 ++ [casn1]).
  Proof.
    iIntros "%Hne (Hhistory_auth & %Hcasns1 & _) (#Hhistory_lb2 & %Hcasns2)".
    iDestruct (mono_list_lb_get with "Hhistory_auth") as "#Hhistory_lb1".
    iDestruct (mono_list_lb_valid with "Hhistory_auth Hhistory_lb2") as %(casns3 & Heq).
    destruct (rev_elim casns3) as [-> | (casns4 & casn3 & ->)].
    - apply (f_equal last) in Heq.
      rewrite right_id !last_snoc in Heq.
      naive_solver.
    - apply (f_equal last) in Heq as H.
      rewrite assoc last_app_cons !last_snoc /= in H.
      injection H as <-.
      iExists casns4. rewrite assoc -Heq. iSteps.
  Qed.
  #[local] Lemma history_elem_valid γ casns casn :
    history_auth γ casns -∗
    history_elem γ casn -∗
    ⌜casn ∈ casns⌝.
  Proof.
    iIntros "(Hhistory_auth & _) Hhistory_elem".
    iApply (mono_list_elem_valid with "Hhistory_auth Hhistory_elem").
  Qed.
  #[local] Lemma history_running γ casns casn1 casn2 η2 i :
    history_auth γ (casns ++ [casn1]) -∗
    meta casn2 nroot η2 -∗
    lstatus_auth η2 (Running i) -∗
    ⌜casn2 ∉ casns⌝.
  Proof.
    iIntros "(Hhistory_auth & %Hcasns & Hcasns) Hcasn2_meta Hlstatus2_auth" ((j & Hcasns_lookup)%elem_of_list_lookup).
    iDestruct (big_sepL_lookup with "Hcasns") as "(%_η2 & _Hcasn2_meta & Hlstatus2_lb)".
    { rewrite removelast_last //. }
    iDestruct (meta_agree with "Hcasn2_meta _Hcasn2_meta") as %<-. iClear "_Hcasn2_meta".
    iDestruct (lstatus_finished with "Hlstatus2_auth Hlstatus2_lb") as %[=].
  Qed.
  #[local] Lemma history_update {γ casns casn1 η1} casn2 :
    casn2 ∉ casns →
    casn2 ≠ casn1 →
    history_auth γ (casns ++ [casn1]) -∗
    meta casn1 nroot η1 -∗
    lstatus_lb η1 Finished ==∗
      history_auth γ ((casns ++ [casn1]) ++ [casn2]) ∗
      history_elem γ casn2.
  Proof.
    iIntros "% % Hhistory_auth Hcasn1_meta Hlstatus1_lb".
    iDestruct "Hhistory_auth" as "(Hhistory_auth & %Hcasns & Hcasns)".
    iMod (mono_list_update_snoc casn2 with "Hhistory_auth") as "Hhistory_auth".
    iDestruct (mono_list_elem_get with "Hhistory_auth") as "#$"; first set_solver.
    iSteps.
    - iPureIntro.
      rewrite comm NoDup_cons not_elem_of_app elem_of_list_singleton //.
    - rewrite !removelast_last big_sepL_snoc. iSteps.
  Qed.
  #[local] Lemma history_update_running {γ casns casn1 η1} casn2 η2 i :
    casn1 ≠ casn2 →
    history_auth γ (casns ++ [casn1]) -∗
    meta casn1 nroot η1 -∗
    lstatus_lb η1 Finished -∗
    meta casn2 nroot η2 -∗
    lstatus_auth η2 (Running i) ==∗
      history_auth γ ((casns ++ [casn1]) ++ [casn2]) ∗
      history_elem γ casn2 ∗
      lstatus_auth η2 (Running i).
  Proof.
    iIntros "% Hhistory_auth Hcasn1_meta Hlstatus1_lb Hcasn2_meta Hlstatus2_auth".
    iDestruct (history_running with "Hhistory_auth Hcasn2_meta Hlstatus2_auth") as %?.
    iMod (history_update with "Hhistory_auth Hcasn1_meta Hlstatus1_lb") as "($ & $)"; [done.. |].
    iSteps.
  Qed.

  #[local] Lemma lock_alloc :
    ⊢ |==>
      ∃ η_lock,
      lock' η_lock.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma lock_allocs n :
    ⊢ |==>
      ∃ η_locks,
      ⌜length η_locks = n⌝ ∗
      [∗ list] η_lock ∈ η_locks,
        lock' η_lock.
  Proof.
    iInduction n as [| n] "IH".
    - iExists []. iSteps.
    - iMod lock_alloc as "(%η_lock & Hlock)".
      iMod "IH" as "(%η_locks & %Hlength & Hlocks)".
      iExists (η_lock :: η_locks). iSteps.
  Qed.
  #[local] Lemma lock_exclusive η i :
    lock η i -∗
    lock η i -∗
    False.
  Proof.
    iIntros "(%γ_lock & %Hlookup & Hexcl1) (%_γ_lock & %_Hlookup & Hexcl2)".
    simplify.
    iApply (excl_exclusive with "Hexcl1 Hexcl2").
  Qed.

  #[local] Lemma helpers_alloc :
    ⊢ |==>
      ∃ η_helpers,
      helpers_auth' η_helpers ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma helpers_insert {η helpers} i P :
    helpers_auth η helpers ⊢ |==>
      ∃ helper,
      helpers_auth η (<[helper := i]> helpers) ∗
      helpers_elem η helper i ∗
      saved_prop helper P.
  Proof.
    iIntros "Hhelpers_auth".
    iMod (saved_prop_alloc_cofinite (dom helpers)) as "(%helper & %Hhelper & #Hhelper)".
    iMod (ghost_map_insert with "Hhelpers_auth") as "(Hhelpers_auth & Hhelpers_elem)".
    { apply not_elem_of_dom. done. }
    iSteps.
  Qed.
  #[local] Lemma helpers_lookup η helpers helper i :
    helpers_auth η helpers -∗
    helpers_elem η helper i -∗
    ⌜helpers !! helper = Some i⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma helpers_delete η helpers helper i :
    helpers_auth η helpers -∗
    helpers_elem η helper i ==∗
    helpers_auth η (delete helper helpers).
  Proof.
    apply ghost_map_delete.
  Qed.

  #[local] Lemma winning_alloc :
    ⊢ |==>
      ∃ η_winning,
      winning' η_winning.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma winning_exclusive η :
    winning η -∗
    winning η -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  #[local] Lemma owner_alloc :
    ⊢ |==>
      ∃ η_owner,
      owner' η_owner.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma owner_exclusive η :
    owner η -∗
    owner η -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  #[local] Lemma casn_help {casn η ι P i} descr Q :
    η.(metadata_descrs) !! i = Some descr →
    inv (ι.@"casn") (casn_inv_inner casn η ι P) -∗
    lock η i -∗
    helper_au' η ι descr Q -∗
      |={⊤ ∖ ↑ι.@"loc"}=>
      ∃ helper,
      lock η i ∗
      saved_prop helper Q ∗
      helpers_elem η helper i.
  Proof.
    iIntros "%Hdescrs_lookup #Hcasn_inv Hlock H".
    iInv "Hcasn_inv" as "(:casn_inv_inner >)".
    iMod (helpers_insert i Q with "Hhelpers_auth") as "(%helper & Hhelpers_auth & Hhelpers_elem & #Hhelper)".
    destruct lstatus as [j |].

    - iDestruct "Hlstatus" as "(:casn_inv_inner_running >)".

      iAssert ⌜i < j⌝%I as %Hi.
      { destruct (decide (i < j)); first iSteps.
        iDestruct (big_sepL_lookup _ _ (i - j) (i - j) with "Hlocks") as "_Hlock".
        { apply lookup_lt_Some in Hdescrs_lookup.
          apply lookup_seq. rewrite /metadata_size. lia.
        }
        rewrite -Nat.le_add_sub; first lia.
        iDestruct (lock_exclusive with "Hlock _Hlock") as %[].
      }

      iDestruct (big_sepM_insert_2 _ _ helper i with "[H] Hhelpers") as "Hhelpers"; first iSteps.
      iSplitR "Hlock Hhelpers_elem". { do 2 iFrame. iSteps. }
      iModIntro.

      iFrame. iSteps.

    - iDestruct "Hlstatus" as "(:casn_inv_inner_finished >)".
      iDestruct (big_sepL_lookup_acc with "Hmodels₂") as "(([Hmodel₂ | _Hlock] & Hhistory_elem) & Hmodels₂)"; first done; last first.
      { iDestruct (lock_exclusive with "Hlock _Hlock") as %[]. }
      iApply (fupd_mask_mono (⊤ ∖ ↑ι)); first solve_ndisj.
      iMod "H" as "(%v & Hmodel₁ & _ & H)".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("H" with "[$Hmodel₁ //]") as "HQ".
      iDestruct ("Hmodels₂" with "[Hmodel₂ Hhistory_elem]") as "Hmodels₂"; first iSteps.
      iDestruct (big_sepM_insert_2 _ _ helper i with "[HQ] Hhelpers") as "Hhelpers"; first iSteps.
      iSplitR "Hlock Hhelpers_elem". { do 2 iFrame. iSteps. }
      iModIntro.

      iFrame. iSteps.
  Qed.
  #[local] Lemma casn_retrieve casn η ι P helper Q i :
    inv (ι.@"casn") (casn_inv_inner casn η ι P) -∗
    lstatus_lb η Finished -∗
    saved_prop helper Q -∗
    helpers_elem η helper i ={⊤}=∗
    ▷^2 Q.
  Proof.
    iIntros "#Hcasn_inv #Hlstatus_lb #Hhelper Hhelpers_elem".
    iInv "Hcasn_inv" as "(:casn_inv_inner >)".
    iDestruct (lstatus_finished with "Hlstatus_auth Hlstatus_lb") as %->.
    iDestruct "Hlstatus" as "(:casn_inv_inner_finished >)".
    iDestruct (helpers_lookup with "Hhelpers_auth Hhelpers_elem") as %Hhelpers_lookup.
    iMod (helpers_delete with "Hhelpers_auth Hhelpers_elem") as "Hhelpers_auth".
    iDestruct (big_sepM_delete with "Hhelpers") as "((%_Q & _Hhelper & HQ) & Hhelpers)"; first done.
    iDestruct (saved_prop_agree with "Hhelper _Hhelper") as "Heq".
    iSplitR "HQ Heq". { do 2 iFrame. iSteps. }
    iModIntro.

    do 3 iModIntro. iRewrite "Heq". iSteps.
  Qed.

  #[local] Lemma kcas_status_to_bool_spec fstatus :
    {{{
      True
    }}}
      kcas_status_to_bool (final_status_to_val fstatus)
    {{{
      RET #(final_status_to_bool fstatus);
      True
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    destruct fstatus; iSteps.
  Qed.

  #[local] Lemma kcas_finish_spec {gid casn η ι} fstatus :
    {{{
      meta casn nroot η ∗
      casn_inv' ι casn η ∗
      ( ( ⌜gid ≠ metadata_winner η⌝ ∗
          identifier_model gid
        ) ∨ (
          ∃ P,
          ⌜fstatus = FinalBefore⌝ ∗
          winning η ∗
          saved_prop η.(metadata_post) P ∗
          P
        ) ∨ (
          ∃ i,
          ⌜gid = metadata_winner η⌝ ∗
          identifier_model gid ∗
          ⌜fstatus = FinalAfter⌝ ∗
          ⌜metadata_size η ≤ i⌝ ∗
          lstatus_lb η (Running i)
        )
      )
    }}}
      kcas_finish #gid #casn (final_status_to_val fstatus)
    {{{
      RET #(metadata_success η);
      lstatus_lb η Finished
    }}}.
  Proof.
    iIntros "%Φ (#Hcasn_meta & #Hcasn_inv' & H) HΦ".
    iDestruct (casn_inv'_unfold with "Hcasn_inv'") as "(:casn_inv)".

    wp_rec. wp_pures.

    wp_bind (_.{status})%E.
    iInv "Hcasn_inv" as "(:casn_inv_inner >)".
    wp_load.
    destruct lstatus as [i |].

    - iDestruct "Hlstatus" as "(:casn_inv_inner_running)".
      iSplitR "H HΦ". { do 2 iFrame. iSteps. }
      iModIntro. clear.

      wp_smart_apply (kcas_status_to_bool_spec with "[//]") as "_".
      wp_load. wp_pures.

      wp_bind (Resolve _ _ _).
      wp_apply (wp_wand _ _ (λ _, lstatus_lb η Finished) with "[- HΦ]") as (res) "#Hlstatus_lb".

      { iInv "Hcasn_inv" as "(:casn_inv_inner >)".
        wp_apply (typed_prophet_wp_resolve prophet (_, _) with "Hproph"); [done.. |].
        destruct lstatus as [i |].

        - iDestruct "Hlstatus" as "(:casn_inv_inner_running >)".
          wp_cas as ? | _; first naive_solver.
          iIntros "!> %prophs %Hprophs Hproph".

          assert (metadata_success η = final_status_to_bool fstatus) as Hsuccess.
          { rewrite /metadata_success /metadata_outcome Hprophs //. }

          iAssert (
            ( [∗ list] descr ∈ take i η.(metadata_descrs),
              model₂ descr.(descriptor_meta) (descriptor_final descr η)
            ) ={⊤ ∖ ↑ι.@"casn"}=∗
              ( [∗ map] helper ↦ j ∈ helpers,
                ∃ Q,
                saved_prop helper Q ∗
                Q
              ) ∗
              ( [∗ list] descr ∈ take i η.(metadata_descrs),
                model₂ descr.(descriptor_meta) (descriptor_final descr η)
              )
          )%I with "[Hhelpers]" as "Hhelpers".
          { iIntros "Hmodels₂".
            iApply (big_sepM_impl_thread_fupd _ (
              λ helper j,
                ∃ Q,
                saved_prop helper Q ∗
                Q
            )%I with "Hhelpers Hmodels₂ []").
            iIntros "!> %helper %j %Hhelpers_lookup (%Q & %Hj & Hhelper & (%descr & %Hdescrs_lookup & HQ)) Hmodels₂".
            iDestruct (big_sepL_lookup_acc with "Hmodels₂") as "(Hmodel₂ & Hmodels₂)".
            { rewrite lookup_take_Some //. }
            iMod "HQ" as "(%v & Hmodel₁ & _ & HQ)".
            iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
            iSteps.
          }

          iDestruct "H" as "[(%Hgid & Hgid) | [(%_P & -> & Hwinning & _Hpost & HP) | (%j & -> & Hgid & -> & %Hj & #Hlstatus_lb)]]".

          + apply (f_equal (fst ∘ hd inhabitant)) in Hprophs. done.

          + iDestruct (saved_prop_agree with "Hpost _Hpost") as "Heq".
            iDestruct "Hau" as "[(Hau & _Hwinning) | Hwinner]".
            { iDestruct (winning_exclusive with "Hwinning _Hwinning") as %[]. }

            iDestruct (big_sepL_sep with "Hmodels₂") as "(Hmodels₂ & _)".
            iMod ("Hhelpers" with "[Hmodels₂]") as "(Hhelpers & Hmodels₂)".
            { rewrite /descriptor_final Hsuccess //. }

            iAssert (
              [∗ list] i ↦ descr ∈ η.(metadata_descrs),
              ( model₂ descr.(descriptor_meta) (descriptor_final descr η)
              ∨ lock η i
              ) ∗
              if metadata_success η then
                history_elem descr.(descriptor_meta) casn
              else
                True
            )%I with "[Hmodels₂ Hlocks]" as "Hmodels₂".
            { iApply big_sepL_take_drop. iSplitL "Hmodels₂".
              - iApply (big_sepL_impl with "Hmodels₂").
                rewrite /descriptor_final Hsuccess /=. iSteps.
              - iDestruct (big_sepL_seq_index_1 (drop i η.(metadata_descrs)) with "Hlocks") as "Hlocks".
                { rewrite length_drop //. }
                iApply (big_sepL_impl with "Hlocks").
                rewrite Hsuccess. iSteps.
            }

            iMod (lstatus_update Finished with "Hlstatus_auth") as "Hlstatus_auth"; first done.
            iDestruct (lstatus_lb_get with "Hlstatus_auth") as "#$".
            do 2 iModIntro.
            iRewrite -"Heq" in "HP".
            do 2 iFrame. iSteps.
            rewrite /metadata_final Hsuccess //.

          + iDestruct "Hau" as "[(Hau & Hwinning) | Hwinner]"; last first.
            { iDestruct (identifier_model_exclusive with "Hgid Hwinner") as %[]. }
            iDestruct (lstatus_le with "Hlstatus_auth Hlstatus_lb") as %Hi.
            iMod (lstatus_update Finished with "Hlstatus_auth") as "Hlstatus_auth"; first done.
            iDestruct (lstatus_lb_get with "Hlstatus_auth") as "#$".
            rewrite firstn_all2.
            { rewrite /metadata_size in Hj. lia. }
            iMod "Hau" as "(%vs & Hmodels₁ & _ & HP)".

            iDestruct (big_sepL2_sep_sepL_l with "[$Hmodels₂ $Hmodels₁]") as "Hmodels".
            iMod (big_sepL2_impl_bupd _ _ (λ _ descr v,
              ( model₁ descr.(descriptor_meta) descr.(descriptor_after) ∗
                model₂ descr.(descriptor_meta) (descriptor_final descr η) ∗
                if metadata_success η then
                  history_elem descr.(descriptor_meta) casn
                else
                  True
              ) ∗
              ⌜descr.(descriptor_before) = v⌝
            )%I with "Hmodels []") as "Hmodels".
            { iIntros "!> %k %descr %v %Hdescrs_lookup %Hvs_lookup ((Hmodel₂ & Hhistory_elem) & Hmodel₁)".
              iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
              iMod (model_update descr.(descriptor_after) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
              rewrite /descriptor_final Hsuccess /=.
              iSteps.
            }
            iDestruct (big_sepL2_sep_sepL_l with "Hmodels") as "(Hmodels & Hvs)".
            iDestruct (big_sepL_sep with "Hmodels") as "(Hmodels₁ & Hmodels₂)".
            iDestruct (big_sepL2_Forall with "Hvs") as %Hvs.

            iMod ("HP" with "[Hmodels₁]") as "HP"; first iSteps.
            iDestruct (big_sepL_sep with "Hmodels₂") as "(Hmodels₂ & Hhistory_elems)".
            iMod ("Hhelpers" with "Hmodels₂") as "(Hhelpers & Hmodels₂)".
            iDestruct (big_sepL_or_r with "Hmodels₂") as "Hmodels₂".
            iDestruct (big_sepL_sep_2 with "Hmodels₂ Hhistory_elems") as "Hmodels₂".
            iSteps.
            rewrite /metadata_final Hsuccess //.

        - iDestruct "Hlstatus" as "(:casn_inv_inner_finished >)".
          wp_cas as _ | Hcas; last first.
          { destruct (metadata_final η) in Hcas; naive_solver. }
          iDestruct (lstatus_lb_get with "Hlstatus_auth") as "#Hlstatus_lb".
          iSteps.
      }

      wp_pures.

      wp_bind (_.{status})%E.
      iInv "Hcasn_inv" as "(:casn_inv_inner >)".
      wp_load.
      iDestruct (lstatus_finished with "Hlstatus_auth Hlstatus_lb") as %->.
      iDestruct "Hlstatus" as "(:casn_inv_inner_finished)".
      iSplitR "HΦ". { do 2 iFrame. iSteps. }
      iModIntro. clear.

      wp_apply (kcas_status_to_bool_spec with "[//]") as "_".
      rewrite final_status_to_of_bool. iSteps.

    - iDestruct "Hlstatus" as "(:casn_inv_inner_finished)".
      iDestruct (lstatus_lb_get with "Hlstatus_auth") as "#Hlstatus_lb".
      iSplitR "HΦ". { do 2 iFrame. iSteps. }
      iModIntro. clear.

      rewrite /metadata_final.
      destruct (metadata_success η); iSteps.
  Qed.
  #[local] Lemma kcas_finish_spec_loser {gid casn η ι} fstatus :
    gid ≠ metadata_winner η →
    {{{
      meta casn nroot η ∗
      casn_inv' ι casn η ∗
      identifier_model gid
    }}}
      kcas_finish #gid #casn (final_status_to_val fstatus)
    {{{
      RET #(metadata_success η);
      lstatus_lb η Finished
    }}}.
  Proof.
    iIntros "%Hgid %Φ (#Hcasn_meta & #Hcasn_inv' & Hgid) HΦ".
    wp_apply (kcas_finish_spec with "[- HΦ] HΦ").
    iSteps.
  Qed.
  #[local] Lemma kcas_finish_spec_winner_before gid casn η ι P :
    gid = metadata_winner η →
    {{{
      meta casn nroot η ∗
      casn_inv' ι casn η ∗
      winning η ∗
      saved_prop η.(metadata_post) P ∗
      P
    }}}
      kcas_finish #gid #casn §Before
    {{{
      RET #(metadata_success η);
      lstatus_lb η Finished
    }}}.
  Proof.
    iIntros "%Hgid %Φ (#Hcasn_meta & #Hcasn_inv' & Hwinning & #Hpost & HP) HΦ".
    wp_apply (kcas_finish_spec FinalBefore with "[- HΦ] HΦ").
    iSteps.
  Qed.
  #[local] Lemma kcas_finish_spec_after {gid casn η ι} i :
    metadata_size η ≤ i →
    {{{
      meta casn nroot η ∗
      casn_inv' ι casn η ∗
      identifier_model gid ∗
      lstatus_lb η (Running i)
    }}}
      kcas_finish #gid #casn §After
    {{{
      RET #(metadata_success η);
      lstatus_lb η Finished
    }}}.
  Proof.
    iIntros "%Hi %Φ (#Hcasn_meta & #Hcasn_inv' & Hgid & #Hlstatus_lb) HΦ".
    wp_apply (kcas_finish_spec FinalAfter with "[- HΦ] HΦ").
    destruct (decide (gid = metadata_winner η)); iSteps.
  Qed.

  #[local] Lemma kcas_determine_as_get_as_determine_spec ι :
    ⊢ (
      ∀ casn η v_cass i,
      {{{
        ⌜v_cass = lst_to_val (drop i (metadata_cass casn η))⌝ ∗
        meta casn nroot η ∗
        casn_inv' ι casn η ∗
        lstatus_lb η (Running i)
      }}}
        kcas_determine_as #casn v_cass
      {{{
        RET #(metadata_success η);
        lstatus_lb η Finished
      }}}
    ) ∧ (
      ∀ state casn η descr,
      {{{
        ⌜state = state_to_val casn descr⌝ ∗
        ⌜descr ∈ η.(metadata_descrs)⌝ ∗
        meta casn nroot η ∗
        casn_inv' ι casn η
      }}}
        kcas_get_as state
      {{{
        RET descriptor_final descr η;
        lstatus_lb η Finished ∗
        £ 1
      }}}
    ) ∧ (
      ∀ casn η,
      {{{
        meta casn nroot η ∗
        casn_inv' ι casn η
      }}}
        kcas_determine #casn
      {{{
        RET #(metadata_success η);
        lstatus_lb η Finished
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(Hdetermine_as & Hget_as & Hdetermine)".
    repeat iSplit.

    { iIntros "%casn %η %v_cass %i !> %Φ (-> & #Hcasn_meta & #Hcasn_inv' & #Hlstatus_lb) HΦ".
      iDestruct (casn_inv'_unfold with "Hcasn_inv'") as "(:casn_inv)".

      wp_recs credit:"H£".
      wp_smart_apply (wp_id with "[//]") as (gid) "Hgid".

      destruct (η.(metadata_descrs) !! i) as [descr |] eqn:Hdescrs_lookup.

      - apply lookup_lt_Some in Hdescrs_lookup as Hi.
        erewrite drop_S; last first.
        { apply list_lookup_fmap_Some. naive_solver. }
        iDestruct (big_sepL_lookup with "Hlocs_inv") as "(Hloc_meta & Hloc_inv')"; first done.
        iDestruct (loc_inv'_elim with "Hloc_meta Hloc_inv'") as "Hloc_inv".
        wp_pures.

        wp_bind (!_)%E.
        iInv "Hloc_inv" as "(:loc_inv_inner > =1)".
        wp_load.
        iDestruct (casn_inv'_unfold with "Hcasn1_inv'") as "(:casn_inv =1)".
        iDestruct (history_lb_get with "Hhistory_auth") as "#Hhistory_lb1".

        iAssert ⌜descr1.(descriptor_meta) = descr.(descriptor_meta)⌝%I as %Hmeta1.
        { iDestruct (big_sepL_lookup with "Hlocs_inv") as "(Hloc_meta_1 & _)"; first done.
          iDestruct (big_sepL_lookup with "Hlocs1_inv") as "(Hloc_meta_2 & _)"; first done.
          iEval (rewrite -Hloc1) in "Hloc_meta_2".
          iApply (meta_agree with "Hloc_meta_2 Hloc_meta_1").
        }

        destruct (decide (casn1 = casn)) as [-> | Hcasn1].

        + iDestruct (meta_agree with "Hcasn_meta Hcasn1_meta") as %<-. iClear "Hcasn1_meta".
          assert (i1 = i) as ->.
          { eapply NoDup_lookup; first done.
            - rewrite list_lookup_fmap Hdescrs1_lookup //.
            - rewrite list_lookup_fmap Hdescrs_lookup -Hloc1 //.
          }
          simplify.
          iSplitR "HΦ". { iFrame. iSteps. }
          iModIntro. clear.

          wp_equal as ? | _; first naive_solver.
          wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus1_lb //] HΦ").

        + destruct (decide (gid = metadata_winner η ∧ descr.(descriptor_before) ≠ descriptor_final descr1 η1)) as [(-> & Hfail) | Hok%not_and_r_alt].

          * iInv "Hcasn_inv" as "(:casn_inv_inner)".
            destruct lstatus as [j |]; last first.
            { iDestruct "Hlstatus" as "(:casn_inv_inner_finished >)".
              iDestruct (identifier_model_exclusive with "Hgid Hwinner") as %[].
            }
            iDestruct "Hlstatus" as "(:casn_inv_inner_running >)".
            iDestruct "Hau" as "[(Hau & Hwinning) | >Hwinner]"; last first.
            { iDestruct (identifier_model_exclusive with "Hgid Hwinner") as %[]. }
            iMod (lc_fupd_elim_later with "H£ Hau") as "Hau".
            iSplitR "Hloc Hlock1 Hhistory_auth Hau Hwinning HΦ". { do 2 iFrame. iSteps. }
            iModIntro. clear j helpers.

            iMod (casn_help _ P with "Hcasn1_inv Hlock1 [Hau]") as "(%helper & Hlock1 & #Hhelper & Hhelpers1_elem)"; [solve_ndisj | done.. | |].
            { rewrite /helper_au'. iAuIntro.
              iApply (aacc_aupd_commit with "Hau"); first done. iIntros "%vs Hmodels₂".
              iDestruct (big_sepL2_lookup_acc_l with "Hmodels₂") as "(%v & %Hvs_lookup & Hmodel₁ & Hmodels₂)"; first done.
              rewrite Hmeta1. iAaccIntro with "Hmodel₁"; iSteps.
            }

            iSplitR "Hwinning Hhelpers1_elem HΦ". { do 2 iFrame. iSteps. }
            iModIntro.

            wp_equal as _ | ?; last naive_solver.

            iClear "Hlstatus1_lb".
            wp_smart_apply ("Hget_as" with "[$Hcasn1_meta $Hcasn1_inv']") as "(#Hlstatus1_lb & H£)".
            { iSteps. iPureIntro. eapply elem_of_list_lookup_2. done. }
            iMod (casn_retrieve with "Hcasn1_inv Hlstatus1_lb Hhelper Hhelpers1_elem") as "HP".

            wp_smart_apply wp_equal.
            rewrite bool_decide_eq_false_2 //.
            wp_smart_apply (kcas_finish_spec_winner_before with "[$Hcasn_meta $Hcasn_inv' $Hwinning $Hpost $HP] HΦ"); first done.

          * iSplitR "Hgid HΦ". { iFrame. iSteps. }
            iModIntro.

            wp_equal as _ | ?; last naive_solver.

            iClear "Hlstatus1_lb".
            wp_smart_apply ("Hget_as" with "[$Hcasn1_meta $Hcasn1_inv']") as "(#Hlstatus1_lb & H£)".
            { iSteps. iPureIntro. eapply elem_of_list_lookup_2. done. }

            wp_smart_apply wp_equal.
            destruct Hok as [(Hgid & Hfail) | Hok%dec_stable].

            -- rewrite bool_decide_eq_false_2 //.
               wp_smart_apply (kcas_finish_spec_loser FinalBefore with "[$Hcasn_meta $Hcasn_inv' $Hgid] HΦ"); first done.

            -- rewrite bool_decide_eq_true_2 //.
               wp_pures.

               wp_bind (_.{status})%E.
               iInv "Hcasn_inv" as "(:casn_inv_inner)".
               wp_load.
               destruct lstatus as [j |].

               ++ iDestruct "Hlstatus" as "(:casn_inv_inner_running)".

                  iInv "Hloc_inv" as "(:loc_inv_inner > =2)".
                  destruct (decide (casn1 = casn2)) as [<- | Hcasn2].

                  ** iDestruct (history_lb_get with "Hhistory_auth") as "#Hhistory_lb2".
                     iDestruct (history_running with "Hhistory_auth Hcasn_meta Hlstatus_auth") as %?.
                     iSplitL "Hloc Hlock2 Hhistory_auth". { iFrame. iSteps. }
                     iModIntro.

                     iSplitR "HΦ". { do 2 iFrame. iSteps. }
                     iModIntro. clear j helpers.

                     wp_pures.

                     wp_bind (CAS _ _ _).
                     iInv "Hloc_inv" as "(:loc_inv_inner > =3)".
                     wp_cas as _ | (_ & _ & [= -> _ _]).

                     --- iSplitR "HΦ". { iFrame. iSteps. }
                         iModIntro.

                         wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb] HΦ").
                         { iPureIntro.
                           erewrite (drop_S _ _ i); first done.
                           rewrite list_lookup_fmap Hdescrs_lookup //.
                         }

                     --- iDestruct (meta_agree with "Hcasn1_meta Hcasn3_meta") as %<-. iClear "Hcasn3_meta Hcasn3_inv' Hlstatus3_lb".
                         assert (i3 = i1) as ->.
                         { eapply NoDup_lookup.
                           - apply Hlocs1.
                           - rewrite list_lookup_fmap Hdescrs3_lookup //.
                           - rewrite list_lookup_fmap Hdescrs1_lookup /=. congruence.
                         }
                         simplify.

                         iInv "Hcasn1_inv" as "(:casn_inv_inner > =1)".
                         iDestruct (lstatus_finished with "Hlstatus1_auth Hlstatus1_lb") as %->.
                         iDestruct "Hlstatus1" as "(:casn_inv_inner_finished > =1)".
                         iDestruct (big_sepL_lookup_acc with "Hmodels1₂") as "(([Hmodel₂ | Hlock1] & Hhistory_elem) & Hmodels1₂)"; first done; last first.
                         { iDestruct (lock_exclusive with "Hlock3 Hlock1") as %[]. }

                         iDestruct ("Hmodels1₂" with "[$Hlock3 $Hhistory_elem]") as "Hmodels1₂".
                         iSplitR "Hloc Hhistory_auth Hmodel₂ HΦ". { do 2 iFrame. iSteps. }
                         iModIntro. clear helpers1 prophs1.

                         iEval (rewrite Hmeta1) in "Hmodel₂".
                         iInv "Hcasn_inv" as "(:casn_inv_inner >)".
                         destruct lstatus as [j |].

                         +++ iDestruct "Hlstatus" as "(:casn_inv_inner_running >)".

                             iAssert ⌜j = i⌝%I as %->.
                             { destruct (Nat.lt_trichotomy j i) as [? | [-> | ?]].
                               - iDestruct (lstatus_le with "Hlstatus_auth Hlstatus_lb") as %?. lia.
                               - iSteps.
                               - iDestruct (big_sepL_lookup with "Hmodels₂") as "(_Hmodel₂ & _)".
                                 { apply lookup_take_Some. done. }
                                 iDestruct (model₂_exclusive with "Hmodel₂ _Hmodel₂") as %[].
                             }

                             iMod (history_update_running casn with "Hhistory_auth Hcasn1_meta Hlstatus1_lb Hcasn_meta Hlstatus_auth") as "(Hhistory_auth & #Hhistory_elem & Hlstatus_auth)"; first done.
                             iMod (lstatus_update (Running (S i)) with "Hlstatus_auth") as "Hlstatus_auth"; first done.
                             iClear "Hlstatus_lb". iDestruct (lstatus_lb_get with "Hlstatus_auth") as "#Hlstatus_lb".
                             iEval (rewrite -Hok) in "Hmodel₂".
                             iDestruct (big_sepL_snoc_2 with "Hmodels₂ [$Hmodel₂ $Hhistory_elem]") as "Hmodels₂".
                             iEval (rewrite -take_S_r //) in "Hmodels₂".
                             rewrite -(Nat.succ_pred_pos (metadata_size η - i)).
                             { rewrite /metadata_size. lia. }
                             rewrite -cons_seq.
                             iDestruct "Hlocks" as "(Hlock & Hlocks)".
                             iEval (rewrite Nat.add_0_r) in "Hlock".
                             iDestruct (big_sepL_seq_shift_2 1 0 with "Hlocks") as "Hlocks".
                             iEval (setoid_rewrite Nat.add_1_r) in "Hlocks".
                             iEval (setoid_rewrite Nat.add_succ_r) in "Hlocks".
                             assert (Nat.pred (metadata_size η - i) = metadata_size η - S i) as -> by lia.
                             iSplitR "Hloc Hhistory_auth Hlock HΦ".
                             { do 2 iFrame. iSteps. do 2 iModIntro.
                               iApply (big_sepM_impl with "Hhelpers").
                               iSteps.
                             }
                             iModIntro. clear helpers.

                             iSplitR "HΦ". { iFrame. iSteps. }
                             iModIntro.

                             wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //] HΦ").

                         +++ iDestruct "Hlstatus" as "(:casn_inv_inner_finished >)".
                             iDestruct (history_lb_valid_eq with "Hhistory_auth Hhistory_lb2") as %(-> & _).
                             destruct (metadata_success η) eqn:Hsuccess.

                             *** iDestruct (big_sepL_lookup with "Hmodels₂") as "(_ & Hhistory_elem)"; first done.
                                 iDestruct (history_elem_valid with "Hhistory_auth Hhistory_elem") as %[| ?%elem_of_list_singleton]%elem_of_app.
                                 all: exfalso; done.

                             *** iDestruct (big_sepL_lookup_acc with "Hmodels₂") as "(([_Hmodel₂ | Hlock] & _) & Hmodels₂)"; first done.
                                 { iDestruct (model₂_exclusive with "Hmodel₂ _Hmodel₂") as %[]. }
                                 iDestruct ("Hmodels₂" with "[Hmodel₂]") as "Hmodels₂".
                                 { rewrite -Hok /descriptor_final Hsuccess. iSteps. }
                                 iClear "Hlstatus_lb". iDestruct (lstatus_lb_get_finished (Running (S i)) with "Hlstatus_auth") as "#Hlstatus_lb".
                                 iSplitR "Hloc Hhistory_auth Hlock HΦ". { do 2 iFrame. rewrite Hsuccess. iSteps. }
                                 iModIntro. clear helpers prophs.

                                 iMod (history_update with "Hhistory_auth Hcasn1_meta Hlstatus1_lb") as "(Hhistory_auth & _)"; [done.. |].
                                 iSplitR "HΦ". { iFrame. iSteps. }
                                 iModIntro.

                                 wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //]").
                                 rewrite Hsuccess. iSteps.

                  ** iDestruct (history_lb_valid_ne with "Hhistory_auth Hhistory_lb1") as "(%casns & #Hhistory_lb2)"; first done.
                     iSplitL "Hloc Hlock2 Hhistory_auth". { iFrame. iSteps. }
                     iModIntro.

                     iSplitR "HΦ". { do 2 iFrame. iSteps. }
                     iModIntro. clear j helpers.

                     wp_pures.

                     wp_bind (CAS _ _ _).
                     iInv "Hloc_inv" as "(:loc_inv_inner > =3)".
                     wp_cas as _ | (_ & _ & [= -> _ _]).

                     --- iSplitR "HΦ". { iFrame. iSteps. }
                         iModIntro.

                         wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb] HΦ").
                         { iPureIntro.
                           erewrite (drop_S _ _ i); first done.
                           rewrite list_lookup_fmap Hdescrs_lookup //.
                         }

                     --- iDestruct (history_lb_valid_eq with "Hhistory_auth Hhistory_lb2") as %(_ & (_ & [=])%app_nil).

               ++ iDestruct "Hlstatus" as "(:casn_inv_inner_finished)".
                  iClear "Hlstatus_lb". iDestruct (lstatus_lb_get with "Hlstatus_auth") as "#Hlstatus_lb".
                  iSplitR "HΦ". { do 2 iFrame. iSteps. }
                  iModIntro. clear helpers prophs.

                  rewrite /metadata_final.
                  destruct (metadata_success η); iSteps.

      - rewrite drop_lookup_None //.
        { rewrite list_lookup_fmap Hdescrs_lookup //. }
        wp_smart_apply (kcas_finish_spec_after with "[$Hcasn_meta $Hcasn_inv' $Hgid $Hlstatus_lb] HΦ").
        { rewrite lookup_ge_None // in Hdescrs_lookup. }
    }

    { iIntros "%state %casn %η %descr !> %Φ (-> & %Hdescr & #Hcasn_meta & #Hcasn_inv') HΦ".

      wp_recs credit:"H£".
      wp_smart_apply ("Hdetermine" with "[$Hcasn_meta $Hcasn_inv']") as "#Hlstatus_lb".
      rewrite /descriptor_final.
      destruct (metadata_success η); iSteps.
    }

    { iIntros "%casn %η !> %Φ (#Hcasn_meta & #Hcasn_inv') HΦ".
      iDestruct (casn_inv'_unfold with "Hcasn_inv'") as "(:casn_inv)".

      wp_recs.

      wp_bind ((#casn).{status})%E.
      iInv "Hcasn_inv" as "(:casn_inv_inner)".
      wp_load.
      destruct lstatus as [i |].

      - iDestruct "Hlstatus" as "(:casn_inv_inner_running)".
        iDestruct (lstatus_lb_get_running0 with "Hlstatus_auth") as "#Hlstatus_lb".
        iSplitR "HΦ". { do 2 iFrame. iSteps. }
        iModIntro. clear.

        wp_smart_apply ("Hdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //]").
        iSteps.

      - iDestruct "Hlstatus" as "(:casn_inv_inner_finished)".
        iDestruct (lstatus_lb_get with "Hlstatus_auth") as "#Hlstatus_lb".
        iSplitR "HΦ". { do 2 iFrame. iSteps. }
        iModIntro. clear.

        rewrite /metadata_final.
        destruct (metadata_success η); iSteps.
    }
  Qed.
  #[local] Lemma kcas_determine_as_spec casn η ι v_cass i :
    v_cass = lst_to_val (drop i (metadata_cass casn η)) →
    {{{
      meta casn nroot η ∗
      casn_inv' ι casn η ∗
      lstatus_lb η (Running i)
    }}}
      kcas_determine_as #casn v_cass
    {{{
      RET #(metadata_success η);
      lstatus_lb η Finished
    }}}.
  Proof.
    iDestruct kcas_determine_as_get_as_determine_spec as "(H & _)".
    iIntros (->) "%Φ (#Hcasn_meta & #Hcasn_inv' & #Hlstatus_lb) HΦ".
    wp_apply ("H" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //] HΦ").
  Qed.
  #[local] Lemma kcas_get_as_spec state casn η ι descr :
    state = state_to_val casn descr →
    descr ∈ η.(metadata_descrs) →
    {{{
      meta casn nroot η ∗
      casn_inv' ι casn η
    }}}
      kcas_get_as state
    {{{
      RET descriptor_final descr η;
      lstatus_lb η Finished ∗
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
      casn_inv' ι casn η
    }}}
      kcas_determine #casn
    {{{
      RET #(metadata_success η);
      lstatus_lb η Finished
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
    wp_smart_apply (typed_prophet_wp_proph prophet with "[//]") as (pid prophs) "Hproph".
    wp_block casn as "Hcasn_meta" "(Hcasn_state & Hcasn_proph & _)".
    iMod (pointsto_persist with "Hcasn_proph") as "#Hcasn_proph".
    wp_reveal bid.
    wp_ref loc as "Hloc_meta" "Hloc".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod history_alloc as "(%γ_history & Hhistory_auth & #Hhistory_elem)".

    pose γ := {|
      loc_metadata_model := γ_model ;
      loc_metadata_history := γ_history ;
    |}.
    iMod (meta_set _ _ γ with "Hloc_meta") as "#Hloc_meta"; first done.

    iMod (saved_prop_alloc True) as "(%η_post & #Hpost)".
    iMod (lstatus_alloc Finished) as "(%η_lstatus & Hlstatus_auth)".
    iMod lock_alloc as "(%η_lock & Hlock)".
    iMod helpers_alloc as "(%η_helpers & Hhelpers_auth)".
    iMod winning_alloc as "(%η_winning & Hwinning)".
    iMod owner_alloc as "(%η_owner & Howner)".

    pose descr := {|
      descriptor_loc := loc ;
      descriptor_meta := γ ;
      descriptor_before := v ;
      descriptor_after := v ;
      descriptor_state := bid ;
    |}.
    pose η := {|
      metadata_descrs := [descr] ;
      metadata_prophet := pid ;
      metadata_prophs := ((gid, true) :: prophs) ;
      metadata_undetermined := bid ;
      metadata_post := η_post ;
      metadata_lstatus := η_lstatus ;
      metadata_locks := [η_lock] ;
      metadata_helpers := η_helpers ;
      metadata_winning := η_winning ;
      metadata_owner := η_owner ;
    |}.
    iMod (meta_set _ _ η with "Hcasn_meta") as "#Hcasn_meta"; first done.

    iDestruct (lstatus_lb_get_finished (η := η) (Running 1) with "Hlstatus_auth") as "#Hlstatus_lb".

    iMod (inv_alloc _ _ (casn_inv_inner casn η ι True) with "[Hgid Hproph Hcasn_state Hmodel₂ Hlstatus_auth Hhelpers_auth Hwinning Howner]") as "#Hcasn_inv".
    { iExists §After%V, Finished, ∅.
      setoid_rewrite big_sepM_empty. iSteps.
    }

    iAssert (|={⊤}=> loc_inv' ι (loc, γ))%I with "[Hloc Hlock Hhistory_auth]" as ">#Hloc_inv'".
    { iApply loc_inv'_intro.
      iApply inv_alloc.
      iExists [], casn, η, 0, descr.
      setoid_rewrite <- (fixpoint_A_unfold (casn_inv_pre ι) (loc_inv_pre ι) _).
      iSteps; iPureIntro; apply NoDup_singleton.
    }

    iDestruct (casn_inv'_unfold with "[$Hcasn_inv]") as "#Hcasn_inv'".
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
    iDestruct (loc_inv'_elim with "Hloc_meta Hloc_inv'") as "#Hloc_inv".

    wp_rec credit:"H£1".

    wp_bind (!_)%E.
    iInv "Hloc_inv" as "(:loc_inv_inner >)".
    wp_load.
    iDestruct (casn_inv'_unfold with "Hcasn_inv'") as "(:casn_inv)".
    iDestruct (big_sepL_lookup with "Hlocs_inv") as "(_Hloc_meta & _)"; first done.
    iDestruct (meta_agree with "Hloc_meta _Hloc_meta") as %->. iClear "_Hloc_meta".
    iMod (casn_help _ (Φ (descriptor_final descr η)) with "Hcasn_inv Hlock [HΦ]") as "(%helper & Hlock & #Hhelper & Hhelpers_elem)"; [solve_ndisj | done.. | |].
    { rewrite /helper_au'. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%v (%γ & _Hloc_meta & Hmodel₁)".
      iDestruct (meta_agree with "Hloc_meta _Hloc_meta") as %<-. iClear "_Hloc_meta".
      iAaccIntro with "Hmodel₁"; iSteps.
    }
    iSplitR "H£1 Hhelpers_elem". { iFrame. iSteps. }
    iModIntro. clear Hlocs.

    iApply wp_fupd. iClear "Hlstatus_lb".
    wp_apply (kcas_get_as_spec with "[$Hcasn_meta $Hcasn_inv']") as "(#Hlstatus_lb & H£2)"; first done.
    { eapply elem_of_list_lookup_2. done. }
    iMod (casn_retrieve with "Hcasn_inv Hlstatus_lb Hhelper Hhelpers_elem") as "HΦ".
    iMod (lc_fupd_elim_later with "H£1 HΦ") as "HΦ".
    iApply (lc_fupd_elim_later with "H£2 HΦ").
  Qed.

  Lemma kcas_cas_spec {ι v_cass} cass :
    NoDup cass.*1 →
    lst_model' v_cass ((λ cas, (#cas.1, cas.2.1, cas.2.2)%V) <$> cass) →
    <<<
      [∗ list] cas ∈ cass, kcas_loc_inv cas.1 ι
    | ∀∀ vs,
      [∗ list] cas; v ∈ cass; vs, kcas_loc_model cas.1 v
    >>>
      kcas_cas v_cass @ ↑ι
    <<<
      ∃∃ b,
      if b then
        ⌜Forall2 (λ cas v, cas.2.1 = v) cass vs⌝ ∗
        [∗ list] cas ∈ cass, kcas_loc_model cas.1 cas.2.2
      else
        ∃ i cas v,
        ⌜cass !! i = Some cas⌝ ∗
        ⌜vs !! i = Some v⌝ ∗
        ⌜cas.2.1 ≠ v⌝ ∗
        [∗ list] cas; v ∈ cass; vs, kcas_loc_model cas.1 v
    | RET #b;
      True
    >>>.
  Proof.
    iIntros (Hnodup ->) "!> %Φ _Hlocs_inv HΦ".
    iDestruct (big_sepL_exists with "_Hlocs_inv") as "(%γs & %Hγs & #Hlocs_inv)". iClear "_Hlocs_inv".

    wp_rec credit:"H£".
    wp_smart_apply (typed_prophet_wp_proph prophet with "[//]") as (pid prophs0) "Hproph".
    wp_block casn as "Hcasn_meta" "(Hcasn_state & Hcasn_proph & _)".
    iMod (pointsto_persist with "Hcasn_proph") as "#Hcasn_proph".

    pose (Ψ i (_ : list val) vs_cass := (
      ∃ descrs,
      ⌜ vs_cass =
        (λ descr,
          (#descr.(descriptor_loc), state_to_val casn descr)%V
        ) <$> descrs
      ⌝ ∗
      ⌜Forall3 (λ cas γ descr,
        descr.(descriptor_loc) = cas.1 ∧
        descr.(descriptor_before) = cas.2.1 ∧
        descr.(descriptor_after) = cas.2.2 ∧
        descr.(descriptor_meta) = γ
      ) (take i cass) (take i γs) descrs⌝
    )%I : iProp Σ).
    wp_smart_apply (lst_map_spec Ψ with "[]") as (v_cass vs_cass) "(%Hlength & -> & (%descrs & -> & %Hdescrs))".
    { iSplit. { iExists []. iSteps. iPureIntro. apply Forall3_nil. }
      iSplit; first iSteps.
      iIntros "!> %i %v_cass %vs_cass".
      admit.
    }
    rewrite !length_fmap in Hdescrs Hlength.
    rewrite -{2}Hγs !firstn_all in Hdescrs.

    (* pose (Ψ i (_ : val) v_cass := ( *)
    (*   ∃ cas γ descr, *)
    (*   ⌜cass !! i = Some cas⌝ ∗ *)
    (*   ⌜γs !! i = Some γ⌝ ∗ *)
    (*   ⌜v_cass = (#descr.(descriptor_loc), state_to_val casn descr)%V⌝ ∗ *)
    (*   ⌜descr.(descriptor_loc) = cas.1⌝ ∗ *)
    (*   ⌜descr.(descriptor_before) = cas.2.1⌝ ∗ *)
    (*   ⌜descr.(descriptor_after) = cas.2.2⌝ ∗ *)
    (*   ⌜descr.(descriptor_meta) = γ⌝ *)
    (* )%I : iProp Σ). *)
    (* wp_smart_apply (lst_map_spec_disentangled Ψ with "[]") as (v_cass vs_cass) "(% & -> & Hdescrs)". *)
    (* { iSplit; first iSteps. *)
    (*   iIntros "!> %i %v_cass %Hlookup". *)
    (*   admit. *)
    (* } *)

    wp_reveal bid.
    wp_store.

    set P := Φ #(hd inhabitant prophs0).2.

    iMod (saved_prop_alloc P) as "(%η_post & #Hpost)".
    iMod (lstatus_alloc (Running 0)) as "(%η_lstatus & Hlstatus_auth)".
    iMod (lock_allocs (length cass)) as "(%η_locks & %Hη_locks & Hlocks)".
    iMod helpers_alloc as "(%η_helpers & Hhelpers_auth)".
    iMod winning_alloc as "(%η_winning & Hwinning)".
    iMod owner_alloc as "(%η_owner & Howner)".

    pose η := {|
      metadata_descrs := descrs ;
      metadata_prophet := pid ;
      metadata_prophs := prophs0 ;
      metadata_undetermined := bid ;
      metadata_post := η_post ;
      metadata_lstatus := η_lstatus ;
      metadata_locks := η_locks ;
      metadata_helpers := η_helpers ;
      metadata_winning := η_winning ;
      metadata_owner := η_owner ;
    |}.
    iMod (meta_set _ _ η with "Hcasn_meta") as "#Hcasn_meta"; first done.

    iDestruct (lstatus_lb_get η with "Hlstatus_auth") as "#Hlstatus_lb".

    iMod (inv_alloc _ _ (casn_inv_inner casn η ι P) with "[Hproph Hcasn_state Hlstatus_auth Hlocks Hhelpers_auth Hwinning HΦ]") as "#Hcasn_inv".
    { iExists _, (Running 0), ∅, _. iSteps.
      iSplitL "Hlocks".
      { iApply (big_sepL_seq_index η_locks); first lia.
        iApply (big_sepL_impl with "Hlocks").
        iSteps.
      }
      iSplitR. { rewrite big_sepM_empty. iSteps. }
      iLeft. iFrame.
      rewrite /au. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodels".
      admit.
    }

    iDestruct (casn_inv'_unfold with "[$Hcasn_inv]") as "#Hcasn_inv'".
    { iSteps.
      - iPureIntro.
        apply NoDup_alt. intros i1 i2 loc (descr1 & Hdescrs_lookup_1 & ->)%list_lookup_fmap_Some (descr2 & Hdescrs_lookup_2 & Heq)%list_lookup_fmap_Some.
        odestruct (Forall3_lookup_r _ _ _ _ i1) as (cas1 & γ1 & Hcass_lookup_1 & Hγs_lookup_1 & H1); [done.. |].
        destruct H1 as (-> & _) in Heq.
        odestruct (Forall3_lookup_r _ _ _ _ i2) as (cas2 & γ2 & Hcass_lookup_2 & Hγs_lookup_2 & H2); [done.. |].
        destruct H2 as (-> & _) in Heq.
        eapply NoDup_lookup; first done.
        all: rewrite list_lookup_fmap_Some; naive_solver.
      - admit.
    }

    iApply wp_fupd.
    wp_smart_apply (kcas_determine_as_spec with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb]") as "#Hlstatus_lb_finished"; first done.

    iInv "Hcasn_inv" as "(:casn_inv_inner >)".
    iDestruct (lstatus_finished with "Hlstatus_auth Hlstatus_lb_finished") as %->.
    iDestruct "Hlstatus" as "(:casn_inv_inner_finished >)".
    iDestruct "HP" as "[>_Howner | HP]".
    { iDestruct (owner_exclusive η with "Howner _Howner") as %[]. }
    iSplitR "H£ HP". { do 2 iFrame. iSteps. }
    iModIntro. clear.

    iApply (lc_fupd_elim_later with "H£ HP").
  Admitted.
End kcas_G.

#[global] Opaque kcas_make.
#[global] Opaque kcas_get.
#[global] Opaque kcas_cas.

#[global] Opaque kcas_loc_inv.
#[global] Opaque kcas_loc_model.
