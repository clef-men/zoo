(* Based on:
   https://github.com/ocaml-multicore/kcas/blob/44c732c83585f662abda0ef0984fdd2fe8990f4a/doc/gkmz-with-read-only-cmp-ops.md
*)

From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.auth_mono
  lib.excl
  lib.saved_prop.
From zoo.language Require Import
  identifier
  typed_prophet
  notations
  diaframe.
From zoo.std Require Import
  lst.
From zoo Require Import
  options.

Implicit Types i : nat.
Implicit Types l loc casn : location.
Implicit Types id : identifier.
Implicit Types status : val.

#[local] Notation "'casn'" := (
  in_type "state" 0
)(in custom zoo_proj
).
#[local] Notation "'before'" := (
  in_type "state" 1
)(in custom zoo_proj
).
#[local] Notation "'after'" := (
  in_type "state" 2
)(in custom zoo_proj
).

#[local] Notation "'loc'" := (
  in_type "cas" 0
)(in custom zoo_proj
).
#[local] Notation "'state'" := (
  in_type "cas" 1
)(in custom zoo_proj
).

#[local] Notation "'Undetermined'" := (
  in_type "status" 0
)(in custom zoo_tag
).
#[local] Notation "'Before'" := (
  in_type "status" 1
)(in custom zoo_tag
).
#[local] Notation "'After'" := (
  in_type "status" 2
)(in custom zoo_tag
).

#[local] Notation "'status'" := (
  in_type "casn" 0
)(in custom zoo_field
).
#[local] Notation "'prophet'" := (
  in_type "casn" 1
)(in custom zoo_field
).

#[local] Definition kcas_status_to_bool : val :=
  fun: "status" =>
    match: "status" with
    | Before =>
        #false
    | After =>
        #true
    end.
#[local] Definition kcas_finish : val :=
  fun: "id" "casn" "status" =>
    match: "casn".{status} with
    | Before =>
        #false
    | After =>
        #true
    | Undetermined <> as "old_status" =>
        Resolve (CAS "casn".[status] "old_status" "status") "casn".{prophet} ("id", kcas_status_to_bool "status") ;;
        "casn".{status} = §After
    end.

#[local] Definition kcas_determine_aux : val :=
  rec: "kcas_determine_aux" "kcas_determine" "casn" "cass" =>
    let: "id" := Id in
    match: "cass" with
    | Nil =>
        kcas_finish "id" "cas" §After
    | Cons "cas" "cass'" =>
        let: "loc", "state" := "cas" in
        let: "state'" := !"loc" in
        if: "state" = "state'" then (
          "kcas_determine_aux" "kcas_determine" "casn" "cass'"
        ) else (
          let: "v" :=
            if: "kcas_determine" "state'".<casn> then
              "state'".<after>
            else
              "state'".<before>
          in
          if: "v" ≠ "state".<before> then
            kcas_finish "id" "casn" §Before
          else
            match: "casn".{status} with
            | Before =>
                #false
            | After =>
                #true
            | Undetermined <> =>
                if: CAS "loc" "state'" "state" then
                  "kcas_determine_aux" "casn" "cass'"
                else
                  "kcas_determine_aux" "casn" "cass"
            end
        )
    end.
#[local] Definition kcas_determine : val :=
  rec: "kcas_determine" "casn" =>
    match: "casn".{status} with
    | Before =>
        #false
    | After =>
        #true
    | Undetermined "cass" =>
        kcas_determine_aux "kcas_determine" "casn" "cass"
    end.

Definition kcas_get : val :=
  fun: "loc" =>
    let: "state" := !"loc" in
    if: kcas_determine "state".<casn> then
      "state".<after>
    else
      "state".<before>.

Definition kcas_cas : val :=
  fun: "cass" =>
    let: "casn" := { §After, Proph } in
    let: "cass" :=
      lst_map "cass" (fun: "cas" =>
        ("cas".<0>, ("casn", "cas".<1>, "cas".<2>))
      )
    in
    "cass" <-{status} ‘Undetermined{ "cass" } ;;
    kcas_determine_aux kcas_determine "casn" "cass".

Inductive kcas_lstatus :=
  | KcasUndetermined i
  | KcasFinished.
Implicit Types lstatus : kcas_lstatus.

Inductive kcas_lstep : kcas_lstatus → kcas_lstatus → Prop :=
  | kcas_lstep_incr i :
      kcas_lstep (KcasUndetermined i) (KcasUndetermined (S i))
  | kcas_lstep_finish i :
      kcas_lstep (KcasUndetermined i) KcasFinished.
#[local] Hint Constructors kcas_lstep : core.

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

  #[local] Program Definition kcas_prophet := {|
    typed_prophet_type :=
      identifier * bool ;
    typed_prophet_of_val v :=
      match v with
      | ValTuple [ValProphecy id; ValBool b] =>
          Some (id, b)
      | _ =>
          None
      end ;
    typed_prophet_to_val '(id, b) :=
      (#id, #b)%V ;
  |}.
  Solve Obligations of kcas_prophet with
    try done.
  Next Obligation.
    intros (id & b) v ->. done.
  Qed.

  Definition kcas_loc_meta : Type :=
    gname.
  Implicit Types γ : kcas_loc_meta.

  #[local] Definition kcas_model₁ γ v :=
    twins_twin1 γ (DfracOwn 1) v.
  #[local] Definition kcas_model₂ γ v :=
    twins_twin2 γ v.

  Record kcas_descr := {
    kcas_descr_loc : location ;
    kcas_descr_meta : kcas_loc_meta ;
    kcas_descr_before : val ;
    kcas_descr_after : val ;
  }.

  #[local] Instance kcas_descr_eq_dec : EqDecision kcas_descr :=
    ltac:(solve_decision).
  #[local] Instance kcas_descr_countable :
    Countable kcas_descr.
  Proof.
    pose encode descr := (
      descr.(kcas_descr_loc),
      descr.(kcas_descr_meta),
      descr.(kcas_descr_before),
      descr.(kcas_descr_after)
    ).
    pose decode := λ '(loc, γ, before, after), {|
      kcas_descr_loc := loc ;
      kcas_descr_meta := γ ;
      kcas_descr_before := before ;
      kcas_descr_after := after ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  Record kcas_casn_meta := {
    kcas_casn_meta_descrs : list kcas_descr ;
    kcas_casn_meta_prophet : prophet_id ;
    kcas_casn_meta_prophs : list kcas_prophet.(typed_prophet_type) ;
    kcas_casn_meta_undetermined : location ;
    kcas_casn_meta_post : gname ;
    kcas_casn_meta_lstatus : gname ;
    kcas_casn_meta_witnesses : list gname ;
    kcas_casn_meta_waiters : gname ;
    kcas_casn_meta_winning : gname ;
    kcas_casn_meta_owner : gname ;
  }.
  Implicit Types η : kcas_casn_meta.

  #[local] Definition kcas_casn_meta_size η :=
    length η.(kcas_casn_meta_descrs).
  #[local] Definition kcas_casn_meta_cass casn η :=
    (λ descr,
      ( #descr.(kcas_descr_loc),
        (#casn, descr.(kcas_descr_before), descr.(kcas_descr_after))
      )%V
    ) <$> η.(kcas_casn_meta_descrs).
  #[local] Definition kcas_casn_meta_outcome η :=
    hd inhabitant η.(kcas_casn_meta_prophs).
  #[local] Definition kcas_casn_meta_winner η :=
    (kcas_casn_meta_outcome η).1.
  #[local] Definition kcas_casn_meta_success η :=
    (kcas_casn_meta_outcome η).2.
  #[local] Definition kcas_casn_meta_final η :=
    if kcas_casn_meta_success η then §After%V else §Before%V.

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

  #[local] Definition kcas_lstatus_auth η lstatus :=
    auth_mono_auth _ η.(kcas_casn_meta_lstatus) (DfracOwn 1) lstatus.
  #[local] Definition kcas_lstatus_lb η lstatus :=
    auth_mono_lb _ η.(kcas_casn_meta_lstatus) lstatus.

  #[local] Definition kcas_witness η i : iProp Σ :=
    ∃ γ_witness,
    ⌜η.(kcas_casn_meta_witnesses) !! i = Some γ_witness⌝ ∗
    excl γ_witness ().

  #[local] Definition kcas_waiters η waiters :=
    ghost_map_auth η.(kcas_casn_meta_waiters) 1 waiters.
  #[local] Definition kcas_waiter η waiter i :=
    ghost_map_elem η.(kcas_casn_meta_waiters) waiter (DfracOwn 1) i.

  #[local] Definition kcas_winning η :=
    excl η.(kcas_casn_meta_winning) ().

  #[local] Definition kcas_owner η :=
    excl η.(kcas_casn_meta_owner) ().

  Inductive kcas_which :=
    | KcasLoc
    | KcasCasn.

  Record kcas_param := KcasParam {
    kcas_param_which : kcas_which ;
    kcas_param_location : location ;
    kcas_param_meta : if kcas_param_which then kcas_loc_meta else kcas_casn_meta ;
  }.

  #[local] Definition kcas_loc_inv_inner' (kcas_inv : kcas_param → iProp Σ) loc γ : iProp Σ :=
    ∃ casn η i descr,
    meta casn nroot η ∗
    ⌜η.(kcas_casn_meta_descrs) !! i = Some descr⌝ ∗
    ⌜descr.(kcas_descr_loc) = loc⌝ ∗
    loc ↦ (descr.(kcas_descr_before), descr.(kcas_descr_after), #casn) ∗
    kcas_lstatus_lb η (KcasUndetermined i) ∗
    kcas_witness η i ∗
    kcas_inv (KcasParam KcasCasn casn η).

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

  #[local] Definition kcas_waiter_au η ι i Q : iProp Σ :=
    ∃ descr,
    ⌜η.(kcas_casn_meta_descrs) !! i = Some descr⌝ ∗
    AU <{
      ∃∃ v,
      kcas_model₁ descr.(kcas_descr_meta) v
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ⌜v = if kcas_casn_meta_success η then descr.(kcas_descr_after) else descr.(kcas_descr_before)⌝ ∗
      kcas_model₁ descr.(kcas_descr_meta) v
    , COMM
      Q
    }>.

  #[local] Definition kcas_casn_inv_inner' (kcas_inv : kcas_param → iProp Σ) casn η ι P : iProp Σ :=
    ∃ status lstatus waiters,
    casn.[status] ↦ status ∗
    kcas_lstatus_auth η lstatus ∗
    kcas_waiters η waiters ∗
    match lstatus with
    | KcasUndetermined i =>
        ⌜i < kcas_casn_meta_size η⌝ ∗
        ⌜status = #η.(kcas_casn_meta_undetermined)⌝ ∗
        ( [∗ list] descr ∈ take i η.(kcas_casn_meta_descrs),
          meta descr.(kcas_descr_loc) nroot descr.(kcas_descr_meta) ∗
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
          meta descr.(kcas_descr_loc) nroot descr.(kcas_descr_meta) ∗
          ( kcas_model₂ descr.(kcas_descr_meta) (if kcas_casn_meta_success η then descr.(kcas_descr_after) else descr.(kcas_descr_before))
          ∨ kcas_witness η i
          )
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

  #[local] Definition kcas_inv_pre ι
  : (kcas_param -d> iProp Σ) →
    kcas_param -d> iProp Σ
  :=
    λ kcas_inv param,
      match param.(kcas_param_which) as which
      return (if which then kcas_loc_meta else kcas_casn_meta) → _
      with
      | KcasLoc => λ γ,
          let loc := param.(kcas_param_location) in
          inv (ι.@"loc") (kcas_loc_inv_inner' kcas_inv loc γ)
      | KcasCasn => λ η,
          let casn := param.(kcas_param_location) in
          ∃ P,
          casn.[prophet] ↦□ #η.(kcas_casn_meta_prophet) ∗
          η.(kcas_casn_meta_undetermined) ↦ₕ Header §Undetermined 1 ∗
          η.(kcas_casn_meta_undetermined).[0] ↦ (lst_to_val $ kcas_casn_meta_cass casn η) ∗
          saved_prop η.(kcas_casn_meta_post) P ∗
          inv (ι.@"casn".@casn) (kcas_casn_inv_inner' kcas_inv casn η ι P)
      end%I
      param.(kcas_param_meta).
  #[local] Instance kcas_inv_pre_contractive ι :
    Contractive (kcas_inv_pre ι).
  Proof.
    rewrite /kcas_inv_pre /kcas_loc_inv_inner' /kcas_casn_inv_inner' => n Ψ1 Ψ2 HΨ param.
    destruct param as ([], ?, ?); solve_contractive.
  Qed.
  #[local] Definition kcas_inv ι : kcas_param → iProp Σ :=
    fixpoint (kcas_inv_pre ι).

  #[local] Definition kcas_loc_inv_inner loc γ ι :=
    kcas_loc_inv_inner' (kcas_inv ι) loc γ.
  #[local] Definition kcas_loc_inv' loc γ ι :=
    kcas_inv ι (KcasParam KcasLoc loc γ).
  Definition kcas_loc_inv loc ι : iProp Σ :=
    ∃ γ,
    meta loc nroot γ ∗
    kcas_loc_inv' loc γ ι.

  #[local] Definition kcas_casn_inv_inner casn η ι P :=
    kcas_casn_inv_inner' (kcas_inv ι) casn η ι P.
  #[local] Definition kcas_casn_inv' casn η ι :=
    kcas_inv ι (KcasParam KcasCasn casn η).
  #[local] Definition kcas_casn_inv casn ι : iProp Σ :=
    ∃ η,
    meta casn nroot η ∗
    kcas_casn_inv' casn η ι.

  Definition kcas_loc_model loc v : iProp Σ :=
    ∃ γ,
    meta loc nroot γ ∗
    kcas_model₁ γ v.

  #[local] Lemma kcas_finish_spec_loser id casn η ι status :
    status = §Before%V ∨ status = §After%V →
    id ≠ kcas_casn_meta_winner η →
    {{{
      kcas_casn_inv' casn η ι
    }}}
      kcas_finish #id #casn status
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
  Admitted.
  #[local] Lemma kcas_finish_spec_winner_after id casn η ι :
    id = kcas_casn_meta_winner η →
    {{{
      kcas_casn_inv' casn η ι ∗
      identifier_model id ∗
      kcas_lstatus_lb η (KcasUndetermined (kcas_casn_meta_size η - 1))
    }}}
      kcas_finish #id #casn §After
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
  Admitted.
  #[local] Lemma kcas_finish_spec_winner_before id casn η ι :
    id = kcas_casn_meta_winner η →
    {{{
      kcas_casn_inv' casn η ι ∗
      kcas_winning η
    }}}
      kcas_finish #id #casn §Before
    {{{
      RET #false;
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
  Admitted.

  #[local] Definition kcas_determine_specification : iProp Σ :=
    ∀ casn η ι,
    {{{
      kcas_casn_inv' casn η ι
    }}}
      kcas_determine #casn
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.

  #[local] Lemma kcas_determine_aux_spec {casn η ι cass} i :
    cass = lst_to_val (drop i (kcas_casn_meta_cass casn η)) →
    {{{
      kcas_casn_inv' casn η ι ∗
      kcas_lstatus_lb η (KcasUndetermined i) ∗
      kcas_determine_specification
    }}}
      kcas_determine_aux kcas_determine #casn cass
    {{{
      RET #(kcas_casn_meta_success η);
      kcas_lstatus_lb η KcasFinished
    }}}.
  Proof.
  Admitted.

  #[local] Lemma kcas_determine_spec :
    ⊢ kcas_determine_specification.
  Proof.
  Admitted.
End kcas_G.

#[global] Opaque kcas_get.

#[global] Opaque kcas_loc_inv.
#[global] Opaque kcas_loc_model.
