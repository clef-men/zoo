Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.list.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.saved_prop.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_bool.
Require Import zoo.program_logic.identifier.
Require Export zoo_mcas.mcas_1__code.
Require Import zoo_mcas.mcas_1__types.
Require Import zoo.options.

Implicit Type b full : bool.
Implicit Type i : nat.
Implicit Type l loc casn : location.
Implicit Type casns : list location.
Implicit Type gid : identifier.
Implicit Type v w state : val.
Implicit Type vs befores afters : list val.
Implicit Type cas : location * (val * val).
Implicit Type cass : list (location * (val * val)).
Implicit Type helpers : gmap gname nat.

#[local] Definition global_prophet :=
  {|prophet_typed۰type :=
      identifier * bool
  ; prophet_typed۰of_val _ v :=
      match v with
      | ValTuple [ValProph gid; ValBool b] =>
          Some $ Some (gid, b)
      | _ =>
          None
      end
  |}.
Implicit Type prophs : list global_prophet.(prophet_typed۰type).

Record loc۰metadata :=
  { loc۰metadata۰model : gname
  ; loc۰metadata۰history : gname
  }.
Implicit Type γ : loc۰metadata.

#[local] Instance loc۰metadataｰinhabited : Inhabited loc۰metadata :=
  populate
    {|loc۰metadata۰model := inhabitant
    ; loc۰metadata۰history := inhabitant
    |}.
#[local] Instance loc۰metadataｰeq_dec : EqDecision loc۰metadata :=
  ltac:(solve_decision).
#[local] Instance loc۰metadataｰcountable :
  Countable loc۰metadata.
Proof.
  solve_countable.
Qed.

Record descriptor :=
  { descriptor۰loc : location
  ; descriptor۰meta : loc۰metadata
  ; descriptor۰before : val
  ; descriptor۰after : val
  ; descriptor۰state : location
  }.
Implicit Type descr : descriptor.
Implicit Type descrs : list descriptor.

#[local] Definition descriptor۰cas descr : val :=
  (#descr.(descriptor۰loc), #descr.(descriptor۰state)).

#[local] Instance descriptorｰinhabited : Inhabited descriptor :=
  populate
    {|descriptor۰loc := inhabitant
    ; descriptor۰meta := inhabitant
    ; descriptor۰before := inhabitant
    ; descriptor۰after := inhabitant
    ; descriptor۰state := inhabitant
    |}.
#[local] Instance descriptorｰeq_dec : EqDecision descriptor :=
  ltac:(solve_decision).
#[local] Instance descriptorｰcountable :
  Countable descriptor.
Proof.
  solve_countable.
Qed.

Variant status :=
  | Undetermined
  | After
  | Before.
Implicit Type status : status.

Variant final_status :=
  | FinalAfter
  | FinalBefore.
Implicit Type fstatus : final_status.

Definition final_status۰to_bool fstatus :=
  if fstatus then true else false.
#[global] Arguments final_status۰to_bool !_ : assert.
Definition final_status۰of_bool b :=
  if b then FinalAfter else FinalBefore.
#[global] Arguments final_status۰of_bool !_ : assert.
Definition final_status۰to_val fstatus :=
  match fstatus with
  | FinalAfter =>
      §After
  | FinalBefore =>
      §Before
  end%V.
#[global] Arguments final_status۰to_val !_ : assert.

#[local] Lemma final_statusｰto_boolｰof_bool b :
  final_status۰to_bool (final_status۰of_bool b) = b.
Proof.
  destruct b; done.
Qed.
#[local] Lemma final_status۰to_valｰundetermined fstatus bid 𝑐𝑎𝑠𝑠 :
  ¬ final_status۰to_val fstatus ≈ ‘Undetermined@bid[ 𝑐𝑎𝑠𝑠 ]%V.
Proof.
  destruct fstatus; done.
Qed.

Record metadata :=
  { metadata۰descrs : list descriptor
  ; metadata۰prophet : prophet_id
  ; metadata۰prophs : list global_prophet.(prophet_typed۰type)
  ; metadata۰undetermined : block_id
  ; metadata۰post : gname
  ; metadata۰lstatus : gname
  ; metadata۰locks : list gname
  ; metadata۰helpers : gname
  ; metadata۰winning : gname
  ; metadata۰owner : gname
  }.
Implicit Type η : metadata.

#[local] Instance metadataｰinhabited : Inhabited metadata :=
  populate
    {|metadata۰descrs := inhabitant
    ; metadata۰prophet := inhabitant
    ; metadata۰prophs := inhabitant
    ; metadata۰undetermined := inhabitant
    ; metadata۰post := inhabitant
    ; metadata۰lstatus := inhabitant
    ; metadata۰locks := inhabitant
    ; metadata۰helpers := inhabitant
    ; metadata۰winning := inhabitant
    ; metadata۰owner := inhabitant
    |}.
#[local] Instance metadataｰeq_dec : EqDecision metadata :=
  ltac:(solve_decision).
#[local] Instance metadataｰcountable :
  Countable metadata.
Proof.
  solve_countable.
Qed.

#[local] Definition metadata۰size η :=
  length η.(metadata۰descrs).
#[local] Definition metadata۰cass η :=
  descriptor۰cas <$> η.(metadata۰descrs).
#[local] Definition metadata۰cass۰val η :=
  list۰to_val $ metadata۰cass η.
#[local] Definition metadata۰outcome η :=
  hd inhabitant η.(metadata۰prophs).
#[local] Definition metadata۰winner η :=
  (metadata۰outcome η).1.
#[local] Definition metadata۰success η :=
  (metadata۰outcome η).2.
#[local] Definition metadata۰final η :=
  final_status۰to_val $ final_status۰of_bool $ metadata۰success η.

#[local] Instance statusｰinhabited : Inhabited status :=
  populate Undetermined.

#[local] Definition status۰to_val η status : val :=
  match status with
  | Undetermined =>
      ‘Undetermined@η.(metadata۰undetermined)[ metadata۰cass۰val η ]
  | After =>
      §After
  | Before =>
      §Before
  end.

Variant lstatus :=
  | Running i
  | Finished.
Implicit Type lstatus : lstatus.

#[local] Instance lstatusｰinhabited : Inhabited lstatus :=
  populate Finished.

Variant lstep : lstatus → lstatus → Prop :=
  | lstepｰincr i :
      lstep (Running i) (Running ˖i)
  | lstepｰfinish i :
      lstep (Running i) Finished.
#[local] Hint Constructors lstep : core.

#[local] Lemma lstepsｰrunning0 lstatus :
  rtc lstep (Running 0) lstatus.
Proof.
  destruct lstatus as [i |].
  - induction i; first done.
    eapply rtc_r; [done | constructor].
  - apply rtc_once. done.
Qed.
#[local] Lemma lstepｰfinished lstatus :
  ¬ lstep Finished lstatus.
Proof.
  inversion 1.
Qed.
#[local] Lemma lstepsｰfinished lstatus :
  rtc lstep Finished lstatus →
  lstatus = Finished.
Proof.
  inversion 1 as [| ? ? ? []] => //.
Qed.
#[local] Lemma lstepsｰle lstatus1 i1 lstatus2 i2 :
  rtc lstep lstatus1 lstatus2 →
  lstatus1 = Running i1 →
  lstatus2 = Running i2 →
  i1 ≤ i2.
Proof.
  intros Hlsteps. move: i1. induction Hlsteps as [lstatus | lstatus1 ? lstatus2 Hlstep Hlsteps IH] => i1.
  - naive_solver.
  - intros -> ->. invert Hlstep.
    + specialize (IH ˖i1). lia.
    + apply lstepsｰfinished in Hlsteps as [=].
Qed.

#[local] Definition descriptor۰final descr η :=
  if metadata۰success η then
    descr.(descriptor۰after)
  else
    descr.(descriptor۰before).

Class Mcas1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mcas_1۰G۰model۰G :: TwinsG Σ val_O
  ; #[local] mcas_1۰G۰helper۰G :: SavedPropG Σ
  ; #[local] mcas_1۰G۰post۰G :: SavedPredG Σ bool
  ; #[local] mcas_1۰G۰lstatus۰G :: AuthMonoG (A := leibnizO lstatus) Σ lstep
  ; #[local] mcas_1۰G۰history۰G :: MonoListG Σ location
  ; #[local] mcas_1۰G۰lock۰G :: ExclG Σ unitO
  ; #[local] mcas_1۰G۰helpers۰G :: ghost_mapG Σ gname nat
  ; #[local] mcas_1۰G۰winning۰G :: ExclG Σ unitO
  ; #[local] mcas_1۰G۰owner۰G :: ExclG Σ unitO
  }.

Definition mcas_1۰Σ :=
  #[twins۰Σ val_O
  ; saved_prop۰Σ
  ; saved_pred۰Σ bool
  ; auth_mono۰Σ (A := leibnizO lstatus) lstep
  ; mono_list۰Σ location
  ; excl۰Σ unitO
  ; ghost_mapΣ gname nat
  ; excl۰Σ unitO
  ; excl۰Σ unitO
  ].
#[global] Instance subGｰmcas_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mcas_1۰Σ Σ →
  Mcas1G Σ.
Proof.
  solve_inG.
Qed.

Section mcas_1۰G.
  Context `{mcas_1۰G : Mcas1G Σ}.

  Implicit Type P : iProp Σ.

  #[local] Definition model₁' γ_model v :=
    twins۰twin₁ γ_model (DfracOwn 1) v.
  #[local] Definition model₁ γ v :=
    model₁' γ.(loc۰metadata۰model) v.
  #[local] Definition model₂' γ_model v : iProp Σ :=
    ∃ w,
    ⌜v ≈ w⌝ ∗
    twins۰twin₂ γ_model w.
  #[local] Definition model₂ γ v :=
    model₂' γ.(loc۰metadata۰model) v.

  #[local] Definition lstatus۰auth' η_lstatus lstatus :=
    auth_mono۰auth _ η_lstatus (DfracOwn 1) lstatus.
  #[local] Definition lstatus۰auth η lstatus :=
    lstatus۰auth' η.(metadata۰lstatus) lstatus.
  #[local] Definition lstatus۰lb η lstatus :=
    auth_mono۰lb _ η.(metadata۰lstatus) lstatus.

  #[local] Definition history۰auth' γ_history casns : iProp Σ :=
    mono_list۰auth γ_history (DfracOwn 1) casns ∗
    ⌜NoDup casns⌝ ∗
    [∗ list] casn ∈ removelast casns,
      ∃ η,
      casn ↪ η ∗
      lstatus۰lb η Finished.
  #[local] Definition history۰auth γ casns :=
    history۰auth' γ.(loc۰metadata۰history) casns.
  #[local] Definition history۰lb γ casns : iProp Σ :=
    mono_list۰lb γ.(loc۰metadata۰history) casns ∗
    ⌜NoDup casns⌝.
  #[local] Definition history۰elem' γ_history casn : iProp Σ :=
    mono_list۰elem γ_history casn.
  #[local] Definition history۰elem γ casn :=
    history۰elem' γ.(loc۰metadata۰history) casn.

  #[local] Definition lock' η_lock :=
    excl η_lock ().
  #[local] Definition lock η i : iProp Σ :=
    ∃ η_lock,
    ⌜η.(metadata۰locks) !! i = Some η_lock⌝ ∗
    lock' η_lock.

  #[local] Definition helpers۰auth' η_helpers helpers :=
    ghost_map_auth η_helpers 1 helpers.
  #[local] Definition helpers۰auth η helpers :=
    helpers۰auth' η.(metadata۰helpers) helpers.
  #[local] Definition helpers۰elem η helper i :=
    ghost_map_elem η.(metadata۰helpers) helper (DfracOwn 1) i.

  #[local] Definition winning' η_winning :=
    excl η_winning ().
  #[local] Definition winning η :=
    winning' η.(metadata۰winning).

  #[local] Definition owner' η_owner :=
    excl η_owner ().
  #[local] Definition owner η :=
    owner' η.(metadata۰owner).

  #[local] Definition au η ι Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      [∗ list] descr; v ∈ η.(metadata۰descrs); vs,
        model₁ descr.(descriptor۰meta) v
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ∀∀ b,
      if b then
        ⌜vs ≈ descriptor۰before <$> η.(metadata۰descrs)⌝ ∗
        [∗ list] descr ∈ η.(metadata۰descrs),
          model₁ descr.(descriptor۰meta) descr.(descriptor۰after)
      else
        ∃ i descr v,
        ⌜η.(metadata۰descrs) !! i = Some descr⌝ ∗
        ⌜vs !! i = Some v⌝ ∗
        ⌜descr.(descriptor۰before) ≉ v⌝ ∗
        [∗ list] descr; v ∈ η.(metadata۰descrs); vs,
          model₁ descr.(descriptor۰meta) v
    , COMM
      Ψ b
    }>.

  #[local] Definition helper۰au' η ι descr P : iProp Σ :=
    AU <{
      ∃∃ v,
      model₁ descr.(descriptor۰meta) v
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ⌜v ≈ descriptor۰final descr η⌝ ∗
      model₁ descr.(descriptor۰meta) v
    , COMM
      P
    }>.
  #[local] Definition helper۰au η ι i P : iProp Σ :=
    ∃ descr,
    ⌜η.(metadata۰descrs) !! i = Some descr⌝ ∗
    helper۰au' η ι descr P.

  #[local] Definition casn۰inv۰name ι casn :=
    ι.@"casn".@casn.
  #[local] Definition casn۰inv۰inner casn η ι Ψ : iProp Σ :=
    ∃ 𝑠𝑡𝑎𝑡𝑢𝑠 lstatus helpers prophs,
    casn.[status] ↦ 𝑠𝑡𝑎𝑡𝑢𝑠 ∗
    lstatus۰auth η lstatus ∗
    helpers۰auth η helpers ∗
    prophet_typed۰model global_prophet η.(metadata۰prophet) prophs ∗
    match lstatus with
    | Running i =>
        ⌜𝑠𝑡𝑎𝑡𝑢𝑠 = status۰to_val η Undetermined⌝ ∗
        ⌜prophs = η.(metadata۰prophs)⌝ ∗
        ( au η ι Ψ ∗
          winning η
        ∨ identifier۰model (metadata۰winner η)
        ) ∗
        ( [∗ map] helper ↦ j ∈ helpers,
          ∃ P,
          ⌜j < i⌝ ∗
          saved_prop helper P ∗
          helper۰au η ι j P
        ) ∗
        ( [∗ list] descr ∈ η.(metadata۰descrs),
          descr.(descriptor۰state).[before] ↦ descr.(descriptor۰before) ∗
          descr.(descriptor۰state).[after] ↦ descr.(descriptor۰after)
        ) ∗
        ( [∗ list] descr ∈ take i η.(metadata۰descrs),
          model₂ descr.(descriptor۰meta) descr.(descriptor۰before) ∗
          history۰elem descr.(descriptor۰meta) casn
        ) ∗
        ( [∗ list] j ∈ seq i (metadata۰size η - i),
          lock η j
        )
    | Finished =>
        ⌜𝑠𝑡𝑎𝑡𝑢𝑠 = metadata۰final η⌝ ∗
        identifier۰model (metadata۰winner η) ∗
        (owner η ∨ Ψ (metadata۰success η)) ∗
        ( [∗ map] helper ↦ _ ∈ helpers,
          ∃ P,
          saved_prop helper P ∗
          P
        ) ∗
        ( [∗ list] i ↦ descr ∈ η.(metadata۰descrs),
          ( model₂ descr.(descriptor۰meta) (descriptor۰final descr η)
          ∨ lock η i
          ) ∗
          if metadata۰success η then
            history۰elem descr.(descriptor۰meta) casn ∗
            descr.(descriptor۰state).[after] ↦ descr.(descriptor۰after) ∗
            descr.(descriptor۰state).[before] ↦-
          else
            descr.(descriptor۰state).[before] ↦ descr.(descriptor۰before) ∗
            descr.(descriptor۰state).[after] ↦-
        )
    end.
  #[local] Instance : CustomIpat "casn۰inv۰inner" :=
    " ( %status{}
      & %lstatus{}
      & %helpers{}
      & %prophs{}
      & >Hcasn{}_status
      & >Hlstatus{}_auth
      & >Hhelpers{}_auth
      & >Hgproph{}
      & Hlstatus{}
      )
    ".
  #[local] Instance : CustomIpat "casn۰inv۰inner۰running" :=
    " ( {>;}->
      & {>;}->
      & Hau{}
      & Hhelpers{}
      & {>;}Hdescrs{}
      & {>;}Hmodels₂{}
      & {>;}Hlocks{}
      )
    ".
  #[local] Instance : CustomIpat "casn۰inv۰inner۰finished" :=
    " ( {>;}->
      & {>;}Hwinner{}
      & HΨ{}
      & Hhelpers{}
      & {>;}Hdescrs{}
      )
    ".
  #[local] Definition casn۰inv۰pre ι
    (casn۰inv' : location * metadata * option nat -d> iProp Σ)
    (loc۰inv' : location * loc۰metadata -d> iProp Σ)
  : location * metadata * option nat -d> iProp Σ
  :=
    λ '(casn, η, i), (
      ∃ Ψ,
      casn.[proph] ↦□ #η.(metadata۰prophet) ∗
      saved_pred η.(metadata۰post) Ψ ∗
      ⌜NoDup (descriptor۰loc <$> η.(metadata۰descrs))⌝ ∗
      inv (casn۰inv۰name ι casn) (casn۰inv۰inner casn η ι Ψ) ∗
      [∗ list] j ↦ descr ∈ η.(metadata۰descrs),
        if i is Some i then
          if decide (j = i) then
            descr.(descriptor۰loc) ↪ descr.(descriptor۰meta) ∗
            descr.(descriptor۰state).[casn] ↦□ #casn
          else
            descr.(descriptor۰loc) ↪ descr.(descriptor۰meta) ∗
            descr.(descriptor۰state).[casn] ↦□ #casn ∗
            loc۰inv' (descr.(descriptor۰loc), descr.(descriptor۰meta))
        else
          descr.(descriptor۰loc) ↪ descr.(descriptor۰meta) ∗
          descr.(descriptor۰state).[casn] ↦□ #casn ∗
          loc۰inv' (descr.(descriptor۰loc), descr.(descriptor۰meta))
    )%I.
  #[local] Instance : CustomIpat "casn۰inv" :=
    " ( %Ψ{}
      & Hcasn{}_proph
      & Hpost{}
      & %Hlocs{}
      & Hcasn{}_inv
      & Hlocs{}
      )
    ".
  #[local] Instance casn۰inv۰preｰcontractive ι n :
    Proper (dist_later n ==> (≡{n}≡) ==> (≡{n}≡)) (casn۰inv۰pre ι).
  Proof.
    solve_proper.
  Qed.

  #[local] Definition loc۰inv۰name ι :=
    ι.@"loc".
  #[local] Definition loc۰inv۰inner'' full casn۰inv' loc γ : iProp Σ :=
    ∃ casns casn η i descr,
    casn ↪ η ∗
    ⌜η.(metadata۰descrs) !! i = Some descr⌝ ∗
    ⌜loc = descr.(descriptor۰loc)⌝ ∗
    loc ↦ᵣ #descr.(descriptor۰state) ∗
    lstatus۰lb η (Running ˖i) ∗
    lock η i ∗
    history۰auth γ (casns ++ [casn]) ∗
    casn۰inv' (casn, η, if full then None else Some i).
  #[local] Instance : CustomIpat "loc۰inv۰inner" :=
    " ( %casns{}
      & %casn{}
      & %η{}
      & %i{}
      & %descr{}
      & {>;}{#}Hcasn{}_meta
      & {>;}%Hdescrs{}_lookup
      & {>;}{%Hloc{};->}
      & {>;}Hloc
      & {>;}{#}Hlstatus{}_lb
      & {>;}Hlock{}
      & {>;}Hhistory_auth
      & {#}Hcasn{}_inv'
      )
    ".
  #[local] Definition loc۰inv۰inner' :=
    loc۰inv۰inner'' false.
  #[local] Definition loc۰inv۰pre ι
    (casn۰inv' : location * metadata * option nat -d> iProp Σ)
    (loc۰inv' : location * loc۰metadata -d> iProp Σ)
  : location * loc۰metadata -d> iProp Σ
  :=
    λ '(loc, γ),
      inv (loc۰inv۰name ι) (loc۰inv۰inner' casn۰inv' loc γ).
  #[local] Instance loc۰inv۰preｰcontractive ι n :
    Proper (dist_later n ==> dist_later n ==> (≡{n}≡)) (loc۰inv۰pre ι).
  Proof.
    rewrite /loc۰inv۰pre /loc۰inv۰inner' /loc۰inv۰inner'' /curry.
    solve_contractive.
  Qed.

  #[local] Definition casn۰inv'' ι :=
    fixpoint_A (casn۰inv۰pre ι) (loc۰inv۰pre ι).
  #[local] Definition casn۰inv' ι casn η :=
    casn۰inv'' ι (casn, η, None).
  #[local] Definition casn۰inv casn ι : iProp Σ :=
    ∃ η,
    casn ↪ η ∗
    casn۰inv' ι casn η.

  #[local] Definition loc۰inv' ι :=
    fixpoint_B (casn۰inv۰pre ι) (loc۰inv۰pre ι).
  #[local] Definition loc۰inv۰inner loc γ ι : iProp Σ :=
    loc۰inv۰inner'' true (casn۰inv'' ι) loc γ.
  Definition mcas_1۰loc۰inv loc ι : iProp Σ :=
    ∃ γ,
    loc ↪ γ ∗
    loc۰inv' ι (loc, γ).

  Definition mcas_1۰loc۰model loc v : iProp Σ :=
    ∃ γ,
    loc ↪ γ ∗
    model₁ γ v.
  #[local] Instance : CustomIpat "loc۰model" :=
    " ( %γ{}
      & Hmeta{_{}}
      & Hmodel₁{_{}}
      )
    ".

  #[local] Lemma casn۰inv''ｰunfold ι casn (i : option nat) η :
    casn۰inv'' ι (casn, η, i) ⊣⊢
    casn۰inv۰pre ι (casn۰inv'' ι) (loc۰inv' ι) (casn, η, i).
  Proof.
    symmetry. apply (fixpoint_A_unfold (casn۰inv۰pre ι) (loc۰inv۰pre ι) _).
  Qed.
  #[local] Lemma casn۰inv'ｰunfold ι casn η :
    casn۰inv' ι casn η ⊣⊢
    casn۰inv۰pre ι (casn۰inv'' ι) (loc۰inv' ι) (casn, η, None).
  Proof.
    apply casn۰inv''ｰunfold.
  Qed.

  #[local] Lemma loc۰inv'ｰunfold loc γ ι :
    loc۰inv' ι (loc, γ) ⊣⊢
    inv (loc۰inv۰name ι) (loc۰inv۰inner' (casn۰inv'' ι) loc γ).
  Proof.
    symmetry. apply (fixpoint_B_unfold (casn۰inv۰pre ι) (loc۰inv۰pre ι) (loc, γ)).
  Qed.
  #[local] Lemma loc۰inv'ｰintro loc γ ι :
    inv (loc۰inv۰name ι) (loc۰inv۰inner' (casn۰inv'' ι) loc γ) ⊢
    loc۰inv' ι (loc, γ).
  Proof.
    setoid_rewrite <- (fixpoint_B_unfold (casn۰inv۰pre ι) (loc۰inv۰pre ι) _).
    iIntros "#Hloc_inv".
    iApply (inv_alter with "Hloc_inv"). iIntros "!> !> (:loc۰inv۰inner #=)".
    iFrameSteps.
  Qed.
  #[local] Lemma loc۰inv'ｰelim loc γ ι :
    loc ↪ γ -∗
    loc۰inv' ι (loc, γ) -∗
    inv (loc۰inv۰name ι) (loc۰inv۰inner loc γ ι).
  Proof.
    setoid_rewrite <- (fixpoint_B_unfold (casn۰inv۰pre ι) (loc۰inv۰pre ι) _).
    iIntros "#Hloc_meta #Hloc_inv".
    iApply (inv_alter with "Hloc_inv"). iIntros "!> !> (:loc۰inv۰inner #=)".
    iSplitL.
    - iFrameSteps.
      setoid_rewrite <- (fixpoint_A_unfold (casn۰inv۰pre ι) (loc۰inv۰pre ι) _).
      iDestruct "Hcasn_inv'" as "(:casn۰inv)".
      iSteps.
      iApply (big_sepL_impl with "Hlocs"). iIntros "!> %i' %descr' %Hdescr_lookup' H".
      case_decide; last iSteps. simp.
      iDestruct "H" as "(H & $)".
      iDestruct (metaｰagree with "Hloc_meta H") as %->.
      setoid_rewrite <- (fixpoint_B_unfold (casn۰inv۰pre ι) (loc۰inv۰pre ι) _).
      iSteps.
    - iSteps.
      setoid_rewrite <- (fixpoint_A_unfold (casn۰inv۰pre ι) (loc۰inv۰pre ι) _).
      iSteps.
      iApply (big_sepL_impl with "[$]").
      iSteps.
      case_decide; iSteps.
  Qed.

  #[local] Instance model₂ｰtimeless γ v :
    Timeless (model₂ γ v).
  Proof.
    apply _.
  Qed.
  #[local] Instance history۰authｰtimeless γ casns :
    Timeless (history۰auth γ casns).
  Proof.
    apply _.
  Qed.
  #[local] Instance lockｰtimeless η i :
    Timeless (lock η i).
  Proof.
    apply _.
  Qed.
  #[global] Instance mcas_1۰loc۰modelｰtimeless loc ι :
    Timeless (mcas_1۰loc۰model loc ι).
  Proof.
    apply _.
  Qed.

  #[local] Instance history۰lbｰpersistent γ casns :
    Persistent (history۰lb γ casns).
  Proof.
    apply _.
  Qed.
  #[local] Instance loc۰inv'ｰpersistent loc γ ι :
    Persistent (loc۰inv' ι (loc, γ)).
  Proof.
    rewrite loc۰inv'ｰunfold.
    apply _.
  Qed.
  #[global] Instance mcas_1۰loc۰invｰpersistent loc γ ι :
    Persistent (mcas_1۰loc۰inv loc ι).
  Proof.
    rewrite /mcas_1۰loc۰inv.
    apply _.
  Qed.
  #[local] Instance casn۰inv''ｰpersistent casn η (i : option nat) ι :
    Persistent (casn۰inv'' ι (casn, η, i)).
  Proof.
    rewrite casn۰inv''ｰunfold.
    apply _.
  Qed.
  #[local] Instance casn۰inv'ｰpersistent casn η ι :
    Persistent (casn۰inv' ι casn η).
  Proof.
    apply _.
  Qed.

  #[local] Lemma modelｰalloc v :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model v ∗
      model₂' γ_model v.
  Proof.
    iMod twinsｰalloc' as "(%γ_model & Htwin₁ & Htwin₂)".
    iFrameSteps.
  Qed.
  #[local] Lemma model₁ｰexclusive γ v1 v2 :
    model₁ γ v1 -∗
    model₁ γ v2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma model₂ｰsimilar {γ v1} v2 :
    v1 ≈ v2 →
    model₂ γ v1 ⊢
    model₂ γ v2.
  Proof.
    iIntros (?%symmetry) "(%v & % & Hmodel₂)".
    iExists v. iSteps. iPureIntro. etrans; done.
  Qed.
  #[local] Lemma model₂ｰexclusive γ v1 v2 :
    model₂ γ v1 -∗
    model₂ γ v2 -∗
    False.
  Proof.
    iIntros "(% & % & Hmodel₂1) (% & % & Hmodel₂2)".
    iApply (twins۰twin₂ｰexclusive with "Hmodel₂1 Hmodel₂2").
  Qed.
  #[local] Lemma modelｰagree γ v1 v2 :
    model₁ γ v1 -∗
    model₂ γ v2 -∗
    ⌜v1 ≈ v2⌝.
  Proof.
    iIntros "Hmodel₁ (%w2 & %Hv2 & Hmodel₂)".
    iDestruct (twinsｰagreeｰL with "Hmodel₁ Hmodel₂") as %<-.
    iSteps.
  Qed.
  #[local] Lemma modelｰupdate {γ v1 v2} v :
    model₁ γ v1 -∗
    model₂ γ v2 ==∗
      model₁ γ v ∗
      model₂ γ v.
  Proof.
    iIntros "Hmodel₁ (% & % & Hmodel₂)".
    iMod (twinsｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iFrameSteps.
  Qed.

  #[local] Lemma lstatusｰalloc lstatus :
    ⊢ |==>
      ∃ η_lstatus,
      lstatus۰auth' η_lstatus lstatus.
  Proof.
    apply: auth_monoｰalloc.
  Qed.
  #[local] Lemma lstatus۰lbｰget η lstatus :
    lstatus۰auth η lstatus ⊢
    lstatus۰lb η lstatus.
  Proof.
    apply auth_mono۰lbｰget.
  Qed.
  #[local] Lemma lstatus۰lbｰgetｰrunning0 η lstatus :
    lstatus۰auth η lstatus ⊢
    lstatus۰lb η (Running 0).
  Proof.
    apply auth_mono۰lbｰgetｰmono, lstepsｰrunning0.
  Qed.
  #[local] Lemma lstatus۰lbｰgetｰfinished {η} lstatus :
    lstatus۰auth η Finished ⊢
    lstatus۰lb η lstatus.
  Proof.
    destruct lstatus.
    - apply auth_mono۰lbｰgetｰmono'. done.
    - apply lstatus۰lbｰget.
  Qed.
  #[local] Lemma lstatusｰfinished η lstatus :
    lstatus۰auth η lstatus -∗
    lstatus۰lb η Finished -∗
    ⌜lstatus = Finished⌝.
  Proof.
    iIntros "Hlstatus_auth Hlstatus_lb".
    iDestruct (auth_mono۰lbｰvalid with "Hlstatus_auth Hlstatus_lb") as %->%lstepsｰfinished.
    iSteps.
  Qed.
  #[local] Lemma lstatusｰle η i1 i2 :
    lstatus۰auth η (Running i1) -∗
    lstatus۰lb η (Running i2) -∗
    ⌜i2 ≤ i1⌝.
  Proof.
    iIntros "Hlstatus_auth Hlstatus_lb".
    iDestruct (auth_mono۰lbｰvalid with "Hlstatus_auth Hlstatus_lb") as %Hlsteps.
    iPureIntro. eapply lstepsｰle; done.
  Qed.
  #[local] Lemma lstatusｰupdate {η lstatus} lstatus' :
    lstep lstatus lstatus' →
    lstatus۰auth η lstatus ⊢ |==>
    lstatus۰auth η lstatus'.
  Proof.
    apply auth_monoｰupdate'.
  Qed.

  #[local] Lemma historyｰalloc casn :
    ⊢ |==>
      ∃ γ_history,
      history۰auth' γ_history [casn] ∗
      history۰elem' γ_history casn.
  Proof.
    iMod (mono_listｰalloc [casn]) as "(%γ_history & Hhistory_auth)".
    iDestruct (mono_list۰elemｰget with "Hhistory_auth") as "#Hhistory_elem".
    { apply list_elem_of_singleton. done. }
    iSteps. iPureIntro.
    apply NoDup_singleton.
  Qed.
  #[local] Lemma history۰lbｰget γ casns :
    history۰auth γ casns ⊢
    history۰lb γ casns.
  Proof.
    iIntros "(Hhistory_auth & %Hcasns & _)".
    iDestruct (mono_list۰lbｰget with "Hhistory_auth") as "#Hhistory_lb".
    iSteps.
  Qed.
  #[local] Lemma history۰lbｰvalidｰeq γ casns1 casn casns2 casns3 :
    history۰auth γ (casns1 ++ [casn]) -∗
    history۰lb γ (casns2 ++ casn :: casns3) -∗
      ⌜casns1 = casns2⌝ ∗
      ⌜casns3 = []⌝.
  Proof.
    iIntros "(Hhistory_auth & %Hcasns1 & _) (Hhistory_lb & %Hcasns2)".
    iDestruct (mono_list۰lbｰvalid with "Hhistory_auth Hhistory_lb") as %(casns4 & Heq).
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
  #[local] Lemma history۰lbｰvalidｰne γ casns1 casn1 casns2 casn2 :
    casn1 ≠ casn2 →
    history۰auth γ (casns1 ++ [casn1]) -∗
    history۰lb γ (casns2 ++ [casn2]) -∗
      ∃ casns3,
      history۰lb γ (casns2 ++ [casn2] ++ casns3 ++ [casn1]).
  Proof.
    iIntros "%Hne (Hhistory_auth & %Hcasns1 & _) (#Hhistory_lb2 & %Hcasns2)".
    iDestruct (mono_list۰lbｰget with "Hhistory_auth") as "#Hhistory_lb1".
    iDestruct (mono_list۰lbｰvalid with "Hhistory_auth Hhistory_lb2") as %(casns3 & Heq).
    destruct casns3 as [| casn3 casns3 _] using rev_ind.
    - apply (f_equal last) in Heq.
      rewrite right_id !last_snoc in Heq.
      naive_solver.
    - apply (f_equal last) in Heq as H.
      rewrite assoc last_app_cons !last_snoc /= in H.
      injection H as <-.
      iExists casns3. rewrite assoc -Heq. iSteps.
  Qed.
  #[local] Lemma history۰elemｰvalid γ casns casn :
    history۰auth γ casns -∗
    history۰elem γ casn -∗
    ⌜casn ∈ casns⌝.
  Proof.
    iIntros "(Hhistory_auth & _) Hhistory_elem".
    iApply (mono_list۰elemｰvalid with "Hhistory_auth Hhistory_elem").
  Qed.
  #[local] Lemma historyｰrunning γ casns casn1 casn2 η2 i :
    history۰auth γ (casns ++ [casn1]) -∗
    casn2 ↪ η2 -∗
    lstatus۰auth η2 (Running i) -∗
    ⌜casn2 ∉ casns⌝.
  Proof.
    iIntros "(Hhistory_auth & %Hcasns & Hcasns) Hcasn2_meta Hlstatus2_auth" ((j & Hcasns_lookup)%list_elem_of_lookup).
    iDestruct (big_sepL_lookup with "Hcasns") as "(%_η2 & _Hcasn2_meta & Hlstatus2_lb)".
    { rewrite removelast_last //. }
    iDestruct (metaｰagree with "Hcasn2_meta _Hcasn2_meta") as %<-. iClear "_Hcasn2_meta".
    iDestruct (lstatusｰfinished with "Hlstatus2_auth Hlstatus2_lb") as %[=].
  Qed.
  #[local] Lemma historyｰupdate {γ casns casn1 η1} casn2 :
    casn2 ∉ casns →
    casn2 ≠ casn1 →
    history۰auth γ (casns ++ [casn1]) -∗
    casn1 ↪ η1 -∗
    lstatus۰lb η1 Finished ==∗
      history۰auth γ ((casns ++ [casn1]) ++ [casn2]) ∗
      history۰elem γ casn2.
  Proof.
    iIntros "% % Hhistory_auth Hcasn1_meta Hlstatus1_lb".
    iDestruct "Hhistory_auth" as "(Hhistory_auth & %Hcasns & Hcasns)".
    iMod (mono_listｰupdateｰsnoc casn2 with "Hhistory_auth") as "Hhistory_auth".
    iDestruct (mono_list۰elemｰget with "Hhistory_auth") as "#$"; first set_solver.
    iSteps.
    - iPureIntro.
      rewrite comm NoDup_cons not_elem_of_app list_elem_of_singleton //.
    - rewrite !removelast_last big_sepL_snoc. iSteps.
  Qed.
  #[local] Lemma historyｰupdateｰrunning {γ casns casn1 η1} casn2 η2 i :
    casn1 ≠ casn2 →
    history۰auth γ (casns ++ [casn1]) -∗
    casn1 ↪ η1 -∗
    lstatus۰lb η1 Finished -∗
    casn2 ↪ η2 -∗
    lstatus۰auth η2 (Running i) ==∗
      history۰auth γ ((casns ++ [casn1]) ++ [casn2]) ∗
      history۰elem γ casn2 ∗
      lstatus۰auth η2 (Running i).
  Proof.
    iIntros "% Hhistory_auth Hcasn1_meta Hlstatus1_lb Hcasn2_meta Hlstatus2_auth".
    iDestruct (historyｰrunning with "Hhistory_auth Hcasn2_meta Hlstatus2_auth") as %?.
    iMod (historyｰupdate with "Hhistory_auth Hcasn1_meta Hlstatus1_lb") as "($ & $)"; [done.. |].
    iSteps.
  Qed.

  #[local] Lemma lockｰalloc :
    ⊢ |==>
      ∃ η_lock,
      lock' η_lock.
  Proof.
    apply exclｰalloc.
  Qed.
  #[local] Lemma lockｰallocs n :
    ⊢ |==>
      ∃ ηs_lock,
      ⌜length ηs_lock = n⌝ ∗
      [∗ list] η_lock ∈ ηs_lock,
        lock' η_lock.
  Proof.
    iInduction n as [| n] "IH".
    - iExists []. iSteps.
    - iMod lockｰalloc as "(%η_lock & Hlock)".
      iMod "IH" as "(%ηs_lock & %Hlength & Hlocks)".
      iExists (η_lock :: ηs_lock). iSteps.
  Qed.
  #[local] Lemma lockｰexclusive η i :
    lock η i -∗
    lock η i -∗
    False.
  Proof.
    iIntros "(%γ_lock & %Hlookup & Hexcl1) (%_γ_lock & %_Hlookup & Hexcl2)".
    simp.
    iApply (exclｰexclusive with "Hexcl1 Hexcl2").
  Qed.

  #[local] Lemma helpersｰalloc :
    ⊢ |==>
      ∃ η_helpers,
      helpers۰auth' η_helpers ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma helpersｰinsert {η helpers} i P :
    helpers۰auth η helpers ⊢ |==>
      ∃ helper,
      helpers۰auth η (<[helper := i]> helpers) ∗
      helpers۰elem η helper i ∗
      saved_prop helper P.
  Proof.
    iIntros "Hhelpers_auth".
    iMod (saved_propｰallocｰcofinite (dom helpers)) as "(%helper & %Hhelper & #Hhelper)".
    iMod (ghost_map_insert with "Hhelpers_auth") as "(Hhelpers_auth & Hhelpers_elem)".
    { apply not_elem_of_dom. done. }
    iSteps.
  Qed.
  #[local] Lemma helpersｰlookup η helpers helper i :
    helpers۰auth η helpers -∗
    helpers۰elem η helper i -∗
    ⌜helpers !! helper = Some i⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma helpersｰdelete η helpers helper i :
    helpers۰auth η helpers -∗
    helpers۰elem η helper i ==∗
    helpers۰auth η (delete helper helpers).
  Proof.
    apply ghost_map_delete.
  Qed.

  #[local] Lemma winningｰalloc :
    ⊢ |==>
      ∃ η_winning,
      winning' η_winning.
  Proof.
    apply exclｰalloc.
  Qed.
  #[local] Lemma winningｰexclusive η :
    winning η -∗
    winning η -∗
    False.
  Proof.
    apply exclｰexclusive.
  Qed.

  #[local] Lemma ownerｰalloc :
    ⊢ |==>
      ∃ η_owner,
      owner' η_owner.
  Proof.
    apply exclｰalloc.
  Qed.
  #[local] Lemma ownerｰexclusive η :
    owner η -∗
    owner η -∗
    False.
  Proof.
    apply exclｰexclusive.
  Qed.

  Opaque model₂'.
  Opaque history۰auth'.
  Opaque history۰lb.

  Lemma mcas_1۰loc۰modelｰexclusive loc v1 v2 :
    mcas_1۰loc۰model loc v1 -∗
    mcas_1۰loc۰model loc v2 -∗
    False.
  Proof.
    iIntros "(:loc۰model =1) (:loc۰model =2)".
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  #[local] Lemma casnｰhelp {casn η ι Ψ i} descr P :
    η.(metadata۰descrs) !! i = Some descr →
    inv (casn۰inv۰name ι casn) (casn۰inv۰inner casn η ι Ψ) -∗
    lock η i -∗
    helper۰au' η ι descr P -∗
      |={⊤ ∖ ↑loc۰inv۰name ι}=>
      ∃ helper,
      lock η i ∗
      saved_prop helper P ∗
      helpers۰elem η helper i.
  Proof.
    iIntros "%Hdescrs_lookup #Hcasn_inv Hlock H".
    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    iMod (helpersｰinsert i P with "Hhelpers_auth") as "(%helper & Hhelpers_auth & Hhelpers_elem & #Hhelper)".
    destruct lstatus as [j |].

    - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰running >)".

      iAssert ⌜i < j⌝%I as %Hi.
      { destruct_decide (i < j); first iSteps.
        iDestruct (big_sepLｰseqｰlookup' i with "Hlocks") as "_Hlock".
        { apply lookup_lt_Some in Hdescrs_lookup.
          rewrite /metadata۰size. lia.
        }
        iDestruct (lockｰexclusive with "Hlock _Hlock") as %[].
      }

      iDestruct (big_sepM_insert_2 _ _ helper i with "[H] Hhelpers") as "Hhelpers"; first iSteps.
      iSplitR "Hlock Hhelpers_elem". { iFrameSteps 2. }
      iFrameSteps.

    - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
      iDestruct (big_sepL_lookup_acc with "Hdescrs") as "(([Hmodel₂ | _Hlock] & Hhistory_elem) & Hdescrs)"; first done; last first.
      { iDestruct (lockｰexclusive with "Hlock _Hlock") as %[]. }
      iApply (fupd_mask_mono (⊤ ∖ ↑ι)); first solve_ndisj.
      iMod "H" as "(%v & Hmodel₁ & _ & H)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %Hv.
      iMod ("H" with "[$Hmodel₁ //]") as "HQ".
      iDestruct ("Hdescrs" with "[Hmodel₂ Hhistory_elem]") as "Hdescrs"; first iSteps.
      iDestruct (big_sepM_insert_2 _ _ helper i with "[HQ] Hhelpers") as "Hhelpers"; first iSteps.
      iSplitR "Hlock Hhelpers_elem". { iFrameSteps 2. }
      iFrameSteps.
  Qed.
  #[local] Lemma casnｰretrieve casn η ι Ψ helper P i :
    inv (casn۰inv۰name ι casn) (casn۰inv۰inner casn η ι Ψ) -∗
    lstatus۰lb η Finished -∗
    saved_prop helper P -∗
    helpers۰elem η helper i ={⊤}=∗
    ▷^2 P.
  Proof.
    iIntros "#Hcasn_inv #Hlstatus_lb #Hhelper Hhelpers_elem".
    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    iDestruct (lstatusｰfinished with "Hlstatus_auth Hlstatus_lb") as %->.
    iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
    iDestruct (helpersｰlookup with "Hhelpers_auth Hhelpers_elem") as %Hhelpers_lookup.
    iMod (helpersｰdelete with "Hhelpers_auth Hhelpers_elem") as "Hhelpers_auth".
    iDestruct (big_sepM_delete with "Hhelpers") as "((%_Q & _Hhelper & HQ) & Hhelpers)"; first done.
    iDestruct (saved_propｰagree with "Hhelper _Hhelper") as "Heq".
    iSplitR "HQ Heq". { iFrameSteps 2. }
    iModIntro.

    do 3 iModIntro. iRewrite "Heq". iSteps.
  Qed.

  #[local] Lemma statusｰspecｰfinished casn η ι :
    {{{
      casn۰inv' ι casn η ∗
      lstatus۰lb η Finished
    }}}
      (#casn).{status}
    {{{
      RET metadata۰final η;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hcasn_inv' & #Hlstatus_lb) HΦ".
    iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".
    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    wp۰load.
    iDestruct (lstatusｰfinished with "Hlstatus_auth Hlstatus_lb") as %->.
    iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished)".
    iSplitR "HΦ". { iFrameSteps 2. }
    iSteps.
  Qed.

  #[local] Lemma beforeｰspec {casn η ι} i descr :
    η.(metadata۰descrs) !! i = Some descr →
    {{{
      casn۰inv' ι casn η
    }}}
      (#descr.(descriptor۰state)).{before}
    {{{
      v
    , RET v;
        ⌜v = descr.(descriptor۰before)⌝
      ∨ lstatus۰lb η Finished
    }}}.
  Proof.
    iIntros "%Hdescrs_lookup %Φ #Hcasn_inv' HΦ".
    iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".

    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    destruct lstatus as [j |].

    - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰running >)".
      iDestruct (big_sepL_lookup_acc with "Hdescrs") as "((Hstate_before & Hstate_after) & Hdescrs)"; first done.
      wp۰load.
      iDestruct ("Hdescrs" with "[$]") as "Hdescrs".
      iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
      iDestruct (lstatus۰lbｰget with "Hlstatus_auth") as "#Hlstatus_lb".
      destruct (metadata۰success η) eqn:Hsuccess.
      1: iDestruct (big_sepL_lookup_acc with "Hdescrs") as "((Hmodel₂ & History_elem & Hstate_after & %v & Hstate_before) & Hdescrs)"; first done.
      2: iDestruct (big_sepL_lookup_acc with "Hdescrs") as "((Hmodel₂ & Hstate_before & Hstate_after) & Hdescrs)"; first done.
      all: wp۰load.
      all: iDestruct ("Hdescrs" with "[$]") as "Hdescrs".
      all: iSplitR "HΦ"; first (rewrite /casn۰inv۰inner Hsuccess; iFrameSteps 2).
      all: iApply "HΦ"; iRight; iSteps.
  Qed.
  #[local] Lemma beforeｰspecｰfinished {casn η ι} i descr :
    η.(metadata۰descrs) !! i = Some descr →
    metadata۰success η = false →
    {{{
      casn۰inv' ι casn η ∗
      lstatus۰lb η Finished
    }}}
      (#descr.(descriptor۰state)).{before}
    {{{
      RET descr.(descriptor۰before);
      True
    }}}.
  Proof.
    iIntros "%Hdescrs_lookup %Hsuccess %Φ (#Hcasn_inv' & #Hlstatus_lb) HΦ".
    iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".

    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    iDestruct (lstatusｰfinished with "Hlstatus_auth Hlstatus_lb") as %->.
    iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
    rewrite Hsuccess.
    iDestruct (big_sepL_lookup_acc with "Hdescrs") as "((Hmodel₂ & Hstate_before & Hstate_after) & Hdescrs)"; first done.
    wp۰load.
    iDestruct ("Hdescrs" with "[$]") as "Hdescrs".
    iSplitR "HΦ". { rewrite /casn۰inv۰inner Hsuccess. iFrameSteps 2. }
    iSteps.
  Qed.
  #[local] Lemma set_beforeｰspecｰfinished {casn η ι} i descr v :
    η.(metadata۰descrs) !! i = Some descr →
    metadata۰success η = true →
    {{{
      casn۰inv' ι casn η ∗
      lstatus۰lb η Finished
    }}}
      (#descr.(descriptor۰state)) <-{before} v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hdescrs_lookup %Hsuccess %Φ (#Hcasn_inv' & #Hlstatus_lb) HΦ".
    iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".

    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    iDestruct (lstatusｰfinished with "Hlstatus_auth Hlstatus_lb") as %->.
    iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
    rewrite Hsuccess.
    iDestruct (big_sepL_lookup_acc with "Hdescrs") as "((Hmodel₂ & Hhistory_elem & Hstate_before & % & Hstate_after) & Hdescrs)"; first done.
    wp۰store.
    iDestruct ("Hdescrs" with "[$]") as "Hdescrs".
    iSplitR "HΦ". { rewrite /casn۰inv۰inner Hsuccess. iFrameSteps 2. }
    iSteps.
  Qed.

  #[local] Lemma afterｰspecｰfinished {casn η ι} i descr :
    η.(metadata۰descrs) !! i = Some descr →
    metadata۰success η = true →
    {{{
      casn۰inv' ι casn η ∗
      lstatus۰lb η Finished
    }}}
      (#descr.(descriptor۰state)).{after}
    {{{
      RET descr.(descriptor۰after);
      True
    }}}.
  Proof.
    iIntros "%Hdescrs_lookup %Hsuccess %Φ (#Hcasn_inv' & #Hlstatus_lb) HΦ".
    iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".

    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    iDestruct (lstatusｰfinished with "Hlstatus_auth Hlstatus_lb") as %->.
    iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
    rewrite Hsuccess.
    iDestruct (big_sepL_lookup_acc with "Hdescrs") as "((Hmodel₂ & Hhistory_elem & Hstate_before & Hstate_after) & Hdescrs)"; first done.
    wp۰load.
    iDestruct ("Hdescrs" with "[$]") as "Hdescrs".
    iSplitR "HΦ". { rewrite /casn۰inv۰inner Hsuccess. iFrameSteps 2. }
    iSteps.
  Qed.
  #[local] Lemma set_afterｰspecｰfinished {casn η ι} i descr v :
    η.(metadata۰descrs) !! i = Some descr →
    metadata۰success η = false →
    {{{
      casn۰inv' ι casn η ∗
      lstatus۰lb η Finished
    }}}
      (#descr.(descriptor۰state)) <-{after} v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hdescrs_lookup %Hsuccess %Φ (#Hcasn_inv' & #Hlstatus_lb) HΦ".
    iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".

    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    iDestruct (lstatusｰfinished with "Hlstatus_auth Hlstatus_lb") as %->.
    iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
    rewrite Hsuccess.
    iDestruct (big_sepL_lookup_acc with "Hdescrs") as "((Hmodel₂ & Hstate_before & % & Hstate_after) & Hdescrs)"; first done.
    wp۰store.
    iDestruct ("Hdescrs" with "[$]") as "Hdescrs".
    iSplitR "HΦ". { rewrite /casn۰inv۰inner Hsuccess. iFrameSteps 2. }
    iSteps.
  Qed.

  #[local] Lemma mcas_1٠status_to_boolｰspec fstatus :
    {{{
      True
    }}}
      mcas_1٠status_to_bool (final_status۰to_val fstatus)
    {{{
      RET #(final_status۰to_bool fstatus);
      True
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰rec.
    destruct fstatus; iSteps.
  Qed.

  #[local] Lemma mcas_1٠clearｰspec casn η ι b :
    b = metadata۰success η →
    {{{
      casn۰inv' ι casn η ∗
      lstatus۰lb η Finished
    }}}
      mcas_1٠clear (metadata۰cass۰val η) #b
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hcasn_inv' & #Hlstatus_lb) HΦ".
    iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".

    wp۰rec. wp۰pures.
    destruct (metadata۰success η) eqn:Hsuccess.
    all: wp۰apply+ (list٠iterｰspecｰdisentangled (λ _ _, True)%I); [done | | iSteps].
    all: iIntros "!>" (i v (descr & -> & Hdescrs_lookup)%list_lookup_fmap_Some).

    - wp۰apply+ (afterｰspecｰfinished with "[$Hcasn_inv' $Hlstatus_lb]") as "_"; [done.. |].
      wp۰apply+ (set_beforeｰspecｰfinished with "[$Hcasn_inv' $Hlstatus_lb]"); [done.. |].
      iSteps.

    - wp۰apply+ (beforeｰspecｰfinished with "[$Hcasn_inv' $Hlstatus_lb]") as "_"; [done.. |].
      wp۰apply+ (set_afterｰspecｰfinished with "[$Hcasn_inv' $Hlstatus_lb]"); [done.. |].
      iSteps.
  Qed.

  #[local] Lemma mcas_1٠finishｰspec {gid casn η ι} fstatus :
    {{{
      casn ↪ η ∗
      casn۰inv' ι casn η ∗
      ( ( ⌜gid ≠ metadata۰winner η⌝ ∗
          identifier۰model gid
        ) ∨ (
          ∃ Ψ,
          ⌜fstatus = FinalBefore⌝ ∗
          winning η ∗
          saved_pred η.(metadata۰post) Ψ ∗
          Ψ false
        ) ∨ (
          ∃ i,
          ⌜gid = metadata۰winner η⌝ ∗
          identifier۰model gid ∗
          ⌜fstatus = FinalAfter⌝ ∗
          ⌜metadata۰size η ≤ i⌝ ∗
          lstatus۰lb η (Running i)
        ) ∨ (
          lstatus۰lb η Finished
        )
      )
    }}}
      mcas_1٠finish #gid #casn (final_status۰to_val fstatus)
    {{{
      RET #(metadata۰success η);
      lstatus۰lb η Finished
    }}}.
  Proof.
    iIntros "%Φ (#Hcasn_meta & #Hcasn_inv' & H) HΦ".
    iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".

    wp۰rec. wp۰pures.

    wp۰bind (_.{status})%E.
    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    wp۰load.
    destruct lstatus as [i |].

    - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰running)".
      iSplitR "H HΦ". { iFrameSteps 2. }
      iModIntro. clear.

      wp۰apply+ (mcas_1٠status_to_boolｰspec with "[//]") as "_".
      wp۰load. wp۰pures.

      wp۰bind (𝗿𝗲𝘀𝗼𝗹𝘃𝗲 _ _ _)%E.
      wp۰apply (wpｰwand (λ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        ⌜b = true → final_status۰to_bool fstatus = metadata۰success η⌝ ∗
        lstatus۰lb η Finished
      )%I with "[- HΦ]") as (res) "(%b & -> & % & #Hlstatus_lb)".

      { iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
        wp۰apply (prophet_typedｰwpｰresolve global_prophet with "Hgproph"). 1: done.
        destruct lstatus as [i |].

        - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰running >)".
          wp۰cas as Hcas | _.
          { exfalso. zoo۰simp in Hcas. naive_solver. }
          iStep. iIntros "!> %prophs %Hprophs Hgproph".

          assert (metadata۰success η = final_status۰to_bool fstatus) as Hsuccess.
          { rewrite /metadata۰success /metadata۰outcome Hprophs //. }

          iAssert (
            ( [∗ list] descr ∈ take i η.(metadata۰descrs),
              model₂ descr.(descriptor۰meta) (descriptor۰final descr η)
            ) ={⊤ ∖ ↑casn۰inv۰name ι casn}=∗
              ( [∗ map] helper ↦ j ∈ helpers,
                ∃ P,
                saved_prop helper P ∗
                P
              ) ∗
              ( [∗ list] descr ∈ take i η.(metadata۰descrs),
                model₂ descr.(descriptor۰meta) (descriptor۰final descr η)
              )
          )%I with "[Hhelpers]" as "Hhelpers".
          { iIntros "Hmodels₂".
            iApply (big_sepMｰimplｰthreadｰfupd _ (
              λ helper j,
                ∃ P,
                saved_prop helper P ∗
                P
            )%I with "Hhelpers Hmodels₂ []").
            iIntros "!> %helper %j %Hhelpers_lookup (%P & %Hj & Hhelper & (%descr & %Hdescrs_lookup & HQ)) Hmodels₂".
            iDestruct (big_sepL_lookup_acc with "Hmodels₂") as "(Hmodel₂ & Hmodels₂)".
            { rewrite lookup_take_Some //. }
            iMod "HQ" as "(%v & Hmodel₁ & _ & HQ)".
            iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %Hv.
            iSteps.
          }

          iDestruct "H" as "[(%Hgid & Hgid) | [(%Ψ_ & -> & Hwinning & Hpost_ & HΨ) | [(%j & -> & Hgid & -> & %Hj & #Hlstatus_lb)| #Hlstatus_lb]]]".

          + apply (f_equal (fst ∘ hd inhabitant)) in Hprophs. done.

          + iDestruct (saved_predｰagree false with "Hpost Hpost_") as "Heq".
            iDestruct "Hau" as "[(Hau & _Hwinning) | Hwinner]".
            { iDestruct (winningｰexclusive with "Hwinning _Hwinning") as %[]. }

            iDestruct (big_sepL_sep with "Hmodels₂") as "(Hmodels₂ & _)".
            iMod ("Hhelpers" with "[Hmodels₂]") as "(Hhelpers & Hmodels₂)".
            { rewrite /descriptor۰final Hsuccess //. }

            iAssert (
              [∗ list] i ↦ descr ∈ η.(metadata۰descrs),
                  model₂ descr.(descriptor۰meta) (descriptor۰final descr η)
                ∨ lock η i
            )%I with "[Hmodels₂ Hlocks]" as "Hmodels₂".
            { iApply big_sepL_take_drop. iSplitL "Hmodels₂".
              - iApply (big_sepL_impl with "Hmodels₂").
                rewrite /descriptor۰final Hsuccess /=. iSteps.
              - iApply (big_sepLｰseqｰindex₁ (drop i η.(metadata۰descrs))) in "Hlocks".
                { simp_length. }
                iApply (big_sepL_impl with "Hlocks").
                iSteps.
            }

            iMod (lstatusｰupdate Finished with "Hlstatus_auth") as "Hlstatus_auth"; first done.
            iDestruct (lstatus۰lbｰget with "Hlstatus_auth") as "#$".
            iSplitL; last iSteps. do 2 iModIntro.
            iRewrite -"Heq" in "HΨ".
            rewrite /casn۰inv۰inner Hsuccess. iFrameSteps 2.
            { rewrite /metadata۰final Hsuccess //. }
            { iApply (big_sepL_sep_2 with "Hmodels₂ [Hdescrs]").
              iApply (big_sepL_impl with "Hdescrs").
              iSteps.
            }

          + iDestruct "Hau" as "[(Hau & Hwinning) | Hwinner]"; last first.
            { iDestruct (identifier۰modelｰexclusive with "Hgid Hwinner") as %[]. }
            iDestruct (lstatusｰle with "Hlstatus_auth Hlstatus_lb") as %Hi.
            iMod (lstatusｰupdate Finished with "Hlstatus_auth") as "Hlstatus_auth"; first done.
            iDestruct (lstatus۰lbｰget with "Hlstatus_auth") as "#$".
            rewrite firstn_all2.
            { rewrite /metadata۰size in Hj. lia. }
            iMod "Hau" as "(%vs & Hmodels₁ & _ & HΨ)".

            iDestruct (big_sepL2_sep_sepL_l with "[$Hmodels₂ $Hmodels₁]") as "Hmodels".
            iMod (big_sepL2ｰimplｰbupd _ _ (λ _ descr v,
              ( model₁ descr.(descriptor۰meta) descr.(descriptor۰after) ∗
                model₂ descr.(descriptor۰meta) (descriptor۰final descr η) ∗
                history۰elem descr.(descriptor۰meta) casn
              ) ∗
              ⌜descr.(descriptor۰before) ≈ v⌝
            )%I with "Hmodels []") as "Hmodels".
            { iIntros "!> %k %descr %v %Hdescrs_lookup %Hvs_lookup ((Hmodel₂ & Hhistory_elem) & Hmodel₁)".
              iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %Hv.
              iMod (modelｰupdate descr.(descriptor۰after) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
              rewrite /descriptor۰final Hsuccess /=.
              iSteps.
            }
            iDestruct (big_sepL2_sep_sepL_l with "Hmodels") as "(Hmodels & Hvs)".
            iDestruct (big_sepL_sep with "Hmodels") as "(Hmodels₁ & Hmodels₂)".
            iDestruct (big_sepL2ｰForall2 with "Hvs") as %Hvs. iClear "Hvs".

            iMod ("HΨ" $! true with "[Hmodels₁]") as "HΨ".
            { iSteps. iPureIntro.
              symmetry. setoid_rewrite Forall2_fmap_l. done.
            }
            iDestruct (big_sepL_sep with "Hmodels₂") as "(Hmodels₂ & Hhistory_elems)".
            iMod ("Hhelpers" with "Hmodels₂") as "(Hhelpers & Hmodels₂)".
            iApply (big_sepLｰorｰr (λ i _, lock η i)) in "Hmodels₂".
            iDestruct (big_sepL_sep_2 with "Hmodels₂ Hhistory_elems") as "Hmodels₂".
            iSplitL; last iSteps. do 2 iModIntro.
            rewrite /casn۰inv۰inner Hsuccess. iFrameSteps 2.
            { rewrite /metadata۰final Hsuccess //. }
            { iDestruct (big_sepL_sep with "[$Hmodels₂ $Hdescrs]") as "Hdescrs".
              iApply (big_sepL_impl with "Hdescrs"). iIntros "!>".
              iSteps.
            }

          + iDestruct (lstatusｰfinished with "Hlstatus_auth Hlstatus_lb") as %[=].

        - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
          wp۰cas as _ | []%final_status۰to_valｰundetermined.
          iDestruct (lstatus۰lbｰget with "Hlstatus_auth") as "#Hlstatus_lb".
          iSteps.
      }

      wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
      wp۰apply (wpｰwand itype۰unit with "[- HΦ]") as (res) "->".
      { destruct b; last iSteps.
        wp۰apply+ (mcas_1٠clearｰspec with "[$Hcasn_inv' $Hlstatus_lb]"); first auto.
        iSteps.
      }

      wp۰apply+ (statusｰspecｰfinished with "[$Hcasn_inv' $Hlstatus_lb]") as "_".
      wp۰apply (mcas_1٠status_to_boolｰspec with "[//]") as "_".
      rewrite final_statusｰto_boolｰof_bool. iSteps.

    - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished)".
      iDestruct (lstatus۰lbｰget with "Hlstatus_auth") as "#Hlstatus_lb".
      iSplitR "HΦ". { iFrameSteps 2. }
      iModIntro. clear.

      rewrite /metadata۰final. destruct (metadata۰success η); iSteps.
  Qed.
  #[local] Lemma mcas_1٠finishｰspecｰloser {gid casn η ι} fstatus :
    gid ≠ metadata۰winner η →
    {{{
      casn ↪ η ∗
      casn۰inv' ι casn η ∗
      identifier۰model gid
    }}}
      mcas_1٠finish #gid #casn (final_status۰to_val fstatus)
    {{{
      RET #(metadata۰success η);
      lstatus۰lb η Finished
    }}}.
  Proof.
    iIntros "%Hgid %Φ (#Hcasn_meta & #Hcasn_inv' & Hgid) HΦ".
    wp۰apply (mcas_1٠finishｰspec with "[- HΦ] HΦ").
    iSteps.
  Qed.
  #[local] Lemma mcas_1٠finishｰspecｰwinnerｰbefore gid casn η ι Ψ :
    gid = metadata۰winner η →
    {{{
      casn ↪ η ∗
      casn۰inv' ι casn η ∗
      winning η ∗
      saved_pred η.(metadata۰post) Ψ ∗
      Ψ false
    }}}
      mcas_1٠finish #gid #casn §Before
    {{{
      RET #(metadata۰success η);
      lstatus۰lb η Finished
    }}}.
  Proof.
    iIntros "%Hgid %Φ (#Hcasn_meta & #Hcasn_inv' & Hwinning & #Hpost & HΨ) HΦ".
    wp۰apply (mcas_1٠finishｰspec FinalBefore with "[- HΦ] HΦ").
    iSteps.
  Qed.
  #[local] Lemma mcas_1٠finishｰspecｰafter {gid casn η ι} i :
    metadata۰size η ≤ i →
    {{{
      casn ↪ η ∗
      casn۰inv' ι casn η ∗
      identifier۰model gid ∗
      lstatus۰lb η (Running i)
    }}}
      mcas_1٠finish #gid #casn §After
    {{{
      RET #(metadata۰success η);
      lstatus۰lb η Finished
    }}}.
  Proof.
    iIntros "%Hi %Φ (#Hcasn_meta & #Hcasn_inv' & Hgid & #Hlstatus_lb) HΦ".
    wp۰apply (mcas_1٠finishｰspec FinalAfter with "[- HΦ] HΦ").
    destruct_decide (gid = metadata۰winner η); iSteps.
  Qed.
  #[local] Lemma mcas_1٠finishｰspecｰfinished gid casn η ι :
    {{{
      casn ↪ η ∗
      casn۰inv' ι casn η ∗
      lstatus۰lb η Finished
    }}}
      mcas_1٠finish #gid #casn §Before
    {{{
      RET #(metadata۰success η);
      lstatus۰lb η Finished
    }}}.
  Proof.
    iIntros "%Φ (#Hcasn_meta & #Hcasn_inv' & #Hlstatus_lb) HΦ".
    wp۰apply (mcas_1٠finishｰspec FinalBefore with "[- HΦ] HΦ").
    iSmash.
  Qed.

  #[local] Lemma descriptor۰stateｰinj {ι casn1 η1 casn2 η2} i1 descr1 i2 descr2 :
    casn1 ≠ casn2 →
    η1.(metadata۰descrs) !! i1 = Some descr1 →
    η2.(metadata۰descrs) !! i2 = Some descr2 →
    casn۰inv' ι casn1 η1 -∗
    casn۰inv' ι casn2 η2 ={⊤ ∖ ↑loc۰inv۰name ι}=∗
    ⌜descr1.(descriptor۰state) ≠ descr2.(descriptor۰state)⌝.
  Proof.
    iIntros "%Hneq %Hdescrs1_lookup %Hdescrs2_lookup #Hcasn1_inv' #Hcasn2_inv'".
    iDestruct (casn۰inv'ｰunfold with "Hcasn1_inv'") as "(:casn۰inv =1)".
    iDestruct (casn۰inv'ｰunfold with "Hcasn2_inv'") as "(:casn۰inv =2)".
    iInv "Hcasn1_inv" as "(:casn۰inv۰inner =1)".
    iInv "Hcasn2_inv" as "(:casn۰inv۰inner =2)".
    all:
      destruct lstatus1 as [j1 |];
      [ iDestruct "Hlstatus1" as "(:casn۰inv۰inner۰running > =1)";
        iDestruct (big_sepL_lookup_acc with "Hdescrs1") as "((Hstate1_before & Hstate1_after) & Hdescrs1)"; first done
      | iDestruct "Hlstatus1" as "(:casn۰inv۰inner۰finished > =1)";
        destruct (metadata۰success η1) eqn:Hsuccess1;
        [ iDestruct (big_sepL_lookup_acc with "Hdescrs1") as "((Hmodel₂1 & Hhistory1_elem & Hstate1_after & (% & Hstate1_before)) & Hdescrs1)"; first done
        | iDestruct (big_sepL_lookup_acc with "Hdescrs1") as "((Hmodel₂1 & Hstate1_before & Hstate1_after) & Hdescrs1)"; first done
        ]
      ].
    all:
      destruct lstatus2 as [j2 |];
      [ iDestruct "Hlstatus2" as "(:casn۰inv۰inner۰running > =2)";
        iDestruct (big_sepL_lookup_acc with "Hdescrs2") as "((Hstate2_before & Hstate2_after) & Hdescrs2)"; first done
      | iDestruct "Hlstatus2" as "(:casn۰inv۰inner۰finished > =2)";
        destruct (metadata۰success η2) eqn:Hsuccess2;
        [ iDestruct (big_sepL_lookup_acc with "Hdescrs2") as "((Hmodel₂2 & Hhistory2_elem & Hstate2_after & (% & Hstate2_before)) & Hdescrs2)"; first done
        | iDestruct (big_sepL_lookup_acc with "Hdescrs2") as "((Hmodel₂2 & Hstate2_before & Hstate2_after) & Hdescrs2)"; first done
        ]
      ].
    all: iDestruct (pointstoｰne with "Hstate1_before Hstate2_before") as %?.
    all: iDestruct ("Hdescrs1" with "[$]") as "Hdescrs1".
    all: iDestruct ("Hdescrs2" with "[$]") as "Hdescrs2".
    all:
      ( iSplitR "Hcasn1_status Hlstatus1_auth Hhelpers1_auth Hgproph1 Hau1 Hhelpers1 Hmodels₂1 Hlocks1 Hdescrs1" ||
        iSplitR "Hcasn1_status Hlstatus1_auth Hhelpers1_auth Hgproph1 Hwinner1 HΨ1 Hhelpers1 Hdescrs1"
      );
      first (rewrite /casn۰inv۰inner ?Hsuccess2; iFrameSteps 2).
    all: iSplitL; first (rewrite /casn۰inv۰inner ?Hsuccess1; iFrameSteps 2).
    all: iPureIntro; congruence.
  Qed.

  #[local] Lemma mcas_1٠determine_asｰevalｰdetermineｰspec ι :
    ⊢ (
      ∀ casn η 𝑐𝑎𝑠𝑠 i,
      {{{
        ⌜𝑐𝑎𝑠𝑠 = list۰to_val (drop i (metadata۰cass η))⌝ ∗
        casn ↪ η ∗
        casn۰inv' ι casn η ∗
        lstatus۰lb η (Running i)
      }}}
        mcas_1٠determine_as #casn 𝑐𝑎𝑠𝑠
      {{{
        RET #(metadata۰success η);
        lstatus۰lb η Finished
      }}}
    ) ∧ (
      ∀ casn η i descr casn1 η1 i1 descr1 casns1 𝑟𝑒𝑡𝑟𝑦 𝑐𝑜𝑛𝑡𝑖𝑛𝑢𝑒,
      {{{
        ⌜𝑟𝑒𝑡𝑟𝑦 = list۰to_val (drop i (metadata۰cass η))⌝ ∗
        ⌜𝑐𝑜𝑛𝑡𝑖𝑛𝑢𝑒 = list۰to_val (drop ˖i (metadata۰cass η))⌝ ∗
        ⌜η.(metadata۰descrs) !! i = Some descr⌝ ∗
        ⌜η1.(metadata۰descrs) !! i1 = Some descr1⌝ ∗
        ⌜descr1.(descriptor۰loc) = descr.(descriptor۰loc)⌝ ∗
        ⌜descr1.(descriptor۰meta) = descr.(descriptor۰meta)⌝ ∗
        ⌜casn1 ≠ casn⌝ ∗
        casn ↪ η ∗
        casn۰inv' ι casn η ∗
        lstatus۰lb η (Running i) ∗
        casn1 ↪ η1 ∗
        casn۰inv' ι casn1 η1 ∗
        lstatus۰lb η1 Finished ∗
        history۰lb descr.(descriptor۰meta) (casns1 ++ [casn1]) ∗
        ( lstatus۰lb η Finished
        ∨ ⌜descriptor۰final descr1 η1 ≈ descr.(descriptor۰before)⌝
        )
      }}}
        mcas_1٠lock #casn #descr.(descriptor۰loc) #descr1.(descriptor۰state) #descr.(descriptor۰state) 𝑟𝑒𝑡𝑟𝑦 𝑐𝑜𝑛𝑡𝑖𝑛𝑢𝑒
      {{{
        RET #(metadata۰success η);
        lstatus۰lb η Finished
      }}}
    ) ∧ (
      ∀ casn η i descr,
      {{{
        ⌜η.(metadata۰descrs) !! i = Some descr⌝ ∗
        casn ↪ η ∗
        casn۰inv' ι casn η
      }}}
        mcas_1٠eval #descr.(descriptor۰state)
      {{{
        RET descriptor۰final descr η;
        lstatus۰lb η Finished ∗
        £ 1
      }}}
    ) ∧ (
      ∀ casn η,
      {{{
        casn ↪ η ∗
        casn۰inv' ι casn η
      }}}
        mcas_1٠determine #casn
      {{{
        RET #(metadata۰success η);
        lstatus۰lb η Finished
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHdetermine_as & IHlock & IHeval & IHdetermine)".
    repeat iSplit.

    { iIntros "%casn %η %𝑐𝑎𝑠𝑠 %i !> %Φ (-> & #Hcasn_meta & #Hcasn_inv' & #Hlstatus_lb) HΦ".
      iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".

      wp۰rec credit:"H£".
      wp۰apply+ (wpｰid with "[//]") as (gid) "Hgid".

      destruct (η.(metadata۰descrs) !! i) as [descr |] eqn:Hdescrs_lookup.

      - apply lookup_lt_Some in Hdescrs_lookup as Hi.
        erewrite drop_S; last first.
        { apply list_lookup_fmap_Some. naive_solver. }
        iDestruct (big_sepL_lookup with "Hlocs") as "(Hloc_meta & Hstate_casn & Hloc_inv')"; first done.
        iDestruct (loc۰inv'ｰelim with "Hloc_meta Hloc_inv'") as "Hloc_inv".

        wp۰apply+ (prophet_typed₁ｰwpｰproph prophet_bool₁ with "[//]") as (pid b) "Hlproph".
        wp۰pures.

        wp۰bind (!_)%E.
        iInv "Hloc_inv" as "(:loc۰inv۰inner > =1)".
        wp۰load.
        iDestruct (casn۰inv'ｰunfold with "Hcasn1_inv'") as "(:casn۰inv =1)".
        iDestruct (history۰lbｰget with "Hhistory_auth") as "#Hhistory_lb1".

        iAssert ⌜descr1.(descriptor۰meta) = descr.(descriptor۰meta)⌝%I as %Hmeta1.
        { iDestruct (big_sepL_lookup with "Hlocs") as "(Hloc_meta_1 & _)"; first done.
          iDestruct (big_sepL_lookup with "Hlocs1") as "(Hloc_meta_2 & _)"; first done.
          iEval (rewrite -Hloc1) in "Hloc_meta_2".
          iApply (metaｰagree with "Hloc_meta_2 Hloc_meta_1").
        }

        destruct_decide (casn1 = casn) as -> | Hcasn1.

        + iDestruct (metaｰagree with "Hcasn_meta Hcasn1_meta") as %<-. iClear "Hcasn1_meta".
          assert (i1 = i) as ->.
          { eapply NoDup_lookup; first done.
            - rewrite list_lookup_fmap Hdescrs1_lookup //.
            - rewrite list_lookup_fmap Hdescrs_lookup -Hloc1 //.
          }
          simp.
          iSplitR "HΦ". { iFrameSteps. }
          iModIntro. clear.

          wp۰pures. rewrite bool_decide_eq_true_2 //.
          wp۰apply+ ("IHdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus1_lb //] HΦ").

        + iMod (descriptor۰stateｰinj with "Hcasn_inv' Hcasn1_inv'") as %?; [done.. |].
          destruct_decide (
            gid = metadata۰winner η ∧
            b = false ∧
            descr.(descriptor۰before) ≉ descriptor۰final descr1 η1
          ) as (-> & -> & Hbefore) | Hok%not_and_r_alt.

          * iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
            destruct lstatus as [j |]; last first.
            { iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
              iDestruct (identifier۰modelｰexclusive with "Hgid Hwinner") as %[].
            }
            iDestruct "Hlstatus" as "(:casn۰inv۰inner۰running >)".
            iDestruct "Hau" as "[(Hau & Hwinning) | >Hwinner]"; last first.
            { iDestruct (identifier۰modelｰexclusive with "Hgid Hwinner") as %[]. }
            iMod (lc_fupd_elim_later with "H£ Hau") as "Hau".
            iSplitR "Hloc Hlock1 Hhistory_auth Hau Hwinning Hlproph HΦ". { iFrameSteps 2. }
            iModIntro. clear j helpers.

            iMod (casnｰhelp _ (Ψ false) with "Hcasn1_inv Hlock1 [Hau]") as "(%helper & Hlock1 & #Hhelper & Hhelpers1_elem)"; [solve_ndisj | done.. | |].
            { rewrite /helper۰au'. iAuIntro.
              iApply (aaccｰaupdｰcommit with "Hau"); first done. iIntros "%vs Hmodels₂".
              iDestruct (big_sepL2ｰlookupｰaccｰl with "Hmodels₂") as "(%v & %Hvs_lookup & Hmodel₁ & Hmodels₂)"; first done.
              rewrite Hmeta1. iAaccIntro with "Hmodel₁"; first iSteps.
              iStep. iExists false. iSteps. iPureIntro.
              eapply valｰnonsimilarｰsimilar; done.
            }

            iSplitR "Hwinning Hhelpers1_elem Hlproph HΦ". { iFrameSteps 2. }
            iModIntro.

            wp۰pures. rewrite bool_decide_eq_false_2 //.

            iClear "Hlstatus1_lb".
            wp۰apply+ ("IHeval" with "[$Hcasn1_meta $Hcasn1_inv']") as "(#Hlstatus1_lb & H£)"; first iSteps.
            iMod (casnｰretrieve with "Hcasn1_inv Hlstatus1_lb Hhelper Hhelpers1_elem") as "HΨ".

            wp۰apply (beforeｰspec with "Hcasn_inv'") as (v) "Hbefore"; first done.
            wp۰equal.
            all: wp۰apply+ (prophet_typed₁ｰwpｰresolve prophet_bool₁ with "Hlproph"); [done.. |].
            all: iStep 12.
            wp۰apply (mcas_1٠finishｰspecｰwinnerｰbefore with "[- HΦ] HΦ"); first done.
            iSteps.

          * iSplitR "Hgid Hlproph HΦ". { iFrameSteps. }
            iModIntro.

            wp۰pures. rewrite bool_decide_eq_false_2 //.

            iClear "Hlstatus1_lb".
            wp۰apply+ ("IHeval" with "[$Hcasn1_meta $Hcasn1_inv']") as "(#Hlstatus1_lb & H£)"; first iSteps.
            wp۰apply (beforeｰspec with "Hcasn_inv'") as (v) "Hbefore"; first done.
            wp۰equal.
            all: wp۰apply+ (prophet_typed₁ｰwpｰresolve prophet_bool₁ with "Hlproph"); [done.. |].
            all: iStep 12.

            -- iDestruct "Hbefore" as "[-> | #Hlstatus_lb_finished]".

               ++ destruct Hok as [(Hgid & _ & _) | Hbefore%not_and_l].

                  ** wp۰apply (mcas_1٠finishｰspecｰloser FinalBefore with "[$Hcasn_meta $Hcasn_inv' $Hgid] HΦ"); first done.

                  ** exfalso. naive_solver.

               ++ wp۰apply (mcas_1٠finishｰspecｰfinished with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb_finished] HΦ").

            -- wp۰apply ("IHlock" with "[- HΦ] HΦ").
               erewrite (drop_S _ _ i); last first.
               { rewrite list_lookup_fmap Hdescrs_lookup //. }
               iFrameSteps. done.

      - rewrite dropｰlookupｰNone //.
        { rewrite list_lookup_fmap Hdescrs_lookup //. }
        wp۰apply+ (mcas_1٠finishｰspecｰafter with "[$Hcasn_meta $Hcasn_inv' $Hgid $Hlstatus_lb] HΦ").
        { rewrite lookup_ge_None // in Hdescrs_lookup. }
    }

    { iIntros "%casn %η %i %descr %casn1 %η1 %i1 %descr1 %casns1 %𝑟𝑒𝑡𝑟𝑦 %𝑐𝑜𝑛𝑡𝑖𝑛𝑢𝑒 !> %Φ (-> & -> & %Hdescrs_lookup & %Hdescrs1_lookup & %Hloc1 & %Hmeta1 & %Hcasn1 & #Hcasn_meta & #Hcasn_inv' & #Hlstatus_lb & #Hcasn1_meta & #Hcasn1_inv' & #Hlstatus1_lb & #Hhistory_lb1 & H) HΦ".
      iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".
      iDestruct (casn۰inv'ｰunfold with "Hcasn1_inv'") as "(:casn۰inv =1)".
      iDestruct (big_sepL_lookup with "Hlocs") as "(Hloc_meta & Hstate_casn & Hloc_inv')"; first done.
      iDestruct (loc۰inv'ｰelim with "Hloc_meta Hloc_inv'") as "Hloc_inv".
      iDestruct (big_sepL_lookup with "Hlocs1") as "(_ & Hstate1_casn & _)"; first done.

      wp۰rec. wp۰pures.

      iDestruct "H" as "[#Hlstatus_lb_finished | %Hfinal1]".

      - wp۰apply (statusｰspecｰfinished with "[$Hcasn_inv' $Hlstatus_lb_finished]") as "_".
        rewrite /metadata۰final. destruct (metadata۰success η); iSteps.

      - wp۰bind (_.{status})%E.
        iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
        wp۰load.
        destruct lstatus as [j |].

        + iDestruct "Hlstatus" as "(:casn۰inv۰inner۰running)".

          iInv "Hloc_inv" as "(:loc۰inv۰inner > =2)".
          destruct_decide (casn1 = casn2) as <- | Hcasn2.

          * iDestruct (history۰lbｰget with "Hhistory_auth") as "#Hhistory_lb2".
            iDestruct (historyｰrunning with "Hhistory_auth Hcasn_meta Hlstatus_auth") as %?.
            iSplitL "Hloc Hlock2 Hhistory_auth". { iFrameSteps. }
            iModIntro.

            iSplitR "HΦ". { iFrameSteps 2. }
            iModIntro. clear j helpers.

            wp۰pures.

            wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
            iInv "Hloc_inv" as "(:loc۰inv۰inner > =3)".
            wp۰cas as _ | [= Hcas].

            -- iSplitR "HΦ". { iFrameSteps. }
               iModIntro.

               wp۰apply+ ("IHdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb] HΦ").
               { iPureIntro.
                 erewrite (drop_S _ _ i); first done.
                 rewrite list_lookup_fmap Hdescrs_lookup //.
               }

            -- iDestruct (casn۰inv'ｰunfold with "Hcasn3_inv'") as "(:casn۰inv =3)".
               iDestruct (big_sepL_lookup with "Hlocs3") as "(_ & Hstate3_casn & _)"; first done.
               rewrite Hcas.
               iDestruct (pointstoｰagree with "Hstate1_casn Hstate3_casn") as %[= <-].
               iDestruct (metaｰagree with "Hcasn1_meta Hcasn3_meta") as %<-. iClear "Hcasn3_meta Hcasn3_inv' Hlstatus3_lb".
               assert (i3 = i1) as ->.
               { eapply NoDup_lookup.
                 - apply Hlocs1.
                 - rewrite list_lookup_fmap Hdescrs3_lookup //.
                 - rewrite list_lookup_fmap Hdescrs1_lookup /=. congruence.
               }
               simp.

               iInv "Hcasn1_inv" as "(:casn۰inv۰inner =1)".
               iDestruct (lstatusｰfinished with "Hlstatus1_auth Hlstatus1_lb") as %->.
               iDestruct "Hlstatus1" as "(:casn۰inv۰inner۰finished > =1)".
               iDestruct (big_sepL_lookup_acc with "Hdescrs1") as "(([Hmodel₂ | Hlock1] & Hdescr1) & Hdescrs1)"; first done; last first.
               { iDestruct (lockｰexclusive with "Hlock3 Hlock1") as %[]. }

               iDestruct ("Hdescrs1" with "[$Hlock3 $Hdescr1]") as "Hdescrs1".
               iSplitR "Hloc Hhistory_auth Hmodel₂ HΦ". { iFrameSteps 2. }
               iModIntro. clear helpers1 prophs1.

               iEval (rewrite Hmeta1) in "Hmodel₂".
               iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
               destruct lstatus as [j |].

               ++ iDestruct "Hlstatus" as "(:casn۰inv۰inner۰running >)".

                  iAssert ⌜j = i⌝%I as %->.
                  { destruct (Nat.lt_trichotomy j i) as [? | [-> | ?]].
                    - iDestruct (lstatusｰle with "Hlstatus_auth Hlstatus_lb") as %?. lia.
                    - iSteps.
                    - iDestruct (big_sepL_lookup with "Hmodels₂") as "(_Hmodel₂ & _)".
                      { apply lookup_take_Some. done. }
                      iDestruct (model₂ｰexclusive with "Hmodel₂ _Hmodel₂") as %[].
                  }

                  iMod (historyｰupdateｰrunning casn with "Hhistory_auth Hcasn1_meta Hlstatus1_lb Hcasn_meta Hlstatus_auth") as "(Hhistory_auth & #Hhistory_elem & Hlstatus_auth)"; first done.
                  iMod (lstatusｰupdate (Running ˖i) with "Hlstatus_auth") as "Hlstatus_auth"; first done.
                  iClear "Hlstatus_lb". iDestruct (lstatus۰lbｰget with "Hlstatus_auth") as "#Hlstatus_lb".
                  iApply model₂ｰsimilar in "Hmodel₂"; first done.
                  iDestruct (big_sepLｰsnoc₂ with "Hmodels₂ [$Hmodel₂ $Hhistory_elem]") as "Hmodels₂".
                  iEval (rewrite -take_S_r //) in "Hmodels₂".
                  rewrite -(Nat.succ_pred_pos (metadata۰size η - i)).
                  { apply lookup_lt_Some in Hdescrs_lookup.
                    rewrite /metadata۰size. lia.
                  }
                  iDestruct (big_sepLｰseqｰcons₁ with "Hlocks") as "(Hlock & Hlocks)".
                  assert (Nat.pred (metadata۰size η - i) = metadata۰size η - ˖i) as -> by lia.
                  iSplitR "Hloc Hhistory_auth Hlock HΦ".
                  { iFrameSteps 2. do 2 iModIntro.
                    iApply (big_sepM_impl with "Hhelpers").
                    iSteps.
                  }
                  iModIntro. clear helpers.

                  iSplitR "HΦ". { iFrameSteps. }
                  iModIntro.

                  wp۰apply+ ("IHdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //] HΦ").

               ++ iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
                  iDestruct (history۰lbｰvalidｰeq with "Hhistory_auth Hhistory_lb2") as %(-> & _).
                  destruct (metadata۰success η) eqn:Hsuccess.

                  ** iDestruct (big_sepL_lookup with "Hdescrs") as "(_ & Hhistory_elem & _)"; first done.
                     iDestruct (history۰elemｰvalid with "Hhistory_auth Hhistory_elem") as %[| ?%list_elem_of_singleton]%elem_of_app.
                     all: exfalso; done.

                  ** iDestruct (big_sepL_lookup_acc with "Hdescrs") as "(([Hmodel₂_ | Hlock] & Hdescr) & Hdescrs)"; first done.
                     { iDestruct (model₂ｰexclusive with "Hmodel₂ Hmodel₂_") as %[]. }
                       iApply (model₂ｰsimilar (descriptor۰final descr η)) in "Hmodel₂".
                       { rewrite {2}/descriptor۰final Hsuccess //. }
                       iDestruct ("Hdescrs" with "[$Hmodel₂ $Hdescr]") as "Hdescrs".
                       iClear "Hlstatus_lb". iDestruct (lstatus۰lbｰgetｰfinished (Running ˖i) with "Hlstatus_auth") as "#Hlstatus_lb".
                       iSplitR "Hloc Hhistory_auth Hlock HΦ". { rewrite /casn۰inv۰inner Hsuccess. iFrameSteps 2. }
                       iModIntro. clear helpers prophs.

                       iMod (historyｰupdate with "Hhistory_auth Hcasn1_meta Hlstatus1_lb") as "(Hhistory_auth & _)"; [done.. |].
                       iSplitR "HΦ". { iFrameSteps. }
                       iModIntro.

                       wp۰apply+ ("IHdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //]").
                       rewrite Hsuccess. iSteps.

          * iDestruct (history۰lbｰvalidｰne with "Hhistory_auth Hhistory_lb1") as "(%casns & #Hhistory_lb2)"; first done.
            iSplitL "Hloc Hlock2 Hhistory_auth". { iFrameSteps. }
            iModIntro.

            iSplitR "HΦ". { iFrameSteps 2. }
            iModIntro. clear j helpers.

            wp۰pures.

            wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
            iInv "Hloc_inv" as "(:loc۰inv۰inner > =3)".
            wp۰cas as _ | [= Hcas].

            -- iSplitR "HΦ". { iFrameSteps. }
               iModIntro.

               wp۰apply+ ("IHdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb] HΦ").
               { iPureIntro.
                 erewrite (drop_S _ _ i); first done.
                 rewrite list_lookup_fmap Hdescrs_lookup //.
               }

            -- iDestruct (casn۰inv'ｰunfold with "Hcasn3_inv'") as "(:casn۰inv =3)".
               iDestruct (big_sepL_lookup with "Hlocs3") as "(_ & Hstate3_casn & _)"; first done.
               rewrite Hcas.
               iDestruct (pointstoｰagree with "Hstate1_casn Hstate3_casn") as %[= <-].
               iDestruct (history۰lbｰvalidｰeq with "Hhistory_auth Hhistory_lb2") as %(_ & (_ & [=])%app_nil).

        + iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished)".
          iClear "Hlstatus_lb". iDestruct (lstatus۰lbｰget with "Hlstatus_auth") as "#Hlstatus_lb".
          iSplitR "HΦ". { iFrameSteps 2. }
          iModIntro. clear helpers prophs.

          rewrite /metadata۰final. destruct (metadata۰success η); iSteps.
    }

    { iIntros "%casn %η %i %descr !> %Φ (%Hdescrs_lookup & #Hcasn_meta & #Hcasn_inv') HΦ".
      iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".
      iDestruct (big_sepL_lookup with "Hlocs") as "(_ & #Hstate_casn & _)"; first done.

      wp۰rec credit:"H£". wp۰load.
      wp۰apply ("IHdetermine" with "[$Hcasn_meta $Hcasn_inv']") as "#Hlstatus_lb".
      destruct (metadata۰success η) eqn:Hsuccess; wp۰pures.

      - wp۰apply (afterｰspecｰfinished with "[$Hcasn_inv' $Hlstatus_lb]"); [done.. |].
        rewrite /descriptor۰final Hsuccess. iSteps.

      - wp۰apply (beforeｰspecｰfinished with "[$Hcasn_inv' $Hlstatus_lb]"); [done.. |].
        rewrite /descriptor۰final Hsuccess. iSteps.
    }

    { iIntros "%casn %η !> %Φ (#Hcasn_meta & #Hcasn_inv') HΦ".
      iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".

      wp۰rec.

      wp۰bind ((#casn).{status})%E.
      iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
      wp۰load.
      destruct lstatus as [i |].

      - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰running)".
        iDestruct (lstatus۰lbｰgetｰrunning0 with "Hlstatus_auth") as "#Hlstatus_lb".
        iSplitR "HΦ". { iFrameSteps 2. }
        iModIntro. clear.

        wp۰apply+ ("IHdetermine_as" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //]").
        iSteps.

      - iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished)".
        iDestruct (lstatus۰lbｰget with "Hlstatus_auth") as "#Hlstatus_lb".
        iSplitR "HΦ". { iFrameSteps 2. }
        iModIntro. clear.

        rewrite /metadata۰final. destruct (metadata۰success η); iSteps.
    }
  Qed.
  #[local] Lemma mcas_1٠determine_asｰspec casn η ι 𝑐𝑎𝑠𝑠 i :
    𝑐𝑎𝑠𝑠 = list۰to_val (drop i (metadata۰cass η)) →
    {{{
      casn ↪ η ∗
      casn۰inv' ι casn η ∗
      lstatus۰lb η (Running i)
    }}}
      mcas_1٠determine_as #casn 𝑐𝑎𝑠𝑠
    {{{
      RET #(metadata۰success η);
      lstatus۰lb η Finished
    }}}.
  Proof.
    iDestruct mcas_1٠determine_asｰevalｰdetermineｰspec as "(H & _)".
    iIntros (->) "%Φ (#Hcasn_meta & #Hcasn_inv' & #Hlstatus_lb) HΦ".
    wp۰apply ("H" with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb //] HΦ").
  Qed.
  #[local] Lemma mcas_1٠evalｰspec {casn η ι} i descr :
    η.(metadata۰descrs) !! i = Some descr →
    {{{
      casn ↪ η ∗
      casn۰inv' ι casn η
    }}}
      mcas_1٠eval #descr.(descriptor۰state)
    {{{
      RET descriptor۰final descr η;
      lstatus۰lb η Finished ∗
      £ 1
    }}}.
  Proof.
    iDestruct mcas_1٠determine_asｰevalｰdetermineｰspec as "(_ & _ & H & _)".
    iIntros "%Hdescrs_lookup %Φ (#Hcasn_meta & #Hcasn_inv') HΦ".
    wp۰apply ("H" with "[$Hcasn_meta $Hcasn_inv' //] HΦ").
  Qed.
  #[local] Lemma mcas_1٠determineｰspec casn η ι :
    {{{
      casn ↪ η ∗
      casn۰inv' ι casn η
    }}}
      mcas_1٠determine #casn
    {{{
      RET #(metadata۰success η);
      lstatus۰lb η Finished
    }}}.
  Proof.
    iDestruct mcas_1٠determine_asｰevalｰdetermineｰspec as "(_ & _ & H)".
    iIntros "%Φ (#Hcasn_meta & #Hcasn_inv') HΦ".
    wp۰apply ("H" with "[$Hcasn_meta $Hcasn_inv' //] HΦ").
  Qed.

  Lemma mcas_1٠makeｰspec ι v :
    {{{
      True
    }}}
      mcas_1٠make v
    {{{
      loc
    , RET #loc;
      mcas_1۰loc۰inv loc ι ∗
      mcas_1۰loc۰model loc v
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply (wpｰid with "[//]") as (gid) "Hgid".
    wp۰apply+ (prophet_typedｰwpｰproph global_prophet with "[//]") as (pid prophs) "Hgproph".
    wp۰block casn as "Hcasn_meta" "(Hcasn_status & Hcasn_proph & _)".
    iMod (pointstoｰpersist with "Hcasn_proph") as "#Hcasn_proph".
    wp۰block state as "(Hstate_casn & Hstate_before & Hstate_after & _)".
    iMod (pointstoｰpersist with "Hstate_casn") as "#Hstate_casn".
    wp۰ref loc as "Hloc_meta" "Hloc".

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod historyｰalloc as "(%γ_history & Hhistory_auth & #Hhistory_elem)".

    pose γ :=
      {|loc۰metadata۰model := γ_model
      ; loc۰metadata۰history := γ_history
      |}.
    iMod (metaｰset γ with "Hloc_meta") as "#Hloc_meta"; first done.

    iMod (saved_predｰalloc (λ _, True)%I) as "(%η_post & #Hpost)".
    iMod (lstatusｰalloc Finished) as "(%η_lstatus & Hlstatus_auth)".
    iMod lockｰalloc as "(%η_lock & Hlock)".
    iMod helpersｰalloc as "(%η_helpers & Hhelpers_auth)".
    iMod ownerｰalloc as "(%η_owner & Howner)".

    pose descr :=
      {|descriptor۰loc := loc
      ; descriptor۰meta := γ
      ; descriptor۰before := v
      ; descriptor۰after := v
      ; descriptor۰state := state
      |}.
    set η :=
      {|metadata۰descrs := [descr]
      ; metadata۰prophet := pid
      ; metadata۰prophs := ((gid, true) :: prophs)
      ; metadata۰undetermined := inhabitant
      ; metadata۰post := η_post
      ; metadata۰lstatus := η_lstatus
      ; metadata۰locks := [η_lock]
      ; metadata۰helpers := η_helpers
      ; metadata۰winning := inhabitant
      ; metadata۰owner := η_owner
      |}.
    iMod (metaｰset η with "Hcasn_meta") as "#Hcasn_meta"; first done.

    iDestruct (lstatus۰lbｰgetｰfinished (η := η) (Running 1) with "Hlstatus_auth") as "#Hlstatus_lb".

    iMod (inv_alloc _ _ (casn۰inv۰inner casn η ι (λ _, True)%I) with "[Hgid Hgproph Hcasn_status Hstate_before Hstate_after Hmodel₂ Hlstatus_auth Hhelpers_auth Howner]") as "#Hcasn_inv".
    { iExists §After%V, Finished, ∅.
      setoid_rewrite big_sepM_empty. iSteps.
    }

    iAssert (|={⊤}=> loc۰inv' ι (loc, γ))%I with "[Hloc Hlock Hhistory_auth]" as ">#Hloc_inv'".
    { iApply loc۰inv'ｰintro.
      iApply inv_alloc.
      iExists [], casn, η, 0, descr.
      setoid_rewrite <- (fixpoint_A_unfold (casn۰inv۰pre ι) (loc۰inv۰pre ι) _).
      iSteps; iPureIntro; apply NoDup_singleton.
    }

    iDestruct (casn۰inv'ｰunfold with "[$Hcasn_inv]") as "#Hcasn_inv'".
    { iSteps. iPureIntro. apply NoDup_singleton. }

    iSteps.
  Qed.

  Lemma mcas_1٠getｰspec loc ι :
    <<<
      mcas_1۰loc۰inv loc ι
    | ∀∀ v,
      mcas_1۰loc۰model loc v
    >>>
      mcas_1٠get #loc @ ↑ι
    <<<
      mcas_1۰loc۰model loc v
    | w,
      RET w;
      ⌜v ≈ w⌝
    >>>.
  Proof.
    iIntros "%Φ (%γ & #Hloc_meta & #Hloc_inv') HΦ".
    iDestruct (loc۰inv'ｰelim with "Hloc_meta Hloc_inv'") as "#Hloc_inv".

    wp۰rec credit:"H£1".

    wp۰bind (!_)%E.
    iInv "Hloc_inv" as "(:loc۰inv۰inner >)".
    wp۰load.
    iDestruct (casn۰inv'ｰunfold with "Hcasn_inv'") as "(:casn۰inv)".
    iDestruct (big_sepL_lookup with "Hlocs") as "(_Hloc_meta & _)"; first done.
    iDestruct (metaｰagree with "Hloc_meta _Hloc_meta") as %->. iClear "_Hloc_meta".
    iMod (casnｰhelp _ (Φ (descriptor۰final descr η)) with "Hcasn_inv Hlock [HΦ]") as "(%helper & Hlock & #Hhelper & Hhelpers_elem)"; [solve_ndisj | done.. | |].
    { rewrite /helper۰au'. iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%v (%γ & Hloc_meta_ & Hmodel₁)".
      iDestruct (metaｰagree with "Hloc_meta Hloc_meta_") as %<-. iClear "Hloc_meta_".
      iAaccIntro with "Hmodel₁"; first iSteps.
      iSteps.
    }
    iSplitR "H£1 Hhelpers_elem". { iFrameSteps. }
    iModIntro. clear Hlocs.

    iApply wpｰfupd. iClear "Hlstatus_lb".
    wp۰apply (mcas_1٠evalｰspec with "[$Hcasn_meta $Hcasn_inv']") as "(#Hlstatus_lb & H£2)"; first done.
    iMod (casnｰretrieve with "Hcasn_inv Hlstatus_lb Hhelper Hhelpers_elem") as "HΦ".
    iMod (lc_fupd_elim_later with "H£1 HΦ") as "HΦ".
    iApply (lc_fupd_elim_later with "H£2 HΦ").
  Qed.

  Lemma mcas_1٠mcasｰspec {ι 𝑠𝑝𝑒𝑐} locs befores afters :
    length locs = length befores →
    length locs = length afters →
    NoDup locs →
    list۰model' 𝑠𝑝𝑒𝑐 $ zip3_with (λ loc before after, (#loc, before, after)%V) locs befores afters →
    <<<
      [∗ list] loc ∈ locs, mcas_1۰loc۰inv loc ι
    | ∀∀ vs,
      [∗ list] loc; v ∈ locs; vs, mcas_1۰loc۰model loc v
    >>>
      mcas_1٠mcas 𝑠𝑝𝑒𝑐 @ ↑ι
    <<<
      ∃∃ b,
      if b then
        ⌜vs ≈ befores⌝ ∗
        [∗ list] loc; v ∈ locs; afters, mcas_1۰loc۰model loc v
      else
        ∃ i before v,
        ⌜befores !! i = Some before⌝ ∗
        ⌜vs !! i = Some v⌝ ∗
        ⌜v ≉ before⌝ ∗
        [∗ list] loc; v ∈ locs; vs, mcas_1۰loc۰model loc v
    | RET #b;
      True
    >>>.
  Proof.
    iIntros (? ? Hnodup ->) "%Φ Hlocs_ HΦ".
    iDestruct (big_sepLｰexists with "Hlocs_") as "(%γs & %Hγs & #Hlocs)". iClear "Hlocs_".

    wp۰rec credit:"H£".
    wp۰apply+ (prophet_typedｰwpｰproph global_prophet with "[//]") as (pid prophs0) "Hgproph".
    wp۰block casn as "Hcasn_meta" "(Hcasn_state & Hcasn_proph & _)".
    iMod (pointstoｰpersist with "Hcasn_proph") as "#Hcasn_proph".

    pose (Ψ i (_ : val) 𝑐𝑎𝑠 := (
      ∃ descr,
      ⌜𝑐𝑎𝑠 = descriptor۰cas descr⌝ ∗
      descr.(descriptor۰state).[casn] ↦□ #casn ∗
      ( descr.(descriptor۰state).[before] ↦ descr.(descriptor۰before) ∗
        descr.(descriptor۰state).[after] ↦ descr.(descriptor۰after)
      ) ∗
        ∃ γ,
        ⌜γs !! i = Some γ⌝ ∗
        ⌜ ∃ loc before after,
          locs !! i = Some loc ∧
          befores !! i = Some before ∧
          afters !! i = Some after ∧
          descr.(descriptor۰loc) = loc ∧
          descr.(descriptor۰meta) = γ ∧
          descr.(descriptor۰before) = before ∧
          descr.(descriptor۰after) = after
        ⌝
    )%I : iProp Σ).
    wp۰apply+ (list٠mapｰspecｰdisentangled Ψ with "[]") as (𝑐𝑎𝑠𝑠 𝑐𝑎𝑠s) "(%Hvs_cass & -> & Hdescrs)"; first done.
    { iIntros "!>" (i ? (loc & before & after & Hlocs_lookup & Hbefores_lookup & Hafters_lookup & ->)%lookupｰzip3_withｰSome).
      wp۰block state as "(Hstate_casn & Hstate_before & Hstate_after & _)".
      iMod (pointstoｰpersist with "Hstate_casn") as "#Hstate_casn".
      wp۰pures.
      destruct (lookup_lt_is_Some_2 γs i) as (γ & Hγs_lookup).
      { rewrite Hγs. eapply lookup_lt_Some. done. }
      pose descr :=
        {|descriptor۰loc := loc
        ; descriptor۰meta := γ
        ; descriptor۰before := before
        ; descriptor۰after := after
        ; descriptor۰state := state
        |}.
      iExists descr. iSteps.
    }
    iDestruct (big_sepL2_const_sepL_r with "Hdescrs") as "(_ & Hdescrs)".
    iDestruct (big_sepLｰexists with "Hdescrs") as "(%descrs & _ & Hdescrs)".
    iDestruct (big_sepL2_sep_sepL_r with "Hdescrs") as "(Hvs_cass & Hdescrs)".
    iDestruct (big_sepL2ｰForall2 with "Hvs_cass") as %->%listｰfmapｰaltｰForall2ｰl. iClear "Hvs_cass".
    simp_length in Hvs_cass.
    iDestruct (big_sepL_sep with "Hdescrs") as "(#Hstates_casn & Hdescrs)".
    iDestruct (big_sepL_sep with "Hdescrs") as "(Hstates & Hdescrs)".
    iApply big_sepLｰextractｰr in "Hdescrs"; first lia.
    iDestruct (big_sepL2ｰForall2i with "Hdescrs") as %Hdescrs. iClear "Hdescrs".

    assert (Hafters : afters = descriptor۰after <$> descrs).
    { apply listｰfmapｰaltｰForall2ｰl, Forall2_same_length_lookup_2; first congruence. intros.
      eapply Forall2iｰlookupｰr in Hdescrs; last done.
      naive_solver.
    }
    assert (Hbefores : befores = descriptor۰before <$> descrs).
    { apply listｰfmapｰaltｰForall2ｰl, Forall2_same_length_lookup_2; first congruence. intros.
      eapply Forall2iｰlookupｰr in Hdescrs; last done.
      naive_solver.
    }

    wp۰block۰generative undetermined.
    wp۰store.

    pose Φ' b := Φ #b.

    iMod (saved_predｰalloc Φ') as "(%η_post & #Hpost)".
    iMod (lstatusｰalloc (Running 0)) as "(%η_lstatus & Hlstatus_auth)".
    iMod (lockｰallocs (length descrs)) as "(%ηs_lock & %Hηs_lock & Hlocks)".
    iMod helpersｰalloc as "(%η_helpers & Hhelpers_auth)".
    iMod winningｰalloc as "(%η_winning & Hwinning)".
    iMod ownerｰalloc as "(%η_owner & Howner)".

    pose η :=
      {|metadata۰descrs := descrs
      ; metadata۰prophet := pid
      ; metadata۰prophs := prophs0
      ; metadata۰undetermined := undetermined
      ; metadata۰post := η_post
      ; metadata۰lstatus := η_lstatus
      ; metadata۰locks := ηs_lock
      ; metadata۰helpers := η_helpers
      ; metadata۰winning := η_winning
      ; metadata۰owner := η_owner
      |}.
    iMod (metaｰset η with "Hcasn_meta") as "#Hcasn_meta"; first done.

    iDestruct (lstatus۰lbｰget η with "Hlstatus_auth") as "#Hlstatus_lb".

    iMod (inv_alloc _ _ (casn۰inv۰inner casn η ι Φ') with "[Hgproph Hcasn_state Hlstatus_auth Hlocks Hhelpers_auth Hwinning Hstates HΦ]") as "#Hcasn_inv".
    { iExists _, (Running 0), ∅, _. iFrameStep 3.
      rewrite big_sepM_empty comm. iSteps.
      iSplitL "Hlocks".
      { iApply (big_sepLｰseqｰindex ηs_lock); first lia.
        iApply (big_sepL_impl with "Hlocks").
        iSteps.
      }
      iLeft. iFrame.
      rewrite /au. iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs Hmodels".
      iAssert (
        [∗ list] descr; v ∈ descrs; vs,
          model₁ descr.(descriptor۰meta) v
      )%I with "[Hmodels]" as "Hmodels".
      { iApply (big_sepL2ｰimplｰstrongｰl with "Hmodels"); first done. iIntros "!> %i %loc %v %descr %Hlocs_lookup %Hvs_lookup %Hdescrs_lookup (:loc۰model)".
        iDestruct (big_sepL2_lookup_l with "Hlocs") as "(%γ_ & %Hγs_lookup & Hmeta_ & _)"; first done.
        iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        odestruct Forall2iｰlookupｰr; [done.. |]. simp.
        iSteps.
      }
      iAssert (
        ( [∗ list] descr; v ∈ descrs; vs,
          model₁ descr.(descriptor۰meta) v
        ) -∗
        [∗ list] loc; v ∈ locs; vs,
          mcas_1۰loc۰model loc v
      )%I as "?".
      { iIntros "Hmodels₁".
        iApply (big_sepL2ｰimplｰstrongｰl with "Hmodels₁"); first done. iIntros "!> %i %descr %v %loc %Hdescrs_lookup %Hvs_lookup %Hlocs_lookup Hmodel₁".
        iDestruct (big_sepL2_lookup_l with "Hlocs") as "(%γ & %Hγs_lookup & Hmeta & _)"; first done.
        odestruct Forall2iｰlookupｰr; [done.. |]. simp.
        iSteps.
      }
      iAaccIntro with "Hmodels"; first iSteps. iIntros "%b H !>".
      iExists b. destruct b.
      all: iSplitL; last iSteps.
      - iDestruct "H" as "(%Hvs & Hmodels₁)".
        iSplit. { rewrite Hbefores //. }
        iApply (big_sepLｰimplｰsepL2 with "Hmodels₁"); [simpl; congruence.. |]. iIntros "!> %i %descr %loc %after %Hdescrs_lookup %Hlocs_lookup %Hafters_lookup Hmodel₁".
        iDestruct (big_sepL2_lookup_l with "Hlocs") as "(%γ & %Hγs_lookup & Hmeta & _)"; first done.
        odestruct Forall2iｰlookupｰr; [done.. |]. simp.
        iSteps.
      - iDestruct "H" as "(%i & %descr & %v & %Hdescrs_lookup & %Hvs_lookup & %Hneq & Hmodels₁)".
        odestruct Forall2iｰlookupｰr; [done.. |]. simp.
        iSteps.
    }

    iDestruct (casn۰inv'ｰunfold with "[$Hcasn_inv]") as "#Hcasn_inv'".
    { iSteps.
      - iPureIntro.
        apply NoDup_alt. intros i1 i2 loc (descr1 & -> & Hdescrs_lookup_1)%list_lookup_fmap_Some (descr2 & Heq & Hdescrs_lookup_2)%list_lookup_fmap_Some.
        odestruct (Forall2iｰlookupｰr _ _ _ i1) as (γ1 & _ & H1); [done.. |].
        destruct H1 as (loc1 & before1 & after1 & Hlocs_lookup_1 & _ & _ & -> & _) in Heq.
        odestruct (Forall2iｰlookupｰr _ _ _ i2) as (γ2 & _ & H2); [done.. |].
        destruct H2 as (loc2 & before2 & after2 & Hlocs_lookup_2 & _ & _ & -> & _) in Heq.
        eapply NoDup_lookup; [done | naive_solver..].
      - iApply (big_sepL_wand with "Hstates_casn").
        iApply (big_sepL2ｰimplｰsepL with "Hlocs"); first auto. iIntros "!> %i %loc %γ %descr %Hlocs_lookup %Hγs_lookup %Hdescrs_lookup (Hmeta & Hloc_inv)".
        odestruct Forall2iｰlookupｰr; [done.. |]. simp.
        iSteps.
    }

    iApply wpｰfupd.
    wp۰apply+ (mcas_1٠determine_asｰspec with "[$Hcasn_meta $Hcasn_inv' $Hlstatus_lb]") as "#Hlstatus_lb_finished"; first done.

    iInv "Hcasn_inv" as "(:casn۰inv۰inner)".
    iDestruct (lstatusｰfinished with "Hlstatus_auth Hlstatus_lb_finished") as %->.
    iDestruct "Hlstatus" as "(:casn۰inv۰inner۰finished >)".
    iDestruct "HΨ" as "[>Howner_ | HΨ]".
    { iDestruct (ownerｰexclusive η with "Howner Howner_") as %[]. }
    iSplitR "H£ HΨ". { iFrameSteps 2. }
    iModIntro. clear.

    iApply (lc_fupd_elim_later with "H£ HΨ").
  Qed.
End mcas_1۰G.

Require zoo_mcas.mcas_1__opaque.

#[global] Opaque mcas_1۰loc۰inv.
#[global] Opaque mcas_1۰loc۰model.
