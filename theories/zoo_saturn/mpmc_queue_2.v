From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  relations.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.auth_mono
  lib.auth_nat_max.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  prophet_bool.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  domain
  option.
From zoo_saturn Require Export
  base
  mpmc_queue_2__code.
From zoo_saturn Require Import
  mpmc_queue_2__types.
From zoo Require Import
  options.

Implicit Types strong : bool.
Implicit Types l back back_prev : location.
Implicit Types backs : gmap location nat.
Implicit Types v w t pref suff 𝑚𝑜𝑣𝑒 : val.
Implicit Types o : option val.
Implicit Types vs vs_front vs_back move : list val.

Variant emptiness :=
  | Empty
  | Nonempty.
Implicit Types empty : emptiness.

#[local] Instance emptiness_inhabited : Inhabited emptiness :=
  populate Empty.
#[local] Instance emptiness_eq_dec : EqDecision emptiness :=
  ltac:(solve_decision).

Variant status :=
  | Stable empty
  | Unstable back move.
Implicit Types status : status.

#[local] Instance status_inhabited : Inhabited status :=
  populate (Stable inhabitant).
#[local] Instance status_eq_dec : EqDecision status :=
  ltac:(solve_decision).

Record state :=
  { state_backs : gmap location nat
  ; state_index : nat
  ; state_status : status
  }.
Implicit Types state : state.

#[local] Definition state_with_status state status :=
  {|state_backs := state.(state_backs)
  ; state_index := state.(state_index)
  ; state_status := status
  |}.

Definition state_wf backs i :=
  map_Forall (λ _ i_back, i_back ≤ i) backs.

#[local] Definition state_le state1 state2 :=
  state1.(state_backs) ⊆ state2.(state_backs) ∧
  state1.(state_index) ≤ state2.(state_index).

#[local] Instance state_inhabited : Inhabited state :=
  populate
    {|state_backs := inhabitant
    ; state_index := inhabitant
    ; state_status := inhabitant
    |}.

#[local] Instance state_le_reflexive :
  Reflexive state_le.
Proof.
  done.
Qed.
#[local] Instance state_le_transitive :
  Transitive state_le.
Proof.
  intros state1 state2 state3 (? & ?) (? & ?).
  split.
  - etrans; done.
  - lia.
Qed.

Variant step : relation state :=
  | step_empty state1 state2 :
      state1.(state_status) = Stable Nonempty →
      state2 = state_with_status state1 (Stable Empty) →
      step state1 state2
  | step_destabilize state1 state2 back move :
      state1.(state_status) = Stable Empty →
      state2 = state_with_status state1 (Unstable back move) →
      step state1 state2
  | step_stabilize state1 state2 back move :
      state1.(state_status) = Unstable back move →
      state1.(state_backs) !! back = None →
      state2 =
        {|state_backs := <[back := state1.(state_index) + length move]> state1.(state_backs)
        ; state_index := state1.(state_index) + length move
        ; state_status := Stable Nonempty
        |} →
      step state1 state2.
#[local] Hint Constructors step : core.

#[local] Definition steps :=
  rtc step.

#[local] Lemma step_mono state1 state2 :
  step state1 state2 →
  state_le state1 state2.
Proof.
  intros Hstep. invert Hstep; [done.. |].
  split.
  - apply insert_subseteq. done.
  - simpl. lia.
Qed.
#[local] Lemma steps_mono state1 state2 :
  steps state1 state2 →
  state_le state1 state2.
Proof.
  intros Hsteps.
  rewrite -preorder_rtc.
  apply (rtc_congruence (R := step) id); last done.
  apply step_mono.
Qed.

Class MpmcQueue2G Σ `{zoo_G : !ZooG Σ} :=
  { #[local] mpmc_queue_2_G_model_G :: TwinsG Σ (leibnizO (list val))
  ; #[local] mpmc_queue_2_G_state_G :: AuthMonoG (A := leibnizO state) Σ step
  ; #[local] mpmc_queue_2_G_front_G :: AuthNatMaxG Σ
  }.

Definition mpmc_queue_2_Σ :=
  #[twins_Σ (leibnizO (list val))
  ; auth_mono_Σ (A := leibnizO state) step
  ; auth_nat_max_Σ
  ].
#[global] Instance subG_mpmc_queue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_queue_2_Σ Σ →
  MpmcQueue2G Σ.
Proof.
  solve_inG.
Qed.

#[local] Fixpoint suffix_to_val (i : nat) vs : val :=
  match vs with
  | [] =>
      ‘Front[ #i ]
  | v :: vs =>
      ‘Cons[ #i, v, suffix_to_val (S i) vs ]
  end.

#[local] Lemma suffix_to_val_generative i1 vs1 i2 vs2 :
  suffix_to_val i1 vs1 ≈ suffix_to_val i2 vs2 →
  suffix_to_val i1 vs1 = suffix_to_val i2 vs2.
Proof.
  destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2] => Hsimilar.
  all: zoo_simplify.
  all: congruence.
Qed.

#[local] Instance suffix_to_val_inj2 :
  Inj2 (=) (=) (=) suffix_to_val.
Proof.
  move=> + vs1. induction vs1 as [| v1 vs1 IH] => i1 i2 [| v2 vs2] Hsimilar.
  all: naive_solver.
Qed.
#[local] Instance suffix_to_val_inj2' :
  Inj2 (=) (=) (≈) suffix_to_val.
Proof.
  intros ?* Hsimilar%suffix_to_val_generative.
  apply (inj2 suffix_to_val). done.
Qed.

#[local] Fixpoint prefix_to_val (i : nat) back vs : val :=
  match vs with
  | [] =>
      #back
  | v :: vs =>
      ‘Snoc[ #⁺(i + S (length vs)), v, prefix_to_val i back vs ]
  end.

#[local] Lemma prefix_to_val_generative i1 back1 vs1 i2 back2 vs2 :
  prefix_to_val i1 back1 vs1 ≈ prefix_to_val i2 back2 vs2 →
  prefix_to_val i1 back1 vs1 = prefix_to_val i2 back2 vs2.
Proof.
  destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2] => Hsimilar.
  all: zoo_simplify.
  all: congruence.
Qed.

#[local] Lemma prefix_to_val_inj i1 back1 vs1 i2 back2 vs2 :
  prefix_to_val i1 back1 vs1 = prefix_to_val i2 back2 vs2 →
    (vs1 ≠ [] → i1 = i2) ∧
    back1 = back2 ∧
    vs1 = vs2.
Proof.
  move: i1 i2 vs2. induction vs1 as [| v1 vs1 IH] => i1 i2 [| v2 vs2] /= Hsimilar.
  all: zoo_simplify; try done.
  edestruct IH as (_ & -> & Hvs); first done.
  rewrite {}Hvs in Hsimilar |- *.
  auto with lia.
Qed.
#[local] Lemma prefix_to_val_inj' i1 back1 vs1 i2 back2 vs2 :
  prefix_to_val i1 back1 vs1 ≈ prefix_to_val i2 back2 vs2 →
    (vs1 ≠ [] → i1 = i2) ∧
    back1 = back2 ∧
    vs1 = vs2.
Proof.
  intros Hsimilar%prefix_to_val_generative.
  apply prefix_to_val_inj. done.
Qed.

Section mpmc_queue_2_G.
  Context `{mpmc_queue_2_G : MpmcQueue2G Σ}.

  Record metadata :=
    { metadata_inv : namespace
    ; metadata_model : gname
    ; metadata_state : gname
    ; metadata_front : gname
    }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata_model).
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata_model).

  #[local] Definition state_auth' γ_state backs i status : iProp Σ :=
    auth_mono_auth _ γ_state (DfracOwn 1)
      {|state_backs := backs
      ; state_index := i
      ; state_status := status
      |} ∗
    ⌜state_wf backs i⌝.
  #[local] Instance : CustomIpat "state_auth" :=
    " ( Hauth
      & %Hwf
      )
    ".
  #[local] Definition state_auth γ backs i status :=
    state_auth' γ.(metadata_state) backs i status.
  #[local] Definition state_lb γ backs i status :=
    auth_mono_lb _ γ.(metadata_state)
      {|state_backs := backs
      ; state_index := i
      ; state_status := status
      |}.
  #[local] Definition state_seen γ back i_prev back_prev move : iProp Σ :=
    ∃ backs,
    state_lb γ backs i_prev (Unstable back move) ∗
    ⌜backs !! back_prev = Some i_prev⌝.
  #[local] Instance : CustomIpat "state_seen" :=
    " ( %backs{}
      & #Hstate_lb
      & %Hbacks{}_lookup
      )
    ".
  #[local] Definition state_at γ back i_back : iProp Σ :=
    ∃ backs i status,
    state_lb γ backs i status ∗
    ⌜backs !! back = Some i_back⌝ ∗
    ⌜i_back ≤ i⌝.
  #[local] Instance : CustomIpat "state_at" :=
    " ( %backs{}
      & %i{}
      & %status{}
      & #Hstate_lb{_{}}
      & %Hbacks{}_lookup
      & %Hi{}
      )
    ".

  #[local] Definition front_auth' γ_front i :=
    auth_nat_max_auth γ_front (DfracOwn 1) i.
  #[local] Definition front_auth γ i :=
    front_auth' γ.(metadata_front) i.
  #[local] Definition front_lb γ i :=
    auth_nat_max_lb γ.(metadata_front) i.

  #[local] Definition move_model_1 𝑚𝑜𝑣𝑒 i_prev back_prev move : iProp Σ :=
      ⌜𝑚𝑜𝑣𝑒 = §Used%V⌝
    ∨ ⌜𝑚𝑜𝑣𝑒 = prefix_to_val i_prev back_prev move⌝ ∗
      ⌜0 < length move⌝ ∗
      back_prev ↦ₕ Header §Back 2.
  #[local] Instance : CustomIpat "move_model_1" :=
    " [ ->
      | ( ->
        & %
        & #Hback{}_prev_header
        )
      ]
    ".
  #[local] Definition move_model_2 γ back 𝑚𝑜𝑣𝑒 : iProp Σ :=
    ∃ backs_prev i_prev back_prev move,
    state_lb γ backs_prev i_prev (Unstable back move) ∗
    move_model_1 𝑚𝑜𝑣𝑒 i_prev back_prev move.
  #[local] Instance : CustomIpat "move_model_2" :=
    " ( %backs{}_prev
      & %i{}_prev{_{!}}
      & %back{}_prev{_{!}}
      & %move{}{_{!}}
      & #Hstate_lb_unstable{_{}}
      & H𝑚𝑜𝑣𝑒{}
      )
    ".

  #[local] Definition back_model_1 back (i : nat) : iProp Σ :=
    back ↦ₕ Header §Back 2 ∗
    back.[index] ↦□ #i.
  #[local] Instance : CustomIpat "back_model_1" :=
    " ( { {!} _
        ; #Hback{}_header
        ; #Hback_header
        }
      & #Hback{}_index{_{!}}
      )
    ".
  #[local] Definition back_model_2 back (i : nat) 𝑚𝑜𝑣𝑒 : iProp Σ :=
    back_model_1 back i ∗
    back.[move] ↦ 𝑚𝑜𝑣𝑒.
  #[local] Instance : CustomIpat "back_model_2" :=
    " ( { {only_move} _
        ; (:back_model_1 // /!/)
        }
      & Hback{}_move{_{suff}}
      )
    ".
  #[local] Definition back_model_3 γ back i : iProp Σ :=
    ∃ 𝑚𝑜𝑣𝑒,
    back_model_2 back i 𝑚𝑜𝑣𝑒 ∗
    move_model_2 γ back 𝑚𝑜𝑣𝑒.
  #[local] Instance : CustomIpat "back_model_3" :=
    " ( %𝑚𝑜𝑣𝑒{}
      & (:back_model_2)
      & H𝑚𝑜𝑣𝑒{}
      )
    ".

  #[local] Definition inv_status_stable γ i vs_front i_back back vs_back vs empty : iProp Σ :=
    ⌜i_back = i⌝ ∗
    ⌜vs = vs_front ++ reverse vs_back⌝ ∗
    ⌜if empty then vs_front = [] else 0 < length vs_front⌝ ∗
    state_at γ back i_back.
  #[local] Instance : CustomIpat "inv_status_stable" :=
    " ( {>;}->
      & {>;}%Hvs{}
      & {>;}{{empty}->;%Hempty{};%Hempty}
      & {>;}#Hstate_at{_{}}
      )
    ".
  #[local] Definition inv_status_unstable strong γ backs i vs_front i_back back vs_back vs back_ move : iProp Σ :=
    ∃ back_prev,
    ⌜back_ = back⌝ ∗
    ⌜i_back = (i + length move)%nat⌝ ∗
    ⌜vs_front = []⌝ ∗
    ⌜vs_back = []⌝ ∗
    ⌜vs = reverse move⌝ ∗
    ⌜0 < length move⌝ ∗
    state_at γ back_prev i ∗
    back_model_2 back i_back (prefix_to_val i back_prev move) ∗
    if strong then
      ⌜backs !! back = None⌝ ∗
      back_prev ↦ₕ Header §Back 2
    else
      True.
  #[local] Instance : CustomIpat "inv_status_unstable" :=
    " ( %back{}_prev
      & {>;}->
      & {>;}->
      & {>;}{{lazy}%Hvs_front{};->}
      & {>;}{{lazy}%Hvs_back{};->}
      & {>;}->
      & {>;}%
      & {>;}#Hstate_at_back{}_prev
      & Hback{}
      & { {strong}
            %Hbacks{}_lookup
          & #Hback{}_prev_header
        ; _
        }
      )
    ".
  #[local] Definition inv_status strong γ backs i status vs_front i_back back vs_back vs : iProp Σ :=
    match status with
    | Stable empty =>
        inv_status_stable γ i vs_front i_back back vs_back vs empty
    | Unstable back_ move =>
        inv_status_unstable strong γ backs i vs_front i_back back vs_back vs back_ move
    end.

  #[local] Definition inv_inner strong l γ : iProp Σ :=
    ∃ backs i status i_front vs_front i_back back vs_back vs,
    l.[front] ↦ suffix_to_val i_front vs_front ∗
    front_auth γ i_front ∗
    l.[back] ↦ prefix_to_val i_back back vs_back ∗
    ([∗ map] back ↦ i ∈ backs, back_model_3 γ back i) ∗
    model₂ γ vs ∗
    state_auth γ backs i status ∗
    ⌜(i_front + length vs_front)%nat = S i⌝ ∗
    inv_status strong γ backs i status vs_front i_back back vs_back vs.
  #[local] Instance : CustomIpat "inv_inner" :=
    " ( %backs{}
      & %i{}
      & %status{}
      & %i_front{}
      & %vs_front{}
      & %i_back{}
      & %back{}
      & %vs_back{}
      & %vs{}
      & Hl_front
      & {>;}Hfront_auth
      & Hl_back
      & Hbacks
      & Hmodel₂
      & {>;}Hstate_auth
      & {>;}%Hfront{}
      & Hstatus
      )
    ".
  #[local] Definition inv' l γ : iProp Σ :=
    inv γ.(metadata_inv) (inv_inner false l γ).
  Definition mpmc_queue_2_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata_inv)⌝ ∗
    meta l nroot γ ∗
    inv' l γ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l
      & %γ
      & ->
      & ->
      & #Hmeta
      & #Hinv
      )
    ".

  Definition mpmc_queue_2_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & Hmodel₁{_{}}
      )
    ".

  #[local] Instance state_auth_timeless γ backs i status :
    Timeless (state_auth γ backs i status).
  Proof.
    apply _.
  Qed.
  #[local] Instance state_at_timeless γ back i_back :
    Timeless (state_at γ back i_back).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_queue_2_model_timeless t vs :
    Timeless (mpmc_queue_2_model t vs).
  Proof.
    apply _.
  Qed.

  #[local] Instance state_at_persistent γ back i_back :
    Persistent (state_at γ back i_back).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_queue_2_inv_persistent t ι :
    Persistent (mpmc_queue_2_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma model₁_exclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins_twin1_exclusive.
  Qed.
  #[local] Lemma model_agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma model_update {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twins_update.
  Qed.

  #[local] Lemma state_alloc back :
    ⊢ |==>
      ∃ γ_state,
      state_auth' γ_state ∅ 0 (Unstable back []).
  Proof.
    set state :=
      {|state_backs := ∅
      ; state_index := 0
      ; state_status := Unstable back []
      |}.
    iMod (auth_mono_alloc _ (auth_mono_G := mpmc_queue_2_G_state_G) state) as "(%γ_state & $)".
    iSteps.
  Qed.
  #[local] Lemma state_auth_wf γ backs i status :
    state_auth γ backs i status ⊢
    ⌜state_wf backs i⌝.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma state_lb_get γ backs i status :
    state_auth γ backs i status ⊢
    state_lb γ backs i status.
  Proof.
    iIntros "(:state_auth)".
    iApply (auth_mono_lb_get with "Hauth").
  Qed.
  #[local] Lemma state_at_get {γ backs i status} back i_back :
    backs !! back = Some i_back →
    state_auth γ backs i status ⊢
    state_at γ back i_back.
  Proof.
    iIntros "%Hbacks_lookup (:state_auth)".
    iDestruct (state_lb_get with "[$Hauth //]") as "#Hlb".
    iSteps.
  Qed.
  #[local] Lemma state_lb_valid γ backs1 i1 status1 backs2 i2 status2 :
    state_auth γ backs1 i1 status1 -∗
    state_lb γ backs2 i2 status2 -∗
      ⌜backs2 ⊆ backs1⌝ ∗
      ⌜i2 ≤ i1⌝.
  Proof.
    iIntros "(:state_auth) Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %(? & ?)%steps_mono. done.
  Qed.
  #[local] Lemma state_lb_valid_Unstable γ backs1 i1 status1 backs2 i2 back2 move2 :
    state_auth γ backs1 i1 status1 -∗
    state_lb γ backs2 i2 (Unstable back2 move2) -∗
        ⌜backs1 = backs2⌝ ∗
        ⌜i1 = i2⌝ ∗
        ⌜status1 = Unstable back2 move2⌝
      ∨ ⌜backs1 !! back2 = Some (i2 + length move2)%nat⌝ ∗
        ⌜i2 + length move2 ≤ i1⌝ ∗
        state_at γ back2 (i2 + length move2).
  Proof.
    iIntros "(:state_auth) Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %[| (state & Hstep & (? & ?)%steps_mono)]%rtc_inv.
    - naive_solver.
    - invert Hstep.
      assert (backs1 !! back = Some (i2 + length move)) as backs1_lookup.
      { eapply lookup_weaken; last done.
        apply lookup_insert_eq.
      }
      iDestruct (state_at_get with "[$Hauth //]") as "Hstate_at"; first done.
      iRight. iSteps.
  Qed.
  #[local] Lemma state_lb_lookup {γ backs1 i1 status1 backs2 i2 status2} back i_back  :
    backs2 !! back = Some i_back →
    state_auth γ backs1 i1 status1 -∗
    state_lb γ backs2 i2 status2 -∗
    ⌜backs1 !! back = Some i_back⌝.
  Proof.
    iIntros "%Hbacks2_lookup Hauth Hlb".
    iDestruct (state_lb_valid with "Hauth Hlb") as %(? & _).
    iPureIntro. eapply lookup_weaken; done.
  Qed.
  #[local] Lemma state_seen_valid γ backs i status back i_prev back_prev move :
    state_auth γ backs i status -∗
    state_seen γ back i_prev back_prev move -∗
      ⌜backs !! back_prev = Some i_prev⌝ ∗
      ( ⌜i = i_prev⌝ ∗
        ⌜status = Unstable back move⌝
      ∨ ⌜backs !! back = Some (i_prev + length move)%nat⌝ ∗
        ⌜i_prev + length move ≤ i⌝ ∗
        state_at γ back (i_prev + length move)
      ).
  Proof.
    iIntros "Hstate_auth (:state_seen =1)".
    iDestruct (state_lb_lookup  with "Hstate_auth Hstate_lb") as %Hbacks_lookup; first done.
    iDestruct (state_lb_valid_Unstable with "Hstate_auth Hstate_lb") as "[(<- & -> & ->) | $]".
    all: iSteps.
  Qed.
  #[local] Lemma state_at_valid γ backs i status back i_back :
    state_auth γ backs i status -∗
    state_at γ back i_back -∗
      ⌜backs !! back = Some i_back⌝ ∗
      ⌜i_back ≤ i⌝.
  Proof.
    iIntros "Hstate_auth (:state_at =1)".
    iDestruct (state_lb_lookup with "Hstate_auth Hstate_lb_1") as %Hbacks_lookup; first done.
    iDestruct (state_lb_valid with "Hstate_auth Hstate_lb_1") as "(_ & %Hi)".
    iSteps.
  Qed.
  (* #[local] Lemma state_seen_at_agree γ backs i status back i_prev back_prev1 move back_prev2 : *)
  (*   state_auth γ backs i status -∗ *)
  (*   state_seen γ back i_prev back_prev1 move -∗ *)
  (*   state_at γ back_prev2 i_prev -∗ *)
  (*   ⌜back_prev1 = back_prev2⌝. *)
  (* Proof. *)
  (*   iIntros "Hstate_auth Hstate_seen Hstate_at". *)
  (*   iDestruct (state_auth_wf with "Hstate_auth") as %Hwf. *)
  (*   iDestruct (state_seen_valid with "Hstate_auth Hstate_seen") as "#(%Hbacks_lookup_1 & _)". *)
  (*   iDestruct (state_at_valid with "Hstate_auth Hstate_at") as "#(%Hbacks_lookup_2 & _)". *)
  (*   iPureIntro. eapply state_wf_inj; done. *)
  (* Qed. *)
  #[local] Lemma state_lb_stabilized γ backs1 i1 status1 backs2 i2 back2 move2 :
    ( status1 ≠ Unstable back2 move2
    ∨ i2 + length move2 ≤ i1 ∧
      0 < length move2
    ) →
    state_auth γ backs1 i1 status1 -∗
    state_lb γ backs2 i2 (Unstable back2 move2) -∗
      ⌜backs1 !! back2 = Some (i2 + length move2)%nat⌝ ∗
      state_at γ back2 (i2 + length move2).
  Proof.
    iIntros "% Hauth Hlb".
    iDestruct (state_lb_valid_Unstable with "Hauth Hlb") as "[(-> & -> & ->) | ($ & _ & $)]".
    exfalso. naive_solver lia.
  Qed.
  #[local] Lemma state_lb_unstabilized γ backs1 i1 status1 backs2 i2 back2 move2 :
    i1 < i2 + length move2 →
    state_auth γ backs1 i1 status1 -∗
    state_lb γ backs2 i2 (Unstable back2 move2) -∗
      ⌜backs1 = backs2⌝ ∗
      ⌜i1 = i2⌝ ∗
      ⌜status1 = Unstable back2 move2⌝.
  Proof.
    iIntros "% Hauth Hlb".
    iDestruct (state_lb_valid_Unstable with "Hauth Hlb") as "[(-> & -> & ->) | (_ & % & _)]"; first iSteps.
    exfalso. lia.
  Qed.
  #[local] Lemma state_stabilize γ backs i back move :
    backs !! back = None →
    state_auth γ backs i (Unstable back move) ⊢ |==>
      state_auth γ (<[back := i + length move]> backs) (i + length move) (Stable Nonempty) ∗
      state_lb γ (<[back := i + length move]> backs) (i + length move) (Stable Nonempty) ∗
      state_at γ back (i + length move).
  Proof.
    iIntros "%Hbacks_lookup (:state_auth)".

    iMod (auth_mono_update' with "Hauth") as "Hauth"; first eauto. simpl.

    set i' := i + length move.
    set backs' := <[back := i']> backs.

    assert (state_wf backs' i') as Hwf'.
    { apply map_Forall_insert; first done.
      split; first done.
      eapply map_Forall_impl; first apply Hwf.
      naive_solver lia.
    }

    iDestruct (state_lb_get with "[$Hauth //]") as "#Hstate_lb".
    iDestruct (state_at_get back with "[$Hauth //]") as "#Hat".
    { apply lookup_insert_eq. }
    iFrame "#∗". iSteps.
  Qed.
  #[local] Lemma state_empty γ backs i :
    state_auth γ backs i (Stable Nonempty) ⊢ |==>
    state_auth γ backs i (Stable Empty).
  Proof.
    iIntros "(:state_auth)".
    iMod (auth_mono_update' with "Hauth") as "$"; first auto.
    iSteps.
  Qed.
  #[local] Lemma state_destabilize {γ backs i} back move :
    state_auth γ backs i (Stable Empty) ⊢ |==>
    state_auth γ backs i (Unstable back move).
  Proof.
    iIntros "(:state_auth)".
    iMod (auth_mono_update' with "Hauth") as "$"; first eauto.
    iSteps.
  Qed.

  #[local] Lemma front_alloc :
    ⊢ |==>
      ∃ γ_front,
      front_auth' γ_front 1.
  Proof.
    apply auth_nat_max_alloc.
  Qed.
  #[local] Lemma front_lb_get γ i :
    front_auth γ i ⊢
    front_lb γ i.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma front_lb_valid γ i1 i2 :
    front_auth γ i1 -∗
    front_lb γ i2 -∗
    ⌜i2 ≤ i1⌝.
  Proof.
    apply auth_nat_max_lb_valid.
  Qed.
  #[local] Lemma front_update γ i :
    front_auth γ i ⊢ |==>
    front_auth γ (S i).
  Proof.
    apply auth_nat_max_update. lia.
  Qed.

  Opaque state_auth.
  Opaque state_at.

  #[local] Lemma inv_status_weaken γ backs i status vs_front i_back back vs_back vs :
    inv_status true γ backs i status vs_front i_back back vs_back vs ⊢
    inv_status false γ backs i status vs_front i_back back vs_back vs.
  Proof.
    destruct status as [empty | back_ move]; iSteps.
  Qed.
  #[local] Lemma inv_status_Stable strong γ backs i status vs_front i_back back vs_back vs :
    ( strong = true ∧ is_Some (backs !! back)
    ∨ 0 < length vs_front
    ∨ 0 < length vs_back
    ) →
    inv_status strong γ backs i status vs_front i_back back vs_back vs ⊢
      ∃ empty,
      ⌜status = Stable empty⌝ ∗
      inv_status_stable γ i vs_front i_back back vs_back vs empty.
  Proof.
    iIntros "%H H".
    destruct status as [empty | back_ move].
    - iDestruct "H" as "(:inv_status_stable)".
      iSteps.
    - destruct H as [(-> & i_back_ & Hbacks_lookup) |].
      + iDestruct "H" as "(:inv_status_unstable =1 strong=)".
        congruence.
      + iDestruct "H" as "(:inv_status_unstable)".
        simpl in *. lia.
  Qed.

  #[local] Lemma inv_inner_strengthen l γ :
    inv_inner false l γ ⊢
    inv_inner true l γ.
  Proof.
    iIntros "(:inv_inner)".
    destruct status as [empty | back_ move].

    - iDestruct "Hstatus" as "(:inv_status_stable)".
      iFrameSteps.

    - iDestruct "Hstatus" as "(:inv_status_unstable)".

      iAssert ⌜backs !! back = None⌝%I as %Hbacks_lookup.
      { rewrite -eq_None_ne_Some.
        iIntros "%i_back %Hbacks_lookup".
        iDestruct (big_sepM_lookup with "Hbacks") as "(:back_model_3 only_move=)"; first done.
        iDestruct "Hback" as "(:back_model_2 suff=)".
        iApply (pointsto_exclusive with "Hback_move Hback_move_").
      }

      iAssert (back_prev ↦ₕ Header §Back 2)%I as "#Hback_prev_header".
      { iDestruct (state_at_valid with "Hstate_auth Hstate_at_back_prev") as %(Hbacks_lookup_prev & _).
        iDestruct (big_sepM_lookup with "Hbacks") as "(:back_model_3 =_prev)"; first done.
        iFrame "#".
      }

      iFrameSteps.
  Qed.

  #[local] Lemma inv'_state_at {l γ} back i_back :
    inv' l γ -∗
    state_at γ back i_back ={⊤}=∗
    back_model_1 back i_back.
  Proof.
    iIntros "#Hinv #Hstate_at".

    iInv "Hinv" as "(:inv_inner =1 >)".

    iAssert (▷ back_model_1 back i_back)%I as "#>$".
    { iDestruct (state_at_valid with "Hstate_auth Hstate_at") as %(Hbacks_lookup & _).
      iDestruct (big_sepM_lookup with "Hbacks") as "(:back_model_3)".
      { eapply lookup_weaken; done. }
      iFrame "#".
    }

    iFrameSteps.
  Qed.

  Lemma mpmc_queue_2_model_exclusive t vs1 vs2 :
    mpmc_queue_2_model t vs1 -∗
    mpmc_queue_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  #[local] Lemma mpmc_queue_2_suffix_index𑁒spec (i : nat) vs :
    {{{
      True
    }}}
      mpmc_queue_2_suffix_index (suffix_to_val i vs)
    {{{
      RET #i;
      True
    }}}.
  Proof.
    destruct vs; iSteps.
  Qed.

  #[local] Lemma mpmc_queue_2_prefix_index𑁒spec (i : nat) back vs :
    {{{
      back ↦ₕ Header §Back 2 ∗
      back.[index] ↦□ #i
    }}}
      mpmc_queue_2_prefix_index (prefix_to_val i back vs)
    {{{
      RET #⁺(i + length vs);
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hback_header & #Hback_index) HΦ".

    wp_rec.
    destruct vs => /=.
    1: rewrite Nat.add_0_r.
    2: rewrite Nat.add_succ_r.
    all: iSteps.
  Qed.

  #[local] Lemma mpmc_queue_2_rev₀𑁒spec i vs1 vs2 back :
    0 < length vs1 →
    {{{
      back ↦ₕ Header §Back 2
    }}}
      mpmc_queue_2_rev₀ (suffix_to_val (i + S (length vs2)) vs1) (prefix_to_val i back vs2)
    {{{
      RET suffix_to_val (S i) (reverse vs2 ++ vs1);
      True
    }}}.
  Proof.
    iIntros "%Hvs1 %Φ #Hback_header HΦ".

    iInduction vs2 as [| v2 vs2] "IH" forall (vs1 Hvs1).
    all: wp_rec.
    all: destruct vs1 as [| v1 vs1]; first naive_solver lia.
    all: wp_pures.

    - rewrite Nat.add_1_r. iSteps.

    - rewrite !Nat.add_succ_r.
      wp_apply ("IH" $! (v2 :: v1 :: vs1) with "[%]").
      { simpl. lia. }
      rewrite reverse_cons -assoc //.
  Qed.
  #[local] Lemma mpmc_queue_2_rev𑁒spec i back vs :
    0 < length vs →
    {{{
      back ↦ₕ Header §Back 2
    }}}
      mpmc_queue_2_rev (prefix_to_val i back vs)
    {{{
      RET suffix_to_val (S i) (reverse vs);
      True
    }}}.
  Proof.
    iIntros "%Hvs %Φ #Hback_header HΦ".

    wp_rec.
    destruct vs as [| v vs]; first naive_solver lia.
    wp_pures.
    rewrite Z.add_1_r -Nat2Z.inj_succ.
    wp_apply (mpmc_queue_2_rev₀𑁒spec i [v] with "Hback_header"); first auto.
    rewrite reverse_cons //.
  Qed.

  Lemma mpmc_queue_2_create𑁒spec ι :
    {{{
      True
    }}}
      mpmc_queue_2_create ()
    {{{
      t
    , RET t;
      mpmc_queue_2_inv t ι ∗
      mpmc_queue_2_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_block back as "Hback_header" "_" "(Hback_index & Hback_move & _)".
    iMod (pointsto_persist with "Hback_index") as "#Hback_index".
    wp_block l as "Hmeta" "(Hl_front & Hl_back & _)".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod (state_alloc back) as "(%γ_state & Hstate_auth)".
    iMod front_alloc as "(%γ_front & Hfront_auth)".

    pose γ :=
      {|metadata_inv := ι
      ; metadata_model := γ_model
      ; metadata_state := γ_state
      ; metadata_front := γ_front
      |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iDestruct (state_lb_get γ with "Hstate_auth") as "#Hstate_lb".
    iMod (state_stabilize γ with "Hstate_auth") as "(Hstate_auth & _) /="; first done.
    iMod (state_empty γ with "Hstate_auth") as "Hstate_auth".
    iDestruct (state_at_get (γ := γ) back 0 with "Hstate_auth") as "#Hstate_at".
    { apply lookup_insert_eq. }

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. iStep 3. iApply inv_alloc.
    iExists {[back := 0]}, 0, (Stable Empty), 1, [], 0, back, [], [].
    rewrite /= /inv_status_stable big_sepM_singleton.
    iFrameSteps.
  Qed.

  #[local] Lemma front𑁒spec_strong {l γ} i_front i_back :
    {{{
      inv' l γ ∗
      match i_front with
      | None =>
          True
      | Some i_front =>
          front_lb γ i_front
      end ∗
      match i_back with
      | None =>
          True
      | Some i_back =>
          ∃ back,
          state_at γ back i_back
      end
    }}}
      (#l).{front}
    {{{
      i_front' vs_front'
    , RET suffix_to_val i_front' vs_front';
      front_lb γ i_front' ∗
      match i_front with
      | None =>
          True
      | Some i_front =>
          ⌜i_front ≤ i_front'⌝
      end ∗
      match i_back with
      | None =>
          True
      | Some i_back =>
          ∃ i',
          ⌜i_back ≤ i'⌝ ∗
          ⌜(i_front' + length vs_front')%nat = S i'⌝
      end
    }}}.
  Proof.
    iIntros "%Φ (Hinv & #Hfront_lb & #Hstate_at) HΦ".

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1 >)".
    wp_load.
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_1".

    iAssert
      match i_front with
      | None =>
          True
      | Some i_front =>
          ⌜i_front ≤ i_front1⌝
      end%I
    as "#?".
    { destruct i_front as [i_state |]; last iSteps.
      iApply (front_lb_valid with "Hfront_auth Hfront_lb").
    }

    iAssert
      match i_back with
      | None =>
          True
      | Some i_back =>
          ∃ i1,
          ⌜i_back ≤ i1⌝ ∗
          ⌜(i_front1 + length vs_front1)%nat = S i1⌝
      end%I
    as "#?".
    { destruct i_back as [i_back |]; last iSteps.
      iDestruct "Hstate_at" as "(%back & Hstate_at)".
      iDestruct (state_at_valid with "Hstate_auth Hstate_at") as %(_ & ?).
      iSteps.
    }

    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma front𑁒spec l γ :
    {{{
      inv' l γ
    }}}
      (#l).{front}
    {{{
      i_front' vs_front'
    , RET suffix_to_val i_front' vs_front';
      front_lb γ i_front'
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_apply (front𑁒spec_strong None None with "[$Hinv //]").
    iSteps.
  Qed.

  #[local] Lemma move𑁒spec l γ backs back i move :
    {{{
      inv' l γ ∗
      state_lb γ backs i (Unstable back move)
    }}}
      (#back).{move}
    {{{
      𝑚𝑜𝑣𝑒
    , RET 𝑚𝑜𝑣𝑒;
        ⌜𝑚𝑜𝑣𝑒 = §Used%V⌝
      ∨ ∃ backs i back_prev move,
        ⌜𝑚𝑜𝑣𝑒 = prefix_to_val i back_prev move⌝ ∗
        ⌜0 < length move⌝ ∗
        state_lb γ backs i (Unstable back move)
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hstate_lb) HΦ".

    iInv "Hinv" as "(:inv_inner =1 >)".
    iDestruct (state_lb_valid_Unstable with "Hstate_auth Hstate_lb") as "#[(-> & -> & ->) | (%Hbacks1_lookup & _)]".

    - iDestruct "Hstatus" as "(:inv_status_unstable =1 >)".
      iDestruct "Hback1" as "(:back_model_2 =1)".
      wp_load.
      iSplitR "HΦ". { iFrameSteps 2. }
      iStep. iRight. iSteps.

    - iDestruct (big_sepM_lookup_acc with "Hbacks") as "((:back_model_3) & Hbacks)"; first done.
      wp_load.
      iDestruct "H𝑚𝑜𝑣𝑒" as "(:move_model_2 !=)".
      iDestruct "H𝑚𝑜𝑣𝑒" as "(:move_model_1)".

      + iDestruct ("Hbacks" with "[$Hback_move]") as "Hbacks"; first iSteps.
        iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      + iDestruct ("Hbacks" with "[$Hback_move]") as "Hbacks"; first iSteps.
        iSplitR "HΦ". { iFrameSteps. }
        iStep. iRight. iSteps.
  Qed.

  Lemma mpmc_queue_2_size𑁒spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_size t @ ↑ι
    <<<
      mpmc_queue_2_model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_apply (front𑁒spec with "Hinv") as (i_front1 vs_front1) "#Hfront_lb_1".

    wp_apply+ (prophet_typed_1_wp_proph prophet_bool_1 with "[//]") as (pid proph) "Hproph".
    wp_pures.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(:inv_inner =2 >)".
    wp_load.
    destruct proph.

    - iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_1") as %Hi_front2.
      iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_2".

      iAssert (back_model_1 back2 i_back2) as "#(:back_model_1 =2)".
      { destruct status2.
        - iDestruct "Hstatus" as "(:inv_status_stable =2)".
          iDestruct (state_at_valid with "Hstate_auth Hstate_at_2") as %(Hbacks2_lookup & _).
          iDestruct (big_sepM_lookup with "Hbacks") as "(:back_model_3 =2)"; first done.
          iFrame "#".
        - iDestruct "Hstatus" as "(:inv_status_unstable =2)".
          iDestruct "Hback2" as "(:back_model_2 =2)".
          iFrame "#".
      }

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.

      iAssert ⌜(i_front2 + length vs2 = i_back2 + length vs_back2 + 1)%nat⌝%I as %Hsize.
      { destruct status2.
        - iDestruct "Hstatus" as "(:inv_status_stable =2)". iPureIntro.
          apply (f_equal length) in Hvs2. simpl_length in Hvs2. lia.
        - iDestruct "Hstatus" as "(:inv_status_unstable =2)". iPureIntro.
          simpl_length/=. lia.
      }

      iSplitR "Hproph HΦ". { iFrameSteps. }
      iIntros "!> {%- Hi_front2 Hsize}".

      wp_apply+ (front𑁒spec_strong (Some i_front2) None with "[$Hinv $Hfront_lb_2]") as (i_front3 vs_front3) "(_ & %Hi_front3 & _)".
      wp_equal as _ | (-> & ->)%(inj2 _).
      all: wp_apply+ (prophet_typed_1_wp_resolve with "Hproph"); [done.. |].
      all: iStep 11.
      wp_apply (mpmc_queue_2_suffix_index𑁒spec with "[//]") as "_".
      wp_apply (mpmc_queue_2_prefix_index𑁒spec with "[$]") as "_".
      wp_pures.

      replace (⁺(i_back2 + length vs_back2) - i_front1 + 1)%Z with ⁺(length vs2) by lia.
      iSteps.

    - iSplitR "Hproph HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp_apply+ (front𑁒spec with "Hinv") as (i_front3 vs_front3) "_".
      wp_equal.
      all: wp_apply+ (prophet_typed_1_wp_resolve with "Hproph"); [done.. |].
      all: iSteps.
  Qed.

  Lemma mpmc_queue_2_is_empty𑁒spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_is_empty t @ ↑ι
    <<<
      mpmc_queue_2_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.

    awp_apply (mpmc_queue_2_size𑁒spec with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; iSteps.
    destruct vs; iSteps.
  Qed.

  #[local] Lemma mpmc_queue_2_finish𑁒spec {l γ} i_back back :
    {{{
      inv' l γ ∗
      state_at γ back i_back
    }}}
      mpmc_queue_2_finish #back
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hstate_at) HΦ".
    iMod (inv'_state_at with "Hinv Hstate_at") as "(:back_model_1)".

    wp_rec. wp_match.

    iInv "Hinv" as "(:inv_inner =1 >)".
    iDestruct (state_at_valid with "Hstate_auth Hstate_at") as %(Hbacks1_lookup & _).
    iDestruct (big_sepM_lookup_acc with "Hbacks") as "((:back_model_3 only_move=) & Hbacks)".
    { eapply lookup_weaken; done. }
    wp_store.
    iDestruct ("Hbacks" with "[$Hback_move H𝑚𝑜𝑣𝑒]") as "Hbacks".
    { iDestruct "H𝑚𝑜𝑣𝑒" as "(:move_model_2)".
      iSteps.
    }
    iFrameSteps.
  Qed.

  #[local] Lemma mpmc_queue_2_help𑁒spec {l γ backs i back_prev back} move :
    0 < length move →
    {{{
      inv' l γ ∗
      state_lb γ backs i (Unstable back move) ∗
      back_prev ↦ₕ Header §Back 2
    }}}
      mpmc_queue_2_help #l #back #⁺(i + length move) (prefix_to_val i back_prev move)
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hmove %Φ (#Hinv & #Hstate_lb & #Hback_prev_header) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1 >)".
    wp_load.
    iDestruct (state_lb_get with "Hstate_auth") as "#Hstate_lb_1".

    destruct vs_front1 as [| v vs_front1'].

    - rewrite Nat.add_0_r in Hfront1. subst i_front1.

      destruct_decide (i + length move < S i1) as Hif.

      + iDestruct (state_lb_stabilized with "Hstate_auth Hstate_lb") as "#(_ & #Hstate_at)"; first lia.

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hif}".

        wp_pures.
        rewrite bool_decide_eq_true_2; first lia.
        wp_apply+ (mpmc_queue_2_finish𑁒spec with "[$] HΦ").

      + iDestruct (state_lb_unstabilized with "Hstate_auth Hstate_lb") as %(-> & -> & ->); first lia.

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hmove Hif}".

        wp_pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp_apply+ (mpmc_queue_2_rev𑁒spec with "Hback_prev_header") as "_"; first lia.
        wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "Hinv_inner".
        iDestruct (inv_inner_strengthen with "Hinv_inner") as "(:inv_inner =2 >)".
        wp_cas as _ | (-> & ->)%(inj2 suffix_to_val _ _ _ []).

        * iSplitR "HΦ".
          { rewrite inv_status_weaken. iFrameSteps. }
          iSteps.

        * rewrite Nat.add_0_r in Hfront2. injection Hfront2 as <-.
          iDestruct (state_lb_unstabilized with "Hstate_auth Hstate_lb") as %(-> & _ & ->); first lia.
          iDestruct "Hstatus" as "(:inv_status_unstable =2 strong= lazy=)".

          iMod (state_stabilize with "Hstate_auth") as "(Hstate_auth & _ & #Hstate_at)"; first done.
          iDestruct (big_sepM_insert_2 with "[Hback2] Hbacks") as "Hbacks"; first iFrameSteps.
          iSplitR "HΦ".
          { iFrameSteps; iPureIntro.
            - simpl_length.
            - rewrite Hvs_back2 right_id //.
            - simpl_length.
          }
          iIntros "!> {%}".

          wp_apply+ (mpmc_queue_2_finish𑁒spec with "[$] HΦ").

    - iAssert ⌜status1 ≠ Unstable back move⌝%I as %Hstabilized.
      { iIntros (->).
        iDestruct "Hstatus" as "(:inv_status_unstable =1 lazy=)". done.
      }
      iDestruct (state_lb_stabilized with "Hstate_auth Hstate_lb") as "#(_ & #Hstate_at)"; first auto.

      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp_apply+ (mpmc_queue_2_finish𑁒spec with "[$] HΦ").
  Qed.

  #[local] Lemma mpmc_queue_2_push𑁒spec_aux l γ v :
    ⊢ (
      ∀ back i ws (j : Z),
      <<<
        ⌜j = ⁺(i + length ws)⌝ ∗
        inv' l γ ∗
        state_at γ back i
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpmc_queue_2_push_aux #l v #j (prefix_to_val i back ws) @ ↑γ.(metadata_inv)
      <<<
        model₁ γ (vs ++ [v])
      | RET ();
        True
      >>>
    ) ∧ (
      <<<
        inv' l γ
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpmc_queue_2_push #l v @ ↑γ.(metadata_inv)
      <<<
        model₁ γ (vs ++ [v])
      | RET ();
        True
      >>>
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHpush_aux & IHpush)".
    iSplit.

    { iClear "IHpush_aux".
      iIntros "%back %i %ws %j %Φ (-> & #Hinv & #Hstate_at) HΦ".

      wp_rec. wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "Hinv_inner".
      iDestruct (inv_inner_strengthen with "Hinv_inner") as "(:inv_inner =1 >)".
      iDestruct (state_at_valid with "Hstate_auth Hstate_at") as %(Hbacks1_lookup_ & _).
      wp_cas as _ | (_ & -> & ->)%prefix_to_val_inj'.

      - iSplitR "HΦ".
        { rewrite inv_status_weaken. iFrameSteps. }
        iSteps.

      - iDestruct (inv_status_Stable with "Hstatus") as "(%empty1 & -> & (:inv_status_stable =1))"; first auto.

        iAssert ⌜i1 = i⌝%I as %->.
        { iDestruct (state_at_valid with "Hstate_auth Hstate_at_1") as %(Hbacks1_lookup & _). simplify.
          iSteps.
        }

        iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_update with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "Hmodel₁ [//]") as "HΦ".

        iSplitR "HΦ".
        { rewrite Z.add_1_r -Nat2Z.inj_succ -Nat.add_succ_r.
          rewrite -/(prefix_to_val i back (v :: ws)).
          iFrameSteps. iPureIntro.
          rewrite reverse_cons Hvs1 assoc //.
        }
        iSteps.
    }

    { iIntros "%Φ #Hinv HΦ".

      wp_rec. wp_pures.

      wp_bind (_.{back})%E.
      iInv "Hinv" as "(:inv_inner =1 >)".
      wp_load.
      destruct vs_back1 as [| v1 vs_back1].

      - iAssert (
          ∃ backs1_prev i1_prev move1,
          back_model_1 back1 i_back1 ∗
          state_lb γ backs1_prev i1_prev (Unstable back1 move1)
        )%I as "#(%backs1_prev & %i1_prev & %move1 & (:back_model_1 =1) & #Hstate_lb_1)".
        { destruct status1 as [empty1 | back1_ move1].
          - iDestruct "Hstatus" as "(:inv_status_stable =1)".
            iDestruct (state_at_valid with "Hstate_auth Hstate_at_1") as %(Hbacks_lookup & _).
            iDestruct (big_sepM_lookup with "Hbacks") as "(:back_model_3 =1)"; first done.
            iDestruct "H𝑚𝑜𝑣𝑒1" as "(:move_model_2 =1)".
            iSteps.
          - iDestruct "Hstatus" as "(:inv_status_unstable =1 lazy=)".
            iDestruct "Hback1" as "(:back_model_2 =1)".
            iDestruct (state_lb_get with "Hstate_auth") as "$".
            iSteps.
        }

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        wp_match. wp_pures.

        wp_bind (_.{move})%E.
        wp_apply (wp_wand (λ 𝑚𝑜𝑣𝑒,
            ⌜𝑚𝑜𝑣𝑒 = §Used%V⌝ ∗
            state_at γ back1 i_back1
          ∨ ∃ backs i back move,
            ⌜𝑚𝑜𝑣𝑒 = prefix_to_val i back move⌝ ∗
            ⌜0 < length move⌝ ∗
            state_lb γ backs i (Unstable back1 move) ∗
            back ↦ₕ Header §Back 2
        )%I) as (𝑚𝑜𝑣𝑒) "[(-> & #Hstate_at_1) | (%backs & %i & %back & %move & -> & %Hmove & #Hstate_lb & #Hback_header)]".
        { iInv "Hinv" as "(:inv_inner =2 >)".
          iDestruct (state_lb_valid_Unstable with "Hstate_auth Hstate_lb_1") as "#[(-> & -> & ->) | (%Hbacks2_lookup & _ & #Hstate_at)]".
          - iDestruct "Hstatus" as "(:inv_status_unstable =2 >)".
            iDestruct "Hback2" as "(:back_model_2 =2)".
            wp_load.
            iDestruct (state_at_valid with "Hstate_auth Hstate_at_back2_prev") as %(Hbacks2_lookup & _).
            iAssert (back2_prev ↦ₕ Header §Back 2)%I as "#Hback2_prev_header".
            { iDestruct (big_sepM_lookup with "Hbacks") as "(:back_model_3 =2_prev)"; first done.
              iFrame "#".
            }
            iSplitL. { iFrameSteps. }
            iRight. iSteps.
          - iDestruct (big_sepM_lookup_acc with "Hbacks") as "((:back_model_3 =1 !=) & Hbacks)"; first done.
            wp_load.
            iDestruct (pointsto_agree with "Hback1_index Hback1_index_") as %[= ->%(inj _)].
            iDestruct "H𝑚𝑜𝑣𝑒1" as "#H𝑚𝑜𝑣𝑒1".
            iDestruct ("Hbacks" with "[$]") as "Hbacks".
            iSplitL. { iFrameSteps. }
            iDecompose "H𝑚𝑜𝑣𝑒1"; iSteps.
        }

        + wp_load.
          wp_apply ("IHpush_aux" $! back1 i_back1 [] with "[$Hinv $Hstate_at_1] HΦ"); first iSteps.

        + destruct move as [| w move]; first naive_solver lia.

          wp_apply+ (mpmc_queue_2_help𑁒spec with "[$]"); first done.
          iSteps.

      - iDestruct (inv_status_Stable with "Hstatus") as "(%empty1 & -> & (:inv_status_stable =1))"; first naive_solver lia.

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        wp_apply+ ("IHpush_aux" $! _ _ (v1 :: vs_back1) with "[$Hinv $Hstate_at_1] HΦ").
        iSteps.
    }
  Qed.
  Lemma mpmc_queue_2_push𑁒spec t v ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_push t v @ ↑ι
    <<<
      mpmc_queue_2_model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (mpmc_queue_2_push𑁒spec_aux with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hmodel₁"; iSteps.
  Qed.

  #[local] Lemma mpmc_queue_2_pop𑁒spec_aux l γ :
    ⊢ (
      ∀ i_front vs_front,
      <<<
        inv' l γ ∗
        front_lb γ i_front
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpmc_queue_2_pop_1 #l (suffix_to_val i_front vs_front) @ ↑γ.(metadata_inv)
      <<<
        ∃∃ o,
        match o with
        | None =>
            model₁ γ vs
        | Some v =>
            ∃ vs',
            ⌜vs = v :: vs'⌝ ∗
            model₁ γ vs'
        end
      | RET o;
        True
      >>>
    ) ∧ (
      ∀ (i_front : nat) backs back i back_prev move,
      <<<
        ⌜i_front ≤ S i⌝ ∗
        ⌜1 < length move⌝ ∗
        inv' l γ ∗
        state_lb γ backs i (Unstable back move) ∗
        back_prev ↦ₕ Header §Back 2
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpmc_queue_2_pop_2 #l ’Front[ #i_front ] #back (prefix_to_val i back_prev move) @ ↑γ.(metadata_inv)
      <<<
        ∃∃ o,
        match o with
        | None =>
            model₁ γ vs
        | Some v =>
            ∃ vs',
            ⌜vs = v :: vs'⌝ ∗
            model₁ γ vs'
        end
      | RET o;
        True
      >>>
    ) ∧ (
      ∀ i_front,
      <<<
        inv' l γ
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpmc_queue_2_pop_3 #l ’Front[ #i_front ] @ ↑γ.(metadata_inv)
      <<<
        ∃∃ o,
        match o with
        | None =>
            model₁ γ vs
        | Some v =>
            ∃ vs',
            ⌜vs = v :: vs'⌝ ∗
            model₁ γ vs'
        end
      | RET o;
        True
      >>>
    ) ∧ (
      <<<
        inv' l γ
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpmc_queue_2_pop #l @ ↑γ.(metadata_inv)
      <<<
        ∃∃ o,
        match o with
        | None =>
            model₁ γ vs
        | Some v =>
            ∃ vs',
            ⌜vs = v :: vs'⌝ ∗
            model₁ γ vs'
        end
      | RET o;
        True
      >>>
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHpop_1 & IHpop_2 & IHpop_3 & IHpop)".
    repeat iSplit.

    { iIntros "%i_front %vs_front %Φ (#Hinv & #Hfront_lb) HΦ".

      wp_rec. wp_pures.
      destruct vs_front as [| v vs_front]; wp_pures.

      - wp_bind (_.{back})%E.
        iInv "Hinv" as "(:inv_inner =1 >)".
        wp_load.
        iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %Hi_front1.
        iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_1".

        destruct vs_back1 as [| v vs_back1].

        + iAssert (
            ∃ backs1_prev i1_prev move1,
            back1 ↦ₕ Header §Back 2 ∗
            state_lb γ backs1_prev i1_prev (Unstable back1 move1)
          )%I as "(%backs1_prev & %i1_prev & %move1 & #Hback1_header & #Hstate_lb_1)".
          { destruct status1 as [empty1 | back1_ move1].
            - iDestruct "Hstatus" as "(:inv_status_stable =1)".
              iDestruct (state_at_valid with "Hstate_auth Hstate_at_1") as %(Hbacks1_lookup & _).
              iDestruct (big_sepM_lookup with "Hbacks") as "(:back_model_3 =1)"; first done.
              iDestruct "H𝑚𝑜𝑣𝑒1" as "(:move_model_2 =1)".
              iFrame "#".
            - iDestruct "Hstatus" as "(:inv_status_unstable =1 lazy=)".
              iDestruct "Hback1" as "(:back_model_2 =1)".
              iDestruct (state_lb_get with "Hstate_auth") as "$".
              iFrame "#".
          }

          iSplitR "HΦ". { iFrameSteps. }
          iSteps.

        + iDestruct (inv_status_Stable with "Hstatus") as "(%empty1 & -> & (:inv_status_stable =1))"; first naive_solver lia.

          iSplitR "HΦ". { iFrameSteps. }
          iIntros "!> {%- Hfront1 Hi_front1}".

          wp_pures.
          case_bool_decide as Hif; wp_pures.

          * assert (length vs_front1 = 0) as ->%nil_length_inv by lia.
            assert (length vs_back1 = 0) as ->%nil_length_inv by lia.
            replace i_front with (S i1) by lia.
            replace i_front1 with (S i1) by lia.
            simpl. clear.

            wp_bind (CAS _ _ _).
            iInv "Hinv" as "(:inv_inner =2 >)".
            wp_cas as _ | (Hcas & -> & ->)%(prefix_to_val_inj' _ _ _ _ _ [v]).

            -- iSplitR "HΦ". { iFrameSteps. }
               iSteps.

            -- ospecialize* Hcas; first done. subst i_back2.
               iDestruct (inv_status_Stable with "Hstatus") as "(%empty2 & -> & (:inv_status_stable =2))"; first naive_solver lia.
               iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
               assert (length vs_front2 = 0) as ->%nil_length_inv by lia.
               replace i_front2 with (S i2) by lia.
               rewrite reverse_singleton /= in Hvs2. subst vs2.

               iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
               iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
               iMod (model_update with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
               iMod ("HΦ" $! (Some _) with "[$Hmodel₁ //] [//]") as "HΦ".

               iSplitR "HΦ".
               { iFrameSteps. iExists _, _, []. iSteps. }
               iSteps.

          * wp_block back as "#Hback_header" "_" "(Hback_index & Hback_move & _) /=".
            wp_match.
            wp_apply (front𑁒spec_strong (Some i_front1) (Some i1) with "[$Hinv $Hfront_lb_1 $Hstate_at_1]") as (i_front3 vs_front3) "(#Hfront_lb_3 & %Hi_front3 & (%i3 & %Hi3 & %Hfront3))".
            wp_equal as _ | (-> & ->)%(inj2 suffix_to_val _ _ _ []); wp_pures.
            1: iSteps.

            simpl in Hfront3.
            replace i_front with (S i1) in * by lia.
            replace i_front1 with (S i1) in * by lia.
            replace i3 with i1 in * by lia.
            assert (length vs_front1 = 0) as ->%nil_length_inv by lia.
            assert (0 < length vs_back1) as Hvs_back1 by lia.
            clear- Hvs_back1.

            wp_bind (CAS _ _ _).
            iInv "Hinv" as "(:inv_inner =4 >)".
            wp_cas as _ | (Hcas & -> & ->)%(prefix_to_val_inj' _ _ _ _ _ (v :: vs_back1)).

            -- iSplitR "HΦ". { iFrameSteps. }
               iSteps.

            -- ospecialize* Hcas; first done. subst i_back4.
               iDestruct (inv_status_Stable with "Hstatus") as "(%empty4 & -> & (:inv_status_stable =4))"; first naive_solver lia.
               iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %Hi_front4.
               replace i_front4 with (S i4) in * by lia.
               destruct empty4; last lia. subst vs_front4.

               iMod (state_destabilize with "Hstate_auth") as "Hstate_auth".
               iDestruct (state_lb_get with "Hstate_auth") as "#Hstate_lb_4".
               iSplitR "HΦ".
               { iFrameSteps. iExists _, _, []. iSteps. }
               iIntros "!> {%- Hvs_back1}".

               wp_apply+ ("IHpop_2" with "[> $Hinv $Hstate_lb_4] HΦ").
               { iSteps.
                 iMod (inv'_state_at with "Hinv Hstate_at_1") as "(:back_model_1 =1)".
                 iSteps.
               }

      - wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner =1 >)".
        wp_cas as _ | (-> & ->)%(inj2 suffix_to_val _ _ _ (v :: vs_front)).

        + iSplitR "HΦ". { iFrameSteps. }
          iSteps.

        + iDestruct (inv_status_Stable with "Hstatus") as "(%empty1 & -> & (:inv_status_stable =1))"; first naive_solver lia.
          destruct empty1; first congruence.

          iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (model_update with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" $! (Some _) with "[$Hmodel₁ //] [//]") as "HΦ".

          iMod (front_update with "Hfront_auth") as "Hfront_auth".
          iSplitR "HΦ".
          { destruct (nil_or_length_pos vs_front) as [-> | Hvs_front].
            1: iMod (state_empty with "Hstate_auth") as "Hstate_auth".
            all: iFrameSteps; iPureIntro.
            all: naive_solver lia.
          }
          iSteps.
    }

    { iClear "IHpop_1 IHpop_2".
      iIntros "%i_front %backs %back %i %back_prev %move %Φ (%Hmove & %Hi_front & #Hinv & #Hstate_lb & #Hback_prev_header) HΦ".

      wp_rec.
      wp_apply+ (mpmc_queue_2_rev𑁒spec with "[$]") as "_"; first lia.
      destruct move as [| v move _] using rev_ind; first naive_solver lia.
      rewrite reverse_snoc /=. wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "Hinv_inner".
      iDestruct (inv_inner_strengthen with "Hinv_inner") as "(:inv_inner =1 >)".
      wp_cas as _ | (-> & ->)%(inj2 suffix_to_val _ _ _ []).

      - iSplitR "HΦ".
        { rewrite inv_status_weaken. iFrameSteps. }
        iSteps.

      - rewrite Nat.add_0_r in Hfront1. subst i_front.
        iDestruct (state_lb_valid with "Hstate_auth Hstate_lb") as %(_ & ?).
        replace i1 with i by lia.

        iDestruct (state_lb_unstabilized with "Hstate_auth Hstate_lb") as %(-> & _ & ->). lia.
        iDestruct "Hstatus" as "(:inv_status_unstable =1 strong= lazy=)".
        rewrite reverse_snoc.

        iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_update with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some _) with "[$Hmodel₁ //] [//]") as "HΦ /=".

        iMod (state_stabilize with "Hstate_auth") as "(Hstate_auth & _ & #Hstate_at)"; first done.
        iMod (front_update with "Hfront_auth") as "Hfront_auth".
        iDestruct (big_sepM_insert_2 with "[Hback1] Hbacks") as "Hbacks"; first iFrameSteps.
        iSplitR "HΦ".
        { iFrameSteps; iPureIntro.
          - simpl_length/=. lia.
          - rewrite Hvs_back1 right_id //.
          - simpl_length/= in *. lia.
        }
        iIntros "!> {%}".

        wp_apply+ (mpmc_queue_2_finish𑁒spec with "[$]").
        iSteps.
    }

    { iClear "IHpop_2 IHpop_3 IHpop".
      iIntros "%i_front %Φ #Hinv HΦ".

      wp_rec.
      wp_apply+ (front𑁒spec with "Hinv") as (i_front1 vs_front1) "#Hfront_lb".
      wp_equal as _; first iSteps.
      wp_pures.

      iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
      iApply ("HΦ" $! None with "Hmodel₁ [//]").
    }

    { iClear "IHpop_2 IHpop".
      iIntros "%Φ #Hinv HΦ".

      wp_rec.
      wp_apply (front𑁒spec with "Hinv").
      iSteps.
    }
  Qed.
  Lemma mpmc_queue_2_pop𑁒spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_pop t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          mpmc_queue_2_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          mpmc_queue_2_model t vs'
      end
    | RET o;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (mpmc_queue_2_pop𑁒spec_aux with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hmodel₁"; first iSteps. iIntros (o) "Hmodel₁ !>".
    iExists o. destruct o as [v |]; last iSteps.
    iDestruct "Hmodel₁" as "(%vs' & -> & Hmodel₁)".
    iSteps.
  Qed.
End mpmc_queue_2_G.

From zoo_saturn Require
  mpmc_queue_2__opaque.

#[global] Opaque mpmc_queue_2_inv.
#[global] Opaque mpmc_queue_2_model.
