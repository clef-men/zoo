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
  typed_prophet.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From zoo_saturn Require Export
  base
  mpmc_queue_2__code.
From zoo_saturn Require Import
  mpmc_queue_2__types.
From zoo Require Import
  options.

Implicit Types l back prev_back : location.
Implicit Types backs : gmap location nat.
Implicit Types v w t pref suff 𝑚𝑜𝑣𝑒 : val.
Implicit Types vs vs_front vs_back move : list val.

#[local] Program Definition prophet := {|
  typed_strong_prophet1_type :=
    bool ;
  typed_strong_prophet1_of_val v _ :=
    match v with
    | ValBool b =>
        Some b
    | _ =>
        None
    end ;
  typed_strong_prophet1_to_val b :=
    (#b, inhabitant) ;
|}.
Solve Obligations of prophet with
  try done.
Next Obligation.
  naive_solver.
Qed.

Inductive emptiness :=
  | Empty
  | Nonempty.
Implicit Types empty : emptiness.

#[local] Instance emptiness_inhabited : Inhabited emptiness :=
  populate Empty.

Inductive status :=
  | Stable empty
  | Unstable back move.
Implicit Types status : status.

#[local] Instance status_inhabited : Inhabited status :=
  populate (Stable inhabitant).

Record state := {
  state_backs : gmap location nat ;
  state_index : nat ;
  state_status : status ;
}.
Implicit Types state : state.

#[local] Definition state_with_status state status :=
  {|state_backs := state.(state_backs) ;
    state_index := state.(state_index) ;
    state_status := status ;
  |}.

#[local] Definition state_le state1 state2 :=
  state1.(state_backs) ⊆ state2.(state_backs) ∧
  state1.(state_index) ≤ state2.(state_index).

#[local] Instance state_inhabited : Inhabited state :=
  populate {|
    state_backs := inhabitant ;
    state_index := inhabitant ;
    state_status := inhabitant ;
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

Inductive step : relation state :=
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
        {|state_backs := <[back := state1.(state_index) + length move]> state1.(state_backs) ;
          state_index := state1.(state_index) + length move ;
          state_status := Stable Nonempty ;
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

Class MpmcQueue2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_queue_2_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
  #[local] mpmc_queue_2_G_state_G :: AuthMonoG (A := leibnizO state) Σ step ;
  #[local] mpmc_queue_2_G_front_G :: AuthNatMaxG Σ ;
}.

Definition mpmc_queue_2_Σ := #[
  twins_Σ (leibnizO (list val)) ;
  auth_mono_Σ (A := leibnizO state) step ;
  auth_nat_max_Σ
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
  all: zoo_simpl.
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
      ‘Snoc[ #⁺(i + length vs), v, prefix_to_val i back vs ]
  end.

#[local] Lemma prefix_to_val_generative i1 back1 vs1 i2 back2 vs2 :
  prefix_to_val i1 back1 vs1 ≈ prefix_to_val i2 back2 vs2 →
  prefix_to_val i1 back1 vs1 = prefix_to_val i2 back2 vs2.
Proof.
  destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2] => Hsimilar.
  all: zoo_simpl.
  all: congruence.
Qed.

#[local] Lemma prefix_to_val_inj3 i1 back1 vs1 i2 back2 vs2 :
  prefix_to_val i1 back1 vs1 = prefix_to_val i2 back2 vs2 →
    (vs1 ≠ [] → i1 = i2) ∧
    back1 = back2 ∧
    vs1 = vs2.
Proof.
  move: i1 i2 vs2. induction vs1 as [| v1 vs1 IH] => i1 i2 [| v2 vs2] /= Hsimilar.
  all: zoo_simpl; try done.
  edestruct IH as (_ & -> & Hvs); first done.
  rewrite {}Hvs in Hsimilar |- *.
  auto with lia.
Qed.
#[local] Lemma prefix_to_val_inj3' i1 back1 vs1 i2 back2 vs2 :
  prefix_to_val i1 back1 vs1 ≈ prefix_to_val i2 back2 vs2 →
    (vs1 ≠ [] → i1 = i2) ∧
    back1 = back2 ∧
    vs1 = vs2.
Proof.
  intros Hsimilar%prefix_to_val_generative.
  apply prefix_to_val_inj3. done.
Qed.

Section mpmc_queue_2_G.
  Context `{mpmc_queue_2_G : MpmcQueue2G Σ}.

  Record metadata := {
    metadata_inv : namespace ;
    metadata_model : gname ;
    metadata_state : gname ;
    metadata_front : gname ;
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

  #[local] Definition state_auth' γ_state backs i status :=
    auth_mono_auth _ γ_state (DfracOwn 1)
      {|state_backs := backs ;
        state_index := i ;
        state_status := status ;
      |}.
  #[local] Definition state_auth γ backs i status :=
    state_auth' γ.(metadata_state) backs i status.
  #[local] Definition state_lb γ backs i status :=
    auth_mono_lb _ γ.(metadata_state)
      {|state_backs := backs ;
        state_index := i ;
        state_status := status ;
      |}.

  #[local] Definition front_auth' γ_front i :=
    auth_nat_max_auth γ_front (DfracOwn 1) i.
  #[local] Definition front_auth γ i :=
    front_auth' γ.(metadata_front) i.
  #[local] Definition front_lb γ i :=
    auth_nat_max_lb γ.(metadata_front) i.

  #[local] Definition back_model_1 back (i : nat) : iProp Σ :=
    back ↦ₕ Header §Back 2 ∗
    back.[index] ↦□ #i.
  #[local] Instance : CustomIpatFormat "back_model_1" :=
    "(
      #Hback{}_header &
      #Hback{}_index
    )".
  #[local] Definition back_model_2 back (i : nat) 𝑚𝑜𝑣𝑒 : iProp Σ :=
    back_model_1 back i ∗
    back.[move] ↦ 𝑚𝑜𝑣𝑒.
  #[local] Instance : CustomIpatFormat "back_model_2" :=
    "(
      { {only_move} _
      ; (:back_model_1 //)
      } &
      Hback{}_move{_{suff}}
    )".
  #[local] Definition back_model_3 back i : iProp Σ :=
    ∃ 𝑚𝑜𝑣𝑒,
    back_model_2 back i 𝑚𝑜𝑣𝑒.
  #[local] Instance : CustomIpatFormat "back_model_3" :=
    "(
      %𝑚𝑜𝑣𝑒{} &
      (:back_model_2 {//} {/only_move/})
    )".

  #[local] Definition inv_status_stable backs i vs_front i_back back vs_back vs empty : iProp Σ :=
    ⌜i_back = i⌝ ∗
    ⌜backs !! back = Some i_back⌝ ∗
    ⌜vs = vs_front ++ reverse vs_back⌝ ∗
    ⌜if empty then vs_front = [] else 0 < length vs_front⌝.
  #[local] Instance : CustomIpatFormat "inv_status_stable" :=
    "(
      -> &
      %Hbacks{}_lookup &
      %Hvs{} &
      {{empty}->;%}
    )".
  #[local] Definition inv_status_unstable backs i vs_front i_back back vs_back vs back_ move : iProp Σ :=
    ∃ prev_back,
    ⌜back_ = back⌝ ∗
    ⌜backs !! prev_back = Some i⌝ ∗
    ⌜i_back = (i + length move)%nat⌝ ∗
    ⌜vs_front = []⌝ ∗
    ⌜vs_back = []⌝ ∗
    ⌜vs = reverse move⌝ ∗
    back_model_2 back i_back (prefix_to_val i prev_back move).
  #[local] Instance : CustomIpatFormat "inv_status_unstable" :=
    "(
      %prev_back{_{}} &
      -> &
      %Hbacks{}_lookup &
      -> &
      {{lazy}%Hvs_front{};->} &
      -> &
      -> &
      Hback{}
    )".
  #[local] Definition inv_status backs i status vs_front i_back back vs_back vs : iProp Σ :=
    match status with
    | Stable empty =>
        inv_status_stable backs i vs_front i_back back vs_back vs empty
    | Unstable back_ move =>
        inv_status_unstable backs i vs_front i_back back vs_back vs back_ move
    end.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ backs i status i_front vs_front i_back back vs_back vs,
    l.[front] ↦ suffix_to_val i_front vs_front ∗
    front_auth γ i_front ∗
    l.[back] ↦ prefix_to_val (S i_back) back vs_back ∗
    ([∗ map] back ↦ i ∈ backs, back_model_3 back i) ∗
    model₂ γ vs ∗
    state_auth γ backs i status ∗
    ⌜(i_front + length vs_front)%nat = S i⌝ ∗
    inv_status backs i status vs_front i_back back vs_back vs.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %backs{} &
      %i{} &
      %status{} &
      %i_front{} &
      %vs_front{} &
      %i_back{} &
      %back{} &
      %vs_back{} &
      %vs{} &
      Hl_front &
      Hfront_auth &
      Hl_back &
      Hbacks &
      Hmodel₂ &
      >Hstate_auth &
      >%Hi{} &
      Hstatus
    )".
  #[local] Definition inv' l γ : iProp Σ :=
    inv γ.(metadata_inv) (inv_inner l γ).
  Definition mpmc_queue_2_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata_inv)⌝ ∗
    meta l nroot γ ∗
    inv' l γ.
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      -> &
      #Hmeta &
      #Hinv
    )".

  Definition mpmc_queue_2_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l_ &
      %γ_ &
      %Heq &
      #Hmeta_ &
      Hmodel₁
    )".

  #[global] Instance mpmc_queue_2_model_timeless t vs :
    Timeless (mpmc_queue_2_model t vs).
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
    apply twins_update'.
  Qed.

  #[local] Lemma state_alloc back :
    ⊢ |==>
      ∃ γ_state,
      state_auth' γ_state {[back := 0]} 0 (Stable Empty).
  Proof.
    apply auth_mono_alloc.
  Qed.
  #[local] Lemma state_lb_get γ backs i status :
    state_auth γ backs i status ⊢
    state_lb γ backs i status.
  Proof.
    apply auth_mono_lb_get.
  Qed.
  #[local] Lemma state_lb_valid γ backs1 i1 status1 backs2 i2 status2 :
    state_auth γ backs1 i1 status1 -∗
    state_lb γ backs2 i2 status2 -∗
      ⌜backs2 ⊆ backs1⌝ ∗
      ⌜i2 ≤ i2⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %(? & ?)%steps_mono. done.
  Qed.
  #[local] Lemma state_lb_stabilized γ backs1 i1 status1 backs2 i2 back2 move2 :
    ( status1 ≠ Unstable back2 move2
    ∨ i2 + length move2 ≤ i1 ∧
      0 < length move2
    ) →
    state_auth γ backs1 i1 status1 -∗
    state_lb γ backs2 i2 (Unstable back2 move2) -∗
    ⌜backs1 !! back2 = Some (i2 + length move2)%nat⌝.
  Proof.
    iIntros "%H Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %[? | (step3 & Hstep & (? & _)%steps_mono)]%rtc_inv.
    all: iPureIntro.
    - naive_solver lia.
    - invert Hstep.
      eapply lookup_weaken; last done.
      rewrite lookup_insert //.
  Qed.
  #[local] Lemma state_lb_unstabilized γ backs1 i1 status1 backs2 i2 back2 move2 :
    i1 < i2 + length move2 →
    state_auth γ backs1 i1 status1 -∗
    state_lb γ backs2 i2 (Unstable back2 move2) -∗
      ⌜backs1 = backs2⌝ ∗
      ⌜i1 = i2⌝ ∗
      ⌜status1 = Unstable back2 move2⌝.
  Proof.
    iIntros "%H Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %[? | (step3 & Hstep & (_ & HH2)%steps_mono)]%rtc_inv.
    all: iPureIntro.
    - simplify. done.
    - invert Hstep. lia.
  Qed.
  #[local] Lemma state_stabilize γ backs i back move :
    backs !! back = None →
    state_auth γ backs i (Unstable back move) ⊢ |==>
      state_auth γ (<[back := i + length move]> backs) (i + length move) (Stable Nonempty) ∗
      state_lb γ (<[back := i + length move]> backs) (i + length move) (Stable Nonempty).
  Proof.
    iIntros "%Hbacks_lookup Hauth".
    iMod (auth_mono_update' with "Hauth") as "Hauth"; first eauto.
    iDestruct (state_lb_get with "Hauth") as "#Hstate_lb".
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

  #[local] Lemma inv'_back_model_1 {l γ backs i status} back i_back :
    backs !! back = Some i_back →
    inv' l γ -∗
    state_lb γ backs i status ={⊤}=∗
    back_model_1 back i_back.
  Proof.
    iIntros "%Hbacks_lookup #Hinv #Hstate_lb".
    iInv "Hinv" as "(:inv_inner =1)".
    iAssert (▷ back_model_1 back i_back)%I as "#>$".
    { iDestruct (state_lb_valid with "Hstate_auth Hstate_lb") as %(? & _).
      iDestruct (big_sepM_lookup with "Hbacks") as "(:back_model_3)".
      { eapply lookup_weaken; done. }
      iFrame "#".
    }
    iFrameSteps.
  Qed.

  #[local] Lemma mpmc_queue_2_suffix_index_spec (i : nat) vs :
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

  #[local] Lemma mpmc_queue_2_prefix_index_spec (i : nat) back vs :
    {{{
      back ↦ₕ Header §Back 2 ∗
      back.[index] ↦□ #i
    }}}
      mpmc_queue_2_prefix_index (prefix_to_val (S i) back vs)
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

  #[local] Lemma mpmc_queue_2_rev_0_spec i vs1 vs2 back :
    0 < length vs1 →
    {{{
      back ↦ₕ Header §Back 2
    }}}
      mpmc_queue_2_rev_0 (suffix_to_val (S i + length vs2) vs1) (prefix_to_val (S i) back vs2)
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

    - rewrite Nat.add_0_r. iSteps.

    - rewrite Nat.add_succ_r.
      wp_apply ("IH" $! (v2 :: v1 :: vs1) with "[%]").
      { simpl. lia. }
      rewrite reverse_cons -assoc //.
  Qed.
  #[local] Lemma mpmc_queue_2_rev_spec i back vs :
    0 < length vs →
    {{{
      back ↦ₕ Header §Back 2
    }}}
      mpmc_queue_2_rev (prefix_to_val (S i) back vs)
    {{{
      RET suffix_to_val (S i) (reverse vs);
      True
    }}}.
  Proof.
    iIntros "%Hvs %Φ #Hback_header HΦ".

    wp_rec.
    destruct vs as [| v vs]; first naive_solver lia.
    wp_pures.
    replace (⁺(S (i + length vs)) + 1)%Z with ⁺(S (S (i + length vs))) by lia.
    wp_apply (mpmc_queue_2_rev_0_spec i [v] with "Hback_header").
    { simpl. lia. }
    rewrite reverse_cons //.
  Qed.

  Lemma mpmc_queue_2_create_spec ι :
    {{{
      True
    }}}
      mpmc_queue_2_create ()
    {{{ t,
      RET t;
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

    pose γ := {|
      metadata_inv := ι ;
      metadata_model := γ_model ;
      metadata_state := γ_state ;
      metadata_front := γ_front ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. iStep 3. iApply inv_alloc.
    iExists {[back := 0]}, 0, (Stable Empty), 1, [], 0, back, [], [].
    rewrite /= /inv_status_stable big_sepM_singleton lookup_singleton.
    iFrameSteps.
  Qed.

  #[local] Lemma front_spec l γ :
    {{{
      inv' l γ
    }}}
      (#l).{front}
    {{{ i_front vs_front,
      RET suffix_to_val i_front vs_front;
      front_lb γ i_front
    }}}.
  Proof.
    iIntros "%Φ Hinv HΦ".

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma mpmc_queue_2_size_spec t ι :
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
    wp_apply (front_spec with "Hinv") as (i_front1 vs_front1) "#Hfront_lb_1".

    wp_smart_apply (typed_strong_prophet1_wp_proph prophet with "[//]") as (pid proph) "Hproph".
    wp_pures.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_load.
    destruct proph.

    - iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_1") as %Hi_front2.
      iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_2".

      iAssert (back_model_1 back2 i_back2) as "#(:back_model_1 =2)".
      { destruct status2.
        - iDestruct "Hstatus" as "(:inv_status_stable =2)".
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
      iModIntro. clear- Hi_front2 Hsize.

      wp_pures.

      wp_bind (_.{front})%E.
      iInv "Hinv" as "(:inv_inner =3)".
      wp_load.
      iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_2") as %Hi_front3.
      iSplitR "Hproph HΦ". { iFrameSteps. }
      iModIntro. clear- Hi_front2 Hi_front3 Hsize.

      wp_apply (typed_strong_prophet1_wp_resolve with "Hproph"); first done.
      wp_equal as _ | (-> & ->)%(inj2 _); first iSteps.
      iStep 5.
      wp_apply (mpmc_queue_2_suffix_index_spec with "[//]") as "_".
      wp_apply (mpmc_queue_2_prefix_index_spec with "[$]") as "_".
      wp_pures.

      replace (⁺(i_back2 + length vs_back2) - i_front1 + 1)%Z with ⁺(length vs2) by lia.
      iSteps.

    - iSplitR "Hproph HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp_smart_apply (front_spec with "Hinv") as (i_front3 vs_front3) "_".
      wp_apply (typed_strong_prophet1_wp_resolve with "Hproph"); first done.
      wp_equal; iSteps.
  Qed.

  Lemma mpmc_queue_2_is_empty_spec t ι :
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

    awp_apply (mpmc_queue_2_size_spec with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; iSteps.
    destruct vs; iSteps.
  Qed.

  #[local] Lemma mpmc_queue_2_finish_spec {l γ backs i status} i_back back :
    backs !! back = Some i_back →
    {{{
      inv' l γ ∗
      state_lb γ backs i status
    }}}
      mpmc_queue_2_finish #back
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hbacks_lookup %Φ (#Hinv & #Hstate_lb) HΦ".
    iMod (inv'_back_model_1 with "Hinv Hstate_lb") as "(:back_model_1)"; first done.

    wp_rec. wp_match.

    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (state_lb_valid with "Hstate_auth Hstate_lb") as %(? & _).
    iDestruct (big_sepM_lookup_acc with "Hbacks") as "((:back_model_3 only_move=) & Hbacks)".
    { eapply lookup_weaken; done. }
    wp_store.
    iDestruct ("Hbacks" with "[$]") as "Hbacks".
    iFrameSteps.
  Qed.

  #[local] Lemma mpmc_queue_2_help_spec l γ backs i prev_back back move :
    0 < length move →
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      state_lb γ backs i (Unstable back move) ∗
      prev_back ↦ₕ Header §Back 2
    }}}
      mpmc_queue_2_help #l #back #⁺(S i + length move) (prefix_to_val (S i) prev_back move)
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hmove %Φ (#Hmeta & #Hinv & #Hstate_lb & #Hprev_back_header) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (state_lb_get with "Hstate_auth") as "#Hstate_lb_1".

    destruct vs_front1 as [| v vs_front1'].

    - rewrite right_id in Hi1. simplify.

      destruct (decide (i + length move ≤ i1)) as [Hif | Hif].

      + iDestruct (state_lb_stabilized with "Hstate_auth Hstate_lb") as %Hbacks1_lookup; first auto.

        iSplitR "HΦ". { iFrameSteps. }
        iModIntro. clear- Hif Hbacks1_lookup.

        wp_pures.
        rewrite bool_decide_eq_true_2; first lia.
        wp_smart_apply (mpmc_queue_2_finish_spec with "[$] HΦ"); first done.

      + iDestruct (state_lb_unstabilized with "Hstate_auth Hstate_lb") as %(-> & -> & ->); first lia.
        iSplitR "HΦ". { iFrameSteps. }
        iModIntro. clear- Hmove Hif.

        wp_pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp_smart_apply (mpmc_queue_2_rev_spec with "Hprev_back_header") as "_"; first lia.
        wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner =2)".
        wp_cas as _ | (-> & ->)%(inj2 suffix_to_val _ _ _ []).

        * iSplitR "HΦ". { iFrameSteps. }
          iSteps.

        * rewrite Nat.add_0_r in Hi2. injection Hi2 as <-.
          iDestruct (state_lb_unstabilized with "Hstate_auth Hstate_lb") as %(-> & _ & ->); first lia.
          iDestruct "Hstatus" as "(:inv_status_unstable =2 lazy=)".

          iAssert ⌜backs !! back2 = None⌝%I as %Hbacks_lookup.
          { rewrite -eq_None_ne_Some. iIntros "%i_back %Hbacks_lookup".
            iDestruct (big_sepM_lookup with "Hbacks") as "(:back_model_3 only_move=)"; first done.
            iDestruct "Hback2" as "(:back_model_2 suff=)".
            iApply (pointsto_exclusive with "Hback_move Hback_move_").
          }

          iMod (state_stabilize with "Hstate_auth") as "(Hstate_auth & #Hstatus_lb_2)"; first done.
          iDestruct (big_sepM_insert_2 with "[Hback2] Hbacks") as "Hbacks"; first iFrameSteps.
          iSplitR "HΦ".
          { iFrameSteps; iPureIntro.
            - simpl_length.
            - rewrite lookup_insert //.
            - rewrite right_id //.
            - simpl_length.
          }
          iIntros "!> {%}".

          wp_smart_apply (mpmc_queue_2_finish_spec with "[$] HΦ").
          { rewrite lookup_insert //. }

    - iAssert ⌜status1 ≠ Unstable back move⌝%I as %Hstabilized.
      { iIntros (->).
        iDestruct "Hstatus" as "(:inv_status_unstable =1 lazy=)". done.
      }
      iDestruct (state_lb_stabilized with "Hstate_auth Hstate_lb") as %Hbacks1_lookup; first auto.

      iSplitR "HΦ". { iFrameSteps. }
      iModIntro. clear- Hbacks1_lookup.

      wp_smart_apply (mpmc_queue_2_finish_spec with "[$] HΦ"); first done.
  Qed.

  #[local] Lemma mpmc_queue_2_push_aux_push_spec t v ι :
    ⊢ (
      ∀ (i : nat) w pref,
      <<<
        mpmc_queue_2_inv t ι
      | ∀∀ vs,
        mpmc_queue_2_model t vs
      >>>
        mpmc_queue_2_push_aux t v #i ’Snoc( #i, w, pref ) @ ↑ι
      <<<
        mpmc_queue_2_model t (vs ++ [v])
      | RET ();
        True
      >>>
    ) ∧ (
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
      >>>
    ).
  Proof.
  Admitted.
  Lemma mpmc_queue_2_push_spec t v ι :
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
    iDestruct mpmc_queue_2_push_aux_push_spec as "(_ & H)".
    iApply "H".
  Qed.

  Lemma mpmc_queue_2_pop_spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_pop t @ ↑ι
    <<<
      mpmc_queue_2_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
  Admitted.
End mpmc_queue_2_G.

From zoo_saturn Require
  mpmc_queue_2__opaque.

#[global] Opaque mpmc_queue_2_inv.
#[global] Opaque mpmc_queue_2_model.
