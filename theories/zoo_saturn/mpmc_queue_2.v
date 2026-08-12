Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.relations.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_bool.
Require Import zoo_std.option.
Require Export zoo_saturn.mpmc_queue_2__code.
Require Import zoo_saturn.mpmc_queue_2__types.
Require Import zoo.options.

Implicit Type strong : bool.
Implicit Type l back back_prev : location.
Implicit Type backs : gmap location nat.
Implicit Type v w t pref suff 𝑚𝑜𝑣𝑒 : val.
Implicit Type o : option val.
Implicit Type vs vs_front vs_back move : list val.

Variant emptiness :=
  | Empty
  | Nonempty.
Implicit Type empty : emptiness.

#[local] Instance emptinessｰinhabited : Inhabited emptiness :=
  populate Empty.
#[local] Instance emptinessｰeq_dec : EqDecision emptiness :=
  ltac:(solve_decision).

Variant status :=
  | Stable empty
  | Unstable back move.
Implicit Type status : status.

#[local] Instance statusｰinhabited : Inhabited status :=
  populate (Stable inhabitant).
#[local] Instance statusｰeq_dec : EqDecision status :=
  ltac:(solve_decision).

Record state :=
  { state۰backs : gmap location nat
  ; state۰index : nat
  ; state۰status : status
  }.
Implicit Type state : state.

#[local] Definition state۰with_status state status :=
  {|state۰backs := state.(state۰backs)
  ; state۰index := state.(state۰index)
  ; state۰status := status
  |}.

Definition state۰wf backs i :=
  map_Forall (λ _ i_back, i_back ≤ i) backs.

#[local] Definition state۰le state1 state2 :=
  state1.(state۰backs) ⊆ state2.(state۰backs) ∧
  state1.(state۰index) ≤ state2.(state۰index).

#[local] Instance stateｰinhabited : Inhabited state :=
  populate
    {|state۰backs := inhabitant
    ; state۰index := inhabitant
    ; state۰status := inhabitant
    |}.

#[local] Instance state۰leｰreflexive :
  Reflexive state۰le.
Proof.
  done.
Qed.
#[local] Instance state۰leｰtransitive :
  Transitive state۰le.
Proof.
  intros state1 state2 state3 (? & ?) (? & ?).
  split.
  - etrans; done.
  - lia.
Qed.

Variant step : relation state :=
  | stepｰempty state1 state2 :
      state1.(state۰status) = Stable Nonempty →
      state2 = state۰with_status state1 (Stable Empty) →
      step state1 state2
  | stepｰdestabilize state1 state2 back move :
      state1.(state۰status) = Stable Empty →
      state2 = state۰with_status state1 (Unstable back move) →
      step state1 state2
  | stepｰstabilize state1 state2 back move :
      state1.(state۰status) = Unstable back move →
      state1.(state۰backs) !! back = None →
      state2 =
        {|state۰backs := <[back := state1.(state۰index) + length move]> state1.(state۰backs)
        ; state۰index := state1.(state۰index) + length move
        ; state۰status := Stable Nonempty
        |} →
      step state1 state2.
#[local] Hint Constructors step : core.

#[local] Definition steps :=
  rtc step.

#[local] Lemma stepｰmono state1 state2 :
  step state1 state2 →
  state۰le state1 state2.
Proof.
  intros Hstep. invert Hstep; [done.. |].
  split.
  - apply insert_subseteq. done.
  - simpl. lia.
Qed.
#[local] Lemma stepsｰmono state1 state2 :
  steps state1 state2 →
  state۰le state1 state2.
Proof.
  intros Hsteps.
  rewrite -preorderｰrtc.
  apply (rtc_congruence (R := step) id); last done.
  apply stepｰmono.
Qed.

Class MpmcQueue2G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpmc_queue_2۰G۰model۰G :: TwinsG Σ (leibnizO (list val))
  ; #[local] mpmc_queue_2۰G۰state۰G :: AuthMonoG (A := leibnizO state) Σ step
  ; #[local] mpmc_queue_2۰G۰front۰G :: AuthNatMaxG Σ
  }.

Definition mpmc_queue_2۰Σ :=
  #[twins۰Σ (leibnizO (list val))
  ; auth_mono۰Σ (A := leibnizO state) step
  ; auth_nat_max۰Σ
  ].
#[global] Instance subGｰmpmc_queue_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpmc_queue_2۰Σ Σ →
  MpmcQueue2G Σ.
Proof.
  solve_inG.
Qed.

#[local] Fixpoint suffix۰to_val (i : nat) vs : val :=
  match vs with
  | [] =>
      ‘Front[ #i ]
  | v :: vs =>
      ‘Cons[ #i, v, suffix۰to_val ˖i vs ]
  end.

#[local] Lemma suffix۰to_valｰgenerative i1 vs1 i2 vs2 :
  suffix۰to_val i1 vs1 ≈ suffix۰to_val i2 vs2 →
  suffix۰to_val i1 vs1 = suffix۰to_val i2 vs2.
Proof.
  destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2] => Hsimilar.
  all: zoo۰simp.
  all: congruence.
Qed.

#[local] Instance suffix۰to_valｰinj2 :
  Inj2 (=) (=) (=) suffix۰to_val.
Proof.
  move=> + vs1. induction vs1 as [| v1 vs1 IH] => i1 i2 [| v2 vs2] Hsimilar.
  all: naive_solver.
Qed.
#[local] Instance suffix۰to_valｰinj2' :
  Inj2 (=) (=) (≈) suffix۰to_val.
Proof.
  intros ?* Hsimilar%suffix۰to_valｰgenerative.
  apply (inj2 suffix۰to_val). done.
Qed.

#[local] Fixpoint prefix۰to_val (i : nat) back vs : val :=
  match vs with
  | [] =>
      #back
  | v :: vs =>
      ‘Snoc[ #⁺(i + ˖(length vs)), v, prefix۰to_val i back vs ]
  end.

#[local] Lemma prefix۰to_valｰgenerative i1 back1 vs1 i2 back2 vs2 :
  prefix۰to_val i1 back1 vs1 ≈ prefix۰to_val i2 back2 vs2 →
  prefix۰to_val i1 back1 vs1 = prefix۰to_val i2 back2 vs2.
Proof.
  destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2] => Hsimilar.
  all: zoo۰simp.
  all: congruence.
Qed.

#[local] Lemma prefix۰to_valｰinj i1 back1 vs1 i2 back2 vs2 :
  prefix۰to_val i1 back1 vs1 = prefix۰to_val i2 back2 vs2 →
    (vs1 ≠ [] → i1 = i2) ∧
    back1 = back2 ∧
    vs1 = vs2.
Proof.
  move: i1 i2 vs2. induction vs1 as [| v1 vs1 IH] => i1 i2 [| v2 vs2] /= Hsimilar.
  all: zoo۰simp; try done.
  edestruct IH as (_ & -> & Hvs); first done.
  rewrite {}Hvs in Hsimilar |- *.
  auto with lia.
Qed.
#[local] Lemma prefix۰to_valｰinj' i1 back1 vs1 i2 back2 vs2 :
  prefix۰to_val i1 back1 vs1 ≈ prefix۰to_val i2 back2 vs2 →
    (vs1 ≠ [] → i1 = i2) ∧
    back1 = back2 ∧
    vs1 = vs2.
Proof.
  intros Hsimilar%prefix۰to_valｰgenerative.
  apply prefix۰to_valｰinj. done.
Qed.

Section mpmc_queue_2۰G.
  Context `{mpmc_queue_2۰G : MpmcQueue2G Σ}.

  Record metadata :=
    { metadata۰inv : namespace
    ; metadata۰model : gname
    ; metadata۰state : gname
    ; metadata۰front : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadataｰeq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadataｰcountable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata۰model).
  #[local] Definition model₂' γ_model vs :=
    twins۰twin₂ γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata۰model).

  #[local] Definition state۰auth' γ_state backs i status : iProp Σ :=
    auth_mono۰auth _ γ_state (DfracOwn 1)
      {|state۰backs := backs
      ; state۰index := i
      ; state۰status := status
      |} ∗
    ⌜state۰wf backs i⌝.
  #[local] Instance : CustomIpat "state۰auth" :=
    " ( Hauth
      & %Hwf
      )
    ".
  #[local] Definition state۰auth γ backs i status :=
    state۰auth' γ.(metadata۰state) backs i status.
  #[local] Definition state۰lb γ backs i status :=
    auth_mono۰lb _ γ.(metadata۰state)
      {|state۰backs := backs
      ; state۰index := i
      ; state۰status := status
      |}.
  #[local] Definition state۰seen γ back i_prev back_prev move : iProp Σ :=
    ∃ backs,
    state۰lb γ backs i_prev (Unstable back move) ∗
    ⌜backs !! back_prev = Some i_prev⌝.
  #[local] Instance : CustomIpat "state۰seen" :=
    " ( %backs{}
      & #Hstate_lb
      & %Hbacks{}_lookup
      )
    ".
  #[local] Definition state۰at γ back i_back : iProp Σ :=
    ∃ backs i status,
    state۰lb γ backs i status ∗
    ⌜backs !! back = Some i_back⌝ ∗
    ⌜i_back ≤ i⌝.
  #[local] Instance : CustomIpat "state۰at" :=
    " ( %backs{}
      & %i{}
      & %status{}
      & #Hstate_lb{_{}}
      & %Hbacks{}_lookup
      & %Hi{}
      )
    ".

  #[local] Definition front۰auth' γ_front i :=
    auth_nat_max۰auth γ_front (DfracOwn 1) i.
  #[local] Definition front۰auth γ i :=
    front۰auth' γ.(metadata۰front) i.
  #[local] Definition front۰lb γ i :=
    auth_nat_max۰lb γ.(metadata۰front) i.

  #[local] Definition move۰model₁ 𝑚𝑜𝑣𝑒 i_prev back_prev move : iProp Σ :=
      ⌜𝑚𝑜𝑣𝑒 = §Used%V⌝
    ∨ ⌜𝑚𝑜𝑣𝑒 = prefix۰to_val i_prev back_prev move⌝ ∗
      ⌜0 < length move⌝ ∗
      back_prev ↦ₕ Header §Back 2.
  #[local] Instance : CustomIpat "move۰model₁" :=
    " [ ->
      | ( ->
        & %
        & #Hback{}_prev_header
        )
      ]
    ".
  #[local] Definition move۰model₂ γ back 𝑚𝑜𝑣𝑒 : iProp Σ :=
    ∃ backs_prev i_prev back_prev move,
    state۰lb γ backs_prev i_prev (Unstable back move) ∗
    move۰model₁ 𝑚𝑜𝑣𝑒 i_prev back_prev move.
  #[local] Instance : CustomIpat "move۰model₂" :=
    " ( %backs{}_prev
      & %i{}_prev{_{!}}
      & %back{}_prev{_{!}}
      & %move{}{_{!}}
      & #Hstate_lb_unstable{_{}}
      & H𝑚𝑜𝑣𝑒{}
      )
    ".

  #[local] Definition back۰model₁ back (i : nat) : iProp Σ :=
    back ↦ₕ Header §Back 2 ∗
    back.[index] ↦□ #i.
  #[local] Instance : CustomIpat "back۰model₁" :=
    " ( { {!} _
        ; #Hback{}_header
        ; #Hback_header
        }
      & #Hback{}_index{_{!}}
      )
    ".
  #[local] Definition back۰model₂ back (i : nat) 𝑚𝑜𝑣𝑒 : iProp Σ :=
    back۰model₁ back i ∗
    back.[move] ↦ 𝑚𝑜𝑣𝑒.
  #[local] Instance : CustomIpat "back۰model₂" :=
    " ( { {only_move} _
        ; (:back۰model₁ // /!/)
        }
      & Hback{}_move{_{suff}}
      )
    ".
  #[local] Definition back۰model₃ γ back i : iProp Σ :=
    ∃ 𝑚𝑜𝑣𝑒,
    back۰model₂ back i 𝑚𝑜𝑣𝑒 ∗
    move۰model₂ γ back 𝑚𝑜𝑣𝑒.
  #[local] Instance : CustomIpat "back۰model₃" :=
    " ( %𝑚𝑜𝑣𝑒{}
      & (:back۰model₂)
      & H𝑚𝑜𝑣𝑒{}
      )
    ".

  #[local] Definition inv۰status۰stable γ i vs_front i_back back vs_back vs empty : iProp Σ :=
    ⌜i_back = i⌝ ∗
    ⌜vs = vs_front ++ reverse vs_back⌝ ∗
    ⌜if empty then vs_front = [] else 0 < length vs_front⌝ ∗
    state۰at γ back i_back.
  #[local] Instance : CustomIpat "inv۰status۰stable" :=
    " ( {>;}->
      & {>;}%Hvs{}
      & {>;}{{empty}->;%Hempty{};%Hempty}
      & {>;}#Hstate_at{_{}}
      )
    ".
  #[local] Definition inv۰status۰unstable strong γ backs i vs_front i_back back vs_back vs back_ move : iProp Σ :=
    ∃ back_prev,
    ⌜back_ = back⌝ ∗
    ⌜i_back = (i + length move)%nat⌝ ∗
    ⌜vs_front = []⌝ ∗
    ⌜vs_back = []⌝ ∗
    ⌜vs = reverse move⌝ ∗
    ⌜0 < length move⌝ ∗
    state۰at γ back_prev i ∗
    back۰model₂ back i_back (prefix۰to_val i back_prev move) ∗
    if strong then
      ⌜backs !! back = None⌝ ∗
      back_prev ↦ₕ Header §Back 2
    else
      True.
  #[local] Instance : CustomIpat "inv۰status۰unstable" :=
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
  #[local] Definition inv۰status strong γ backs i status vs_front i_back back vs_back vs : iProp Σ :=
    match status with
    | Stable empty =>
        inv۰status۰stable γ i vs_front i_back back vs_back vs empty
    | Unstable back_ move =>
        inv۰status۰unstable strong γ backs i vs_front i_back back vs_back vs back_ move
    end.

  #[local] Definition inv۰inner strong l γ : iProp Σ :=
    ∃ backs i status i_front vs_front i_back back vs_back vs,
    l.[front] ↦ suffix۰to_val i_front vs_front ∗
    front۰auth γ i_front ∗
    l.[back] ↦ prefix۰to_val i_back back vs_back ∗
    ([∗ map] back ↦ i ∈ backs, back۰model₃ γ back i) ∗
    model₂ γ vs ∗
    state۰auth γ backs i status ∗
    ⌜(i_front + length vs_front)%nat = ˖i⌝ ∗
    inv۰status strong γ backs i status vs_front i_back back vs_back vs.
  #[local] Instance : CustomIpat "inv۰inner" :=
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
    inv γ.(metadata۰inv) (inv۰inner false l γ).
  Definition mpmc_queue_2۰inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata۰inv)⌝ ∗
    l ↪ γ ∗
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

  Definition mpmc_queue_2۰model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & Hmodel₁{_{}}
      )
    ".

  #[local] Instance state۰authｰtimeless γ backs i status :
    Timeless (state۰auth γ backs i status).
  Proof.
    apply _.
  Qed.
  #[local] Instance state۰atｰtimeless γ back i_back :
    Timeless (state۰at γ back i_back).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_queue_2۰modelｰtimeless t vs :
    Timeless (mpmc_queue_2۰model t vs).
  Proof.
    apply _.
  Qed.

  #[local] Instance state۰atｰpersistent γ back i_back :
    Persistent (state۰at γ back i_back).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_queue_2۰invｰpersistent t ι :
    Persistent (mpmc_queue_2۰inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma stateｰalloc back :
    ⊢ |==>
      ∃ γ_state,
      state۰auth' γ_state ∅ 0 (Unstable back []).
  Proof.
    set state :=
      {|state۰backs := ∅
      ; state۰index := 0
      ; state۰status := Unstable back []
      |}.
    iMod (auth_monoｰalloc _ (auth_mono۰G := mpmc_queue_2۰G۰state۰G) state) as "(%γ_state & $)".
    iSteps.
  Qed.
  #[local] Lemma state۰authｰwf γ backs i status :
    state۰auth γ backs i status ⊢
    ⌜state۰wf backs i⌝.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma state۰lbｰget γ backs i status :
    state۰auth γ backs i status ⊢
    state۰lb γ backs i status.
  Proof.
    iIntros "(:state۰auth)".
    iApply (auth_mono۰lbｰget with "Hauth").
  Qed.
  #[local] Lemma state۰atｰget {γ backs i status} back i_back :
    backs !! back = Some i_back →
    state۰auth γ backs i status ⊢
    state۰at γ back i_back.
  Proof.
    iIntros "%Hbacks_lookup (:state۰auth)".
    iDestruct (state۰lbｰget with "[$Hauth //]") as "#Hlb".
    iSteps.
  Qed.
  #[local] Lemma state۰lbｰvalid γ backs1 i1 status1 backs2 i2 status2 :
    state۰auth γ backs1 i1 status1 -∗
    state۰lb γ backs2 i2 status2 -∗
      ⌜backs2 ⊆ backs1⌝ ∗
      ⌜i2 ≤ i1⌝.
  Proof.
    iIntros "(:state۰auth) Hlb".
    iDestruct (auth_mono۰lbｰvalid with "Hauth Hlb") as %(? & ?)%stepsｰmono. done.
  Qed.
  #[local] Lemma state۰lbｰvalidｰUnstable γ backs1 i1 status1 backs2 i2 back2 move2 :
    state۰auth γ backs1 i1 status1 -∗
    state۰lb γ backs2 i2 (Unstable back2 move2) -∗
        ⌜backs1 = backs2⌝ ∗
        ⌜i1 = i2⌝ ∗
        ⌜status1 = Unstable back2 move2⌝
      ∨ ⌜backs1 !! back2 = Some (i2 + length move2)%nat⌝ ∗
        ⌜i2 + length move2 ≤ i1⌝ ∗
        state۰at γ back2 (i2 + length move2).
  Proof.
    iIntros "(:state۰auth) Hlb".
    iDestruct (auth_mono۰lbｰvalid with "Hauth Hlb") as %[| (state & Hstep & (? & ?)%stepsｰmono)]%rtc_inv.
    - naive_solver.
    - invert Hstep.
      assert (backs1 !! back = Some (i2 + length move)) as backs1_lookup.
      { eapply lookup_weaken; last done.
        apply lookup_insert_eq.
      }
      iDestruct (state۰atｰget with "[$Hauth //]") as "Hstate_at"; first done.
      iRight. iSteps.
  Qed.
  #[local] Lemma state۰lbｰlookup {γ backs1 i1 status1 backs2 i2 status2} back i_back  :
    backs2 !! back = Some i_back →
    state۰auth γ backs1 i1 status1 -∗
    state۰lb γ backs2 i2 status2 -∗
    ⌜backs1 !! back = Some i_back⌝.
  Proof.
    iIntros "%Hbacks2_lookup Hauth Hlb".
    iDestruct (state۰lbｰvalid with "Hauth Hlb") as %(? & _).
    iPureIntro. eapply lookup_weaken; done.
  Qed.
  #[local] Lemma state۰seenｰvalid γ backs i status back i_prev back_prev move :
    state۰auth γ backs i status -∗
    state۰seen γ back i_prev back_prev move -∗
      ⌜backs !! back_prev = Some i_prev⌝ ∗
      ( ⌜i = i_prev⌝ ∗
        ⌜status = Unstable back move⌝
      ∨ ⌜backs !! back = Some (i_prev + length move)%nat⌝ ∗
        ⌜i_prev + length move ≤ i⌝ ∗
        state۰at γ back (i_prev + length move)
      ).
  Proof.
    iIntros "Hstate_auth (:state۰seen =1)".
    iDestruct (state۰lbｰlookup  with "Hstate_auth Hstate_lb") as %Hbacks_lookup; first done.
    iDestruct (state۰lbｰvalidｰUnstable with "Hstate_auth Hstate_lb") as "[(<- & -> & ->) | $]".
    all: iSteps.
  Qed.
  #[local] Lemma state۰atｰvalid γ backs i status back i_back :
    state۰auth γ backs i status -∗
    state۰at γ back i_back -∗
      ⌜backs !! back = Some i_back⌝ ∗
      ⌜i_back ≤ i⌝.
  Proof.
    iIntros "Hstate_auth (:state۰at =1)".
    iDestruct (state۰lbｰlookup with "Hstate_auth Hstate_lb_1") as %Hbacks_lookup; first done.
    iDestruct (state۰lbｰvalid with "Hstate_auth Hstate_lb_1") as "(_ & %Hi)".
    iSteps.
  Qed.
  (* #[local] Lemma stateｰseenｰatｰagree γ backs i status back i_prev back_prev1 move back_prev2 : *)
  (*   state۰auth γ backs i status -∗ *)
  (*   state۰seen γ back i_prev back_prev1 move -∗ *)
  (*   state۰at γ back_prev2 i_prev -∗ *)
  (*   ⌜back_prev1 = back_prev2⌝. *)
  (* Proof. *)
  (*   iIntros "Hstate_auth Hstate_seen Hstate_at". *)
  (*   iDestruct (state۰auth_wf with "Hstate_auth") as %Hwf. *)
  (*   iDestruct (state۰seen_valid with "Hstate_auth Hstate_seen") as "#(%Hbacks_lookup_1 & _)". *)
  (*   iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at") as "#(%Hbacks_lookup_2 & _)". *)
  (*   iPureIntro. eapply state۰wf_inj; done. *)
  (* Qed. *)
  #[local] Lemma state۰lbｰstabilized γ backs1 i1 status1 backs2 i2 back2 move2 :
    ( status1 ≠ Unstable back2 move2
    ∨ i2 + length move2 ≤ i1 ∧
      0 < length move2
    ) →
    state۰auth γ backs1 i1 status1 -∗
    state۰lb γ backs2 i2 (Unstable back2 move2) -∗
      ⌜backs1 !! back2 = Some (i2 + length move2)%nat⌝ ∗
      state۰at γ back2 (i2 + length move2).
  Proof.
    iIntros "% Hauth Hlb".
    iDestruct (state۰lbｰvalidｰUnstable with "Hauth Hlb") as "[(-> & -> & ->) | ($ & _ & $)]".
    exfalso. naive_solver lia.
  Qed.
  #[local] Lemma state۰lbｰunstabilized γ backs1 i1 status1 backs2 i2 back2 move2 :
    i1 < i2 + length move2 →
    state۰auth γ backs1 i1 status1 -∗
    state۰lb γ backs2 i2 (Unstable back2 move2) -∗
      ⌜backs1 = backs2⌝ ∗
      ⌜i1 = i2⌝ ∗
      ⌜status1 = Unstable back2 move2⌝.
  Proof.
    iIntros "% Hauth Hlb".
    iDestruct (state۰lbｰvalidｰUnstable with "Hauth Hlb") as "[(-> & -> & ->) | (_ & % & _)]"; first iSteps.
    exfalso. lia.
  Qed.
  #[local] Lemma stateｰstabilize γ backs i back move :
    backs !! back = None →
    state۰auth γ backs i (Unstable back move) ⊢ |==>
      state۰auth γ (<[back := i + length move]> backs) (i + length move) (Stable Nonempty) ∗
      state۰lb γ (<[back := i + length move]> backs) (i + length move) (Stable Nonempty) ∗
      state۰at γ back (i + length move).
  Proof.
    iIntros "%Hbacks_lookup (:state۰auth)".

    iMod (auth_monoｰupdate' with "Hauth") as "Hauth"; first eauto. simpl.

    set i' := i + length move.
    set backs' := <[back := i']> backs.

    assert (state۰wf backs' i') as Hwf'.
    { apply map_Forall_insert; first done.
      split; first done.
      eapply map_Forall_impl; first apply Hwf.
      naive_solver lia.
    }

    iDestruct (state۰lbｰget with "[$Hauth //]") as "#Hstate_lb".
    iDestruct (state۰atｰget back with "[$Hauth //]") as "#Hat".
    { apply lookup_insert_eq. }
    iFrame "#∗". iSteps.
  Qed.
  #[local] Lemma stateｰempty γ backs i :
    state۰auth γ backs i (Stable Nonempty) ⊢ |==>
    state۰auth γ backs i (Stable Empty).
  Proof.
    iIntros "(:state۰auth)".
    iMod (auth_monoｰupdate' with "Hauth") as "$"; first auto.
    iSteps.
  Qed.
  #[local] Lemma stateｰdestabilize {γ backs i} back move :
    state۰auth γ backs i (Stable Empty) ⊢ |==>
    state۰auth γ backs i (Unstable back move).
  Proof.
    iIntros "(:state۰auth)".
    iMod (auth_monoｰupdate' with "Hauth") as "$"; first eauto.
    iSteps.
  Qed.

  #[local] Lemma frontｰalloc :
    ⊢ |==>
      ∃ γ_front,
      front۰auth' γ_front 1.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma front۰lbｰget γ i :
    front۰auth γ i ⊢
    front۰lb γ i.
  Proof.
    apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma front۰lbｰvalid γ i1 i2 :
    front۰auth γ i1 -∗
    front۰lb γ i2 -∗
    ⌜i2 ≤ i1⌝.
  Proof.
    apply auth_nat_max۰lbｰvalid.
  Qed.
  #[local] Lemma frontｰupdate γ i :
    front۰auth γ i ⊢ |==>
    front۰auth γ ˖i.
  Proof.
    apply auth_nat_maxｰupdate. lia.
  Qed.

  Opaque state۰auth.
  Opaque state۰at.

  #[local] Lemma inv۰statusｰweaken γ backs i status vs_front i_back back vs_back vs :
    inv۰status true γ backs i status vs_front i_back back vs_back vs ⊢
    inv۰status false γ backs i status vs_front i_back back vs_back vs.
  Proof.
    destruct status as [empty | back_ move]; iSteps.
  Qed.
  #[local] Lemma inv۰statusｰStable strong γ backs i status vs_front i_back back vs_back vs :
    ( strong = true ∧ is_Some (backs !! back)
    ∨ 0 < length vs_front
    ∨ 0 < length vs_back
    ) →
    inv۰status strong γ backs i status vs_front i_back back vs_back vs ⊢
      ∃ empty,
      ⌜status = Stable empty⌝ ∗
      inv۰status۰stable γ i vs_front i_back back vs_back vs empty.
  Proof.
    iIntros "%H H".
    destruct status as [empty | back_ move].
    - iDestruct "H" as "(:inv۰status۰stable)".
      iSteps.
    - destruct H as [(-> & i_back_ & Hbacks_lookup) |].
      + iDestruct "H" as "(:inv۰status۰unstable =1 strong=)".
        congruence.
      + iDestruct "H" as "(:inv۰status۰unstable)".
        simpl in *. lia.
  Qed.

  #[local] Lemma inv۰innerｰstrengthen l γ :
    inv۰inner false l γ ⊢
    inv۰inner true l γ.
  Proof.
    iIntros "(:inv۰inner)".
    destruct status as [empty | back_ move].

    - iDestruct "Hstatus" as "(:inv۰status۰stable)".
      iFrameSteps.

    - iDestruct "Hstatus" as "(:inv۰status۰unstable)".

      iAssert ⌜backs !! back = None⌝%I as %Hbacks_lookup.
      { rewrite -eq_None_ne_Some.
        iIntros "%i_back %Hbacks_lookup".
        iDestruct (big_sepM_lookup with "Hbacks") as "(:back۰model₃ only_move=)"; first done.
        iDestruct "Hback" as "(:back۰model₂ suff=)".
        iApply (pointstoｰexclusive with "Hback_move Hback_move_").
      }

      iAssert (back_prev ↦ₕ Header §Back 2)%I as "#Hback_prev_header".
      { iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at_back_prev") as %(Hbacks_lookup_prev & _).
        iDestruct (big_sepM_lookup with "Hbacks") as "(:back۰model₃ =_prev)"; first done.
        iFrame "#".
      }

      iFrameSteps.
  Qed.

  #[local] Lemma inv'ｰstate۰at {l γ} back i_back :
    inv' l γ -∗
    state۰at γ back i_back ={⊤}=∗
    back۰model₁ back i_back.
  Proof.
    iIntros "#Hinv #Hstate_at".

    iInv "Hinv" as "(:inv۰inner =1 >)".

    iAssert (▷ back۰model₁ back i_back)%I as "#>$".
    { iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at") as %(Hbacks_lookup & _).
      iDestruct (big_sepM_lookup with "Hbacks") as "(:back۰model₃)".
      { eapply lookup_weaken; done. }
      iFrame "#".
    }

    iFrameSteps.
  Qed.

  Lemma mpmc_queue_2۰modelｰexclusive t vs1 vs2 :
    mpmc_queue_2۰model t vs1 -∗
    mpmc_queue_2۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  #[local] Lemma mpmc_queue_2٠suffix_indexｰspec (i : nat) vs :
    {{{
      True
    }}}
      mpmc_queue_2٠suffix_index (suffix۰to_val i vs)
    {{{
      RET #i;
      True
    }}}.
  Proof.
    destruct vs; iSteps.
  Qed.

  #[local] Lemma mpmc_queue_2٠prefix_indexｰspec (i : nat) back vs :
    {{{
      back ↦ₕ Header §Back 2 ∗
      back.[index] ↦□ #i
    }}}
      mpmc_queue_2٠prefix_index (prefix۰to_val i back vs)
    {{{
      RET #⁺(i + length vs);
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hback_header & #Hback_index) HΦ".

    wp۰rec.
    destruct vs => /=.
    1: rewrite Nat.add_0_r.
    2: rewrite Nat.add_succ_r.
    all: iSteps.
  Qed.

  #[local] Lemma mpmc_queue_2٠rev₁ｰspec i vs1 vs2 back :
    0 < length vs1 →
    {{{
      back ↦ₕ Header §Back 2
    }}}
      mpmc_queue_2٠rev₁ (suffix۰to_val (i + ˖(length vs2)) vs1) (prefix۰to_val i back vs2)
    {{{
      RET suffix۰to_val ˖i (reverse vs2 ++ vs1);
      True
    }}}.
  Proof.
    iIntros "%Hvs1 %Φ #Hback_header HΦ".

    iInduction vs2 as [| v2 vs2] "IH" forall (vs1 Hvs1).
    all: wp۰rec.
    all: destruct vs1 as [| v1 vs1]; first naive_solver lia.
    all: wp۰pures.

    - rewrite Nat.add_1_r. iSteps.

    - rewrite !Nat.add_succ_r.
      wp۰apply ("IH" $! (v2 :: v1 :: vs1) with "[%]").
      { simpl. lia. }
      rewrite reverse_cons -assoc //.
  Qed.
  #[local] Lemma mpmc_queue_2٠revｰspec i back vs :
    0 < length vs →
    {{{
      back ↦ₕ Header §Back 2
    }}}
      mpmc_queue_2٠rev (prefix۰to_val i back vs)
    {{{
      RET suffix۰to_val ˖i (reverse vs);
      True
    }}}.
  Proof.
    iIntros "%Hvs %Φ #Hback_header HΦ".

    wp۰rec.
    destruct vs as [| v vs]; first naive_solver lia.
    wp۰pures.
    rewrite Z.add_1_r -Nat2Z.inj_succ.
    wp۰apply (mpmc_queue_2٠rev₁ｰspec i [v] with "Hback_header"); first auto.
    rewrite reverse_cons //.
  Qed.

  Lemma mpmc_queue_2٠createｰspec ι :
    {{{
      True
    }}}
      mpmc_queue_2٠create ()
    {{{
      t
    , RET t;
      mpmc_queue_2۰inv t ι ∗
      mpmc_queue_2۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰block back as "Hback_header" "_" "(Hback_index & Hback_move & _)".
    iMod (pointstoｰpersist with "Hback_index") as "#Hback_index".
    wp۰block l as "Hmeta" "(Hl_front & Hl_back & _)".

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod (stateｰalloc back) as "(%γ_state & Hstate_auth)".
    iMod frontｰalloc as "(%γ_front & Hfront_auth)".

    pose γ :=
      {|metadata۰inv := ι
      ; metadata۰model := γ_model
      ; metadata۰state := γ_state
      ; metadata۰front := γ_front
      |}.
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iDestruct (state۰lbｰget γ with "Hstate_auth") as "#Hstate_lb".
    iMod (stateｰstabilize γ with "Hstate_auth") as "(Hstate_auth & _) /="; first done.
    iMod (stateｰempty γ with "Hstate_auth") as "Hstate_auth".
    iDestruct (state۰atｰget (γ := γ) back 0 with "Hstate_auth") as "#Hstate_at".
    { apply lookup_insert_eq. }

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. iStep 3. iApply inv_alloc.
    iExists {[back := 0]}, 0, (Stable Empty), 1, [], 0, back, [], [].
    rewrite /= /inv۰status۰stable big_sepM_singleton.
    iFrameSteps.
  Qed.

  #[local] Lemma frontｰspec_strong {l γ} i_front i_back :
    {{{
      inv' l γ ∗
      match i_front with
      | None =>
          True
      | Some i_front =>
          front۰lb γ i_front
      end ∗
      match i_back with
      | None =>
          True
      | Some i_back =>
          ∃ back,
          state۰at γ back i_back
      end
    }}}
      (#l).{front}
    {{{
      i_front' vs_front'
    , RET suffix۰to_val i_front' vs_front';
      front۰lb γ i_front' ∗
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
          ⌜(i_front' + length vs_front')%nat = ˖i'⌝
      end
    }}}.
  Proof.
    iIntros "%Φ (Hinv & #Hfront_lb & #Hstate_at) HΦ".

    wp۰bind (_.{front})%E.
    iInv "Hinv" as "(:inv۰inner =1 >)".
    wp۰load.
    iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb_1".

    iAssert
      match i_front with
      | None =>
          True
      | Some i_front =>
          ⌜i_front ≤ i_front1⌝
      end%I
    as "#?".
    { destruct i_front as [i_state |]; last iSteps.
      iApply (front۰lbｰvalid with "Hfront_auth Hfront_lb").
    }

    iAssert
      match i_back with
      | None =>
          True
      | Some i_back =>
          ∃ i1,
          ⌜i_back ≤ i1⌝ ∗
          ⌜(i_front1 + length vs_front1)%nat = ˖i1⌝
      end%I
    as "#?".
    { destruct i_back as [i_back |]; last iSteps.
      iDestruct "Hstate_at" as "(%back & Hstate_at)".
      iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at") as %(_ & ?).
      iSteps.
    }

    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma frontｰspec l γ :
    {{{
      inv' l γ
    }}}
      (#l).{front}
    {{{
      i_front' vs_front'
    , RET suffix۰to_val i_front' vs_front';
      front۰lb γ i_front'
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰apply (frontｰspec_strong None None with "[$Hinv //]").
    iSteps.
  Qed.

  #[local] Lemma moveｰspec l γ backs back i move :
    {{{
      inv' l γ ∗
      state۰lb γ backs i (Unstable back move)
    }}}
      (#back).{move}
    {{{
      𝑚𝑜𝑣𝑒
    , RET 𝑚𝑜𝑣𝑒;
        ⌜𝑚𝑜𝑣𝑒 = §Used%V⌝
      ∨ ∃ backs i back_prev move,
        ⌜𝑚𝑜𝑣𝑒 = prefix۰to_val i back_prev move⌝ ∗
        ⌜0 < length move⌝ ∗
        state۰lb γ backs i (Unstable back move)
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hstate_lb) HΦ".

    iInv "Hinv" as "(:inv۰inner =1 >)".
    iDestruct (state۰lbｰvalidｰUnstable with "Hstate_auth Hstate_lb") as "#[(-> & -> & ->) | (%Hbacks1_lookup & _)]".

    - iDestruct "Hstatus" as "(:inv۰status۰unstable =1 >)".
      iDestruct "Hback1" as "(:back۰model₂ =1)".
      wp۰load.
      iSplitR "HΦ". { iFrameSteps 2. }
      iStep. iRight. iSteps.

    - iDestruct (big_sepM_lookup_acc with "Hbacks") as "((:back۰model₃) & Hbacks)"; first done.
      wp۰load.
      iDestruct "H𝑚𝑜𝑣𝑒" as "(:move۰model₂ !=)".
      iDestruct "H𝑚𝑜𝑣𝑒" as "(:move۰model₁)".

      + iDestruct ("Hbacks" with "[$Hback_move]") as "Hbacks"; first iSteps.
        iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      + iDestruct ("Hbacks" with "[$Hback_move]") as "Hbacks"; first iSteps.
        iSplitR "HΦ". { iFrameSteps. }
        iStep. iRight. iSteps.
  Qed.

  Lemma mpmc_queue_2٠sizeｰspec t ι :
    <<<
      mpmc_queue_2۰inv t ι
    | ∀∀ vs,
      mpmc_queue_2۰model t vs
    >>>
      mpmc_queue_2٠size t @ ↑ι
    <<<
      mpmc_queue_2۰model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec.
    wp۰apply (frontｰspec with "Hinv") as (i_front1 vs_front1) "#Hfront_lb_1".

    wp۰apply+ (prophet_typed₁ｰwpｰproph prophet_bool₁ with "[//]") as (pid proph) "Hproph".
    wp۰pures.

    wp۰bind (_.{back})%E.
    iInv "Hinv" as "(:inv۰inner =2 >)".
    wp۰load.
    destruct proph.

    - iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb_1") as %Hi_front2.
      iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb_2".

      iAssert (back۰model₁ back2 i_back2) as "#(:back۰model₁ =2)".
      { destruct status2.
        - iDestruct "Hstatus" as "(:inv۰status۰stable =2)".
          iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at_2") as %(Hbacks2_lookup & _).
          iDestruct (big_sepM_lookup with "Hbacks") as "(:back۰model₃ =2)"; first done.
          iFrame "#".
        - iDestruct "Hstatus" as "(:inv۰status۰unstable =2)".
          iDestruct "Hback2" as "(:back۰model₂ =2)".
          iFrame "#".
      }

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.

      iAssert ⌜(i_front2 + length vs2 = i_back2 + length vs_back2 + 1)%nat⌝%I as %Hsize.
      { destruct status2.
        - iDestruct "Hstatus" as "(:inv۰status۰stable =2)". iPureIntro.
          apply (f_equal length) in Hvs2. simpl_length in Hvs2. lia.
        - iDestruct "Hstatus" as "(:inv۰status۰unstable =2)". iPureIntro.
          simpl_length/=. lia.
      }

      iSplitR "Hproph HΦ". { iFrameSteps. }
      iIntros "!> {%- Hi_front2 Hsize}".

      wp۰apply+ (frontｰspec_strong (Some i_front2) None with "[$Hinv $Hfront_lb_2]") as (i_front3 vs_front3) "(_ & %Hi_front3 & _)".
      wp۰equal as _ | (-> & ->)%(inj2 _).
      all: wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
      all: iStep 12.
      wp۰apply (mpmc_queue_2٠suffix_indexｰspec with "[//]") as "_".
      wp۰apply (mpmc_queue_2٠prefix_indexｰspec with "[$]") as "_".
      wp۰pures.

      replace (⁺(i_back2 + length vs_back2) - i_front1 + 1)%Z with ⁺(length vs2) by lia.
      iSteps.

    - iSplitR "Hproph HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰apply+ (frontｰspec with "Hinv") as (i_front3 vs_front3) "_".
      wp۰equal.
      all: wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
      all: iSteps.
  Qed.

  Lemma mpmc_queue_2٠is_emptyｰspec t ι :
    <<<
      mpmc_queue_2۰inv t ι
    | ∀∀ vs,
      mpmc_queue_2۰model t vs
    >>>
      mpmc_queue_2٠is_empty t @ ↑ι
    <<<
      mpmc_queue_2۰model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.

    awp۰apply (mpmc_queue_2٠sizeｰspec with "Hinv").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; iSteps.
    destruct vs; iSteps.
  Qed.

  #[local] Lemma mpmc_queue_2٠finishｰspec {l γ} i_back back :
    {{{
      inv' l γ ∗
      state۰at γ back i_back
    }}}
      mpmc_queue_2٠finish #back
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hstate_at) HΦ".
    iMod (inv'ｰstate۰at with "Hinv Hstate_at") as "(:back۰model₁)".

    wp۰rec. wp۰match.

    iInv "Hinv" as "(:inv۰inner =1 >)".
    iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at") as %(Hbacks1_lookup & _).
    iDestruct (big_sepM_lookup_acc with "Hbacks") as "((:back۰model₃ only_move=) & Hbacks)".
    { eapply lookup_weaken; done. }
    wp۰store.
    iDestruct ("Hbacks" with "[$Hback_move H𝑚𝑜𝑣𝑒]") as "Hbacks".
    { iDestruct "H𝑚𝑜𝑣𝑒" as "(:move۰model₂)".
      iSteps.
    }
    iFrameSteps.
  Qed.

  #[local] Lemma mpmc_queue_2٠helpｰspec {l γ backs i back_prev back} move :
    0 < length move →
    {{{
      inv' l γ ∗
      state۰lb γ backs i (Unstable back move) ∗
      back_prev ↦ₕ Header §Back 2
    }}}
      mpmc_queue_2٠help #l #back #⁺(i + length move) (prefix۰to_val i back_prev move)
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hmove %Φ (#Hinv & #Hstate_lb & #Hback_prev_header) HΦ".

    wp۰rec. wp۰pures.

    wp۰bind (_.{front})%E.
    iInv "Hinv" as "(:inv۰inner =1 >)".
    wp۰load.
    iDestruct (state۰lbｰget with "Hstate_auth") as "#Hstate_lb_1".

    destruct vs_front1 as [| v vs_front1'].

    - rewrite Nat.add_0_r in Hfront1. subst i_front1.

      destruct_decide (i + length move < ˖i1) as Hif.

      + iDestruct (state۰lbｰstabilized with "Hstate_auth Hstate_lb") as "#(_ & #Hstate_at)"; first lia.

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hif}".

        wp۰pures.
        rewrite bool_decide_eq_true_2; first lia.
        wp۰apply+ (mpmc_queue_2٠finishｰspec with "[$] HΦ").

      + iDestruct (state۰lbｰunstabilized with "Hstate_auth Hstate_lb") as %(-> & -> & ->); first lia.

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hmove Hif}".

        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰apply+ (mpmc_queue_2٠revｰspec with "Hback_prev_header") as "_"; first lia.
        wp۰pures.

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "Hinv_inner".
        iDestruct (inv۰innerｰstrengthen with "Hinv_inner") as "(:inv۰inner =2 >)".
        wp۰cas as _ | (-> & ->)%(inj2 suffix۰to_val _ _ _ []).

        * iSplitR "HΦ".
          { rewrite inv۰statusｰweaken. iFrameSteps. }
          iSteps.

        * rewrite Nat.add_0_r in Hfront2. injection Hfront2 as <-.
          iDestruct (state۰lbｰunstabilized with "Hstate_auth Hstate_lb") as %(-> & _ & ->); first lia.
          iDestruct "Hstatus" as "(:inv۰status۰unstable =2 strong= lazy=)".

          iMod (stateｰstabilize with "Hstate_auth") as "(Hstate_auth & _ & #Hstate_at)"; first done.
          iDestruct (big_sepM_insert_2 with "[Hback2] Hbacks") as "Hbacks"; first iFrameSteps.
          iSplitR "HΦ".
          { iFrameSteps; iPureIntro.
            - simpl_length.
            - rewrite Hvs_back2 right_id //.
            - simpl_length.
          }
          iIntros "!> {%}".

          wp۰apply+ (mpmc_queue_2٠finishｰspec with "[$] HΦ").

    - iAssert ⌜status1 ≠ Unstable back move⌝%I as %Hstabilized.
      { iIntros (->).
        iDestruct "Hstatus" as "(:inv۰status۰unstable =1 lazy=)". done.
      }
      iDestruct (state۰lbｰstabilized with "Hstate_auth Hstate_lb") as "#(_ & #Hstate_at)"; first auto.

      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰apply+ (mpmc_queue_2٠finishｰspec with "[$] HΦ").
  Qed.

  #[local] Lemma mpmc_queue_2٠pushｰspecｰaux l γ v :
    ⊢ (
      ∀ back i ws (j : Z),
      <<<
        ⌜j = ⁺(i + length ws)⌝ ∗
        inv' l γ ∗
        state۰at γ back i
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpmc_queue_2٠push_aux #l v #j (prefix۰to_val i back ws) @ ↑γ.(metadata۰inv)
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
        mpmc_queue_2٠push #l v @ ↑γ.(metadata۰inv)
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

      wp۰rec. wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "Hinv_inner".
      iDestruct (inv۰innerｰstrengthen with "Hinv_inner") as "(:inv۰inner =1 >)".
      iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at") as %(Hbacks1_lookup_ & _).
      wp۰cas as _ | (_ & -> & ->)%prefix۰to_valｰinj'.

      - iSplitR "HΦ".
        { rewrite inv۰statusｰweaken. iFrameSteps. }
        iSteps.

      - iDestruct (inv۰statusｰStable with "Hstatus") as "(%empty1 & -> & (:inv۰status۰stable =1))"; first auto.

        iAssert ⌜i1 = i⌝%I as %->.
        { iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at_1") as %(Hbacks1_lookup & _). simp.
          iSteps.
        }

        iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "Hmodel₁ [//]") as "HΦ".

        iSplitR "HΦ".
        { rewrite Z.add_1_r -Nat2Z.inj_succ -Nat.add_succ_r.
          rewrite -/(prefix۰to_val i back (v :: ws)).
          iFrameSteps. iPureIntro.
          rewrite reverse_cons Hvs1 assoc //.
        }
        iSteps.
    }

    { iIntros "%Φ #Hinv HΦ".

      wp۰rec. wp۰pures.

      wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner =1 >)".
      wp۰load.
      destruct vs_back1 as [| v1 vs_back1].

      - iAssert (
          ∃ backs1_prev i1_prev move1,
          back۰model₁ back1 i_back1 ∗
          state۰lb γ backs1_prev i1_prev (Unstable back1 move1)
        )%I as "#(%backs1_prev & %i1_prev & %move1 & (:back۰model₁ =1) & #Hstate_lb_1)".
        { destruct status1 as [empty1 | back1_ move1].
          - iDestruct "Hstatus" as "(:inv۰status۰stable =1)".
            iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at_1") as %(Hbacks_lookup & _).
            iDestruct (big_sepM_lookup with "Hbacks") as "(:back۰model₃ =1)"; first done.
            iDestruct "H𝑚𝑜𝑣𝑒1" as "(:move۰model₂ =1)".
            iSteps.
          - iDestruct "Hstatus" as "(:inv۰status۰unstable =1 lazy=)".
            iDestruct "Hback1" as "(:back۰model₂ =1)".
            iDestruct (state۰lbｰget with "Hstate_auth") as "$".
            iSteps.
        }

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        wp۰match. wp۰pures.

        wp۰bind (_.{move})%E.
        wp۰apply (wpｰwand (λ 𝑚𝑜𝑣𝑒,
            ⌜𝑚𝑜𝑣𝑒 = §Used%V⌝ ∗
            state۰at γ back1 i_back1
          ∨ ∃ backs i back move,
            ⌜𝑚𝑜𝑣𝑒 = prefix۰to_val i back move⌝ ∗
            ⌜0 < length move⌝ ∗
            state۰lb γ backs i (Unstable back1 move) ∗
            back ↦ₕ Header §Back 2
        )%I) as (𝑚𝑜𝑣𝑒) "[(-> & #Hstate_at_1) | (%backs & %i & %back & %move & -> & %Hmove & #Hstate_lb & #Hback_header)]".
        { iInv "Hinv" as "(:inv۰inner =2 >)".
          iDestruct (state۰lbｰvalidｰUnstable with "Hstate_auth Hstate_lb_1") as "#[(-> & -> & ->) | (%Hbacks2_lookup & _ & #Hstate_at)]".
          - iDestruct "Hstatus" as "(:inv۰status۰unstable =2 >)".
            iDestruct "Hback2" as "(:back۰model₂ =2)".
            wp۰load.
            iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at_back2_prev") as %(Hbacks2_lookup & _).
            iAssert (back2_prev ↦ₕ Header §Back 2)%I as "#Hback2_prev_header".
            { iDestruct (big_sepM_lookup with "Hbacks") as "(:back۰model₃ =2_prev)"; first done.
              iFrame "#".
            }
            iSplitL. { iFrameSteps. }
            iRight. iSteps.
          - iDestruct (big_sepM_lookup_acc with "Hbacks") as "((:back۰model₃ =1 !=) & Hbacks)"; first done.
            wp۰load.
            iDestruct (pointstoｰagree with "Hback1_index Hback1_index_") as %[= ->%(inj _)].
            iDestruct "H𝑚𝑜𝑣𝑒1" as "#H𝑚𝑜𝑣𝑒1".
            iDestruct ("Hbacks" with "[$]") as "Hbacks".
            iSplitL. { iFrameSteps. }
            iDecompose "H𝑚𝑜𝑣𝑒1"; iSteps.
        }

        + wp۰load.
          wp۰apply ("IHpush_aux" $! back1 i_back1 [] with "[$Hinv $Hstate_at_1] HΦ"); first iSteps.

        + destruct move as [| w move]; first naive_solver lia.

          wp۰apply+ (mpmc_queue_2٠helpｰspec with "[$]"); first done.
          iSteps.

      - iDestruct (inv۰statusｰStable with "Hstatus") as "(%empty1 & -> & (:inv۰status۰stable =1))"; first naive_solver lia.

        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        wp۰apply+ ("IHpush_aux" $! _ _ (v1 :: vs_back1) with "[$Hinv $Hstate_at_1] HΦ").
        iSteps.
    }
  Qed.
  Lemma mpmc_queue_2٠pushｰspec t v ι :
    <<<
      mpmc_queue_2۰inv t ι
    | ∀∀ vs,
      mpmc_queue_2۰model t vs
    >>>
      mpmc_queue_2٠push t v @ ↑ι
    <<<
      mpmc_queue_2۰model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (mpmc_queue_2٠pushｰspecｰaux with "Hinv").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hmodel₁"; iSteps.
  Qed.

  #[local] Lemma mpmc_queue_2٠popｰspecｰaux l γ :
    ⊢ (
      ∀ i_front vs_front,
      <<<
        inv' l γ ∗
        front۰lb γ i_front
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpmc_queue_2٠pop_1 #l (suffix۰to_val i_front vs_front) @ ↑γ.(metadata۰inv)
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
        ⌜i_front ≤ ˖i⌝ ∗
        ⌜1 < length move⌝ ∗
        inv' l γ ∗
        state۰lb γ backs i (Unstable back move) ∗
        back_prev ↦ₕ Header §Back 2
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpmc_queue_2٠pop_2 #l ’Front[ #i_front ] #back (prefix۰to_val i back_prev move) @ ↑γ.(metadata۰inv)
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
        mpmc_queue_2٠pop_3 #l ’Front[ #i_front ] @ ↑γ.(metadata۰inv)
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
        mpmc_queue_2٠pop #l @ ↑γ.(metadata۰inv)
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

      wp۰rec. wp۰pures.
      destruct vs_front as [| v vs_front]; wp۰pures.

      - wp۰bind (_.{back})%E.
        iInv "Hinv" as "(:inv۰inner =1 >)".
        wp۰load.
        iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %Hi_front1.
        iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb_1".

        destruct vs_back1 as [| v vs_back1].

        + iAssert (
            ∃ backs1_prev i1_prev move1,
            back1 ↦ₕ Header §Back 2 ∗
            state۰lb γ backs1_prev i1_prev (Unstable back1 move1)
          )%I as "(%backs1_prev & %i1_prev & %move1 & #Hback1_header & #Hstate_lb_1)".
          { destruct status1 as [empty1 | back1_ move1].
            - iDestruct "Hstatus" as "(:inv۰status۰stable =1)".
              iDestruct (state۰atｰvalid with "Hstate_auth Hstate_at_1") as %(Hbacks1_lookup & _).
              iDestruct (big_sepM_lookup with "Hbacks") as "(:back۰model₃ =1)"; first done.
              iDestruct "H𝑚𝑜𝑣𝑒1" as "(:move۰model₂ =1)".
              iFrame "#".
            - iDestruct "Hstatus" as "(:inv۰status۰unstable =1 lazy=)".
              iDestruct "Hback1" as "(:back۰model₂ =1)".
              iDestruct (state۰lbｰget with "Hstate_auth") as "$".
              iFrame "#".
          }

          iSplitR "HΦ". { iFrameSteps. }
          iSteps.

        + iDestruct (inv۰statusｰStable with "Hstatus") as "(%empty1 & -> & (:inv۰status۰stable =1))"; first naive_solver lia.

          iSplitR "HΦ". { iFrameSteps. }
          iIntros "!> {%- Hfront1 Hi_front1}".

          wp۰pures.
          case_bool_decide as Hif; wp۰pures.

          * assert (length vs_front1 = 0) as ->%nil_length_inv by lia.
            assert (length vs_back1 = 0) as ->%nil_length_inv by lia.
            replace i_front with ˖i1 by lia.
            replace i_front1 with ˖i1 by lia.
            simpl. clear.

            wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
            iInv "Hinv" as "(:inv۰inner =2 >)".
            wp۰cas as _ | (Hcas & -> & ->)%(prefix۰to_valｰinj' _ _ _ _ _ [v]).

            -- iSplitR "HΦ". { iFrameSteps. }
               iSteps.

            -- ospecialize* Hcas; first done. subst i_back2.
               iDestruct (inv۰statusｰStable with "Hstatus") as "(%empty2 & -> & (:inv۰status۰stable =2))"; first naive_solver lia.
               iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %?.
               assert (length vs_front2 = 0) as ->%nil_length_inv by lia.
               replace i_front2 with ˖i2 by lia.
               rewrite reverse_singleton /= in Hvs2. subst vs2.

               iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
               iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
               iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
               iMod ("HΦ" $! (Some _) with "[$Hmodel₁ //] [//]") as "HΦ".

               iSplitR "HΦ".
               { iFrameSteps. iExists _, _, []. iSteps. }
               iSteps.

          * wp۰block back as "#Hback_header" "_" "(Hback_index & Hback_move & _) /=".
            wp۰match.
            wp۰apply (frontｰspec_strong (Some i_front1) (Some i1) with "[$Hinv $Hfront_lb_1 $Hstate_at_1]") as (i_front3 vs_front3) "(#Hfront_lb_3 & %Hi_front3 & (%i3 & %Hi3 & %Hfront3))".
            wp۰equal as _ | (-> & ->)%(inj2 suffix۰to_val _ _ _ []); wp۰pures.
            1: iSteps.

            simpl in Hfront3.
            replace i_front with ˖i1 in * by lia.
            replace i_front1 with ˖i1 in * by lia.
            replace i3 with i1 in * by lia.
            assert (length vs_front1 = 0) as ->%nil_length_inv by lia.
            assert (0 < length vs_back1) as Hvs_back1 by lia.
            clear- Hvs_back1.

            wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
            iInv "Hinv" as "(:inv۰inner =4 >)".
            wp۰cas as _ | (Hcas & -> & ->)%(prefix۰to_valｰinj' _ _ _ _ _ (v :: vs_back1)).

            -- iSplitR "HΦ". { iFrameSteps. }
               iSteps.

            -- ospecialize* Hcas; first done. subst i_back4.
               iDestruct (inv۰statusｰStable with "Hstatus") as "(%empty4 & -> & (:inv۰status۰stable =4))"; first naive_solver lia.
               iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %Hi_front4.
               replace i_front4 with ˖i4 in * by lia.
               destruct empty4; last lia. subst vs_front4.

               iMod (stateｰdestabilize with "Hstate_auth") as "Hstate_auth".
               iDestruct (state۰lbｰget with "Hstate_auth") as "#Hstate_lb_4".
               iSplitR "HΦ".
               { iFrameSteps. iExists _, _, []. iSteps. }
               iIntros "!> {%- Hvs_back1}".

               wp۰apply+ ("IHpop_2" with "[> $Hinv $Hstate_lb_4] HΦ").
               { iSteps.
                 iMod (inv'ｰstate۰at with "Hinv Hstate_at_1") as "(:back۰model₁ =1)".
                 iSteps.
               }

      - wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner =1 >)".
        wp۰cas as _ | (-> & ->)%(inj2 suffix۰to_val _ _ _ (v :: vs_front)).

        + iSplitR "HΦ". { iFrameSteps. }
          iSteps.

        + iDestruct (inv۰statusｰStable with "Hstatus") as "(%empty1 & -> & (:inv۰status۰stable =1))"; first naive_solver lia.
          destruct empty1; first congruence.

          iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" $! (Some _) with "[$Hmodel₁ //] [//]") as "HΦ".

          iMod (frontｰupdate with "Hfront_auth") as "Hfront_auth".
          iSplitR "HΦ".
          { destruct (nil_or_length_pos vs_front) as [-> | Hvs_front].
            1: iMod (stateｰempty with "Hstate_auth") as "Hstate_auth".
            all: iFrameSteps; iPureIntro.
            all: naive_solver lia.
          }
          iSteps.
    }

    { iClear "IHpop_1 IHpop_2".
      iIntros "%i_front %backs %back %i %back_prev %move %Φ (%Hmove & %Hi_front & #Hinv & #Hstate_lb & #Hback_prev_header) HΦ".

      wp۰rec.
      wp۰apply+ (mpmc_queue_2٠revｰspec with "[$]") as "_"; first lia.
      destruct move as [| v move _] using rev_ind; first naive_solver lia.
      rewrite reverse_snoc /=. wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "Hinv_inner".
      iDestruct (inv۰innerｰstrengthen with "Hinv_inner") as "(:inv۰inner =1 >)".
      wp۰cas as _ | (-> & ->)%(inj2 suffix۰to_val _ _ _ []).

      - iSplitR "HΦ".
        { rewrite inv۰statusｰweaken. iFrameSteps. }
        iSteps.

      - rewrite Nat.add_0_r in Hfront1. subst i_front.
        iDestruct (state۰lbｰvalid with "Hstate_auth Hstate_lb") as %(_ & ?).
        replace i1 with i by lia.

        iDestruct (state۰lbｰunstabilized with "Hstate_auth Hstate_lb") as %(-> & _ & ->). lia.
        iDestruct "Hstatus" as "(:inv۰status۰unstable =1 strong= lazy=)".
        rewrite reverse_snoc.

        iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some _) with "[$Hmodel₁ //] [//]") as "HΦ /=".

        iMod (stateｰstabilize with "Hstate_auth") as "(Hstate_auth & _ & #Hstate_at)"; first done.
        iMod (frontｰupdate with "Hfront_auth") as "Hfront_auth".
        iDestruct (big_sepM_insert_2 with "[Hback1] Hbacks") as "Hbacks"; first iFrameSteps.
        iSplitR "HΦ".
        { iFrameSteps; iPureIntro.
          - simpl_length/=. lia.
          - rewrite Hvs_back1 right_id //.
          - simpl_length/= in *. lia.
        }
        iIntros "!> {%}".

        wp۰apply+ (mpmc_queue_2٠finishｰspec with "[$]").
        iSteps.
    }

    { iClear "IHpop_2 IHpop_3 IHpop".
      iIntros "%i_front %Φ #Hinv HΦ".

      wp۰rec.
      wp۰apply+ (frontｰspec with "Hinv") as (i_front1 vs_front1) "#Hfront_lb".
      wp۰equal as _; first iSteps.
      wp۰pures.

      iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
      iApply ("HΦ" $! None with "Hmodel₁ [//]").
    }

    { iClear "IHpop_2 IHpop".
      iIntros "%Φ #Hinv HΦ".

      wp۰rec.
      wp۰apply (frontｰspec with "Hinv").
      iSteps.
    }
  Qed.
  Lemma mpmc_queue_2٠popｰspec t ι :
    <<<
      mpmc_queue_2۰inv t ι
    | ∀∀ vs,
      mpmc_queue_2۰model t vs
    >>>
      mpmc_queue_2٠pop t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          mpmc_queue_2۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          mpmc_queue_2۰model t vs'
      end
    | RET o;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (mpmc_queue_2٠popｰspecｰaux with "Hinv").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hmodel₁"; first iSteps. iIntros (o) "Hmodel₁ !>".
    iExists o. destruct o as [v |]; last iSteps.
    iDestruct "Hmodel₁" as "(%vs' & -> & Hmodel₁)".
    iSteps.
  Qed.
End mpmc_queue_2۰G.

Require zoo_saturn.mpmc_queue_2__opaque.

#[global] Opaque mpmc_queue_2۰inv.
#[global] Opaque mpmc_queue_2۰model.
