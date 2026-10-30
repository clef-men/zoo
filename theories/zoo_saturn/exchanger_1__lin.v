Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.program_logic.identifier.
Require Import zoo.program_logic.tracker.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.exchanger_1.
Require Import zoo.options.

Implicit Type v t : val.
Implicit Type o : option val.
Implicit Type id : identifier.

#[local] Zoo type t :=
  { tracker
  ; exchanger
  }.

#[local] Zoo type event :=
  | Call _
  | Return _.

Please Definition exchanger_1ˡⁱⁿ٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    (𝗽𝗿𝗼𝗽𝗵, exchanger_1٠create ()).

Please Definition exchanger_1ˡⁱⁿ٠exchange : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "id" = Id 𝗶𝗻
    𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "t".<tracker> ‘Call( "id", "v") ⍮
    𝗹𝗲𝘁 "res" = exchanger_1٠exchange "t".<exchanger> "v" 𝗶𝗻
    𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "t".<tracker> ‘Return( "id", "res") ⍮
    "res".

Variant event :=
  | Call id v
  | Lin id1 v1 id2 v2
  | Return id o.
Implicit Type ev : event.

#[local] Definition event۰of_val 𝑒𝑣 :=
  match 𝑒𝑣 with
  | ValBlock _ Tag0 [ValId id; v] =>
      Some $ Call id v
  | ValBlock _ Tag1 [ValId id; 𝑜] =>
      if option۰of_val 𝑜 is Some o then
        Some $ Return id o
      else
        None
  | _ =>
      None
  end.

#[local] Definition trace :=
  list event.
Implicit Type tr : trace.

Please begin.

Section trace۰consistent.
  #[local] Definition event۰basic ev :=
    if ev is Lin _ _ _ _ then
      False
    else
      True.
  #[global] Arguments event۰basic !_ : assert.

  #[local] Instance event۰basicｰdec ev :
    Decision (event۰basic ev).
  Proof.
    refine (
      if ev is Lin _ _ _ _ then
        right _
      else
        left _
    ).
    all: abstract naive.
  Defined.

  #[local] Please Definition trace۰consistent tr trₗ :=
    tr = filter event۰basic trₗ.

  #[local] Lemma trace۰consistentｰnil :
    trace۰consistent [] [].
  Proof.
    done.
  Qed.

  #[local] Lemma trace۰consistentｰappｰcall tr trₗ id v :
    trace۰consistent tr trₗ →
    trace۰consistent (tr ++ [Call id v]) (trₗ ++ [Call id v]).
  Proof.
    intros ->.
    rewrite /trace۰consistent filter_app //.
  Qed.
  #[local] Lemma trace۰consistentｰappｰlin tr trₗ id1 v1 id2 v2 :
    trace۰consistent tr trₗ →
    trace۰consistent tr (trₗ ++ [Lin id1 v1 id2 v2]).
  Proof.
    intros ->.
    rewrite /trace۰consistent filter_app app_nil_r //.
  Qed.
  #[local] Lemma trace۰consistentｰappｰreturn tr trₗ id o :
    trace۰consistent tr trₗ →
    trace۰consistent (tr ++ [Return id o]) (trₗ ++ [Return id o]).
  Proof.
    intros ->.
    rewrite /trace۰consistent filter_app //.
  Qed.
End trace۰consistent.

Please opacify.
Please end.

Variant status :=
  | StatusCall v
  | StatusLin id v
  | StatusReturn.
Implicit Type status : status.

#[local] Definition state :=
  gmap identifier status.
Implicit Type state : state.

Please begin.

Section trace۰interp.
  Variant step : state → event → state → Prop :=
    | stepｰcall state id v state' :
        state !! id = None →
        state' = <[id := StatusCall v]> state →
        step state (Call id v) state'
    | stepｰlin state id1 v1 id2 v2 state' :
        id1 ≠ id2 →
        state !! id1 = Some $ StatusCall v1 →
        state !! id2 = Some $ StatusCall v2 →
        state' = <[id2 := StatusLin id1 v1]> $ <[id1 := StatusLin id2 v2]> state →
        step state (Lin id1 v1 id2 v2) state'
    | stepｰreturnｰSome state id id' v' state' :
        state !! id = Some $ StatusLin id' v' →
        state' = <[id := StatusReturn]> state →
        step state (Return id (Some v')) state'
    | stepｰreturnｰNone state id v state' :
        state !! id = Some $ StatusCall v →
        state' = <[id := StatusReturn]> state →
        step state (Return id None) state'.

  Inductive steps : state → trace → state → Prop :=
    | stepsｰnil state :
        steps state [] state
    | stepsｰcons state1 ev state2 tr state3 :
        step state1 ev state2 →
        steps state2 tr state3 →
        steps state1 (ev :: tr) state3.

  #[local] Lemma stepsｰsnoc state1 tr state2 ev state3 :
    steps state1 tr state2 →
    step state2 ev state3 →
    steps state1 (tr ++ [ev]) state3.
  Proof.
    intros Hsteps Hstep.
    induction Hsteps; eauto using steps.
  Qed.

  #[local] Please Definition trace۰interp tr state :=
    steps ∅ tr state.

  #[local] Lemma trace۰interpｰnil :
    trace۰interp [] ∅.
  Proof.
    constructor.
  Qed.

  #[local] Lemma trace۰interpｰappｰcall tr state id v :
    state !! id = None →
    trace۰interp tr state →
    trace۰interp (tr ++ [Call id v]) (<[id := StatusCall v]> state).
  Proof.
    intros Hstate_lookup Htr.
    eapply stepsｰsnoc. 1: done.
    constructor => //.
  Qed.
  #[local] Lemma trace۰interpｰappｰlin tr state id1 v1 id2 v2 :
    id1 ≠ id2 →
    state !! id1 = Some $ StatusCall v1 →
    state !! id2 = Some $ StatusCall v2 →
    trace۰interp tr state →
    trace۰interp (tr ++ [Lin id1 v1 id2 v2]) (<[id2 := StatusLin id1 v1]> $ <[id1 := StatusLin id2 v2]> state).
  Proof.
    intros Hid Hstate_lookup_1 Hstate_lookup_2 Htr.
    eapply stepsｰsnoc. 1: done.
    constructor => //.
  Qed.
  #[local] Lemma trace۰interpｰappｰreturnｰSome tr state id id' v' :
    state !! id = Some $ StatusLin id' v' →
    trace۰interp tr state →
    trace۰interp (tr ++ [Return id (Some v')]) (<[id := StatusReturn]> state).
  Proof.
    intros Hstate_lookup Htr.
    eapply stepsｰsnoc. 1: done.
    econstructor => //.
  Qed.
  #[local] Lemma trace۰interpｰappｰreturnｰNone tr state id v :
    state !! id = Some $ StatusCall v →
    trace۰interp tr state →
    trace۰interp (tr ++ [Return id None]) (<[id := StatusReturn]> state).
  Proof.
    intros Hstate_lookup Htr.
    eapply stepsｰsnoc. 1: done.
    econstructor => //.
  Qed.
End trace۰interp.

Please opacify.
Please end.

Record exchanger_1ˡⁱⁿ۰name :=
  { exchanger_1ˡⁱⁿ۰name۰tracker : tracker۰name
  ; exchanger_1ˡⁱⁿ۰name۰exchanger : val
  ; exchanger_1ˡⁱⁿ۰name۰state : gname
  }.
Implicit Type γ : exchanger_1ˡⁱⁿ۰name.

#[local] Coercion exchanger_1ˡⁱⁿ۰name۰to_val γ : val :=
  ( γ.(exchanger_1ˡⁱⁿ۰name۰tracker)
  , γ.(exchanger_1ˡⁱⁿ۰name۰exchanger)
  ).

#[local] Definition tracker :=
  {|tracker۰event := event
  ; tracker۰event۰of_val := event۰of_val
  |}.

Class Exchanger1ˡⁱⁿG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] exchanger_1ˡⁱⁿ۰G۰tracker۰G :: TrackerG Σ tracker
  ; #[local] exchanger_1ˡⁱⁿ۰G۰exchanger۰G :: Exchanger1G Σ identifier
  ; #[local] exchanger_1ˡⁱⁿ۰G۰state۰G :: ghost_mapG Σ identifier status
  }.

Definition exchanger_1ˡⁱⁿ۰Σ :=
  #[tracker۰Σ tracker
  ; exchanger_1۰Σ identifier
  ; ghost_mapΣ identifier status
  ].
#[global] Instance subGｰexchanger_1ˡⁱⁿ۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG exchanger_1ˡⁱⁿ۰Σ Σ →
  Exchanger1ˡⁱⁿG Σ.
Proof.
  solve_inG.
Qed.

Section exchanger_1ˡⁱⁿ۰G.
  Context `{exchanger_1ˡⁱⁿ۰G : Exchanger1ˡⁱⁿG Σ}.

  #[local] Definition state۰auth' γ۰state state :=
    ghost_map_auth γ۰state Own state.
  #[local] Definition state۰auth γ state :=
    state۰auth' γ.(exchanger_1ˡⁱⁿ۰name۰state) state.
  #[local] Definition state۰at' γ۰state id status :=
    ghost_map_elem γ۰state id Own status.
  #[local] Definition state۰at γ id status :=
    state۰at' γ.(exchanger_1ˡⁱⁿ۰name۰state) id status.

  #[local] Definition pre γ v id :=
    state۰at γ id (StatusCall v).
  #[local] Instance : CustomIpat "pre" :=
    " Hstate۰at{۰{}}
    ".
  #[local] Definition post γ v id v' id' : iProp Σ :=
    state۰at γ id (StatusLin id' v').
  #[local] Instance : CustomIpat "post" :=
    " Hstate۰at{۰{}}
    ".

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ tr trₗ state,
    tracker۰model tracker γ.(exchanger_1ˡⁱⁿ۰name۰tracker) tr ∗
    ⌜trace۰consistent tr trₗ⌝ ∗
    state۰auth γ state ∗
    ⌜trace۰interp trₗ state⌝ ∗
    ([∗ set] id ∈ dom state, identifier۰model id).
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %tr
      & %trₗ
      & %state
      & >Htracker۰model
      & >%Hconsistent
      & >Hstate۰auth
      & >%Hinterp
      & >Hstate
      )
    ".
  Please Definition exchanger_1ˡⁱⁿ۰inv γ : iProp Σ :=
    exchanger_1۰inv γ.(exchanger_1ˡⁱⁿ۰name۰exchanger) (nroot.@"exchanger") (pre γ) (post γ) ∗
    inv (nroot.@"inv") (inv۰inner γ).
  #[local] Instance : CustomIpat "inv" :=
    " ( #Hexchanger۰inv
      & #Hinv
      )
    ".

  Zoo derive Persistent for exchanger_1ˡⁱⁿ۰inv.

  #[local] Lemma stateｰalloc :
    ⊢ |==>
      ∃ γ۰state,
      state۰auth' γ۰state ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma state۰atｰne γ id1 status1 id2 status2 :
    state۰at γ id1 status1 -∗
    state۰at γ id2 status2 -∗
    ⌜id1 ≠ id2⌝.
  Proof.
    apply ghost_map_elem_ne.
  Qed.
  #[local] Lemma stateｰlookup γ state id status :
    state۰auth γ state -∗
    state۰at γ id status -∗
    ⌜state !! id = Some status⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma stateｰinsert {γ state} id status :
    state !! id = None →
    state۰auth γ state ==∗
      state۰auth γ (<[id := status]> state) ∗
      state۰at γ id status.
  Proof.
    apply ghost_map_insert.
  Qed.
  #[local] Lemma stateｰupdate {γ state id status} status' :
    state۰auth γ state -∗
    state۰at γ id status ==∗
      state۰auth γ (<[id := status']> state) ∗
      state۰at γ id status'.
  Proof.
    apply ghost_map_update.
  Qed.

  Lemma exchanger_1ˡⁱⁿ٠createｰspec :
    {{{
      True
    }}}
      exchanger_1ˡⁱⁿ٠create ()
    {{{
      γ
    , RET γ;
      exchanger_1ˡⁱⁿ۰inv γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply (exchanger_1٠createｰspecｰinit with "[//]") as (exchanger) "Hexchanger۰init".
    wp۰apply (trackerｰwpｰproph with "[//]") as (γ۰tracker) "Htracker۰model".
    wp۰pures.

    iMod stateｰalloc as "(%γ۰state & Hstate۰auth)".

    pose γ :=
      {|exchanger_1ˡⁱⁿ۰name۰tracker := γ۰tracker
      ; exchanger_1ˡⁱⁿ۰name۰exchanger := exchanger
      ; exchanger_1ˡⁱⁿ۰name۰state := γ۰state
      |}.

    iMod (inv_alloc (nroot.@"inv") _ (inv۰inner γ) with "[Htracker۰model Hstate۰auth]") as "#Hinv".
    { iFrame. iExists []. iSteps. iPureIntro.
      apply trace۰interpｰnil.
    }

    iMod (exchanger_1۰initｰtoｰinv (nroot.@"exchanger") (pre γ) (post γ) with "Hexchanger۰init []") as "#Hexchanger۰inv".
    { iIntros "!> !> %v1 %id1 %v2 %id2 (:pre =1) (:pre =2)".
      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (state۰atｰne with "Hstate۰at۰1 Hstate۰at۰2") as %Hid.
      iDestruct (stateｰlookup with "Hstate۰auth Hstate۰at۰1") as %Hstate_lookup_1.
      iDestruct (stateｰlookup with "Hstate۰auth Hstate۰at۰2") as %Hstate_lookup_2.
      iMod (stateｰupdate with "Hstate۰auth Hstate۰at۰1") as "(Hstate۰auth & $)".
      iMod (stateｰupdate with "Hstate۰auth Hstate۰at۰2") as "(Hstate۰auth & $)".
      iSplitL.
      { iFrame. iExists (trₗ ++ [Lin id1 v1 id2 v2]). iSteps; try iPureIntro.
        - apply trace۰consistentｰappｰlin => //.
        - apply trace۰interpｰappｰlin => //.
        - iEval (rewrite dom_insert_lookup_L; first rewrite lookup_insert_ne //).
          iEval (rewrite dom_insert_lookup_L //).
          iFrameSteps.
      }
      iSteps.
    }

    iApply ("HΦ" $! γ).
    iSteps.
  Qed.

  Lemma exchanger_1ˡⁱⁿ٠exchangeｰspec γ v :
    {{{
      exchanger_1ˡⁱⁿ۰inv γ
    }}}
      exchanger_1ˡⁱⁿ٠exchange γ v
    {{{
      o
    , RET o;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
    wp۰pures.

    wp۰bind (𝗿𝗲𝘀𝗼𝗹𝘃𝗲 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰apply (trackerｰwpｰresolve with "Htracker۰model") as "Htracker۰model". 1: done.
    iAssert ⌜state !! id = None⌝%I as %Hstate_lookup.
    { iEval (rewrite eq_None_not_Some). iIntros (Hid%elem_of_dom).
      iDestruct (big_sepS_elem_of with "Hstate") as "Hid!". 1: done.
      iApply (identifier۰modelｰexclusive with "Hid Hid!").
    }
    iMod (stateｰinsert id (StatusCall v) with "Hstate۰auth") as "(Hstate۰auth & Hstate۰at)". 1: done.
    iSplitR "Hstate۰at HΦ".
    { iFrame. iExists (trₗ ++ [Call id v]). iSteps; try iPureIntro.
      - apply trace۰consistentｰappｰcall => //.
      - apply trace۰interpｰappｰcall => //.
      - iEval (rewrite dom_insert_L).
        iApply (big_sepS_insert_2 id with "Hid Hstate").
    }
    iIntros "!> {%}".

    wp۰apply+ (exchanger_1٠exchangeｰspec with "[$Hexchanger۰inv $Hstate۰at]") as ([v' |]) "H".

    - iDestruct "H" as "(%id' & (:post))".

      wp۰pures.

      wp۰bind (𝗿𝗲𝘀𝗼𝗹𝘃𝗲 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰apply (trackerｰwpｰresolve with "Htracker۰model") as "Htracker۰model". 1: done.
      iDestruct (stateｰlookup with "Hstate۰auth Hstate۰at") as %Hstate_lookup.
      iMod (stateｰupdate StatusReturn with "Hstate۰auth Hstate۰at") as "(Hstate۰auth & _)".
      iSplitR "HΦ".
      { iFrame. iExists (trₗ ++ [Return id (Some v')]). iSteps; try iPureIntro.
        - apply trace۰consistentｰappｰreturn => //.
        - eapply trace۰interpｰappｰreturnｰSome => //.
        - iEval (rewrite dom_insert_lookup_L //).
          iFrameSteps.
      }
      iIntros "!> {%}".

      wp۰pures.

      iApply ("HΦ" $! (Some v') with "[//]").

    - iDestruct "H" as "(:pre)".

      wp۰pures.

      wp۰bind (𝗿𝗲𝘀𝗼𝗹𝘃𝗲 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰apply (trackerｰwpｰresolve with "Htracker۰model") as "Htracker۰model". 1: done.
      iDestruct (stateｰlookup with "Hstate۰auth Hstate۰at") as %Hstate_lookup.
      iMod (stateｰupdate StatusReturn with "Hstate۰auth Hstate۰at") as "(Hstate۰auth & _)".
      iSplitR "HΦ".
      { iFrame. iExists (trₗ ++ [Return id None]). iSteps; try iPureIntro.
        - apply trace۰consistentｰappｰreturn => //.
        - eapply trace۰interpｰappｰreturnｰNone => //.
        - iEval (rewrite dom_insert_lookup_L //).
          iFrameSteps.
      }
      iIntros "!> {%}".

      wp۰pures.

      iApply ("HΦ" $! None with "[//]").
  Qed.
End exchanger_1ˡⁱⁿ۰G.

Please opacify.
