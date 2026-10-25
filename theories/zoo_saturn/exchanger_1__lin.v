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

Variant state :=
  | StateCall v
  | StateLin id v
  | StateReturn.
Implicit Type state : state.

#[local] Definition states :=
  gmap identifier state.
Implicit Type states : states.

Please begin.

Section trace۰interp.
  Variant step : states → event → states → Prop :=
    | stepｰcall states id v states' :
        states !! id = None →
        states' = <[id := StateCall v]> states →
        step states (Call id v) states'
    | stepｰlin states id1 v1 id2 v2 states' :
        id1 ≠ id2 →
        states !! id1 = Some $ StateCall v1 →
        states !! id2 = Some $ StateCall v2 →
        states' = <[id2 := StateLin id1 v1]> $ <[id1 := StateLin id2 v2]> states →
        step states (Lin id1 v1 id2 v2) states'
    | stepｰreturnｰSome states id id' v' states' :
        states !! id = Some $ StateLin id' v' →
        states' = <[id := StateReturn]> states →
        step states (Return id (Some v')) states'
    | stepｰreturnｰNone states id v states' :
        states !! id = Some $ StateCall v →
        states' = <[id := StateReturn]> states →
        step states (Return id None) states'.

  Inductive steps : states → trace → states → Prop :=
    | stepsｰnil states :
        steps states [] states
    | stepsｰcons states1 ev states2 tr states3 :
        step states1 ev states2 →
        steps states2 tr states3 →
        steps states1 (ev :: tr) states3.

  #[local] Lemma stepsｰsnoc states1 tr states2 ev states3 :
    steps states1 tr states2 →
    step states2 ev states3 →
    steps states1 (tr ++ [ev]) states3.
  Proof.
    intros Hsteps Hstep.
    induction Hsteps; eauto using steps.
  Qed.

  #[local] Please Definition trace۰interp tr states :=
    steps ∅ tr states.

  #[local] Lemma trace۰interpｰnil :
    trace۰interp [] ∅.
  Proof.
    constructor.
  Qed.

  #[local] Lemma trace۰interpｰappｰcall tr states id v :
    states !! id = None →
    trace۰interp tr states →
    trace۰interp (tr ++ [Call id v]) (<[id := StateCall v]> states).
  Proof.
    intros Hstates_lookup Htr.
    eapply stepsｰsnoc. 1: done.
    constructor => //.
  Qed.
  #[local] Lemma trace۰interpｰappｰlin tr states id1 v1 id2 v2 :
    id1 ≠ id2 →
    states !! id1 = Some $ StateCall v1 →
    states !! id2 = Some $ StateCall v2 →
    trace۰interp tr states →
    trace۰interp (tr ++ [Lin id1 v1 id2 v2]) (<[id2 := StateLin id1 v1]> $ <[id1 := StateLin id2 v2]> states).
  Proof.
    intros Hid Hstates_lookup_1 Hstates_lookup_2 Htr.
    eapply stepsｰsnoc. 1: done.
    constructor => //.
  Qed.
  #[local] Lemma trace۰interpｰappｰreturnｰSome tr states id id' v' :
    states !! id = Some $ StateLin id' v' →
    trace۰interp tr states →
    trace۰interp (tr ++ [Return id (Some v')]) (<[id := StateReturn]> states).
  Proof.
    intros Hstates_lookup Htr.
    eapply stepsｰsnoc. 1: done.
    econstructor => //.
  Qed.
  #[local] Lemma trace۰interpｰappｰreturnｰNone tr states id v :
    states !! id = Some $ StateCall v →
    trace۰interp tr states →
    trace۰interp (tr ++ [Return id None]) (<[id := StateReturn]> states).
  Proof.
    intros Hstates_lookup Htr.
    eapply stepsｰsnoc. 1: done.
    econstructor => //.
  Qed.
End trace۰interp.

Please opacify.
Please end.

Record exchanger_1ˡⁱⁿ۰name :=
  { exchanger_1ˡⁱⁿ۰name۰tracker : tracker۰name
  ; exchanger_1ˡⁱⁿ۰name۰exchanger : val
  ; exchanger_1ˡⁱⁿ۰name۰states : gname
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
  ; #[local] exchanger_1ˡⁱⁿ۰G۰states۰G :: ghost_mapG Σ identifier state
  }.

Definition exchanger_1ˡⁱⁿ۰Σ :=
  #[tracker۰Σ tracker
  ; exchanger_1۰Σ identifier
  ; ghost_mapΣ identifier state
  ].
#[global] Instance subGｰexchanger_1ˡⁱⁿ۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG exchanger_1ˡⁱⁿ۰Σ Σ →
  Exchanger1ˡⁱⁿG Σ.
Proof.
  solve_inG.
Qed.

Section exchanger_1ˡⁱⁿ۰G.
  Context `{exchanger_1ˡⁱⁿ۰G : Exchanger1ˡⁱⁿG Σ}.

  #[local] Definition states۰auth' γ۰states states :=
    ghost_map_auth γ۰states Own states.
  #[local] Definition states۰auth γ states :=
    states۰auth' γ.(exchanger_1ˡⁱⁿ۰name۰states) states.
  #[local] Definition states۰at' γ۰states id state :=
    ghost_map_elem γ۰states id Own state.
  #[local] Definition states۰at γ id state :=
    states۰at' γ.(exchanger_1ˡⁱⁿ۰name۰states) id state.

  #[local] Definition pre γ v id :=
    states۰at γ id (StateCall v).
  #[local] Instance : CustomIpat "pre" :=
    " Hstates۰at{۰{}}
    ".
  #[local] Definition post γ v id v' id' : iProp Σ :=
    states۰at γ id (StateLin id' v').
  #[local] Instance : CustomIpat "post" :=
    " Hstates۰at{۰{}}
    ".

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ tr trₗ states,
    tracker۰model tracker γ.(exchanger_1ˡⁱⁿ۰name۰tracker) tr ∗
    ⌜trace۰consistent tr trₗ⌝ ∗
    states۰auth γ states ∗
    ⌜trace۰interp trₗ states⌝ ∗
    ([∗ set] id ∈ dom states, identifier۰model id).
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %tr
      & %trₗ
      & %states
      & >Htracker۰model
      & >%Hconsistent
      & >Hstates۰auth
      & >%Hinterp
      & >Hids
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

  #[local] Lemma statesｰalloc :
    ⊢ |==>
      ∃ γ۰states,
      states۰auth' γ۰states ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma states۰atｰne γ id1 state1 id2 state2 :
    states۰at γ id1 state1 -∗
    states۰at γ id2 state2 -∗
    ⌜id1 ≠ id2⌝.
  Proof.
    apply ghost_map_elem_ne.
  Qed.
  #[local] Lemma statesｰlookup γ states id state :
    states۰auth γ states -∗
    states۰at γ id state -∗
    ⌜states !! id = Some state⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma statesｰinsert {γ states} id state :
    states !! id = None →
    states۰auth γ states ==∗
      states۰auth γ (<[id := state]> states) ∗
      states۰at γ id state.
  Proof.
    apply ghost_map_insert.
  Qed.
  #[local] Lemma statesｰupdate {γ states id state} state' :
    states۰auth γ states -∗
    states۰at γ id state ==∗
      states۰auth γ (<[id := state']> states) ∗
      states۰at γ id state'.
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

    iMod statesｰalloc as "(%γ۰states & Hstates۰auth)".

    pose γ :=
      {|exchanger_1ˡⁱⁿ۰name۰tracker := γ۰tracker
      ; exchanger_1ˡⁱⁿ۰name۰exchanger := exchanger
      ; exchanger_1ˡⁱⁿ۰name۰states := γ۰states
      |}.

    iMod (inv_alloc (nroot.@"inv") _ (inv۰inner γ) with "[Htracker۰model Hstates۰auth]") as "#Hinv".
    { iFrame. iExists []. iSteps. iPureIntro.
      apply trace۰interpｰnil.
    }

    iMod (exchanger_1۰initｰtoｰinv (nroot.@"exchanger") (pre γ) (post γ) with "Hexchanger۰init []") as "#Hexchanger۰inv".
    { iIntros "!> !> %v1 %id1 %v2 %id2 (:pre =1) (:pre =2)".
      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (states۰atｰne with "Hstates۰at۰1 Hstates۰at۰2") as %Hid.
      iDestruct (statesｰlookup with "Hstates۰auth Hstates۰at۰1") as %Hstates_lookup_1.
      iDestruct (statesｰlookup with "Hstates۰auth Hstates۰at۰2") as %Hstates_lookup_2.
      iMod (statesｰupdate with "Hstates۰auth Hstates۰at۰1") as "(Hstates۰auth & $)".
      iMod (statesｰupdate with "Hstates۰auth Hstates۰at۰2") as "(Hstates۰auth & $)".
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
    iAssert ⌜states !! id = None⌝%I as %Hstates_lookup.
    { iEval (rewrite eq_None_not_Some). iIntros (Hid%elem_of_dom).
      iDestruct (big_sepS_elem_of with "Hids") as "Hid!". 1: done.
      iApply (identifier۰modelｰexclusive with "Hid Hid!").
    }
    iMod (statesｰinsert id (StateCall v) with "Hstates۰auth") as "(Hstates۰auth & Hstates۰at)". 1: done.
    iSplitR "Hstates۰at HΦ".
    { iFrame. iExists (trₗ ++ [Call id v]). iSteps; try iPureIntro.
      - apply trace۰consistentｰappｰcall => //.
      - apply trace۰interpｰappｰcall => //.
      - iEval (rewrite dom_insert_L).
        iApply (big_sepS_insert_2 id with "Hid Hids").
    }
    iIntros "!> {%}".

    wp۰apply+ (exchanger_1٠exchangeｰspec with "[$Hexchanger۰inv $Hstates۰at]") as ([v' |]) "H".

    - iDestruct "H" as "(%id' & (:post))".

      wp۰pures.

      wp۰bind (𝗿𝗲𝘀𝗼𝗹𝘃𝗲 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰apply (trackerｰwpｰresolve with "Htracker۰model") as "Htracker۰model". 1: done.
      iDestruct (statesｰlookup with "Hstates۰auth Hstates۰at") as %Hstates_lookup.
      iMod (statesｰupdate StateReturn with "Hstates۰auth Hstates۰at") as "(Hstates۰auth & _)".
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
      iDestruct (statesｰlookup with "Hstates۰auth Hstates۰at") as %Hstates_lookup.
      iMod (statesｰupdate StateReturn with "Hstates۰auth Hstates۰at") as "(Hstates۰auth & _)".
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
