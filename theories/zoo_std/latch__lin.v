Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.gmap.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.auth_nat_add.
Require Import zoo.program_logic.identifier.
Require Import zoo.program_logic.tracker.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_std.latch.
Require Import zoo.options.

Implicit Type i cnt : nat.
Implicit Type v t : val.
Implicit Type id : identifier.

#[local] Zoo type t :=
  { tracker
  ; latch
  }.

#[local] Zoo type event :=
  | Call _
  | Return _.

Please Definition latchˡⁱⁿ٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    (𝗽𝗿𝗼𝗽𝗵, latch٠create "sz").

Please Definition latchˡⁱⁿ٠wait : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "id" = Id 𝗶𝗻
    𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "t".<tracker> ‘Call( "id" ) ⍮
    𝗹𝗲𝘁 "res" = latch٠wait "t".<latch> 𝗶𝗻
    𝗿𝗲𝘀𝗼𝗹𝘃𝗲 𝘀𝗸𝗶𝗽 "t".<tracker> ‘Return( "id" ) ⍮
    "res".

Variant event :=
  | Call id
  | Lin
  | Return id.
Implicit Type ev : event.

#[local] Please derive EqDecision for event.

#[local] Definition event۰of_val 𝑒𝑣 :=
  match 𝑒𝑣 with
  | ValBlock _ Tag0 [ValId id] =>
      Some $ Call id
  | ValBlock _ Tag1 [ValId id] =>
      Some $ Return id
  | _ =>
      None
  end.

#[local] Definition trace :=
  list event.
Implicit Type tr : trace.

Please begin.

Section trace۰consistent.
  #[local] Definition event۰basic ev :=
    ev ≠ Lin.

  #[local] Please Definition trace۰consistent tr trₗ :=
    tr = filter event۰basic trₗ.

  #[local] Lemma trace۰consistentｰnil :
    trace۰consistent [] [].
  Proof.
    done.
  Qed.

  #[local] Lemma trace۰consistentｰappｰcall tr trₗ id :
    trace۰consistent tr trₗ →
    trace۰consistent (tr ++ [Call id]) (trₗ ++ [Call id]).
  Proof.
    intros ->.
    rewrite /trace۰consistent filter_app //.
  Qed.
  #[local] Lemma trace۰consistentｰappｰlin tr trₗ :
    trace۰consistent tr trₗ →
    trace۰consistent tr (trₗ ++ [Lin]).
  Proof.
    intros ->.
    rewrite /trace۰consistent filter_app app_nil_r //.
  Qed.
  #[local] Lemma trace۰consistentｰappｰreturn tr trₗ id :
    trace۰consistent tr trₗ →
    trace۰consistent (tr ++ [Return id]) (trₗ ++ [Return id]).
  Proof.
    intros ->.
    rewrite /trace۰consistent filter_app //.
  Qed.
End trace۰consistent.

Please opacify.
Please end.

Variant status :=
  | StatusCall
  | StatusLin
  | StatusReturn.
Implicit Type status : status.

#[local] Abbreviation state := (
  gmap identifier status
).
Implicit Type state : state.

Please begin.

Section trace۰interp.
  Context (sz : nat).

  Variant step : state → event → state → Prop :=
    | stepｰcall state id state' :
        state !! id = None →
        state' = <[id := StatusCall]> state →
        step state (Call id) state'
    | stepｰlin state state' :
        size state = sz →
        map_Forall (const (.= StatusCall)) state →
        state' = gset_to_gmap StatusLin (dom state) →
        step state Lin state'
    | stepｰreturn state id state' :
        state !! id = Some StatusLin →
        state' = <[id := StatusReturn]> state →
        step state (Return id) state'.

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

  #[local] Lemma trace۰interpｰappｰcall tr state id :
    state !! id = None →
    trace۰interp tr state →
    trace۰interp (tr ++ [Call id]) (<[id := StatusCall]> state).
  Proof.
    intros Hstate_lookup Htr.
    eapply stepsｰsnoc. 1: done.
    constructor => //.
  Qed.
  #[local] Lemma trace۰interpｰappｰlin tr state ids :
    size state = sz →
    map_Forall (const (.= StatusCall)) state →
    dom state = ids →
    trace۰interp tr state →
    trace۰interp (tr ++ [Lin]) (gset_to_gmap StatusLin ids).
  Proof.
    intros Hsize Hstate <- Htr.
    eapply stepsｰsnoc. 1: done.
    constructor => //.
  Qed.
  #[local] Lemma trace۰interpｰappｰreturn tr state id :
    state !! id = Some StatusLin →
    trace۰interp tr state →
    trace۰interp (tr ++ [Return id]) (<[id := StatusReturn]> state).
  Proof.
    intros Hstate_lookup Htr.
    eapply stepsｰsnoc. 1: done.
    econstructor => //.
  Qed.
End trace۰interp.

Please opacify.
Please end.

Record latchˡⁱⁿ۰name :=
  { latchˡⁱⁿ۰name۰size : nat
  ; latchˡⁱⁿ۰name۰tracker : tracker۰name
  ; latchˡⁱⁿ۰name۰latch : latch۰name
  ; latchˡⁱⁿ۰name۰state : gname
  ; latchˡⁱⁿ۰name۰tokens : gname
  }.
Implicit Type γ : latchˡⁱⁿ۰name.

#[local] Coercion latchˡⁱⁿ۰name۰to_val γ : val :=
  ( γ.(latchˡⁱⁿ۰name۰tracker)
  , γ.(latchˡⁱⁿ۰name۰latch)
  ).

#[local] Definition tracker :=
  {|tracker۰event := event
  ; tracker۰event۰of_val := event۰of_val
  |}.

Class LatchˡⁱⁿG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] latchˡⁱⁿ۰G۰tracker۰G :: TrackerG Σ tracker
  ; #[local] latchˡⁱⁿ۰G۰latch۰G :: LatchG Σ identifier
  ; #[local] latchˡⁱⁿ۰G۰state۰G :: ghost_mapG Σ identifier status
  ; #[local] latchˡⁱⁿ۰G۰tokens۰G :: AuthNatAddG Σ
  }.

Definition latchˡⁱⁿ۰Σ :=
  #[tracker۰Σ tracker
  ; latch۰Σ identifier
  ; ghost_mapΣ identifier status
  ; auth_nat_add۰Σ
  ].
#[global] Instance subGｰlatchˡⁱⁿ۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG latchˡⁱⁿ۰Σ Σ →
  LatchˡⁱⁿG Σ.
Proof.
  solve_inG.
Qed.

Section latchˡⁱⁿ۰G.
  Context `{latchˡⁱⁿ۰G : LatchˡⁱⁿG Σ}.

  #[local] Definition state۰auth' γ۰state state :=
    ghost_map_auth γ۰state Own state.
  #[local] Definition state۰auth γ state :=
    state۰auth' γ.(latchˡⁱⁿ۰name۰state) state.
  #[local] Definition state۰at' γ۰state id status :=
    ghost_map_elem γ۰state id Own status.
  #[local] Definition state۰at γ id status :=
    state۰at' γ.(latchˡⁱⁿ۰name۰state) id status.

  #[local] Definition tokens۰auth' γ۰tokens cnt :=
    auth_nat_add۰auth γ۰tokens Own cnt.
  #[local] Definition tokens۰auth γ :=
    tokens۰auth' γ.(latchˡⁱⁿ۰name۰tokens).
  #[local] Definition tokens۰frag' γ۰tokens :=
    auth_nat_add۰frag γ۰tokens 1.
  #[local] Definition tokens۰frag γ :=
    tokens۰frag' γ.(latchˡⁱⁿ۰name۰tokens).

  #[local] Definition pre γ i id :=
    state۰at γ id StatusCall.
  #[local] Instance : CustomIpat "pre" :=
    " Hstate۰at{۰{}}
    ".
  #[local] Definition post γ i id (ids : gmap nat identifier) : iProp Σ :=
    state۰at γ id StatusLin.
  #[local] Instance : CustomIpat "post" :=
    " Hstate۰at{۰{}}
    ".

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ tr trₗ state cnt,
    tracker۰model tracker γ.(latchˡⁱⁿ۰name۰tracker) tr ∗
    ⌜trace۰consistent tr trₗ⌝ ∗
    state۰auth γ state ∗
    ⌜trace۰interp γ.(latchˡⁱⁿ۰name۰size) trₗ state⌝ ∗
    ([∗ set] id ∈ dom state, identifier۰model id) ∗
    tokens۰auth γ cnt ∗
    ⌜(size state + cnt)%nat = γ.(latchˡⁱⁿ۰name۰size)⌝.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %tr
      & %trₗ
      & %state
      & %cnt
      & >Htracker۰model
      & >%Hconsistent
      & >Hstate۰auth
      & >%Hinterp
      & >Hstate
      & >Htokens۰auth
      & >%Hsize
      )
    ".
  Please Definition latchˡⁱⁿ۰inv γ : iProp Σ :=
    latch۰inv γ.(latchˡⁱⁿ۰name۰latch) γ.(latchˡⁱⁿ۰name۰size) (pre γ) (post γ) ∗
    inv nroot (inv۰inner γ).
  #[local] Instance : CustomIpat "inv" :=
    " ( #Hlatch۰inv
      & #Hinv
      )
    ".

  Please Definition latchˡⁱⁿ۰token γ : iProp Σ :=
    ∃ i,
    latch۰token γ.(latchˡⁱⁿ۰name۰latch) i ∗
    tokens۰frag γ.
  #[local] Instance : CustomIpat "token" :=
    " ( %i
      & Htoken
      & Htokens۰frag
      )
    ".

  #[local] Zoo derive Timeless for tokens۰auth.

  Zoo derive Persistent for latchˡⁱⁿ۰inv.

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

  #[local] Lemma tokensｰalloc sz :
    ⊢ |==>
      ∃ γ_tokens,
      tokens۰auth' γ_tokens sz ∗
      [∗ list] _ ∈ seq 0 sz, tokens۰frag' γ_tokens.
  Proof.
    iMod auth_nat_addｰalloc as (γ_tokens) "($ & Hfrag)".
    iDestruct (auth_nat_add۰fragｰatomize with "Hfrag") as "$" => //.
  Qed.
  #[local] Lemma tokens۰fragｰvalid γ cnt :
    tokens۰auth γ cnt -∗
    tokens۰frag γ -∗
    ⌜0 < cnt⌝.
  Proof.
    apply auth_nat_add۰fragｰvalid.
  Qed.
  #[local] Lemma tokensｰdecr γ cnt :
    tokens۰auth γ cnt -∗
    tokens۰frag γ ==∗
    tokens۰auth γ (cnt - 1).
  Proof.
    apply auth_nat_addｰupdateｰdecrease.
  Qed.

  Opaque tokens۰auth'.
  Opaque tokens۰frag'.

  Lemma latchˡⁱⁿ٠createｰspec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      latchˡⁱⁿ٠create #sz
    {{{
      γ
    , RET γ;
      latchˡⁱⁿ۰inv γ ∗
      [∗ list] _ ∈ seq 0 ₊sz, latchˡⁱⁿ۰token γ
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.
    wp۰apply (latch٠createｰspecｰinit with "[//]") as (latch) "(Hlatch۰init & Htokens)". 1: done.
    wp۰apply (trackerｰwpｰproph with "[//]") as (γ۰tracker) "Htracker۰model".
    wp۰pures.

    iMod stateｰalloc as "(%γ۰state & Hstate۰auth)".
    iMod (tokensｰalloc ₊sz) as "(%γ۰tokens & Htokens۰auth & Htokens۰frags)".

    pose γ :=
      {|latchˡⁱⁿ۰name۰size := ₊sz
      ; latchˡⁱⁿ۰name۰tracker := γ۰tracker
      ; latchˡⁱⁿ۰name۰latch := latch
      ; latchˡⁱⁿ۰name۰state := γ۰state
      ; latchˡⁱⁿ۰name۰tokens := γ۰tokens
      |}.

    iMod (inv_alloc nroot _ (inv۰inner γ) with "[Htracker۰model Hstate۰auth Htokens۰auth]") as "#Hinv".
    { iFrame. iExists []. iSteps. iPureIntro.
      apply trace۰interpｰnil.
    }

    iMod (latch۰initｰtoｰinv (pre γ) (post γ) with "Hlatch۰init []") as "#Hlatch۰inv".
    { iIntros "%ids %Hids Hstate۰ats".
      iInv "Hinv" as "(:inv۰inner)".

      iAssert ⌜map_inj ids⌝%I as %Hinj.
      { iIntros (i1 i2 id Hlookup_1 Hlookup_2).
        destruct_decide (i1 = i2). 1: done.
        iDestruct (big_sepM_delete _ _ i1 with "Hstate۰ats") as "(Hstate۰at۰1 & Hstate۰ats)". 1: done.
        iDestruct (big_sepM_delete _ _ i2 with "Hstate۰ats") as "(Hstate۰at۰2 & Hstate۰ats)".
        { rewrite lookup_delete_ne //. }
        iDestruct (state۰atｰne with "Hstate۰at۰1 Hstate۰at۰2") as %[] => //.
      }

      iApply big_sepMｰmap_img in "Hstate۰ats".
      iApply big_sepM_gset_to_gmap in "Hstate۰ats".
      iDestruct (ghost_map_lookup_big with "Hstate۰auth Hstate۰ats") as %<-%map_subseteq_size_eq; last first.
      { rewrite sizeｰgset_to_gmap sizeｰmap_imgｰinj // -(size_dom ids) Hids size_set_seq. simp. lia. }
      iMod (ghost_map_update_big _ (gset_to_gmap StatusLin $ map_img ids) with "Hstate۰auth Hstate۰ats") as "(Hstate۰auth & Hstate۰ats)". 1: set_solver.
      iEval (rewrite mapｰunionｰdom; first set_solver) in "Hstate۰auth".
      iApply big_sepM_gset_to_gmap in "Hstate۰ats".
      iApply (big_sepSｰmap_img ids) in "Hstate۰ats". 1: done.
      { apply symmetry, sizeｰmap_imgｰinj => //. }

      rewrite sizeｰgset_to_gmap sizeｰmap_imgｰinj // in Hsize.
      assert (cnt = 0) as ->.
      { rewrite -size_dom Hids size_set_seq in Hsize. simp. lia. }

      iSplitR "Hstate۰ats".
      { iFrame. iExists (trₗ ++ [Lin]).
        iEval (rewrite !dom_gset_to_gmap) in "Hstate" |- *.
        iFrameSteps; iPureIntro.
        - apply trace۰consistentｰappｰlin => //.
        - eapply trace۰interpｰappｰlin => //.
          { rewrite sizeｰgset_to_gmap sizeｰmap_imgｰinj //. simp. lia. }
          { apply map_Forallｰgset_to_gmap => //. }
          { rewrite dom_gset_to_gmap //. }
        - rewrite sizeｰgset_to_gmap sizeｰmap_imgｰinj //.
      }
      iSteps.
    }

    iApply ("HΦ" $! γ).
    iSteps.
    iDestruct (big_sepL_sep_2 with "Htokens Htokens۰frags") as "Htokens".
    iApply (big_sepL_impl with "Htokens").
    iSteps.
  Qed.

  Lemma latchˡⁱⁿ٠exchangeｰspec γ v :
    {{{
      latchˡⁱⁿ۰inv γ ∗
      latchˡⁱⁿ۰token γ
    }}}
      latchˡⁱⁿ٠wait γ
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:token)) HΦ".

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
    iMod (stateｰinsert id StatusCall with "Hstate۰auth") as "(Hstate۰auth & Hstate۰at)". 1: done.
    iSplitR "Htoken Hstate۰at HΦ".
    { iDestruct (big_sepS_insert_2 id with "Hid Hstate") as "Hstate".
      iEval (erewrite <- dom_insert_L) in "Hstate".
      iDestruct (tokens۰fragｰvalid with "Htokens۰auth Htokens۰frag") as %Hcnt.
      iMod (tokensｰdecr with "Htokens۰auth Htokens۰frag") as "Htokens۰auth".
      iFrame. iExists (trₗ ++ [Call id]). iSteps; try iPureIntro.
      - apply trace۰consistentｰappｰcall => //.
      - apply trace۰interpｰappｰcall => //.
      - rewrite map_size_insert_None //. lia.
    }
    iIntros "!> {%}".

    wp۰apply+ (latch٠waitｰspec with "[$Hlatch۰inv $Htoken $Hstate۰at]") as (ids) "(%Hxs_lookup & %Hxs_dom & (:post))".
    wp۰pures.

    wp۰bind (𝗿𝗲𝘀𝗼𝗹𝘃𝗲 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰apply (trackerｰwpｰresolve with "Htracker۰model") as "Htracker۰model". 1: done.
    iDestruct (stateｰlookup with "Hstate۰auth Hstate۰at") as %Hstate_lookup.
    iMod (stateｰupdate StatusReturn with "Hstate۰auth Hstate۰at") as "(Hstate۰auth & _)".
    iSplitR "HΦ".
    { iFrame. iExists (trₗ ++ [Return id]). iSteps; try iPureIntro.
      - apply trace۰consistentｰappｰreturn => //.
      - eapply trace۰interpｰappｰreturn => //.
      - iEval (rewrite dom_insert_lookup_L //).
        iSteps. iPureIntro.
        rewrite map_size_insert_Some //.
    }
    iIntros "!> {%}".

    iSteps.
  Qed.
End latchˡⁱⁿ۰G.

Please opacify.
