From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  function
  list
  relations.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.auth_nat_max
  lib.auth_twins
  lib.excl
  lib.mono_gmultiset
  lib.mono_list
  lib.twins.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  identifier
  prophet_identifier
  prophet_multi.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  array
  domain
  option.
From zoo_saturn Require Export
  base
  ws_deque_1__code.
From zoo_saturn Require Import
  ws_deque_1__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types front back : nat.
Implicit Types l : location.
Implicit Types id : prophet_id.
Implicit Types v t : val.
Implicit Types us vs ws hist priv : list val.
Implicit Types datas : gmultiset val.
Implicit Types past prophs : list prophet_identifier.(prophet_typed_type).
Implicit Types pasts prophss : nat → list prophet_identifier.(prophet_typed_type).

Inductive state :=
  | Empty
  | Nonempty
  | Emptyish
  | Superempty.
Implicit Types state : state.

#[local] Instance state_inhabited : Inhabited state :=
  populate Empty.

Inductive stability :=
  | Stable
  | Unstable.
Implicit Types stable : stability.

#[local] Instance stability_inhabited : Inhabited stability :=
  populate Stable.

Class WsQueue1G Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_deque_1_G_prophet_G :: ProphetMultiG Σ prophet_identifier ;
  #[local] ws_deque_1_G_model_G :: AuthTwinsG Σ (leibnizO (list val)) suffix ;
  #[local] ws_deque_1_G_owner_G :: TwinsG Σ (leibnizO (stability * nat * val * nat)) ;
  #[local] ws_deque_1_G_front_G :: AuthNatMaxG Σ ;
  #[local] ws_deque_1_G_history_G :: MonoListG Σ val ;
  #[local] ws_deque_1_G_winner_G :: TwinsG Σ (natO * leibnizO (option val) * ▶ ∙) ;
  #[local] ws_deque_1_G_datas_G :: MonoGmultisetG Σ val ;
}.

Definition ws_deque_1_Σ := #[
  prophet_multi_Σ prophet_identifier ;
  auth_twins_Σ (leibnizO (list val)) suffix ;
  twins_Σ (leibnizO (stability * nat * val * nat)) ;
  auth_nat_max_Σ ;
  mono_list_Σ val ;
  twins_Σ (natO * leibnizO (option val) * ▶ ∙) ;
  mono_gmultiset_Σ val
].
#[global] Instance subG_ws_deque_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_deque_1_Σ Σ →
  WsQueue1G Σ .
Proof.
  solve_inG.
Qed.

#[local] Definition min_capacity :=
  val_to_nat ws_deque_1_min_capacity.
#[local] Lemma min_capacity_nonzero :
  0 < min_capacity.
Proof.
  compute_done.
Qed.
#[local] Hint Resolve
  min_capacity_nonzero
: core.
#[local] Lemma ws_deque_1_min_capacity :
  ws_deque_1_min_capacity = #min_capacity.
Proof.
  done.
Qed.
Opaque ws_deque_1__code.ws_deque_1_min_capacity.
Opaque min_capacity.

Section ws_deque_1_G.
  Context `{ws_deque_1_G : WsQueue1G Σ}.

  Implicit Types P : iProp Σ.

  Record metadata := {
    metadata_inv : namespace ;
    metadata_prophet : prophet_id ;
    metadata_prophet_name : prophet_multi_name ;
    metadata_model : auth_twins_name ;
    metadata_owner : gname ;
    metadata_front : gname ;
    metadata_history : gname ;
    metadata_winner : gname ;
    metadata_datas : gname ;
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
    auth_twins_twin1 _ γ_model vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata_model).
  #[local] Definition model₂' γ_model vs :=
    auth_twins_twin2 _ γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata_model).

  #[local] Definition owner₁' γ_owner γ_model stable back data cap ws : iProp Σ :=
    twins_twin1 (twins_G := ws_deque_1_G_owner_G) γ_owner (DfracOwn 1) (stable, back, data, cap) ∗
    auth_twins_auth _ γ_model ws.
  #[local] Definition owner₁ γ :=
    owner₁' γ.(metadata_owner) γ.(metadata_model).
  #[local] Instance : CustomIpatFormat "owner₁" :=
    " ( Howner₁{_{}} &
        Hmodel_auth{_{}}
      )
    ".
  #[local] Definition owner₂' γ_owner stable back data cap :=
    twins_twin2 (twins_G := ws_deque_1_G_owner_G) γ_owner (stable, back, data, cap).
  #[local] Definition owner₂ γ :=
    owner₂' γ.(metadata_owner).

  #[local] Definition front_auth' γ_front :=
    auth_nat_max_auth γ_front (DfracOwn 1).
  #[local] Definition front_auth γ :=
    front_auth' γ.(metadata_front).
  #[local] Definition front_lb γ :=
    auth_nat_max_lb γ.(metadata_front).

  #[local] Definition history_auth' γ_history :=
    mono_list_auth γ_history (DfracOwn 1).
  #[local] Definition history_auth γ :=
    history_auth' γ.(metadata_history).
  #[local] Definition history_at γ :=
    mono_list_at γ.(metadata_history).

  #[local] Definition winner_pop' γ_winner front (data : option val) P : iProp Σ :=
    twins_twin1 γ_winner (DfracOwn 1) (front, data, Next P).
  #[local] Definition winner_pop γ :=
    winner_pop' γ.(metadata_winner).
  #[local] Definition winner_steal' γ_winner front (data : option val) P :=
    twins_twin2 γ_winner (front, data, Next P).
  #[local] Definition winner_steal γ :=
    winner_steal' γ.(metadata_winner).
  #[local] Definition winner γ : iProp Σ :=
    ∃ front data P1 P2,
    winner_pop γ front data P1 ∗
    winner_steal γ front data P2.
  #[local] Instance : CustomIpatFormat "winner" :=
    " ( %front_winner &
        %data_winner &
        %P1 &
        %P2 &
        Hwinner_pop{_{}} &
        Hwinner_steal{_{}}
      )
    ".

  #[local] Definition datas_auth' γ_datas :=
    mono_gmultiset_auth γ_datas (DfracOwn 1).
  #[local] Definition datas_auth γ :=
    datas_auth' γ.(metadata_datas).
  #[local] Definition datas_elem' γ_datas :=
    mono_gmultiset_elem γ_datas.
  #[local] Definition datas_elem γ :=
    datas_elem' γ.(metadata_datas).

  #[local] Definition data_model data : iProp Σ :=
    ∃ cap i vs,
    array_cslice data cap i DfracDiscarded vs ∗
    ⌜0 < cap⌝ ∗
    ⌜length vs = cap⌝.
  #[local] Instance : CustomIpatFormat "data_model" :=
    " ( %cap_data{} &
        %i_data{} &
        %vs_data{} &
        Hdata{}_cslice &
        %Hcap_data{} &
        %Hvs_data{}
      )
    ".

  #[local] Definition winner_au γ front P : iProp Σ :=
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑γ.(metadata_inv), ∅ <{
      ∀∀ v vs',
      ⌜vs = v :: vs'⌝ ∗
      model₁ γ vs' ∗
      history_at γ front v
    , COMM
      P
    }>.
  #[local] Definition winner_model_1 γ front data data_winner : iProp Σ :=
      ⌜data = data_winner⌝
    ∨ ∃ cap_winner v,
      array_cslice data_winner cap_winner front DfracDiscarded [v]  ∗
      history_at γ front v.
  #[local] Instance : CustomIpatFormat "winner_model_1" :=
    " [ ->
      | ( %cap &
          %v_ &
          Hdata_cslice &
          Hhistory_at_
        )
      ]
    ".
  #[local] Definition winner_model_2 γ front data data_winner P : iProp Σ :=
    winner_steal γ front (Some data_winner) P ∗
    winner_model_1 γ front data data_winner.
  #[local] Instance : CustomIpatFormat "winner_model_2" :=
    " ( Hwinner_steal{_{!}} &
        Hwinner
      )
    ".
  #[local] Definition winner_pending_1 γ front data data_winner P id : iProp Σ :=
    winner_model_2 γ front data data_winner P ∗
    identifier_model' id ∗
    winner_au γ front P.
  #[local] Instance : CustomIpatFormat "winner_pending_1" :=
    " ( (:winner_model_2 {/!/}) &
        Hid{_{!}} &
        HP{}
      )
    ".
  #[local] Definition winner_pending_2 γ front data id : iProp Σ :=
    ∃ data_winner P,
    winner_pending_1 γ front data data_winner P id.
  #[local] Instance : CustomIpatFormat "winner_pending_2" :=
    " ( %data_winner &
        %P{} &
        (:winner_pending_1 {//} {/!/})
      )
    ".
  #[local] Definition winner_linearized_1 γ front data data_winner P : iProp Σ :=
    winner_model_2 γ front data data_winner P ∗
    P.
  #[local] Instance : CustomIpatFormat "winner_linearized_1" :=
    " ( (:winner_model_2 {/!/}) &
        HP{}
      )
    ".
  #[local] Definition winner_linearized_2 γ front data P : iProp Σ :=
    ∃ data_winner,
    winner_linearized_1 γ front data data_winner P.
  #[local] Instance : CustomIpatFormat "winner_linearized_2" :=
    " ( %data_winner &
        (:winner_linearized_1 {//} {/!/})
      )
    ".

  #[local] Definition inv_state_empty γ stable front back hist : iProp Σ :=
    ⌜stable = Stable⌝ ∗
    ⌜front = back⌝ ∗
    ⌜length hist = front⌝ ∗
    winner γ.
  #[local] Instance : CustomIpatFormat "inv_state_empty" :=
    " ( { {lazy}{>}%
        ; {lazy}%
        ; {>}->
        ; ->
        } &
        {>;}-> &
        {>;}%Hhist{} &
        Hwinner
      )
    ".
  #[local] Definition inv_state_nonempty γ stable front back data hist vs prophs : iProp Σ :=
    ⌜stable = Stable⌝ ∗
    ⌜front < back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant vs) ∗
    ( winner γ
    ∨ match prophs with
      | [] =>
          False
      | id :: _ =>
          winner_pending_2 γ front data id
      end
    ).
  #[local] Instance : CustomIpatFormat "inv_state_nonempty" :=
    " ( { {lazy}{>}%
        ; {lazy}%
        ; {>}->
        ; ->
        } &
        {>;}% &
        {>;}%Hhist{} &
        #Hhistory_at_front{} &
        Hwinner
      )
    ".
  #[local] Definition inv_state_nonempty_steal γ state stable front back data hist vs prophs data_winner P : iProp Σ :=
    ⌜state = Nonempty⌝ ∗
    ⌜stable = Stable⌝ ∗
    ⌜front < back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant vs) ∗
    match prophs with
    | [] =>
        False
    | id :: _ =>
        winner_pending_1 γ front data data_winner P id
    end.
  #[local] Instance : CustomIpatFormat "inv_state_nonempty_steal" :=
    " ( {>;}-> &
        { {lazy}{>}%
        ; {lazy}%
        ; {>}->
        ; ->
        } &
        {>;}% &
        {>;}%Hhist{} &
        #Hhistory_at_front{} &
        Hwinner
      )
    ".
  #[local] Definition inv_state_emptyish γ stable front back data hist priv : iProp Σ :=
    ∃ P,
    ⌜stable = Unstable⌝ ∗
    ⌜front = back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant priv) ∗
    ( winner_pop γ front None P
    ∨ winner_linearized_2 γ front data P
    ).
  #[local] Instance : CustomIpatFormat "inv_state_emptyish" :=
    " ( %P_ &
        { {lazy}{>}%
        ; {lazy}%
        ; {>}->
        ; ->
        } &
        {>;}-> &
        {>;}%Hhist{} &
        #Hhistory_at_front{} &
        Hwinner
      )
    ".
  #[local] Definition inv_state_emptyish_pop γ state stable front back hist priv P : iProp Σ :=
    ⌜state = Emptyish⌝ ∗
    ⌜stable = Unstable⌝ ∗
    ⌜front = back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant priv) ∗
    winner_pop γ front None P.
  #[local] Instance : CustomIpatFormat "inv_state_emptyish_pop" :=
    " ( {>;}-> &
        { {lazy}{>}%
        ; {lazy}%
        ; {>}->
        ; ->
        } &
        {>;}-> &
        {>;}%Hhist{} &
        #Hhistory_at_front{} &
        Hwinner_pop
      )
    ".
  #[local] Definition inv_state_emptyish_steal γ state stable front back data hist priv data_winner P : iProp Σ :=
    ⌜state = Emptyish⌝ ∗
    ⌜stable = Unstable⌝ ∗
    ⌜front = back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant priv) ∗
    winner_linearized_1 γ front data data_winner P.
  #[local] Instance : CustomIpatFormat "inv_state_emptyish_steal" :=
    " ( {>;}-> &
        { {lazy}{>}%
        ; {lazy}%
        ; {>}->
        ; ->
        } &
        {>;}-> &
        {>;}%Hhist{} &
        #Hhistory_at_front{} &
        (:winner_linearized_1)
      )
    ".
  #[local] Definition inv_state_superempty γ stable front back hist : iProp Σ :=
    ⌜stable = Unstable⌝ ∗
    ⌜front = S back⌝ ∗
    ⌜length hist = front⌝ ∗
    winner γ.
  #[local] Instance : CustomIpatFormat "inv_state_superempty" :=
    " ( { {lazy}{>}%
        ; {lazy}%
        ; {>}->
        ; ->
        } &
        {>;}-> &
        {>;}%Hhist{} &
        Hwinner
      )
    ".
  #[local] Definition inv_state γ state stable front back data hist vs priv prophs : iProp Σ :=
    match state with
    | Empty =>
        inv_state_empty γ stable front back hist
    | Nonempty =>
        inv_state_nonempty γ stable front back data hist vs prophs
    | Emptyish =>
        inv_state_emptyish γ stable front back data hist priv
    | Superempty =>
        inv_state_superempty γ stable front back hist
    end.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ state stable front back data cap hist vs priv datas pasts prophss,
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    l.[data] ↦ data ∗
    owner₂ γ stable back data cap ∗
    front_auth γ front ∗
    ⌜0 < front⌝ ∗
    model₂ γ vs ∗
    ⌜length vs = back - front⌝ ∗
    array_cslice data cap front (DfracOwn (1/2)) (vs ++ priv) ∗
    ⌜0 < cap⌝ ∗
    ⌜(length vs + length priv)%nat = cap⌝ ∗
    history_auth γ hist ∗
    datas_auth γ ({[+data+]} ⊎ datas) ∗
    ([∗ mset] data ∈ datas, data_model data) ∗
    prophet_multi_model prophet_identifier γ.(metadata_prophet) γ.(metadata_prophet_name) pasts prophss ∗
    ⌜∀ i, front ≤ i → pasts i = []⌝ ∗
    inv_state γ state stable front back data hist vs priv (prophss front).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    " ( %state{} &
        %stable{} &
        %front{} &
        %back{} &
        %data{} &
        %cap{} &
        %hist{} &
        %vs{} &
        %priv{} &
        %datas{} &
        %pasts{} &
        %prophss{} &
        >Hl_front &
        >Hl_back &
        >Hl_data &
        >Howner₂ &
        >Hfront_auth &
        >%Hfront{} &
        >Hmodel₂ &
        >%Hvs{} &
        >Hdata{}_cslice₁ &
        >%Hcap{} &
        >%Hdata{} &
        >Hhistory_auth &
        >Hdatas_auth &
        >Hdatas &
        >Hprophet_model &
        >%Hpasts{} &
        Hstate
      )
    ".
  #[local] Definition inv' l γ : iProp Σ :=
    l.[proph] ↦□ #γ.(metadata_prophet) ∗
    inv γ.(metadata_inv) (inv_inner l γ).
  #[local] Instance : CustomIpatFormat "inv'" :=
    " ( #Hl_proph &
        #Hinv
      )
    ".
  Definition ws_deque_1_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata_inv)⌝ ∗
    meta l nroot γ ∗
    inv' l γ.
  #[local] Instance : CustomIpatFormat "inv" :=
    " ( %l &
        %γ &
        -> &
        -> &
        #Hmeta &
        (:inv')
      )
    ".

  Definition ws_deque_1_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    " ( %l{;_} &
        %γ{;_} &
        %Heq{} &
        Hmeta_{} &
        Hmodel₁{_{}}
      )
    ".

  #[local] Definition owner' γ stable back data cap ws i us : iProp Σ :=
    owner₁ γ stable back data cap ws ∗
    array_cslice data cap i (DfracOwn (1/2)) us ∗
    ⌜0 < cap⌝ ∗
    ⌜length us = cap⌝.
  #[local] Instance : CustomIpatFormat "owner'" :=
    " ( Howner₁{_{}} &
        Hdata_cslice₂{_{}} &
        { {!} _
        ; %Hcap{}
        ; %Hcap
        } &
        { {!} _
        ; %Hus{}
        ; %Hus
        }
      )
    ".
  Definition ws_deque_1_owner t ws : iProp Σ :=
    ∃ l γ back data cap i us,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    owner' γ Stable back data cap ws i us.
  #[local] Instance : CustomIpatFormat "owner" :=
    " ( %l{;_} &
        %γ{;_} &
        %back{} &
        %data{} &
        %cap{} &
        %i{} &
        %us{} &
        %Heq{} &
        Hmeta_{} &
        Howner{_{}}
      )
    ".

  #[global] Instance ws_deque_1_model_timeless t vs :
    Timeless (ws_deque_1_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_deque_1_owner_timeless t ws :
    Timeless (ws_deque_1_owner t ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_deque_1_inv_persistent t ι :
    Persistent (ws_deque_1_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_owner_alloc data cap :
    ⊢ |==>
      ∃ γ_model γ_owner,
      model₁' γ_model [] ∗
      model₂' γ_model [] ∗
      owner₁' γ_owner γ_model Stable 1 data cap [] ∗
      owner₂' γ_owner Stable 1 data cap.
  Proof.
    iMod (auth_twins_alloc _ (auth_twins_G := ws_deque_1_G_model_G)) as "(%γ_model & Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iMod (twins_alloc' (twins_G := ws_deque_1_G_owner_G)) as "(%γ_owner & Howner₁ & Howner₂)".
    iFrameSteps.
  Qed.
  #[local] Lemma model₁_valid γ stable back data cap ws vs :
    owner₁ γ stable back data cap ws -∗
    model₁ γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner₁) Hmodel₁".
    iDestruct (auth_twins_valid_1 with "Hmodel_auth Hmodel₁") as %H.
    rewrite preorder_rtc in H. iSteps.
  Qed.
  #[local] Lemma model₁_exclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply auth_twins_twin1_exclusive.
  Qed.
  #[local] Lemma model₂_valid γ stable back data cap ws vs :
    owner₁ γ stable back data cap ws -∗
    model₂ γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner₁) Hmodel₁".
    iDestruct (auth_twins_valid_2 with "Hmodel_auth Hmodel₁") as %H.
    rewrite preorder_rtc in H. iSteps.
  Qed.
  #[local] Lemma model_agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: auth_twins_agree_L.
  Qed.
  #[local] Lemma model_owner₁_agree γ stable back data cap ws vs1 vs2 :
    owner₁ γ stable back data cap ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
      ⌜vs1 `suffix_of` ws⌝ ∗
      ⌜vs1 = vs2⌝.
  Proof.
    iIntros "Howner₁ Hmodel₁ Hmodel₂".
    iDestruct (model₁_valid with "Howner₁ Hmodel₁") as %Hsuffix.
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iSteps.
  Qed.
  #[local] Lemma model_empty {γ stable back data cap ws vs1 vs2} :
    owner₁ γ stable back data cap ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      owner₁ γ stable back data cap [] ∗
      model₁ γ [] ∗
      model₂ γ [].
  Proof.
    iIntros "(:owner₁) Hmodel₁ Hmodel₂".
    iMod (auth_twins_update_auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma model_push {γ stable back data cap ws vs1 vs2} v :
    owner₁ γ stable back data cap ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      owner₁ γ stable back data cap (vs1 ++ [v]) ∗
      model₁ γ (vs1 ++ [v]) ∗
      model₂ γ (vs1 ++ [v]).
  Proof.
    iIntros "(:owner₁) Hmodel₁ Hmodel₂".
    iMod (auth_twins_update_auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma model_steal γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ (tail vs1) ∗
      model₂ γ (tail vs1).
  Proof.
    apply: auth_twins_update_twins_L.
    rewrite preorder_rtc. apply suffix_tail. done.
  Qed.
  #[local] Lemma model_pop γ stable back data cap ws vs1 vs2 :
    owner₁ γ stable back data cap ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      owner₁ γ stable back data cap (removelast vs1) ∗
      model₁ γ (removelast vs1) ∗
      model₂ γ (removelast vs1).
  Proof.
    iIntros "(:owner₁) Hmodel₁ Hmodel₂".
    iMod (auth_twins_update_auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma model_pop' γ stable back data cap ws vs1 v vs2 :
    owner₁ γ stable back data cap ws -∗
    model₁ γ (vs1 ++ [v]) -∗
    model₂ γ vs2 ==∗
      owner₁ γ stable back data cap vs1 ∗
      model₁ γ vs1 ∗
      model₂ γ vs1.
  Proof.
    rewrite -{2 3 4}(removelast_last vs1 v).
    apply model_pop.
  Qed.

  #[local] Lemma owner₁_exclusive γ stable1 back1 data1 cap1 ws1 stable2 back2 data2 cap2 ws2 :
    owner₁ γ stable1 back1 data1 cap1 ws1 -∗
    owner₁ γ stable2 back2 data2 cap2 ws2 -∗
    False.
  Proof.
    iIntros "(:owner₁ =1) (:owner₁ =2)".
    iApply (twins_twin1_exclusive with "Howner₁_1 Howner₁_2").
  Qed.
  #[local] Lemma owner_agree γ stable1 back1 data1 cap1 ws stable2 back2 data2 cap2 :
    owner₁ γ stable1 back1 data1 cap1 ws -∗
    owner₂ γ stable2 back2 data2 cap2 -∗
      ⌜stable1 = stable2⌝ ∗
      ⌜back1 = back2⌝ ∗
      ⌜data1 = data2⌝ ∗
      ⌜cap1 = cap2⌝.
  Proof.
    iIntros "(:owner₁) Howner₂".
    iDestruct (twins_agree_L with "Howner₁ Howner₂") as %[= <- <- <- <-].
    iSteps.
  Qed.
  #[local] Lemma owner₁_update γ stable back data cap ws vs :
    owner₁ γ stable back data cap ws -∗
    model₁ γ vs -∗
    model₂ γ vs ==∗
      owner₁ γ stable back data cap vs ∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    iIntros "(:owner₁) Hmodel₁ Hmodel₂".
    iMod (auth_twins_update_auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "($ & $ & $)".
    iSteps.
  Qed.
  #[local] Lemma owner_update {γ stable1 back1 data1 cap1 ws stable2 back2 data2 cap2} stable back data cap :
    owner₁ γ stable1 back1 data1 cap1 ws -∗
    owner₂ γ stable2 back2 data2 cap2 ==∗
      owner₁ γ stable back data cap ws ∗
      owner₂ γ stable back data cap.
  Proof.
    iIntros "(:owner₁) Howner₂".
    iMod (twins_update with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
    iSteps.
  Qed.

  #[local] Lemma front_alloc :
    ⊢ |==>
      ∃ γ_front,
      front_auth' γ_front 1.
  Proof.
    apply auth_nat_max_alloc.
  Qed.
  #[local] Lemma front_lb_get γ front :
    front_auth γ front ⊢
    front_lb γ front.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma front_lb_le {γ front} front' :
    front' ≤ front →
    front_lb γ front ⊢
    front_lb γ front'.
  Proof.
    apply auth_nat_max_lb_le.
  Qed.
  #[local] Lemma front_lb_valid γ front1 front2 :
    front_auth γ front1 -∗
    front_lb γ front2 -∗
    ⌜front2 ≤ front1⌝.
  Proof.
    apply auth_nat_max_lb_valid.
  Qed.
  #[local] Lemma front_update γ front :
    front_auth γ front ⊢ |==>
    front_auth γ (S front).
  Proof.
    apply auth_nat_max_update; first lia.
  Qed.

  #[local] Lemma history_alloc :
    ⊢ |==>
      ∃ γ_hist,
      history_auth' γ_hist [()%V].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma history_at_get {γ hist v} i :
    i = length hist →
    history_auth γ (hist ++ [v]) ⊢
    history_at γ i v.
  Proof.
    intros ->.
    apply mono_list_at_get, list_lookup_middle. done.
  Qed.
  #[local] Lemma history_at_lookup γ hist i v :
    history_auth γ hist -∗
    history_at γ i v -∗
    ⌜hist !! i = Some v⌝.
  Proof.
    apply mono_list_at_valid.
  Qed.
  #[local] Lemma history_at_agree γ i v1 v2 :
    history_at γ i v1 -∗
    history_at γ i v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply mono_list_at_agree.
  Qed.
  #[local] Lemma history_update {γ hist} i v :
    i = length hist →
    history_auth γ hist ⊢ |==>
      history_auth γ (hist ++ [v]) ∗
      history_at γ i v.
  Proof.
    iIntros (->) "Hauth".
    iMod (mono_list_update_snoc with "Hauth") as "Hauth".
    iDestruct (history_at_get with "Hauth") as "#Hat"; first done.
    iSteps.
  Qed.

  #[local] Lemma winner_alloc :
    ⊢ |==>
      ∃ γ_winner,
      winner_pop' γ_winner 1 None True ∗
      winner_steal' γ_winner 1 None True.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma winner_pop_exclusive γ front1 data1 P1 front2 data2 P2 :
    winner_pop γ front1 data1 P1 -∗
    winner_pop γ front2 data2 P2 -∗
    False.
  Proof.
    apply twins_twin1_exclusive.
  Qed.
  #[local] Lemma winner_pop_exclusive' γ front data P :
    winner_pop γ front data P -∗
    winner γ -∗
    False.
  Proof.
    iIntros "Hwinner_pop_1 (:winner =2)".
    iApply (winner_pop_exclusive with "Hwinner_pop_1 Hwinner_pop_2").
  Qed.
  #[local] Lemma winner_steal_exclusive γ front1 data1 P1 front2 data2 P2 :
    winner_steal γ front1 data1 P1 -∗
    winner_steal γ front2 data2 P2 -∗
    False.
  Proof.
    apply twins_twin2_exclusive.
  Qed.
  #[local] Lemma winner_steal_exclusive' γ front data P :
    winner_steal γ front data P -∗
    winner γ -∗
    False.
  Proof.
    iIntros "Hwinner_steal_1 (:winner =2)".
    iApply (winner_steal_exclusive with "Hwinner_steal_1 Hwinner_steal_2").
  Qed.
  #[local] Lemma winner_agree γ front1 data1 P1 front2 data2 P2 :
    winner_pop γ front1 data1 P1 -∗
    winner_steal γ front2 data2 P2 -∗
      ⌜front1 = front2⌝ ∗
      ⌜data1 = data2⌝ ∗
      ▷ (P1 ≡ P2).
  Proof.
    iIntros "Hwinner_pop Hwinner_steal".
    iDestruct (twins_agree with "Hwinner_pop Hwinner_steal") as "#Heq".
    rewrite !prod_equivI /= !discrete_eq_1.
    iDestruct "Heq" as "(($ & $) & $)".
  Qed.
  #[local] Lemma winner_update' {γ front1 data1 P1 front2 data2 P2} front data :
    winner_pop γ front1 data1 P1 -∗
    winner_steal γ front2 data2 P2 ==∗
      winner_pop γ front data P1 ∗
      winner_steal γ front data P2.
  Proof.
    iIntros "Hwinner_pop Hwinner_steal".
    iDestruct (winner_agree with "Hwinner_pop Hwinner_steal") as "#(_ & _ & Heq)".
    iApply (twins_update_equivI with "Hwinner_pop Hwinner_steal").
    rewrite -later_equivI prod_equivI /=. auto.
  Qed.
  #[local] Lemma winner_update {γ front1 data1 P1 front2 data2 P2} front data P :
    winner_pop γ front1 data1 P1 -∗
    winner_steal γ front2 data2 P2 ==∗
      winner_pop γ front data P ∗
      winner_steal γ front data P.
  Proof.
    apply twins_update.
  Qed.

  #[local] Lemma datas_alloc data :
    ⊢ |==>
      ∃ γ_datas,
      datas_auth' γ_datas ({[+data+]} ⊎ ∅).
  Proof.
    apply mono_gmultiset_alloc.
  Qed.
  #[local] Lemma datas_elem_get γ data datas :
    datas_auth γ ({[+data+]} ⊎ datas) ⊢
    datas_elem γ data.
  Proof.
    apply mono_gmultiset_elem_get; first set_solver.
  Qed.
  #[local] Lemma datas_elem_valid γ data1 datas data2 :
    datas_auth γ ({[+data1+]} ⊎ datas) -∗
    datas_elem γ data2 -∗
    ⌜data1 = data2 ∨ data2 ∈ datas⌝.
  Proof.
    iIntros "Hauth Helem".
    iDestruct (mono_gmultiset_elem_valid with "Hauth Helem") as %?. set_solver.
  Qed.
  #[local] Lemma datas_insert {γ datas} data :
    datas_auth γ datas ⊢ |==>
    datas_auth γ ({[+data+]} ⊎ datas).
  Proof.
    apply mono_gmultiset_insert.
  Qed.

  Opaque owner₁'.

  Lemma ws_deque_1_model_exclusive t vs1 vs2 :
    ws_deque_1_model t vs1 -∗
    ws_deque_1_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  #[local] Lemma owner'_rebase {γ stable back data cap ws i1 us} i2 :
    owner' γ stable back data cap ws i1 us ⊢
      ∃ us,
      owner' γ stable back data cap ws i2 us.
  Proof.
    iIntros "(:owner')".
    iDestruct (array_cslice_rebase i2 with "Hdata_cslice₂") as "(%us' & %n & -> & Hdata_cslice₂ & _)"; [done.. |].
    iSteps. simpl_length.
  Qed.

  #[local] Lemma array_cslice_reshape {data cap back dq us} front :
    0 < cap →
    length us = cap →
    front ≤ back →
    back ≤ front + cap →
    array_cslice data cap back dq us ⊢
      ∃ vs priv,
      ⌜(front + length vs)%nat = back⌝ ∗
      ⌜(length vs + length priv)%nat = cap⌝ ∗
      array_cslice data cap front dq (vs ++ priv) ∗
      ( array_cslice data cap front dq (vs ++ priv) -∗
        array_cslice data cap back dq us
      ).
  Proof.
    iIntros "%Hcap %Hus % % Hdata_cslice".

    destruct_decide (back = front + cap) as Hback.

    - iDestruct (array_cslice_shift_left' front with  "Hdata_cslice") as "Hdata_cslice"; [lia.. |].
      iExists us, []. rewrite app_nil_r. iSteps as "Hdata_cslice".
      iApply (array_cslice_shift_right' with "Hdata_cslice"); first done.

    - iDestruct (array_cslice_rotation_left_small_1' front (back - front) with "Hdata_cslice") as "Hdata_cslice"; [lia.. |].
      iFrame. iSteps as_anon / as_anon / as "Hdata_cslice".
      1,2: iPureIntro; simpl_length; lia.
      iDestruct (array_cslice_rotation_right_small_1' back (back - front) with "Hdata_cslice") as "Hdata_cslice"; [simpl_length; lia.. |].
      rewrite rotation_add; first lia.
      rewrite rotation_length //; first lia.
  Qed.

  Lemma ws_deque_1_owner_exclusive t ws1 ws2 :
    ws_deque_1_owner t ws1 -∗
    ws_deque_1_owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". subst t. injection Heq2 as <-.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct "Howner_1" as "(:owner' =1)".
    iDestruct "Howner_2" as "(:owner' =2)".
    iApply (owner₁_exclusive with "Howner₁_1 Howner₁_2").
  Qed.
  Lemma ws_deque_1_owner_model t ws vs :
    ws_deque_1_owner t ws -∗
    ws_deque_1_model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model)". subst t. injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_") as %->.
    iDestruct "Howner_1" as "(:owner' =1)".
    iApply (model₁_valid with "Howner₁_1 Hmodel₁").
  Qed.

  #[local] Lemma inv_state_Stable γ state front data back hist vs priv prophs :
    length vs = back - front →
    inv_state γ state Stable front back data hist vs priv prophs ⊢
      ⌜state = Empty ∨ state = Nonempty⌝ ∗
      ⌜front ≤ back⌝.
  Proof.
    iIntros "%Hvs Hstate".
    destruct state.
    - iDestruct "Hstate" as "(:inv_state_empty lazy=)".
      iSteps.
    - iDestruct "Hstate" as "(:inv_state_nonempty lazy=)".
      iSteps.
    - iDestruct "Hstate" as "(:inv_state_emptyish lazy=)". done.
    - iDestruct "Hstate" as "(:inv_state_superempty lazy=)". done.
  Qed.
  #[local] Lemma inv_state_Unstable γ state front back data hist vs priv prophs :
    inv_state γ state Unstable front back data hist vs priv prophs ⊢
      ⌜state = Emptyish ∨ state = Superempty⌝ ∗
      ⌜front = back ∨ front = S back⌝.
  Proof.
    iIntros "Hstate".
    destruct state.
    - iDestruct "Hstate" as "(:inv_state_empty lazy=)". done.
    - iDestruct "Hstate" as "(:inv_state_nonempty lazy=)". done.
    - iDestruct "Hstate" as "(:inv_state_emptyish lazy=)".
      iSteps.
    - iDestruct "Hstate" as "(:inv_state_superempty lazy=)".
      iSteps.
  Qed.
  #[local] Lemma inv_state_Nonempty γ state stable front back data hist vs priv prophs :
    front < back →
    inv_state γ state stable front back data hist vs priv prophs ⊢
    ⌜state = Nonempty⌝.
  Proof.
    iIntros "% Hstate".
    destruct state.
    - iDestruct "Hstate" as "(:inv_state_empty)". lia.
    - done.
    - iDestruct "Hstate" as "(:inv_state_emptyish)". lia.
    - iDestruct "Hstate" as "(:inv_state_superempty)". lia.
  Qed.
  #[local] Lemma inv_state_Superempty γ state front back data hist vs priv prophs :
    back < front →
    inv_state γ state Unstable front back data hist vs priv prophs -∗
    ⌜state = Superempty⌝.
  Proof.
    iIntros "% Hstate".
    destruct state.
    - iDestruct "Hstate" as "(:inv_state_empty lazy=)". done.
    - iDestruct "Hstate" as "(:inv_state_nonempty lazy=)". done.
    - iDestruct "Hstate" as "(:inv_state_emptyish lazy=)". lia.
    - done.
  Qed.
  #[local] Lemma inv_state_winner_pop γ state stable front1 back data1 hist vs priv prophs front2 data2 P :
    inv_state γ state stable front1 back data1 hist vs priv prophs -∗
    winner_pop γ front2 (Some data2) P -∗
      ∃ P_,
      ⌜front1 = front2⌝ ∗
      ▷ (P ≡ P_) ∗
      ( inv_state_nonempty_steal γ state stable front2 back data1 hist vs prophs data2 P_
      ∨ inv_state_emptyish_steal γ state stable front2 back data1 hist priv data2 P_
      ) ∗
      winner_model_1 γ front2 data1 data2 ∗
      winner_pop γ front2 (Some data2) P.
  Proof.
    iIntros "Hstate Hwinner_pop".
    destruct state.
    - iDestruct "Hstate" as "(:inv_state_empty)".
      iDestruct "Hwinner" as "(:winner =3)".
      iDestruct (winner_pop_exclusive with "Hwinner_pop Hwinner_pop_3") as %[].
    - iDestruct "Hstate" as "(:inv_state_nonempty)".
      iDestruct "Hwinner" as "[(:winner =3) | Hwinner]".
      + iDestruct (winner_pop_exclusive with "Hwinner_pop Hwinner_pop_3") as %[].
      + destruct prophs as [| id prophs]; first done.
        iDestruct "Hwinner" as "(:winner_pending_2 =_)".
        iDestruct (winner_agree with "Hwinner_pop Hwinner_steal") as "#(<- & %Heq & $)". injection Heq as <-.
        iSteps.
    - iDestruct "Hstate" as "(:inv_state_emptyish)".
      iDestruct "Hwinner" as "[Hwinner_pop_ | (:winner_linearized_2)]".
      + iDestruct (winner_pop_exclusive with "Hwinner_pop Hwinner_pop_") as %[].
      + iDestruct (winner_agree with "Hwinner_pop Hwinner_steal") as "#(<- & %Heq & $)". injection Heq as <-.
        iSteps.
    - iDestruct "Hstate" as "(:inv_state_superempty)".
      iDestruct "Hwinner" as "(:winner =3)".
      iDestruct (winner_pop_exclusive with "Hwinner_pop Hwinner_pop_3") as %[].
  Qed.
  #[local] Lemma inv_state_winner_steal γ state stable front2 back data1 hist vs priv prophs front1 data2 P :
    inv_state γ state stable front1 back data1 hist vs priv prophs -∗
    winner_steal γ front2 data2 P -∗
      ∃ P_,
      ⌜front1 = front2⌝ ∗
      ▷ (P_ ≡ P) ∗
      inv_state_emptyish_pop γ state stable front2 back hist priv P_ ∗
      winner_steal γ front2 data2 P.
  Proof.
    iIntros "Hstate Hwinner_steal".
    destruct state.
    - iDestruct "Hstate" as "(:inv_state_empty)".
      iDestruct "Hwinner" as "(:winner =3)".
      iDestruct (winner_steal_exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
    - iDestruct "Hstate" as "(:inv_state_nonempty)".
      destruct prophs as [| id prophs].
      + iDestruct "Hwinner" as "[(:winner =3) | []]".
        iDestruct (winner_steal_exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
      + iDestruct "Hwinner" as "[(:winner =3) | (:winner_pending_2 =_ !=)]".
        * iDestruct (winner_steal_exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
        * iDestruct (winner_steal_exclusive with "Hwinner_steal Hwinner_steal_") as %[].
    - iDestruct "Hstate" as "(:inv_state_emptyish)".
      iDestruct "Hwinner" as "[Hwinner_pop | (:winner_linearized_2 !=)]".
      + iDestruct (winner_agree with "Hwinner_pop Hwinner_steal") as "#(<- & _ & $)".
        iSteps.
      + iDestruct (winner_steal_exclusive with "Hwinner_steal Hwinner_steal_") as %[].
    - iDestruct "Hstate" as "(:inv_state_superempty)".
      iDestruct "Hwinner" as "(:winner =3)".
      iDestruct (winner_steal_exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
  Qed.

  Lemma ws_deque_1_create_spec ι :
    {{{
      True
    }}}
      ws_deque_1_create ()
    {{{ t,
      RET t;
      ws_deque_1_inv t ι ∗
      ws_deque_1_model t [] ∗
      ws_deque_1_owner t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_apply (prophet_multi_wp_proph with "[//]") as (pid γ_prophet prophss) "Hprophet_model".

    rewrite ws_deque_1_min_capacity.
    wp_apply (array_unsafe_make_spec with "[//]") as (data) "Hdata_model"; first done.
    iEval (rewrite Nat2Z.id) in "Hdata_model".
    iDestruct (array_model_to_cslice with "Hdata_model") as "Hdata_cslice".
    iEval (simpl_length) in "Hdata_cslice".
    iDestruct (array_cslice_to_inv with "Hdata_cslice") as "#Hdata_inv".
    iDestruct (array_cslice_rotation_right_0 1 with "Hdata_cslice") as "Hdata_cslice"; [done.. |].
    iEval (rewrite rotation_replicate) in "Hdata_cslice".
    iDestruct "Hdata_cslice" as "(Hdata_cslice₁ & Hdata_cslice₂)".

    wp_block l as "Hmeta" "(Hl_front & Hl_back & Hl_data & Hl_proph & _)".
    iMod (pointsto_persist with "Hl_proph") as "#Hl_proph".

    iMod model_owner_alloc as "(%γ_model & %γ_owner & Hmodel₁ & Hmodel₂ & Howner₁ & Howner₂)".
    iMod front_alloc as "(%γ_front & Hfront_auth)".
    iMod history_alloc as "(%γ_history & Hhist_auth)".
    iMod winner_alloc as "(%γ_winner & Hwinner_pop & Hwinner_steal)".
    iMod (datas_alloc data) as "(%γ_datas & Hdatas_auth)".

    set γ := {|
      metadata_inv := ι ;
      metadata_prophet := pid ;
      metadata_prophet_name := γ_prophet ;
      metadata_model := γ_model ;
      metadata_owner := γ_owner ;
      metadata_front := γ_front ;
      metadata_history := γ_history ;
      metadata_winner := γ_winner ;
      metadata_datas := γ_datas ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Howner₁ Hdata_cslice₂"; last iFrameSteps.
    iExists l, γ. iStep 4.
    iApply inv_alloc.
    iExists Empty, Stable, 1, 1, data, min_capacity, [()%V], [], (replicate min_capacity ()%V), ∅, (λ _, []), prophss.
    rewrite big_sepMS_empty. iFrameSteps.
  Qed.

  #[local] Lemma front_spec l γ :
    {{{
      inv' l γ
    }}}
      (#l).{front}
    {{{ front,
      RET #front;
      front_lb γ front
    }}}.
  Proof.
    iIntros "%Φ (:inv') HΦ".

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_1".
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma front_spec_owner_Stable l γ back data cap ws :
    {{{
      inv' l γ ∗
      owner₁ γ Stable back data cap ws
    }}}
      (#l).{front}
    {{{ front,
      RET #front;
      owner₁ γ Stable back data cap ws ∗
      front_lb γ front ∗
      ⌜front ≤ back⌝
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Howner₁) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
    iDestruct (inv_state_Stable with "Hstate") as "#(_ & %)"; first done.
    iSplitR "Howner₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma front_spec_owner_Unstable l γ back data cap ws :
    {{{
      inv' l γ ∗
      owner₁ γ Unstable back data cap ws
    }}}
      (#l).{front}
    {{{ front,
      RET #front;
      owner₁ γ Unstable back data cap ws ∗
      front_lb γ front ∗
      ⌜front = back ∨ front = S back⌝
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Howner₁) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
    iDestruct (inv_state_Unstable with "Hstate") as "#(_ & %)".
    iSplitR "Howner₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma front_spec_Superempty l γ back data cap ws front :
    back < front →
    {{{
      inv' l γ ∗
      owner₁ γ Unstable back data cap ws ∗
      front_lb γ front
    }}}
      (#l).{front}
    {{{
      RET #front;
      owner₁ γ Unstable back data cap ws
    }}}.
  Proof.
    iIntros "% %Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    iDestruct (inv_state_Superempty with "Hstate") as %->; first lia.
    iDestruct "Hstate" as "(:inv_state_superempty =1 lazy=)".
    iSplitR "Howner₁ HΦ". { iExists Superempty. iFrameSteps. }
    replace (S back) with front by lia.
    iSteps.
  Qed.
  #[local] Lemma front_spec_winner_steal l γ front data P :
    {{{
      inv' l γ ∗
      winner_steal γ front data P
    }}}
      (#l).{front}
    {{{
      RET #front;
      winner_steal γ front data P
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hwinner_steal) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.

    iAssert ⌜front1 = front⌝%I as %->.
    { iDestruct (inv_state_winner_steal with "Hstate Hwinner_steal") as "(%P_ & $ & _)". }

    iSplitR "Hwinner_steal HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma back_spec l γ stable back data cap ws :
    {{{
      inv' l γ ∗
      owner₁ γ stable back data cap ws
    }}}
      (#l).{back}
    {{{
      RET #back;
      owner₁ γ stable back data cap ws
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Howner₁) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as "(<- & <- & <- & <-)".
    iSplitR "Howner₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma set_back_spec_Superempty l γ back data cap ws front (back' : Z) :
    back < front →
    back' = S back →
    {{{
      inv' l γ ∗
      owner₁ γ Unstable back data cap ws ∗
      front_lb γ front
    }}}
      #l <-{back} #back'
    {{{
      RET ();
      owner₁ γ Stable (S back) data cap ws
    }}}.
  Proof.
    iIntros (? ->) "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_store.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iMod (owner_update Stable (S back) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    iDestruct (inv_state_Superempty with "Hstate") as %->; first lia.
    iDestruct "Hstate" as "(:inv_state_superempty =1 lazy=)".
    iSplitR "Howner₁ HΦ". { iExists Empty. iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma data_spec l γ :
    {{{
      inv' l γ
    }}}
      (#l).{data}
    {{{ data,
      RET data;
      datas_elem γ data
    }}}.
  Proof.
    iIntros "%Φ (:inv') HΦ".

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iDestruct (datas_elem_get with "Hdatas_auth") as "#Hdatas_elem".
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma data_spec_owner l γ stable back data cap ws :
    {{{
      inv' l γ ∗
      owner₁ γ stable back data cap ws
    }}}
      (#l).{data}
    {{{
      RET data;
      owner₁ γ stable back data cap ws
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Howner₁) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iSplitR "Howner₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma data_spec_winner_pop l γ front data P :
    {{{
      inv' l γ ∗
      winner_pop γ front (Some data) P
    }}}
      (#l).{data}
    {{{ data,
      RET data;
      winner_pop γ front (Some data) P
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hwinner_pop) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.

    iAssert (
      winner_pop γ front (Some data1) P ∗
      ▷ inv_state γ state1 stable1 front1 back1 data1 hist1 vs1 priv1 (prophss1 front1)
    )%I with "[> Hwinner_pop Hstate]" as "(Hwinner_pop & Hstate)".
    { iDestruct (inv_state_winner_pop with "Hstate Hwinner_pop") as "(%P_ & -> & _ & [(:inv_state_nonempty_steal =1) | (:inv_state_emptyish_steal =1)] & _ & Hwinner_pop)".
      - destruct (prophss1 front) as [| id prophs].
        { iDestruct "Hwinner" as %[]. }
        iDestruct "Hwinner" as "(:winner_pending_1)".
        iMod (winner_update' front (Some data1) with "Hwinner_pop Hwinner_steal") as "($ & Hwinner_steal)".
        iFrameSteps.
      - iMod (winner_update' back1 (Some data1) with "Hwinner_pop Hwinner_steal") as "($ & Hwinner_steal)".
        iExists P_. iSteps.
    }

    iSplitR "Hwinner_pop HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma set_data_spec l γ front vs back data1 cap1 priv1 ws data2 cap2 priv2 :
    0 < cap2 →
    front + length vs = back →
    length vs + length priv1 = cap1 →
    length vs + length priv2 = cap2 →
    {{{
      inv' l γ ∗
      owner₁ γ Stable back data1 cap1 ws ∗
      front_lb γ front ∗
      array_cslice data1 cap1 front (DfracOwn (1/2)) (vs ++ priv1) ∗
      array_cslice data2 cap2 front (DfracOwn (1/2)) (vs ++ priv2)
    }}}
      #l <-{data} data2
    {{{
      RET ();
      owner₁ γ Stable back data2 cap2 ws ∗
      array_cslice data1 cap1 front (DfracOwn (1/2)) (vs ++ priv1)
    }}}.
  Proof.
    iIntros "%Hcap2 % % % %Φ ((:inv') & Howner₁ & #Hfront_lb & Hdata1_cslice₂ & Hdata2_cslice) HΦ".

    iInv "Hinv" as "(:inv_inner =3)".
    wp_store.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iMod (owner_update Stable back data2 cap2 with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
    iMod (datas_insert data2 with "Hdatas_auth") as "Hdatas_auth".
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    iDestruct (inv_state_Stable with "Hstate") as "(%Hstate3 & %)"; first done.

    iAssert (
      ∃ priv,
      ⌜vs = priv ++ vs3⌝ ∗
      ⌜(front + length priv)%nat = front3⌝
    )%I as "(%priv & -> & %)".
    { destruct (nil_or_length_pos vs3) as [-> |].
      - iExists vs. rewrite app_nil_r.
        simpl in Hvs3. iSteps.
      - iDestruct (array_cslice_rotation_left_small_1' front (front3 - front) with "Hdata3_cslice₁") as "Hdata1_cslice₁"; [simpl_length; lia.. |].
        iDestruct (array_cslice_agree with "Hdata1_cslice₁ Hdata1_cslice₂") as %Heq%(f_equal (take $ length vs)).
        { simpl_length. lia. }
        rewrite take_app_length take_app take_take take_app_length' in Heq.
        { simpl_length. lia. }
        rewrite -Heq. iSteps. iPureIntro.
        simpl_length. lia.
    }

    iDestruct (array_cslice_rotation_right_1' front3 (front3 - front) with "Hdata2_cslice") as "Hdata2_cslice"; [simpl_length; lia.. |].

    assert (
      ∃ priv4,
      rotation ((front3 - front) `mod` cap2) ((priv ++ vs3) ++ priv2) = vs3 ++ priv4 ∧
      length vs3 + length priv4 = cap2
    ) as (priv4 & -> & ?).
    { destruct_decide (front3 = front + cap2) as -> | ?.
      - assert (length vs3 = 0) as ->%nil_length_inv by lia.
        eexists. split; [done | simpl_length; lia].
      - rewrite Nat.mod_small; first lia.
        rewrite /rotation drop_app -assoc drop_app_length'; first lia.
        eexists. split; [done | simpl_length; lia].
    }

    iMod (array_cslice_persist with "Hdata3_cslice₁") as "#Hdata1_cslice₁".
    iDestruct (big_sepMS_insert_2 data1 with "Hdatas []") as "Hdatas".
    { iSteps. iPureIntro. simpl_length. }

    iSplitR "Howner₁ Hdata1_cslice₂ HΦ".
    { iExists state3. iFrameSteps.
      destruct Hstate3 as [-> | ->]; first iFrameSteps.
      iDestruct "Hstate" as "(:inv_state_nonempty =3 lazy=)".
      iStep 4.
      iDestruct "Hwinner" as "[$ | Hwinner]"; first iSteps.
      destruct (prophss3 front3) as [| id prophs]; first done.
      iDestruct "Hwinner" as "(:winner_pending_2)".
      iRight. iFrame. iRight.
      iDestruct "Hwinner" as "(:winner_model_1)"; last iFrameSteps.
      destruct vs3 as [| v vs3]; first naive_solver lia.
      iEval (rewrite -(assoc _ [_])) in "Hdata1_cslice₁".
      iDestruct (array_cslice_app_2 with "Hdata1_cslice₁") as "-#($ & _)"; first done.
      iSteps.
    }
    iSteps.
  Qed.

  #[local] Lemma array_unsafe_cget_spec_loser l γ (data : val) i :
    (0 ≤ i)%Z →
    {{{
      inv' l γ ∗
      datas_elem γ data
    }}}
      array_unsafe_cget data #i
    {{{ v,
      RET v;
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ ((:inv') & #Hdatas_elem) HΦ".

    iApply wp_fupd.
    wp_apply (wp_wand (λ _, £ 1)%I).
    { awp_apply (array_unsafe_cget_spec_atomic_weak with "[//]"); first done.
      iInv "Hinv" as "(:inv_inner =1)".
      rewrite /atomic_acc /=.
      iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
      iDestruct (datas_elem_valid with "Hdatas_auth Hdatas_elem") as %[-> | Hdatas1_elem].

      - unshelve iStep 3. { iPureIntro. simpl_length. }
        all: iMod "Hclose" as "_".
        all: iSplitL; first iFrameSteps.
        all: iSteps.

      - iDestruct (big_sepMS_elem_of_acc with "Hdatas") as "((:data_model) & Hdatas)"; first done.
        iStep 3.
        all: iMod "Hclose" as "_".
        all: iSplitL; first iFrameSteps.
        all: iSteps.
    }

    iIntros "%v H£".
    iMod (lc_fupd_elim_later with "H£ HΦ").
    iSteps.
  Qed.
  #[local] Lemma array_unsafe_cget_spec_winner_pop l γ front data P v :
    {{{
      inv' l γ ∗
      winner_pop γ front (Some data) P ∗
      history_at γ front v
    }}}
      array_unsafe_cget data #front
    {{{
      RET v;
      winner_pop γ front (Some data) P
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hwinner_pop & #Hhistory_at) HΦ".

    iApply wp_fupd.
    awp_apply (array_unsafe_cget_spec_atomic with "[//]") without "HΦ".
    iInv "Hinv" as "(:inv_inner =1)".

    iAssert (◇ (
      ⌜front1 = front⌝ ∗
      ⌜hd inhabitant (vs1 ++ priv1) = v⌝ ∗
      winner_model_1 γ front data1 data
    ))%I as "#>(-> & %Hlookup & Hwinner)".
    { iDestruct (inv_state_winner_pop with "Hstate [$Hwinner_pop]") as "(%P_ & >-> & _ & [(:inv_state_nonempty_steal =1 >) | (:inv_state_emptyish_steal =1 >)] & >$ & Hwinner_pop)".
      - iDestruct (history_at_agree with "Hhistory_at Hhistory_at_front1") as ">->".
        rewrite hd_app //; first lia.
      - iDestruct (history_at_agree with "Hhistory_at Hhistory_at_front1") as ">->".
        assert (length vs1 = 0) as ->%nil_length_inv by lia.
        iSteps.
    }

    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".

    iDestruct "Hwinner" as "(:winner_model_1)".

    - apply hd_correct in Hlookup; last (simpl_length; lia).
      rewrite head_lookup in Hlookup.

      iExists _, front, _, _, v. rewrite Nat2Z.id Nat.sub_diag. iStep 3.
      all: iMod "Hclose" as "_".
      all: iSplitR "Hwinner_pop"; first iFrameSteps.
      1: iSteps.
      iIntros "!> H£ HΦ".
      iMod (lc_fupd_elim_later with "H£ HΦ").
      iSteps.

    - iDestruct (history_at_agree with "Hhistory_at Hhistory_at_") as %<-.

      iExists _, front, _, [v], v. rewrite Nat2Z.id Nat.sub_diag. iStep 3.
      all: iMod "Hclose" as "_".
      all: iSplitR "Hwinner_pop"; first iFrameSteps.
      1: iSteps.
      iIntros "!> H£ HΦ".
      iMod (lc_fupd_elim_later with "H£ HΦ").
      iSteps.
  Qed.

  #[local] Lemma array_unsafe_cset_spec_owner l γ back data cap ws us front v :
    back < front + cap →
    {{{
      inv' l γ ∗
      owner' γ Stable back data cap ws back us ∗
      front_lb γ front
    }}}
      array_unsafe_cset data #back v
    {{{
      RET ();
      owner' γ Stable back data cap ws back (<[0 := v]> us)
    }}}.
  Proof.
    iIntros "% %Φ ((:inv') & (:owner') & #Hfront_lb) HΦ".

    iApply wp_fupd.
    awp_apply (array_unsafe_cset_spec_atomic_cell with "[//]") without "HΦ".
    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    iDestruct (inv_state_Stable with "Hstate") as "#>(%Hstate1 & %)"; first done.

    iDestruct (array_cslice_app with "Hdata1_cslice₁") as "(Hdata_cslice₁_1 & Hdata_cslice₁_2)".
    destruct (lookup_lt_is_Some_2 priv1 0) as (w & Hpriv_lookup); first lia.
    iDestruct (array_cslice_update with "Hdata_cslice₁_2") as "(Hdata_back₁ & Hdata_cslice₁_2)"; first done.
    replace (front1 + length vs1 + 0) with back by lia.

    destruct (lookup_lt_is_Some_2 us 0) as (w_ & Hus_lookup); first lia.
    iDestruct (array_cslice_update with "Hdata_cslice₂") as "(Hdata_back₂ & Hdata_cslice₂)"; first done.
    rewrite Nat.add_0_r.

    iDestruct (array_cslice_combine with "Hdata_back₁ Hdata_back₂") as "(%Heq & Hdata_back)"; first done. injection Heq as <-.
    iEval (rewrite dfrac_op_own Qp.half_half) in "Hdata_back".

    rewrite /atomic_acc /=.
    iExists back, w.
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    iSplitL "Hdata_back"; first iSteps. iSplit.

    - iIntros "(_ & (Hdata_back₁ & Hdata_back₂))". iMod "Hclose" as "_".

      iDestruct (array_cslice_app_1 with "Hdata_cslice₁_1 (Hdata_cslice₁_2 Hdata_back₁)") as "Hdata_cslice₁"; first done.
      iEval (rewrite list_insert_id //) in "Hdata_cslice₁".

      iDestruct ("Hdata_cslice₂" with "Hdata_back₂") as "Hdata_cslice₂".
      iEval (rewrite list_insert_id //) in "Hdata_cslice₂".

      iSplitR "Howner₁ Hdata_cslice₂". { iFrameSteps. }
      iSteps.

    - iIntros "(Hdata_back₁ & Hdata_back₂)". iMod "Hclose" as "_".

      iDestruct (array_cslice_app_1 with "Hdata_cslice₁_1 (Hdata_cslice₁_2 Hdata_back₁)") as "Hdata_cslice₁"; first done.

      iDestruct ("Hdata_cslice₂" with "Hdata_back₂") as "Hdata_cslice₂".

      iSplitR "Howner₁ Hdata_cslice₂".
      { iFrameSteps.
        - iPureIntro. simpl_length.
        - iExists state1.
          destruct Hstate1 as [-> | ->]; iFrameSteps.
      }
      iIntros "!> H£ HΦ".

      iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
      iSteps. simpl_length.
  Qed.

  #[local] Lemma resolve_spec_loser_1 l γ front1 front2 id :
    front1 < front2 →
    {{{
      inv' l γ ∗
      front_lb γ front2
    }}}
      Resolve (CAS (#l).[front]%V #front1 #(front1 + 1)) #γ.(metadata_prophet) (#front1, #id)%V
    {{{
      RET #false;
      True
    }}}.
  Proof.
    iIntros "%Hloser %Φ ((:inv') & #Hfront_lb) HΦ".

    iInv "Hinv" as "(:inv_inner =3)".
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    wp_apply (prophet_multi_wp_resolve' with "Hprophet_model"); [done.. |].
    wp_cas as Hcas; zoo_simplify in Hcas; last lia.
    iIntros "!> %prophs %Hprophss3 Hprophet_model".
    iSplitR "HΦ".
    { iFrameSteps.
      - iPureIntro => *.
        rewrite fn_lookup_alter_ne; first lia.
        auto.
      - rewrite fn_lookup_insert_ne //. iSteps.
    }
    iSteps.
  Qed.
  #[local] Lemma resolve_spec_loser_2 l γ front id prophs0 :
    head prophs0 ≠ Some id →
    {{{
      inv' l γ ∗
      front_lb γ front ∗
      prophet_multi_full prophet_identifier γ.(metadata_prophet_name) front prophs0
    }}}
      Resolve (CAS (#l).[front]%V #front #(front + 1)) #γ.(metadata_prophet) (#front, #id)%V
    {{{
      RET #false;
      front_lb γ (S front)
    }}}.
  Proof.
    iIntros "%Hloser %Φ ((:inv') & #Hfront_lb & #Hprophet_full) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    wp_apply (prophet_multi_wp_resolve' with "Hprophet_model"); [done.. |].
    wp_apply (wp_cas_nobranch' with "Hl_front") as (b) "%Hcas Hl_front".
    iIntros "%prophs %Hprophss1 Hprophet_model".
    destruct b; zoo_simplify in Hcas; first subst front1.

    - iDestruct (prophet_multi_full_valid with "Hprophet_model Hprophet_full") as %->.
      rewrite fn_lookup_alter Hpasts1 // in Hloser.

    - iDestruct (front_lb_get with "Hfront_auth") as "#-#Hfront_lb_1".
      iDestruct (front_lb_le (S front) with "Hfront_lb_1") as "-##Hfront_lb_1"; first lia.
      iSplitR "HΦ".
      { iFrameSteps.
        - iPureIntro => *.
          rewrite fn_lookup_alter_ne; first lia.
          auto.
        - rewrite fn_lookup_insert_ne //. iSteps.
      }
      iSteps.
  Qed.
  #[local] Lemma resolve_spec_winner_pop l γ front data P id :
    {{{
      inv' l γ ∗
      winner_pop γ front (Some data) P
    }}}
      Resolve (CAS (#l).[front]%V #front #(front + 1)) #γ.(metadata_prophet) (#front, #id)%V
    {{{
      RET #true;
      ▷ P
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hwinner_pop) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_apply (prophet_multi_wp_resolve' with "Hprophet_model"); [done.. |].
    wp_apply (wp_cas_nobranch' with "Hl_front") as (b) "%Hcas Hl_front".
    iIntros "%prophs %Hprophss1 Hprophet_model".
    iDestruct (inv_state_winner_pop with "Hstate Hwinner_pop") as "(%P_ & -> & #Heq & Hstate & _ & Hwinner_pop)".
    rewrite Hprophss1.
    destruct b; zoo_simplify in Hcas; last congruence.
    iMod (front_update with "Hfront_auth") as "Hfront_auth".
    iDestruct "Hstate" as "[(:inv_state_nonempty_steal =1) | (:inv_state_emptyish_steal =1)]".

    - iDestruct "Hwinner" as "(:winner_pending_1)".
      destruct vs1 as [| v1 vs1] => /=; first naive_solver lia.

      iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_steal with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂) /=".
      iMod ("HP" with "[$Hmodel₁ $Hhistory_at_front1 //]") as "HP".

      iDestruct (array_cslice_rotation_right_1' (S front) 1 with "Hdata1_cslice₁") as "Hdata1_cslice₁"; [simpl_length/=; lia.. |].
      eassert (rotation _ _ = vs1 ++ priv1 ++ [v1]) as ->.
      { destruct_decide (cap1 = 1) as Heq | ?.
        - rewrite -> Heq in *.
          simpl in Hdata1.
          assert (length vs1 = 0) as ->%nil_length_inv by lia.
          assert (length priv1 = 0) as ->%nil_length_inv by lia.
          done.
        - rewrite Nat.mod_1_l; first lia.
          rewrite rotation_S; first lia.
          rewrite rotation_0 assoc //.
      }

      iSplitR "HP HΦ".
      { destruct_decide (S front = back1) as <- | ?.

        - simpl in Hvs1.
          iExists Empty. iFrameSteps; iPureIntro.
          + simpl_length/=. lia.
          + intros.
            rewrite fn_lookup_alter_ne; first lia.
            apply Hpasts1; first lia.

        - destruct vs1 as [| v2 vs1] => /=; first naive_solver lia.
          simpl in Hvs1.
          iMod (history_update _ v2 with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)"; first done.
          iExists Nonempty. iFrameSteps; iPureIntro.
          + simpl_length/=. lia.
          + intros.
            rewrite fn_lookup_alter_ne; first lia.
            apply Hpasts1; first lia.
          + simpl_length/=. lia.
      }
      iIntros "!> {%}".

      iApply "HΦ". iModIntro.
      iRewrite "Heq" => //.

    - assert (length vs1 = 0) as ->%nil_length_inv by lia.

      iDestruct (array_cslice_rotation_right_1' (S back1) 1 with "Hdata1_cslice₁") as "Hdata1_cslice₁"; [simpl_length/=; lia.. |].
      iEval (rewrite /= -(app_nil_l (rotation _ _))) in "Hdata1_cslice₁".

      iSplitR "HP HΦ".
      { iExists Superempty. iFrameSteps; iPureIntro.
        - simpl_length.
        - intros.
          rewrite fn_lookup_alter_ne; first lia.
          apply Hpasts1; first lia.
      }
      iIntros "!> {%}".

      iApply "HΦ". iModIntro.
      iRewrite "Heq" => //.
  Qed.
  #[local] Lemma resolve_spec_winner_steal l γ front P id :
    {{{
      inv' l γ ∗
      winner_steal γ front None P
    }}}
      Resolve (CAS (#l).[front]%V #front #(front + 1)) #γ.(metadata_prophet) (#front, #id)%V
    {{{
      RET #true;
      front_lb γ (S front)
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hwinner_steal) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_apply (prophet_multi_wp_resolve' with "Hprophet_model"); [done.. |].
    wp_apply (wp_cas_nobranch' with "Hl_front") as (b) "%Hcas Hl_front".
    iIntros "%prophs %Hprophss1 Hprophet_model".
    iDestruct (inv_state_winner_steal with "Hstate Hwinner_steal") as "(%P_ & -> & _ & (:inv_state_emptyish_pop =1) & Hwinner_steal)".
    destruct b; zoo_simplify in Hcas; last congruence.
    iMod (front_update with "Hfront_auth") as "Hfront_auth".
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".

    assert (length vs1 = 0) as ->%nil_length_inv by lia.

    iDestruct (array_cslice_rotation_right_1' (S back1) 1 with "Hdata1_cslice₁") as "Hdata1_cslice₁"; [simpl_length; lia.. |].
    iEval (rewrite /= -(app_nil_l (rotation _ _))) in "Hdata1_cslice₁".

    iSplitR "HΦ".
    { iExists Superempty. iFrameSteps; iPureIntro.
      - simpl_length.
      - intros.
        rewrite fn_lookup_alter_ne; first lia.
        apply Hpasts1; first lia.
    }
    iSteps.
  Qed.
  #[local] Lemma resolve_spec_Empty l γ back data cap ws id :
    {{{
      inv' l γ ∗
      owner₁ γ Stable back data cap ws ∗
      front_lb γ back
    }}}
      Resolve (CAS (#l).[front]%V #back #(back + 1)) #γ.(metadata_prophet) (#back, #id)%V
    {{{
      RET #true;
      owner₁ γ Unstable back data cap ws ∗
      front_lb γ (S back)
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_apply (prophet_multi_wp_resolve' with "Hprophet_model"); [done.. |].
    wp_apply (wp_cas_nobranch' with "Hl_front") as (b) "%Hcas Hl_front".
    iIntros "%prophs %Hprophss1 Hprophet_model".
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    iDestruct (inv_state_Stable with "Hstate") as "#([-> | ->] & _)"; first done.

    - iDestruct "Hstate" as "(:inv_state_empty =1 lazy=)".
      assert (length vs1 = 0) as ->%nil_length_inv by lia.
      destruct b; zoo_simplify in Hcas; last lia.

      iMod (front_update with "Hfront_auth") as "Hfront_auth".
      iClear "Hfront_lb". iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
      iMod (history_update _ inhabitant with "Hhistory_auth") as "(Hhistory_auth & _)"; first done.
      iMod (owner_update Unstable (length hist1) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

      iDestruct (array_cslice_rotation_right_1' (S (length hist1)) 1 with "Hdata1_cslice₁") as "Hdata_cslice₁"; [simpl_length; lia.. |].
      iEval (rewrite -(app_nil_l (rotation _ _ ))) in "Hdata_cslice₁".

      iSplitR "Howner₁ HΦ".
      { iExists Superempty. iFrameSteps; iPureIntro.
        - simpl_length.
        - intros.
          rewrite fn_lookup_alter_ne; first lia.
          apply Hpasts1; first lia.
        - simpl_length/=. lia.
      }
      rewrite Hhist1. iSteps.

    - iDestruct "Hstate" as "(:inv_state_nonempty =1 lazy=)".
      exfalso. lia.
  Qed.

  Lemma ws_deque_1_size_spec t ι ws :
    <<<
      ws_deque_1_inv t ι ∗
      ws_deque_1_owner t ws
    | ∀∀ vs,
      ws_deque_1_model t vs
    >>>
      ws_deque_1_size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_deque_1_model t vs
    | RET #(length vs);
      ws_deque_1_owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct "Howner" as "(:owner')".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iDestruct (inv_state_Stable with "Hstate") as %(_ & Hback); first done.

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
    iMod (owner₁_update with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Howner₁ Hdata_cslice₂ HΦ". { iFrameSteps. }
    iModIntro. clear- Hcap Hus Hvs1 Hback.

    wp_apply (back_spec with "[$Howner₁]") as "Howner₁"; first iSteps.
    wp_pures.

    replace (⁺back - ⁺front1)%Z with ⁺(length vs) by lia.
    iSteps.
  Qed.

  Lemma ws_deque_1_is_empty_spec t ι ws :
    <<<
      ws_deque_1_inv t ι ∗
      ws_deque_1_owner t ws
    | ∀∀ vs,
      ws_deque_1_model t vs
    >>>
      ws_deque_1_is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_deque_1_model t vs
    | RET #(bool_decide (vs = []%list));
      ws_deque_1_owner t vs
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_apply (ws_deque_1_size_spec with "[$]").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ (%Hvs & Howner)".
    wp_pures.

    rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
    { rewrite -length_zero_iff_nil. lia. }
    iApply "HΦ".
    iFrameSteps.
  Qed.

  Lemma ws_deque_1_push_spec t ι ws v :
    <<<
      ws_deque_1_inv t ι ∗
      ws_deque_1_owner t ws
    | ∀∀ vs,
      ws_deque_1_model t vs
    >>>
      ws_deque_1_push t v @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_deque_1_model t (vs ++ [v])
    | RET ();
      ws_deque_1_owner t (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    rename us into us0. iDestruct (owner'_rebase with "Howner") as "(%us & (:owner'))".

    wp_rec.
    wp_smart_apply (back_spec with "[$]") as "Howner₁".
    wp_smart_apply (data_spec_owner with "[$]") as "Howner₁".
    wp_smart_apply (array_size_spec_cslice with "Hdata_cslice₂") as "Hdata_cslice₂".
    wp_pures.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
    iSplitR "Howner₁ Hdata_cslice₂ HΦ". { iFrameSteps. }
    iModIntro. clear- Hcap Hus Hvs1 Hdata1.

    wp_pures.

    wp_bind (if: _ then _ else _)%E.
    wp_apply (wp_wand (λ _,
      ∃ data cap us,
      ⌜back < front1 + cap⌝ ∗
      ⌜us !! 0 = Some v⌝ ∗
      owner' γ Stable back data cap ws back us
    )%I with "[Howner₁ Hdata_cslice₂]") as (res) "{%} (%data & %cap & %us & % & %Hus_lookup & (:owner'))".
    { case_bool_decide; wp_pures.

      - wp_apply (array_unsafe_cset_spec_owner with "[$Howner₁ $Hdata_cslice₂ $Hfront_lb]") as "(:owner' !=)"; [lia | iSteps |].

        iFrameSteps; iPureIntro.
        { apply list_lookup_insert_eq; first lia. }
        { simpl_length. }

      - assert (length priv1 = 0) as ->%nil_length_inv by lia.
        iEval (rewrite Z.shiftl_mul_pow2 //).

        iDestruct (array_cslice_reshape front1 with "Hdata_cslice₂") as "(%vs & %priv & % & % & Hdata_cslice₂ & _)"; [lia.. |].
        wp_apply (array_unsafe_cgrow_spec with "Hdata_cslice₂") as (data') "(Hdata_cslice₂ & Hdata'_cslice)"; [simpl_length; lia.. |].

        wp_smart_apply (array_unsafe_cset_spec with "Hdata'_cslice") as "Hdata'_cslice".
        { simpl_length. lia. }
        iEval (rewrite -assoc insert_app_r_0; first lia) in "Hdata'_cslice".
        iDestruct "Hdata'_cslice" as "(Hdata'_cslice₁ & Hdata'_cslice₂)".
        wp_smart_apply (set_data_spec with "[$Howner₁ $Hdata_cslice₂ $Hdata'_cslice₁]") as "(Howner₁ & _)"; [simpl_length; lia.. | iSteps |].

        iDestruct (array_cslice_rotation_right_small_1' back cap with "Hdata'_cslice₂") as "Hdata'_cslice₂"; [simpl_length; lia.. |].
        iEval (rewrite /rotation drop_app_length'; first lia) in "Hdata'_cslice₂".
        iEval (rewrite take_app_length'; first lia) in "Hdata'_cslice₂".
        iFrameSteps; iPureIntro.
        { rewrite -insert_app_l.
          { simpl_length. lia. }
          apply list_lookup_insert_eq.
          { simpl_length. lia. }
        } {
          simpl_length. lia.
        }
    }

    wp_pures.

    wp_bind (_ <-{back} _)%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_store.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iMod (owner_update Stable (S back) data cap with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
    iDestruct (inv_state_Stable with "Hstate") as "(%Hstate2 & %)"; first done.
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.

    iAssert ⌜head priv2 = Some v⌝%I as %(priv2' & ->)%head_Some.
    { iDestruct (array_cslice_rotation_right_small_1' back (length vs2) with "Hdata2_cslice₁") as "Hdata_cslice₁"; [simpl_length; lia.. |].
      rewrite /rotation drop_app_length.
      rewrite head_lookup -(lookup_app_l _ (take (length vs2) (vs2 ++ priv2))); first lia.
      iDestruct (array_cslice_agree with "Hdata_cslice₁ Hdata_cslice₂") as %->.
      { simpl_length. lia. }
      iSteps.
    }
    iEval (rewrite (assoc _ _ [_])) in "Hdata2_cslice₁".

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
    iMod (model_push v with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Howner₁ Hdata_cslice₂ HΦ".
    { iExists Nonempty.
      destruct Hstate2 as [-> | ->].

      - iDestruct "Hstate" as "(:inv_state_empty =1 lazy=)".
        assert (length vs = 0) as ->%nil_length_inv by lia.
        iMod (history_update back v with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)"; first done.
        iFrameSteps. iPureIntro.
        simpl_length/=. lia.

      - iDestruct "Hstate" as "(:inv_state_nonempty =1 lazy=)".
        iFrameSteps; try iPureIntro.
        + simpl_length/=. lia.
        + simpl_length/=. lia.
        + rewrite hd_app //; first lia.
    }
    iSteps.
  Qed.

  Lemma ws_deque_1_steal_spec t ι :
    <<<
      ws_deque_1_inv t ι
    | ∀∀ vs,
      ws_deque_1_model t vs
    >>>
      ws_deque_1_steal t @ ↑ι
    <<<
      ws_deque_1_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_apply (wp_id with "[//]") as (id) "Hid".
    wp_smart_apply (front_spec with "[$]") as (front1) "#Hfront_lb_1".
    wp_pures.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_load.
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_1") as %?.

    destruct_decide (front1 < back2) as Hbranch1; last first.
    { assert (length vs2 = 0) as ->%nil_length_inv by lia.

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁] [//]") as "HΦ"; first iSteps.

      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
    }

    destruct_decide (front1 = front2) as <- | ?; last first.
    { assert (front1 < front2) as Hbranch2 by lia.
      iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_2".
      iSplitR "HΦ". { iFrameSteps. }
      iModIntro. clear- Hbranch1 Hbranch2.

      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_smart_apply (data_spec with "[$]") as (data) "#Hdatas_elem".
      wp_smart_apply (array_unsafe_cget_spec_loser with "[$]") as (v) "_"; first lia.
      wp_load.
      wp_smart_apply (resolve_spec_loser_1 with "[$]"); first done.
      iSteps.
    }

    iDestruct (prophet_multi_full_get _ front1 with "Hprophet_model") as "#Hprophet_full".
    iEval (rewrite Hpasts2 //=) in "Hprophet_full".

    destruct_decide (head $ prophss2 front1 = Some id) as (prophs0 & Hbranch3)%head_Some | Hbranch3; last first.
    { iSplitR "HΦ". { iFrameSteps. }
      remember (prophss2 front1) as prophs0.
      iModIntro. clear- Hbranch1 Hbranch3.

      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_smart_apply (data_spec with "[$]") as (data) "#Hdatas_elem".
      wp_smart_apply (array_unsafe_cget_spec_loser with "[$]") as (v) "_"; first lia.
      wp_load.
      wp_smart_apply (resolve_spec_loser_2 with "[$]"); first done.
      iSteps.
    }
    rewrite Hbranch3.

    iDestruct (inv_state_Nonempty with "Hstate") as %->; first done.
    iDestruct "Hstate" as "(:inv_state_nonempty =2)".
    iDestruct "Hwinner" as "[(:winner) | (:winner_pending_2 !=)]"; last first.
    { iDestruct (identifier_model_exclusive with "Hid Hid_") as %[]. }

    destruct vs2 as [| v vs2] => /=; first naive_solver lia.
    iMod (winner_update front1 (Some data2) (Φ (Some v)) with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

    iSplitR "Hwinner_pop".
    { iExists Nonempty. iFrameSteps.
      rewrite Hbranch3 /winner_pending_2. iSteps. iIntros "!> !>".
      rewrite /winner_au. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%v_ %vs' (-> & Hmodel₁ & Hhistory_at) !>".
      iDestruct (history_at_agree with "Hhistory_at Hhistory_at_front2") as %<-.
      iSteps.
    }
    iModIntro. clear- Hbranch1.

    wp_pures.
    rewrite bool_decide_eq_false_2; first lia.
    wp_smart_apply (data_spec_winner_pop with "[$]") as (data) "Hwinner_pop".
    wp_smart_apply (array_unsafe_cget_spec_winner_pop with "[$]") as "Hwinner_pop".
    wp_load.
    wp_smart_apply (resolve_spec_winner_pop with "[$]") as "HΦ".
    iSteps.
  Qed.

  Inductive pop_state :=
    | PopNonempty v
    | PopEmptyishWinner v
    | PopEmptyishLoser
    | PopSuperempty.
  #[local] Lemma ws_deque_1_pop_0_spec {l γ} (state : pop_state) stable back (back_ : Z) data cap ws us id :
    back_ = back →
    {{{
      inv' l γ ∗
      owner' γ stable back data cap ws back us ∗
      match state with
      | PopNonempty v =>
          ⌜stable = Stable⌝ ∗
          ⌜us !! 0 = Some v⌝
      | PopEmptyishWinner v =>
          ⌜stable = Unstable⌝ ∗
          ⌜us !! 0 = Some v⌝ ∗
          winner_steal γ back None inhabitant
      | PopEmptyishLoser =>
          ∃ id_winner prophs,
          ⌜stable = Unstable⌝ ∗
          prophet_multi_full prophet_identifier γ.(metadata_prophet_name) back (id_winner :: prophs) ∗
          ⌜head (id_winner :: prophs) ≠ Some id⌝
      | PopSuperempty =>
          ∃ front,
          ⌜stable = Unstable⌝ ∗
          front_lb γ front ∗
          ⌜front = S back⌝
      end
    }}}
      ws_deque_1_pop_0 #l #id #back_
    {{{ o back data cap i us,
      RET o : val;
      owner' γ Stable back data cap ws i us ∗
      match state with
      | PopNonempty v =>
          ⌜o = Some v⌝
      | PopEmptyishWinner v =>
          ⌜o = Some v⌝
      | PopEmptyishLoser =>
          ⌜o = None⌝
      | PopSuperempty =>
          ⌜o = None⌝
      end
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv') & (:owner') & H) HΦ".

    wp_rec. wp_pures.
    destruct state.

    - iDestruct "H" as "(-> & %Hus_lookup)".
      iSpecialize ("HΦ" $! (Some v)).

      wp_apply (front_spec_owner_Stable with "[$]") as (front2) "(Howner₁ & #Hfront_lb_1 & %Hfront2)".
      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_pures.
      case_bool_decide as Hbranch; wp_pures.

      + wp_apply (data_spec_owner with "[$]") as "Howner₁".
        wp_smart_apply (array_size_spec_cslice with "Hdata_cslice₂") as "Hdata_cslice₂".
        rewrite ws_deque_1_min_capacity.
        wp_pures.

        wp_bind (if: _ then _ else _)%E.
        wp_apply (wp_wand (λ _,
          array_cslice data cap back (DfracOwn (1/2)) us ∗
          ( array_cslice data cap back (DfracOwn (1/2)) us -∗
              ∃ data' cap' us',
              owner' γ Stable back data' cap' ws back us'
          )
        )%I with "[Howner₁ Hdata_cslice₂]") as (res) "(Hdata_cslice₂ & Howner)".
        { case_bool_decide; wp_pures; last iFrameSteps.
          iEval (rewrite Z.shiftr_div_pow2 //).

          iDestruct (array_cslice_reshape front2 with "Hdata_cslice₂") as "(%vs & %priv & % & % & Hdata_cslice₂ & Hdata_cslice₂_rebase)"; [lia.. |].
          wp_apply (array_unsafe_cshrink_slice_spec_fit with "Hdata_cslice₂") as (data') "(Hdata_cslice₂ & Hdata'_cslice)"; [simpl_length; lia.. |].
          iEval (rewrite take_app_ge; first lia) in "Hdata'_cslice".
          iDestruct "Hdata'_cslice" as "(Hdata'_cslice₁ & Hdata'_cslice₂)".
          wp_smart_apply (set_data_spec with "[$Howner₁ $Hdata_cslice₂ $Hdata'_cslice₁]") as "(Howner₁ & Hdata_cslice₂)"; [simpl_length; lia.. | iSteps |].

          iDestruct ("Hdata_cslice₂_rebase" with "Hdata_cslice₂") as "$".
          iIntros "_".
          iDestruct (array_cslice_rebase back with "Hdata'_cslice₂") as "(% & %n & -> & $ & _)"; [simpl_length; lia.. |].
          iFrameSteps. iPureIntro. simpl_length. lia.
        }

        wp_smart_apply (array_unsafe_cget_spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
        iSteps.

      + replace front2 with back by lia.

        wp_load.
        wp_smart_apply (resolve_spec_Empty with "[$]") as "(Howner₁ & #Hfront_lb_2)".
        wp_smart_apply (set_back_spec_Superempty with "[$]") as "Howner₁"; [lia.. |].
        wp_smart_apply (data_spec_owner with "[$]") as "Howner₁".
        wp_apply (array_unsafe_cget_spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
        iSteps.

    - iDestruct "H" as "(-> & %Hus_lookup & Hwinner_steal)".
      iSpecialize ("HΦ" $! (Some v)).

      wp_apply (front_spec_winner_steal with "[$]") as "Hwinner_steal".
      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_load.
      wp_smart_apply (resolve_spec_winner_steal with "[$]") as "#Hfront_lb".
      wp_smart_apply (set_back_spec_Superempty with "[$]") as "Howner₁"; [lia.. |].
      wp_smart_apply (data_spec_owner with "[$]") as "Howner₁".
      wp_apply (array_unsafe_cget_spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
      iSteps.

    - iDestruct "H" as "(%id_winner & %prophs & -> & #Hprophet_full & %Hloser)".
      iSpecialize ("HΦ" $! None).

      wp_apply (front_spec_owner_Unstable with "[$]") as (front2) "(Howner₁ & #Hfront_lb_1 & %Hbranch)".
      wp_pures.
      destruct Hbranch as [-> | ->].

      + rewrite bool_decide_eq_false_2; first lia.
        wp_pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp_load.
        wp_smart_apply (resolve_spec_loser_2 with "[$]") as "#Hfront_lb_2"; first done.
        wp_smart_apply (set_back_spec_Superempty with "[$]") as "Howner₁"; [lia.. |].
        iSteps.

      + rewrite bool_decide_eq_true_2; first lia.
        wp_smart_apply (set_back_spec_Superempty with "[$]") as "Howner₁"; [lia.. |].
        iSteps.

    - iDestruct "H" as "(%front & -> & #Hfront_lb & ->)".
      iSpecialize ("HΦ" $! None).

      wp_apply (front_spec_Superempty with "[$]") as "Howner₁"; [lia |].
      wp_pures.
      rewrite bool_decide_eq_true_2; first lia.
      wp_smart_apply (set_back_spec_Superempty with "[$]") as "Howner₁"; [lia.. |].
      iSteps.
  Qed.
  Lemma ws_deque_1_pop_spec t ι ws :
    <<<
      ws_deque_1_inv t ι ∗
      ws_deque_1_owner t ws
    | ∀∀ vs,
      ws_deque_1_model t vs
    >>>
      ws_deque_1_pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_deque_1_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          ws_deque_1_model t vs'
      end
    | RET o;
      ws_deque_1_owner t ws'
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    rename us into us0. iDestruct (owner'_rebase (back - 1) with "Howner") as "(%us & (:owner'))".

    wp_rec.
    wp_apply (wp_id with "[//]") as (id) "Hid".
    wp_smart_apply (back_spec with "[$]") as "Howner₁".
    wp_pures.

    wp_bind (_ <-{back} _)%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_store.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
    iDestruct (inv_state_Stable with "Hstate") as "#(%Hstate1 & %)"; first done.
    destruct Hstate1 as [-> | ->].

    { iDestruct "Hstate" as "(:inv_state_empty =1 lazy=)".
      assert (0 < back) as Hback by lia.
      assert (length vs1 = 0) as ->%nil_length_inv by lia.

      iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
      iMod (owner_update Unstable (back - 1) data cap with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (model_empty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! None with "[$Hmodel₁]") as "HΦ"; first iSteps.

      iSplitR "Howner₁ Hdata_cslice₂ HΦ".
      { iExists Superempty. iFrameSteps. }
      iModIntro. clear- Hcap Hus Hback.

      wp_smart_apply (ws_deque_1_pop_0_spec PopSuperempty _ (back - 1) with "[$Howner₁ $Hdata_cslice₂]"); [lia.. | iFrameSteps |].
      iSteps.
    }

    iDestruct "Hstate" as "(:inv_state_nonempty =1 lazy=)".
    assert (0 < back) as Hback by lia.
    destruct vs1 as [| v vs1 _] using rev_ind; first naive_solver lia.
    simpl_length/= in Hvs1.
    simpl_length/= in Hdata1.

    destruct_decide (S front1 = back) as <- | Hbranch1.

    - assert (length vs1 = 0) as ->%nil_length_inv.
      { simpl_length/= in Hvs1. lia. }
      simpl in *.
      iEval (rewrite Nat.sub_0_r) in "Hdata_cslice₂".

      iAssert ⌜us !! 0 = Some v⌝%I as %Hus_lookup.
      { iDestruct (array_cslice_agree with "Hdata1_cslice₁ Hdata_cslice₂") as %<-; first (simpl; lia).
        iSteps.
      }

      iMod (owner_update Unstable front1 data cap with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

      destruct_decide (head $ prophss1 front1 = Some id) as (prophs0 & Hprophss1)%head_Some | Hbranch2.

      + rewrite Hprophss1.
        iDestruct "Hwinner" as "[(:winner) | (:winner_pending_2 !=)]"; last first.
        { iDestruct (identifier_model_exclusive with "Hid Hid_") as %[]. }
        iMod (winner_update front1 inhabitant with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (model_pop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
        iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

        iSplitR "Howner₁ Hdata_cslice₂ Hwinner_steal HΦ".
        { iExists Emptyish. iFrameSteps. }
        iModIntro. clear- Hcap Hus Hback Hus_lookup.

        wp_smart_apply (ws_deque_1_pop_0_spec (PopEmptyishWinner v) _ front1 with "[$Howner₁ $Hdata_cslice₂ $Hwinner_steal]"); [lia.. | iFrameSteps |].
        iSteps.

      + iDestruct "Hwinner" as "[(:winner) | Hwinner]".

        { iMod (winner_update front1 inhabitant with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
          iMod (model_pop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
          iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

          iSplitR "Howner₁ Hdata_cslice₂ Hwinner_steal HΦ".
          { iExists Emptyish. iFrameSteps. }
          iModIntro. clear- Hcap Hus Hus_lookup.

          wp_smart_apply (ws_deque_1_pop_0_spec (PopEmptyishWinner v) _ front1 with "[$Howner₁ $Hdata_cslice₂ $Hwinner_steal]"); [lia.. | iFrameSteps |].
          iSteps.
        }

        iDestruct (prophet_multi_full_get _ front1 with "Hprophet_model") as "#Hprophet_full".
        iEval (rewrite Hpasts1 //=) in "Hprophet_full".
        destruct (prophss1 front1) as [| id_winner prophs]; first done.
        iDestruct "Hwinner" as "(:winner_pending_2 !=)".

        iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_steal with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂) /=".
        iMod ("HP" with "[$Hmodel₁]") as "HP"; first iSteps.

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (model_empty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! None with "[$Hmodel₁]") as "HΦ"; first iSteps.

        iSplitR "Howner₁ Hdata_cslice₂ HΦ".
        { iExists Emptyish. iFrameStep 7. iExists P. iSteps. }
        iModIntro. clear- Hcap Hus Hbranch2.

        wp_smart_apply (ws_deque_1_pop_0_spec PopEmptyishLoser _ front1 with "[$Howner₁ $Hdata_cslice₂]"); [lia.. | iFrameSteps |].
        iSteps.

    - iMod (owner_update Stable (back - 1) data cap with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iEval (rewrite -assoc) in "Hdata1_cslice₁".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (model_pop' with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

      iAssert ⌜us !! 0 = Some v⌝%I as %Hus_lookup.
      { iDestruct (array_cslice_rotation_right_small_1' (back - 1) (length vs1) with "Hdata1_cslice₁") as "Hdata_cslice₁"; [simpl_length/=; lia.. |].
        iDestruct (array_cslice_agree with "Hdata_cslice₁ Hdata_cslice₂") as %<-.
        { simpl_length/=. lia. }
        rewrite /rotation drop_app_length //.
      }

      iSplitR "Howner₁ Hdata_cslice₂ HΦ".
      { iExists Nonempty. iFrameSteps.
        rewrite hd_app //; first lia.
      }
      iModIntro. clear- Hcap Hus Hback Hus_lookup.

      wp_smart_apply (ws_deque_1_pop_0_spec (PopNonempty v) _ (back - 1) with "[$Howner₁ $Hdata_cslice₂]"); [lia.. | iFrameSteps |].
      iSteps.
  Qed.
End ws_deque_1_G.

From zoo_saturn Require
  ws_deque_1__opaque.

#[global] Opaque ws_deque_1_inv.
#[global] Opaque ws_deque_1_model.
#[global] Opaque ws_deque_1_owner.
