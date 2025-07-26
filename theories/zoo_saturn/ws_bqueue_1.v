From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  function
  relations.
From zoo.iris.base_logic Require Import
  lib.auth_nat_max
  lib.auth_twins
  lib.excl
  lib.mono_list
  lib.twins.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  identifier
  wise_prophets.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  array
  domain
  option.
From zoo_saturn Require Export
  base
  ws_bqueue_1__code.
From zoo_saturn Require Import
  ws_bqueue_1__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types front back : nat.
Implicit Types l : location.
Implicit Types id : prophet_id.
Implicit Types v t : val.
Implicit Types us vs ws hist priv : list val.

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

#[local] Program Definition prophet := {|
  typed_prophet_type :=
    identifier ;
  typed_prophet_of_val v :=
    match v with
    | ValId id =>
        Some id
    | _ =>
        None
    end ;
  typed_prophet_to_val id :=
    #id ;
|}.
Solve Obligations of prophet with
  try done.
Next Obligation.
  naive_solver.
Qed.
Implicit Types past prophs : list prophet.(typed_prophet_type).
Implicit Types pasts prophss : nat → list prophet.(typed_prophet_type).

Class WsBqueue1G Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_bqueue_1_G_prophets_G :: WiseProphetsG Σ prophet ;
  #[local] ws_bqueue_1_G_model_G :: AuthTwinsG Σ (leibnizO (list val)) suffix ;
  #[local] ws_bqueue_1_G_owner_G :: TwinsG Σ (leibnizO (stability * nat)) ;
  #[local] ws_bqueue_1_G_front_G :: AuthNatMaxG Σ ;
  #[local] ws_bqueue_1_G_history_G :: MonoListG Σ val ;
  #[local] ws_bqueue_1_G_winner_G :: TwinsG Σ (natO * ▶ ∙) ;
}.

Definition ws_bqueue_1_Σ := #[
  wise_prophets_Σ prophet ;
  auth_twins_Σ (leibnizO (list val)) suffix ;
  twins_Σ (leibnizO (stability * nat)) ;
  auth_nat_max_Σ ;
  mono_list_Σ val ;
  twins_Σ (natO * ▶ ∙)
].
#[global] Instance subG_ws_bqueue_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_bqueue_1_Σ Σ →
  WsBqueue1G Σ .
Proof.
  solve_inG.
Qed.

Section ws_bqueue_1_G.
  Context `{ws_bqueue_1_G : WsBqueue1G Σ}.

  Implicit Types P : iProp Σ.

  Record metadata := {
    metadata_capacity : nat ;
    metadata_data : val ;
    metadata_inv : namespace ;
    metadata_prophet : prophet_id ;
    metadata_prophet_name : wise_prophets_name ;
    metadata_model : auth_twins_name ;
    metadata_owner : gname ;
    metadata_front : gname ;
    metadata_history : gname ;
    metadata_winner : gname ;
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

  #[local] Definition owner₁' γ_owner γ_model stable back ws : iProp Σ :=
    twins_twin1 (twins_G := ws_bqueue_1_G_owner_G) γ_owner (DfracOwn 1) (stable, back) ∗
    auth_twins_auth _ γ_model ws.
  #[local] Definition owner₁ γ :=
    owner₁' γ.(metadata_owner) γ.(metadata_model).
  #[local] Instance : CustomIpatFormat "owner₁" :=
    "(
      Howner₁{_{}} &
      Hmodel_auth{_{}}
    )".
  #[local] Definition owner₂' γ_owner stable back :=
    twins_twin2 (twins_G := ws_bqueue_1_G_owner_G) γ_owner (stable, back).
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

  #[local] Definition winner_pop' γ_winner front P : iProp Σ :=
    twins_twin1 γ_winner (DfracOwn 1) (front, Next P).
  #[local] Definition winner_pop γ :=
    winner_pop' γ.(metadata_winner).
  #[local] Definition winner_steal' γ_winner front P :=
    twins_twin2 γ_winner (front, Next P).
  #[local] Definition winner_steal γ :=
    winner_steal' γ.(metadata_winner).
  #[local] Definition winner γ : iProp Σ :=
    ∃ front P1 P2,
    winner_pop γ front P1 ∗
    winner_steal γ front P2.
  #[local] Instance : CustomIpatFormat "winner" :=
    "(
      %front_winner &
      %P_winner_1 &
      %P_winner_2 &
      Hwinner_pop{_{}} &
      Hwinner_steal{_{}}
    )".

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
  #[local] Definition winner_pending_1 γ front P id : iProp Σ :=
    winner_steal γ front P ∗
    identifier_model' id ∗
    winner_au γ front P.
  #[local] Instance : CustomIpatFormat "winner_pending_1" :=
    "(
      Hwinner_steal{_{!}} &
      Hid{_{!}} &
      HP{}
    )".
  #[local] Definition winner_pending_2 γ front id : iProp Σ :=
    ∃ P,
    winner_pending_1 γ front P id.
  #[local] Instance : CustomIpatFormat "winner_pending_2" :=
    "(
      %P{} &
      (:winner_pending_1 {//} {/!/})
    )".
  #[local] Definition winner_linearized γ front P : iProp Σ :=
    winner_steal γ front P ∗
    P.
  #[local] Instance : CustomIpatFormat "winner_linearized" :=
    "(
      Hwinner_steal{_{!}} &
      HP{}
    )".

  #[local] Definition inv_state_empty γ stable front back hist : iProp Σ :=
    ⌜stable = Stable⌝ ∗
    ⌜front = back⌝ ∗
    ⌜length hist = front⌝ ∗
    winner γ.
  #[local] Instance : CustomIpatFormat "inv_state_empty" :=
    "(
      { {lazy}{>}%
      ; {lazy}%
      ; {>}->
      ; ->
      } &
      {>;}-> &
      {>;}%Hhist{} &
      Hwinner
    )".
  #[local] Definition inv_state_nonempty γ stable front back hist vs prophs : iProp Σ :=
    ⌜stable = Stable⌝ ∗
    ⌜front < back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant vs) ∗
    ( winner γ
    ∨ match prophs with
      | [] =>
          False
      | id :: _ =>
          winner_pending_2 γ front id
      end
    ).
  #[local] Instance : CustomIpatFormat "inv_state_nonempty" :=
    "(
      { {lazy}{>}%
      ; {lazy}%
      ; {>}->
      ; ->
      } &
      {>;}% &
      {>;}%Hhist{} &
      #Hhistory_at_front{} &
      Hwinner
    )".
  #[local] Definition inv_state_nonempty_steal γ state stable front back hist vs prophs P : iProp Σ :=
    ⌜state = Nonempty⌝ ∗
    ⌜stable = Stable⌝ ∗
    ⌜front < back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant vs) ∗
    match prophs with
    | [] =>
        False
    | id :: _ =>
        winner_pending_1 γ front P id
    end.
  #[local] Instance : CustomIpatFormat "inv_state_nonempty_steal" :=
    "(
      {>;}-> &
      { {lazy}{>}%
      ; {lazy}%
      ; {>}->
      ; ->
      } &
      {>;}% &
      {>;}%Hhist{} &
      #Hhistory_at_front{} &
      Hwinner
    )".
  #[local] Definition inv_state_emptyish γ stable front back hist priv : iProp Σ :=
    ∃ P,
    ⌜stable = Unstable⌝ ∗
    ⌜front = back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant priv) ∗
    ( winner_pop γ front P
    ∨ winner_linearized γ front P
    ).
  #[local] Instance : CustomIpatFormat "inv_state_emptyish" :=
    "(
      %P_ &
      { {lazy}{>}%
      ; {lazy}%
      ; {>}->
      ; ->
      } &
      {>;}-> &
      {>;}%Hhist{} &
      #Hhistory_at_front{} &
      Hwinner
    )".
  #[local] Definition inv_state_emptyish_pop γ state stable front back hist priv P : iProp Σ :=
    ⌜state = Emptyish⌝ ∗
    ⌜stable = Unstable⌝ ∗
    ⌜front = back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant priv) ∗
    winner_pop γ front P.
  #[local] Instance : CustomIpatFormat "inv_state_emptyish_pop" :=
    "(
      {>;}-> &
      { {lazy}{>}%
      ; {lazy}%
      ; {>}->
      ; ->
      } &
      {>;}-> &
      {>;}%Hhist{} &
      #Hhistory_at_front{} &
      Hwinner_pop
    )".
  #[local] Definition inv_state_emptyish_steal γ state stable front back hist priv P : iProp Σ :=
    ⌜state = Emptyish⌝ ∗
    ⌜stable = Unstable⌝ ∗
    ⌜front = back⌝ ∗
    ⌜length hist = S front⌝ ∗
    history_at γ front (hd inhabitant priv) ∗
    winner_linearized γ front P.
  #[local] Instance : CustomIpatFormat "inv_state_emptyish_steal" :=
    "(
      {>;}-> &
      { {lazy}{>}%
      ; {lazy}%
      ; {>}->
      ; ->
      } &
      {>;}-> &
      {>;}%Hhist{} &
      #Hhistory_at_front{} &
      (:winner_linearized)
    )".
  #[local] Definition inv_state_superempty γ stable front back hist : iProp Σ :=
    ⌜stable = Unstable⌝ ∗
    ⌜front = S back⌝ ∗
    ⌜length hist = front⌝ ∗
    winner γ.
  #[local] Instance : CustomIpatFormat "inv_state_superempty" :=
    "(
      { {lazy}{>}%
      ; {lazy}%
      ; {>}->
      ; ->
      } &
      {>;}-> &
      {>;}%Hhist{} &
      Hwinner
    )".
  #[local] Definition inv_state γ state stable front back hist vs priv prophs : iProp Σ :=
    match state with
    | Empty =>
        inv_state_empty γ stable front back hist
    | Nonempty =>
        inv_state_nonempty γ stable front back hist vs prophs
    | Emptyish =>
        inv_state_emptyish γ stable front back hist priv
    | Superempty =>
        inv_state_superempty γ stable front back hist
    end.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ state stable front back hist vs priv pasts prophss,
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    owner₂ γ stable back ∗
    front_auth γ front ∗
    ⌜0 < front⌝ ∗
    model₂ γ vs ∗
    ⌜length vs = back - front⌝ ∗
    array_cslice γ.(metadata_data) γ.(metadata_capacity) front (DfracOwn (1/2)) (vs ++ priv) ∗
    ⌜(length vs + length priv)%nat = γ.(metadata_capacity)⌝ ∗
    history_auth γ hist ∗
    wise_prophets_model prophet γ.(metadata_prophet) γ.(metadata_prophet_name) pasts prophss ∗
    ⌜∀ i, front ≤ i → pasts i = []⌝ ∗
    inv_state γ state stable front back hist vs priv (prophss front).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %state{} &
      %stable{} &
      %front{} &
      %back{} &
      %hist{} &
      %vs{} &
      %priv{} &
      %pasts{} &
      %prophss{} &
      >Hl_front &
      >Hl_back &
      >Howner₂ &
      >Hfront_auth &
      >%Hfront{} &
      >Hmodel₂ &
      >%Hvs{} &
      >Hdata_cslice₁ &
      >%Hdata{} &
      >Hhistory_auth &
      >Hprophet_model &
      >%Hpasts{} &
      Hstate
    )".
  #[local] Definition inv' l γ : iProp Σ :=
    ⌜0 < γ.(metadata_capacity)⌝ ∗
    l.[capacity] ↦□ #γ.(metadata_capacity) ∗
    l.[data] ↦□ γ.(metadata_data) ∗
    l.[proph] ↦□ #γ.(metadata_prophet) ∗
    inv γ.(metadata_inv) (inv_inner l γ).
  #[local] Instance : CustomIpatFormat "inv'" :=
    "(
      %Hcapacity &
      #Hl_capacity &
      #Hl_data &
      #Hl_proph &
      #Hinv
    )".
  Definition ws_bqueue_1_inv t ι cap : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata_inv)⌝ ∗
    ⌜cap = γ.(metadata_capacity)⌝ ∗
    meta l nroot γ ∗
    inv' l γ.
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      -> &
      -> &
      #Hmeta &
      (:inv')
    )".

  Definition ws_bqueue_1_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs ∗
    ⌜length vs ≤ γ.(metadata_capacity)⌝.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l{;_} &
      %γ{;_} &
      %Heq{} &
      Hmeta_{} &
      Hmodel₁{_{}} &
      %Hvs{}
    )".

  #[local] Definition owner' γ stable back ws i us : iProp Σ :=
    owner₁ γ stable back ws ∗
    array_cslice γ.(metadata_data) γ.(metadata_capacity) i (DfracOwn (1/2)) us ∗
    ⌜length us = γ.(metadata_capacity)⌝.
  #[local] Instance : CustomIpatFormat "owner'" :=
    "(
      Howner₁{_{}} &
      Hdata_cslice₂{_{}} &
      { {!} _
      ; %Hus{}
      ; %Hus
      }
    )".
  Definition ws_bqueue_1_owner t ws : iProp Σ :=
    ∃ l γ back i us,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    owner' γ Stable back ws i us.
  #[local] Instance : CustomIpatFormat "owner" :=
    "(
      %l{;_} &
      %γ{;_} &
      %back{} &
      %i{} &
      %us{} &
      %Heq{} &
      Hmeta_{} &
      Howner{_{}}
    )".

  #[global] Instance ws_bqueue_1_model_timeless t vs :
    Timeless (ws_bqueue_1_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_bqueue_1_owner_timeless t ws :
    Timeless (ws_bqueue_1_owner t ws).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_bqueue_1_inv_persistent t ι cap :
    Persistent (ws_bqueue_1_inv t ι cap).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_owner_alloc :
    ⊢ |==>
      ∃ γ_model γ_owner,
      model₁' γ_model [] ∗
      model₂' γ_model [] ∗
      owner₁' γ_owner γ_model Stable 1 [] ∗
      owner₂' γ_owner Stable 1.
  Proof.
    iMod (auth_twins_alloc _ (auth_twins_G := ws_bqueue_1_G_model_G)) as "(%γ_model & Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iMod (twins_alloc' (twins_G := ws_bqueue_1_G_owner_G)) as "(%γ_owner & Howner₁ & Howner₂)".
    iFrameSteps.
  Qed.
  #[local] Lemma model₁_valid γ stable back ws vs :
    owner₁ γ stable back ws -∗
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
  #[local] Lemma model₂_valid γ stable back ws vs :
    owner₁ γ stable back ws -∗
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
  #[local] Lemma model_owner₁_agree γ stable back ws vs1 vs2 :
    owner₁ γ stable back ws -∗
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
  #[local] Lemma model_empty {γ stable back ws vs1 vs2} :
    owner₁ γ stable back ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      owner₁ γ stable back [] ∗
      model₁ γ [] ∗
      model₂ γ [].
  Proof.
    iIntros "(:owner₁) Hmodel₁ Hmodel₂".
    iMod (auth_twins_update_auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma model_push {γ stable back ws vs1 vs2} v :
    owner₁ γ stable back ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      owner₁ γ stable back (vs1 ++ [v]) ∗
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
  #[local] Lemma model_pop γ stable back ws vs1 vs2 :
    owner₁ γ stable back ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      owner₁ γ stable back (removelast vs1) ∗
      model₁ γ (removelast vs1) ∗
      model₂ γ (removelast vs1).
  Proof.
    iIntros "(:owner₁) Hmodel₁ Hmodel₂".
    iMod (auth_twins_update_auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma model_pop' γ stable back ws vs1 v vs2 :
    owner₁ γ stable back ws -∗
    model₁ γ (vs1 ++ [v]) -∗
    model₂ γ vs2 ==∗
      owner₁ γ stable back vs1 ∗
      model₁ γ vs1 ∗
      model₂ γ vs1.
  Proof.
    rewrite -{2 3 4}(removelast_last vs1 v).
    apply model_pop.
  Qed.

  #[local] Lemma owner₁_exclusive γ stable1 back1 ws1 stable2 back2 ws2 :
    owner₁ γ stable1 back1 ws1 -∗
    owner₁ γ stable2 back2 ws2 -∗
    False.
  Proof.
    iIntros "(:owner₁ =1) (:owner₁ =2)".
    iApply (twins_twin1_exclusive with "Howner₁_1 Howner₁_2").
  Qed.
  #[local] Lemma owner_agree γ stable1 back1 ws stable2 back2 :
    owner₁ γ stable1 back1 ws -∗
    owner₂ γ stable2 back2 -∗
      ⌜stable1 = stable2⌝ ∗
      ⌜back1 = back2⌝.
  Proof.
    iIntros "(:owner₁) Howner₂".
    iDestruct (twins_agree_L with "Howner₁ Howner₂") as %[= <- <-].
    iSteps.
  Qed.
  #[local] Lemma owner₁_update γ stable back ws vs :
    owner₁ γ stable back ws -∗
    model₁ γ vs -∗
    model₂ γ vs ==∗
      owner₁ γ stable back vs ∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    iIntros "(:owner₁) Hmodel₁ Hmodel₂".
    iMod (auth_twins_update_auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "($ & $ & $)".
    iSteps.
  Qed.
  #[local] Lemma owner_update {γ stable1 back1 ws stable2 back2} stable back :
    owner₁ γ stable1 back1 ws -∗
    owner₂ γ stable2 back2 ==∗
      owner₁ γ stable back ws ∗
      owner₂ γ stable back.
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
      winner_pop' γ_winner 1 True ∗
      winner_steal' γ_winner 1 True.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma winner_pop_exclusive γ front1 P1 front2 P2 :
    winner_pop γ front1 P1 -∗
    winner_pop γ front2 P2 -∗
    False.
  Proof.
    apply twins_twin1_exclusive.
  Qed.
  #[local] Lemma winner_pop_exclusive' γ front P :
    winner_pop γ front P -∗
    winner γ -∗
    False.
  Proof.
    iIntros "Hwinner_pop_1 (:winner =2)".
    iApply (winner_pop_exclusive with "Hwinner_pop_1 Hwinner_pop_2").
  Qed.
  #[local] Lemma winner_steal_exclusive γ front1 P1 front2 P2 :
    winner_steal γ front1 P1 -∗
    winner_steal γ front2 P2 -∗
    False.
  Proof.
    apply twins_twin2_exclusive.
  Qed.
  #[local] Lemma winner_steal_exclusive' γ front P :
    winner_steal γ front P -∗
    winner γ -∗
    False.
  Proof.
    iIntros "Hwinner_steal_1 (:winner =2)".
    iApply (winner_steal_exclusive with "Hwinner_steal_1 Hwinner_steal_2").
  Qed.
  #[local] Lemma winner_agree γ front1 P1 front2 P2 :
    winner_pop γ front1 P1 -∗
    winner_steal γ front2 P2 -∗
      ⌜front1 = front2⌝ ∗
      ▷ (P1 ≡ P2).
  Proof.
    iIntros "Hwinner_pop Hwinner_steal".
    iDestruct (twins_agree with "Hwinner_pop Hwinner_steal") as "#Heq".
    rewrite prod_equivI /= discrete_eq_1.
    iDestruct "Heq" as "($ & $)".
  Qed.
  #[local] Lemma winner_update {γ front1 P1 front2 P2} front P :
    winner_pop γ front1 P1 -∗
    winner_steal γ front2 P2 ==∗
      winner_pop γ front P ∗
      winner_steal γ front P.
  Proof.
    apply twins_update.
  Qed.

  Opaque owner₁'.

  Lemma ws_bqueue_1_model_valid t ι cap vs :
    ws_bqueue_1_inv t ι cap -∗
    ws_bqueue_1_model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv) (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    iSteps.
  Qed.
  Lemma ws_bqueue_1_model_exclusive t vs1 vs2 :
    ws_bqueue_1_model t vs1 -∗
    ws_bqueue_1_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  #[local] Lemma owner'_rebase {γ stable back ws i1 us} i2 :
    0 < γ.(metadata_capacity) →
    owner' γ stable back ws i1 us ⊢
      ∃ us,
      owner' γ stable back ws i2 us.
  Proof.
    iIntros "%Hcapacity (:owner')".
    iDestruct (array_cslice_rebase i2 with "Hdata_cslice₂") as "(%us' & %n & -> & Hdata_cslice₂ & _)"; [done.. |].
    iSteps. simpl_length.
  Qed.

  Lemma ws_bqueue_1_owner_exclusive t ws1 ws2 :
    ws_bqueue_1_owner t ws1 -∗
    ws_bqueue_1_owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". subst t. injection Heq2 as <-.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct "Howner_1" as "(:owner' =1)".
    iDestruct "Howner_2" as "(:owner' =2)".
    iApply (owner₁_exclusive with "Howner₁_1 Howner₁_2").
  Qed.
  Lemma ws_bqueue_1_owner_model t ws vs :
    ws_bqueue_1_owner t ws -∗
    ws_bqueue_1_model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model)". subst t. injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_") as %->.
    iDestruct "Howner_1" as "(:owner' =1)".
    iApply (model₁_valid with "Howner₁_1 Hmodel₁").
  Qed.

  #[local] Lemma inv_state_Stable γ state front back hist vs priv prophs :
    length vs = back - front →
    inv_state γ state Stable front back hist vs priv prophs ⊢
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
  #[local] Lemma inv_state_Unstable γ state front back hist vs priv prophs :
    inv_state γ state Unstable front back hist vs priv prophs ⊢
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
  #[local] Lemma inv_state_Nonempty γ state stable front back hist vs priv prophs :
    front < back →
    inv_state γ state stable front back hist vs priv prophs ⊢
    ⌜state = Nonempty⌝.
  Proof.
    iIntros "% Hstate".
    destruct state.
    - iDestruct "Hstate" as "(:inv_state_empty)". lia.
    - done.
    - iDestruct "Hstate" as "(:inv_state_emptyish)". lia.
    - iDestruct "Hstate" as "(:inv_state_superempty)". lia.
  Qed.
  #[local] Lemma inv_state_Superempty γ state front back hist vs priv prophs :
    back < front →
    inv_state γ state Unstable front back hist vs priv prophs -∗
    ⌜state = Superempty⌝.
  Proof.
    iIntros "% Hstate".
    destruct state.
    - iDestruct "Hstate" as "(:inv_state_empty lazy=)". done.
    - iDestruct "Hstate" as "(:inv_state_nonempty lazy=)". done.
    - iDestruct "Hstate" as "(:inv_state_emptyish lazy=)". lia.
    - done.
  Qed.
  #[local] Lemma inv_state_winner_pop γ state stable front1 back hist vs priv prophs front2 P :
    inv_state γ state stable front1 back hist vs priv prophs -∗
    winner_pop γ front2 P -∗
      ∃ P_,
      ⌜front1 = front2⌝ ∗
      ▷ (P ≡ P_) ∗
      ( inv_state_nonempty_steal γ state stable front2 back hist vs prophs P_
      ∨ inv_state_emptyish_steal γ state stable front2 back hist priv P_
      ) ∗
      winner_pop γ front2 P.
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
        iDestruct (winner_agree with "Hwinner_pop Hwinner_steal") as "#(<- & $)".
        iSteps.
    - iDestruct "Hstate" as "(:inv_state_emptyish)".
      iDestruct "Hwinner" as "[Hwinner_pop_ | (:winner_linearized)]".
      + iDestruct (winner_pop_exclusive with "Hwinner_pop Hwinner_pop_") as %[].
      + iDestruct (winner_agree with "Hwinner_pop Hwinner_steal") as "#(<- & $)".
        iSteps.
    - iDestruct "Hstate" as "(:inv_state_superempty)".
      iDestruct "Hwinner" as "(:winner =3)".
      iDestruct (winner_pop_exclusive with "Hwinner_pop Hwinner_pop_3") as %[].
  Qed.
  #[local] Lemma inv_state_winner_steal γ state stable front1 back hist vs priv prophs front2 P :
    inv_state γ state stable front1 back hist vs priv prophs -∗
    winner_steal γ front2 P -∗
      ∃ P_,
      ⌜front1 = front2⌝ ∗
      ▷ (P_ ≡ P) ∗
      inv_state_emptyish_pop γ state stable front2 back hist priv P_ ∗
      winner_steal γ front2 P.
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
      iDestruct "Hwinner" as "[Hwinner_pop | (:winner_linearized !=)]".
      + iDestruct (winner_agree with "Hwinner_pop Hwinner_steal") as "#(<- & $)".
        iSteps.
      + iDestruct (winner_steal_exclusive with "Hwinner_steal Hwinner_steal_") as %[].
    - iDestruct "Hstate" as "(:inv_state_superempty)".
      iDestruct "Hwinner" as "(:winner =3)".
      iDestruct (winner_steal_exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
  Qed.

  Lemma ws_bqueue_1_create_spec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      ws_bqueue_1_create #cap
    {{{ t,
      RET t;
      ws_bqueue_1_inv t ι ₊cap ∗
      ws_bqueue_1_model t [] ∗
      ws_bqueue_1_owner t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp_rec.

    wp_apply (wise_prophets_wp_proph with "[//]") as (pid γ_prophet prophss) "Hprophet_model".

    wp_apply (array_unsafe_make_spec with "[//]") as (data) "Hdata_model"; first lia.
    iDestruct (array_model_to_cslice with "Hdata_model") as "Hdata_cslice".
    iEval (simpl_length) in "Hdata_cslice".
    iDestruct (array_cslice_rotation_right_0 1 with "Hdata_cslice") as "Hdata_cslice"; [simpl_length; lia.. |].
    iEval (rewrite rotation_replicate) in "Hdata_cslice".
    iDestruct "Hdata_cslice" as "(Hdata_cslice₁ & Hdata_cslice₂)".

    wp_block l as "Hmeta" "(Hl_capacity & Hl_front & Hl_back & Hl_data & Hl_proph & _)".
    iMod (pointsto_persist with "Hl_capacity") as "#Hl_capacity".
    iMod (pointsto_persist with "Hl_data") as "#Hl_data".
    iMod (pointsto_persist with "Hl_proph") as "#Hl_proph".

    iMod model_owner_alloc as "(%γ_model & %γ_owner & Hmodel₁ & Hmodel₂ & Howner₁ & Howner₂)".
    iMod front_alloc as "(%γ_front & Hfront_auth)".
    iMod history_alloc as "(%γ_history & Hhist_auth)".
    iMod winner_alloc as "(%γ_winner & Hwinner_pop & Hwinner_steal)".

    set γ := {|
      metadata_capacity := ₊cap ;
      metadata_data := data ;
      metadata_inv := ι ;
      metadata_prophet := pid ;
      metadata_prophet_name := γ_prophet ;
      metadata_model := γ_model ;
      metadata_owner := γ_owner ;
      metadata_front := γ_front ;
      metadata_history := γ_history ;
      metadata_winner := γ_winner ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Howner₁ Hdata_cslice₂".
    - iExists l, γ. unshelve iStep 8; first iSteps.
      iApply inv_alloc.
      iExists Empty, Stable, 1, 1, [()%V], [], (replicate ₊cap ()%V), (λ _, []), prophss. iFrameSteps.
      simpl_length.
    - iSteps. simpl_length.
  Qed.

  Lemma ws_bqueue_1_capacity_spec t ι cap :
    {{{
      ws_bqueue_1_inv t ι cap
    }}}
      ws_bqueue_1_capacity t
    {{{
      RET #cap;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    iSteps.
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
  #[local] Lemma front_spec_owner_Stable l γ back ws :
    {{{
      inv' l γ ∗
      owner₁ γ Stable back ws
    }}}
      (#l).{front}
    {{{ front,
      RET #front;
      owner₁ γ Stable back ws ∗
      front_lb γ front ∗
      ⌜front ≤ back⌝
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Howner₁) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
    iDestruct (inv_state_Stable with "Hstate") as "#(_ & %)"; first done.
    iSplitR "Howner₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma front_spec_owner_Unstable l γ back ws :
    {{{
      inv' l γ ∗
      owner₁ γ Unstable back ws
    }}}
      (#l).{front}
    {{{ front,
      RET #front;
      owner₁ γ Unstable back ws ∗
      front_lb γ front ∗
      ⌜front = back ∨ front = S back⌝
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Howner₁) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
    iDestruct (inv_state_Unstable with "Hstate") as "#(_ & %)".
    iSplitR "Howner₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma front_spec_Superempty l γ back ws front :
    back < front →
    {{{
      inv' l γ ∗
      owner₁ γ Unstable back ws ∗
      front_lb γ front
    }}}
      (#l).{front}
    {{{
      RET #front;
      owner₁ γ Unstable back ws
    }}}.
  Proof.
    iIntros "% %Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    iDestruct (inv_state_Superempty with "Hstate") as %->; first lia.
    iDestruct "Hstate" as "(:inv_state_superempty =1 lazy=)".
    iSplitR "Howner₁ HΦ". { iExists Superempty. iFrameSteps. }
    replace (S back) with front by lia.
    iSteps.
  Qed.
  #[local] Lemma front_spec_winner_steal l γ front P :
    {{{
      inv' l γ ∗
      winner_steal γ front P
    }}}
      (#l).{front}
    {{{
      RET #front;
      winner_steal γ front P
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

  #[local] Lemma back_spec l γ stable back ws :
    {{{
      inv' l γ ∗
      owner₁ γ stable back ws
    }}}
      (#l).{back}
    {{{
      RET #back;
      owner₁ γ stable back ws
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Howner₁) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as "(<- & <-)".
    iSplitR "Howner₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma set_back_spec_Superempty l γ back ws front (back' : Z) :
    back < front →
    back' = S back →
    {{{
      inv' l γ ∗
      owner₁ γ Unstable back ws ∗
      front_lb γ front
    }}}
      #l <-{back} #back'
    {{{
      RET ();
      owner₁ γ Stable (S back) ws
    }}}.
  Proof.
    iIntros (? ->) "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_store.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
    iMod (owner_update Stable (S back) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    iDestruct (inv_state_Superempty with "Hstate") as %->; first lia.
    iDestruct "Hstate" as "(:inv_state_superempty =1 lazy=)".
    iSplitR "Howner₁ HΦ". { iExists Empty. iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma array_unsafe_cget_spec_loser l γ i :
    (0 ≤ i)%Z →
    {{{
      inv' l γ
    }}}
      array_unsafe_cget γ.(metadata_data) #i
    {{{ v,
      RET v;
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ (:inv') HΦ".

    iApply wp_fupd.
    awp_apply (array_unsafe_cget_spec_atomic_weak with "[//]") without "HΦ"; first done.
    iInv "Hinv" as "(:inv_inner)".
    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    unshelve iStep 3. { iPureIntro. simpl_length. }
    all: iMod "Hclose" as "_".
    all: iSplitL; first iFrameSteps.
    all: iModIntro.
    1: iSteps.
    iIntros "%v H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ").
    iSteps.
  Qed.
  #[local] Lemma array_unsafe_cget_spec_winner_pop l γ front P v :
    {{{
      inv' l γ ∗
      winner_pop γ front P ∗
      history_at γ front v
    }}}
      array_unsafe_cget γ.(metadata_data) #front
    {{{
      RET v;
      winner_pop γ front P
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hwinner_pop & #Hhistory_at) HΦ".

    iApply wp_fupd.
    awp_apply (array_unsafe_cget_spec_atomic with "[//]") without "HΦ".
    iInv "Hinv" as "(:inv_inner =1)".

    iAssert (◇ (
      ⌜front1 = front⌝ ∗
      ⌜hd inhabitant (vs1 ++ priv1) = v⌝
    ))%I as "#>(-> & %Hlookup)".
    { iDestruct (inv_state_winner_pop with "Hstate [$Hwinner_pop]") as "(%P_ & >-> & _ & [(:inv_state_nonempty_steal =1 >) | (:inv_state_emptyish_steal =1 >)] & Hwinner_pop)".
      - iDestruct (history_at_agree with "Hhistory_at Hhistory_at_front1") as ">->".
        rewrite hd_app //; first lia.
      - iDestruct (history_at_agree with "Hhistory_at Hhistory_at_front1") as ">->".
        assert (length vs1 = 0) as ->%nil_length_inv by lia.
        iSteps.
    }
    apply hd_correct in Hlookup; last (simpl_length; lia).
    rewrite head_lookup in Hlookup.

    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    iExists _, front, _, _, v. rewrite Nat2Z.id Nat.sub_diag. iStep 3.
    all: iMod "Hclose" as "_".
    all: iSplitR "Hwinner_pop"; first iFrameSteps.
    all: iModIntro.
    1: iSteps.
    iIntros "H£ HΦ".
    iMod (lc_fupd_elim_later with "H£ HΦ").
    iSteps.
  Qed.

  #[local] Lemma array_unsafe_cset_spec_owner l γ back ws us front v :
    back < front + γ.(metadata_capacity) →
    {{{
      inv' l γ ∗
      owner' γ Stable back ws back us ∗
      front_lb γ front
    }}}
      array_unsafe_cset γ.(metadata_data) #back v
    {{{
      RET ();
      owner' γ Stable back ws back (<[0 := v]> us)
    }}}.
  Proof.
    iIntros "% %Φ ((:inv') & (:owner') & #Hfront_lb) HΦ".

    iApply wp_fupd.
    awp_apply (array_unsafe_cset_spec_atomic_cell with "[//]") without "HΦ".
    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    iDestruct (inv_state_Stable with "Hstate") as "#>(%Hstate1 & %)"; first done.

    iDestruct (array_cslice_app with "Hdata_cslice₁") as "(Hdata_cslice₁_1 & Hdata_cslice₁_2)".
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
    wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
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
      wise_prophets_full prophet γ.(metadata_prophet_name) front prophs0
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
    wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
    wp_apply (wp_cas_nobranch' with "Hl_front") as (b) "%Hcas Hl_front".
    iIntros "%prophs %Hprophss1 Hprophet_model".
    destruct b; zoo_simplify in Hcas; first subst front1.

    - iDestruct (wise_prophets_full_valid with "Hprophet_model Hprophet_full") as %->.
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
  #[local] Lemma resolve_spec_winner_pop l γ front P id :
    {{{
      inv' l γ ∗
      winner_pop γ front P
    }}}
      Resolve (CAS (#l).[front]%V #front #(front + 1)) #γ.(metadata_prophet) (#front, #id)%V
    {{{
      RET #true;
      ▷ P
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hwinner_pop) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
    wp_apply (wp_cas_nobranch' with "Hl_front") as (b) "%Hcas Hl_front".
    iIntros "%prophs %Hprophss1 Hprophet_model".
    iDestruct (inv_state_winner_pop with "Hstate Hwinner_pop") as "(%P_ & -> & #Heq & Hstate & Hwinner_pop)".
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

      iDestruct (array_cslice_rotation_right_1' (S front) 1 with "Hdata_cslice₁") as "Hdata_cslice₁"; [simpl_length/=; lia.. |].
      eassert (rotation _ _ = vs1 ++ priv1 ++ [v1]) as ->.
      { destruct_decide (γ.(metadata_capacity) = 1) as Heq | ?.
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

      iDestruct (array_cslice_rotation_right_1' (S back1) 1 with "Hdata_cslice₁") as "Hdata_cslice₁"; [simpl_length; lia.. |].
      iEval (rewrite /= -(app_nil_l (rotation _ _))) in "Hdata_cslice₁".

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
      winner_steal γ front P
    }}}
      Resolve (CAS (#l).[front]%V #front #(front + 1)) #γ.(metadata_prophet) (#front, #id)%V
    {{{
      RET #true;
      front_lb γ (S front)
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hwinner_steal) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
    wp_apply (wp_cas_nobranch' with "Hl_front") as (b) "%Hcas Hl_front".
    iIntros "%prophs %Hprophss1 Hprophet_model".
    iDestruct (inv_state_winner_steal with "Hstate Hwinner_steal") as "(%P_ & -> & _ & (:inv_state_emptyish_pop =1) & Hwinner_steal)".
    destruct b; zoo_simplify in Hcas; last congruence.
    iMod (front_update with "Hfront_auth") as "Hfront_auth".
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".

    assert (length vs1 = 0) as ->%nil_length_inv by lia.

    iDestruct (array_cslice_rotation_right_1' (S back1) 1 with "Hdata_cslice₁") as "Hdata_cslice₁"; [simpl_length; lia.. |].
    iEval (rewrite /= -(app_nil_l (rotation _ _))) in "Hdata_cslice₁".

    iSplitR "HΦ".
    { iExists Superempty. iFrameSteps; iPureIntro.
      - simpl_length.
      - intros.
        rewrite fn_lookup_alter_ne; first lia.
        apply Hpasts1; first lia.
    }
    iSteps.
  Qed.
  #[local] Lemma resolve_spec_Empty l γ back ws id :
    {{{
      inv' l γ ∗
      owner₁ γ Stable back ws ∗
      front_lb γ back
    }}}
      Resolve (CAS (#l).[front]%V #back #(back + 1)) #γ.(metadata_prophet) (#back, #id)%V
    {{{
      RET #true;
      owner₁ γ Unstable back ws ∗
      front_lb γ (S back)
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

    iInv "Hinv" as "(:inv_inner =1)".
    wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
    wp_apply (wp_cas_nobranch' with "Hl_front") as (b) "%Hcas Hl_front".
    iIntros "%prophs %Hprophss1 Hprophet_model".
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
    iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
    iDestruct (inv_state_Stable with "Hstate") as "#([-> | ->] & _)"; first done.

    - iDestruct "Hstate" as "(:inv_state_empty =1 lazy=)".
      assert (length vs1 = 0) as ->%nil_length_inv by lia.
      destruct b; zoo_simplify in Hcas; last lia.

      iMod (front_update with "Hfront_auth") as "Hfront_auth".
      iClear "Hfront_lb". iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
      iMod (history_update _ inhabitant with "Hhistory_auth") as "(Hhistory_auth & _)"; first done.
      iMod (owner_update Unstable (length hist1) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

      iDestruct (array_cslice_rotation_right_1' (S (length hist1)) 1 with "Hdata_cslice₁") as "Hdata_cslice₁"; [simpl_length; lia.. |].
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

  Lemma ws_bqueue_1_size_spec t ι cap ws :
    <<<
      ws_bqueue_1_inv t ι cap ∗
      ws_bqueue_1_owner t ws
    | ∀∀ vs,
      ws_bqueue_1_model t vs
    >>>
      ws_bqueue_1_size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bqueue_1_model t vs
    | RET #(length vs);
      ws_bqueue_1_owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct "Howner" as "(:owner')".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
    iDestruct (inv_state_Stable with "Hstate") as %(_ & Hback); first done.

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
    iMod (owner₁_update with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Howner₁ Hdata_cslice₂ HΦ". { iFrameSteps. }
    iModIntro. clear- Hcapacity Hus Hvs1 Hback.

    wp_apply (back_spec with "[$Howner₁]") as "Howner₁"; first iSteps.
    wp_pures.

    replace (⁺back - ⁺front1)%Z with ⁺(length vs) by lia.
    iSteps.
  Qed.

  Lemma ws_bqueue_1_is_empty_spec t ι cap ws :
    <<<
      ws_bqueue_1_inv t ι cap ∗
      ws_bqueue_1_owner t ws
    | ∀∀ vs,
      ws_bqueue_1_model t vs
    >>>
      ws_bqueue_1_is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bqueue_1_model t vs
    | RET #(bool_decide (vs = []%list));
      ws_bqueue_1_owner t vs
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_apply (ws_bqueue_1_size_spec with "[$]").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ (%Hvs & Howner)".
    wp_pures.

    rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
    { rewrite -length_zero_iff_nil. lia. }
    iApply "HΦ".
    iFrameSteps.
  Qed.

  Lemma ws_bqueue_1_push_spec t ι cap ws v :
    <<<
      ws_bqueue_1_inv t ι cap ∗
      ws_bqueue_1_owner t ws
    | ∀∀ vs,
      ws_bqueue_1_model t vs
    >>>
      ws_bqueue_1_push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bqueue_1_model t (if b then vs ++ [v] else vs)
    | RET #b;
      ws_bqueue_1_owner t (if b then vs ++ [v] else ws)
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    rename us into us0. iDestruct (owner'_rebase back with "Howner") as "(%us & (:owner'))"; first done.

    wp_rec. wp_pures.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).

    destruct_decide (back < front1 + γ.(metadata_capacity)) as Hif.

    - iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
      iSplitR "Howner₁ Hdata_cslice₂ HΦ". { iFrameSteps. }
      iModIntro. clear- Hcapacity Hus Hif.

      wp_smart_apply (back_spec with "[$Howner₁]") as "Howner₁"; first iSteps.
      wp_load.
      wp_smart_apply (array_size_spec_cslice with "Hdata_cslice₂") as "Hdata_cslice₂".
      wp_pures.
      rewrite bool_decide_eq_true_2; first lia.
      wp_smart_apply (array_unsafe_cset_spec_owner with "[$Howner₁ $Hdata_cslice₂]") as "(:owner' !=)"; [done | iSteps |].
      wp_pures.

      wp_bind (_ <-{back} _)%E.
      iInv "Hinv" as "(:inv_inner =2)".
      wp_store.
      iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
      iMod (owner_update Stable (S back) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iDestruct (inv_state_Stable with "Hstate") as "(%Hstate2 & %)"; first done.
      iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.

      iAssert ⌜head priv2 = Some v⌝%I as %(priv2' & ->)%head_Some.
      { iDestruct (array_cslice_rotation_right_small_1' back (length vs2) with "Hdata_cslice₁") as "Hdata_cslice₁"; [simpl_length; lia.. |].
        rewrite /rotation drop_app_length.
        rewrite head_lookup -(lookup_app_l _ (take (length vs2) (vs2 ++ priv2))); first lia.
        iDestruct (array_cslice_agree with "Hdata_cslice₁ Hdata_cslice₂") as %->.
        { simpl_length. lia. }
        rewrite list_lookup_insert //; first lia.
      }
      iEval (rewrite (assoc _ _ [_])) in "Hdata_cslice₁".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
      iMod (model_push v with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! true with "[$Hmodel₁]") as "HΦ".
      { iSteps; iPureIntro.
        - rewrite bool_decide_eq_true_2 //; first lia.
        - simpl_length/=. lia.
      }

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
      iModIntro. clear- Hcapacity Hus.

      iSteps. iPureIntro. simpl_length.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
      rewrite bool_decide_eq_false_2; first lia.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iFrameSteps.

      iSplitR "Howner₁ Hdata_cslice₂ HΦ". { iFrameSteps. }
      iModIntro. clear- Hcapacity Hus Hif.

      wp_smart_apply (back_spec with "[$Howner₁]") as "Howner₁"; first iSteps.
      wp_load.
      wp_smart_apply (array_size_spec_cslice with "Hdata_cslice₂") as "Hdata_cslice₂".
      iSteps.
  Qed.

  Lemma ws_bqueue_1_steal_spec t ι cap :
    <<<
      ws_bqueue_1_inv t ι cap
    | ∀∀ vs,
      ws_bqueue_1_model t vs
    >>>
      ws_bqueue_1_steal t @ ↑ι
    <<<
      ws_bqueue_1_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_apply (wp_id with "[//]") as (id) "Hid".
    wp_smart_apply front_spec as (front1) "#Hfront_lb_1"; first iSteps.
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
      iModIntro. clear- Hcapacity Hbranch1 Hbranch2.

      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_load.
      wp_smart_apply array_unsafe_cget_spec_loser as (v) "_"; [lia | iSteps |].
      wp_load.
      wp_smart_apply resolve_spec_loser_1; [done | iSteps |].
      iSteps.
    }

    iDestruct (wise_prophets_full_get _ front1 with "Hprophet_model") as "#Hprophet_full".
    iEval (rewrite Hpasts2 //=) in "Hprophet_full".

    destruct_decide (head $ prophss2 front1 = Some id) as (prophs0 & Hbranch3)%head_Some | Hbranch3; last first.
    { iSplitR "HΦ". { iFrameSteps. }
      remember (prophss2 front1) as prophs0.
      iModIntro. clear- Hcapacity Hbranch1 Hbranch3.

      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_load.
      wp_smart_apply array_unsafe_cget_spec_loser as (v) "_"; [lia | iSteps |].
      wp_load.
      wp_smart_apply resolve_spec_loser_2; [done | iSteps |].
      iSteps.
    }
    rewrite Hbranch3.

    iDestruct (inv_state_Nonempty with "Hstate") as %->; first done.
    iDestruct "Hstate" as "(:inv_state_nonempty =2)".
    iDestruct "Hwinner" as "[(:winner) | (:winner_pending_2 !=)]"; last first.
    { iDestruct (identifier_model_exclusive with "Hid Hid_") as %[]. }

    destruct vs2 as [| v vs2] => /=; first naive_solver lia.
    iMod (winner_update front1 (Φ (Some v)) with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

    iSplitR "Hwinner_pop".
    { iExists Nonempty. iFrameSteps.
      rewrite Hbranch3 /winner_pending_2. iSteps. iIntros "!> !>".
      rewrite /winner_au. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%v_ %vs' (-> & Hmodel₁ & Hhistory_at) !>".
      iDestruct (history_at_agree with "Hhistory_at Hhistory_at_front2") as %<-.
      simpl in Hvs. iSteps.
    }
    iModIntro. clear- Hcapacity Hbranch1.

    wp_pures.
    rewrite bool_decide_eq_false_2; first lia.
    wp_load.
    wp_smart_apply (array_unsafe_cget_spec_winner_pop with "[$Hwinner_pop]") as "Hwinner_pop"; first iSteps.
    wp_load.
    wp_smart_apply (resolve_spec_winner_pop with "[$Hwinner_pop]") as "HΦ"; first iSteps.
    iSteps.
  Qed.

  Inductive pop_state :=
    | PopNonempty v
    | PopEmptyishWinner v
    | PopEmptyishLoser
    | PopSuperempty.
  #[local] Lemma ws_bqueue_1_pop_0_spec {l γ} (state : pop_state) stable back (back_ : Z) ws us id :
    back_ = back →
    {{{
      inv' l γ ∗
      owner' γ stable back ws back us ∗
      match state with
      | PopNonempty v =>
          ⌜stable = Stable⌝ ∗
          ⌜us !! 0 = Some v⌝
      | PopEmptyishWinner v =>
          ⌜stable = Unstable⌝ ∗
          ⌜us !! 0 = Some v⌝ ∗
          winner_steal γ back inhabitant
      | PopEmptyishLoser =>
          ∃ id_winner prophs,
          ⌜stable = Unstable⌝ ∗
          wise_prophets_full prophet γ.(metadata_prophet_name) back (id_winner :: prophs) ∗
          ⌜head (id_winner :: prophs) ≠ Some id⌝
      | PopSuperempty =>
          ∃ front,
          ⌜stable = Unstable⌝ ∗
          front_lb γ front ∗
          ⌜front = S back⌝
      end
    }}}
      ws_bqueue_1_pop_0 #l #id #back_
    {{{ o back i us,
      RET o : val;
      owner' γ Stable back ws i us ∗
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

      wp_apply (front_spec_owner_Stable with "[$Howner₁]") as (front2) "(Howner₁ & #Hfront_lb_1 & %Hfront2)"; first iSteps.
      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_pures.
      case_bool_decide as Hbranch; wp_pures.

      + wp_load.
        wp_apply (array_unsafe_cget_spec with "Hdata_cslice₂"); [done.. | lia |].
        iSteps.

      + replace front2 with back by lia.

        wp_load.
        wp_smart_apply (resolve_spec_Empty with "[$Howner₁]") as "(Howner₁ & #Hfront_lb_2)"; first iSteps.
        wp_smart_apply (set_back_spec_Superempty with "[$Howner₁ $Hfront_lb_2]") as "Howner₁"; [lia.. | iSteps |].
        wp_load.
        wp_apply (array_unsafe_cget_spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
        iSteps.

    - iDestruct "H" as "(-> & %Hus_lookup & Hwinner_steal)".
      iSpecialize ("HΦ" $! (Some v)).

      wp_apply (front_spec_winner_steal with "[$Hwinner_steal]") as "Hwinner_steal"; first iSteps.
      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_load.
      wp_smart_apply (resolve_spec_winner_steal with "[$Hwinner_steal]") as "#Hfront_lb"; first iSteps.
      wp_smart_apply (set_back_spec_Superempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
      wp_load.
      wp_apply (array_unsafe_cget_spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
      iSteps.

    - iDestruct "H" as "(%id_winner & %prophs & -> & #Hprophet_full & %Hloser)".
      iSpecialize ("HΦ" $! None).

      wp_apply (front_spec_owner_Unstable with "[$Howner₁]") as (front2) "(Howner₁ & #Hfront_lb_1 & %Hbranch)"; first iSteps.
      wp_pures.
      destruct Hbranch as [-> | ->].

      + rewrite bool_decide_eq_false_2; first lia.
        wp_pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp_load.
        wp_smart_apply (resolve_spec_loser_2 with "[$Hfront_lb_1 $Hprophet_full]") as "#Hfront_lb_2"; [done | iSteps |].
        wp_smart_apply (set_back_spec_Superempty with "[$Howner₁ $Hfront_lb_2]") as "Howner₁"; [lia.. | iSteps |].
        iSteps.

      + rewrite bool_decide_eq_true_2; first lia.
        wp_smart_apply (set_back_spec_Superempty with "[$Howner₁ $Hfront_lb_1]") as "Howner₁"; [lia.. | iSteps |].
        iSteps.

    - iDestruct "H" as "(%front & -> & #Hfront_lb & ->)".
      iSpecialize ("HΦ" $! None).

      wp_apply (front_spec_Superempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia | iSteps |].
      wp_pures.
      rewrite bool_decide_eq_true_2; first lia.
      wp_smart_apply (set_back_spec_Superempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
      iSteps.
  Qed.
  Lemma ws_bqueue_1_pop_spec t ι cap ws :
    <<<
      ws_bqueue_1_inv t ι cap ∗
      ws_bqueue_1_owner t ws
    | ∀∀ vs,
      ws_bqueue_1_model t vs
    >>>
      ws_bqueue_1_pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_bqueue_1_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          ws_bqueue_1_model t vs'
      end
    | RET o;
      ws_bqueue_1_owner t ws'
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    rename us into us0. iDestruct (owner'_rebase (back - 1) with "Howner") as "(%us & (:owner'))"; first done.

    wp_rec.
    wp_apply (wp_id with "[//]") as (id) "Hid".
    wp_smart_apply (back_spec with "[$Howner₁]") as "Howner₁"; first iSteps.
    wp_pures.

    wp_bind (_ <-{back} _)%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_store.
    iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
    iDestruct (inv_state_Stable with "Hstate") as "#(%Hstate1 & %)"; first done.
    destruct Hstate1 as [-> | ->].

    { iDestruct "Hstate" as "(:inv_state_empty =1 lazy=)".
      assert (0 < back) as Hback by lia.
      assert (length vs1 = 0) as ->%nil_length_inv by lia.

      iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
      iMod (owner_update Unstable (back - 1) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (model_empty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! None with "[$Hmodel₁]") as "HΦ"; first iSteps.

      iSplitR "Howner₁ Hdata_cslice₂ HΦ".
      { iExists Superempty. iFrameSteps. }
      iModIntro. clear- Hcapacity Hus Hback.

      wp_smart_apply (ws_bqueue_1_pop_0_spec PopSuperempty _ (back - 1) with "[- HΦ]"); [lia | iFrameSteps |].
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
      { iDestruct (array_cslice_agree with "Hdata_cslice₁ Hdata_cslice₂") as %<-; first (simpl; lia).
        iSteps.
      }

      iMod (owner_update Unstable front1 with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

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
        iModIntro. clear- Hcapacity Hus Hback Hus_lookup.

        wp_smart_apply (ws_bqueue_1_pop_0_spec (PopEmptyishWinner v) _ front1 with "[- HΦ]"); [lia | iFrameSteps |].
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
          iModIntro. clear- Hcapacity Hus Hus_lookup.

          wp_smart_apply (ws_bqueue_1_pop_0_spec (PopEmptyishWinner v) _ front1 with "[- HΦ]"); [lia | iFrameSteps |].
          iSteps.
        }

        iDestruct (wise_prophets_full_get _ front1 with "Hprophet_model") as "#Hprophet_full".
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
        iModIntro. clear- Hcapacity Hus Hbranch2.

        wp_smart_apply (ws_bqueue_1_pop_0_spec PopEmptyishLoser _ front1 with "[- HΦ]"); [lia | iFrameSteps |].
        iSteps.

    - iMod (owner_update Stable (back - 1) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iEval (rewrite -assoc) in "Hdata_cslice₁".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (model_pop' with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

      iAssert ⌜us !! 0 = Some v⌝%I as %Hus_lookup.
      { iDestruct (array_cslice_rotation_right_small_1' (back - 1) (length vs1) with "Hdata_cslice₁") as "Hdata_cslice₁"; [simpl_length/=; lia.. |].
        iDestruct (array_cslice_agree with "Hdata_cslice₁ Hdata_cslice₂") as %<-.
        { simpl_length/=. lia. }
        rewrite /rotation drop_app_length //.
      }

      iSplitR "Howner₁ Hdata_cslice₂ HΦ".
      { iExists Nonempty. iFrameSteps.
        rewrite hd_app //; first lia.
      }
      iModIntro. clear- Hcapacity Hus Hback Hus_lookup.

      wp_smart_apply (ws_bqueue_1_pop_0_spec (PopNonempty v) _ (back - 1) with "[- HΦ]"); [lia | iFrameSteps |].
      iSteps.
  Qed.
End ws_bqueue_1_G.

From zoo_saturn Require
  ws_bqueue_1__opaque.

#[global] Opaque ws_bqueue_1_inv.
#[global] Opaque ws_bqueue_1_model.
#[global] Opaque ws_bqueue_1_owner.
