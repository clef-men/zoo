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
  ws_bdeque_1__code.
From zoo_saturn Require Import
  ws_bdeque_1__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types front front_cache back : nat.
Implicit Types id : prophet_id.
Implicit Types v : val.
Implicit Types us vs ws hist priv : list val.
Implicit Types past prophs : list prophet_identifier.(prophet_typed_type).
Implicit Types pasts prophss : nat → list prophet_identifier.(prophet_typed_type).

Variant state :=
  | Empty
  | Nonempty
  | Emptyish
  | Superempty.
Implicit Types state : state.

#[local] Instance state_inhabited : Inhabited state :=
  populate Empty.

Variant stability :=
  | Stable
  | Unstable.
Implicit Types stable : stability.

#[local] Instance stability_inhabited : Inhabited stability :=
  populate Stable.

Class WsBdeque1G Σ `{zoo_G : !ZooG Σ} :=
  { #[local] ws_bdeque_1_G_prophet_G :: ProphetMultiG Σ prophet_identifier
  ; #[local] ws_bdeque_1_G_model_G :: AuthTwinsG Σ (leibnizO (list val)) suffix
  ; #[local] ws_bdeque_1_G_owner_G :: TwinsG Σ (leibnizO (stability * nat))
  ; #[local] ws_bdeque_1_G_front_G :: AuthNatMaxG Σ
  ; #[local] ws_bdeque_1_G_history_G :: MonoListG Σ val
  ; #[local] ws_bdeque_1_G_winner_G :: TwinsG Σ (natO * ▶ ∙)
  }.

Definition ws_bdeque_1_Σ := #[
  prophet_multi_Σ prophet_identifier ;
  auth_twins_Σ (leibnizO (list val)) suffix ;
  twins_Σ (leibnizO (stability * nat)) ;
  auth_nat_max_Σ ;
  mono_list_Σ val ;
  twins_Σ (natO * ▶ ∙)
].
#[global] Instance subG_ws_bdeque_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_bdeque_1_Σ Σ →
  WsBdeque1G Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section ws_bdeque_1_G.
    Context `{ws_bdeque_1_G : WsBdeque1G Σ}.

    Implicit Types t : location.
    Implicit Types P : iProp Σ.

    Record ws_bdeque_1_name :=
      { ws_bdeque_1_name_capacity : nat
      ; ws_bdeque_1_name_data : val
      ; ws_bdeque_1_name_inv : namespace
      ; ws_bdeque_1_name_prophet : prophet_id
      ; ws_bdeque_1_name_prophet_name : prophet_multi_name
      ; ws_bdeque_1_name_model : auth_twins_name
      ; ws_bdeque_1_name_owner : gname
      ; ws_bdeque_1_name_front : gname
      ; ws_bdeque_1_name_history : gname
      ; ws_bdeque_1_name_winner : gname
      }.
    Implicit Types γ : ws_bdeque_1_name.

    #[global] Instance ws_bdeque_1_name_eq_dec : EqDecision ws_bdeque_1_name :=
      ltac:(solve_decision).
    #[global] Instance ws_bdeque_1_name_countable :
      Countable ws_bdeque_1_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      auth_twins_twin1 _ γ_model vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(ws_bdeque_1_name_model).
    #[local] Definition model₂' γ_model vs :=
      auth_twins_twin2 _ γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(ws_bdeque_1_name_model).

    #[local] Definition owner₁' γ_owner γ_model stable back ws : iProp Σ :=
      twins_twin1 (twins_G := ws_bdeque_1_G_owner_G) γ_owner (DfracOwn 1) (stable, back) ∗
      auth_twins_auth _ γ_model ws.
    #[local] Definition owner₁ γ :=
      owner₁' γ.(ws_bdeque_1_name_owner) γ.(ws_bdeque_1_name_model).
    #[local] Instance : CustomIpat "owner₁" :=
      " ( Howner₁{_{}}
        & Hmodel_auth{_{}}
        )
      ".
    #[local] Definition owner₂' γ_owner stable back :=
      twins_twin2 (twins_G := ws_bdeque_1_G_owner_G) γ_owner (stable, back).
    #[local] Definition owner₂ γ :=
      owner₂' γ.(ws_bdeque_1_name_owner).

    #[local] Definition front_auth' γ_front :=
      auth_nat_max_auth γ_front (DfracOwn 1).
    #[local] Definition front_auth γ :=
      front_auth' γ.(ws_bdeque_1_name_front).
    #[local] Definition front_lb γ :=
      auth_nat_max_lb γ.(ws_bdeque_1_name_front).

    #[local] Definition history_auth' γ_history :=
      mono_list_auth γ_history (DfracOwn 1).
    #[local] Definition history_auth γ :=
      history_auth' γ.(ws_bdeque_1_name_history).
    #[local] Definition history_at γ :=
      mono_list_at γ.(ws_bdeque_1_name_history).

    #[local] Definition winner_pop' γ_winner front P : iProp Σ :=
      twins_twin1 γ_winner (DfracOwn 1) (front, Next P).
    #[local] Definition winner_pop γ :=
      winner_pop' γ.(ws_bdeque_1_name_winner).
    #[local] Definition winner_steal' γ_winner front P :=
      twins_twin2 γ_winner (front, Next P).
    #[local] Definition winner_steal γ :=
      winner_steal' γ.(ws_bdeque_1_name_winner).
    #[local] Definition winner γ : iProp Σ :=
      ∃ front P1 P2,
      winner_pop γ front P1 ∗
      winner_steal γ front P2.
    #[local] Instance : CustomIpat "winner" :=
      " ( %front_winner
        & %P_winner_1
        & %P_winner_2
        & Hwinner_pop{_{}}
        & Hwinner_steal{_{}}
        )
      ".

    #[local] Definition winner_au γ front P : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(ws_bdeque_1_name_inv), ∅ <{
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
    #[local] Instance : CustomIpat "winner_pending_1" :=
      " ( Hwinner_steal{_{!}}
        & Hid{_{!}}
        & HP
        )
      ".
    #[local] Definition winner_pending_2 γ front id : iProp Σ :=
      ∃ P,
      winner_pending_1 γ front P id.
    #[local] Instance : CustomIpat "winner_pending_2" :=
      " ( %P{}
        & (:winner_pending_1)
        )
      ".
    #[local] Definition winner_linearized γ front P : iProp Σ :=
      winner_steal γ front P ∗
      P.
    #[local] Instance : CustomIpat "winner_linearized" :=
      " ( Hwinner_steal{_{!}}
        & HP
        )
      ".

    #[local] Definition inv_state_empty γ stable front back hist : iProp Σ :=
      ⌜stable = Stable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = front⌝ ∗
      winner γ.
    #[local] Instance : CustomIpat "inv_state_empty" :=
      " ( { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}%Hhist{}
        & Hwinner
        )
      ".
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
    #[local] Instance : CustomIpat "inv_state_nonempty" :=
      " ( { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}%
        & {>;}%Hhist{}
        & #Hhistory_at_front{}
        & Hwinner
        )
      ".
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
    #[local] Instance : CustomIpat "inv_state_nonempty_steal" :=
      " ( {>;}->
        & { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}%
        & {>;}%Hhist{}
        & #Hhistory_at_front{}
        & Hwinner
        )
      ".
    #[local] Definition inv_state_emptyish γ stable front back hist priv : iProp Σ :=
      ∃ P,
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = S front⌝ ∗
      history_at γ front (hd inhabitant priv) ∗
      ( winner_pop γ front P
      ∨ winner_linearized γ front P
      ).
    #[local] Instance : CustomIpat "inv_state_emptyish" :=
      " ( %P_
        & { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}%Hhist{}
        & #Hhistory_at_front{}
        & Hwinner
        )
      ".
    #[local] Definition inv_state_emptyish_pop γ state stable front back hist priv P : iProp Σ :=
      ⌜state = Emptyish⌝ ∗
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = S front⌝ ∗
      history_at γ front (hd inhabitant priv) ∗
      winner_pop γ front P.
    #[local] Instance : CustomIpat "inv_state_emptyish_pop" :=
      " ( {>;}->
        & { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}%Hhist{}
        & #Hhistory_at_front{}
        & Hwinner_pop
        )
      ".
    #[local] Definition inv_state_emptyish_steal γ state stable front back hist priv P : iProp Σ :=
      ⌜state = Emptyish⌝ ∗
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = S front⌝ ∗
      history_at γ front (hd inhabitant priv) ∗
      winner_linearized γ front P.
    #[local] Instance : CustomIpat "inv_state_emptyish_steal" :=
      " ( {>;}->
        & { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}%Hhist{}
        & #Hhistory_at_front{}
        & (:winner_linearized)
        )
      ".
    #[local] Definition inv_state_superempty γ stable front back hist : iProp Σ :=
      ⌜stable = Unstable⌝ ∗
      ⌜front = S back⌝ ∗
      ⌜length hist = front⌝ ∗
      winner γ.
    #[local] Instance : CustomIpat "inv_state_superempty" :=
      " ( { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}%Hhist{}
        & Hwinner
        )
      ".
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

    #[local] Definition inv_inner t γ : iProp Σ :=
      ∃ state stable front back hist vs priv pasts prophss,
      t.[front] ↦ #front ∗
      t.[back] ↦ #back ∗
      owner₂ γ stable back ∗
      front_auth γ front ∗
      ⌜0 < front⌝ ∗
      model₂ γ vs ∗
      ⌜length vs = back - front⌝ ∗
      array_cslice γ.(ws_bdeque_1_name_data) γ.(ws_bdeque_1_name_capacity) front (DfracOwn (1/2)) (vs ++ priv) ∗
      ⌜(length vs + length priv)%nat = γ.(ws_bdeque_1_name_capacity)⌝ ∗
      history_auth γ hist ∗
      prophet_multi_model prophet_identifier γ.(ws_bdeque_1_name_prophet) γ.(ws_bdeque_1_name_prophet_name) pasts prophss ∗
      ⌜∀ i, front ≤ i → pasts i = []⌝ ∗
      inv_state γ state stable front back hist vs priv (prophss front).
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %state{}
        & %stable{}
        & %front{}
        & %back{}
        & %hist{}
        & %vs{}
        & %priv{}
        & %pasts{}
        & %prophss{}
        & >Ht_front
        & >Ht_back
        & >Howner₂
        & >Hfront_auth
        & >%Hfront{}
        & >Hmodel₂
        & >%Hvs{}
        & >Hdata_cslice₁
        & >%Hdata{}
        & >Hhistory_auth
        & >Hprophet_model
        & >%Hpasts{}
        & Hstate
        )
      ".
    #[local] Definition inv' t γ : iProp Σ :=
      ⌜0 < γ.(ws_bdeque_1_name_capacity)⌝ ∗
      t.[capacity] ↦□ #γ.(ws_bdeque_1_name_capacity) ∗
      t.[data] ↦□ γ.(ws_bdeque_1_name_data) ∗
      t.[proph] ↦□ #γ.(ws_bdeque_1_name_prophet) ∗
      inv γ.(ws_bdeque_1_name_inv) (inv_inner t γ).
    #[local] Instance : CustomIpat "inv'" :=
      " ( %Hcapacity
        & #Ht_capacity
        & #Ht_data
        & #Ht_proph
        & #Hinv
        )
      ".
    Definition ws_bdeque_1_inv t γ ι cap : iProp Σ :=
      ⌜ι = γ.(ws_bdeque_1_name_inv)⌝ ∗
      ⌜cap = γ.(ws_bdeque_1_name_capacity)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & ->
        & (:inv')
        )
      ".

    Definition ws_bdeque_1_model γ vs : iProp Σ :=
      model₁ γ vs ∗
      ⌜length vs ≤ γ.(ws_bdeque_1_name_capacity)⌝.
    #[local] Instance : CustomIpat "model" :=
      " ( Hmodel₁{_{}}
        & %Hvs{}
        )
      ".

    Variant owner_flag :=
      | OwnerNormal
      | OwnerPop.
    #[local] Definition owner_1 flag t γ stable back ws front_cache i us : iProp Σ :=
      owner₁ γ stable back ws ∗
      t.[front_cache] ↦ #front_cache ∗
      front_lb γ front_cache ∗
      ⌜(if flag is OwnerPop then S back else back) ≤ front_cache + γ.(ws_bdeque_1_name_capacity)⌝ ∗
      array_cslice γ.(ws_bdeque_1_name_data) γ.(ws_bdeque_1_name_capacity) i (DfracOwn (1/2)) us ∗
      ⌜length us = γ.(ws_bdeque_1_name_capacity)⌝.
    #[local] Instance : CustomIpat "owner_1" :=
      " ( Howner₁{_{}}
        & Ht_front_cache{_{}}
        & { {!} _
          ; #Hfront_lb_cache_{}
          ; #Hfront_lb_cache
          } &
          { {!} _
          ; %Hfront_cache_{}
          ; %Hfront_cache
          }
        & Hdata_cslice₂{_{}}
        & { {!} _
          ; %Hus{}
          ; %Hus
          }
        )
      ".
    #[local] Definition owner_2 :=
      owner_1 OwnerNormal.
    #[local] Instance : CustomIpat "owner_2" :=
      " (:owner_1)
      ".
    Definition ws_bdeque_1_owner t γ ws : iProp Σ :=
      ∃ back front_cache i us,
      owner_2 t γ Stable back ws front_cache i us.
    #[local] Instance : CustomIpat "owner" :=
      " ( %back{}
        & %front_cache{_{}}
        & %i{}
        & %us{}
        & Howner{_{}}
        )
      ".

    #[global] Instance ws_bdeque_1_model_timeless γ vs :
      Timeless (ws_bdeque_1_model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ws_bdeque_1_owner_timeless t γ ws :
      Timeless (ws_bdeque_1_owner t γ ws).
    Proof.
      apply _.
    Qed.

    #[global] Instance ws_bdeque_1_inv_persistent t γ ι cap :
      Persistent (ws_bdeque_1_inv t γ ι cap).
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
      iMod (auth_twins_alloc _ (auth_twins_G := ws_bdeque_1_G_model_G)) as "(%γ_model & Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iMod (twins_alloc' (twins_G := ws_bdeque_1_G_owner_G)) as "(%γ_owner & Howner₁ & Howner₂)".
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

    Lemma ws_bdeque_1_model_valid t γ ι cap vs :
      ws_bdeque_1_inv t γ ι cap -∗
      ws_bdeque_1_model γ vs -∗
      ⌜length vs ≤ cap⌝.
    Proof.
      iSteps.
    Qed.
    Lemma ws_bdeque_1_model_exclusive γ vs1 vs2 :
      ws_bdeque_1_model γ vs1 -∗
      ws_bdeque_1_model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    #[local] Lemma owner_2_rebase {t γ stable back ws front_cache i1 us} i2 :
      0 < γ.(ws_bdeque_1_name_capacity) →
      owner_2 t γ stable back ws front_cache i1 us ⊢
        ∃ us,
        owner_2 t γ stable back ws front_cache i2 us.
    Proof.
      iIntros "%Hcapacity (:owner_2)".
      iDestruct (array_cslice_rebase i2 with "Hdata_cslice₂") as "(%us' & %n & -> & Hdata_cslice₂ & _)"; [done.. |].
      iSteps. simpl_length.
    Qed.

    Lemma ws_bdeque_1_owner_exclusive t γ ws1 ws2 :
      ws_bdeque_1_owner t γ ws1 -∗
      ws_bdeque_1_owner t γ ws2 -∗
      False.
    Proof.
      iIntros "(:owner =1) (:owner =2)".
      iDestruct "Howner_1" as "(:owner_2 =1)".
      iDestruct "Howner_2" as "(:owner_2 =2)".
      iApply (owner₁_exclusive with "Howner₁_1 Howner₁_2").
    Qed.
    Lemma ws_bdeque_1_owner_model t γ ws vs :
      ws_bdeque_1_owner t γ ws -∗
      ws_bdeque_1_model γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:owner =1) (:model =2)".
      iDestruct "Howner_1" as "(:owner_2 =1)".
      iApply (model₁_valid with "Howner₁_1 Hmodel₁_2").
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

    Lemma ws_bdeque_1_create𑁒spec ι (cap : Z) :
      (0 < cap)%Z →
      {{{
        True
      }}}
        ws_bdeque_1_create #cap
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        ws_bdeque_1_inv t γ ι ₊cap ∗
        ws_bdeque_1_model γ [] ∗
        ws_bdeque_1_owner t γ []
      }}}.
    Proof.
      iIntros "%Hcap %Φ _ HΦ".

      wp_rec.

      wp_apply (prophet_multi_wp_proph with "[//]") as (pid γ_prophet prophss) "Hprophet_model".

      wp_apply (array_unsafe_make𑁒spec with "[//]") as (data) "Hdata_model"; first lia.
      iDestruct (array_model_to_cslice with "Hdata_model") as "Hdata_cslice".
      iEval (simpl_length) in "Hdata_cslice".
      iDestruct (array_cslice_rotation_right_0 1 with "Hdata_cslice") as "Hdata_cslice"; [simpl_length; lia.. |].
      iEval (rewrite rotation_replicate) in "Hdata_cslice".
      iDestruct "Hdata_cslice" as "(Hdata_cslice₁ & Hdata_cslice₂)".

      wp_block t as "Hmeta" "(Ht_capacity & Ht_front & Ht_front_cache & Ht_back & Ht_data & Ht_proph & _)".
      iMod (pointsto_persist with "Ht_capacity") as "#Ht_capacity".
      iMod (pointsto_persist with "Ht_data") as "#Ht_data".
      iMod (pointsto_persist with "Ht_proph") as "#Ht_proph".

      iMod model_owner_alloc as "(%γ_model & %γ_owner & Hmodel₁ & Hmodel₂ & Howner₁ & Howner₂)".
      iMod front_alloc as "(%γ_front & Hfront_auth)".
      iMod history_alloc as "(%γ_history & Hhist_auth)".
      iMod winner_alloc as "(%γ_winner & Hwinner_pop & Hwinner_steal)".

      set γ :=
        {|ws_bdeque_1_name_capacity := ₊cap
        ; ws_bdeque_1_name_data := data
        ; ws_bdeque_1_name_inv := ι
        ; ws_bdeque_1_name_prophet := pid
        ; ws_bdeque_1_name_prophet_name := γ_prophet
        ; ws_bdeque_1_name_model := γ_model
        ; ws_bdeque_1_name_owner := γ_owner
        ; ws_bdeque_1_name_front := γ_front
        ; ws_bdeque_1_name_history := γ_history
        ; ws_bdeque_1_name_winner := γ_winner
        |}.

      iDestruct (front_lb_get γ with "Hfront_auth") as "#Hfront_lb".

      iApply ("HΦ" $! t γ).
      iFrame "#∗". iSplitL.
      - iStep 4.
        iApply inv_alloc.
        iExists Empty, Stable, 1, 1, [()%V], [], (replicate ₊cap ()%V), (λ _, []), prophss. iFrameSteps.
        iPureIntro. simpl_length.
      - iSteps.
        iPureIntro. simpl_length.
    Qed.

    Lemma ws_bdeque_1_capacity𑁒spec t γ ι cap :
      {{{
        ws_bdeque_1_inv t γ ι cap
      }}}
        ws_bdeque_1_capacity #t
      {{{
        RET #cap;
        True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec. wp_load.
      iSteps.
    Qed.

    #[local] Lemma front𑁒spec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
        front_lb γ front
      }}}.
    Proof.
      iIntros "%Φ (:inv') HΦ".

      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_1".
      iFrameSteps.
    Qed.
    #[local] Lemma front𑁒spec_owner_Stable t γ back ws :
      {{{
        inv' t γ ∗
        owner₁ γ Stable back ws
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
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
      iFrameSteps.
    Qed.
    #[local] Lemma front𑁒spec_owner_Unstable t γ back ws :
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back ws
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
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
      iFrameSteps.
    Qed.
    #[local] Lemma front𑁒spec_Superempty t γ back ws front :
      back < front →
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back ws ∗
        front_lb γ front
      }}}
        (#t).{front}
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
    #[local] Lemma front𑁒spec_winner_steal t γ front P :
      {{{
        inv' t γ ∗
        winner_steal γ front P
      }}}
        (#t).{front}
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

      iFrameSteps.
    Qed.

    #[local] Lemma back𑁒spec t γ stable back ws :
      {{{
        inv' t γ ∗
        owner₁ γ stable back ws
      }}}
        (#t).{back}
      {{{
        RET #back;
        owner₁ γ stable back ws
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv_inner =1)".
      wp_load.
      iDestruct (owner_agree with "Howner₁ Howner₂") as "(<- & <-)".
      iFrameSteps.
    Qed.

    #[local] Lemma set_back𑁒spec_Superempty t γ back ws front (back' : Z) :
      back < front →
      back' = S back →
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back ws ∗
        front_lb γ front
      }}}
        #t <-{back} #back'
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

    #[local] Lemma array_unsafe_cget𑁒spec_loser t γ i :
      (0 ≤ i)%Z →
      {{{
        inv' t γ
      }}}
        array_unsafe_cget γ.(ws_bdeque_1_name_data) #i
      {{{
        v
      , RET v;
        True
      }}}.
    Proof.
      iIntros "%Hi %Φ (:inv') HΦ".

      iApply wp_fupd.
      awp_apply (array_unsafe_cget𑁒spec_atomic_weak with "[//]") without "HΦ"; first done.
      iInv "Hinv" as "(:inv_inner)".
      iAaccIntro with "[$Hdata_cslice₁]".
      { iPureIntro. simpl_length. }
      { iIntros "(Hdata_cslice₁ & _) !>". iFrameSteps. }
      iIntros "Hdata_cslice₁ !>".
      iSplitL. { iFrameSteps. }
      iIntros "%v H£ HΦ".
      iApply (lc_fupd_elim_later with "H£ HΦ [//]").
    Qed.
    #[local] Lemma array_unsafe_cget𑁒spec_winner_pop t γ front P v :
      {{{
        inv' t γ ∗
        winner_pop γ front P ∗
        history_at γ front v
      }}}
        array_unsafe_cget γ.(ws_bdeque_1_name_data) #front
      {{{
        RET v;
        winner_pop γ front P
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_pop & #Hhistory_at) HΦ".

      iApply wp_fupd.
      awp_apply (array_unsafe_cget𑁒spec_atomic with "[//]") without "HΦ".
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

      iAaccIntro with "[$Hdata_cslice₁]".
      { rewrite Nat2Z.id Nat.sub_diag. iSteps. }
      { iIntros "(_ & _ & Hdata_cslice₁) !>". iFrameSteps. }
      iIntros "Hdata_cslice₁ !>".
      iSplitR "Hwinner_pop". { iFrameSteps. }
      iIntros "H£ HΦ".
      iApply (lc_fupd_elim_later with "H£ HΦ Hwinner_pop").
    Qed.

    #[local] Lemma array_unsafe_cset𑁒spec_owner t γ back ws front_cache us front v :
      back < front + γ.(ws_bdeque_1_name_capacity) →
      {{{
        inv' t γ ∗
        owner_2 t γ Stable back ws front_cache back us ∗
        front_lb γ front
      }}}
        array_unsafe_cset γ.(ws_bdeque_1_name_data) #back v
      {{{
        RET ();
        owner_2 t γ Stable back ws front_cache back (<[0 := v]> us)
      }}}.
    Proof.
      iIntros "% %Φ ((:inv') & (:owner_2) & #Hfront_lb) HΦ".

      iApply wp_fupd.
      awp_apply (array_unsafe_cset𑁒spec_atomic_cell with "[//]") without "HΦ".
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
      iEval (rewrite Nat.add_0_r) in "Hdata_back₂ Hdata_cslice₂".

      iDestruct (array_cslice_combine with "Hdata_back₁ Hdata_back₂") as "(%Heq & Hdata_back)"; first done. injection Heq as <-.
      iEval (rewrite dfrac_op_own Qp.half_half) in "Hdata_back".

      iAaccIntro with "[$Hdata_back]". 1: iSteps.

      - iIntros "(_ & (Hdata_back₁ & Hdata_back₂)) !>".

        iDestruct (array_cslice_app_1 with "Hdata_cslice₁_1 (Hdata_cslice₁_2 Hdata_back₁)") as "Hdata_cslice₁"; first done.
        iEval (rewrite list_insert_id //) in "Hdata_cslice₁".

        iDestruct ("Hdata_cslice₂" with "Hdata_back₂") as "Hdata_cslice₂".
        iEval (rewrite list_insert_id //) in "Hdata_cslice₂".

        iFrameSteps.

      - iIntros "(Hdata_back₁ & Hdata_back₂) !>".

        iDestruct (array_cslice_app_1 with "Hdata_cslice₁_1 (Hdata_cslice₁_2 Hdata_back₁)") as "Hdata_cslice₁"; first done.

        iDestruct ("Hdata_cslice₂" with "Hdata_back₂") as "Hdata_cslice₂".

        iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂".
        { iFrameSteps.
          - iPureIntro. simpl_length.
          - iExists state1.
            destruct Hstate1 as [-> | ->]; iFrameSteps.
        }
        iIntros "H£ HΦ".

        iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
        iSteps. iPureIntro. simpl_length.
    Qed.

    #[local] Lemma resolve𑁒spec_loser_1 t γ front1 front2 id :
      front1 < front2 →
      {{{
        inv' t γ ∗
        front_lb γ front2
      }}}
        Resolve (CAS (#t).[front]%V #front1 #(front1 + 1)) #γ.(ws_bdeque_1_name_prophet) (#front1, #id)%V
      {{{
        RET false;
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
    #[local] Lemma resolve𑁒spec_loser_2 t γ front id prophs0 :
      head prophs0 ≠ Some id →
      {{{
        inv' t γ ∗
        front_lb γ front ∗
        prophet_multi_full prophet_identifier γ.(ws_bdeque_1_name_prophet_name) front prophs0
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(ws_bdeque_1_name_prophet) (#front, #id)%V
      {{{
        RET false;
        front_lb γ (S front)
      }}}.
    Proof.
      iIntros "%Hloser %Φ ((:inv') & #Hfront_lb & #Hprophet_full) HΦ".

      iInv "Hinv" as "(:inv_inner =1)".
      iDestruct (front_lb_valid with "Hfront_auth Hfront_lb") as %?.
      wp_apply (prophet_multi_wp_resolve' with "Hprophet_model"); [done.. |].
      wp_apply (wp_cas_nobranch' with "Ht_front") as (b) "%Hcas Ht_front".
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
    #[local] Lemma resolve𑁒spec_winner_pop t γ front P id :
      {{{
        inv' t γ ∗
        winner_pop γ front P
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(ws_bdeque_1_name_prophet) (#front, #id)%V
      {{{
        RET true;
        ▷ P
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_pop) HΦ".

      iInv "Hinv" as "(:inv_inner =1)".
      wp_apply (prophet_multi_wp_resolve' with "Hprophet_model"); [done.. |].
      wp_apply (wp_cas_nobranch' with "Ht_front") as (b) "%Hcas Ht_front".
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
        { destruct_decide (γ.(ws_bdeque_1_name_capacity) = 1) as Heq | ?.
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
    #[local] Lemma resolve𑁒spec_winner_steal t γ front P id :
      {{{
        inv' t γ ∗
        winner_steal γ front P
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(ws_bdeque_1_name_prophet) (#front, #id)%V
      {{{
        RET true;
        front_lb γ (S front)
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_steal) HΦ".

      iInv "Hinv" as "(:inv_inner =1)".
      wp_apply (prophet_multi_wp_resolve' with "Hprophet_model"); [done.. |].
      wp_apply (wp_cas_nobranch' with "Ht_front") as (b) "%Hcas Ht_front".
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
    #[local] Lemma resolve𑁒spec_Empty t γ back ws id :
      {{{
        inv' t γ ∗
        owner₁ γ Stable back ws ∗
        front_lb γ back
      }}}
        Resolve (CAS (#t).[front]%V #back #(back + 1)) #γ.(ws_bdeque_1_name_prophet) (#back, #id)%V
      {{{
        RET true;
        owner₁ γ Unstable back ws ∗
        front_lb γ (S back)
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv_inner =1)".
      wp_apply (prophet_multi_wp_resolve' with "Hprophet_model"); [done.. |].
      wp_apply (wp_cas_nobranch' with "Ht_front") as (b) "%Hcas Ht_front".
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

    Lemma ws_bdeque_1_size𑁒spec t γ ι cap ws :
      <<<
        ws_bdeque_1_inv t γ ι cap ∗
        ws_bdeque_1_owner t γ ws
      | ∀∀ vs,
        ws_bdeque_1_model γ vs
      >>>
        ws_bdeque_1_size #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_1_model γ vs
      | RET #(length vs);
        ws_bdeque_1_owner t γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".
      iDestruct "Howner" as "(:owner_2)".

      wp_rec.

      wp_bind (_.{front})%E.
      iInv "Hinv" as "(:inv_inner =1)".
      wp_load.
      iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
      iDestruct (inv_state_Stable with "Hstate") as %(_ & Hback); first done.

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
      iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
      iMod (owner₁_update with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁ //]") as "HΦ".

      iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ". { iFrameSteps. }
      iIntros "!> {%- Hcapacity Hfront_cache Hus Hvs1 Hback}".

      wp_apply (back𑁒spec with "[$Howner₁]") as "Howner₁"; first iSteps.
      wp_pures.

      replace (⁺back - ⁺front1)%Z with ⁺(length vs) by lia.
      iSteps.
    Qed.

    Lemma ws_bdeque_1_is_empty𑁒spec t γ ι cap ws :
      <<<
        ws_bdeque_1_inv t γ ι cap ∗
        ws_bdeque_1_owner t γ ws
      | ∀∀ vs,
        ws_bdeque_1_model γ vs
      >>>
        ws_bdeque_1_is_empty #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_1_model γ vs
      | RET #(bool_decide (vs = []%list));
        ws_bdeque_1_owner t γ vs
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & Howner) HΦ".

      wp_rec.
      wp_apply (ws_bdeque_1_size𑁒spec with "[$]").
      iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ (%Hvs & Howner)".
      wp_pures.

      rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
      { rewrite -length_zero_iff_nil. lia. }
      iApply "HΦ".
      iFrameSteps.
    Qed.

    #[local] Definition push_au t γ ws v Φ : iProp Σ :=
      AU <{
        ∃∃ vs,
        ws_bdeque_1_model γ vs
      }> @ ⊤ ∖ ↑γ.(ws_bdeque_1_name_inv), ∅ <{
        ∀∀ b,
        ⌜b = bool_decide (length vs < γ.(ws_bdeque_1_name_capacity))⌝ ∗
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_1_model γ (if b then vs ++ [v] else vs)
      , COMM
        ws_bdeque_1_owner t γ (if b then vs ++ [v] else ws) -∗
        Φ #b
      }>.
    Lemma ws_bdeque_1_push𑁒spec t γ ι cap ws v :
      <<<
        ws_bdeque_1_inv t γ ι cap ∗
        ws_bdeque_1_owner t γ ws
      | ∀∀ vs,
        ws_bdeque_1_model γ vs
      >>>
        ws_bdeque_1_push #t v @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_1_model γ (if b then vs ++ [v] else vs)
      | RET #b;
        ws_bdeque_1_owner t γ (if b then vs ++ [v] else ws)
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".
      rename us into us0. iDestruct (owner_2_rebase back with "Howner") as "(%us & (:owner_2))"; first done.

      wp_rec.
      wp_apply+ (back𑁒spec with "[$Howner₁]") as "Howner₁"; first iSteps.
      wp_load.
      wp_apply+ (array_size𑁒spec_cslice with "Hdata_cslice₂") as "Hdata_cslice₂".
      wp_load. wp_pures.

      wp_bind (_ or _)%E.
      wp_apply (wp_wand (λ res,
        ∃ b front_cache,
        ⌜res = #b⌝ ∗
        t.[front_cache] ↦ #front_cache ∗
        front_lb γ front_cache ∗
        owner₁ γ Stable back ws ∗
        if b then
          ⌜back < front_cache + γ.(ws_bdeque_1_name_capacity)⌝ ∗
          push_au t γ ws v Φ
        else
          ⌜back ≤ front_cache + γ.(ws_bdeque_1_name_capacity)⌝ ∗
          (ws_bdeque_1_owner t γ ws -∗ Φ false%V)
      )%I with "[Howner₁ Ht_front_cache HΦ]") as (res) "{Hfront_lb_cache} {% front_cache Hfront_cache} (%b & %front_cache & -> & Ht_front_cache & #Hfront_lb_cache & Howner₁ & HΦ)".
      { case_bool_decide; wp_pures.

        - iStep. iFrame "#∗". iSteps.

        - wp_rec.

          wp_bind (_.{front})%E.
          wp_apply (wp_wand (λ res,
            ∃ front,
            ⌜res = #front⌝ ∗
            front_lb γ front ∗
            owner₁ γ Stable back ws ∗
            if bool_decide (front_cache < front) then
              ⌜back < front + γ.(ws_bdeque_1_name_capacity)⌝ ∗
              push_au t γ ws v Φ
            else
              ⌜back ≤ front + γ.(ws_bdeque_1_name_capacity)⌝ ∗
              (ws_bdeque_1_owner t γ ws -∗ Φ false%V)
          )%I with "[Howner₁ HΦ]") as (res) "(%front & -> & #Hfront_lb & Howner₁ & HΦ)".
          { iInv "Hinv" as "(:inv_inner =1)".
            wp_load.
            iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
            iDestruct (front_lb_get with "Hfront_auth") as "#$".
            case_bool_decide. 1: iFrameSteps.

            iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
            iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
            rewrite bool_decide_eq_false_2; first lia.
            iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iFrameSteps.

            iFrameSteps.
          }

          wp_store. wp_pures.

          iFrame "#∗". iPureIntro.
          erewrite bool_decide_ext; [done | lia].
      }

      destruct b; wp_pures.

      - iDestruct "HΦ" as "(%Hfront_cache & HΦ)".

        wp_apply (array_unsafe_cset𑁒spec_owner with "[$Howner₁ $Ht_front_cache $Hdata_cslice₂]") as "(:owner_2 !=)"; [done | iSteps |].
        wp_pures.

        wp_bind (_ <-{back} _)%E.
        iInv "Hinv" as "(:inv_inner =2)".
        wp_store.
        iDestruct (owner_agree with "Howner₁ Howner₂") as %(<- & <-).
        iMod (owner_update Stable (S back) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
        iDestruct (inv_state_Stable with "Hstate") as "(%Hstate2 & %)"; first done.
        iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_cache") as %?.

        iAssert ⌜head priv2 = Some v⌝%I as %(priv2' & ->)%head_Some.
        { iDestruct (array_cslice_rotation_right_small_1' back (length vs2) with "Hdata_cslice₁") as "Hdata_cslice₁"; [simpl_length; lia.. |].
          rewrite /rotation drop_app_length.
          rewrite head_lookup -(lookup_app_l _ (take (length vs2) (vs2 ++ priv2))); first lia.
          iDestruct (array_cslice_agree with "Hdata_cslice₁ Hdata_cslice₂") as %->.
          { simpl_length. lia. }
          rewrite list_lookup_insert_eq //; first lia.
        }
        iEval (rewrite (assoc _ _ [_])) in "Hdata_cslice₁".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
        iMod (model_push v with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! true with "[$Hmodel₁]") as "HΦ".
        { iSteps; iPureIntro.
          - rewrite bool_decide_eq_true_2 //; first lia.
          - simpl_length/=. lia.
        }

        iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ".
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
        iIntros "!> {%- Hcapacity Hfront_cache Hus}".

        iSteps. iPureIntro. simpl_length.

      - iDestruct "HΦ" as "(%Hfront_cache & HΦ)".

        iApply "HΦ".
        iFrameSteps.
    Qed.

    Lemma ws_bdeque_1_steal𑁒spec t γ ι cap :
      <<<
        ws_bdeque_1_inv t γ ι cap
      | ∀∀ vs,
        ws_bdeque_1_model γ vs
      >>>
        ws_bdeque_1_steal #t @ ↑ι
      <<<
        ws_bdeque_1_model γ (tail vs)
      | RET head vs;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp_rec.
      wp_apply (wp_id with "[//]") as (id) "Hid".
      wp_apply+ front𑁒spec as (front1) "#Hfront_lb_1"; first iSteps.
      wp_pures.

      wp_bind (_.{back})%E.
      iInv "Hinv" as "(:inv_inner =2)".
      wp_load.
      iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_1") as %?.

      destruct_decide (front1 < back2) as Hbranch1; last first.
      { assert (length vs2 = 0) as ->%nil_length_inv by lia.

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΦ" with "[$Hmodel₁ //] [//]") as "HΦ".

        iFrameSteps.
      }

      destruct_decide (front1 = front2) as <- | ?; last first.
      { assert (front1 < front2) as Hbranch2 by lia.
        iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_2".
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hcapacity Hbranch1 Hbranch2}".

        wp_pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp_load.
        wp_apply+ array_unsafe_cget𑁒spec_loser as (v) "_"; [lia | iSteps |].
        wp_load.
        wp_apply+ resolve𑁒spec_loser_1; [done | iSteps |].
        iSteps.
      }

      iDestruct (prophet_multi_full_get _ front1 with "Hprophet_model") as "#Hprophet_full".
      iEval (rewrite Hpasts2 //=) in "Hprophet_full".

      destruct_decide (head $ prophss2 front1 = Some id) as (prophs0 & Hbranch3)%head_Some | Hbranch3; last first.
      { iSplitR "HΦ". { iFrameSteps. }
        remember (prophss2 front1) as prophs0.
        iIntros "!> {%- Hcapacity Hbranch1 Hbranch3}".

        wp_pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp_load.
        wp_apply+ array_unsafe_cget𑁒spec_loser as (v) "_"; [lia | iSteps |].
        wp_load.
        wp_apply+ resolve𑁒spec_loser_2; [done | iSteps |].
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
        iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
        iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%v_ %vs' (-> & Hmodel₁ & Hhistory_at) !>".
        iDestruct (history_at_agree with "Hhistory_at Hhistory_at_front2") as %<-.
        simpl in Hvs. iSteps.
      }
      iIntros "!> {%- Hcapacity Hbranch1}".

      wp_pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp_load.
      wp_apply+ (array_unsafe_cget𑁒spec_winner_pop with "[$Hwinner_pop]") as "Hwinner_pop"; first iSteps.
      wp_load.
      wp_apply+ (resolve𑁒spec_winner_pop with "[$Hwinner_pop]") as "HΦ"; first iSteps.
      iSteps.
    Qed.

    Variant pop_state :=
      | PopNonempty v
      | PopEmptyishWinner v
      | PopEmptyishLoser
      | PopSuperempty.
    #[local] Lemma ws_bdeque_1_pop₀𑁒spec {t γ} (state : pop_state) {stable} back ws front_cache us id (back_ : Z) :
      back_ = back →
      {{{
        inv' t γ ∗
        owner_1 OwnerPop t γ stable back ws front_cache back us ∗
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
            prophet_multi_full prophet_identifier γ.(ws_bdeque_1_name_prophet_name) back (id_winner :: prophs) ∗
            ⌜head (id_winner :: prophs) ≠ Some id⌝
        | PopSuperempty =>
            ∃ front,
            ⌜stable = Unstable⌝ ∗
            front_lb γ front ∗
            ⌜front = S back⌝
        end
      }}}
        ws_bdeque_1_pop₀ #t #id #back_
      {{{
        o back front_cache i us
      , RET o;
        owner_2 t γ Stable back ws front_cache i us ∗
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
      iIntros (->) "%Φ ((:inv') & (:owner_1) & H) HΦ".

      wp_rec. wp_pures.
      destruct state.

      - iDestruct "H" as "(-> & %Hus_lookup)".
        iSpecialize ("HΦ" $! (Some v)).

        wp_apply (front𑁒spec_owner_Stable with "[$Howner₁]") as (front2) "(Howner₁ & #Hfront_lb & %Hfront2)"; first iSteps.
        wp_pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp_pures.
        case_bool_decide as Hbranch; wp_pures.

        + wp_load.
          wp_apply (array_unsafe_cget𑁒spec with "Hdata_cslice₂"); [done.. | lia |].
          iSteps.

        + replace front2 with back by lia.

          wp_store. wp_load.
          wp_apply+ (resolve𑁒spec_Empty with "[$Howner₁]") as "{Hfront_lb} (Howner₁ & #Hfront_lb)"; first iSteps.
          wp_apply+ (set_back𑁒spec_Superempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
          wp_load.
          wp_apply (array_unsafe_cget𑁒spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
          wp_pures.

          iApply "HΦ".
          iFrame "#∗". iSteps.

      - iDestruct "H" as "(-> & %Hus_lookup & Hwinner_steal)".
        iSpecialize ("HΦ" $! (Some v)).

        wp_apply (front𑁒spec_winner_steal with "[$Hwinner_steal]") as "Hwinner_steal"; first iSteps.
        wp_pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp_pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp_store. wp_load.
        wp_apply+ (resolve𑁒spec_winner_steal with "[$Hwinner_steal]") as "#Hfront_lb"; first iSteps.
        wp_apply+ (set_back𑁒spec_Superempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
        wp_load.
        wp_apply (array_unsafe_cget𑁒spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
        wp_pures.

        iApply "HΦ".
        iFrame "#∗". iSteps.

      - iDestruct "H" as "(%id_winner & %prophs & -> & #Hprophet_full & %Hloser)".
        iSpecialize ("HΦ" $! None).

        wp_apply (front𑁒spec_owner_Unstable with "[$Howner₁]") as (front2) "(Howner₁ & #Hfront_lb & %Hbranch)"; first iSteps.
        wp_pures.
        destruct Hbranch as [-> | ->].

        + rewrite bool_decide_eq_false_2; first lia.
          wp_pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp_store. wp_load.
          wp_apply+ (resolve𑁒spec_loser_2 with "[$Hfront_lb $Hprophet_full]") as "{Hfront_lb} #Hfront_lb"; [done | iSteps |].
          wp_apply+ (set_back𑁒spec_Superempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
          wp_pures.

          iApply "HΦ".
          iFrame "#∗". iSteps.

        + rewrite bool_decide_eq_true_2; first lia.
          wp_apply+ (set_back𑁒spec_Superempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
          iSteps.

      - iDestruct "H" as "(%front & -> & #Hfront_lb & ->)".
        iSpecialize ("HΦ" $! None).

        wp_apply (front𑁒spec_Superempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia | iSteps |].
        wp_pures.
        rewrite bool_decide_eq_true_2; first lia.
        wp_apply+ (set_back𑁒spec_Superempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
        iSteps.
    Qed.
    Lemma ws_bdeque_1_pop𑁒spec t γ ι cap ws :
      <<<
        ws_bdeque_1_inv t γ ι cap ∗
        ws_bdeque_1_owner t γ ws
      | ∀∀ vs,
        ws_bdeque_1_model γ vs
      >>>
        ws_bdeque_1_pop #t @ ↑ι
      <<<
        ∃∃ o ws',
        ⌜vs `suffix_of` ws⌝ ∗
        match o with
        | None =>
            ⌜vs = []⌝ ∗
            ⌜ws' = []⌝ ∗
            ws_bdeque_1_model γ []
        | Some v =>
            ∃ vs',
            ⌜vs = vs' ++ [v]⌝ ∗
            ⌜ws' = vs'⌝ ∗
            ws_bdeque_1_model γ vs'
        end
      | RET o;
        ws_bdeque_1_owner t γ ws'
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".
      rename us into us0. iDestruct (owner_2_rebase (back - 1) with "Howner") as "(%us & (:owner_2))"; first done.

      wp_rec.
      wp_apply (wp_id with "[//]") as (id) "Hid".
      wp_apply+ (back𑁒spec with "[$Howner₁]") as "Howner₁"; first iSteps.
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

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (model_empty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! None with "[$Hmodel₁ //]") as "HΦ".

        iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ".
        { iExists Superempty. iFrameSteps. }
        iIntros "!> {%- Hcapacity Hfront_cache Hus Hback}".

        wp_apply+ (ws_bdeque_1_pop₀𑁒spec PopSuperempty (back - 1) with "[- HΦ]"); [lia | iFrameSteps |].
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

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
          iMod (model_pop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
          iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

          iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ Hwinner_steal HΦ".
          { iExists Emptyish. iFrameSteps. }
          iIntros "!> {%- Hcapacity Hfront_cache Hus Hback Hus_lookup}".

          wp_apply+ (ws_bdeque_1_pop₀𑁒spec (PopEmptyishWinner v) front1 with "[- HΦ]"); [lia | iFrameSteps |].
          iSteps.

        + iDestruct "Hwinner" as "[(:winner) | Hwinner]".

          { iMod (winner_update front1 inhabitant with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

            iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
            iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
            iMod (model_pop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
            iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

            iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ Hwinner_steal HΦ".
            { iExists Emptyish. iFrameSteps. }
            iIntros "!> {%- Hcapacity Hfront_cache Hus Hus_lookup}".

            wp_apply+ (ws_bdeque_1_pop₀𑁒spec (PopEmptyishWinner v) front1 with "[- HΦ]"); [lia | iFrameSteps |].
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

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
          iMod (model_empty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" $! None with "[$Hmodel₁ //]") as "HΦ".

          iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ".
          { iExists Emptyish. iFrameStep 7. iExists P. iSteps. }
          iIntros "!> {%- Hcapacity Hfront_cache Hus Hbranch2}".

          wp_apply+ (ws_bdeque_1_pop₀𑁒spec PopEmptyishLoser front1 with "[- HΦ]"); [lia | iFrameSteps |].
          iSteps.

      - iMod (owner_update Stable (back - 1) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
        iEval (rewrite -assoc) in "Hdata_cslice₁".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model_owner₁_agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (model_pop' with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

        iAssert ⌜us !! 0 = Some v⌝%I as %Hus_lookup.
        { iDestruct (array_cslice_rotation_right_small_1' (back - 1) (length vs1) with "Hdata_cslice₁") as "Hdata_cslice₁"; [simpl_length/=; lia.. |].
          iDestruct (array_cslice_agree with "Hdata_cslice₁ Hdata_cslice₂") as %<-.
          { simpl_length/=. lia. }
          rewrite /rotation drop_app_length //.
        }

        iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ".
        { iExists Nonempty. iFrameSteps.
          rewrite hd_app //; first lia.
        }
        iIntros "!> {%- Hcapacity Hfront_cache Hus Hback Hus_lookup}".

        wp_apply+ (ws_bdeque_1_pop₀𑁒spec (PopNonempty v) (back - 1) with "[- HΦ]"); [lia | iFrameSteps |].
        iSteps.
    Qed.
  End ws_bdeque_1_G.

  #[global] Opaque ws_bdeque_1_inv.
  #[global] Opaque ws_bdeque_1_model.
  #[global] Opaque ws_bdeque_1_owner.
End base.

From zoo_saturn Require
  ws_bdeque_1__opaque.

Section ws_bdeque_1_G.
  Context `{ws_bdeque_1_G : WsBdeque1G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition ws_bdeque_1_inv t ι cap : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ws_bdeque_1_inv 𝑡 γ ι cap.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition ws_bdeque_1_model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ws_bdeque_1_model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition ws_bdeque_1_owner t ws : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ws_bdeque_1_owner 𝑡 γ ws.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Howner{_{}}
      )
    ".

  #[global] Instance ws_bdeque_1_model_timeless γ vs :
    Timeless (ws_bdeque_1_model γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_bdeque_1_owner_timeless γ ws :
    Timeless (ws_bdeque_1_owner γ ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_bdeque_1_inv_persistent t ι cap :
    Persistent (ws_bdeque_1_inv t ι cap).
  Proof.
    apply _.
  Qed.

  Lemma ws_bdeque_1_model_valid t ι cap vs :
    ws_bdeque_1_inv t ι cap -∗
    ws_bdeque_1_model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_1_model_valid with "Hinv_1 Hmodel_2").
  Qed.
  Lemma ws_bdeque_1_model_exclusive t vs1 vs2 :
    ws_bdeque_1_model t vs1 -∗
    ws_bdeque_1_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_1_model_exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma ws_bdeque_1_owner_exclusive t ws1 ws2 :
    ws_bdeque_1_owner t ws1 -∗
    ws_bdeque_1_owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_1_owner_exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma ws_bdeque_1_owner_model γ ws vs :
    ws_bdeque_1_owner γ ws -∗
    ws_bdeque_1_model γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_1_owner_model with "Howner_1 Hmodel_2").
  Qed.

  Lemma ws_bdeque_1_create𑁒spec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      ws_bdeque_1_create #cap
    {{{
      t
    , RET t;
      ws_bdeque_1_inv t ι ₊cap ∗
      ws_bdeque_1_model t [] ∗
      ws_bdeque_1_owner t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.ws_bdeque_1_create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel & Howner)"; first done.
    iMod (meta_set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma ws_bdeque_1_capacity𑁒spec t ι cap :
    {{{
      ws_bdeque_1_inv t ι cap
    }}}
      ws_bdeque_1_capacity t
    {{{
      RET #cap;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ws_bdeque_1_capacity𑁒spec with "[$] HΦ").
  Qed.

  Lemma ws_bdeque_1_size𑁒spec t ι cap ws :
    <<<
      ws_bdeque_1_inv t ι cap ∗
      ws_bdeque_1_owner t ws
    | ∀∀ vs,
      ws_bdeque_1_model t vs
    >>>
      ws_bdeque_1_size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_1_model t vs
    | RET #(length vs);
      ws_bdeque_1_owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.ws_bdeque_1_size𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_1_is_empty𑁒spec t ι cap ws :
    <<<
      ws_bdeque_1_inv t ι cap ∗
      ws_bdeque_1_owner t ws
    | ∀∀ vs,
      ws_bdeque_1_model t vs
    >>>
      ws_bdeque_1_is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_1_model t vs
    | RET #(bool_decide (vs = []%list));
      ws_bdeque_1_owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.ws_bdeque_1_is_empty𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_1_push𑁒spec t ι cap ws v :
    <<<
      ws_bdeque_1_inv t ι cap ∗
      ws_bdeque_1_owner t ws
    | ∀∀ vs,
      ws_bdeque_1_model t vs
    >>>
      ws_bdeque_1_push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_1_model t (if b then vs ++ [v] else vs)
    | RET #b;
      ws_bdeque_1_owner t (if b then vs ++ [v] else ws)
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.ws_bdeque_1_push𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_1_steal𑁒spec t ι cap :
    <<<
      ws_bdeque_1_inv t ι cap
    | ∀∀ vs,
      ws_bdeque_1_model t vs
    >>>
      ws_bdeque_1_steal t @ ↑ι
    <<<
      ws_bdeque_1_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.ws_bdeque_1_steal𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_1_pop𑁒spec t ι cap ws :
    <<<
      ws_bdeque_1_inv t ι cap ∗
      ws_bdeque_1_owner t ws
    | ∀∀ vs,
      ws_bdeque_1_model t vs
    >>>
      ws_bdeque_1_pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_bdeque_1_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          ws_bdeque_1_model t vs'
      end
    | RET o;
      ws_bdeque_1_owner t ws'
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.ws_bdeque_1_pop𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1". 1: iSteps. iIntros "%o %ws' ($ & Ho)".
      iExists o, ws'. destruct o.
      all: iDecompose "Ho".
      all: iFrameSteps.
    }
  Qed.
End ws_bdeque_1_G.

#[global] Opaque ws_bdeque_1_inv.
#[global] Opaque ws_bdeque_1_model.
#[global] Opaque ws_bdeque_1_owner.
