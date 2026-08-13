Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.function.
Require Import zoo.common.relations.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.auth_twins.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_identifier.
Require Import zoo.program_logic.prophet_multi.
Require Import zoo_std.option.
Require Export zoo_saturn.ws_bdeque_1__code.
Require Import zoo_saturn.ws_bdeque_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type front front_cache back : nat.
Implicit Type id : prophet_id.
Implicit Type v : val.
Implicit Type us vs ws hist priv : list val.
Implicit Type past prophs : list prophet_identifier.(prophet_typed۰type).
Implicit Type pasts prophss : nat → list prophet_identifier.(prophet_typed۰type).

Variant state :=
  | Empty
  | Nonempty
  | Emptyish
  | Superempty.
Implicit Type state : state.

#[local] Instance stateｰinhabited : Inhabited state :=
  populate Empty.

Variant stability :=
  | Stable
  | Unstable.
Implicit Type stable : stability.

#[local] Instance stabilityｰinhabited : Inhabited stability :=
  populate Stable.

Class WsBdeque1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] ws_bdeque_1۰G۰prophet۰G :: ProphetMultiG Σ prophet_identifier
  ; #[local] ws_bdeque_1۰G۰model۰G :: AuthTwinsG Σ (leibnizO (list val)) suffix
  ; #[local] ws_bdeque_1۰G۰owner۰G :: TwinsG Σ (leibnizO (stability * nat))
  ; #[local] ws_bdeque_1۰G۰front۰G :: AuthNatMaxG Σ
  ; #[local] ws_bdeque_1۰G۰history۰G :: MonoListG Σ val
  ; #[local] ws_bdeque_1۰G۰winner۰G :: TwinsG Σ (natO * ▶ ∙)
  }.

Definition ws_bdeque_1۰Σ :=
  #[prophet_multi۰Σ prophet_identifier
  ; auth_twins۰Σ (leibnizO (list val)) suffix
  ; twins۰Σ (leibnizO (stability * nat))
  ; auth_nat_max۰Σ
  ; mono_list۰Σ val
  ; twins۰Σ (natO * ▶ ∙)
  ].
#[global] Instance subGｰws_bdeque_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG ws_bdeque_1۰Σ Σ →
  WsBdeque1G Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section ws_bdeque_1۰G.
    Context `{ws_bdeque_1۰G : WsBdeque1G Σ}.

    Implicit Type t : location.
    Implicit Type P : iProp Σ.

    Record ws_bdeque_1۰name :=
      { ws_bdeque_1۰name۰capacity : nat
      ; ws_bdeque_1۰name۰data : val
      ; ws_bdeque_1۰name۰inv : namespace
      ; ws_bdeque_1۰name۰prophet : prophet_id
      ; ws_bdeque_1۰name۰prophet_name : prophet_multi۰name
      ; ws_bdeque_1۰name۰model : auth_twins۰name
      ; ws_bdeque_1۰name۰owner : gname
      ; ws_bdeque_1۰name۰front : gname
      ; ws_bdeque_1۰name۰history : gname
      ; ws_bdeque_1۰name۰winner : gname
      }.
    Implicit Type γ : ws_bdeque_1۰name.

    #[global] Instance ws_bdeque_1۰nameｰeq_dec : EqDecision ws_bdeque_1۰name :=
      ltac:(solve_decision).
    #[global] Instance ws_bdeque_1۰nameｰcountable :
      Countable ws_bdeque_1۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      auth_twins۰twin₁ _ γ_model vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(ws_bdeque_1۰name۰model).
    #[local] Definition model₂' γ_model vs :=
      auth_twins۰twin₂ _ γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(ws_bdeque_1۰name۰model).

    #[local] Definition owner₁' γ_owner γ_model stable back ws : iProp Σ :=
      twins۰twin₁ (twins۰G := ws_bdeque_1۰G۰owner۰G) γ_owner (DfracOwn 1) (stable, back) ∗
      auth_twins۰auth _ γ_model ws.
    #[local] Definition owner₁ γ :=
      owner₁' γ.(ws_bdeque_1۰name۰owner) γ.(ws_bdeque_1۰name۰model).
    #[local] Instance : CustomIpat "owner₁" :=
      " ( Howner₁{_{}}
        & Hmodel_auth{_{}}
        )
      ".
    #[local] Definition owner₂' γ_owner stable back :=
      twins۰twin₂ (twins۰G := ws_bdeque_1۰G۰owner۰G) γ_owner (stable, back).
    #[local] Definition owner₂ γ :=
      owner₂' γ.(ws_bdeque_1۰name۰owner).

    #[local] Definition front۰auth' γ_front :=
      auth_nat_max۰auth γ_front (DfracOwn 1).
    #[local] Definition front۰auth γ :=
      front۰auth' γ.(ws_bdeque_1۰name۰front).
    #[local] Definition front۰lb γ :=
      auth_nat_max۰lb γ.(ws_bdeque_1۰name۰front).

    #[local] Definition history۰auth' γ_history :=
      mono_list۰auth γ_history (DfracOwn 1).
    #[local] Definition history۰auth γ :=
      history۰auth' γ.(ws_bdeque_1۰name۰history).
    #[local] Definition history۰at γ :=
      mono_list۰at γ.(ws_bdeque_1۰name۰history).

    #[local] Definition winner۰pop' γ_winner front P : iProp Σ :=
      twins۰twin₁ γ_winner (DfracOwn 1) (front, Next P).
    #[local] Definition winner۰pop γ :=
      winner۰pop' γ.(ws_bdeque_1۰name۰winner).
    #[local] Definition winner۰steal' γ_winner front P :=
      twins۰twin₂ γ_winner (front, Next P).
    #[local] Definition winner۰steal γ :=
      winner۰steal' γ.(ws_bdeque_1۰name۰winner).
    #[local] Definition winner γ : iProp Σ :=
      ∃ front P1 P2,
      winner۰pop γ front P1 ∗
      winner۰steal γ front P2.
    #[local] Instance : CustomIpat "winner" :=
      " ( %front_winner
        & %P_winner_1
        & %P_winner_2
        & Hwinner_pop{_{}}
        & Hwinner_steal{_{}}
        )
      ".

    #[local] Definition winner۰au γ front P : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(ws_bdeque_1۰name۰inv), ∅ <{
        ∀∀ v vs',
        ⌜vs = v :: vs'⌝ ∗
        model₁ γ vs' ∗
        history۰at γ front v
      , COMM
        P
      }>.
    #[local] Definition winner۰pending₁ γ front P id : iProp Σ :=
      winner۰steal γ front P ∗
      identifier۰model id ∗
      winner۰au γ front P.
    #[local] Instance : CustomIpat "winner۰pending₁" :=
      " ( Hwinner_steal{_{!}}
        & Hid{_{!}}
        & HP
        )
      ".
    #[local] Definition winner۰pending₂ γ front id : iProp Σ :=
      ∃ P,
      winner۰pending₁ γ front P id.
    #[local] Instance : CustomIpat "winner۰pending₂" :=
      " ( %P{}
        & (:winner۰pending₁)
        )
      ".
    #[local] Definition winner۰linearized γ front P : iProp Σ :=
      winner۰steal γ front P ∗
      P.
    #[local] Instance : CustomIpat "winner۰linearized" :=
      " ( Hwinner_steal{_{!}}
        & HP
        )
      ".

    #[local] Definition inv۰state۰empty γ stable front back hist : iProp Σ :=
      ⌜stable = Stable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = front⌝ ∗
      winner γ.
    #[local] Instance : CustomIpat "inv۰state۰empty" :=
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
    #[local] Definition inv۰state۰nonempty γ stable front back hist vs prophs : iProp Σ :=
      ⌜stable = Stable⌝ ∗
      ⌜front < back⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      history۰at γ front (hd inhabitant vs) ∗
      ( winner γ
      ∨ match prophs with
        | [] =>
            False
        | id :: _ =>
            winner۰pending₂ γ front id
        end
      ).
    #[local] Instance : CustomIpat "inv۰state۰nonempty" :=
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
    #[local] Definition inv۰state۰nonempty۰steal γ state stable front back hist vs prophs P : iProp Σ :=
      ⌜state = Nonempty⌝ ∗
      ⌜stable = Stable⌝ ∗
      ⌜front < back⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      history۰at γ front (hd inhabitant vs) ∗
      match prophs with
      | [] =>
          False
      | id :: _ =>
          winner۰pending₁ γ front P id
      end.
    #[local] Instance : CustomIpat "inv۰state۰nonempty۰steal" :=
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
    #[local] Definition inv۰state۰emptyish γ stable front back hist priv : iProp Σ :=
      ∃ P,
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      history۰at γ front (hd inhabitant priv) ∗
      ( winner۰pop γ front P
      ∨ winner۰linearized γ front P
      ).
    #[local] Instance : CustomIpat "inv۰state۰emptyish" :=
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
    #[local] Definition inv۰state۰emptyish۰pop γ state stable front back hist priv P : iProp Σ :=
      ⌜state = Emptyish⌝ ∗
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      history۰at γ front (hd inhabitant priv) ∗
      winner۰pop γ front P.
    #[local] Instance : CustomIpat "inv۰state۰emptyish۰pop" :=
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
    #[local] Definition inv۰state۰emptyish۰steal γ state stable front back hist priv P : iProp Σ :=
      ⌜state = Emptyish⌝ ∗
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      history۰at γ front (hd inhabitant priv) ∗
      winner۰linearized γ front P.
    #[local] Instance : CustomIpat "inv۰state۰emptyish۰steal" :=
      " ( {>;}->
        & { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}%Hhist{}
        & #Hhistory_at_front{}
        & (:winner۰linearized)
        )
      ".
    #[local] Definition inv۰state۰superempty γ stable front back hist : iProp Σ :=
      ⌜stable = Unstable⌝ ∗
      ⌜front = ˖back⌝ ∗
      ⌜length hist = front⌝ ∗
      winner γ.
    #[local] Instance : CustomIpat "inv۰state۰superempty" :=
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
    #[local] Definition inv۰state γ state stable front back hist vs priv prophs : iProp Σ :=
      match state with
      | Empty =>
          inv۰state۰empty γ stable front back hist
      | Nonempty =>
          inv۰state۰nonempty γ stable front back hist vs prophs
      | Emptyish =>
          inv۰state۰emptyish γ stable front back hist priv
      | Superempty =>
          inv۰state۰superempty γ stable front back hist
      end.

    #[local] Definition inv۰inner t γ : iProp Σ :=
      ∃ state stable front back hist vs priv pasts prophss,
      t.[front] ↦ #front ∗
      t.[back] ↦ #back ∗
      owner₂ γ stable back ∗
      front۰auth γ front ∗
      ⌜0 < front⌝ ∗
      model₂ γ vs ∗
      ⌜length vs = back - front⌝ ∗
      array۰cslice γ.(ws_bdeque_1۰name۰data) γ.(ws_bdeque_1۰name۰capacity) front (DfracOwn (1/2)) (vs ++ priv) ∗
      ⌜(length vs + length priv)%nat = γ.(ws_bdeque_1۰name۰capacity)⌝ ∗
      history۰auth γ hist ∗
      prophet_multi۰model prophet_identifier γ.(ws_bdeque_1۰name۰prophet) γ.(ws_bdeque_1۰name۰prophet_name) pasts prophss ∗
      ⌜∀ i, front ≤ i → pasts i = []⌝ ∗
      inv۰state γ state stable front back hist vs priv (prophss front).
    #[local] Instance : CustomIpat "inv۰inner" :=
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
      ⌜0 < γ.(ws_bdeque_1۰name۰capacity)⌝ ∗
      t.[capacity] ↦□ #γ.(ws_bdeque_1۰name۰capacity) ∗
      t.[data] ↦□ γ.(ws_bdeque_1۰name۰data) ∗
      t.[proph] ↦□ #γ.(ws_bdeque_1۰name۰prophet) ∗
      inv γ.(ws_bdeque_1۰name۰inv) (inv۰inner t γ).
    #[local] Instance : CustomIpat "inv'" :=
      " ( %Hcapacity
        & #Ht_capacity
        & #Ht_data
        & #Ht_proph
        & #Hinv
        )
      ".
    Definition ws_bdeque_1۰inv t γ ι cap : iProp Σ :=
      ⌜ι = γ.(ws_bdeque_1۰name۰inv)⌝ ∗
      ⌜cap = γ.(ws_bdeque_1۰name۰capacity)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & ->
        & (:inv')
        )
      ".

    Definition ws_bdeque_1۰model γ vs : iProp Σ :=
      model₁ γ vs ∗
      ⌜length vs ≤ γ.(ws_bdeque_1۰name۰capacity)⌝.
    #[local] Instance : CustomIpat "model" :=
      " ( Hmodel₁{_{}}
        & %Hvs{}
        )
      ".

    Variant owner۰flag :=
      | OwnerNormal
      | OwnerPop.
    #[local] Definition owner۰1 flag t γ stable back ws front_cache i us : iProp Σ :=
      owner₁ γ stable back ws ∗
      t.[front_cache] ↦ #front_cache ∗
      front۰lb γ front_cache ∗
      ⌜(if flag is OwnerPop then ˖back else back) ≤ front_cache + γ.(ws_bdeque_1۰name۰capacity)⌝ ∗
      array۰cslice γ.(ws_bdeque_1۰name۰data) γ.(ws_bdeque_1۰name۰capacity) i (DfracOwn (1/2)) us ∗
      ⌜length us = γ.(ws_bdeque_1۰name۰capacity)⌝.
    #[local] Instance : CustomIpat "owner۰1" :=
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
    #[local] Definition owner۰2 :=
      owner۰1 OwnerNormal.
    #[local] Instance : CustomIpat "owner۰2" :=
      " (:owner۰1)
      ".
    Definition ws_bdeque_1۰owner t γ ws : iProp Σ :=
      ∃ back front_cache i us,
      owner۰2 t γ Stable back ws front_cache i us.
    #[local] Instance : CustomIpat "owner" :=
      " ( %back{}
        & %front_cache{_{}}
        & %i{}
        & %us{}
        & Howner{_{}}
        )
      ".

    #[global] Instance ws_bdeque_1۰modelｰtimeless γ vs :
      Timeless (ws_bdeque_1۰model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ws_bdeque_1۰ownerｰtimeless t γ ws :
      Timeless (ws_bdeque_1۰owner t γ ws).
    Proof.
      apply _.
    Qed.

    #[global] Instance ws_bdeque_1۰invｰpersistent t γ ι cap :
      Persistent (ws_bdeque_1۰inv t γ ι cap).
    Proof.
      apply _.
    Qed.

    #[local] Lemma modelｰownerｰalloc :
      ⊢ |==>
        ∃ γ_model γ_owner,
        model₁' γ_model [] ∗
        model₂' γ_model [] ∗
        owner₁' γ_owner γ_model Stable 1 [] ∗
        owner₂' γ_owner Stable 1.
    Proof.
      iMod (auth_twinsｰalloc _ (auth_twins۰G := ws_bdeque_1۰G۰model۰G)) as "(%γ_model & Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iMod (twinsｰalloc' (twins۰G := ws_bdeque_1۰G۰owner۰G)) as "(%γ_owner & Howner₁ & Howner₂)".
      iFrameSteps.
    Qed.
    #[local] Lemma model₁ｰvalid γ stable back ws vs :
      owner₁ γ stable back ws -∗
      model₁ γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:owner₁) Hmodel₁".
      iDestruct (auth_twinsｰvalid₁ with "Hmodel_auth Hmodel₁") as %H.
      rewrite preorderｰrtc in H. iSteps.
    Qed.
    #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₁ γ vs2 -∗
      False.
    Proof.
      apply auth_twins۰twin₁ｰexclusive.
    Qed.
    #[local] Lemma modelｰagree γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      apply: auth_twinsｰagreeｰL.
    Qed.
    #[local] Lemma model۰owner₁ｰagree γ stable back ws vs1 vs2 :
      owner₁ γ stable back ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
        ⌜vs1 `suffix_of` ws⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Howner₁ Hmodel₁ Hmodel₂".
      iDestruct (model₁ｰvalid with "Howner₁ Hmodel₁") as %Hsuffix.
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iSteps.
    Qed.
    #[local] Lemma modelｰempty {γ stable back ws vs1 vs2} :
      owner₁ γ stable back ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back [] ∗
        model₁ γ [] ∗
        model₂ γ [].
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twinsｰupdateｰauth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iSteps.
    Qed.
    #[local] Lemma modelｰpush {γ stable back ws vs1 vs2} v :
      owner₁ γ stable back ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back (vs1 ++ [v]) ∗
        model₁ γ (vs1 ++ [v]) ∗
        model₂ γ (vs1 ++ [v]).
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twinsｰupdateｰauth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iSteps.
    Qed.
    #[local] Lemma modelｰsteal γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        model₁ γ (tail vs1) ∗
        model₂ γ (tail vs1).
    Proof.
      apply: auth_twinsｰupdateｰtwinsｰL.
      rewrite preorderｰrtc. apply suffixｰtail. done.
    Qed.
    #[local] Lemma modelｰpop γ stable back ws vs1 vs2 :
      owner₁ γ stable back ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back (removelast vs1) ∗
        model₁ γ (removelast vs1) ∗
        model₂ γ (removelast vs1).
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twinsｰupdateｰauth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iSteps.
    Qed.
    #[local] Lemma modelｰpop' γ stable back ws vs1 v vs2 :
      owner₁ γ stable back ws -∗
      model₁ γ (vs1 ++ [v]) -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back vs1 ∗
        model₁ γ vs1 ∗
        model₂ γ vs1.
    Proof.
      rewrite -{2 3 4}(removelast_last vs1 v).
      apply modelｰpop.
    Qed.

    #[local] Lemma owner₁ｰexclusive γ stable1 back1 ws1 stable2 back2 ws2 :
      owner₁ γ stable1 back1 ws1 -∗
      owner₁ γ stable2 back2 ws2 -∗
      False.
    Proof.
      iIntros "(:owner₁ =1) (:owner₁ =2)".
      iApply (twins۰twin₁ｰexclusive with "Howner₁_1 Howner₁_2").
    Qed.
    #[local] Lemma ownerｰagree γ stable1 back1 ws stable2 back2 :
      owner₁ γ stable1 back1 ws -∗
      owner₂ γ stable2 back2 -∗
        ⌜stable1 = stable2⌝ ∗
        ⌜back1 = back2⌝.
    Proof.
      iIntros "(:owner₁) Howner₂".
      iDestruct (twinsｰagreeｰL with "Howner₁ Howner₂") as %[= <- <-].
      iSteps.
    Qed.
    #[local] Lemma owner₁ｰupdate γ stable back ws vs :
      owner₁ γ stable back ws -∗
      model₁ γ vs -∗
      model₂ γ vs ==∗
        owner₁ γ stable back vs ∗
        model₁ γ vs ∗
        model₂ γ vs.
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twinsｰupdateｰauth with "Hmodel_auth Hmodel₁ Hmodel₂") as "($ & $ & $)".
      iSteps.
    Qed.
    #[local] Lemma ownerｰupdate {γ stable1 back1 ws stable2 back2} stable back :
      owner₁ γ stable1 back1 ws -∗
      owner₂ γ stable2 back2 ==∗
        owner₁ γ stable back ws ∗
        owner₂ γ stable back.
    Proof.
      iIntros "(:owner₁) Howner₂".
      iMod (twinsｰupdate with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iSteps.
    Qed.

    #[local] Lemma frontｰalloc :
      ⊢ |==>
        ∃ γ_front,
        front۰auth' γ_front 1.
    Proof.
      apply auth_nat_maxｰalloc.
    Qed.
    #[local] Lemma front۰lbｰget γ front :
      front۰auth γ front ⊢
      front۰lb γ front.
    Proof.
      apply auth_nat_max۰lbｰget.
    Qed.
    #[local] Lemma front۰lbｰle {γ front} front' :
      front' ≤ front →
      front۰lb γ front ⊢
      front۰lb γ front'.
    Proof.
      apply auth_nat_max۰lbｰle.
    Qed.
    #[local] Lemma front۰lbｰvalid γ front1 front2 :
      front۰auth γ front1 -∗
      front۰lb γ front2 -∗
      ⌜front2 ≤ front1⌝.
    Proof.
      apply auth_nat_max۰lbｰvalid.
    Qed.
    #[local] Lemma frontｰupdate γ front :
      front۰auth γ front ⊢ |==>
      front۰auth γ ˖front.
    Proof.
      apply auth_nat_maxｰupdate; first lia.
    Qed.

    #[local] Lemma historyｰalloc :
      ⊢ |==>
        ∃ γ_hist,
        history۰auth' γ_hist [()%V].
    Proof.
      apply mono_listｰalloc.
    Qed.
    #[local] Lemma history۰atｰget {γ hist v} i :
      i = length hist →
      history۰auth γ (hist ++ [v]) ⊢
      history۰at γ i v.
    Proof.
      intros ->.
      apply mono_list۰atｰget, list_lookup_middle. done.
    Qed.
    #[local] Lemma history۰atｰlookup γ hist i v :
      history۰auth γ hist -∗
      history۰at γ i v -∗
      ⌜hist !! i = Some v⌝.
    Proof.
      apply mono_list۰atｰvalid.
    Qed.
    #[local] Lemma history۰atｰagree γ i v1 v2 :
      history۰at γ i v1 -∗
      history۰at γ i v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply mono_list۰atｰagree.
    Qed.
    #[local] Lemma historyｰupdate {γ hist} i v :
      i = length hist →
      history۰auth γ hist ⊢ |==>
        history۰auth γ (hist ++ [v]) ∗
        history۰at γ i v.
    Proof.
      iIntros (->) "Hauth".
      iMod (mono_listｰupdateｰsnoc with "Hauth") as "Hauth".
      iDestruct (history۰atｰget with "Hauth") as "#Hat"; first done.
      iSteps.
    Qed.

    #[local] Lemma winnerｰalloc :
      ⊢ |==>
        ∃ γ_winner,
        winner۰pop' γ_winner 1 True ∗
        winner۰steal' γ_winner 1 True.
    Proof.
      apply twinsｰalloc'.
    Qed.
    #[local] Lemma winner۰popｰexclusive γ front1 P1 front2 P2 :
      winner۰pop γ front1 P1 -∗
      winner۰pop γ front2 P2 -∗
      False.
    Proof.
      apply twins۰twin₁ｰexclusive.
    Qed.
    #[local] Lemma winner۰popｰexclusive' γ front P :
      winner۰pop γ front P -∗
      winner γ -∗
      False.
    Proof.
      iIntros "Hwinner_pop_1 (:winner =2)".
      iApply (winner۰popｰexclusive with "Hwinner_pop_1 Hwinner_pop_2").
    Qed.
    #[local] Lemma winner۰stealｰexclusive γ front1 P1 front2 P2 :
      winner۰steal γ front1 P1 -∗
      winner۰steal γ front2 P2 -∗
      False.
    Proof.
      apply twins۰twin₂ｰexclusive.
    Qed.
    #[local] Lemma winner۰stealｰexclusive' γ front P :
      winner۰steal γ front P -∗
      winner γ -∗
      False.
    Proof.
      iIntros "Hwinner_steal_1 (:winner =2)".
      iApply (winner۰stealｰexclusive with "Hwinner_steal_1 Hwinner_steal_2").
    Qed.
    #[local] Lemma winnerｰagree γ front1 P1 front2 P2 :
      winner۰pop γ front1 P1 -∗
      winner۰steal γ front2 P2 -∗
        ⌜front1 = front2⌝ ∗
        ▷ (P1 ≡ P2).
    Proof.
      iIntros "Hwinner_pop Hwinner_steal".
      iDestruct (twinsｰagree with "Hwinner_pop Hwinner_steal") as "#Heq".
      rewrite prod_equivI /= discrete_eq_1.
      iDestruct "Heq" as "($ & $)".
    Qed.
    #[local] Lemma winnerｰupdate {γ front1 P1 front2 P2} front P :
      winner۰pop γ front1 P1 -∗
      winner۰steal γ front2 P2 ==∗
        winner۰pop γ front P ∗
        winner۰steal γ front P.
    Proof.
      apply twinsｰupdate.
    Qed.

    Opaque owner₁'.

    Lemma ws_bdeque_1۰modelｰvalid t γ ι cap vs :
      ws_bdeque_1۰inv t γ ι cap -∗
      ws_bdeque_1۰model γ vs -∗
      ⌜length vs ≤ cap⌝.
    Proof.
      iSteps.
    Qed.
    Lemma ws_bdeque_1۰modelｰexclusive γ vs1 vs2 :
      ws_bdeque_1۰model γ vs1 -∗
      ws_bdeque_1۰model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    #[local] Lemma owner۰2ｰrebase {t γ stable back ws front_cache i1 us} i2 :
      0 < γ.(ws_bdeque_1۰name۰capacity) →
      owner۰2 t γ stable back ws front_cache i1 us ⊢
        ∃ us,
        owner۰2 t γ stable back ws front_cache i2 us.
    Proof.
      iIntros "%Hcapacity (:owner۰2)".
      iDestruct (array۰csliceｰrebase i2 with "Hdata_cslice₂") as "(%us' & %n & -> & Hdata_cslice₂ & _)"; [done.. |].
      iSteps. simp_length.
    Qed.

    Lemma ws_bdeque_1۰ownerｰexclusive t γ ws1 ws2 :
      ws_bdeque_1۰owner t γ ws1 -∗
      ws_bdeque_1۰owner t γ ws2 -∗
      False.
    Proof.
      iIntros "(:owner =1) (:owner =2)".
      iDestruct "Howner_1" as "(:owner۰2 =1)".
      iDestruct "Howner_2" as "(:owner۰2 =2)".
      iApply (owner₁ｰexclusive with "Howner₁_1 Howner₁_2").
    Qed.
    Lemma ws_bdeque_1۰ownerｰmodel t γ ws vs :
      ws_bdeque_1۰owner t γ ws -∗
      ws_bdeque_1۰model γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:owner =1) (:model =2)".
      iDestruct "Howner_1" as "(:owner۰2 =1)".
      iApply (model₁ｰvalid with "Howner₁_1 Hmodel₁_2").
    Qed.

    #[local] Lemma inv۰stateｰStable γ state front back hist vs priv prophs :
      length vs = back - front →
      inv۰state γ state Stable front back hist vs priv prophs ⊢
        ⌜state = Empty ∨ state = Nonempty⌝ ∗
        ⌜front ≤ back⌝.
    Proof.
      iIntros "%Hvs Hstate".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty lazy=)".
        iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰nonempty lazy=)".
        iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰superempty lazy=)". done.
    Qed.
    #[local] Lemma inv۰stateｰUnstable γ state front back hist vs priv prophs :
      inv۰state γ state Unstable front back hist vs priv prophs ⊢
        ⌜state = Emptyish ∨ state = Superempty⌝ ∗
        ⌜front = back ∨ front = ˖back⌝.
    Proof.
      iIntros "Hstate".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰nonempty lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish lazy=)".
        iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰superempty lazy=)".
        iSteps.
    Qed.
    #[local] Lemma inv۰stateｰNonempty γ state stable front back hist vs priv prophs :
      front < back →
      inv۰state γ state stable front back hist vs priv prophs ⊢
      ⌜state = Nonempty⌝.
    Proof.
      iIntros "% Hstate".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty)". lia.
      - done.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish)". lia.
      - iDestruct "Hstate" as "(:inv۰state۰superempty)". lia.
    Qed.
    #[local] Lemma inv۰stateｰSuperempty γ state front back hist vs priv prophs :
      back < front →
      inv۰state γ state Unstable front back hist vs priv prophs -∗
      ⌜state = Superempty⌝.
    Proof.
      iIntros "% Hstate".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰nonempty lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish lazy=)". lia.
      - done.
    Qed.
    #[local] Lemma inv۰stateｰwinner۰pop γ state stable front1 back hist vs priv prophs front2 P :
      inv۰state γ state stable front1 back hist vs priv prophs -∗
      winner۰pop γ front2 P -∗
        ∃ P_,
        ⌜front1 = front2⌝ ∗
        ▷ (P ≡ P_) ∗
        ( inv۰state۰nonempty۰steal γ state stable front2 back hist vs prophs P_
        ∨ inv۰state۰emptyish۰steal γ state stable front2 back hist priv P_
        ) ∗
        winner۰pop γ front2 P.
    Proof.
      iIntros "Hstate Hwinner_pop".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰popｰexclusive with "Hwinner_pop Hwinner_pop_3") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰nonempty)".
        iDestruct "Hwinner" as "[(:winner =3) | Hwinner]".
        + iDestruct (winner۰popｰexclusive with "Hwinner_pop Hwinner_pop_3") as %[].
        + destruct prophs as [| id prophs]; first done.
          iDestruct "Hwinner" as "(:winner۰pending₂ =_)".
          iDestruct (winnerｰagree with "Hwinner_pop Hwinner_steal") as "#(<- & $)".
          iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish)".
        iDestruct "Hwinner" as "[Hwinner_pop_ | (:winner۰linearized)]".
        + iDestruct (winner۰popｰexclusive with "Hwinner_pop Hwinner_pop_") as %[].
        + iDestruct (winnerｰagree with "Hwinner_pop Hwinner_steal") as "#(<- & $)".
          iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰superempty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰popｰexclusive with "Hwinner_pop Hwinner_pop_3") as %[].
    Qed.
    #[local] Lemma inv۰stateｰwinner۰steal γ state stable front1 back hist vs priv prophs front2 P :
      inv۰state γ state stable front1 back hist vs priv prophs -∗
      winner۰steal γ front2 P -∗
        ∃ P_,
        ⌜front1 = front2⌝ ∗
        ▷ (P_ ≡ P) ∗
        inv۰state۰emptyish۰pop γ state stable front2 back hist priv P_ ∗
        winner۰steal γ front2 P.
    Proof.
      iIntros "Hstate Hwinner_steal".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰stealｰexclusive with "Hwinner_steal Hwinner_steal_3") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰nonempty)".
        destruct prophs as [| id prophs].
        + iDestruct "Hwinner" as "[(:winner =3) | []]".
          iDestruct (winner۰stealｰexclusive with "Hwinner_steal Hwinner_steal_3") as %[].
        + iDestruct "Hwinner" as "[(:winner =3) | (:winner۰pending₂ =_ !=)]".
          * iDestruct (winner۰stealｰexclusive with "Hwinner_steal Hwinner_steal_3") as %[].
          * iDestruct (winner۰stealｰexclusive with "Hwinner_steal Hwinner_steal_") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰emptyish)".
        iDestruct "Hwinner" as "[Hwinner_pop | (:winner۰linearized !=)]".
        + iDestruct (winnerｰagree with "Hwinner_pop Hwinner_steal") as "#(<- & $)".
          iSteps.
        + iDestruct (winner۰stealｰexclusive with "Hwinner_steal Hwinner_steal_") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰superempty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰stealｰexclusive with "Hwinner_steal Hwinner_steal_3") as %[].
    Qed.

    Lemma ws_bdeque_1٠createｰspec ι (cap : Z) :
      (0 < cap)%Z →
      {{{
        True
      }}}
        ws_bdeque_1٠create #cap
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        ws_bdeque_1۰inv t γ ι ₊cap ∗
        ws_bdeque_1۰model γ [] ∗
        ws_bdeque_1۰owner t γ []
      }}}.
    Proof.
      iIntros "%Hcap %Φ _ HΦ".

      wp۰rec.

      wp۰apply (prophet_multiｰwpｰproph with "[//]") as (pid γ_prophet prophss) "Hprophet_model".

      wp۰apply (array٠unsafe_makeｰspec with "[//]") as (data) "Hdata_model"; first lia.
      iDestruct (array۰modelｰtoｰcslice with "Hdata_model") as "Hdata_cslice".
      iEval (simp_length) in "Hdata_cslice".
      iDestruct (array۰csliceｰrotationｰrightｰ0 1 with "Hdata_cslice") as "Hdata_cslice"; [simp_length; lia.. |].
      iEval (rewrite rotationｰreplicate) in "Hdata_cslice".
      iDestruct "Hdata_cslice" as "(Hdata_cslice₁ & Hdata_cslice₂)".

      wp۰block t as "Hmeta" "#Ht_capacity Ht_front Ht_front_cache Ht_back #Ht_data #Ht_proph".

      iMod modelｰownerｰalloc as "(%γ_model & %γ_owner & Hmodel₁ & Hmodel₂ & Howner₁ & Howner₂)".
      iMod frontｰalloc as "(%γ_front & Hfront_auth)".
      iMod historyｰalloc as "(%γ_history & Hhist_auth)".
      iMod winnerｰalloc as "(%γ_winner & Hwinner_pop & Hwinner_steal)".

      set γ :=
        {|ws_bdeque_1۰name۰capacity := ₊cap
        ; ws_bdeque_1۰name۰data := data
        ; ws_bdeque_1۰name۰inv := ι
        ; ws_bdeque_1۰name۰prophet := pid
        ; ws_bdeque_1۰name۰prophet_name := γ_prophet
        ; ws_bdeque_1۰name۰model := γ_model
        ; ws_bdeque_1۰name۰owner := γ_owner
        ; ws_bdeque_1۰name۰front := γ_front
        ; ws_bdeque_1۰name۰history := γ_history
        ; ws_bdeque_1۰name۰winner := γ_winner
        |}.

      iDestruct (front۰lbｰget γ with "Hfront_auth") as "#Hfront_lb".

      iApply ("HΦ" $! t γ).
      iFrame "#∗". iSplitL.
      - iStep 4.
        iApply inv_alloc.
        iExists Empty, Stable, 1, 1, [()%V], [], (replicate ₊cap ()%V), (λ _, []), prophss. iFrameSteps.
        iPureIntro. simp_length.
      - iSteps.
        iPureIntro. simp_length.
    Qed.

    Lemma ws_bdeque_1٠capacityｰspec t γ ι cap :
      {{{
        ws_bdeque_1۰inv t γ ι cap
      }}}
        ws_bdeque_1٠capacity #t
      {{{
        RET #cap;
        True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec. wp۰load.
      iSteps.
    Qed.

    #[local] Lemma frontｰspec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
        front۰lb γ front
      }}}.
    Proof.
      iIntros "%Φ (:inv') HΦ".

      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb_1".
      iFrameSteps.
    Qed.
    #[local] Lemma frontｰspecｰownerｰStable t γ back ws :
      {{{
        inv' t γ ∗
        owner₁ γ Stable back ws
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
        owner₁ γ Stable back ws ∗
        front۰lb γ front ∗
        ⌜front ≤ back⌝
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
      iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb".
      iDestruct (inv۰stateｰStable with "Hstate") as "#(_ & %)"; first done.
      iFrameSteps.
    Qed.
    #[local] Lemma frontｰspecｰownerｰUnstable t γ back ws :
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back ws
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
        owner₁ γ Unstable back ws ∗
        front۰lb γ front ∗
        ⌜front = back ∨ front = ˖back⌝
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
      iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb".
      iDestruct (inv۰stateｰUnstable with "Hstate") as "#(_ & %)".
      iFrameSteps.
    Qed.
    #[local] Lemma frontｰspecｰSuperempty t γ back ws front :
      back < front →
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back ws ∗
        front۰lb γ front
      }}}
        (#t).{front}
      {{{
        RET #front;
        owner₁ γ Unstable back ws
      }}}.
    Proof.
      iIntros "% %Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
      iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰stateｰSuperempty with "Hstate") as %->; first lia.
      iDestruct "Hstate" as "(:inv۰state۰superempty =1 lazy=)".
      iSplitR "Howner₁ HΦ". { iExists Superempty. iFrameSteps. }
      replace ˖back with front by lia.
      iSteps.
    Qed.
    #[local] Lemma frontｰspecｰwinner۰steal t γ front P :
      {{{
        inv' t γ ∗
        winner۰steal γ front P
      }}}
        (#t).{front}
      {{{
        RET #front;
        winner۰steal γ front P
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_steal) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.

      iAssert ⌜front1 = front⌝%I as %->.
      { iDestruct (inv۰stateｰwinner۰steal with "Hstate Hwinner_steal") as "(%P_ & $ & _)". }

      iFrameSteps.
    Qed.

    #[local] Lemma backｰspec t γ stable back ws :
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

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (ownerｰagree with "Howner₁ Howner₂") as "(<- & <-)".
      iFrameSteps.
    Qed.

    #[local] Lemma set_backｰspecｰSuperempty t γ back ws front (back' : Z) :
      back < front →
      back' = ˖back →
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back ws ∗
        front۰lb γ front
      }}}
        #t <-{back} #back'
      {{{
        RET ();
        owner₁ γ Stable ˖back ws
      }}}.
    Proof.
      iIntros (? ->) "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰store.
      iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
      iMod (ownerｰupdate Stable ˖back with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰stateｰSuperempty with "Hstate") as %->; first lia.
      iDestruct "Hstate" as "(:inv۰state۰superempty =1 lazy=)".
      iSplitR "Howner₁ HΦ". { iExists Empty. iFrameSteps. }
      iSteps.
    Qed.

    #[local] Lemma array٠unsafe_cgetｰspecｰloser t γ i :
      (0 ≤ i)%Z →
      {{{
        inv' t γ
      }}}
        array٠unsafe_cget γ.(ws_bdeque_1۰name۰data) #i
      {{{
        v
      , RET v;
        True
      }}}.
    Proof.
      iIntros "%Hi %Φ (:inv') HΦ".

      iApply wpｰfupd.
      awp۰apply (array٠unsafe_cgetｰspecｰatomicｰweak with "[//]") without "HΦ"; first done.
      iInv "Hinv" as "(:inv۰inner)".
      iAaccIntro with "[$Hdata_cslice₁]".
      { iPureIntro. simp_length. }
      { iIntros "(Hdata_cslice₁ & _) !>". iFrameSteps. }
      iIntros "Hdata_cslice₁ !>".
      iSplitL. { iFrameSteps. }
      iIntros "%v H£ HΦ".
      iApply (lc_fupd_elim_later with "H£ HΦ [//]").
    Qed.
    #[local] Lemma array٠unsafe_cgetｰspecｰwinner۰pop t γ front P v :
      {{{
        inv' t γ ∗
        winner۰pop γ front P ∗
        history۰at γ front v
      }}}
        array٠unsafe_cget γ.(ws_bdeque_1۰name۰data) #front
      {{{
        RET v;
        winner۰pop γ front P
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_pop & #Hhistory_at) HΦ".

      iApply wpｰfupd.
      awp۰apply (array٠unsafe_cgetｰspecｰatomic with "[//]") without "HΦ".
      iInv "Hinv" as "(:inv۰inner =1)".

      iAssert (◇ (
        ⌜front1 = front⌝ ∗
        ⌜hd inhabitant (vs1 ++ priv1) = v⌝
      ))%I as "#>(-> & %Hlookup)".
      { iDestruct (inv۰stateｰwinner۰pop with "Hstate [$Hwinner_pop]") as "(%P_ & >-> & _ & [(:inv۰state۰nonempty۰steal =1 >) | (:inv۰state۰emptyish۰steal =1 >)] & Hwinner_pop)".
        - iDestruct (history۰atｰagree with "Hhistory_at Hhistory_at_front1") as ">->".
          rewrite hdｰapp //; first lia.
        - iDestruct (history۰atｰagree with "Hhistory_at Hhistory_at_front1") as ">->".
          assert (length vs1 = 0) as ->%nil_length_inv by lia.
          iSteps.
      }
      apply hdｰcorrect in Hlookup; last (simp_length; lia).
      rewrite head_lookup in Hlookup.

      iAaccIntro with "[$Hdata_cslice₁]".
      { rewrite Nat2Z.id Nat.sub_diag. iSteps. }
      { iIntros "(_ & _ & Hdata_cslice₁) !>". iFrameSteps. }
      iIntros "Hdata_cslice₁ !>".
      iSplitR "Hwinner_pop". { iFrameSteps. }
      iIntros "H£ HΦ".
      iApply (lc_fupd_elim_later with "H£ HΦ Hwinner_pop").
    Qed.

    #[local] Lemma array٠unsafe_csetｰspecｰowner t γ back ws front_cache us front v :
      back < front + γ.(ws_bdeque_1۰name۰capacity) →
      {{{
        inv' t γ ∗
        owner۰2 t γ Stable back ws front_cache back us ∗
        front۰lb γ front
      }}}
        array٠unsafe_cset γ.(ws_bdeque_1۰name۰data) #back v
      {{{
        RET ();
        owner۰2 t γ Stable back ws front_cache back (<[0 := v]> us)
      }}}.
    Proof.
      iIntros "% %Φ ((:inv') & (:owner۰2) & #Hfront_lb) HΦ".

      iApply wpｰfupd.
      awp۰apply (array٠unsafe_csetｰspecｰatomicｰcell with "[//]") without "HΦ".
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
      iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰stateｰStable with "Hstate") as "#>(%Hstate1 & %)"; first done.

      iDestruct (array۰csliceｰapp with "Hdata_cslice₁") as "(Hdata_cslice₁_1 & Hdata_cslice₁_2)".
      destruct (lookup_lt_is_Some_2 priv1 0) as (w & Hpriv_lookup); first lia.
      iDestruct (array۰csliceｰupdate with "Hdata_cslice₁_2") as "(Hdata_back₁ & Hdata_cslice₁_2)"; first done.
      replace (front1 + length vs1 + 0) with back by lia.

      destruct (lookup_lt_is_Some_2 us 0) as (w_ & Hus_lookup); first lia.
      iDestruct (array۰csliceｰupdate with "Hdata_cslice₂") as "(Hdata_back₂ & Hdata_cslice₂)"; first done.
      iEval (rewrite Nat.add_0_r) in "Hdata_back₂ Hdata_cslice₂".

      iDestruct (array۰csliceｰcombine with "Hdata_back₁ Hdata_back₂") as "(%Heq & Hdata_back)"; first done. injection Heq as <-.
      iEval (rewrite dfrac_op_own Qp.half_half) in "Hdata_back".

      iAaccIntro with "[$Hdata_back]". 1: iSteps.

      - iIntros "(_ & (Hdata_back₁ & Hdata_back₂)) !>".

        iDestruct (array۰csliceｰapp₁ with "Hdata_cslice₁_1 (Hdata_cslice₁_2 Hdata_back₁)") as "Hdata_cslice₁"; first done.
        iEval (rewrite list_insert_id //) in "Hdata_cslice₁".

        iDestruct ("Hdata_cslice₂" with "Hdata_back₂") as "Hdata_cslice₂".
        iEval (rewrite list_insert_id //) in "Hdata_cslice₂".

        iFrameSteps.

      - iIntros "(Hdata_back₁ & Hdata_back₂) !>".

        iDestruct (array۰csliceｰapp₁ with "Hdata_cslice₁_1 (Hdata_cslice₁_2 Hdata_back₁)") as "Hdata_cslice₁"; first done.

        iDestruct ("Hdata_cslice₂" with "Hdata_back₂") as "Hdata_cslice₂".

        iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂".
        { iFrameSteps.
          - iPureIntro. simp_length.
          - iExists state1.
            destruct Hstate1 as [-> | ->]; iFrameSteps.
        }
        iIntros "H£ HΦ".

        iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
        iSteps. iPureIntro. simp_length.
    Qed.

    #[local] Lemma resolveｰspecｰloser₁ t γ front1 front2 id :
      front1 < front2 →
      {{{
        inv' t γ ∗
        front۰lb γ front2
      }}}
        Resolve (CAS (#t).[front]%V #front1 #(front1 + 1)) #γ.(ws_bdeque_1۰name۰prophet) (#front1, #id)%V
      {{{
        RET false;
        True
      }}}.
    Proof.
      iIntros "%Hloser %Φ ((:inv') & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =3)".
      iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %?.
      wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
      wp۰cas as Hcas; zoo۰simp in Hcas; last lia.
      iStep. iIntros "!> %prophs %Hprophss3 Hprophet_model".
      iSplitR "HΦ".
      { iFrameSteps.
        - iPureIntro => *.
          rewrite fn_lookup_alter_ne; first lia.
          auto.
        - rewrite fn_lookup_insert_ne //. iSteps.
      }
      iSteps.
    Qed.
    #[local] Lemma resolveｰspecｰloser₂ t γ front id prophs0 :
      head prophs0 ≠ Some id →
      {{{
        inv' t γ ∗
        front۰lb γ front ∗
        prophet_multi۰full prophet_identifier γ.(ws_bdeque_1۰name۰prophet_name) front prophs0
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(ws_bdeque_1۰name۰prophet) (#front, #id)%V
      {{{
        RET false;
        front۰lb γ ˖front
      }}}.
    Proof.
      iIntros "%Hloser %Φ ((:inv') & #Hfront_lb & #Hprophet_full) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %?.
      wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
      wp۰apply (wpｰcasｰnobranch' with "Ht_front") as (b) "%Hcas Ht_front".
      iStep. iIntros "%prophs %Hprophss1 Hprophet_model".
      destruct b; zoo۰simp in Hcas; first subst front1.

      - iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %->.
        rewrite fn_lookup_alter Hpasts1 // in Hloser.

      - iDestruct (front۰lbｰget with "Hfront_auth") as "#-#Hfront_lb_1".
        iDestruct (front۰lbｰle ˖front with "Hfront_lb_1") as "-##Hfront_lb_1"; first lia.
        iSplitR "HΦ".
        { iFrameSteps.
          - iPureIntro => *.
            rewrite fn_lookup_alter_ne; first lia.
            auto.
          - rewrite fn_lookup_insert_ne //. iSteps.
        }
        iSteps.
    Qed.
    #[local] Lemma resolveｰspecｰwinner۰pop t γ front P id :
      {{{
        inv' t γ ∗
        winner۰pop γ front P
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(ws_bdeque_1۰name۰prophet) (#front, #id)%V
      {{{
        RET true;
        ▷ P
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_pop) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
      wp۰apply (wpｰcasｰnobranch' with "Ht_front") as (b) "%Hcas Ht_front".
      iStep. iIntros "%prophs %Hprophss1 Hprophet_model".
      iDestruct (inv۰stateｰwinner۰pop with "Hstate Hwinner_pop") as "(%P_ & -> & #Heq & Hstate & Hwinner_pop)".
      rewrite Hprophss1.
      destruct b; zoo۰simp in Hcas; last congruence.
      iMod (frontｰupdate with "Hfront_auth") as "Hfront_auth".
      iDestruct "Hstate" as "[(:inv۰state۰nonempty۰steal =1) | (:inv۰state۰emptyish۰steal =1)]".

      - iDestruct "Hwinner" as "(:winner۰pending₁)".
        destruct vs1 as [| v1 vs1] => /=; first naive_solver lia.

        iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod (modelｰsteal with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂) /=".
        iMod ("HP" with "[$Hmodel₁ $Hhistory_at_front1 //]") as "HP".

        iDestruct (array۰csliceｰrotationｰright₁' ˖front 1 with "Hdata_cslice₁") as "Hdata_cslice₁"; [simp_length/=; lia.. |].
        eassert (rotation _ _ = vs1 ++ priv1 ++ [v1]) as ->.
        { destruct_decide (γ.(ws_bdeque_1۰name۰capacity) = 1) as Heq | ?.
          - rewrite -> Heq in *.
            simpl in Hdata1.
            assert (length vs1 = 0) as ->%nil_length_inv by lia.
            assert (length priv1 = 0) as ->%nil_length_inv by lia.
            done.
          - rewrite Nat.mod_1_l; first lia.
            rewrite rotationｰS; first lia.
            rewrite rotationｰ0 assoc //.
        }

        iSplitR "HP HΦ".
        { destruct_decide (˖front = back1) as <- | ?.

          - simpl in Hvs1.
            iExists Empty. iFrameSteps; iPureIntro.
            + simp_length/=. lia.
            + intros.
              rewrite fn_lookup_alter_ne; first lia.
              apply Hpasts1; first lia.

          - destruct vs1 as [| v2 vs1] => /=; first naive_solver lia.
            simpl in Hvs1.
            iMod (historyｰupdate _ v2 with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)"; first done.
            iExists Nonempty. iFrameSteps; iPureIntro.
            + simp_length/=. lia.
            + intros.
              rewrite fn_lookup_alter_ne; first lia.
              apply Hpasts1; first lia.
            + simp_length/=. lia.
        }
        iIntros "!> {%}".

        iApply "HΦ". iModIntro.
        iRewrite "Heq" => //.

      - assert (length vs1 = 0) as ->%nil_length_inv by lia.

        iDestruct (array۰csliceｰrotationｰright₁' ˖back1 1 with "Hdata_cslice₁") as "Hdata_cslice₁"; [simp_length; lia.. |].
        iEval (rewrite /= -(app_nil_l (rotation _ _))) in "Hdata_cslice₁".

        iSplitR "HP HΦ".
        { iExists Superempty. iFrameSteps; iPureIntro.
          - simp_length.
          - intros.
            rewrite fn_lookup_alter_ne; first lia.
            apply Hpasts1; first lia.
        }
        iIntros "!> {%}".

        iApply "HΦ". iModIntro.
        iRewrite "Heq" => //.
    Qed.
    #[local] Lemma resolveｰspecｰwinner۰steal t γ front P id :
      {{{
        inv' t γ ∗
        winner۰steal γ front P
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(ws_bdeque_1۰name۰prophet) (#front, #id)%V
      {{{
        RET true;
        front۰lb γ ˖front
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_steal) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
      wp۰apply (wpｰcasｰnobranch' with "Ht_front") as (b) "%Hcas Ht_front".
      iStep. iIntros "%prophs %Hprophss1 Hprophet_model".
      iDestruct (inv۰stateｰwinner۰steal with "Hstate Hwinner_steal") as "(%P_ & -> & _ & (:inv۰state۰emptyish۰pop =1) & Hwinner_steal)".
      destruct b; zoo۰simp in Hcas; last congruence.
      iMod (frontｰupdate with "Hfront_auth") as "Hfront_auth".
      iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb".

      assert (length vs1 = 0) as ->%nil_length_inv by lia.

      iDestruct (array۰csliceｰrotationｰright₁' ˖back1 1 with "Hdata_cslice₁") as "Hdata_cslice₁"; [simp_length; lia.. |].
      iEval (rewrite /= -(app_nil_l (rotation _ _))) in "Hdata_cslice₁".

      iSplitR "HΦ".
      { iExists Superempty. iFrameSteps; iPureIntro.
        - simp_length.
        - intros.
          rewrite fn_lookup_alter_ne; first lia.
          apply Hpasts1; first lia.
      }
      iSteps.
    Qed.
    #[local] Lemma resolveｰspecｰEmpty t γ back ws id :
      {{{
        inv' t γ ∗
        owner₁ γ Stable back ws ∗
        front۰lb γ back
      }}}
        Resolve (CAS (#t).[front]%V #back #(back + 1)) #γ.(ws_bdeque_1۰name۰prophet) (#back, #id)%V
      {{{
        RET true;
        owner₁ γ Unstable back ws ∗
        front۰lb γ ˖back
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
      wp۰apply (wpｰcasｰnobranch' with "Ht_front") as (b) "%Hcas Ht_front".
      iStep. iIntros "%prophs %Hprophss1 Hprophet_model".
      iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
      iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰stateｰStable with "Hstate") as "#([-> | ->] & _)"; first done.

      - iDestruct "Hstate" as "(:inv۰state۰empty =1 lazy=)".
        assert (length vs1 = 0) as ->%nil_length_inv by lia.
        destruct b; zoo۰simp in Hcas; last lia.

        iMod (frontｰupdate with "Hfront_auth") as "Hfront_auth".
        iClear "Hfront_lb". iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb".
        iMod (historyｰupdate _ inhabitant with "Hhistory_auth") as "(Hhistory_auth & _)"; first done.
        iMod (ownerｰupdate Unstable (length hist1) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

        iDestruct (array۰csliceｰrotationｰright₁' ˖(length hist1) 1 with "Hdata_cslice₁") as "Hdata_cslice₁"; [simp_length; lia.. |].
        iEval (rewrite -(app_nil_l (rotation _ _ ))) in "Hdata_cslice₁".

        iSplitR "Howner₁ HΦ".
        { iExists Superempty. iFrameSteps; iPureIntro.
          - simp_length.
          - intros.
            rewrite fn_lookup_alter_ne; first lia.
            apply Hpasts1; first lia.
          - simp_length/=. lia.
        }
        rewrite Hhist1. iSteps.

      - iDestruct "Hstate" as "(:inv۰state۰nonempty =1 lazy=)".
        exfalso. lia.
    Qed.

    Lemma ws_bdeque_1٠sizeｰspec t γ ι cap ws :
      <<<
        ws_bdeque_1۰inv t γ ι cap ∗
        ws_bdeque_1۰owner t γ ws
      | ∀∀ vs,
        ws_bdeque_1۰model γ vs
      >>>
        ws_bdeque_1٠size #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_1۰model γ vs
      | RET #(length vs);
        ws_bdeque_1۰owner t γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".
      iDestruct "Howner" as "(:owner۰2)".

      wp۰rec.

      wp۰bind (_.{front})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
      iDestruct (inv۰stateｰStable with "Hstate") as %(_ & Hback); first done.

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
      iDestruct (model۰owner₁ｰagree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
      iMod (owner₁ｰupdate with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁ //]") as "HΦ".

      iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ". { iFrameSteps. }
      iIntros "!> {%- Hcapacity Hfront_cache Hus Hvs1 Hback}".

      wp۰apply (backｰspec with "[$Howner₁]") as "Howner₁"; first iSteps.
      wp۰pures.

      replace (⁺back - ⁺front1)%Z with ⁺(length vs) by lia.
      iSteps.
    Qed.

    Lemma ws_bdeque_1٠is_emptyｰspec t γ ι cap ws :
      <<<
        ws_bdeque_1۰inv t γ ι cap ∗
        ws_bdeque_1۰owner t γ ws
      | ∀∀ vs,
        ws_bdeque_1۰model γ vs
      >>>
        ws_bdeque_1٠is_empty #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_1۰model γ vs
      | RET #(bool_decide (vs = []%list));
        ws_bdeque_1۰owner t γ vs
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & Howner) HΦ".

      wp۰rec.
      wp۰apply (ws_bdeque_1٠sizeｰspec with "[$]").
      iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs HΦ (%Hvs & Howner)".
      wp۰pures.

      rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
      { rewrite -length_zero_iff_nil. lia. }
      iApply "HΦ".
      iFrameSteps.
    Qed.

    #[local] Definition push۰au t γ ws v Φ : iProp Σ :=
      AU <{
        ∃∃ vs,
        ws_bdeque_1۰model γ vs
      }> @ ⊤ ∖ ↑γ.(ws_bdeque_1۰name۰inv), ∅ <{
        ∀∀ b,
        ⌜b = bool_decide (length vs < γ.(ws_bdeque_1۰name۰capacity))⌝ ∗
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_1۰model γ (if b then vs ++ [v] else vs)
      , COMM
        ws_bdeque_1۰owner t γ (if b then vs ++ [v] else ws) -∗
        Φ #b
      }>.
    Lemma ws_bdeque_1٠pushｰspec t γ ι cap ws v :
      <<<
        ws_bdeque_1۰inv t γ ι cap ∗
        ws_bdeque_1۰owner t γ ws
      | ∀∀ vs,
        ws_bdeque_1۰model γ vs
      >>>
        ws_bdeque_1٠push #t v @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_1۰model γ (if b then vs ++ [v] else vs)
      | RET #b;
        ws_bdeque_1۰owner t γ (if b then vs ++ [v] else ws)
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".
      rename us into us0. iDestruct (owner۰2ｰrebase back with "Howner") as "(%us & (:owner۰2))"; first done.

      wp۰rec.
      wp۰apply+ (backｰspec with "[$Howner₁]") as "Howner₁"; first iSteps.
      wp۰load.
      wp۰apply+ (array٠sizeｰspecｰcslice with "Hdata_cslice₂") as "Hdata_cslice₂".
      wp۰load. wp۰pures.

      wp۰bind (_ 𝗼𝗿 _)%E.
      wp۰apply (wpｰwand (λ res,
        ∃ b front_cache,
        ⌜res = #b⌝ ∗
        t.[front_cache] ↦ #front_cache ∗
        front۰lb γ front_cache ∗
        owner₁ γ Stable back ws ∗
        if b then
          ⌜back < front_cache + γ.(ws_bdeque_1۰name۰capacity)⌝ ∗
          push۰au t γ ws v Φ
        else
          ⌜back ≤ front_cache + γ.(ws_bdeque_1۰name۰capacity)⌝ ∗
          (ws_bdeque_1۰owner t γ ws -∗ Φ false%V)
      )%I with "[Howner₁ Ht_front_cache HΦ]") as (res) "{Hfront_lb_cache} {% front_cache Hfront_cache} (%b & %front_cache & -> & Ht_front_cache & #Hfront_lb_cache & Howner₁ & HΦ)".
      { case_bool_decide; wp۰pures.

        - iStep. iFrame "#∗". iSteps.

        - wp۰rec.

          wp۰bind (_.{front})%E.
          wp۰apply (wpｰwand (λ res,
            ∃ front,
            ⌜res = #front⌝ ∗
            front۰lb γ front ∗
            owner₁ γ Stable back ws ∗
            if bool_decide (front_cache < front) then
              ⌜back < front + γ.(ws_bdeque_1۰name۰capacity)⌝ ∗
              push۰au t γ ws v Φ
            else
              ⌜back ≤ front + γ.(ws_bdeque_1۰name۰capacity)⌝ ∗
              (ws_bdeque_1۰owner t γ ws -∗ Φ false%V)
          )%I with "[Howner₁ HΦ]") as (res) "(%front & -> & #Hfront_lb & Howner₁ & HΦ)".
          { iInv "Hinv" as "(:inv۰inner =1)".
            wp۰load.
            iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
            iDestruct (front۰lbｰget with "Hfront_auth") as "#$".
            case_bool_decide. 1: iFrameSteps.

            iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
            iDestruct (model۰owner₁ｰagree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
            rewrite bool_decide_eq_false_2; first lia.
            iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iFrameSteps.

            iFrameSteps.
          }

          wp۰store. wp۰pures.

          iFrame "#∗". iPureIntro.
          erewrite bool_decide_ext; [done | lia].
      }

      destruct b; wp۰pures.

      - iDestruct "HΦ" as "(%Hfront_cache & HΦ)".

        wp۰apply (array٠unsafe_csetｰspecｰowner with "[$Howner₁ $Ht_front_cache $Hdata_cslice₂]") as "(:owner۰2 !=)"; [done | iSteps |].
        wp۰pures.

        wp۰bind (_ <-{back} _)%E.
        iInv "Hinv" as "(:inv۰inner =2)".
        wp۰store.
        iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
        iMod (ownerｰupdate Stable ˖back with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
        iDestruct (inv۰stateｰStable with "Hstate") as "(%Hstate2 & %)"; first done.
        iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb_cache") as %?.

        iAssert ⌜head priv2 = Some v⌝%I as %(priv2' & ->)%head_Some.
        { iDestruct (array۰csliceｰrotationｰrightｰsmall₁' back (length vs2) with "Hdata_cslice₁") as "Hdata_cslice₁"; [simp_length; lia.. |].
          rewrite /rotation drop_app_length.
          rewrite head_lookup -(lookup_app_l _ (take (length vs2) (vs2 ++ priv2))); first lia.
          iDestruct (array۰csliceｰagree with "Hdata_cslice₁ Hdata_cslice₂") as %->.
          { simp_length. lia. }
          rewrite list_lookup_insert_eq //; first lia.
        }
        iEval (rewrite (assoc _ _ [_])) in "Hdata_cslice₁".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model۰owner₁ｰagree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
        iMod (modelｰpush v with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! true with "[$Hmodel₁]") as "HΦ".
        { iSteps; iPureIntro.
          - rewrite bool_decide_eq_true_2 //; first lia.
          - simp_length/=. lia.
        }

        iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ".
        { iExists Nonempty.
          destruct Hstate2 as [-> | ->].

          - iDestruct "Hstate" as "(:inv۰state۰empty =1 lazy=)".
            assert (length vs = 0) as ->%nil_length_inv by lia.
            iMod (historyｰupdate back v with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)"; first done.
            iFrameSteps. iPureIntro.
            simp_length/=. lia.

          - iDestruct "Hstate" as "(:inv۰state۰nonempty =1 lazy=)".
            iFrameSteps; try iPureIntro.
            + simp_length/=. lia.
            + simp_length/=. lia.
            + rewrite hdｰapp //; first lia.
        }
        iIntros "!> {%- Hcapacity Hfront_cache Hus}".

        iSteps. iPureIntro. simp_length.

      - iDestruct "HΦ" as "(%Hfront_cache & HΦ)".

        iApply "HΦ".
        iFrameSteps.
    Qed.

    Lemma ws_bdeque_1٠stealｰspec t γ ι cap :
      <<<
        ws_bdeque_1۰inv t γ ι cap
      | ∀∀ vs,
        ws_bdeque_1۰model γ vs
      >>>
        ws_bdeque_1٠steal #t @ ↑ι
      <<<
        ws_bdeque_1۰model γ (tail vs)
      | RET head vs;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp۰rec.
      wp۰apply (wpｰid with "[//]") as (id) "Hid".
      wp۰apply+ frontｰspec as (front1) "#Hfront_lb_1"; first iSteps.
      wp۰pures.

      wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰load.
      iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb_1") as %?.

      destruct_decide (front1 < back2) as Hbranch1; last first.
      { assert (length vs2 = 0) as ->%nil_length_inv by lia.

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΦ" with "[$Hmodel₁ //] [//]") as "HΦ".

        iFrameSteps.
      }

      destruct_decide (front1 = front2) as <- | ?; last first.
      { assert (front1 < front2) as Hbranch2 by lia.
        iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb_2".
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hcapacity Hbranch1 Hbranch2}".

        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰load.
        wp۰apply+ array٠unsafe_cgetｰspecｰloser as (v) "_"; [lia | iSteps |].
        wp۰load.
        wp۰apply+ resolveｰspecｰloser₁; [done | iSteps |].
        iSteps.
      }

      iDestruct (prophet_multi۰fullｰget _ front1 with "Hprophet_model") as "#Hprophet_full".
      iEval (rewrite Hpasts2 //=) in "Hprophet_full".

      destruct_decide (head $ prophss2 front1 = Some id) as (prophs0 & Hbranch3)%head_Some | Hbranch3; last first.
      { iSplitR "HΦ". { iFrameSteps. }
        remember (prophss2 front1) as prophs0.
        iIntros "!> {%- Hcapacity Hbranch1 Hbranch3}".

        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰load.
        wp۰apply+ array٠unsafe_cgetｰspecｰloser as (v) "_"; [lia | iSteps |].
        wp۰load.
        wp۰apply+ resolveｰspecｰloser₂; [done | iSteps |].
        iSteps.
      }
      rewrite Hbranch3.

      iDestruct (inv۰stateｰNonempty with "Hstate") as %->; first done.
      iDestruct "Hstate" as "(:inv۰state۰nonempty =2)".
      iDestruct "Hwinner" as "[(:winner) | (:winner۰pending₂ !=)]"; last first.
      { iDestruct (identifier۰modelｰexclusive with "Hid Hid_") as %[]. }

      destruct vs2 as [| v vs2] => /=; first naive_solver lia.
      iMod (winnerｰupdate front1 (Φ (Some v)) with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

      iSplitR "Hwinner_pop".
      { iExists Nonempty. iFrameSteps.
        rewrite Hbranch3 /winner۰pending₂. iSteps. iIntros "!> !>".
        rewrite /winner۰au. iAuIntro.
        iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)".
        iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%v_ %vs' (-> & Hmodel₁ & Hhistory_at) !>".
        iDestruct (history۰atｰagree with "Hhistory_at Hhistory_at_front2") as %<-.
        simpl in Hvs. iSteps.
      }
      iIntros "!> {%- Hcapacity Hbranch1}".

      wp۰pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp۰load.
      wp۰apply+ (array٠unsafe_cgetｰspecｰwinner۰pop with "[$Hwinner_pop]") as "Hwinner_pop"; first iSteps.
      wp۰load.
      wp۰apply+ (resolveｰspecｰwinner۰pop with "[$Hwinner_pop]") as "HΦ"; first iSteps.
      iSteps.
    Qed.

    Variant pop_state :=
      | PopNonempty v
      | PopEmptyishWinner v
      | PopEmptyishLoser
      | PopSuperempty.
    #[local] Lemma ws_bdeque_1٠pop₁ｰspec {t γ} (state : pop_state) {stable} back ws front_cache us id (back_ : Z) :
      back_ = back →
      {{{
        inv' t γ ∗
        owner۰1 OwnerPop t γ stable back ws front_cache back us ∗
        match state with
        | PopNonempty v =>
            ⌜stable = Stable⌝ ∗
            ⌜us !! 0 = Some v⌝
        | PopEmptyishWinner v =>
            ⌜stable = Unstable⌝ ∗
            ⌜us !! 0 = Some v⌝ ∗
            winner۰steal γ back inhabitant
        | PopEmptyishLoser =>
            ∃ id_winner prophs,
            ⌜stable = Unstable⌝ ∗
            prophet_multi۰full prophet_identifier γ.(ws_bdeque_1۰name۰prophet_name) back (id_winner :: prophs) ∗
            ⌜head (id_winner :: prophs) ≠ Some id⌝
        | PopSuperempty =>
            ∃ front,
            ⌜stable = Unstable⌝ ∗
            front۰lb γ front ∗
            ⌜front = ˖back⌝
        end
      }}}
        ws_bdeque_1٠pop₁ #t #id #back_
      {{{
        o back front_cache i us
      , RET o;
        owner۰2 t γ Stable back ws front_cache i us ∗
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
      iIntros (->) "%Φ ((:inv') & (:owner۰1) & H) HΦ".

      wp۰rec. wp۰pures.
      destruct state.

      - iDestruct "H" as "(-> & %Hus_lookup)".
        iSpecialize ("HΦ" $! (Some v)).

        wp۰apply (frontｰspecｰownerｰStable with "[$Howner₁]") as (front2) "(Howner₁ & #Hfront_lb & %Hfront2)"; first iSteps.
        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰pures.
        case_bool_decide as Hbranch; wp۰pures.

        + wp۰load.
          wp۰apply (array٠unsafe_cgetｰspec with "Hdata_cslice₂"); [done.. | lia |].
          iSteps.

        + replace front2 with back by lia.

          wp۰store. wp۰load.
          wp۰apply+ (resolveｰspecｰEmpty with "[$Howner₁]") as "{Hfront_lb} (Howner₁ & #Hfront_lb)"; first iSteps.
          wp۰apply+ (set_backｰspecｰSuperempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
          wp۰load.
          wp۰apply (array٠unsafe_cgetｰspec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
          wp۰pures.

          iApply "HΦ".
          iFrame "#∗". iSteps.

      - iDestruct "H" as "(-> & %Hus_lookup & Hwinner_steal)".
        iSpecialize ("HΦ" $! (Some v)).

        wp۰apply (frontｰspecｰwinner۰steal with "[$Hwinner_steal]") as "Hwinner_steal"; first iSteps.
        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰store. wp۰load.
        wp۰apply+ (resolveｰspecｰwinner۰steal with "[$Hwinner_steal]") as "#Hfront_lb"; first iSteps.
        wp۰apply+ (set_backｰspecｰSuperempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
        wp۰load.
        wp۰apply (array٠unsafe_cgetｰspec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
        wp۰pures.

        iApply "HΦ".
        iFrame "#∗". iSteps.

      - iDestruct "H" as "(%id_winner & %prophs & -> & #Hprophet_full & %Hloser)".
        iSpecialize ("HΦ" $! None).

        wp۰apply (frontｰspecｰownerｰUnstable with "[$Howner₁]") as (front2) "(Howner₁ & #Hfront_lb & %Hbranch)"; first iSteps.
        wp۰pures.
        destruct Hbranch as [-> | ->].

        + rewrite bool_decide_eq_false_2; first lia.
          wp۰pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp۰store. wp۰load.
          wp۰apply+ (resolveｰspecｰloser₂ with "[$Hfront_lb $Hprophet_full]") as "{Hfront_lb} #Hfront_lb"; [done | iSteps |].
          wp۰apply+ (set_backｰspecｰSuperempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
          wp۰pures.

          iApply "HΦ".
          iFrame "#∗". iSteps.

        + rewrite bool_decide_eq_true_2; first lia.
          wp۰apply+ (set_backｰspecｰSuperempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
          iSteps.

      - iDestruct "H" as "(%front & -> & #Hfront_lb & ->)".
        iSpecialize ("HΦ" $! None).

        wp۰apply (frontｰspecｰSuperempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia | iSteps |].
        wp۰pures.
        rewrite bool_decide_eq_true_2; first lia.
        wp۰apply+ (set_backｰspecｰSuperempty with "[$Howner₁ $Hfront_lb]") as "Howner₁"; [lia.. | iSteps |].
        iSteps.
    Qed.
    Lemma ws_bdeque_1٠popｰspec t γ ι cap ws :
      <<<
        ws_bdeque_1۰inv t γ ι cap ∗
        ws_bdeque_1۰owner t γ ws
      | ∀∀ vs,
        ws_bdeque_1۰model γ vs
      >>>
        ws_bdeque_1٠pop #t @ ↑ι
      <<<
        ∃∃ o ws',
        ⌜vs `suffix_of` ws⌝ ∗
        match o with
        | None =>
            ⌜vs = []⌝ ∗
            ⌜ws' = []⌝ ∗
            ws_bdeque_1۰model γ []
        | Some v =>
            ∃ vs',
            ⌜vs = vs' ++ [v]⌝ ∗
            ⌜ws' = vs'⌝ ∗
            ws_bdeque_1۰model γ vs'
        end
      | RET o;
        ws_bdeque_1۰owner t γ ws'
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".
      rename us into us0. iDestruct (owner۰2ｰrebase (back - 1) with "Howner") as "(%us & (:owner۰2))"; first done.

      wp۰rec.
      wp۰apply (wpｰid with "[//]") as (id) "Hid".
      wp۰apply+ (backｰspec with "[$Howner₁]") as "Howner₁"; first iSteps.
      wp۰pures.

      wp۰bind (_ <-{back} _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰store.
      iDestruct (ownerｰagree with "Howner₁ Howner₂") as %(<- & <-).
      iDestruct (inv۰stateｰStable with "Hstate") as "#(%Hstate1 & %)"; first done.
      destruct Hstate1 as [-> | ->].

      { iDestruct "Hstate" as "(:inv۰state۰empty =1 lazy=)".
        assert (0 < back) as Hback by lia.
        assert (length vs1 = 0) as ->%nil_length_inv by lia.

        iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb".
        iMod (ownerｰupdate Unstable (back - 1) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model۰owner₁ｰagree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (modelｰempty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! None with "[$Hmodel₁ //]") as "HΦ".

        iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ".
        { iExists Superempty. iFrameSteps. }
        iIntros "!> {%- Hcapacity Hfront_cache Hus Hback}".

        wp۰apply+ (ws_bdeque_1٠pop₁ｰspec PopSuperempty (back - 1) with "[- HΦ]"); [lia | iFrameSteps |].
        iSteps.
      }

      iDestruct "Hstate" as "(:inv۰state۰nonempty =1 lazy=)".
      assert (0 < back) as Hback by lia.
      destruct vs1 as [| v vs1 _] using rev_ind; first naive_solver lia.
      simp_length/= in Hvs1.
      simp_length/= in Hdata1.

      destruct_decide (˖front1 = back) as <- | Hbranch1.

      - assert (length vs1 = 0) as ->%nil_length_inv.
        { simp_length/= in Hvs1. lia. }
        simpl in *.
        iEval (rewrite Nat.sub_0_r) in "Hdata_cslice₂".

        iAssert ⌜us !! 0 = Some v⌝%I as %Hus_lookup.
        { iDestruct (array۰csliceｰagree with "Hdata_cslice₁ Hdata_cslice₂") as %<-; first (simpl; lia).
          iSteps.
        }

        iMod (ownerｰupdate Unstable front1 with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

        destruct_decide (head $ prophss1 front1 = Some id) as (prophs0 & Hprophss1)%head_Some | Hbranch2.

        + rewrite Hprophss1.
          iDestruct "Hwinner" as "[(:winner) | (:winner۰pending₂ !=)]"; last first.
          { iDestruct (identifier۰modelｰexclusive with "Hid Hid_") as %[]. }
          iMod (winnerｰupdate front1 inhabitant with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model۰owner₁ｰagree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
          iMod (modelｰpop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
          iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

          iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ Hwinner_steal HΦ".
          { iExists Emptyish. iFrameSteps. }
          iIntros "!> {%- Hcapacity Hfront_cache Hus Hback Hus_lookup}".

          wp۰apply+ (ws_bdeque_1٠pop₁ｰspec (PopEmptyishWinner v) front1 with "[- HΦ]"); [lia | iFrameSteps |].
          iSteps.

        + iDestruct "Hwinner" as "[(:winner) | Hwinner]".

          { iMod (winnerｰupdate front1 inhabitant with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

            iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
            iDestruct (model۰owner₁ｰagree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
            iMod (modelｰpop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
            iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

            iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ Hwinner_steal HΦ".
            { iExists Emptyish. iFrameSteps. }
            iIntros "!> {%- Hcapacity Hfront_cache Hus Hus_lookup}".

            wp۰apply+ (ws_bdeque_1٠pop₁ｰspec (PopEmptyishWinner v) front1 with "[- HΦ]"); [lia | iFrameSteps |].
            iSteps.
          }

          iDestruct (prophet_multi۰fullｰget _ front1 with "Hprophet_model") as "#Hprophet_full".
          iEval (rewrite Hpasts1 //=) in "Hprophet_full".
          destruct (prophss1 front1) as [| id_winner prophs]; first done.
          iDestruct "Hwinner" as "(:winner۰pending₂ !=)".

          iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod (modelｰsteal with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂) /=".
          iMod ("HP" with "[$Hmodel₁]") as "HP"; first iSteps.

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model۰owner₁ｰagree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
          iMod (modelｰempty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" $! None with "[$Hmodel₁ //]") as "HΦ".

          iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ".
          { iExists Emptyish. iFrameStep 7. iExists P. iSteps. }
          iIntros "!> {%- Hcapacity Hfront_cache Hus Hbranch2}".

          wp۰apply+ (ws_bdeque_1٠pop₁ｰspec PopEmptyishLoser front1 with "[- HΦ]"); [lia | iFrameSteps |].
          iSteps.

      - iMod (ownerｰupdate Stable (back - 1) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
        iEval (rewrite -assoc) in "Hdata_cslice₁".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model۰owner₁ｰagree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (modelｰpop' with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some v) with "[$Hmodel₁]") as "HΦ"; first iSteps.

        iAssert ⌜us !! 0 = Some v⌝%I as %Hus_lookup.
        { iDestruct (array۰csliceｰrotationｰrightｰsmall₁' (back - 1) (length vs1) with "Hdata_cslice₁") as "Hdata_cslice₁"; [simp_length/=; lia.. |].
          iDestruct (array۰csliceｰagree with "Hdata_cslice₁ Hdata_cslice₂") as %<-.
          { simp_length/=. lia. }
          rewrite /rotation drop_app_length //.
        }

        iSplitR "Howner₁ Ht_front_cache Hdata_cslice₂ HΦ".
        { iExists Nonempty. iFrameSteps.
          rewrite hdｰapp //; first lia.
        }
        iIntros "!> {%- Hcapacity Hfront_cache Hus Hback Hus_lookup}".

        wp۰apply+ (ws_bdeque_1٠pop₁ｰspec (PopNonempty v) (back - 1) with "[- HΦ]"); [lia | iFrameSteps |].
        iSteps.
    Qed.
  End ws_bdeque_1۰G.

  #[global] Opaque ws_bdeque_1۰inv.
  #[global] Opaque ws_bdeque_1۰model.
  #[global] Opaque ws_bdeque_1۰owner.
End base.

Require zoo_saturn.ws_bdeque_1__opaque.

Section ws_bdeque_1۰G.
  Context `{ws_bdeque_1۰G : WsBdeque1G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition ws_bdeque_1۰inv t ι cap : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ws_bdeque_1۰inv 𝑡 γ ι cap.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition ws_bdeque_1۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ws_bdeque_1۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition ws_bdeque_1۰owner t ws : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ws_bdeque_1۰owner 𝑡 γ ws.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Howner{_{}}
      )
    ".

  #[global] Instance ws_bdeque_1۰modelｰtimeless γ vs :
    Timeless (ws_bdeque_1۰model γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_bdeque_1۰ownerｰtimeless γ ws :
    Timeless (ws_bdeque_1۰owner γ ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_bdeque_1۰invｰpersistent t ι cap :
    Persistent (ws_bdeque_1۰inv t ι cap).
  Proof.
    apply _.
  Qed.

  Lemma ws_bdeque_1۰modelｰvalid t ι cap vs :
    ws_bdeque_1۰inv t ι cap -∗
    ws_bdeque_1۰model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_1۰modelｰvalid with "Hinv_1 Hmodel_2").
  Qed.
  Lemma ws_bdeque_1۰modelｰexclusive t vs1 vs2 :
    ws_bdeque_1۰model t vs1 -∗
    ws_bdeque_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_1۰modelｰexclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma ws_bdeque_1۰ownerｰexclusive t ws1 ws2 :
    ws_bdeque_1۰owner t ws1 -∗
    ws_bdeque_1۰owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_1۰ownerｰexclusive with "Howner_1 Howner_2").
  Qed.
  Lemma ws_bdeque_1ｰownerｰmodel γ ws vs :
    ws_bdeque_1۰owner γ ws -∗
    ws_bdeque_1۰model γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_1۰ownerｰmodel with "Howner_1 Hmodel_2").
  Qed.

  Lemma ws_bdeque_1٠createｰspec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      ws_bdeque_1٠create #cap
    {{{
      t
    , RET t;
      ws_bdeque_1۰inv t ι ₊cap ∗
      ws_bdeque_1۰model t [] ∗
      ws_bdeque_1۰owner t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.ws_bdeque_1٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel & Howner)"; first done.
    iMod (metaｰset γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma ws_bdeque_1٠capacityｰspec t ι cap :
    {{{
      ws_bdeque_1۰inv t ι cap
    }}}
      ws_bdeque_1٠capacity t
    {{{
      RET #cap;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.ws_bdeque_1٠capacityｰspec with "[$] HΦ").
  Qed.

  Lemma ws_bdeque_1٠sizeｰspec t ι cap ws :
    <<<
      ws_bdeque_1۰inv t ι cap ∗
      ws_bdeque_1۰owner t ws
    | ∀∀ vs,
      ws_bdeque_1۰model t vs
    >>>
      ws_bdeque_1٠size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_1۰model t vs
    | RET #(length vs);
      ws_bdeque_1۰owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_bdeque_1٠sizeｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_1٠is_emptyｰspec t ι cap ws :
    <<<
      ws_bdeque_1۰inv t ι cap ∗
      ws_bdeque_1۰owner t ws
    | ∀∀ vs,
      ws_bdeque_1۰model t vs
    >>>
      ws_bdeque_1٠is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_1۰model t vs
    | RET #(bool_decide (vs = []%list));
      ws_bdeque_1۰owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_bdeque_1٠is_emptyｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_1٠pushｰspec t ι cap ws v :
    <<<
      ws_bdeque_1۰inv t ι cap ∗
      ws_bdeque_1۰owner t ws
    | ∀∀ vs,
      ws_bdeque_1۰model t vs
    >>>
      ws_bdeque_1٠push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_1۰model t (if b then vs ++ [v] else vs)
    | RET #b;
      ws_bdeque_1۰owner t (if b then vs ++ [v] else ws)
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_bdeque_1٠pushｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_1٠stealｰspec t ι cap :
    <<<
      ws_bdeque_1۰inv t ι cap
    | ∀∀ vs,
      ws_bdeque_1۰model t vs
    >>>
      ws_bdeque_1٠steal t @ ↑ι
    <<<
      ws_bdeque_1۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.ws_bdeque_1٠stealｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_1٠popｰspec t ι cap ws :
    <<<
      ws_bdeque_1۰inv t ι cap ∗
      ws_bdeque_1۰owner t ws
    | ∀∀ vs,
      ws_bdeque_1۰model t vs
    >>>
      ws_bdeque_1٠pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_bdeque_1۰model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          ws_bdeque_1۰model t vs'
      end
    | RET o;
      ws_bdeque_1۰owner t ws'
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_bdeque_1٠popｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1". 1: iSteps. iIntros "%o %ws' ($ & Ho)".
      iExists o, ws'. destruct o.
      all: iDecompose "Ho".
      all: iFrameSteps.
    }
  Qed.
End ws_bdeque_1۰G.

#[global] Opaque ws_bdeque_1۰inv.
#[global] Opaque ws_bdeque_1۰model.
#[global] Opaque ws_bdeque_1۰owner.
