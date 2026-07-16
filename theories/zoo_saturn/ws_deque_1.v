Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.function.
Require Import zoo.common.list.
Require Import zoo.common.relations.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.auth_twins.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.mono_gmultiset.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo.program_logic.identifier.
Require Import zoo.program_logic.prophet_identifier.
Require Import zoo.program_logic.prophet_multi.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo_std.option.
Require Export zoo_saturn.ws_deque_1__code.
Require Import zoo_saturn.ws_deque_1__types.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types front back : nat.
Implicit Types id : prophet_id.
Implicit Types v : val.
Implicit Types us vs ws hist priv : list val.
Implicit Types datas : gmultiset val.
Implicit Types past prophs : list prophet_identifier.(prophet_typed۰type).
Implicit Types pasts prophss : nat → list prophet_identifier.(prophet_typed۰type).

Variant state :=
  | Empty
  | Nonempty
  | Emptyish
  | Superempty.
Implicit Types state : state.

#[local] Instance state𑁒inhabited : Inhabited state :=
  populate Empty.

Variant stability :=
  | Stable
  | Unstable.
Implicit Types stable : stability.

#[local] Instance stability𑁒inhabited : Inhabited stability :=
  populate Stable.

Class WsDeque1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] ws_deque_1۰G۰prophet۰G :: ProphetMultiG Σ prophet_identifier
  ; #[local] ws_deque_1۰G۰model۰G :: AuthTwinsG Σ (leibnizO (list val)) suffix
  ; #[local] ws_deque_1۰G۰owner۰G :: TwinsG Σ (leibnizO (stability * nat * val * nat))
  ; #[local] ws_deque_1۰G۰front۰G :: AuthNatMaxG Σ
  ; #[local] ws_deque_1۰G۰history۰G :: MonoListG Σ val
  ; #[local] ws_deque_1۰G۰winner۰G :: TwinsG Σ (natO * leibnizO (option val) * ▶ ∙)
  ; #[local] ws_deque_1۰G۰datas۰G :: MonoGmultisetG Σ val
  }.

Definition ws_deque_1۰Σ :=
  #[prophet_multi۰Σ prophet_identifier
  ; auth_twins۰Σ (leibnizO (list val)) suffix
  ; twins۰Σ (leibnizO (stability * nat * val * nat))
  ; auth_nat_max۰Σ
  ; mono_list۰Σ val
  ; twins۰Σ (natO * leibnizO (option val) * ▶ ∙)
  ; mono_gmultiset۰Σ val
  ].
#[global] Instance subG𑁒ws_deque_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG ws_deque_1۰Σ Σ →
  WsDeque1G Σ .
Proof.
  solve_inG.
Qed.

#[local] Definition min_capacity :=
  val۰to_nat' ws_deque_1٠min_capacity.
#[local] Lemma min_capacity𑁒nonzero :
  0 < min_capacity.
Proof.
  compute_done.
Qed.
#[local] Hint Resolve
  min_capacity𑁒nonzero
: core.
#[local] Lemma ws_deque_1٠min_capacity𑁒unfold :
  ws_deque_1٠min_capacity = #min_capacity.
Proof.
  done.
Qed.
Opaque ws_deque_1٠min_capacity.
Opaque min_capacity.

Module base.
  Section ws_deque_1۰G.
    Context `{ws_deque_1۰G : WsDeque1G Σ}.

    Implicit Types t : location.
    Implicit Types P : iProp Σ.

    Record ws_deque_1۰name :=
      { ws_deque_1۰name۰inv : namespace
      ; ws_deque_1۰name۰prophet : prophet_id
      ; ws_deque_1۰name۰prophet_name : prophet_multi۰name
      ; ws_deque_1۰name۰model : auth_twins۰name
      ; ws_deque_1۰name۰owner : gname
      ; ws_deque_1۰name۰front : gname
      ; ws_deque_1۰name۰history : gname
      ; ws_deque_1۰name۰winner : gname
      ; ws_deque_1۰name۰datas : gname
      }.
    Implicit Types γ : ws_deque_1۰name.

    #[global] Instance ws_deque_1۰name𑁒eq_dec : EqDecision ws_deque_1۰name :=
      ltac:(solve_decision).
    #[global] Instance ws_deque_1۰name𑁒countable :
      Countable ws_deque_1۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      auth_twins۰twin₁ _ γ_model vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(ws_deque_1۰name۰model).
    #[local] Definition model₂' γ_model vs :=
      auth_twins۰twin₂ _ γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(ws_deque_1۰name۰model).

    #[local] Definition owner₁' γ_owner γ_model stable back data cap ws : iProp Σ :=
      twins۰twin₁ (twins۰G := ws_deque_1۰G۰owner۰G) γ_owner (DfracOwn 1) (stable, back, data, cap) ∗
      auth_twins۰auth _ γ_model ws.
    #[local] Definition owner₁ γ :=
      owner₁' γ.(ws_deque_1۰name۰owner) γ.(ws_deque_1۰name۰model).
    #[local] Instance : CustomIpat "owner₁" :=
      " ( Howner₁{_{}}
        & Hmodel_auth{_{}}
        )
      ".
    #[local] Definition owner₂' γ_owner stable back data cap :=
      twins۰twin₂ (twins۰G := ws_deque_1۰G۰owner۰G) γ_owner (stable, back, data, cap).
    #[local] Definition owner₂ γ :=
      owner₂' γ.(ws_deque_1۰name۰owner).

    #[local] Definition front۰auth' γ_front :=
      auth_nat_max۰auth γ_front (DfracOwn 1).
    #[local] Definition front۰auth γ :=
      front۰auth' γ.(ws_deque_1۰name۰front).
    #[local] Definition front۰lb γ :=
      auth_nat_max۰lb γ.(ws_deque_1۰name۰front).

    #[local] Definition history۰auth' γ_history :=
      mono_list۰auth γ_history (DfracOwn 1).
    #[local] Definition history۰auth γ :=
      history۰auth' γ.(ws_deque_1۰name۰history).
    #[local] Definition history۰at γ :=
      mono_list۰at γ.(ws_deque_1۰name۰history).

    #[local] Definition winner۰pop' γ_winner front (data : option val) P : iProp Σ :=
      twins۰twin₁ γ_winner (DfracOwn 1) (front, data, Next P).
    #[local] Definition winner۰pop γ :=
      winner۰pop' γ.(ws_deque_1۰name۰winner).
    #[local] Definition winner۰steal' γ_winner front (data : option val) P :=
      twins۰twin₂ γ_winner (front, data, Next P).
    #[local] Definition winner۰steal γ :=
      winner۰steal' γ.(ws_deque_1۰name۰winner).
    #[local] Definition winner γ : iProp Σ :=
      ∃ front data P1 P2,
      winner۰pop γ front data P1 ∗
      winner۰steal γ front data P2.
    #[local] Instance : CustomIpat "winner" :=
      " ( %front_winner
        & %data_winner
        & %P1
        & %P2
        & Hwinner_pop{_{}}
        & Hwinner_steal{_{}}
        )
      ".

    #[local] Definition datas۰auth' γ_datas :=
      mono_gmultiset۰auth γ_datas (DfracOwn 1).
    #[local] Definition datas۰auth γ :=
      datas۰auth' γ.(ws_deque_1۰name۰datas).
    #[local] Definition datas۰elem' γ_datas :=
      mono_gmultiset۰elem γ_datas.
    #[local] Definition datas۰elem γ :=
      datas۰elem' γ.(ws_deque_1۰name۰datas).

    #[local] Definition data۰model data : iProp Σ :=
      ∃ cap i vs,
      array۰cslice data cap i DfracDiscarded vs ∗
      ⌜0 < cap⌝ ∗
      ⌜length vs = cap⌝.
    #[local] Instance : CustomIpat "data۰model" :=
      " ( %cap_data{}
        & %i_data{}
        & %vs_data{}
        & Hdata{}_cslice
        & %Hcap_data{}
        & %Hvs_data{}
        )
      ".

    #[local] Definition winner۰au γ front P : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(ws_deque_1۰name۰inv), ∅ <{
        ∀∀ v vs',
        ⌜vs = v :: vs'⌝ ∗
        model₁ γ vs' ∗
        history۰at γ front v
      , COMM
        P
      }>.
    #[local] Definition winner۰model₁ γ front data data_winner : iProp Σ :=
        ⌜data = data_winner⌝
      ∨ ∃ cap_winner v,
        array۰cslice data_winner cap_winner front DfracDiscarded [v]  ∗
        history۰at γ front v.
    #[local] Instance : CustomIpat "winner۰model₁" :=
      " [ ->
        | ( %cap
          & %v_
          & Hdata_cslice
          & Hhistory_at_
          )
        ]
      ".
    #[local] Definition winner۰model₂ γ front data data_winner P : iProp Σ :=
      winner۰steal γ front (Some data_winner) P ∗
      winner۰model₁ γ front data data_winner.
    #[local] Instance : CustomIpat "winner۰model₂" :=
      " ( Hwinner_steal{_{!}}
        & Hwinner
        )
      ".
    #[local] Definition winner۰pending₁ γ front data data_winner P id : iProp Σ :=
      winner۰model₂ γ front data data_winner P ∗
      identifier۰model id ∗
      winner۰au γ front P.
    #[local] Instance : CustomIpat "winner۰pending₁" :=
      " ( (:winner۰model₂)
        & Hid{_{!}}
        & HP
        )
      ".
    #[local] Definition winner۰pending₂ γ front data id : iProp Σ :=
      ∃ data_winner P,
      winner۰pending₁ γ front data data_winner P id.
    #[local] Instance : CustomIpat "winner۰pending₂" :=
      " ( %data_winner
        & %P{}
        & (:winner۰pending₁)
        )
      ".
    #[local] Definition winner۰linearized₁ γ front data data_winner P : iProp Σ :=
      winner۰model₂ γ front data data_winner P ∗
      P.
    #[local] Instance : CustomIpat "winner۰linearized₁" :=
      " ( (:winner۰model₂)
        & HP
        )
      ".
    #[local] Definition winner۰linearized₂ γ front data P : iProp Σ :=
      ∃ data_winner,
      winner۰linearized₁ γ front data data_winner P.
    #[local] Instance : CustomIpat "winner۰linearized₂" :=
      " ( %data_winner
        & (:winner۰linearized₁)
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
    #[local] Definition inv۰state۰nonempty γ stable front back data hist vs prophs : iProp Σ :=
      ⌜stable = Stable⌝ ∗
      ⌜front < back⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      history۰at γ front (hd inhabitant vs) ∗
      ( winner γ
      ∨ match prophs with
        | [] =>
            False
        | id :: _ =>
            winner۰pending₂ γ front data id
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
    #[local] Definition inv۰state۰nonempty۰steal γ state stable front back data hist vs prophs data_winner P : iProp Σ :=
      ⌜state = Nonempty⌝ ∗
      ⌜stable = Stable⌝ ∗
      ⌜front < back⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      history۰at γ front (hd inhabitant vs) ∗
      match prophs with
      | [] =>
          False
      | id :: _ =>
          winner۰pending₁ γ front data data_winner P id
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
    #[local] Definition inv۰state۰emptyish γ stable front back data hist priv : iProp Σ :=
      ∃ P,
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      history۰at γ front (hd inhabitant priv) ∗
      ( winner۰pop γ front None P
      ∨ winner۰linearized₂ γ front data P
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
      winner۰pop γ front None P.
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
    #[local] Definition inv۰state۰emptyish۰steal γ state stable front back data hist priv data_winner P : iProp Σ :=
      ⌜state = Emptyish⌝ ∗
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      history۰at γ front (hd inhabitant priv) ∗
      winner۰linearized₁ γ front data data_winner P.
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
        & (:winner۰linearized₁)
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
    #[local] Definition inv۰state γ state stable front back data hist vs priv prophs : iProp Σ :=
      match state with
      | Empty =>
          inv۰state۰empty γ stable front back hist
      | Nonempty =>
          inv۰state۰nonempty γ stable front back data hist vs prophs
      | Emptyish =>
          inv۰state۰emptyish γ stable front back data hist priv
      | Superempty =>
          inv۰state۰superempty γ stable front back hist
      end.

    #[local] Definition inv۰inner t γ : iProp Σ :=
      ∃ state stable front back data cap hist vs priv datas pasts prophss,
      t.[front] ↦ #front ∗
      t.[back] ↦ #back ∗
      t.[data] ↦ data ∗
      owner₂ γ stable back data cap ∗
      front۰auth γ front ∗
      ⌜0 < front⌝ ∗
      model₂ γ vs ∗
      ⌜length vs = back - front⌝ ∗
      array۰cslice data cap front (DfracOwn (1/2)) (vs ++ priv) ∗
      ⌜0 < cap⌝ ∗
      ⌜(length vs + length priv)%nat = cap⌝ ∗
      history۰auth γ hist ∗
      datas۰auth γ ({[+data+]} ⊎ datas) ∗
      ([∗ mset] data ∈ datas, data۰model data) ∗
      prophet_multi۰model prophet_identifier γ.(ws_deque_1۰name۰prophet) γ.(ws_deque_1۰name۰prophet_name) pasts prophss ∗
      ⌜∀ i, front ≤ i → pasts i = []⌝ ∗
      inv۰state γ state stable front back data hist vs priv (prophss front).
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %state{}
        & %stable{}
        & %front{}
        & %back{}
        & %data{}
        & %cap{}
        & %hist{}
        & %vs{}
        & %priv{}
        & %datas{}
        & %pasts{}
        & %prophss{}
        & >Ht_front
        & >Ht_back
        & >Ht_data
        & >Howner₂
        & >Hfront_auth
        & >%Hfront{}
        & >Hmodel₂
        & >%Hvs{}
        & >Hdata{}_cslice₁
        & >%Hcap{}
        & >%Hdata{}
        & >Hhistory_auth
        & >Hdatas_auth
        & >Hdatas
        & >Hprophet_model
        & >%Hpasts{}
        & Hstate
        )
      ".
    #[local] Definition inv' t γ : iProp Σ :=
      t.[proph] ↦□ #γ.(ws_deque_1۰name۰prophet) ∗
      inv γ.(ws_deque_1۰name۰inv) (inv۰inner t γ).
    #[local] Instance : CustomIpat "inv'" :=
      " ( #Ht_proph
        & #Hinv
        )
      ".
    Definition ws_deque_1۰inv t γ ι : iProp Σ :=
      ⌜ι = γ.(ws_deque_1۰name۰inv)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & (:inv')
        )
      ".

    Definition ws_deque_1۰model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    #[local] Definition owner' γ stable back data cap ws i us : iProp Σ :=
      owner₁ γ stable back data cap ws ∗
      array۰cslice data cap i (DfracOwn (1/2)) us ∗
      ⌜0 < cap⌝ ∗
      ⌜length us = cap⌝.
    #[local] Instance : CustomIpat "owner'" :=
      " ( Howner₁{_{}}
        & Hdata_cslice₂{_{}}
        & { {!} _
          ; %Hcap{}
          ; %Hcap
          }
        & { {!} _
          ; %Hus{}
          ; %Hus
          }
        )
      ".
    Definition ws_deque_1۰owner γ ws : iProp Σ :=
      ∃ back data cap i us,
      owner' γ Stable back data cap ws i us.
    #[local] Instance : CustomIpat "owner" :=
      " ( %back{}
        & %data{}
        & %cap{}
        & %i{}
        & %us{}
        & Howner{_{}}
        )
      ".

    #[global] Instance ws_deque_1۰model𑁒timeless γ vs :
      Timeless (ws_deque_1۰model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ws_deque_1۰owner𑁒timeless γ ws :
      Timeless (ws_deque_1۰owner γ ws).
    Proof.
      apply _.
    Qed.

    #[global] Instance ws_deque_1۰inv𑁒persistent t γ ι :
      Persistent (ws_deque_1۰inv t γ ι).
    Proof.
      apply _.
    Qed.

    #[local] Lemma model𑁒owner𑁒alloc data cap :
      ⊢ |==>
        ∃ γ_model γ_owner,
        model₁' γ_model [] ∗
        model₂' γ_model [] ∗
        owner₁' γ_owner γ_model Stable 1 data cap [] ∗
        owner₂' γ_owner Stable 1 data cap.
    Proof.
      iMod (auth_twins𑁒alloc _ (auth_twins۰G := ws_deque_1۰G۰model۰G)) as "(%γ_model & Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iMod (twins𑁒alloc' (twins۰G := ws_deque_1۰G۰owner۰G)) as "(%γ_owner & Howner₁ & Howner₂)".
      iFrameSteps.
    Qed.
    #[local] Lemma model₁𑁒valid γ stable back data cap ws vs :
      owner₁ γ stable back data cap ws -∗
      model₁ γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:owner₁) Hmodel₁".
      iDestruct (auth_twins𑁒valid₁ with "Hmodel_auth Hmodel₁") as %H.
      rewrite preorder𑁒rtc in H. iSteps.
    Qed.
    #[local] Lemma model₁𑁒exclusive γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₁ γ vs2 -∗
      False.
    Proof.
      apply auth_twins۰twin₁𑁒exclusive.
    Qed.
    #[local] Lemma model𑁒agree γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      apply: auth_twins𑁒agree𑁒L.
    Qed.
    #[local] Lemma model۰owner₁𑁒agree γ stable back data cap ws vs1 vs2 :
      owner₁ γ stable back data cap ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
        ⌜vs1 `suffix_of` ws⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Howner₁ Hmodel₁ Hmodel₂".
      iDestruct (model₁𑁒valid with "Howner₁ Hmodel₁") as %Hsuffix.
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iSteps.
    Qed.
    #[local] Lemma model𑁒empty {γ stable back data cap ws vs1 vs2} :
      owner₁ γ stable back data cap ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back data cap [] ∗
        model₁ γ [] ∗
        model₂ γ [].
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twins𑁒update𑁒auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iSteps.
    Qed.
    #[local] Lemma model𑁒push {γ stable back data cap ws vs1 vs2} v :
      owner₁ γ stable back data cap ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back data cap (vs1 ++ [v]) ∗
        model₁ γ (vs1 ++ [v]) ∗
        model₂ γ (vs1 ++ [v]).
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twins𑁒update𑁒auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iSteps.
    Qed.
    #[local] Lemma model𑁒steal γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        model₁ γ (tail vs1) ∗
        model₂ γ (tail vs1).
    Proof.
      apply: auth_twins𑁒update𑁒twins𑁒L.
      rewrite preorder𑁒rtc. apply suffix𑁒tail. done.
    Qed.
    #[local] Lemma model𑁒pop γ stable back data cap ws vs1 vs2 :
      owner₁ γ stable back data cap ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back data cap (removelast vs1) ∗
        model₁ γ (removelast vs1) ∗
        model₂ γ (removelast vs1).
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twins𑁒update𑁒auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iSteps.
    Qed.
    #[local] Lemma model𑁒pop' γ stable back data cap ws vs1 v vs2 :
      owner₁ γ stable back data cap ws -∗
      model₁ γ (vs1 ++ [v]) -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back data cap vs1 ∗
        model₁ γ vs1 ∗
        model₂ γ vs1.
    Proof.
      rewrite -{2 3 4}(removelast_last vs1 v).
      apply model𑁒pop.
    Qed.

    #[local] Lemma owner₁𑁒exclusive γ stable1 back1 data1 cap1 ws1 stable2 back2 data2 cap2 ws2 :
      owner₁ γ stable1 back1 data1 cap1 ws1 -∗
      owner₁ γ stable2 back2 data2 cap2 ws2 -∗
      False.
    Proof.
      iIntros "(:owner₁ =1) (:owner₁ =2)".
      iApply (twins۰twin₁𑁒exclusive with "Howner₁_1 Howner₁_2").
    Qed.
    #[local] Lemma owner𑁒agree γ stable1 back1 data1 cap1 ws stable2 back2 data2 cap2 :
      owner₁ γ stable1 back1 data1 cap1 ws -∗
      owner₂ γ stable2 back2 data2 cap2 -∗
        ⌜stable1 = stable2⌝ ∗
        ⌜back1 = back2⌝ ∗
        ⌜data1 = data2⌝ ∗
        ⌜cap1 = cap2⌝.
    Proof.
      iIntros "(:owner₁) Howner₂".
      iDestruct (twins𑁒agree𑁒L with "Howner₁ Howner₂") as %[= <- <- <- <-].
      iSteps.
    Qed.
    #[local] Lemma owner₁𑁒update γ stable back data cap ws vs :
      owner₁ γ stable back data cap ws -∗
      model₁ γ vs -∗
      model₂ γ vs ==∗
        owner₁ γ stable back data cap vs ∗
        model₁ γ vs ∗
        model₂ γ vs.
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twins𑁒update𑁒auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "($ & $ & $)".
      iSteps.
    Qed.
    #[local] Lemma owner𑁒update {γ stable1 back1 data1 cap1 ws stable2 back2 data2 cap2} stable back data cap :
      owner₁ γ stable1 back1 data1 cap1 ws -∗
      owner₂ γ stable2 back2 data2 cap2 ==∗
        owner₁ γ stable back data cap ws ∗
        owner₂ γ stable back data cap.
    Proof.
      iIntros "(:owner₁) Howner₂".
      iMod (twins𑁒update with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iSteps.
    Qed.

    #[local] Lemma front𑁒alloc :
      ⊢ |==>
        ∃ γ_front,
        front۰auth' γ_front 1.
    Proof.
      apply auth_nat_max𑁒alloc.
    Qed.
    #[local] Lemma front۰lb𑁒get γ front :
      front۰auth γ front ⊢
      front۰lb γ front.
    Proof.
      apply auth_nat_max۰lb𑁒get.
    Qed.
    #[local] Lemma front۰lb𑁒le {γ front} front' :
      front' ≤ front →
      front۰lb γ front ⊢
      front۰lb γ front'.
    Proof.
      apply auth_nat_max۰lb𑁒le.
    Qed.
    #[local] Lemma front۰lb𑁒valid γ front1 front2 :
      front۰auth γ front1 -∗
      front۰lb γ front2 -∗
      ⌜front2 ≤ front1⌝.
    Proof.
      apply auth_nat_max۰lb𑁒valid.
    Qed.
    #[local] Lemma front𑁒update γ front :
      front۰auth γ front ⊢ |==>
      front۰auth γ ˖front.
    Proof.
      apply auth_nat_max𑁒update; first lia.
    Qed.

    #[local] Lemma history𑁒alloc :
      ⊢ |==>
        ∃ γ_hist,
        history۰auth' γ_hist [()%V].
    Proof.
      apply mono_list𑁒alloc.
    Qed.
    #[local] Lemma history۰at𑁒get {γ hist v} i :
      i = length hist →
      history۰auth γ (hist ++ [v]) ⊢
      history۰at γ i v.
    Proof.
      intros ->.
      apply mono_list۰at𑁒get, list_lookup_middle. done.
    Qed.
    #[local] Lemma history۰at𑁒lookup γ hist i v :
      history۰auth γ hist -∗
      history۰at γ i v -∗
      ⌜hist !! i = Some v⌝.
    Proof.
      apply mono_list۰at𑁒valid.
    Qed.
    #[local] Lemma history۰at𑁒agree γ i v1 v2 :
      history۰at γ i v1 -∗
      history۰at γ i v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply mono_list۰at𑁒agree.
    Qed.
    #[local] Lemma history𑁒update {γ hist} i v :
      i = length hist →
      history۰auth γ hist ⊢ |==>
        history۰auth γ (hist ++ [v]) ∗
        history۰at γ i v.
    Proof.
      iIntros (->) "Hauth".
      iMod (mono_list𑁒update𑁒snoc with "Hauth") as "Hauth".
      iDestruct (history۰at𑁒get with "Hauth") as "#Hat"; first done.
      iSteps.
    Qed.

    #[local] Lemma winner𑁒alloc :
      ⊢ |==>
        ∃ γ_winner,
        winner۰pop' γ_winner 1 None True ∗
        winner۰steal' γ_winner 1 None True.
    Proof.
      apply twins𑁒alloc'.
    Qed.
    #[local] Lemma winner۰pop𑁒exclusive γ front1 data1 P1 front2 data2 P2 :
      winner۰pop γ front1 data1 P1 -∗
      winner۰pop γ front2 data2 P2 -∗
      False.
    Proof.
      apply twins۰twin₁𑁒exclusive.
    Qed.
    #[local] Lemma winner۰pop𑁒exclusive' γ front data P :
      winner۰pop γ front data P -∗
      winner γ -∗
      False.
    Proof.
      iIntros "Hwinner_pop_1 (:winner =2)".
      iApply (winner۰pop𑁒exclusive with "Hwinner_pop_1 Hwinner_pop_2").
    Qed.
    #[local] Lemma winner۰steal𑁒exclusive γ front1 data1 P1 front2 data2 P2 :
      winner۰steal γ front1 data1 P1 -∗
      winner۰steal γ front2 data2 P2 -∗
      False.
    Proof.
      apply twins۰twin₂𑁒exclusive.
    Qed.
    #[local] Lemma winner۰steal𑁒exclusive' γ front data P :
      winner۰steal γ front data P -∗
      winner γ -∗
      False.
    Proof.
      iIntros "Hwinner_steal_1 (:winner =2)".
      iApply (winner۰steal𑁒exclusive with "Hwinner_steal_1 Hwinner_steal_2").
    Qed.
    #[local] Lemma winner𑁒agree γ front1 data1 P1 front2 data2 P2 :
      winner۰pop γ front1 data1 P1 -∗
      winner۰steal γ front2 data2 P2 -∗
        ⌜front1 = front2⌝ ∗
        ⌜data1 = data2⌝ ∗
        ▷ (P1 ≡ P2).
    Proof.
      iIntros "Hwinner_pop Hwinner_steal".
      iDestruct (twins𑁒agree with "Hwinner_pop Hwinner_steal") as "#Heq".
      rewrite !prod_equivI /= !discrete_eq_1.
      iDestruct "Heq" as "(($ & $) & $)".
    Qed.
    #[local] Lemma winner𑁒update' {γ front1 data1 P1 front2 data2 P2} front data :
      winner۰pop γ front1 data1 P1 -∗
      winner۰steal γ front2 data2 P2 ==∗
        winner۰pop γ front data P1 ∗
        winner۰steal γ front data P2.
    Proof.
      iIntros "Hwinner_pop Hwinner_steal".
      iDestruct (winner𑁒agree with "Hwinner_pop Hwinner_steal") as "#(_ & _ & Heq)".
      iApply (twins𑁒update𑁒equivI with "Hwinner_pop Hwinner_steal").
      rewrite -later_equivI prod_equivI /=. auto.
    Qed.
    #[local] Lemma winner𑁒update {γ front1 data1 P1 front2 data2 P2} front data P :
      winner۰pop γ front1 data1 P1 -∗
      winner۰steal γ front2 data2 P2 ==∗
        winner۰pop γ front data P ∗
        winner۰steal γ front data P.
    Proof.
      apply twins𑁒update.
    Qed.

    #[local] Lemma datas𑁒alloc data :
      ⊢ |==>
        ∃ γ_datas,
        datas۰auth' γ_datas ({[+data+]} ⊎ ∅).
    Proof.
      apply mono_gmultiset𑁒alloc.
    Qed.
    #[local] Lemma datas۰elem𑁒get γ data datas :
      datas۰auth γ ({[+data+]} ⊎ datas) ⊢
      datas۰elem γ data.
    Proof.
      apply mono_gmultiset۰elem𑁒get; first set_solver.
    Qed.
    #[local] Lemma datas۰elem𑁒valid γ data1 datas data2 :
      datas۰auth γ ({[+data1+]} ⊎ datas) -∗
      datas۰elem γ data2 -∗
      ⌜data1 = data2 ∨ data2 ∈ datas⌝.
    Proof.
      iIntros "Hauth Helem".
      iDestruct (mono_gmultiset۰elem𑁒valid with "Hauth Helem") as %?. set_solver.
    Qed.
    #[local] Lemma datas𑁒insert {γ datas} data :
      datas۰auth γ datas ⊢ |==>
      datas۰auth γ ({[+data+]} ⊎ datas).
    Proof.
      apply mono_gmultiset𑁒insert.
    Qed.

    Opaque owner₁'.

    Lemma ws_deque_1۰model𑁒exclusive γ vs1 vs2 :
      ws_deque_1۰model γ vs1 -∗
      ws_deque_1۰model γ vs2 -∗
      False.
    Proof.
      apply model₁𑁒exclusive.
    Qed.

    #[local] Lemma owner'𑁒rebase {γ stable back data cap ws i1 us} i2 :
      owner' γ stable back data cap ws i1 us ⊢
        ∃ us,
        owner' γ stable back data cap ws i2 us.
    Proof.
      iIntros "(:owner')".
      iDestruct (array۰cslice𑁒rebase i2 with "Hdata_cslice₂") as "(%us' & %n & -> & Hdata_cslice₂ & _)"; [done.. |].
      iSteps. simpl_length.
    Qed.

    #[local] Lemma array۰cslice𑁒reshape {data cap back dq us} front :
      0 < cap →
      length us = cap →
      front ≤ back →
      back ≤ front + cap →
      array۰cslice data cap back dq us ⊢
        ∃ vs priv,
        ⌜(front + length vs)%nat = back⌝ ∗
        ⌜(length vs + length priv)%nat = cap⌝ ∗
        array۰cslice data cap front dq (vs ++ priv) ∗
        ( array۰cslice data cap front dq (vs ++ priv) -∗
          array۰cslice data cap back dq us
        ).
    Proof.
      iIntros "%Hcap %Hus % % Hdata_cslice".

      destruct_decide (back = front + cap) as Hback.

      - iDestruct (array۰cslice𑁒shift𑁒left' front with  "Hdata_cslice") as "Hdata_cslice"; [lia.. |].
        iExists us, []. rewrite app_nil_r. iSteps as "Hdata_cslice".
        iApply (array۰cslice𑁒shift𑁒right' with "Hdata_cslice"); first done.

      - iDestruct (array۰cslice𑁒rotation𑁒left𑁒small₁' front (back - front) with "Hdata_cslice") as "Hdata_cslice"; [lia.. |].
        iFrame. iSteps as_anon / as_anon / as "Hdata_cslice".
        1,2: iPureIntro; simpl_length; lia.
        iDestruct (array۰cslice𑁒rotation𑁒right𑁒small₁' back (back - front) with "Hdata_cslice") as "Hdata_cslice"; [simpl_length; lia.. |].
        rewrite rotation𑁒add; first lia.
        rewrite rotation𑁒length //; first lia.
    Qed.

    Lemma ws_deque_1۰owner𑁒exclusive γ ws1 ws2 :
      ws_deque_1۰owner γ ws1 -∗
      ws_deque_1۰owner γ ws2 -∗
      False.
    Proof.
      iIntros "(:owner =1) (:owner =2)".
      iDestruct "Howner_1" as "(:owner' =1)".
      iDestruct "Howner_2" as "(:owner' =2)".
      iApply (owner₁𑁒exclusive with "Howner₁_1 Howner₁_2").
    Qed.
    Lemma ws_deque_1𑁒owner𑁒model γ ws vs :
      ws_deque_1۰owner γ ws -∗
      ws_deque_1۰model γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:owner =1) (:model =2)".
      iDestruct "Howner_1" as "(:owner' =1)".
      iApply (model₁𑁒valid with "Howner₁_1 Hmodel₁_2").
    Qed.

    #[local] Lemma inv۰state𑁒Stable γ state front data back hist vs priv prophs :
      length vs = back - front →
      inv۰state γ state Stable front back data hist vs priv prophs ⊢
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
    #[local] Lemma inv۰state𑁒Unstable γ state front back data hist vs priv prophs :
      inv۰state γ state Unstable front back data hist vs priv prophs ⊢
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
    #[local] Lemma inv۰state𑁒Nonempty γ state stable front back data hist vs priv prophs :
      front < back →
      inv۰state γ state stable front back data hist vs priv prophs ⊢
      ⌜state = Nonempty⌝.
    Proof.
      iIntros "% Hstate".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty)". lia.
      - done.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish)". lia.
      - iDestruct "Hstate" as "(:inv۰state۰superempty)". lia.
    Qed.
    #[local] Lemma inv۰state𑁒Superempty γ state front back data hist vs priv prophs :
      back < front →
      inv۰state γ state Unstable front back data hist vs priv prophs -∗
      ⌜state = Superempty⌝.
    Proof.
      iIntros "% Hstate".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰nonempty lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish lazy=)". lia.
      - done.
    Qed.
    #[local] Lemma inv۰state𑁒winner۰pop γ state stable front1 back data1 hist vs priv prophs front2 data2 P :
      inv۰state γ state stable front1 back data1 hist vs priv prophs -∗
      winner۰pop γ front2 (Some data2) P -∗
        ∃ P_,
        ⌜front1 = front2⌝ ∗
        ▷ (P ≡ P_) ∗
        ( inv۰state۰nonempty۰steal γ state stable front2 back data1 hist vs prophs data2 P_
        ∨ inv۰state۰emptyish۰steal γ state stable front2 back data1 hist priv data2 P_
        ) ∗
        winner۰model₁ γ front2 data1 data2 ∗
        winner۰pop γ front2 (Some data2) P.
    Proof.
      iIntros "Hstate Hwinner_pop".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰pop𑁒exclusive with "Hwinner_pop Hwinner_pop_3") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰nonempty)".
        iDestruct "Hwinner" as "[(:winner =3) | Hwinner]".
        + iDestruct (winner۰pop𑁒exclusive with "Hwinner_pop Hwinner_pop_3") as %[].
        + destruct prophs as [| id prophs]; first done.
          iDestruct "Hwinner" as "(:winner۰pending₂ =_)".
          iDestruct (winner𑁒agree with "Hwinner_pop Hwinner_steal") as "#(<- & %Heq & $)". injection Heq as <-.
          iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish)".
        iDestruct "Hwinner" as "[Hwinner_pop_ | (:winner۰linearized₂)]".
        + iDestruct (winner۰pop𑁒exclusive with "Hwinner_pop Hwinner_pop_") as %[].
        + iDestruct (winner𑁒agree with "Hwinner_pop Hwinner_steal") as "#(<- & %Heq & $)". injection Heq as <-.
          iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰superempty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰pop𑁒exclusive with "Hwinner_pop Hwinner_pop_3") as %[].
    Qed.
    #[local] Lemma inv۰state𑁒winner۰steal γ state stable front2 back data1 hist vs priv prophs front1 data2 P :
      inv۰state γ state stable front1 back data1 hist vs priv prophs -∗
      winner۰steal γ front2 data2 P -∗
        ∃ P_,
        ⌜front1 = front2⌝ ∗
        ▷ (P_ ≡ P) ∗
        inv۰state۰emptyish۰pop γ state stable front2 back hist priv P_ ∗
        winner۰steal γ front2 data2 P.
    Proof.
      iIntros "Hstate Hwinner_steal".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰steal𑁒exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰nonempty)".
        destruct prophs as [| id prophs].
        + iDestruct "Hwinner" as "[(:winner =3) | []]".
          iDestruct (winner۰steal𑁒exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
        + iDestruct "Hwinner" as "[(:winner =3) | (:winner۰pending₂ =_ !=)]".
          * iDestruct (winner۰steal𑁒exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
          * iDestruct (winner۰steal𑁒exclusive with "Hwinner_steal Hwinner_steal_") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰emptyish)".
        iDestruct "Hwinner" as "[Hwinner_pop | (:winner۰linearized₂ !=)]".
        + iDestruct (winner𑁒agree with "Hwinner_pop Hwinner_steal") as "#(<- & _ & $)".
          iSteps.
        + iDestruct (winner۰steal𑁒exclusive with "Hwinner_steal Hwinner_steal_") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰superempty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰steal𑁒exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
    Qed.

    Lemma ws_deque_1٠create𑁒spec ι :
      {{{
        True
      }}}
        ws_deque_1٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        ws_deque_1۰inv t γ ι ∗
        ws_deque_1۰model γ [] ∗
        ws_deque_1۰owner γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.

      wp۰apply (prophet_multi𑁒wp𑁒proph with "[//]") as (pid γ_prophet prophss) "Hprophet_model".

      rewrite ws_deque_1٠min_capacity𑁒unfold.
      wp۰apply (array٠unsafe_make𑁒spec with "[//]") as (data) "Hdata_model"; first done.
      iEval (rewrite Nat2Z.id) in "Hdata_model".
      iDestruct (array۰model𑁒to𑁒cslice with "Hdata_model") as "Hdata_cslice".
      iEval (simpl_length) in "Hdata_cslice".
      iDestruct (array۰cslice𑁒to𑁒inv with "Hdata_cslice") as "#Hdata_inv".
      iDestruct (array۰cslice𑁒rotation𑁒right𑁒0 1 with "Hdata_cslice") as "Hdata_cslice"; [done.. |].
      iEval (rewrite rotation𑁒replicate) in "Hdata_cslice".
      iDestruct "Hdata_cslice" as "(Hdata_cslice₁ & Hdata_cslice₂)".

      wp۰block t as "Hmeta" "(Ht_front & Ht_back & Ht_data & Ht_proph & _)".
      iMod (pointsto𑁒persist with "Ht_proph") as "#Ht_proph".

      iMod model𑁒owner𑁒alloc as "(%γ_model & %γ_owner & Hmodel₁ & Hmodel₂ & Howner₁ & Howner₂)".
      iMod front𑁒alloc as "(%γ_front & Hfront_auth)".
      iMod history𑁒alloc as "(%γ_history & Hhist_auth)".
      iMod winner𑁒alloc as "(%γ_winner & Hwinner_pop & Hwinner_steal)".
      iMod (datas𑁒alloc data) as "(%γ_datas & Hdatas_auth)".

      set γ :=
        {|ws_deque_1۰name۰inv := ι
        ; ws_deque_1۰name۰prophet := pid
        ; ws_deque_1۰name۰prophet_name := γ_prophet
        ; ws_deque_1۰name۰model := γ_model
        ; ws_deque_1۰name۰owner := γ_owner
        ; ws_deque_1۰name۰front := γ_front
        ; ws_deque_1۰name۰history := γ_history
        ; ws_deque_1۰name۰winner := γ_winner
        ; ws_deque_1۰name۰datas := γ_datas
        |}.

      iApply ("HΦ" $! t γ).
      iFrame "#∗". iSplitL. 2: iSteps.
      iStep.
      iApply inv_alloc.
      iExists Empty, Stable, 1, 1, data, min_capacity, [()%V], [], (replicate min_capacity ()%V), ∅, (λ _, []), prophss.
      rewrite big_sepMS_empty. iFrameSteps.
    Qed.

    #[local] Lemma front𑁒spec t γ :
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
      iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb_1".
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    #[local] Lemma front𑁒spec𑁒owner𑁒Stable t γ back data cap ws :
      {{{
        inv' t γ ∗
        owner₁ γ Stable back data cap ws
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
        owner₁ γ Stable back data cap ws ∗
        front۰lb γ front ∗
        ⌜front ≤ back⌝
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".
      iDestruct (inv۰state𑁒Stable with "Hstate") as "#(_ & %)"; first done.
      iSplitR "Howner₁ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    #[local] Lemma front𑁒spec𑁒owner𑁒Unstable t γ back data cap ws :
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back data cap ws
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
        owner₁ γ Unstable back data cap ws ∗
        front۰lb γ front ∗
        ⌜front = back ∨ front = ˖back⌝
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".
      iDestruct (inv۰state𑁒Unstable with "Hstate") as "#(_ & %)".
      iSplitR "Howner₁ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    #[local] Lemma front𑁒spec𑁒Superempty t γ back data cap ws front :
      back < front →
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back data cap ws ∗
        front۰lb γ front
      }}}
        (#t).{front}
      {{{
        RET #front;
        owner₁ γ Unstable back data cap ws
      }}}.
    Proof.
      iIntros "% %Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰state𑁒Superempty with "Hstate") as %->; first lia.
      iDestruct "Hstate" as "(:inv۰state۰superempty =1 lazy=)".
      iSplitR "Howner₁ HΦ". { iExists Superempty. iFrameSteps. }
      replace ˖back with front by lia.
      iSteps.
    Qed.
    #[local] Lemma front𑁒spec𑁒winner۰steal t γ front data P :
      {{{
        inv' t γ ∗
        winner۰steal γ front data P
      }}}
        (#t).{front}
      {{{
        RET #front;
        winner۰steal γ front data P
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_steal) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.

      iAssert ⌜front1 = front⌝%I as %->.
      { iDestruct (inv۰state𑁒winner۰steal with "Hstate Hwinner_steal") as "(%P_ & $ & _)". }

      iSplitR "Hwinner_steal HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    #[local] Lemma back𑁒spec t γ stable back data cap ws :
      {{{
        inv' t γ ∗
        owner₁ γ stable back data cap ws
      }}}
        (#t).{back}
      {{{
        RET #back;
        owner₁ γ stable back data cap ws
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as "(<- & <- & <- & <-)".
      iSplitR "Howner₁ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    #[local] Lemma set_back𑁒spec𑁒Superempty t γ back data cap ws front (back' : Z) :
      back < front →
      back' = ˖back →
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back data cap ws ∗
        front۰lb γ front
      }}}
        #t <-{back} #back'
      {{{
        RET ();
        owner₁ γ Stable ˖back data cap ws
      }}}.
    Proof.
      iIntros (? ->) "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰store.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iMod (owner𑁒update Stable ˖back with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰state𑁒Superempty with "Hstate") as %->; first lia.
      iDestruct "Hstate" as "(:inv۰state۰superempty =1 lazy=)".
      iSplitR "Howner₁ HΦ". { iExists Empty. iFrameSteps. }
      iSteps.
    Qed.

    #[local] Lemma data𑁒spec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{data}
      {{{
        data
      , RET data;
        datas۰elem γ data
      }}}.
    Proof.
      iIntros "%Φ (:inv') HΦ".

      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      iDestruct (datas۰elem𑁒get with "Hdatas_auth") as "#Hdatas_elem".
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    #[local] Lemma data𑁒spec𑁒owner t γ stable back data cap ws :
      {{{
        inv' t γ ∗
        owner₁ γ stable back data cap ws
      }}}
        (#t).{data}
      {{{
        RET data;
        owner₁ γ stable back data cap ws
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iSplitR "Howner₁ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    #[local] Lemma data𑁒spec𑁒winner۰pop t γ front data P :
      {{{
        inv' t γ ∗
        winner۰pop γ front (Some data) P
      }}}
        (#t).{data}
      {{{
        data
      , RET data;
        winner۰pop γ front (Some data) P
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_pop) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.

      iAssert (
        winner۰pop γ front (Some data1) P ∗
        ▷ inv۰state γ state1 stable1 front1 back1 data1 hist1 vs1 priv1 (prophss1 front1)
      )%I with "[> Hwinner_pop Hstate]" as "(Hwinner_pop & Hstate)".
      { iDestruct (inv۰state𑁒winner۰pop with "Hstate Hwinner_pop") as "(%P_ & -> & _ & [(:inv۰state۰nonempty۰steal =1) | (:inv۰state۰emptyish۰steal =1)] & _ & Hwinner_pop)".
        - destruct (prophss1 front) as [| id prophs].
          { iDestruct "Hwinner" as %[]. }
          iDestruct "Hwinner" as "(:winner۰pending₁)".
          iMod (winner𑁒update' front (Some data1) with "Hwinner_pop Hwinner_steal") as "($ & Hwinner_steal)".
          iFrameSteps.
        - iMod (winner𑁒update' back1 (Some data1) with "Hwinner_pop Hwinner_steal") as "($ & Hwinner_steal)".
          iExists P_. iSteps.
      }

      iSplitR "Hwinner_pop HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    #[local] Lemma set_data𑁒spec t γ front vs back data1 cap1 priv1 ws data2 cap2 priv2 :
      0 < cap2 →
      front + length vs = back →
      length vs + length priv1 = cap1 →
      length vs + length priv2 = cap2 →
      {{{
        inv' t γ ∗
        owner₁ γ Stable back data1 cap1 ws ∗
        front۰lb γ front ∗
        array۰cslice data1 cap1 front (DfracOwn (1/2)) (vs ++ priv1) ∗
        array۰cslice data2 cap2 front (DfracOwn (1/2)) (vs ++ priv2)
      }}}
        #t <-{data} data2
      {{{
        RET ();
        owner₁ γ Stable back data2 cap2 ws ∗
        array۰cslice data1 cap1 front (DfracOwn (1/2)) (vs ++ priv1)
      }}}.
    Proof.
      iIntros "%Hcap2 % % % %Φ ((:inv') & Howner₁ & #Hfront_lb & Hdata1_cslice₂ & Hdata2_cslice) HΦ".

      iInv "Hinv" as "(:inv۰inner =3)".
      wp۰store.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iMod (owner𑁒update Stable back data2 cap2 with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iMod (datas𑁒insert data2 with "Hdatas_auth") as "Hdatas_auth".
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰state𑁒Stable with "Hstate") as "(%Hstate3 & %)"; first done.

      iAssert (
        ∃ priv,
        ⌜vs = priv ++ vs3⌝ ∗
        ⌜(front + length priv)%nat = front3⌝
      )%I as "(%priv & -> & %)".
      { destruct (nil_or_length_pos vs3) as [-> |].
        - iExists vs. rewrite app_nil_r.
          simpl in Hvs3. iSteps.
        - iDestruct (array۰cslice𑁒rotation𑁒left𑁒small₁' front (front3 - front) with "Hdata3_cslice₁") as "Hdata1_cslice₁"; [simpl_length; lia.. |].
          iDestruct (array۰cslice𑁒agree with "Hdata1_cslice₁ Hdata1_cslice₂") as %Heq%(f_equal (take $ length vs)).
          { simpl_length. lia. }
          rewrite take_app_length take_app take_take take_app_length' in Heq.
          { simpl_length. lia. }
          rewrite -Heq. iSteps. iPureIntro.
          simpl_length. lia.
      }

      iDestruct (array۰cslice𑁒rotation𑁒right₁' front3 (front3 - front) with "Hdata2_cslice") as "Hdata2_cslice"; [simpl_length; lia.. |].

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

      iMod (array۰cslice𑁒persist with "Hdata3_cslice₁") as "#Hdata1_cslice₁".
      iDestruct (big_sepMS𑁒insert₂ data1 with "Hdatas []") as "Hdatas".
      { iSteps. iPureIntro. simpl_length. }

      iSplitR "Howner₁ Hdata1_cslice₂ HΦ".
      { iExists state3. iFrameSteps.
        destruct Hstate3 as [-> | ->]; first iFrameSteps.
        iDestruct "Hstate" as "(:inv۰state۰nonempty =3 lazy=)".
        iStep 4.
        iDestruct "Hwinner" as "[$ | Hwinner]"; first iSteps.
        destruct (prophss3 front3) as [| id prophs]; first done.
        iDestruct "Hwinner" as "(:winner۰pending₂)".
        iRight. iFrame. iRight.
        iDestruct "Hwinner" as "(:winner۰model₁)"; last iFrameSteps.
        destruct vs3 as [| v vs3]; first naive_solver lia.
        iEval (rewrite -(assoc _ [_])) in "Hdata1_cslice₁".
        iDestruct (array۰cslice𑁒app₂ with "Hdata1_cslice₁") as "-#($ & _)"; first done.
        iSteps.
      }
      iSteps.
    Qed.

    #[local] Lemma array٠unsafe_cget𑁒spec𑁒loser t γ (data : val) i :
      (0 ≤ i)%Z →
      {{{
        inv' t γ ∗
        datas۰elem γ data
      }}}
        array٠unsafe_cget data #i
      {{{
        v
      , RET v;
        True
      }}}.
    Proof.
      iIntros "%Hi %Φ ((:inv') & #Hdatas_elem) HΦ".

      iApply wp𑁒fupd.
      wp۰apply (wp𑁒wand (λ _, £ 1)%I).
      { awp۰apply (array٠unsafe_cget𑁒spec𑁒atomic𑁒weak with "[//]"); first done.
        iInv "Hinv" as "(:inv۰inner =1)".
        iDestruct (datas۰elem𑁒valid with "Hdatas_auth Hdatas_elem") as %[-> | Hdatas1_elem].

        - iAaccIntro with "[$Hdata1_cslice₁]".
          { iPureIntro. simpl_length. }
          { iIntros "(Hdata1_cslice₁ & _ & _) !>". iFrameSteps. }
          iIntros "Hdata1_cslice₁ !>".
          iSplitL. { iFrameSteps. }
          iSteps.

        - iDestruct (big_sepMS_elem_of_acc with "Hdatas") as "((:data۰model) & Hdatas)"; first done.
          iAaccIntro with "[$Hdata_cslice]".
          { iSteps. }
          { iIntros "(Hdata_cslice & _ & _) !>". iFrameSteps. }
          iIntros "Hdata_cslice !>".
          iSplitL. { iFrameSteps. }
          iSteps.
      }

      iIntros "%v H£".
      iMod (lc_fupd_elim_later with "H£ HΦ").
      iSteps.
    Qed.
    #[local] Lemma array٠unsafe_cget𑁒spec𑁒winner۰pop t γ front data P v :
      {{{
        inv' t γ ∗
        winner۰pop γ front (Some data) P ∗
        history۰at γ front v
      }}}
        array٠unsafe_cget data #front
      {{{
        RET v;
        winner۰pop γ front (Some data) P
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_pop & #Hhistory_at) HΦ".

      iApply wp𑁒fupd.
      awp۰apply (array٠unsafe_cget𑁒spec𑁒atomic with "[//]") without "HΦ".
      iInv "Hinv" as "(:inv۰inner =1)".

      iAssert (◇ (
        ⌜front1 = front⌝ ∗
        ⌜hd inhabitant (vs1 ++ priv1) = v⌝ ∗
        winner۰model₁ γ front data1 data
      ))%I as "#>(-> & %Hlookup & Hwinner)".
      { iDestruct (inv۰state𑁒winner۰pop with "Hstate [$Hwinner_pop]") as "(%P_ & >-> & _ & [(:inv۰state۰nonempty۰steal =1 >) | (:inv۰state۰emptyish۰steal =1 >)] & >$ & Hwinner_pop)".
        - iDestruct (history۰at𑁒agree with "Hhistory_at Hhistory_at_front1") as ">->".
          rewrite hd𑁒app //; first lia.
        - iDestruct (history۰at𑁒agree with "Hhistory_at Hhistory_at_front1") as ">->".
          assert (length vs1 = 0) as ->%nil_length_inv by lia.
          iSteps.
      }

      iDestruct "Hwinner" as "(:winner۰model₁)".

      - apply hd𑁒correct in Hlookup; last (simpl_length; lia).
        rewrite head_lookup in Hlookup.

        iAaccIntro with "[$Hdata1_cslice₁]".
        { rewrite Nat2Z.id Nat.sub_diag. iSteps. }
        { iIntros "(_ & _ & Hdata1_cslice₁) !>". iFrameSteps. }
        iIntros "Hdata1_cslice₁ !>".
        iSplitR "Hwinner_pop". { iFrameSteps. }
        iIntros "H£ HΦ".
        iApply (lc_fupd_elim_later with "H£ HΦ Hwinner_pop").

      - iDestruct (history۰at𑁒agree with "Hhistory_at Hhistory_at_") as %<-.

        iAaccIntro with "[$Hdata_cslice]".
        { rewrite Nat2Z.id Nat.sub_diag. iSteps. }
        { iIntros "_ !>". iFrameSteps. }
        iIntros "_ !>".
        iSplitR "Hwinner_pop". { iFrameSteps. }
        iIntros "H£ HΦ".
        iApply (lc_fupd_elim_later with "H£ HΦ Hwinner_pop").
    Qed.

    #[local] Lemma array٠unsafe_cset𑁒spec𑁒owner t γ back data cap ws us front v :
      back < front + cap →
      {{{
        inv' t γ ∗
        owner' γ Stable back data cap ws back us ∗
        front۰lb γ front
      }}}
        array٠unsafe_cset data #back v
      {{{
        RET ();
        owner' γ Stable back data cap ws back (<[0 := v]> us)
      }}}.
    Proof.
      iIntros "% %Φ ((:inv') & (:owner') & #Hfront_lb) HΦ".

      iApply wp𑁒fupd.
      awp۰apply (array٠unsafe_cset𑁒spec𑁒atomic𑁒cell with "[//]") without "HΦ".
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰state𑁒Stable with "Hstate") as "#>(%Hstate1 & %)"; first done.

      iDestruct (array۰cslice𑁒app with "Hdata1_cslice₁") as "(Hdata_cslice₁_1 & Hdata_cslice₁_2)".
      destruct (lookup_lt_is_Some_2 priv1 0) as (w & Hpriv_lookup); first lia.
      iDestruct (array۰cslice𑁒update with "Hdata_cslice₁_2") as "(Hdata_back₁ & Hdata_cslice₁_2)"; first done.
      replace (front1 + length vs1 + 0) with back by lia.

      destruct (lookup_lt_is_Some_2 us 0) as (w_ & Hus_lookup); first lia.
      iDestruct (array۰cslice𑁒update with "Hdata_cslice₂") as "(Hdata_back₂ & Hdata_cslice₂)"; first done.
      iEval (rewrite Nat.add_0_r) in "Hdata_back₂ Hdata_cslice₂".

      iDestruct (array۰cslice𑁒combine with "Hdata_back₁ Hdata_back₂") as "(%Heq & Hdata_back)"; first done. injection Heq as <-.
      iEval (rewrite dfrac_op_own Qp.half_half) in "Hdata_back".

      iAaccIntro with "[$Hdata_back]". 1: iSteps.

      - iIntros "(_ & (Hdata_back₁ & Hdata_back₂)) !>".

        iDestruct (array۰cslice𑁒app₁ with "Hdata_cslice₁_1 (Hdata_cslice₁_2 Hdata_back₁)") as "Hdata_cslice₁"; first done.
        iEval (rewrite list_insert_id //) in "Hdata_cslice₁".

        iDestruct ("Hdata_cslice₂" with "Hdata_back₂") as "Hdata_cslice₂".
        iEval (rewrite list_insert_id //) in "Hdata_cslice₂".

        iSplitR "Howner₁ Hdata_cslice₂". { iFrameSteps. }
        iSteps.

      - iIntros "(Hdata_back₁ & Hdata_back₂) !>".

        iDestruct (array۰cslice𑁒app₁ with "Hdata_cslice₁_1 (Hdata_cslice₁_2 Hdata_back₁)") as "Hdata_cslice₁"; first done.

        iDestruct ("Hdata_cslice₂" with "Hdata_back₂") as "Hdata_cslice₂".

        iSplitR "Howner₁ Hdata_cslice₂".
        { iFrameSteps.
          - iPureIntro. simpl_length.
          - iExists state1.
            destruct Hstate1 as [-> | ->]; iFrameSteps.
        }
        iIntros "H£ HΦ".

        iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
        iSteps. iPureIntro. simpl_length.
    Qed.

    #[local] Lemma resolve𑁒spec𑁒loser₁ t γ front1 front2 id :
      front1 < front2 →
      {{{
        inv' t γ ∗
        front۰lb γ front2
      }}}
        Resolve (CAS (#t).[front]%V #front1 #(front1 + 1)) #γ.(ws_deque_1۰name۰prophet) (#front1, #id)%V
      {{{
        RET false;
        True
      }}}.
    Proof.
      iIntros "%Hloser %Φ ((:inv') & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =3)".
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
      wp۰cas as Hcas; zoo_simplify in Hcas; last lia.
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
    #[local] Lemma resolve𑁒spec𑁒loser₂ t γ front id prophs0 :
      head prophs0 ≠ Some id →
      {{{
        inv' t γ ∗
        front۰lb γ front ∗
        prophet_multi۰full prophet_identifier γ.(ws_deque_1۰name۰prophet_name) front prophs0
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(ws_deque_1۰name۰prophet) (#front, #id)%V
      {{{
        RET false;
        front۰lb γ ˖front
      }}}.
    Proof.
      iIntros "%Hloser %Φ ((:inv') & #Hfront_lb & #Hprophet_full) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
      wp۰apply (wp𑁒cas𑁒nobranch' with "Ht_front") as (b) "%Hcas Ht_front".
      iStep. iIntros "%prophs %Hprophss1 Hprophet_model".
      destruct b; zoo_simplify in Hcas; first subst front1.

      - iDestruct (prophet_multi۰full𑁒valid with "Hprophet_model Hprophet_full") as %->.
        rewrite fn_lookup_alter Hpasts1 // in Hloser.

      - iDestruct (front۰lb𑁒get with "Hfront_auth") as "#-#Hfront_lb_1".
        iDestruct (front۰lb𑁒le ˖front with "Hfront_lb_1") as "-##Hfront_lb_1"; first lia.
        iSplitR "HΦ".
        { iFrameSteps.
          - iPureIntro => *.
            rewrite fn_lookup_alter_ne; first lia.
            auto.
          - rewrite fn_lookup_insert_ne //. iSteps.
        }
        iSteps.
    Qed.
    #[local] Lemma resolve𑁒spec𑁒winner۰pop t γ front data P id :
      {{{
        inv' t γ ∗
        winner۰pop γ front (Some data) P
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(ws_deque_1۰name۰prophet) (#front, #id)%V
      {{{
        RET true;
        ▷ P
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_pop) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
      wp۰apply (wp𑁒cas𑁒nobranch' with "Ht_front") as (b) "%Hcas Ht_front".
      iStep. iIntros "%prophs %Hprophss1 Hprophet_model".
      iDestruct (inv۰state𑁒winner۰pop with "Hstate Hwinner_pop") as "(%P_ & -> & #Heq & Hstate & _ & Hwinner_pop)".
      rewrite Hprophss1.
      destruct b; zoo_simplify in Hcas; last congruence.
      iMod (front𑁒update with "Hfront_auth") as "Hfront_auth".
      iDestruct "Hstate" as "[(:inv۰state۰nonempty۰steal =1) | (:inv۰state۰emptyish۰steal =1)]".

      - iDestruct "Hwinner" as "(:winner۰pending₁)".
        destruct vs1 as [| v1 vs1] => /=; first naive_solver lia.

        iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model𑁒steal with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂) /=".
        iMod ("HP" with "[$Hmodel₁ $Hhistory_at_front1 //]") as "HP".

        iDestruct (array۰cslice𑁒rotation𑁒right₁' ˖front 1 with "Hdata1_cslice₁") as "Hdata1_cslice₁"; [simpl_length/=; lia.. |].
        eassert (rotation _ _ = vs1 ++ priv1 ++ [v1]) as ->.
        { destruct_decide (cap1 = 1) as Heq | ?.
          - rewrite -> Heq in *.
            simpl in Hdata1.
            assert (length vs1 = 0) as ->%nil_length_inv by lia.
            assert (length priv1 = 0) as ->%nil_length_inv by lia.
            done.
          - rewrite Nat.mod_1_l; first lia.
            rewrite rotation𑁒S; first lia.
            rewrite rotation𑁒0 assoc //.
        }

        iSplitR "HP HΦ".
        { destruct_decide (˖front = back1) as <- | ?.

          - simpl in Hvs1.
            iExists Empty. iFrameSteps; iPureIntro.
            + simpl_length/=. lia.
            + intros.
              rewrite fn_lookup_alter_ne; first lia.
              apply Hpasts1; first lia.

          - destruct vs1 as [| v2 vs1] => /=; first naive_solver lia.
            simpl in Hvs1.
            iMod (history𑁒update _ v2 with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)"; first done.
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

        iDestruct (array۰cslice𑁒rotation𑁒right₁' ˖back1 1 with "Hdata1_cslice₁") as "Hdata1_cslice₁"; [simpl_length/=; lia.. |].
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
    #[local] Lemma resolve𑁒spec𑁒winner۰steal t γ front P id :
      {{{
        inv' t γ ∗
        winner۰steal γ front None P
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(ws_deque_1۰name۰prophet) (#front, #id)%V
      {{{
        RET true;
        front۰lb γ ˖front
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Hwinner_steal) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
      wp۰apply (wp𑁒cas𑁒nobranch' with "Ht_front") as (b) "%Hcas Ht_front".
      iStep. iIntros "%prophs %Hprophss1 Hprophet_model".
      iDestruct (inv۰state𑁒winner۰steal with "Hstate Hwinner_steal") as "(%P_ & -> & _ & (:inv۰state۰emptyish۰pop =1) & Hwinner_steal)".
      destruct b; zoo_simplify in Hcas; last congruence.
      iMod (front𑁒update with "Hfront_auth") as "Hfront_auth".
      iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".

      assert (length vs1 = 0) as ->%nil_length_inv by lia.

      iDestruct (array۰cslice𑁒rotation𑁒right₁' ˖back1 1 with "Hdata1_cslice₁") as "Hdata1_cslice₁"; [simpl_length; lia.. |].
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
    #[local] Lemma resolve𑁒spec𑁒Empty t γ back data cap ws id :
      {{{
        inv' t γ ∗
        owner₁ γ Stable back data cap ws ∗
        front۰lb γ back
      }}}
        Resolve (CAS (#t).[front]%V #back #(back + 1)) #γ.(ws_deque_1۰name۰prophet) (#back, #id)%V
      {{{
        RET true;
        owner₁ γ Unstable back data cap ws ∗
        front۰lb γ ˖back
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
      wp۰apply (wp𑁒cas𑁒nobranch' with "Ht_front") as (b) "%Hcas Ht_front".
      iStep. iIntros "%prophs %Hprophss1 Hprophet_model".
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰state𑁒Stable with "Hstate") as "#([-> | ->] & _)"; first done.

      - iDestruct "Hstate" as "(:inv۰state۰empty =1 lazy=)".
        assert (length vs1 = 0) as ->%nil_length_inv by lia.
        destruct b; zoo_simplify in Hcas; last lia.

        iMod (front𑁒update with "Hfront_auth") as "Hfront_auth".
        iClear "Hfront_lb". iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".
        iMod (history𑁒update _ inhabitant with "Hhistory_auth") as "(Hhistory_auth & _)"; first done.
        iMod (owner𑁒update Unstable (length hist1) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

        iDestruct (array۰cslice𑁒rotation𑁒right₁' ˖(length hist1) 1 with "Hdata1_cslice₁") as "Hdata_cslice₁"; [simpl_length; lia.. |].
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

      - iDestruct "Hstate" as "(:inv۰state۰nonempty =1 lazy=)".
        exfalso. lia.
    Qed.

    Lemma ws_deque_1٠size𑁒spec t γ ι ws :
      <<<
        ws_deque_1۰inv t γ ι ∗
        ws_deque_1۰owner γ ws
      | ∀∀ vs,
        ws_deque_1۰model γ vs
      >>>
        ws_deque_1٠size #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_deque_1۰model γ vs
      | RET #(length vs);
        ws_deque_1۰owner γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".
      iDestruct "Howner" as "(:owner')".

      wp۰rec.

      wp۰bind (_.{front})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iDestruct (inv۰state𑁒Stable with "Hstate") as %(_ & Hback); first done.

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
      iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
      iMod (owner₁𑁒update with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁ //]") as "HΦ".

      iSplitR "Howner₁ Hdata_cslice₂ HΦ". { iFrameSteps. }
      iIntros "!> {%- Hcap Hus Hvs1 Hback}".

      wp۰apply (back𑁒spec with "[$Howner₁]") as "Howner₁"; first iSteps.
      wp۰pures.

      replace (⁺back - ⁺front1)%Z with ⁺(length vs) by lia.
      iSteps.
    Qed.

    Lemma ws_deque_1٠is_empty𑁒spec t γ ι ws :
      <<<
        ws_deque_1۰inv t γ ι ∗
        ws_deque_1۰owner γ ws
      | ∀∀ vs,
        ws_deque_1۰model γ vs
      >>>
        ws_deque_1٠is_empty #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_deque_1۰model γ vs
      | RET #(bool_decide (vs = []%list));
        ws_deque_1۰owner γ vs
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & Howner) HΦ".

      wp۰rec.
      wp۰apply (ws_deque_1٠size𑁒spec with "[$]").
      iApply (atomic_update𑁒wand with "HΦ"). iIntros "%vs HΦ (%Hvs & Howner)".
      wp۰pures.

      rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
      { rewrite -length_zero_iff_nil. lia. }
      iApply "HΦ".
      iFrameSteps.
    Qed.

    Lemma ws_deque_1٠push𑁒spec t γ ι ws v :
      <<<
        ws_deque_1۰inv t γ ι ∗
        ws_deque_1۰owner γ ws
      | ∀∀ vs,
        ws_deque_1۰model γ vs
      >>>
        ws_deque_1٠push #t v @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_deque_1۰model γ (vs ++ [v])
      | RET ();
        ws_deque_1۰owner γ (vs ++ [v])
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".
      rename us into us0. iDestruct (owner'𑁒rebase with "Howner") as "(%us & (:owner'))".

      wp۰rec.
      wp۰apply+ (back𑁒spec with "[$]") as "Howner₁".
      wp۰apply+ (data𑁒spec𑁒owner with "[$]") as "Howner₁".
      wp۰apply+ (array٠size𑁒spec𑁒cslice with "Hdata_cslice₂") as "Hdata_cslice₂".
      wp۰pures.

      wp۰bind (_.{front})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".
      iSplitR "Howner₁ Hdata_cslice₂ HΦ". { iFrameSteps. }
      iIntros "!> {%- Hcap Hus Hvs1 Hdata1}".

      wp۰pures.

      wp۰bind (if: _ then _ else _)%E.
      wp۰apply (wp𑁒wand (λ _,
        ∃ data cap us,
        ⌜back < front1 + cap⌝ ∗
        ⌜us !! 0 = Some v⌝ ∗
        owner' γ Stable back data cap ws back us
      )%I with "[Howner₁ Hdata_cslice₂]") as (res) "{%} (%data & %cap & %us & % & %Hus_lookup & (:owner'))".
      { case_bool_decide; wp۰pures.

        - wp۰apply (array٠unsafe_cset𑁒spec𑁒owner with "[$Howner₁ $Hdata_cslice₂ $Hfront_lb]") as "(:owner' !=)"; [lia | iSteps |].

          iFrameSteps; iPureIntro.
          { apply list_lookup_insert_eq; first lia. }
          { simpl_length. }

        - assert (length priv1 = 0) as ->%nil_length_inv by lia.
          iEval (rewrite Z.shiftl_mul_pow2 //).

          iDestruct (array۰cslice𑁒reshape front1 with "Hdata_cslice₂") as "(%vs & %priv & % & % & Hdata_cslice₂ & _)"; [lia.. |].
          wp۰apply (array٠unsafe_cgrow𑁒spec with "Hdata_cslice₂") as (data') "(Hdata_cslice₂ & Hdata'_cslice)"; [simpl_length; lia.. |].

          wp۰apply+ (array٠unsafe_cset𑁒spec with "Hdata'_cslice") as "Hdata'_cslice".
          { simpl_length. lia. }
          iEval (rewrite -assoc insert𑁒app𑁒r𑁒0; first lia) in "Hdata'_cslice".
          iDestruct "Hdata'_cslice" as "(Hdata'_cslice₁ & Hdata'_cslice₂)".
          wp۰apply+ (set_data𑁒spec with "[$Howner₁ $Hdata_cslice₂ $Hdata'_cslice₁]") as "(Howner₁ & _)"; [simpl_length; lia.. | iSteps |].

          iDestruct (array۰cslice𑁒rotation𑁒right𑁒small₁' back cap with "Hdata'_cslice₂") as "Hdata'_cslice₂"; [simpl_length; lia.. |].
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

      wp۰pures.

      wp۰bind (_ <-{back} _)%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰store.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iMod (owner𑁒update Stable ˖back data cap with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iDestruct (inv۰state𑁒Stable with "Hstate") as "(%Hstate2 & %)"; first done.
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.

      iAssert ⌜head priv2 = Some v⌝%I as %(priv2' & ->)%head_Some.
      { iDestruct (array۰cslice𑁒rotation𑁒right𑁒small₁' back (length vs2) with "Hdata2_cslice₁") as "Hdata_cslice₁"; [simpl_length; lia.. |].
        rewrite /rotation drop_app_length.
        rewrite head_lookup -(lookup_app_l _ (take (length vs2) (vs2 ++ priv2))); first lia.
        iDestruct (array۰cslice𑁒agree with "Hdata_cslice₁ Hdata_cslice₂") as %->.
        { simpl_length. lia. }
        iSteps.
      }
      iEval (rewrite (assoc _ _ [_])) in "Hdata2_cslice₁".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
      iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
      iMod (model𑁒push v with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁ //]") as "HΦ".

      iSplitR "Howner₁ Hdata_cslice₂ HΦ".
      { iExists Nonempty.
        destruct Hstate2 as [-> | ->].

        - iDestruct "Hstate" as "(:inv۰state۰empty =1 lazy=)".
          assert (length vs = 0) as ->%nil_length_inv by lia.
          iMod (history𑁒update back v with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)"; first done.
          iFrameSteps. iPureIntro.
          simpl_length/=. lia.

        - iDestruct "Hstate" as "(:inv۰state۰nonempty =1 lazy=)".
          iFrameSteps; try iPureIntro.
          + simpl_length/=. lia.
          + simpl_length/=. lia.
          + rewrite hd𑁒app //; first lia.
      }
      iSteps.
    Qed.

    Lemma ws_deque_1٠steal𑁒spec t γ ι :
      <<<
        ws_deque_1۰inv t γ ι
      | ∀∀ vs,
        ws_deque_1۰model γ vs
      >>>
        ws_deque_1٠steal #t @ ↑ι
      <<<
        ws_deque_1۰model γ (tail vs)
      | RET head vs;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp۰rec.
      wp۰apply (wp𑁒id with "[//]") as (id) "Hid".
      wp۰apply+ (front𑁒spec with "[$]") as (front1) "#Hfront_lb_1".
      wp۰pures.

      wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰load.
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb_1") as %?.

      destruct_decide (front1 < back2) as Hbranch1; last first.
      { assert (length vs2 = 0) as ->%nil_length_inv by lia.

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΦ" with "Hmodel₁ [//]") as "HΦ".

        iSplitR "HΦ". { iFrameSteps. }
        iSteps.
      }

      destruct_decide (front1 = front2) as <- | ?; last first.
      { assert (front1 < front2) as Hbranch2 by lia.
        iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb_2".
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hbranch1 Hbranch2}".

        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰apply+ (data𑁒spec with "[$]") as (data) "#Hdatas_elem".
        wp۰apply+ (array٠unsafe_cget𑁒spec𑁒loser with "[$]") as (v) "_"; first lia.
        wp۰load.
        wp۰apply+ (resolve𑁒spec𑁒loser₁ with "[$]"); first done.
        iSteps.
      }

      iDestruct (prophet_multi۰full𑁒get _ front1 with "Hprophet_model") as "#Hprophet_full".
      iEval (rewrite Hpasts2 //=) in "Hprophet_full".

      destruct_decide (head $ prophss2 front1 = Some id) as (prophs0 & Hbranch3)%head_Some | Hbranch3; last first.
      { iSplitR "HΦ". { iFrameSteps. }
        remember (prophss2 front1) as prophs0.
        iIntros "!> {%- Hbranch1 Hbranch3}".

        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰apply+ (data𑁒spec with "[$]") as (data) "#Hdatas_elem".
        wp۰apply+ (array٠unsafe_cget𑁒spec𑁒loser with "[$]") as (v) "_"; first lia.
        wp۰load.
        wp۰apply+ (resolve𑁒spec𑁒loser₂ with "[$]"); first done.
        iSteps.
      }
      rewrite Hbranch3.

      iDestruct (inv۰state𑁒Nonempty with "Hstate") as %->; first done.
      iDestruct "Hstate" as "(:inv۰state۰nonempty =2)".
      iDestruct "Hwinner" as "[(:winner) | (:winner۰pending₂ !=)]"; last first.
      { iDestruct (identifier۰model𑁒exclusive with "Hid Hid_") as %[]. }

      destruct vs2 as [| v vs2] => /=; first naive_solver lia.
      iMod (winner𑁒update front1 (Some data2) (Φ (Some v)) with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

      iSplitR "Hwinner_pop".
      { iExists Nonempty. iFrameSteps.
        rewrite Hbranch3 /winner۰pending₂. iSteps. iIntros "!> !>".
        rewrite /winner۰au. iAuIntro.
        iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model)".
        iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%v_ %vs' (-> & Hmodel₁ & Hhistory_at) !>".
        iDestruct (history۰at𑁒agree with "Hhistory_at Hhistory_at_front2") as %<-.
        iSteps.
      }
      iIntros "!> {%- Hbranch1}".

      wp۰pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp۰apply+ (data𑁒spec𑁒winner۰pop with "[$]") as (data) "Hwinner_pop".
      wp۰apply+ (array٠unsafe_cget𑁒spec𑁒winner۰pop with "[$]") as "Hwinner_pop".
      wp۰load.
      wp۰apply+ (resolve𑁒spec𑁒winner۰pop with "[$]") as "HΦ".
      iSteps.
    Qed.

    Variant pop_state :=
      | PopNonempty v
      | PopEmptyishWinner v
      | PopEmptyishLoser
      | PopSuperempty.
    #[local] Lemma ws_deque_1٠pop₀𑁒spec {t γ} (state : pop_state) stable back (back_ : Z) data cap ws us id :
      back_ = back →
      {{{
        inv' t γ ∗
        owner' γ stable back data cap ws back us ∗
        match state with
        | PopNonempty v =>
            ⌜stable = Stable⌝ ∗
            ⌜us !! 0 = Some v⌝
        | PopEmptyishWinner v =>
            ⌜stable = Unstable⌝ ∗
            ⌜us !! 0 = Some v⌝ ∗
            winner۰steal γ back None inhabitant
        | PopEmptyishLoser =>
            ∃ id_winner prophs,
            ⌜stable = Unstable⌝ ∗
            prophet_multi۰full prophet_identifier γ.(ws_deque_1۰name۰prophet_name) back (id_winner :: prophs) ∗
            ⌜head (id_winner :: prophs) ≠ Some id⌝
        | PopSuperempty =>
            ∃ front,
            ⌜stable = Unstable⌝ ∗
            front۰lb γ front ∗
            ⌜front = ˖back⌝
        end
      }}}
        ws_deque_1٠pop₀ #t #id #back_
      {{{
        o back data cap i us
      , RET o;
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

      wp۰rec. wp۰pures.
      destruct state.

      - iDestruct "H" as "(-> & %Hus_lookup)".
        iSpecialize ("HΦ" $! (Some v)).

        wp۰apply (front𑁒spec𑁒owner𑁒Stable with "[$]") as (front2) "(Howner₁ & #Hfront_lb_1 & %Hfront2)".
        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰pures.
        case_bool_decide as Hbranch; wp۰pures.

        + wp۰apply (data𑁒spec𑁒owner with "[$]") as "Howner₁".
          wp۰apply+ (array٠size𑁒spec𑁒cslice with "Hdata_cslice₂") as "Hdata_cslice₂".
          rewrite ws_deque_1٠min_capacity𑁒unfold.
          wp۰pures.

          wp۰bind (if: _ then _ else _)%E.
          wp۰apply (wp𑁒wand (λ _,
            array۰cslice data cap back (DfracOwn (1/2)) us ∗
            ( array۰cslice data cap back (DfracOwn (1/2)) us -∗
                ∃ data' cap' us',
                owner' γ Stable back data' cap' ws back us'
            )
          )%I with "[Howner₁ Hdata_cslice₂]") as (res) "(Hdata_cslice₂ & Howner)".
          { case_bool_decide; wp۰pures; last iFrameSteps.
            iEval (rewrite Z.shiftr_div_pow2 //).

            iDestruct (array۰cslice𑁒reshape front2 with "Hdata_cslice₂") as "(%vs & %priv & % & % & Hdata_cslice₂ & Hdata_cslice₂_rebase)"; [lia.. |].
            wp۰apply (array٠unsafe_cshrink_slice𑁒spec𑁒fit with "Hdata_cslice₂") as (data') "(Hdata_cslice₂ & Hdata'_cslice)"; [simpl_length; lia.. |].
            iEval (rewrite take_app_ge; first lia) in "Hdata'_cslice".
            iDestruct "Hdata'_cslice" as "(Hdata'_cslice₁ & Hdata'_cslice₂)".
            wp۰apply+ (set_data𑁒spec with "[$Howner₁ $Hdata_cslice₂ $Hdata'_cslice₁]") as "(Howner₁ & Hdata_cslice₂)"; [simpl_length; lia.. | iSteps |].

            iDestruct ("Hdata_cslice₂_rebase" with "Hdata_cslice₂") as "$".
            iIntros "_".
            iDestruct (array۰cslice𑁒rebase back with "Hdata'_cslice₂") as "(% & %n & -> & $ & _)"; [simpl_length; lia.. |].
            iFrameSteps. iPureIntro. simpl_length. lia.
          }

          wp۰apply+ (array٠unsafe_cget𑁒spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
          iSteps.

        + replace front2 with back by lia.

          wp۰load.
          wp۰apply+ (resolve𑁒spec𑁒Empty with "[$]") as "(Howner₁ & #Hfront_lb_2)".
          wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]") as "Howner₁"; [lia.. |].
          wp۰apply+ (data𑁒spec𑁒owner with "[$]") as "Howner₁".
          wp۰apply (array٠unsafe_cget𑁒spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
          iSteps.

      - iDestruct "H" as "(-> & %Hus_lookup & Hwinner_steal)".
        iSpecialize ("HΦ" $! (Some v)).

        wp۰apply (front𑁒spec𑁒winner۰steal with "[$]") as "Hwinner_steal".
        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰load.
        wp۰apply+ (resolve𑁒spec𑁒winner۰steal with "[$]") as "#Hfront_lb".
        wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]") as "Howner₁"; [lia.. |].
        wp۰apply+ (data𑁒spec𑁒owner with "[$]") as "Howner₁".
        wp۰apply (array٠unsafe_cget𑁒spec with "Hdata_cslice₂") as "Hdata_cslice₂"; [done.. | lia |].
        iSteps.

      - iDestruct "H" as "(%id_winner & %prophs & -> & #Hprophet_full & %Hloser)".
        iSpecialize ("HΦ" $! None).

        wp۰apply (front𑁒spec𑁒owner𑁒Unstable with "[$]") as (front2) "(Howner₁ & #Hfront_lb_1 & %Hbranch)".
        wp۰pures.
        destruct Hbranch as [-> | ->].

        + rewrite bool_decide_eq_false_2; first lia.
          wp۰pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp۰load.
          wp۰apply+ (resolve𑁒spec𑁒loser₂ with "[$]") as "#Hfront_lb_2"; first done.
          wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]") as "Howner₁"; [lia.. |].
          iSteps.

        + rewrite bool_decide_eq_true_2; first lia.
          wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]") as "Howner₁"; [lia.. |].
          iSteps.

      - iDestruct "H" as "(%front & -> & #Hfront_lb & ->)".
        iSpecialize ("HΦ" $! None).

        wp۰apply (front𑁒spec𑁒Superempty with "[$]") as "Howner₁"; [lia |].
        wp۰pures.
        rewrite bool_decide_eq_true_2; first lia.
        wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]") as "Howner₁"; [lia.. |].
        iSteps.
    Qed.
    Lemma ws_deque_1٠pop𑁒spec t γ ι ws :
      <<<
        ws_deque_1۰inv t γ ι ∗
        ws_deque_1۰owner γ ws
      | ∀∀ vs,
        ws_deque_1۰model γ vs
      >>>
        ws_deque_1٠pop #t @ ↑ι
      <<<
        ∃∃ o ws',
        ⌜vs `suffix_of` ws⌝ ∗
        match o with
        | None =>
            ⌜vs = []⌝ ∗
            ⌜ws' = []⌝ ∗
            ws_deque_1۰model γ []
        | Some v =>
            ∃ vs',
            ⌜vs = vs' ++ [v]⌝ ∗
            ⌜ws' = vs'⌝ ∗
            ws_deque_1۰model γ vs'
        end
      | RET o;
        ws_deque_1۰owner γ ws'
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".
      rename us into us0. iDestruct (owner'𑁒rebase (back - 1) with "Howner") as "(%us & (:owner'))".

      wp۰rec.
      wp۰apply (wp𑁒id with "[//]") as (id) "Hid".
      wp۰apply+ (back𑁒spec with "[$]") as "Howner₁".
      wp۰pures.

      wp۰bind (_ <-{back} _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰store.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <- & <-).
      iDestruct (inv۰state𑁒Stable with "Hstate") as "#(%Hstate1 & %)"; first done.
      destruct Hstate1 as [-> | ->].

      { iDestruct "Hstate" as "(:inv۰state۰empty =1 lazy=)".
        assert (0 < back) as Hback by lia.
        assert (length vs1 = 0) as ->%nil_length_inv by lia.

        iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".
        iMod (owner𑁒update Unstable (back - 1) data cap with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (model𑁒empty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! None with "[$Hmodel₁ //]") as "HΦ".

        iSplitR "Howner₁ Hdata_cslice₂ HΦ".
        { iExists Superempty. iFrameSteps. }
        iIntros "!> {%- Hcap Hus Hback}".

        wp۰apply+ (ws_deque_1٠pop₀𑁒spec PopSuperempty _ (back - 1) with "[$Howner₁ $Hdata_cslice₂]"); [lia.. | iFrameSteps |].
        iSteps.
      }

      iDestruct "Hstate" as "(:inv۰state۰nonempty =1 lazy=)".
      assert (0 < back) as Hback by lia.
      destruct vs1 as [| v vs1 _] using rev_ind; first naive_solver lia.
      simpl_length/= in Hvs1.
      simpl_length/= in Hdata1.

      destruct_decide (˖front1 = back) as <- | Hbranch1.

      - assert (length vs1 = 0) as ->%nil_length_inv.
        { simpl_length/= in Hvs1. lia. }
        simpl in *.
        iEval (rewrite Nat.sub_0_r) in "Hdata_cslice₂".

        iAssert ⌜us !! 0 = Some v⌝%I as %Hus_lookup.
        { iDestruct (array۰cslice𑁒agree with "Hdata1_cslice₁ Hdata_cslice₂") as %<-; first (simpl; lia).
          iSteps.
        }

        iMod (owner𑁒update Unstable front1 data cap with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

        destruct_decide (head $ prophss1 front1 = Some id) as (prophs0 & Hprophss1)%head_Some | Hbranch2.

        + rewrite Hprophss1.
          iDestruct "Hwinner" as "[(:winner) | (:winner۰pending₂ !=)]"; last first.
          { iDestruct (identifier۰model𑁒exclusive with "Hid Hid_") as %[]. }
          iMod (winner𑁒update front1 inhabitant with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
          iMod (model𑁒pop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
          iMod ("HΦ" $! (Some v) with "[$Hmodel₁ //]") as "HΦ".

          iSplitR "Howner₁ Hdata_cslice₂ Hwinner_steal HΦ".
          { iExists Emptyish. iFrameSteps. }
          iIntros "!> {%- Hcap Hus Hback Hus_lookup}".

          wp۰apply+ (ws_deque_1٠pop₀𑁒spec (PopEmptyishWinner v) _ front1 with "[$Howner₁ $Hdata_cslice₂ $Hwinner_steal]"); [lia.. | iFrameSteps |].
          iSteps.

        + iDestruct "Hwinner" as "[(:winner) | Hwinner]".

          { iMod (winner𑁒update front1 inhabitant with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

            iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
            iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
            iMod (model𑁒pop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
            iMod ("HΦ" $! (Some v) with "[$Hmodel₁ //]") as "HΦ".

            iSplitR "Howner₁ Hdata_cslice₂ Hwinner_steal HΦ".
            { iExists Emptyish. iFrameSteps. }
            iIntros "!> {%- Hcap Hus Hus_lookup}".

            wp۰apply+ (ws_deque_1٠pop₀𑁒spec (PopEmptyishWinner v) _ front1 with "[$Howner₁ $Hdata_cslice₂ $Hwinner_steal]"); [lia.. | iFrameSteps |].
            iSteps.
          }

          iDestruct (prophet_multi۰full𑁒get _ front1 with "Hprophet_model") as "#Hprophet_full".
          iEval (rewrite Hpasts1 //=) in "Hprophet_full".
          destruct (prophss1 front1) as [| id_winner prophs]; first done.
          iDestruct "Hwinner" as "(:winner۰pending₂ !=)".

          iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
          iMod (model𑁒steal with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂) /=".
          iMod ("HP" with "[$Hmodel₁]") as "HP"; first iSteps.

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
          iMod (model𑁒empty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" $! None with "[$Hmodel₁ //]") as "HΦ".

          iSplitR "Howner₁ Hdata_cslice₂ HΦ".
          { iExists Emptyish. iFrameStep 7. iExists P. iSteps. }
          iIntros "!> {%- Hcap Hus Hbranch2}".

          wp۰apply+ (ws_deque_1٠pop₀𑁒spec PopEmptyishLoser _ front1 with "[$Howner₁ $Hdata_cslice₂]"); [lia.. | iFrameSteps |].
          iSteps.

      - iMod (owner𑁒update Stable (back - 1) data cap with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
        iEval (rewrite -assoc) in "Hdata1_cslice₁".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (model𑁒pop' with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some v) with "[$Hmodel₁ //]") as "HΦ".

        iAssert ⌜us !! 0 = Some v⌝%I as %Hus_lookup.
        { iDestruct (array۰cslice𑁒rotation𑁒right𑁒small₁' (back - 1) (length vs1) with "Hdata1_cslice₁") as "Hdata_cslice₁"; [simpl_length/=; lia.. |].
          iDestruct (array۰cslice𑁒agree with "Hdata_cslice₁ Hdata_cslice₂") as %<-.
          { simpl_length/=. lia. }
          rewrite /rotation drop_app_length //.
        }

        iSplitR "Howner₁ Hdata_cslice₂ HΦ".
        { iExists Nonempty. iFrameSteps.
          rewrite hd𑁒app //; first lia.
        }
        iIntros "!> {%- Hcap Hus Hback Hus_lookup}".

        wp۰apply+ (ws_deque_1٠pop₀𑁒spec (PopNonempty v) _ (back - 1) with "[$Howner₁ $Hdata_cslice₂]"); [lia.. | iFrameSteps |].
        iSteps.
    Qed.
  End ws_deque_1۰G.

  #[global] Opaque ws_deque_1۰inv.
  #[global] Opaque ws_deque_1۰model.
  #[global] Opaque ws_deque_1۰owner.
End base.

Require zoo_saturn.ws_deque_1__opaque.

Section ws_deque_1۰G.
  Context `{ws_deque_1۰G : WsDeque1G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition ws_deque_1۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ws_deque_1۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition ws_deque_1۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ws_deque_1۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition ws_deque_1۰owner t ws : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ws_deque_1۰owner γ ws.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Howner{_{}}
      )
    ".

  #[global] Instance ws_deque_1۰model𑁒timeless γ vs :
    Timeless (ws_deque_1۰model γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_deque_1۰owner𑁒timeless γ ws :
    Timeless (ws_deque_1۰owner γ ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_deque_1۰inv𑁒persistent t ι :
    Persistent (ws_deque_1۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma ws_deque_1۰model𑁒exclusive t vs1 vs2 :
    ws_deque_1۰model t vs1 -∗
    ws_deque_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_deque_1۰model𑁒exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma ws_deque_1۰owner𑁒exclusive t ws1 ws2 :
    ws_deque_1۰owner t ws1 -∗
    ws_deque_1۰owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_deque_1۰owner𑁒exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma ws_deque_1𑁒owner𑁒model γ ws vs :
    ws_deque_1۰owner γ ws -∗
    ws_deque_1۰model γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_deque_1𑁒owner𑁒model with "Howner_1 Hmodel_2").
  Qed.

  Lemma ws_deque_1٠create𑁒spec ι :
    {{{
      True
    }}}
      ws_deque_1٠create ()
    {{{
      t
    , RET t;
      ws_deque_1۰inv t ι ∗
      ws_deque_1۰model t [] ∗
      ws_deque_1۰owner t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.ws_deque_1٠create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel & Howner)".
    iMod (meta𑁒set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma ws_deque_1٠size𑁒spec t ι ws :
    <<<
      ws_deque_1۰inv t ι ∗
      ws_deque_1۰owner t ws
    | ∀∀ vs,
      ws_deque_1۰model t vs
    >>>
      ws_deque_1٠size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_deque_1۰model t vs
    | RET #(length vs);
      ws_deque_1۰owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_deque_1٠size𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_deque_1٠is_empty𑁒spec t ι ws :
    <<<
      ws_deque_1۰inv t ι ∗
      ws_deque_1۰owner t ws
    | ∀∀ vs,
      ws_deque_1۰model t vs
    >>>
      ws_deque_1٠is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_deque_1۰model t vs
    | RET #(bool_decide (vs = []%list));
      ws_deque_1۰owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_deque_1٠is_empty𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_deque_1٠push𑁒spec t ι ws v :
    <<<
      ws_deque_1۰inv t ι ∗
      ws_deque_1۰owner t ws
    | ∀∀ vs,
      ws_deque_1۰model t vs
    >>>
      ws_deque_1٠push t v @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_deque_1۰model t (vs ++ [v])
    | RET ();
      ws_deque_1۰owner t (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_deque_1٠push𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_deque_1٠steal𑁒spec t ι :
    <<<
      ws_deque_1۰inv t ι
    | ∀∀ vs,
      ws_deque_1۰model t vs
    >>>
      ws_deque_1٠steal t @ ↑ι
    <<<
      ws_deque_1۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.ws_deque_1٠steal𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_deque_1٠pop𑁒spec t ι ws :
    <<<
      ws_deque_1۰inv t ι ∗
      ws_deque_1۰owner t ws
    | ∀∀ vs,
      ws_deque_1۰model t vs
    >>>
      ws_deque_1٠pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_deque_1۰model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          ws_deque_1۰model t vs'
      end
    | RET o;
      ws_deque_1۰owner t ws'
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_deque_1٠pop𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1". 1: iSteps. iIntros "%o %ws' ($ & Ho)".
      iExists o, ws'. destruct o.
      all: iDecompose "Ho".
      all: iFrameSteps.
    }
  Qed.
End ws_deque_1۰G.

#[global] Opaque ws_deque_1۰inv.
#[global] Opaque ws_deque_1۰model.
#[global] Opaque ws_deque_1۰owner.
