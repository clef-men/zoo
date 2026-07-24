Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.function.
Require Import zoo.common.relations.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.base_logic.lib.auth_twins.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.base.
Require Import zoo.program_logic.identifier.
Require Import zoo.program_logic.prophet_identifier.
Require Import zoo.program_logic.prophet_multi.
Require Import zoo_std.domain.
Require Import zoo_std.inf_array.
Require Import zoo_std.option.
Require Export zoo_saturn.inf_ws_deque_1__code.
Require Import zoo_saturn.inf_ws_deque_1__types.
Require Import zoo.options.

Implicit Type front back : nat.
Implicit Type id : prophet_id.
Implicit Type v : val.
Implicit Type vs ws hist lhist : list val.
Implicit Type priv : nat → val.
Implicit Type past prophs : list prophet_identifier.(prophet_typed۰type).
Implicit Type pasts prophss : nat → list prophet_identifier.(prophet_typed۰type).

Variant state :=
  | Empty
  | Nonempty
  | Emptyish
  | Superempty.
Implicit Type state : state.

#[local] Instance state𑁒inhabited : Inhabited state :=
  populate Empty.

Variant stability :=
  | Stable
  | Unstable.
Implicit Type stable : stability.

#[local] Instance stability𑁒inhabited : Inhabited stability :=
  populate Stable.

Class InfWsDeque1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] inf_ws_deque_1۰G۰inf_array۰G :: InfArrayG Σ
  ; #[local] inf_ws_deque_1۰G۰prophet۰G :: ProphetMultiG Σ prophet_identifier
  ; #[local] inf_ws_deque_1۰G۰model۰G :: AuthTwinsG Σ (leibnizO (list val)) suffix
  ; #[local] inf_ws_deque_1۰G۰owner۰G :: TwinsG Σ (leibnizO (stability * nat * (nat → val)))
  ; #[local] inf_ws_deque_1۰G۰front۰G :: AuthNatMaxG Σ
  ; #[local] inf_ws_deque_1۰G۰history۰G :: MonoListG Σ val
  ; #[local] inf_ws_deque_1۰G۰winner۰G :: TwinsG Σ (natO * ▶ ∙)
  }.

Definition inf_ws_deque_1۰Σ :=
  #[inf_array۰Σ
  ; prophet_multi۰Σ prophet_identifier
  ; auth_twins۰Σ (leibnizO (list val)) suffix
  ; twins۰Σ (leibnizO (stability * nat * (nat → val)))
  ; auth_nat_max۰Σ
  ; mono_list۰Σ val
  ; twins۰Σ (natO * ▶ ∙)
  ].
#[global] Instance subG𑁒inf_ws_deque_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG inf_ws_deque_1۰Σ Σ →
  InfWsDeque1G Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section inf_ws_deque_1۰G.
    Context `{inf_ws_deque_1۰G : InfWsDeque1G Σ}.

    Implicit Type t : location.
    Implicit Type P : iProp Σ.

    Record inf_ws_deque_1۰name :=
      { inf_ws_deque_1۰name۰data : val
      ; inf_ws_deque_1۰name۰inv : namespace
      ; inf_ws_deque_1۰name۰prophet : prophet_id
      ; inf_ws_deque_1۰name۰prophet_name : prophet_multi۰name
      ; inf_ws_deque_1۰name۰model : auth_twins۰name
      ; inf_ws_deque_1۰name۰owner : gname
      ; inf_ws_deque_1۰name۰front : gname
      ; inf_ws_deque_1۰name۰history : gname
      ; inf_ws_deque_1۰name۰winner : gname
      }.
    Implicit Type γ : inf_ws_deque_1۰name.

    #[global] Instance inf_ws_deque_1۰name𑁒eq_dec : EqDecision inf_ws_deque_1۰name :=
      ltac:(solve_decision).
    #[global] Instance inf_ws_deque_1۰name𑁒countable :
      Countable inf_ws_deque_1۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      auth_twins۰twin₁ _ γ_model vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(inf_ws_deque_1۰name۰model).
    #[local] Definition model₂' γ_model vs :=
      auth_twins۰twin₂ _ γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(inf_ws_deque_1۰name۰model).

    #[local] Definition owner₁' γ_owner γ_model stable back priv ws : iProp Σ :=
      twins۰twin₁ (twins۰G := inf_ws_deque_1۰G۰owner۰G) γ_owner (DfracOwn 1) (stable, back, priv) ∗
      auth_twins۰auth _ γ_model ws.
    #[local] Definition owner₁ γ :=
      owner₁' γ.(inf_ws_deque_1۰name۰owner) γ.(inf_ws_deque_1۰name۰model).
    #[local] Instance : CustomIpat "owner₁" :=
      " ( Howner₁{_{}}
        & Hmodel_auth{_{}}
        )
      ".
    #[local] Definition owner₂' γ_owner stable back priv :=
      twins۰twin₂ (twins۰G := inf_ws_deque_1۰G۰owner۰G) γ_owner (stable, back, priv).
    #[local] Definition owner₂ γ :=
      owner₂' γ.(inf_ws_deque_1۰name۰owner).

    #[local] Definition front۰auth' γ_front :=
      auth_nat_max۰auth γ_front (DfracOwn 1).
    #[local] Definition front۰auth γ :=
      front۰auth' γ.(inf_ws_deque_1۰name۰front).
    #[local] Definition front۰lb γ :=
      auth_nat_max۰lb γ.(inf_ws_deque_1۰name۰front).

    #[local] Definition history۰auth' γ_history :=
      mono_list۰auth γ_history (DfracOwn 1).
    #[local] Definition history۰auth γ :=
      history۰auth' γ.(inf_ws_deque_1۰name۰history).
    #[local] Definition history۰at γ :=
      mono_list۰at γ.(inf_ws_deque_1۰name۰history).

    #[local] Definition winner۰pop' γ_winner front P : iProp Σ :=
      twins۰twin₁ γ_winner (DfracOwn 1) (front, Next P).
    #[local] Definition winner۰pop γ :=
      winner۰pop' γ.(inf_ws_deque_1۰name۰winner).
    #[local] Definition winner۰steal' γ_winner front P :=
      twins۰twin₂ γ_winner (front, Next P).
    #[local] Definition winner۰steal γ :=
      winner۰steal' γ.(inf_ws_deque_1۰name۰winner).
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
      }> @ ⊤ ∖ ↑γ.(inf_ws_deque_1۰name۰inv), ∅ <{
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

    #[local] Definition inv۰state۰empty γ stable front back hist lhist : iProp Σ :=
      ⌜stable = Stable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜lhist = hist⌝ ∗
      ⌜length hist = front⌝ ∗
      winner γ.
    #[local] Instance : CustomIpat "inv۰state۰empty" :=
      " ( { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}->
        & {>;}%Hhist{}
        & Hwinner
        )
      ".
    #[local] Definition inv۰state۰nonempty γ stable front back hist lhist vs prophs : iProp Σ :=
      ⌜stable = Stable⌝ ∗
      ⌜front < back⌝ ∗
      ⌜lhist = hist ++ take 1 vs⌝ ∗
      ⌜length hist = front⌝ ∗
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
        & {>;}->
        & {>;}%Hhist{}
        & Hwinner
        )
      ".
    #[local] Definition inv۰state۰nonempty۰steal γ state stable front back hist lhist vs prophs P : iProp Σ :=
      ⌜state = Nonempty⌝ ∗
      ⌜stable = Stable⌝ ∗
      ⌜front < back⌝ ∗
      ⌜lhist = hist ++ take 1 vs⌝ ∗
      ⌜length hist = front⌝ ∗
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
        & {>;}->
        & {>;}%Hhist{}
        & (:winner۰pending₁)
        )
      ".
    #[local] Definition inv۰state۰emptyish γ stable front back hist lhist : iProp Σ :=
      ∃ P,
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜lhist = hist⌝ ∗
      ⌜length hist = ˖front⌝ ∗
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
        & {>;}->
        & {>;}%Hhist{}
        & Hwinner
        )
      ".
    #[local] Definition inv۰state۰emptyish۰pop γ state stable front back hist lhist P : iProp Σ :=
      ⌜state = Emptyish⌝ ∗
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜lhist = hist⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      winner۰pop γ front P.
    #[local] Instance : CustomIpat "inv۰state۰emptyish۰pop" :=
      " ( {>;}->
        & { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}->
        & {>;}%Hhist{}
        & Hwinner_pop
        )
      ".
    #[local] Definition inv۰state۰emptyish۰steal γ state stable front back hist lhist P : iProp Σ :=
      ⌜state = Emptyish⌝ ∗
      ⌜stable = Unstable⌝ ∗
      ⌜front = back⌝ ∗
      ⌜lhist = hist⌝ ∗
      ⌜length hist = ˖front⌝ ∗
      winner۰linearized γ front P.
    #[local] Instance : CustomIpat "inv۰state۰emptyish۰steal" :=
      " ( {>;}->
        & { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}->
        & {>;}%Hhist{}
        & (:winner۰linearized)
        )
      ".
    #[local] Definition inv۰state۰superempty γ stable front back hist lhist : iProp Σ :=
      ⌜stable = Unstable⌝ ∗
      ⌜front = ˖back⌝ ∗
      ⌜lhist = hist⌝ ∗
      ⌜length hist = front⌝ ∗
      winner γ.
    #[local] Instance : CustomIpat "inv۰state۰superempty" :=
      " ( { {lazy}{>}%
          ; {lazy}%
          ; {>}->
          ; ->
          }
        & {>;}->
        & {>;}->
        & {>;}%Hhist{}
        & Hwinner
        )
      ".
    #[local] Definition inv۰state γ state stable front back hist lhist vs prophs : iProp Σ :=
      match state with
      | Empty =>
          inv۰state۰empty γ stable front back hist lhist
      | Nonempty =>
          inv۰state۰nonempty γ stable front back hist lhist vs prophs
      | Emptyish =>
          inv۰state۰emptyish γ stable front back hist lhist
      | Superempty =>
          inv۰state۰superempty γ stable front back hist lhist
      end.

    #[local] Definition inv۰inner t γ : iProp Σ :=
      ∃ state stable front back hist lhist vs priv pasts prophss,
      t.[front] ↦ #front ∗
      t.[back] ↦ #back ∗
      owner₂ γ stable back priv ∗
      front۰auth γ front ∗
      ⌜0 < front⌝ ∗
      model₂ γ vs ∗
      ⌜length vs = back - front⌝ ∗
      inf_array۰model' γ.(inf_ws_deque_1۰name۰data) (hist ++ vs) priv ∗
      history۰auth γ lhist ∗
      prophet_multi۰model prophet_identifier γ.(inf_ws_deque_1۰name۰prophet) γ.(inf_ws_deque_1۰name۰prophet_name) pasts prophss ∗
      ⌜∀ i, front ≤ i → pasts i = []⌝ ∗
      inv۰state γ state stable front back hist lhist vs (prophss front).
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %state{}
        & %stable{}
        & %front{}
        & %back{}
        & %hist{}
        & %lhist{}
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
        & >Hdata_model
        & >Hhistory_auth
        & >Hprophet_model
        & >%Hpasts{}
        & Hstate
        )
      ".
    #[local] Definition inv' t γ : iProp Σ :=
      t.[data] ↦□ γ.(inf_ws_deque_1۰name۰data) ∗
      t.[proph] ↦□ #γ.(inf_ws_deque_1۰name۰prophet) ∗
      inf_array۰inv γ.(inf_ws_deque_1۰name۰data) ∗
      inv γ.(inf_ws_deque_1۰name۰inv) (inv۰inner t γ).
    #[local] Instance : CustomIpat "inv'" :=
      " ( #Ht_data
        & #Ht_proph
        & #Hdata_inv
        & #Hinv
        )
      ".
    Definition inf_ws_deque_1۰inv t γ ι : iProp Σ :=
      ⌜ι = γ.(inf_ws_deque_1۰name۰inv)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & (:inv')
        )
      ".

    Definition inf_ws_deque_1۰model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    Definition inf_ws_deque_1۰owner γ ws : iProp Σ :=
      ∃ back priv,
      owner₁ γ Stable back priv ws.
    #[local] Instance : CustomIpat "owner" :=
      " ( %back{}
        & %priv{}
        & Howner₁{_{}}
        )
      ".

    #[global] Instance inf_ws_deque_1۰model𑁒timeless γ vs :
      Timeless (inf_ws_deque_1۰model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance inf_ws_deque_1۰owner𑁒timeless γ ws :
      Timeless (inf_ws_deque_1۰owner γ ws).
    Proof.
      apply _.
    Qed.

    #[global] Instance inf_ws_deque_1۰inv𑁒persistent t γ ι :
      Persistent (inf_ws_deque_1۰inv t γ ι).
    Proof.
      apply _.
    Qed.

    #[local] Lemma model𑁒owner𑁒alloc :
      ⊢ |==>
        ∃ γ_model γ_owner,
        model₁' γ_model [] ∗
        model₂' γ_model [] ∗
        owner₁' γ_owner γ_model Stable 1 (λ _, ()%V) [] ∗
        owner₂' γ_owner Stable 1 (λ _, ()%V).
    Proof.
      iMod (auth_twins𑁒alloc _ (auth_twins۰G := inf_ws_deque_1۰G۰model۰G)) as "(%γ_model & Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iMod (twins𑁒alloc' (twins۰G := inf_ws_deque_1۰G۰owner۰G)) as "(%γ_owner & Howner₁ & Howner₂)".
      iFrameSteps.
    Qed.
    #[local] Lemma model₁𑁒valid γ stable back priv ws vs :
      owner₁ γ stable back priv ws -∗
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
    #[local] Lemma model۰owner₁𑁒agree γ stable back priv ws vs1 vs2 :
      owner₁ γ stable back priv ws -∗
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
    #[local] Lemma model𑁒empty {γ stable back priv ws vs1 vs2} :
      owner₁ γ stable back priv ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back priv [] ∗
        model₁ γ [] ∗
        model₂ γ [].
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twins𑁒update𑁒auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iSteps.
    Qed.
    #[local] Lemma model𑁒push {γ stable back priv ws vs1 vs2} v :
      owner₁ γ stable back priv ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back priv (vs1 ++ [v]) ∗
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
    #[local] Lemma model𑁒pop γ stable back priv ws vs1 vs2 :
      owner₁ γ stable back priv ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back priv (removelast vs1) ∗
        model₁ γ (removelast vs1) ∗
        model₂ γ (removelast vs1).
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twins𑁒update𑁒auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
      iSteps.
    Qed.
    #[local] Lemma model𑁒pop' γ stable back priv ws vs1 v vs2 :
      owner₁ γ stable back priv ws -∗
      model₁ γ (vs1 ++ [v]) -∗
      model₂ γ vs2 ==∗
        owner₁ γ stable back priv vs1 ∗
        model₁ γ vs1 ∗
        model₂ γ vs1.
    Proof.
      rewrite -{2 3 4}(removelast_last vs1 v).
      apply model𑁒pop.
    Qed.

    #[local] Lemma owner₁𑁒exclusive γ stable1 back1 priv1 ws1 stable2 back2 priv2 ws2 :
      owner₁ γ stable1 back1 priv1 ws1 -∗
      owner₁ γ stable2 back2 priv2 ws2 -∗
      False.
    Proof.
      iIntros "(:owner₁ =1) (:owner₁ =2)".
      iApply (twins۰twin₁𑁒exclusive with "Howner₁_1 Howner₁_2").
    Qed.
    #[local] Lemma owner𑁒agree γ stable1 back1 priv1 ws stable2 back2 priv2 :
      owner₁ γ stable1 back1 priv1 ws -∗
      owner₂ γ stable2 back2 priv2 -∗
        ⌜stable1 = stable2⌝ ∗
        ⌜back1 = back2⌝ ∗
        ⌜priv1 = priv2⌝.
    Proof.
      iIntros "(:owner₁) Howner₂".
      iDestruct (twins𑁒agree𑁒L with "Howner₁ Howner₂") as %[= <- <- <-].
      iSteps.
    Qed.
    #[local] Lemma owner₁𑁒update γ stable back priv ws vs :
      owner₁ γ stable back priv ws -∗
      model₁ γ vs -∗
      model₂ γ vs ==∗
        owner₁ γ stable back priv vs ∗
        model₁ γ vs ∗
        model₂ γ vs.
    Proof.
      iIntros "(:owner₁) Hmodel₁ Hmodel₂".
      iMod (auth_twins𑁒update𑁒auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "($ & $ & $)".
      iSteps.
    Qed.
    #[local] Lemma owner𑁒update {γ stable1 back1 priv1 ws stable2 back2 priv2} stable back priv :
      owner₁ γ stable1 back1 priv1 ws -∗
      owner₂ γ stable2 back2 priv2 ==∗
        owner₁ γ stable back priv ws ∗
        owner₂ γ stable back priv.
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
        winner۰pop' γ_winner 1 True ∗
        winner۰steal' γ_winner 1 True.
    Proof.
      apply twins𑁒alloc'.
    Qed.
    #[local] Lemma winner۰pop𑁒exclusive γ front1 P1 front2 P2 :
      winner۰pop γ front1 P1 -∗
      winner۰pop γ front2 P2 -∗
      False.
    Proof.
      apply twins۰twin₁𑁒exclusive.
    Qed.
    #[local] Lemma winner۰pop𑁒exclusive' γ front P :
      winner۰pop γ front P -∗
      winner γ -∗
      False.
    Proof.
      iIntros "Hwinner_pop_1 (:winner =2)".
      iApply (winner۰pop𑁒exclusive with "Hwinner_pop_1 Hwinner_pop_2").
    Qed.
    #[local] Lemma winner۰steal𑁒exclusive γ front1 P1 front2 P2 :
      winner۰steal γ front1 P1 -∗
      winner۰steal γ front2 P2 -∗
      False.
    Proof.
      apply twins۰twin₂𑁒exclusive.
    Qed.
    #[local] Lemma winner۰steal𑁒exclusive' γ front P :
      winner۰steal γ front P -∗
      winner γ -∗
      False.
    Proof.
      iIntros "Hwinner_steal_1 (:winner =2)".
      iApply (winner۰steal𑁒exclusive with "Hwinner_steal_1 Hwinner_steal_2").
    Qed.
    #[local] Lemma winner𑁒agree γ front1 P1 front2 P2 :
      winner۰pop γ front1 P1 -∗
      winner۰steal γ front2 P2 -∗
        ⌜front1 = front2⌝ ∗
        ▷ (P1 ≡ P2).
    Proof.
      iIntros "Hwinner_pop Hwinner_steal".
      iDestruct (twins𑁒agree with "Hwinner_pop Hwinner_steal") as "#Heq".
      rewrite prod_equivI /= discrete_eq_1.
      iDestruct "Heq" as "($ & $)".
    Qed.
    #[local] Lemma winner𑁒update {γ front1 P1 front2 P2} front P :
      winner۰pop γ front1 P1 -∗
      winner۰steal γ front2 P2 ==∗
        winner۰pop γ front P ∗
        winner۰steal γ front P.
    Proof.
      apply twins𑁒update.
    Qed.

    Opaque owner₁'.

    Lemma inf_ws_deque_1۰model𑁒exclusive γ vs1 vs2 :
      inf_ws_deque_1۰model γ vs1 -∗
      inf_ws_deque_1۰model γ vs2 -∗
      False.
    Proof.
      apply model₁𑁒exclusive.
    Qed.

    Lemma inf_ws_deque_1۰owner𑁒exclusive γ ws1 ws2 :
      inf_ws_deque_1۰owner γ ws1 -∗
      inf_ws_deque_1۰owner γ ws2 -∗
      False.
    Proof.
      iIntros "(:owner =1) (:owner =2)".
      iApply (owner₁𑁒exclusive with "Howner₁_1 Howner₁_2").
    Qed.
    Lemma inf_ws_deque_1۰owner𑁒model γ ws vs :
      inf_ws_deque_1۰owner γ ws -∗
      inf_ws_deque_1۰model γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:owner =1) (:model =2)".
      iApply (model₁𑁒valid with "Howner₁_1 Hmodel₁_2").
    Qed.

    #[local] Lemma inv۰state𑁒Stable γ state front back hist lhist vs prophs :
      length vs = back - front →
      inv۰state γ state Stable front back hist lhist vs prophs ⊢
        ⌜state = Empty ∨ state = Nonempty⌝ ∗
        ⌜front ≤ back⌝ ∗
        ⌜length (hist ++ vs) = back⌝.
    Proof.
      iIntros "%Hvs Hstate".
      rewrite length_app.
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty lazy=)".
        iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰nonempty lazy=)".
        iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰superempty lazy=)". done.
    Qed.
    #[local] Lemma inv۰state𑁒Unstable γ state front back hist lhist vs prophs :
      inv۰state γ state Unstable front back hist lhist vs prophs ⊢
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
    #[local] Lemma inv۰state𑁒Nonempty γ state stable front back hist lhist vs prophs :
      front < back →
      inv۰state γ state stable front back hist lhist vs prophs ⊢
      ⌜state = Nonempty⌝.
    Proof.
      iIntros "% Hstate".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty)". lia.
      - done.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish)". lia.
      - iDestruct "Hstate" as "(:inv۰state۰superempty)". lia.
    Qed.
    #[local] Lemma inv۰state𑁒Superempty γ state front back hist lhist vs prophs :
      back < front →
      inv۰state γ state Unstable front back hist lhist vs prophs -∗
      ⌜state = Superempty⌝.
    Proof.
      iIntros "% Hstate".
      destruct state.
      - iDestruct "Hstate" as "(:inv۰state۰empty lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰nonempty lazy=)". done.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish lazy=)". lia.
      - done.
    Qed.
    #[local] Lemma inv۰state𑁒winner۰pop γ state stable front1 back hist lhist vs prophs front2 P :
      inv۰state γ state stable front1 back hist lhist vs prophs -∗
      winner۰pop γ front2 P -∗
        ∃ P_,
        ⌜front1 = front2⌝ ∗
        ▷ (P ≡ P_) ∗
        ( inv۰state۰nonempty۰steal γ state stable front2 back hist lhist vs prophs P_
        ∨ inv۰state۰emptyish۰steal γ state stable front2 back hist lhist P_
        ) ∗
        winner۰pop γ front2 P.
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
          iDestruct (winner𑁒agree with "Hwinner_pop Hwinner_steal") as "#(<- & $)".
          iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰emptyish)".
        iDestruct "Hwinner" as "[Hwinner_pop_ | (:winner۰linearized)]".
        + iDestruct (winner۰pop𑁒exclusive with "Hwinner_pop Hwinner_pop_") as %[].
        + iDestruct (winner𑁒agree with "Hwinner_pop Hwinner_steal") as "#(<- & $)".
          iSteps.
      - iDestruct "Hstate" as "(:inv۰state۰superempty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰pop𑁒exclusive with "Hwinner_pop Hwinner_pop_3") as %[].
    Qed.
    #[local] Lemma inv۰state𑁒winner۰steal γ state stable front1 back hist lhist vs prophs front2 P :
      inv۰state γ state stable front1 back hist lhist vs prophs -∗
      winner۰steal γ front2 P -∗
        ∃ P_,
        ⌜front1 = front2⌝ ∗
        ▷ (P_ ≡ P) ∗
        inv۰state۰emptyish۰pop γ state stable front2 back hist lhist P_ ∗
        winner۰steal γ front2 P.
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
        iDestruct "Hwinner" as "[Hwinner_pop | (:winner۰linearized !=)]".
        + iDestruct (winner𑁒agree with "Hwinner_pop Hwinner_steal") as "#(<- & $)".
          iSteps.
        + iDestruct (winner۰steal𑁒exclusive with "Hwinner_steal Hwinner_steal_") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰superempty)".
        iDestruct "Hwinner" as "(:winner =3)".
        iDestruct (winner۰steal𑁒exclusive with "Hwinner_steal Hwinner_steal_3") as %[].
    Qed.

    Lemma inf_ws_deque_1٠create𑁒spec ι :
      {{{
        True
      }}}
        inf_ws_deque_1٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        inf_ws_deque_1۰inv t γ ι ∗
        inf_ws_deque_1۰model γ [] ∗
        inf_ws_deque_1۰owner γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.

      wp۰apply (prophet_multi𑁒wp𑁒proph with "[//]") as (pid γ_prophet prophss) "Hprophet_model".

      wp۰apply (inf_array٠create𑁒spec with "[//]") as (data) "(#Hdata_inv & Hdata_model)".
      iDestruct (inf_array۰model𑁒to𑁒model'𑁒constant 1 with "Hdata_model") as "Hdata_model".

      wp۰block t as "Hmeta" "(Ht_front & Ht_back & Ht_data & Ht_proph & _)".
      iMod (pointsto𑁒persist with "Ht_data") as "#Ht_data".
      iMod (pointsto𑁒persist with "Ht_proph") as "#Ht_proph".

      iMod model𑁒owner𑁒alloc as "(%γ_model & %γ_owner & Hmodel₁ & Hmodel₂ & Howner₁ & Howner₂)".
      iMod front𑁒alloc as "(%γ_front & Hfront_auth)".
      iMod history𑁒alloc as "(%γ_history & Hhist_auth)".
      iMod winner𑁒alloc as "(%γ_winner & Hwinner_pop & Hwinner_steal)".

      set γ :=
        {|inf_ws_deque_1۰name۰data := data
        ; inf_ws_deque_1۰name۰inv := ι
        ; inf_ws_deque_1۰name۰prophet := pid
        ; inf_ws_deque_1۰name۰prophet_name := γ_prophet
        ; inf_ws_deque_1۰name۰model := γ_model
        ; inf_ws_deque_1۰name۰owner := γ_owner
        ; inf_ws_deque_1۰name۰front := γ_front
        ; inf_ws_deque_1۰name۰history := γ_history
        ; inf_ws_deque_1۰name۰winner := γ_winner
        |}.

      iApply ("HΦ" $! t γ).
      iFrame "#∗". iStep.
      iApply inv_alloc.
      iExists Empty, Stable, 1, 1, [()%V], [inhabitant], [], (λ _, ()%V), (λ _, []), prophss. iFrameSteps.
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
      iFrameSteps.
    Qed.
    #[local] Lemma front𑁒spec𑁒owner𑁒Stable t γ back priv ws :
      {{{
        inv' t γ ∗
        owner₁ γ Stable back priv ws
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
        owner₁ γ Stable back priv ws ∗
        front۰lb γ front ∗
        ⌜front ≤ back⌝
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".
      iDestruct (inv۰state𑁒Stable with "Hstate") as "#(_ & %)"; first done.
      iFrameSteps.
    Qed.
    #[local] Lemma front𑁒spec𑁒owner𑁒Unstable t γ back priv ws :
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back priv ws
      }}}
        (#t).{front}
      {{{
        front
      , RET #front;
        owner₁ γ Unstable back priv ws ∗
        front۰lb γ front ∗
        ⌜front = back ∨ front = ˖back⌝
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".
      iDestruct (inv۰state𑁒Unstable with "Hstate") as "#(_ & %)".
      iFrameSteps.
    Qed.
    #[local] Lemma front𑁒spec𑁒Superempty t γ back priv ws front :
      back < front →
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back priv ws ∗
        front۰lb γ front
      }}}
        (#t).{front}
      {{{
        RET #front;
        owner₁ γ Unstable back priv ws
      }}}.
    Proof.
      iIntros "% %Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰state𑁒Superempty with "Hstate") as %->; first lia.
      iDestruct "Hstate" as "(:inv۰state۰superempty =1 lazy=)".
      iSplitR "Howner₁ HΦ". { iExists Superempty. iFrameSteps. }
      replace ˖back with front by lia.
      iSteps.
    Qed.
    #[local] Lemma front𑁒spec𑁒winner۰steal t γ front P :
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
      { iDestruct (inv۰state𑁒winner۰steal with "Hstate Hwinner_steal") as "(%P_ & $ & _)". }

      iFrameSteps.
    Qed.

    #[local] Lemma back𑁒spec t γ stable back priv ws :
      {{{
        inv' t γ ∗
        owner₁ γ stable back priv ws
      }}}
        (#t).{back}
      {{{
        RET #back;
        owner₁ γ stable back priv ws
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as "(<- & <- & <-)".
      iFrameSteps.
    Qed.

    #[local] Lemma set_back𑁒spec𑁒Superempty t γ back priv ws front (back' : Z) :
      back < front →
      back' = ˖back →
      {{{
        inv' t γ ∗
        owner₁ γ Unstable back priv ws ∗
        front۰lb γ front
      }}}
        #t <-{back} #back'
      {{{
        RET ();
        owner₁ γ Stable ˖back priv ws
      }}}.
    Proof.
      iIntros (? ->) "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰store.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      iMod (owner𑁒update Stable ˖back priv with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰state𑁒Superempty with "Hstate") as %->; first lia.
      iDestruct "Hstate" as "(:inv۰state۰superempty =1 lazy=)".
      iSplitR "Howner₁ HΦ". { iExists Empty. iFrameSteps. }
      iSteps.
    Qed.

    #[local] Lemma inf_array٠get𑁒spec𑁒history t γ (i : nat) (i_ : Z) v :
      i_ = i →
      {{{
        inv' t γ ∗
        history۰at γ i v
      }}}
        inf_array٠get γ.(inf_ws_deque_1۰name۰data) #i_
      {{{
        RET v;
        True
      }}}.
    Proof.
      iIntros (->) "%Φ ((:inv') & #Hhistory_at) HΦ".

      iApply wp𑁒fupd.
      awp۰apply (inf_array٠get𑁒spec' with "Hdata_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner)".
      iAaccIntro with "Hdata_model"; first iStepFrameSteps. iIntros "Hdata_model".

      iAssert (◇ ⌜(hist ++ vs) !! i = Some v⌝)%I as "#>%Hlookup".
      { iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at") as %Hlookup.
        destruct state.
        - iDestruct "Hstate" as "(:inv۰state۰empty >)".
          iPureIntro.
          apply lookup_app_l_Some; first done.
        - iDestruct "Hstate" as "(:inv۰state۰nonempty >)".
          iPureIntro.
          destruct vs as [| w vs]; first naive_solver lia.
          rewrite (assoc (++) hist [w]).
          apply lookup_app_l_Some; first done.
        - iDestruct "Hstate" as "(:inv۰state۰emptyish >)".
          iPureIntro.
          apply lookup_app_l_Some; first done.
        - iDestruct "Hstate" as "(:inv۰state۰superempty >)".
          iPureIntro.
          apply lookup_app_l_Some; first done.
      }

      iSplitL. { iFrameSteps. }
      iIntros "!> H£ HΦ".

      rewrite Nat2Z.id decide_True.
      { eauto using lookup_lt_Some. }
      erewrite list_lookup_total_correct => //.
      iApply (lc_fupd_elim_later with "H£ HΦ [//]").
    Qed.
    #[local] Lemma inf_array٠get𑁒spec𑁒owner t γ back (back_ : Z) priv ws v :
      back_ = back →
      priv 0 = v →
      {{{
        inv' t γ ∗
        owner₁ γ Stable back priv ws
      }}}
        inf_array٠get γ.(inf_ws_deque_1۰name۰data) #back_
      {{{
        RET v;
        owner₁ γ Stable back priv ws
      }}}.
    Proof.
      iIntros (->) "%Hpriv %Φ ((:inv') & Howner₁) HΦ".

      iApply wp𑁒fupd.
      awp۰apply (inf_array٠get𑁒spec' with "Hdata_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =1)".
      iAaccIntro with "Hdata_model"; first iStepFrameSteps. iIntros "Hdata_model".
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      iDestruct (inv۰state𑁒Stable with "Hstate") as "#(_ & _ & >->)"; first done.
      iSplitR "Howner₁". { iFrameSteps. }
      iIntros "!> H£ HΦ".

      rewrite Nat2Z.id Nat.sub_diag Hpriv decide_False; first lia.
      iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
      iSteps.
    Qed.

    #[local] Lemma inf_array٠set𑁒spec𑁒owner t γ back priv ws v :
      {{{
        inv' t γ ∗
        owner₁ γ Stable back priv ws
      }}}
        inf_array٠set γ.(inf_ws_deque_1۰name۰data) #back v
      {{{
        RET ();
        owner₁ γ Stable back (<[0 := v]> priv) ws
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁) HΦ".

      iApply wp𑁒fupd.
      awp۰apply (inf_array٠set𑁒spec' with "Hdata_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      iAaccIntro with "Hdata_model"; first iStepFrameSteps. iIntros "Hdata_model".
      iDestruct (inv۰state𑁒Stable with "Hstate") as "#(_ & _ & >->)"; first done.
      rewrite Nat2Z.id Nat.sub_diag decide_False; first lia.
      iMod (owner𑁒update Stable back (<[0 := v]> priv) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iSplitR "Howner₁". { iFrameSteps. }
      iIntros "!> H£ HΦ".

      iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
      iSteps.
    Qed.

    #[local] Lemma resolve𑁒spec𑁒loser₁ t γ front1 front2 id :
      front1 < front2 →
      {{{
        inv' t γ ∗
        front۰lb γ front2
      }}}
        Resolve (CAS (#t).[front]%V #front1 #(front1 + 1)) #γ.(inf_ws_deque_1۰name۰prophet) (#front1, #id)%V
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
        prophet_multi۰full prophet_identifier γ.(inf_ws_deque_1۰name۰prophet_name) front prophs0
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(inf_ws_deque_1۰name۰prophet) (#front, #id)%V
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
    #[local] Lemma resolve𑁒spec𑁒winner𑁒pop t γ front P id :
      {{{
        inv' t γ ∗
        winner۰pop γ front P
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(inf_ws_deque_1۰name۰prophet) (#front, #id)%V
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
      iDestruct (inv۰state𑁒winner۰pop with "Hstate Hwinner_pop") as "(%P_ & -> & #Heq & Hstate & Hwinner_pop)".
      rewrite Hprophss1.
      destruct b; zoo_simplify in Hcas; last congruence.
      iMod (front𑁒update with "Hfront_auth") as "Hfront_auth".
      iDestruct "Hstate" as "[(:inv۰state۰nonempty۰steal =1) | (:inv۰state۰emptyish۰steal =1)]".

      - destruct vs1 as [| v1 vs1] => /=; first naive_solver lia.
        iDestruct (history۰at𑁒get front with "Hhistory_auth") as "#Hhistory_at"; first done.

        iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model𑁒steal with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂) /=".
        iMod ("HP" with "[$Hmodel₁ $Hhistory_at //]") as "HP".

        iSplitR "HP HΦ".
        { rewrite (assoc _ _ [_]).
          destruct_decide (˖front = back1) as <- | ?.

          - simpl in Hvs1.
            iExists Empty. iFrameSteps; iPureIntro.
            + intros.
              rewrite fn_lookup_alter_ne; first lia.
              apply Hpasts1; first lia.
            + simpl_length/=. lia.

          - destruct vs1 as [| v2 vs1] => /=; first naive_solver lia.
            simpl in Hvs1.
            iMod (history𑁒update _ v2 with "Hhistory_auth") as "(Hhistory_auth & _)"; first done.
            iExists Nonempty. iFrameSteps; iPureIntro.
            + intros.
              rewrite fn_lookup_alter_ne; first lia.
              apply Hpasts1; first lia.
            + simpl_length/=. lia.
        }
        iIntros "!> {%}".

        iApply "HΦ". iModIntro.
        iRewrite "Heq" => //.

      - iSplitR "HP HΦ".
        { iExists Superempty. iFrameSteps. iPureIntro.
          intros.
          rewrite fn_lookup_alter_ne; first lia.
          apply Hpasts1; first lia.
        }
        iIntros "!> {%}".

        iApply "HΦ". iModIntro.
        iRewrite "Heq" => //.
    Qed.
    #[local] Lemma resolve𑁒spec𑁒winner𑁒steal t γ front P id :
      {{{
        inv' t γ ∗
        winner۰steal γ front P
      }}}
        Resolve (CAS (#t).[front]%V #front #(front + 1)) #γ.(inf_ws_deque_1۰name۰prophet) (#front, #id)%V
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
      iSplitR "HΦ".
      { iExists Superempty. iFrameSteps. iPureIntro.
        intros.
        rewrite fn_lookup_alter_ne; first lia.
        apply Hpasts1; first lia.
      }
      iSteps.
    Qed.
    #[local] Lemma resolve𑁒spec𑁒Empty t γ back priv ws id :
      {{{
        inv' t γ ∗
        owner₁ γ Stable back priv ws ∗
        front۰lb γ back
      }}}
        Resolve (CAS (#t).[front]%V #back #(back + 1)) #γ.(inf_ws_deque_1۰name۰prophet) (#back, #id)%V
      {{{
        RET true;
        owner₁ γ Unstable back (priv ∘ S) ws ∗
        front۰lb γ ˖back ∗
        history۰at γ back (priv 0)
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & Howner₁ & #Hfront_lb) HΦ".

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
      wp۰apply (wp𑁒cas𑁒nobranch' with "Ht_front") as (b) "%Hcas Ht_front".
      iStep. iIntros "%prophs %Hprophss1 Hprophet_model".
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb") as %?.
      iDestruct (inv۰state𑁒Stable with "Hstate") as "#([-> | ->] & _)"; first done.

      - iDestruct "Hstate" as "(:inv۰state۰empty =1 lazy=)".
        assert (length vs1 = 0) as ->%nil_length_inv by lia.
        destruct b; zoo_simplify in Hcas; last lia.

        iMod (front𑁒update with "Hfront_auth") as "Hfront_auth".
        iClear "Hfront_lb". iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".
        iMod (history𑁒update _ (priv 0) with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)"; first done.
        iMod (owner𑁒update Unstable (length hist1) (priv ∘ S) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

        iDestruct (inf_array۰model'𑁒shift𑁒l' with "Hdata_model") as "Hdata_model".
        iEval (rewrite app_nil_r -(app_nil_r (hist1 ++ [priv 0]))) in "Hdata_model".

        iSplitR "Howner₁ HΦ".
        { iExists Superempty. iFrameSteps; iPureIntro.
          - intros.
            rewrite fn_lookup_alter_ne; first lia.
            apply Hpasts1; first lia.
          - simpl_length/=. lia.
        }
        rewrite Hhist1. iSteps.

      - iDestruct "Hstate" as "(:inv۰state۰nonempty =1 lazy=)".
        exfalso. lia.
    Qed.

    Lemma inf_ws_deque_1٠size𑁒spec t γ ι ws :
      <<<
        inf_ws_deque_1۰inv t γ ι ∗
        inf_ws_deque_1۰owner γ ws
      | ∀∀ vs,
        inf_ws_deque_1۰model γ vs
      >>>
        inf_ws_deque_1٠size #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        inf_ws_deque_1۰model γ vs
      | RET #(length vs);
        inf_ws_deque_1۰owner γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      wp۰rec.

      wp۰bind (_.{front})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      iDestruct (inv۰state𑁒Stable with "Hstate") as %(_ & Hback & _); first done.

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
      iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
      iMod (owner₁𑁒update with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁ //]") as "HΦ".

      iSplitR "Howner₁ HΦ". { iFrameSteps. }
      iIntros "!> {%- Hvs1 Hback}".

      wp۰apply (back𑁒spec with "[$]") as "Howner₁".
      wp۰pures.

      replace (⁺back - ⁺front1)%Z with ⁺(length vs) by lia.
      iSteps.
    Qed.

    Lemma inf_ws_deque_1٠is_empty𑁒spec t γ ι ws :
      <<<
        inf_ws_deque_1۰inv t γ ι ∗
        inf_ws_deque_1۰owner γ ws
      | ∀∀ vs,
        inf_ws_deque_1۰model γ vs
      >>>
        inf_ws_deque_1٠is_empty #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        inf_ws_deque_1۰model γ vs
      | RET #(bool_decide (vs = []%list));
        inf_ws_deque_1۰owner γ vs
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & Howner) HΦ".

      wp۰rec.
      wp۰apply (inf_ws_deque_1٠size𑁒spec with "[$]").
      iApply (atomic_update𑁒wand with "HΦ"). iIntros "%vs HΦ (%Hvs & Howner)".
      wp۰pures.

      rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
      { rewrite -length_zero_iff_nil. lia. }
      iApply "HΦ".
      iFrameSteps.
    Qed.

    Lemma inf_ws_deque_1٠push𑁒spec t γ ι ws v :
      <<<
        inf_ws_deque_1۰inv t γ ι ∗
        inf_ws_deque_1۰owner γ ws
      | ∀∀ vs,
        inf_ws_deque_1۰model γ vs
      >>>
        inf_ws_deque_1٠push #t v @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        inf_ws_deque_1۰model γ (vs ++ [v])
      | RET ();
        inf_ws_deque_1۰owner γ (vs ++ [v])
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      wp۰rec.
      wp۰apply+ (back𑁒spec with "[$]") as "Howner₁".
      wp۰load.
      wp۰apply (inf_array٠set𑁒spec𑁒owner with "[$]") as "Howner₁".
      wp۰pures.

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰store.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      set priv1 := priv ∘ S.
      iMod (owner𑁒update Stable ˖back priv1 with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

      iDestruct (inf_array۰model'𑁒shift𑁒l with "Hdata_model") as "Hdata_model"; first by intros [].
      iEval (rewrite -assoc) in "Hdata_model".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
      iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & <-).
      iMod (model𑁒push v with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁ //]") as "HΦ".

      iSplitR "Howner₁ HΦ".
      { iExists Nonempty.
        iDestruct (inv۰state𑁒Stable with "Hstate") as "#(%Hstate1 & _)"; first done.
        destruct Hstate1 as [-> | ->].

        - iDestruct "Hstate" as "(:inv۰state۰empty =1 lazy=)".
          assert (length vs = 0) as ->%nil_length_inv by lia.
          iMod (history𑁒update _ v with "Hhistory_auth") as "(Hhistory_auth & _)"; first done.
          iFrameSteps.

        - iDestruct "Hstate" as "(:inv۰state۰nonempty =1 lazy=)".
          iFrameSteps; iPureIntro.
          + simpl_length/=. lia.
          + rewrite take_app_le //; first lia.
      }
      iSteps.
    Qed.

    Lemma inf_ws_deque_1٠steal𑁒spec t γ ι :
      <<<
        inf_ws_deque_1۰inv t γ ι
      | ∀∀ vs,
        inf_ws_deque_1۰model γ vs
      >>>
        inf_ws_deque_1٠steal #t @ ↑ι
      <<<
        inf_ws_deque_1۰model γ (tail vs)
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

        iFrameSteps.
      }

      destruct_decide (front1 = front2) as <- | ?; last first.
      { assert (front1 < front2) as Hbranch2 by lia.
        iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb_2".
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hbranch1 Hbranch2}".

        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰load.
        wp۰apply+ (resolve𑁒spec𑁒loser₁ with "[$]") as "_"; first done.
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
        wp۰load.
        wp۰apply+ (resolve𑁒spec𑁒loser₂ with "[$]") as "_"; first done.
        iSteps.
      }
      rewrite Hbranch3.

      iDestruct (inv۰state𑁒Nonempty with "Hstate") as %->; first done.
      iDestruct "Hstate" as "(:inv۰state۰nonempty =2)".
      iDestruct "Hwinner" as "[(:winner) | (:winner۰pending₂ !=)]"; last first.
      { iDestruct (identifier۰model𑁒exclusive with "Hid Hid_") as %[]. }

      destruct vs2 as [| v vs2]; first naive_solver lia.
      iDestruct (history۰at𑁒get front1 with "Hhistory_auth") as "#Hhistory_at"; first done.
      iMod (winner𑁒update front1 (Φ (Some v)) with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

      iSplitR "Hwinner_pop".
      { iExists Nonempty. iFrameSteps.
        rewrite Hbranch3 /winner۰pending₂. iSteps. iIntros "!> !>".
        rewrite /winner۰au. iAuIntro.
        iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model)".
        iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%v_ %vs' (-> & Hmodel₁ & Hhistory_at_) !>".
        iDestruct (history۰at𑁒agree with "Hhistory_at Hhistory_at_") as %<-.
        iSteps.
      }
      iIntros "!> {%- Hbranch1}".

      wp۰pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp۰load.
      wp۰apply+ (resolve𑁒spec𑁒winner𑁒pop with "[$]") as "HΦ".
      wp۰load.
      wp۰apply (inf_array٠get𑁒spec𑁒history with "[$]") as "_"; first done.
      iSteps.
    Qed.

    Variant pop۰state :=
      | PopNonempty v
      | PopEmptyishWinner v
      | PopEmptyishLoser
      | PopSuperempty.
    #[local] Lemma inf_ws_deque_1٠pop₀𑁒spec {t γ} (state : pop۰state) stable back (back_ : Z) priv ws id :
      back_ = back →
      {{{
        inv' t γ ∗
        owner₁ γ stable back priv ws ∗
        match state with
        | PopNonempty v =>
            ⌜stable = Stable⌝ ∗
            ⌜priv 0 = v⌝
        | PopEmptyishWinner v =>
            ⌜stable = Unstable⌝ ∗
            history۰at γ back v ∗
            winner۰steal γ back inhabitant
        | PopEmptyishLoser =>
            ∃ id_winner prophs,
            ⌜stable = Unstable⌝ ∗
            prophet_multi۰full prophet_identifier γ.(inf_ws_deque_1۰name۰prophet_name) back (id_winner :: prophs) ∗
            ⌜head (id_winner :: prophs) ≠ Some id⌝
        | PopSuperempty =>
            ∃ front,
            ⌜stable = Unstable⌝ ∗
            front۰lb γ front ∗
            ⌜front = ˖back⌝
        end
      }}}
        inf_ws_deque_1٠pop₀ #t #id #back_
      {{{
        o back priv
      , RET o;
        owner₁ γ Stable back priv ws ∗
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
      iIntros (->) "%Φ ((:inv') & Howner₁ & H) HΦ".

      wp۰rec. wp۰pures.
      destruct state.

      - iDestruct "H" as "(-> & %Hpriv)".
        iSpecialize ("HΦ" $! (Some v)).

        wp۰apply (front𑁒spec𑁒owner𑁒Stable with "[$]") as (front2) "(Howner₁ & #Hfront_lb_1 & %Hfront2)".
        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰pures.
        case_bool_decide as Hbranch; wp۰pures.

        + wp۰load.
          wp۰apply (inf_array٠get𑁒spec𑁒owner with "[$]") as "Howner₁"; [done.. |].
          iSteps.

        + replace front2 with back by lia.

          wp۰load.
          wp۰apply+ (resolve𑁒spec𑁒Empty with "[$]") as "(Howner₁ & #Hfront_lb_2 & #Hhistory_at)".
          wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]") as "Howner₁"; [lia.. |].
          wp۰load.
          wp۰apply+ (inf_array٠get𑁒spec𑁒history with "[$]"); first lia.
          rewrite Hpriv. iSteps.

      - iDestruct "H" as "(-> & #Hhistory_at & Hwinner_steal)".
        iSpecialize ("HΦ" $! (Some v)).

        wp۰apply (front𑁒spec𑁒winner۰steal with "[$]") as "Hwinner_steal".
        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰pures.
        rewrite bool_decide_eq_false_2; first lia.
        wp۰load.
        wp۰apply+ (resolve𑁒spec𑁒winner𑁒steal with "[$]") as "#Hfront_lb".
        wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]") as "Howner₁"; [lia.. |].
        wp۰load.
        wp۰apply (inf_array٠get𑁒spec𑁒history with "[$]"); first done.
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
          wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]"); [lia.. |].
          iSteps.

        + rewrite bool_decide_eq_true_2; first lia.
          wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]"); [lia.. |].
          iSteps.

      - iDestruct "H" as "(%front & -> & #Hfront_lb & ->)".
        iSpecialize ("HΦ" $! None).

        wp۰apply (front𑁒spec𑁒Superempty with "[$]") as "Howner₁"; first lia.
        wp۰pures.
        rewrite bool_decide_eq_true_2; first lia.
        wp۰apply+ (set_back𑁒spec𑁒Superempty with "[$]") as "Howner₁"; [lia.. |].
        iSteps.
    Qed.
    Lemma inf_ws_deque_1٠pop𑁒spec t γ ι ws :
      <<<
        inf_ws_deque_1۰inv t γ ι ∗
        inf_ws_deque_1۰owner γ ws
      | ∀∀ vs,
        inf_ws_deque_1۰model γ vs
      >>>
        inf_ws_deque_1٠pop #t @ ↑ι
      <<<
        ∃∃ o ws',
        ⌜vs `suffix_of` ws⌝ ∗
        match o with
        | None =>
            ⌜vs = []⌝ ∗
            ⌜ws' = []⌝ ∗
            inf_ws_deque_1۰model γ []
        | Some v =>
            ∃ vs',
            ⌜vs = vs' ++ [v]⌝ ∗
            ⌜ws' = vs'⌝ ∗
            inf_ws_deque_1۰model γ vs'
        end
      | RET o;
        inf_ws_deque_1۰owner γ ws'
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      wp۰rec.
      wp۰apply (wp𑁒id with "[//]") as (id) "Hid".
      wp۰apply+ (back𑁒spec with "[$]") as "Howner₁".
      wp۰pures.

      wp۰bind (_ <-{back} _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰store.
      iDestruct (owner𑁒agree with "Howner₁ Howner₂") as %(<- & <- & <-).
      iDestruct (inv۰state𑁒Stable with "Hstate") as "#([-> | ->] & _)"; first done.

      { iDestruct "Hstate" as "(:inv۰state۰empty =1 lazy=)".
        assert (0 < back) as Hback by lia.
        assert (length vs1 = 0) as ->%nil_length_inv by lia.

        iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb".
        iMod (owner𑁒update Unstable (back - 1) priv with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (model𑁒empty with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! None with "[$Hmodel₁ //]") as "HΦ".

        iSplitR "Howner₁ HΦ".
        { iExists Superempty. iFrameSteps. }
        iIntros "!> {%- Hback}".

        wp۰apply+ (inf_ws_deque_1٠pop₀𑁒spec PopSuperempty _ (back - 1) with "[- HΦ]"); [lia | iFrameSteps |].
        iSteps.
      }

      iDestruct "Hstate" as "(:inv۰state۰nonempty =1 lazy=)".
      assert (0 < back) as Hback by lia.
      destruct vs1 as [| v vs1 _] using rev_ind; first naive_solver lia.

      destruct_decide (˖front1 = back) as <- | Hbranch1.

      - assert (length vs1 = 0) as ->%nil_length_inv.
        { simpl_length/= in Hvs1. lia. }

        iDestruct (history۰at𑁒get front1 with "Hhistory_auth") as "#Hhistory_at"; first done.
        iMod (owner𑁒update Unstable front1 priv with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
        iEval (rewrite -(app_nil_r (hist1 ++ [v]))) in "Hdata_model".

        destruct_decide (head $ prophss1 front1 = Some id) as (prophs0 & Hprophss1)%head_Some | Hbranch2.

        + rewrite Hprophss1.
          iDestruct "Hwinner" as "[(:winner) | (:winner۰pending₂ !=)]"; last first.
          { iDestruct (identifier۰model𑁒exclusive with "Hid Hid_") as %[]. }
          iMod (winner𑁒update front1 inhabitant with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
          iMod (model𑁒pop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
          iMod ("HΦ" $! (Some v) with "[$Hmodel₁ //]") as "HΦ".

          iSplitR "Howner₁ Hwinner_steal HΦ".
          { iExists Emptyish. iFrameSteps. iPureIntro.
            simpl_length/=. lia.
          }
          iIntros "!> {%}".

          wp۰apply+ (inf_ws_deque_1٠pop₀𑁒spec (PopEmptyishWinner v) _ front1 with "[- HΦ]"); [lia | iFrameSteps |].
          iSteps.

        + iDestruct "Hwinner" as "[(:winner) | Hwinner]".

          { iMod (winner𑁒update front1 inhabitant with "Hwinner_pop Hwinner_steal") as "(Hwinner_pop & Hwinner_steal)".

            iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
            iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
            iMod (model𑁒pop with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂) /=".
            iMod ("HΦ" $! (Some v) with "[$Hmodel₁ //]") as "HΦ".

            iSplitR "Howner₁ Hwinner_steal HΦ".
            { iExists Emptyish. iFrameSteps. iPureIntro.
              simpl_length/=. lia.
            }
            iIntros "!> {%}".

            wp۰apply+ (inf_ws_deque_1٠pop₀𑁒spec (PopEmptyishWinner v) _ front1 with "[- HΦ]"); [lia | iFrameSteps |].
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

          iSplitR "Howner₁ HΦ".
          { iExists Emptyish. iFrameStep 7. iExists P. iSteps. iPureIntro.
            simpl_length/=. lia.
          }
          iIntros "!> {%- Hbranch2}".

          wp۰apply+ (inf_ws_deque_1٠pop₀𑁒spec PopEmptyishLoser _ front1 with "[- HΦ]"); [lia | iFrameSteps |].
          iSteps.

      - iMod (owner𑁒update Stable (back - 1) (v .: priv) with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".

        iEval (rewrite assoc) in "Hdata_model".
        iDestruct (inf_array۰model'𑁒shift𑁒r with "Hdata_model") as "Hdata_model".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model۰owner₁𑁒agree with "Howner₁ Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
        iMod (model𑁒pop' with "Howner₁ Hmodel₁ Hmodel₂") as "(Howner₁ & Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some v) with "[$Hmodel₁ //]") as "HΦ".

        iSplitR "Howner₁ HΦ".
        { iExists Nonempty. iFrameSteps; iPureIntro.
          all: simpl_length/= in Hvs1.
          - lia.
          - rewrite take_app_le //; first lia.
        }
        iIntros "!> {%- Hback}".

        wp۰apply+ (inf_ws_deque_1٠pop₀𑁒spec (PopNonempty v) _ (back - 1) with "[- HΦ]"); [lia | iFrameSteps |].
        iSteps.
    Qed.
  End inf_ws_deque_1۰G.

  #[global] Opaque inf_ws_deque_1۰inv.
  #[global] Opaque inf_ws_deque_1۰model.
  #[global] Opaque inf_ws_deque_1۰owner.
End base.

Require zoo_saturn.inf_ws_deque_1__opaque.

Section inf_ws_deque_1۰G.
  Context `{inf_ws_deque_1۰G : InfWsDeque1G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition inf_ws_deque_1۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.inf_ws_deque_1۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition inf_ws_deque_1۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.inf_ws_deque_1۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition inf_ws_deque_1۰owner t ws : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.inf_ws_deque_1۰owner γ ws.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Howner{_{}}
      )
    ".

  #[global] Instance inf_ws_deque_1۰model𑁒timeless γ vs :
    Timeless (inf_ws_deque_1۰model γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_ws_deque_1۰owner𑁒timeless γ ws :
    Timeless (inf_ws_deque_1۰owner γ ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_ws_deque_1۰inv𑁒persistent t ι :
    Persistent (inf_ws_deque_1۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma inf_ws_deque_1۰model𑁒exclusive t vs1 vs2 :
    inf_ws_deque_1۰model t vs1 -∗
    inf_ws_deque_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_ws_deque_1۰model𑁒exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma inf_ws_deque_1۰owner𑁒exclusive t ws1 ws2 :
    inf_ws_deque_1۰owner t ws1 -∗
    inf_ws_deque_1۰owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_ws_deque_1۰owner𑁒exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma inf_ws_deque_1𑁒owner𑁒model γ ws vs :
    inf_ws_deque_1۰owner γ ws -∗
    inf_ws_deque_1۰model γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_ws_deque_1۰owner𑁒model with "Howner_1 Hmodel_2").
  Qed.

  Lemma inf_ws_deque_1٠create𑁒spec ι :
    {{{
      True
    }}}
      inf_ws_deque_1٠create ()
    {{{
      t
    , RET t;
      inf_ws_deque_1۰inv t ι ∗
      inf_ws_deque_1۰model t [] ∗
      inf_ws_deque_1۰owner t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.inf_ws_deque_1٠create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel & Howner)".
    iMod (meta𑁒set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma inf_ws_deque_1٠size𑁒spec t ι ws :
    <<<
      inf_ws_deque_1۰inv t ι ∗
      inf_ws_deque_1۰owner t ws
    | ∀∀ vs,
      inf_ws_deque_1۰model t vs
    >>>
      inf_ws_deque_1٠size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      inf_ws_deque_1۰model t vs
    | RET #(length vs);
      inf_ws_deque_1۰owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.inf_ws_deque_1٠size𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_ws_deque_1٠is_empty𑁒spec t ι ws :
    <<<
      inf_ws_deque_1۰inv t ι ∗
      inf_ws_deque_1۰owner t ws
    | ∀∀ vs,
      inf_ws_deque_1۰model t vs
    >>>
      inf_ws_deque_1٠is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      inf_ws_deque_1۰model t vs
    | RET #(bool_decide (vs = []%list));
      inf_ws_deque_1۰owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.inf_ws_deque_1٠is_empty𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_ws_deque_1٠push𑁒spec t ι ws v :
    <<<
      inf_ws_deque_1۰inv t ι ∗
      inf_ws_deque_1۰owner t ws
    | ∀∀ vs,
      inf_ws_deque_1۰model t vs
    >>>
      inf_ws_deque_1٠push t v @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      inf_ws_deque_1۰model t (vs ++ [v])
    | RET ();
      inf_ws_deque_1۰owner t (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.inf_ws_deque_1٠push𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_ws_deque_1٠steal𑁒spec t ι :
    <<<
      inf_ws_deque_1۰inv t ι
    | ∀∀ vs,
      inf_ws_deque_1۰model t vs
    >>>
      inf_ws_deque_1٠steal t @ ↑ι
    <<<
      inf_ws_deque_1۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_ws_deque_1٠steal𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_ws_deque_1٠pop𑁒spec t ι ws :
    <<<
      inf_ws_deque_1۰inv t ι ∗
      inf_ws_deque_1۰owner t ws
    | ∀∀ vs,
      inf_ws_deque_1۰model t vs
    >>>
      inf_ws_deque_1٠pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          inf_ws_deque_1۰model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          inf_ws_deque_1۰model t vs'
      end
    | RET o;
      inf_ws_deque_1۰owner t ws'
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.inf_ws_deque_1٠pop𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1". 1: iSteps. iIntros "%o %ws' ($ & Ho)".
      iExists o, ws'. destruct o.
      all: iDecompose "Ho".
      all: iFrameSteps.
    }
  Qed.
End inf_ws_deque_1۰G.

#[global] Opaque inf_ws_deque_1۰inv.
#[global] Opaque inf_ws_deque_1۰model.
#[global] Opaque inf_ws_deque_1۰owner.
