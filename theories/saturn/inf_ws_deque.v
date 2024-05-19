(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/65211c5176b632bd9ed268c0c608ac483f88a992/src_lockfree/ws_deque.ml
*)

From Coq.Logic Require Import
  FunctionalExtensionality.

From iris.algebra Require Import
  list.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.base_logic Require Import
  lib.excl
  lib.twins
  lib.auth_nat_max
  lib.mono_list.
From zoo.language Require Import
  identifier
  wise_prophet
  notations
  diaframe.
From zoo.std Require Import
  option
  inf_array.
From zoo.saturn Require Export
  base.
From zoo Require Import
  options.

Implicit Types front : nat.
Implicit Types back : Z.
Implicit Types l slot : location.
Implicit Types id : identifier.
Implicit Types v t : val.
Implicit Types hist model : list val.
Implicit Types priv : nat → val.

#[local] Program Definition inf_ws_deque_prophet := {|
  typed_prophet_type :=
    nat * identifier ;
  typed_prophet_of_val v :=
    match v with
    | ValTuple [ValInt front; ValProphecy id] =>
        Some (Z.to_nat front, id)
    | _ =>
        None
    end ;
  typed_prophet_to_val '(front, id) :=
    (#front, #id)%V ;
|}.
Solve Obligations of inf_ws_deque_prophet with
  try done.
Next Obligation.
  intros (front & id) v ->. simplify. rewrite Nat2Z.id //.
Qed.
Implicit Types past prophs : list inf_ws_deque_prophet.(typed_prophet_type).

Class InfWsDequeG Σ `{zoo_G : !ZooG Σ} := {
  #[local] inf_ws_deque_G_inf_array_G :: InfArrayG Σ ;
  #[local] inf_ws_deque_G_ctl_G :: TwinsG Σ (ZO * (nat -d> valO)) ;
  #[local] inf_ws_deque_G_front_G :: AuthNatMaxG Σ ;
  #[local] inf_ws_deque_G_hist_G :: MonoListG Σ val ;
  #[local] inf_ws_deque_G_model_G :: TwinsG Σ (listO valO) ;
  #[local] inf_ws_deque_G_lock_G :: ExclG Σ unitO ;
  #[local] inf_ws_deque_G_prophet_G :: WiseProphetG Σ inf_ws_deque_prophet ;
  #[local] inf_ws_deque_G_winner_G :: TwinsG Σ (natO * (valO -d> ▶ ∙)) ;
}.

Definition inf_ws_deque_Σ := #[
  inf_array_Σ ;
  twins_Σ (ZO * (nat -d> valO)) ;
  auth_nat_max_Σ ;
  mono_list_Σ val ;
  twins_Σ (listO valO) ;
  excl_Σ unitO ;
  wise_prophet_Σ inf_ws_deque_prophet ;
  twins_Σ (natO * (valO -d> ▶ ∙))
].
#[global] Instance subG_inf_ws_deque_Σ Σ `{zoo_G : !ZooG Σ} :
  subG inf_ws_deque_Σ Σ →
  InfWsDequeG Σ .
Proof.
  solve_inG.
Qed.

Module raw.
  #[local] Notation "'front'" := (
    in_type "t" 0
  )(in custom zoo_field
  ).
  #[local] Notation "'back'" := (
    in_type "t" 1
  )(in custom zoo_field
  ).
  #[local] Notation "'data'" := (
    in_type "t" 2
  )(in custom zoo_field
  ).
  #[local] Notation "'prophet'" := (
    in_type "t" 3
  )(in custom zoo_field
  ).

  Definition inf_ws_deque_create : val :=
    λ: <>,
      { #0; #0; inf_array_create (); Proph }.

  Definition inf_ws_deque_push : val :=
    λ: "t" "v",
      let: "back" := "t".{back} in
      inf_array_set "t".{data} "back" "v" ;;
      "t" <-{back} "back" + #1.

  Definition inf_ws_deque_steal : val :=
    rec: "inf_ws_deque_steal" "t" :=
      let: "id" := Id in
      let: "front" := "t".{front} in
      let: "back" := "t".{back} in
      if: "front" < "back" then (
        if: Resolve (Cas "t".[front] "front" ("front" + #1)) "t".{prophet} ("front", "id") then (
          ‘Some{ inf_array_get "t".{data} "front" }
        ) else (
          Yield ;;
          "inf_ws_deque_steal" "t"
        )
      ) else (
        §None
      ).

  Definition inf_ws_deque_pop : val :=
    λ: "t",
      let: "id" := Id in
      let: "back" := "t".{back} - #1 in
      "t" <-{back} "back" ;;
      let: "front" := "t".{front} in
      if: "back" < "front" then (
        "t" <-{back} "front" ;;
        §None
      ) else (
        if: "front" < "back" then (
          ‘Some{ inf_array_get "t".{data} "back" }
        ) else (
          if: Resolve (Cas "t".[front] "front" ("front" + #1)) "t".{prophet} ("front", "id") then (
            "t" <-{back} "front" + #1 ;;
            ‘Some{ inf_array_get "t".{data} "back" }
          ) else (
            "t" <-{back} "front" + #1 ;;
            §None
          )
        )
      ).

  Section inf_ws_deque_G.
    Context `{inf_ws_deque_G : InfWsDequeG Σ}.

    Implicit Types Φ : val → iProp Σ.

    Record inf_ws_deque_meta := {
      inf_ws_deque_meta_data : val ;
      inf_ws_deque_meta_prophet : prophet_id ;
      inf_ws_deque_meta_prophet_name : wise_prophet_name ;
      inf_ws_deque_meta_ctl : gname ;
      inf_ws_deque_meta_front : gname ;
      inf_ws_deque_meta_hist : gname ;
      inf_ws_deque_meta_model : gname ;
      inf_ws_deque_meta_lock : gname ;
      inf_ws_deque_meta_winner : gname ;
    }.
    Implicit Types γ : inf_ws_deque_meta.

    #[local] Instance inf_ws_deque_meta_eq_dec :
      EqDecision inf_ws_deque_meta.
    Proof.
      solve_decision.
    Qed.
    #[local] Instance inf_ws_deque_meta_countable :
      Countable inf_ws_deque_meta.
    Proof.
      pose encode γ := (
        γ.(inf_ws_deque_meta_data),
        γ.(inf_ws_deque_meta_prophet),
        γ.(inf_ws_deque_meta_prophet_name),
        γ.(inf_ws_deque_meta_ctl),
        γ.(inf_ws_deque_meta_front),
        γ.(inf_ws_deque_meta_hist),
        γ.(inf_ws_deque_meta_model),
        γ.(inf_ws_deque_meta_lock),
        γ.(inf_ws_deque_meta_winner)
      ).
      pose decode := λ '(data, pid, γ_prophet, γ_ctl, γ_front, γ_hist, γ_model, γ_lock, γ_winner), {|
        inf_ws_deque_meta_data := data ;
        inf_ws_deque_meta_prophet := pid ;
        inf_ws_deque_meta_prophet_name := γ_prophet ;
        inf_ws_deque_meta_ctl := γ_ctl ;
        inf_ws_deque_meta_front := γ_front ;
        inf_ws_deque_meta_hist := γ_hist ;
        inf_ws_deque_meta_model := γ_model ;
        inf_ws_deque_meta_lock := γ_lock ;
        inf_ws_deque_meta_winner := γ_winner ;
      |}.
      refine (inj_countable' encode decode _). intros []. done.
    Qed.

    #[local] Definition inf_ws_deque_ctl₁' γ_ctl back priv :=
      twins_twin1 (twins_G := inf_ws_deque_G_ctl_G) γ_ctl (DfracOwn 1) (back, priv).
    #[local] Definition inf_ws_deque_ctl₁ γ back priv :=
      inf_ws_deque_ctl₁' γ.(inf_ws_deque_meta_ctl) back priv.
    #[local] Definition inf_ws_deque_ctl₂' γ_ctl back priv :=
      twins_twin2 (twins_G := inf_ws_deque_G_ctl_G) γ_ctl (back, priv).
    #[local] Definition inf_ws_deque_ctl₂ γ back priv :=
      inf_ws_deque_ctl₂' γ.(inf_ws_deque_meta_ctl) back priv.

    #[local] Definition inf_ws_deque_front_auth' γ_front front :=
      auth_nat_max_auth γ_front (DfracOwn 1) front.
    #[local] Definition inf_ws_deque_front_auth γ front :=
      inf_ws_deque_front_auth' γ.(inf_ws_deque_meta_front) front.
    #[local] Definition inf_ws_deque_front_lb γ front :=
      auth_nat_max_lb γ.(inf_ws_deque_meta_front) front.

    #[local] Definition inf_ws_deque_hist_auth' γ_hist hist :=
      mono_list_auth γ_hist (DfracOwn 1) hist.
    #[local] Definition inf_ws_deque_hist_auth γ hist :=
      inf_ws_deque_hist_auth' γ.(inf_ws_deque_meta_hist) hist.
    #[local] Definition inf_ws_deque_hist_elem γ i v :=
      mono_list_elem γ.(inf_ws_deque_meta_hist) i v.

    #[local] Definition inf_ws_deque_model₁' γ_model model :=
      twins_twin2 (twins_G := inf_ws_deque_G_model_G) γ_model model.
    #[local] Definition inf_ws_deque_model₁ γ model :=
      inf_ws_deque_model₁' γ.(inf_ws_deque_meta_model) model.
    #[local] Definition inf_ws_deque_model₂' γ_model model :=
      twins_twin1 (twins_G := inf_ws_deque_G_model_G) γ_model (DfracOwn 1) model.
    #[local] Definition inf_ws_deque_model₂ γ model :=
      inf_ws_deque_model₂' γ.(inf_ws_deque_meta_model) model.

    #[local] Definition inf_ws_deque_lock' γ_lock :=
      excl γ_lock ().
    #[local] Definition inf_ws_deque_lock γ :=
      inf_ws_deque_lock' γ.(inf_ws_deque_meta_lock).

    #[local] Definition inf_ws_deque_winner₁' γ_winner front Φ :=
      twins_twin2 (twins_G := inf_ws_deque_G_winner_G) γ_winner (front, Next ∘ Φ).
    #[local] Definition inf_ws_deque_winner₁ γ front Φ :=
      inf_ws_deque_winner₁' γ.(inf_ws_deque_meta_winner) front Φ.
    #[local] Definition inf_ws_deque_winner₂' γ_winner front Φ :=
      twins_twin1 (twins_G := inf_ws_deque_G_winner_G) γ_winner (DfracOwn 1) (front, Next ∘ Φ).
    #[local] Definition inf_ws_deque_winner₂ γ front Φ :=
      inf_ws_deque_winner₂' γ.(inf_ws_deque_meta_winner) front Φ.
    #[local] Definition inf_ws_deque_winner' γ_winner : iProp Σ :=
      ∃ front Φ1 Φ2,
      inf_ws_deque_winner₁' γ_winner front Φ1 ∗
      inf_ws_deque_winner₂' γ_winner front Φ2.
    #[local] Definition inf_ws_deque_winner γ : iProp Σ :=
      ∃ front Φ1 Φ2,
      inf_ws_deque_winner₁ γ front Φ1 ∗
      inf_ws_deque_winner₂ γ front Φ2.

    Definition inf_ws_deque_model t model : iProp Σ :=
      ∃ l γ,
      ⌜t = #l⌝ ∗
      (* metadata *)
      meta l nroot γ ∗
      (* model values *)
      inf_ws_deque_model₂ γ model.

    Definition inf_ws_deque_owner t : iProp Σ :=
      ∃ l γ back priv,
      ⌜t = #l⌝ ∗
      (* metadata *)
      meta l nroot γ ∗
      (* control token *)
      inf_ws_deque_ctl₂ γ back priv ∗
      (* lock *)
      inf_ws_deque_lock γ.

    #[local] Definition inf_ws_deque_atomic_update γ ι Φ : iProp Σ :=
      AU <{
        ∃∃ model,
        inf_ws_deque_model₂ γ model
      }> @ ⊤ ∖ ↑ι, ∅ <{
        ∀∀ v model',
        ⌜model = v :: model'⌝ ∗ inf_ws_deque_model₂ γ model',
        COMM Φ ’Some{ v }
      }>.
    #[local] Definition inf_ws_deque_state_inner₁ γ :=
      inf_ws_deque_winner γ.
    #[local] Definition inf_ws_deque_state₁ γ front back hist : iProp Σ :=
      (* physical configuration *)
      ⌜Z.of_nat front = back⌝ ∗
      (* history values *)
      inf_ws_deque_hist_auth γ hist ∗
      ⌜length hist = front⌝ ∗
      (* inner state *)
      inf_ws_deque_state_inner₁ γ.
    #[local] Definition inf_ws_deque_state_inner₂ γ ι front prophs : iProp Σ :=
      match head $ filter (λ '(front', _), front' = front) prophs with
      | None =>
          inf_ws_deque_winner γ
      | Some (_, id) =>
            inf_ws_deque_winner γ
          ∨ identifier_model id ∗
            ∃ Φ,
            inf_ws_deque_winner₁ γ front Φ ∗
            inf_ws_deque_atomic_update γ ι Φ
      end.
    #[local] Definition inf_ws_deque_state₂ γ ι front back hist model prophs : iProp Σ :=
      (* physical configuration *)
      ⌜(front < back)%Z⌝ ∗
      (* history values *)
      inf_ws_deque_hist_auth γ (hist ++ [model !!! 0]) ∗
      ⌜length hist = front⌝ ∗
      (* inner state *)
      inf_ws_deque_state_inner₂ γ ι front prophs.
    #[local] Definition inf_ws_deque_state_inner₃₁ γ front hist prophs : iProp Σ :=
      match head $ filter (λ '(front', _), front' = front) prophs with
      | None =>
          ∃ Φ,
          inf_ws_deque_winner₂ γ front Φ
      | _ =>
          ∃ Φ,
          inf_ws_deque_winner₁ γ front Φ ∗
          Φ ’Some{ hist !!! front }
      end.
    #[local] Definition inf_ws_deque_state₃₁ γ front back hist prophs : iProp Σ :=
      (* physical configuration *)
      ⌜Z.of_nat front = back⌝ ∗
      (* history values *)
      inf_ws_deque_hist_auth γ hist ∗
      ⌜length hist = S front⌝ ∗
      (* inner state *)
      inf_ws_deque_state_inner₃₁ γ front hist prophs.
    #[local] Definition inf_ws_deque_state_inner₃₂ γ :=
      inf_ws_deque_winner γ.
    #[local] Definition inf_ws_deque_state₃₂ γ front back hist : iProp Σ :=
      (* physical configuration *)
      ⌜Z.of_nat front = (back + 1)%Z⌝ ∗
      (* history values *)
      inf_ws_deque_hist_auth γ hist ∗
      ⌜length hist = front⌝ ∗
      (* inner state *)
      inf_ws_deque_state_inner₃₂ γ.
    #[local] Definition inf_ws_deque_state₃ γ front back hist prophs : iProp Σ :=
      inf_ws_deque_lock γ ∗
      ( inf_ws_deque_state₃₁ γ front back hist prophs
      ∨ inf_ws_deque_state₃₂ γ front back hist
      ).
    #[local] Definition inf_ws_deque_state γ ι front back hist model prophs : iProp Σ :=
        inf_ws_deque_state₁ γ front back hist
      ∨ inf_ws_deque_state₂ γ ι front back hist model prophs
      ∨ inf_ws_deque_state₃ γ front back hist prophs.
    #[local] Typeclasses Opaque inf_ws_deque_state_inner₁.
    #[local] Typeclasses Opaque inf_ws_deque_state_inner₂.
    #[local] Typeclasses Opaque inf_ws_deque_state_inner₃₁.
    #[local] Typeclasses Opaque inf_ws_deque_state_inner₃₂.
    #[local] Typeclasses Opaque inf_ws_deque_state.
    #[local] Ltac unfold_state :=
      rewrite
        /inf_ws_deque_state
        /inf_ws_deque_state_inner₁
        /inf_ws_deque_state_inner₂
        /inf_ws_deque_state_inner₃₁
        /inf_ws_deque_state_inner₃₂.

    #[local] Definition inf_ws_deque_inv_inner l γ ι : iProp Σ :=
      ∃ front back hist model priv past prophs,
      (* mutable physical fields *)
      l.[front] ↦ #front ∗
      l.[back] ↦ #back ∗
      (* control token *)
      inf_ws_deque_ctl₁ γ back priv ∗
      (* front authority *)
      inf_ws_deque_front_auth γ front ∗
      (* data model *)
      inf_array_model' γ.(inf_ws_deque_meta_data) (hist ++ model) priv ∗
      (* model values *)
      inf_ws_deque_model₁ γ model ∗
      ⌜length model = Z.to_nat (back - front)⌝ ∗
      (* prophet model *)
      wise_prophet_model inf_ws_deque_prophet γ.(inf_ws_deque_meta_prophet) γ.(inf_ws_deque_meta_prophet_name) past prophs ∗
      ⌜Forall (λ '(front', _), front' < front) past⌝ ∗
      (* state *)
      inf_ws_deque_state γ ι front back hist model prophs.
    Definition inf_ws_deque_inv t ι : iProp Σ :=
      ∃ l γ,
      ⌜t = #l⌝ ∗
      (* metadata *)
      meta l nroot γ ∗
      (* immutable physical fields *)
      l.[data] ↦□ γ.(inf_ws_deque_meta_data) ∗
      l.[prophet] ↦□ #γ.(inf_ws_deque_meta_prophet) ∗
      (* invariants *)
      inf_array_inv γ.(inf_ws_deque_meta_data) ∗
      inv ι (inf_ws_deque_inv_inner l γ ι).

    #[global] Instance inf_ws_deque_model_timeless t model :
      Timeless (inf_ws_deque_model t model).
    Proof.
      apply _.
    Qed.
    #[global] Instance inf_ws_deque_owner_timeless t :
      Timeless (inf_ws_deque_owner t).
    Proof.
      apply _.
    Qed.
    #[global] Instance inf_ws_deque_inv_persistent t ι :
      Persistent (inf_ws_deque_inv t ι).
    Proof.
      apply _.
    Qed.

    #[local] Lemma inf_ws_deque_ctl_alloc :
      ⊢ |==>
        ∃ γ_ctl,
        inf_ws_deque_ctl₁' γ_ctl 0 (λ _, ()%V) ∗
        inf_ws_deque_ctl₂' γ_ctl 0 (λ _, ()%V).
    Proof.
      apply twins_alloc'.
    Qed.
    #[local] Lemma inf_ws_deque_ctl_agree γ back1 priv1 back2 priv2 :
      inf_ws_deque_ctl₁ γ back1 priv1 -∗
      inf_ws_deque_ctl₂ γ back2 priv2 -∗
      ⌜back1 = back2 ∧ priv1 = priv2⌝.
    Proof.
      iIntros "Hctl₁ Hctl₂".
      iDestruct (twins_agree with "Hctl₁ Hctl₂") as %(? & ?%functional_extensionality).
      iSteps.
    Qed.
    #[local] Lemma inf_ws_deque_ctl_update {γ back1 priv1 back2 priv2} back priv :
      inf_ws_deque_ctl₁ γ back1 priv1 -∗
      inf_ws_deque_ctl₂ γ back2 priv2 ==∗
        inf_ws_deque_ctl₁ γ back priv ∗
        inf_ws_deque_ctl₂ γ back priv.
    Proof.
      apply twins_update'.
    Qed.

    #[local] Lemma inf_ws_deque_front_alloc :
      ⊢ |==>
        ∃ γ_front,
        inf_ws_deque_front_auth' γ_front 0.
    Proof.
      apply auth_nat_max_alloc.
    Qed.
    #[local] Lemma inf_ws_deque_front_valid γ front1 front2 :
      inf_ws_deque_front_auth γ front1 -∗
      inf_ws_deque_front_lb γ front2 -∗
      ⌜front2 ≤ front1⌝.
    Proof.
      apply auth_nat_max_lb_valid.
    Qed.
    #[local] Lemma inf_ws_deque_front_auth_update {γ front} front' :
      front ≤ front' →
      inf_ws_deque_front_auth γ front ⊢ |==>
      inf_ws_deque_front_auth γ front'.
    Proof.
      apply auth_nat_max_update.
    Qed.
    #[local] Lemma inf_ws_deque_front_lb_get γ front :
      inf_ws_deque_front_auth γ front ⊢
      inf_ws_deque_front_lb γ front.
    Proof.
      apply auth_nat_max_lb_get.
    Qed.
    #[local] Lemma inf_ws_deque_front_lb_le {γ front} front' :
      front' ≤ front →
      inf_ws_deque_front_lb γ front ⊢
      inf_ws_deque_front_lb γ front'.
    Proof.
      apply auth_nat_max_lb_le.
    Qed.
    #[local] Lemma inf_ws_deque_front_state₃₂ γ ι front front' back hist model prophs :
      back = (front' - 1)%Z →
      inf_ws_deque_front_auth γ front -∗
      inf_ws_deque_front_lb γ front' -∗
      inf_ws_deque_state γ ι front back hist model prophs -∗
        ⌜front = front'⌝ ∗
        inf_ws_deque_front_auth γ front' ∗
        inf_ws_deque_lock γ ∗
        inf_ws_deque_state₃₂ γ front' back hist.
    Proof.
      iIntros (->) "Hfront_auth #Hfront_lb Hstate".
      iDestruct (inf_ws_deque_front_valid with "Hfront_auth Hfront_lb") as %Hle.
      unfold_state. iDestruct "Hstate" as "[Hstate | [Hstate | (Hlock & [Hstate | Hstate])]]";
        iDestruct "Hstate" as "(%Hstate & Hhist_auth & %Hhist & Hstate)";
        [lia.. |].
      assert (front' = front) as -> by lia. iSteps.
    Qed.

    #[local] Lemma inf_ws_deque_hist_alloc :
      ⊢ |==>
        ∃ γ_hist,
        inf_ws_deque_hist_auth' γ_hist [].
    Proof.
      apply mono_list_alloc.
    Qed.
    #[local] Lemma inf_ws_deque_hist_elem_get {γ hist} i v :
      hist !! i = Some v →
      inf_ws_deque_hist_auth γ hist ⊢
      inf_ws_deque_hist_elem γ i v.
    Proof.
      setoid_rewrite mono_list_lb_get. apply mono_list_elem_get.
    Qed.
    #[local] Lemma inf_ws_deque_hist_agree γ hist i v :
      inf_ws_deque_hist_auth γ hist -∗
      inf_ws_deque_hist_elem γ i v -∗
      ⌜hist !! i = Some v⌝.
    Proof.
      apply mono_list_lookup.
    Qed.
    #[local] Lemma inf_ws_deque_hist_update {γ hist} v :
      inf_ws_deque_hist_auth γ hist ⊢ |==>
      inf_ws_deque_hist_auth γ (hist ++ [v]).
    Proof.
      apply mono_list_update_app.
    Qed.

    #[local] Lemma inf_ws_deque_model_alloc :
      ⊢ |==>
        ∃ γ_model,
        inf_ws_deque_model₁' γ_model [] ∗
        inf_ws_deque_model₂' γ_model [].
    Proof.
      iMod (twins_alloc' (twins_G := inf_ws_deque_G_model_G) []) as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iSteps.
    Qed.
    #[local] Lemma inf_ws_deque_model_agree γ model1 model2 :
      inf_ws_deque_model₁ γ model1 -∗
      inf_ws_deque_model₂ γ model2 -∗
      ⌜model1 = model2⌝.
    Proof.
      iIntros "Hmodel₁ Hmodel₂".
      iDestruct (twins_agree_L with "Hmodel₂ Hmodel₁") as %->.
      iSteps.
    Qed.
    #[local] Lemma inf_ws_deque_model_update {γ model1 model2} model :
      inf_ws_deque_model₁ γ model1 -∗
      inf_ws_deque_model₂ γ model2 ==∗
        inf_ws_deque_model₁ γ model ∗
        inf_ws_deque_model₂ γ model.
    Proof.
      iIntros "Hmodel₁ Hmodel₂".
      iMod (twins_update' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
      iSteps.
    Qed.

    #[local] Lemma inf_ws_deque_lock_alloc :
      ⊢ |==>
        ∃ γ_lock,
        inf_ws_deque_lock' γ_lock.
    Proof.
      apply excl_alloc.
    Qed.
    #[local] Lemma inf_ws_deque_lock_exclusive γ :
      inf_ws_deque_lock γ -∗
      inf_ws_deque_lock γ -∗
      False.
    Proof.
      apply excl_exclusive.
    Qed.
    #[local] Lemma inf_ws_deque_lock_state γ ι front back hist model prophs :
      inf_ws_deque_lock γ -∗
      inf_ws_deque_state γ ι front back hist model prophs -∗
        inf_ws_deque_lock γ ∗
        ( inf_ws_deque_state₁ γ front back hist
        ∨ inf_ws_deque_state₂ γ ι front back hist model prophs
        ).
    Proof.
      unfold_state. iIntros "Hlock [Hstate | [Hstate | (Hlock' & Hstate)]]"; [iFrame.. |].
      iDestruct (inf_ws_deque_lock_exclusive with "Hlock Hlock'") as %[].
    Qed.

    #[local] Lemma inf_ws_deque_winner_alloc :
      ⊢ |==>
        ∃ γ_winner,
        inf_ws_deque_winner' γ_winner.
    Proof.
      iMod (twins_alloc' (twins_G := inf_ws_deque_G_winner_G) (inhabitant, λ _, Next inhabitant)) as "(%γ_winner & Hwinner₁ & Hwinner₂)".
      iSteps.
    Qed.
    #[local] Lemma inf_ws_deque_winner₁_exclusive γ front1 Φ1 front2 Φ2 :
      inf_ws_deque_winner₁ γ front1 Φ1 -∗
      inf_ws_deque_winner₁ γ front2 Φ2 -∗
      False.
    Proof.
      apply twins_twin2_exclusive.
    Qed.
    #[local] Lemma inf_ws_deque_winner₁_exclusive' γ front Φ :
      inf_ws_deque_winner₁ γ front Φ -∗
      inf_ws_deque_winner γ -∗
      False.
    Proof.
      iIntros "Hwinner₁ (%front' & %Φ1 & %Φ2 & Hwinner₁' & Hwinner₂)".
      iApply (inf_ws_deque_winner₁_exclusive with "Hwinner₁ Hwinner₁'").
    Qed.
    #[local] Lemma inf_ws_deque_winner₂_exclusive γ front1 Φ1 front2 Φ2 :
      inf_ws_deque_winner₂ γ front1 Φ1 -∗
      inf_ws_deque_winner₂ γ front2 Φ2 -∗
      False.
    Proof.
      apply twins_twin1_exclusive.
    Qed.
    #[local] Lemma inf_ws_deque_winner₂_exclusive' γ front Φ :
      inf_ws_deque_winner₂ γ front Φ -∗
      inf_ws_deque_winner γ -∗
      False.
    Proof.
      iIntros "Hwinner₂ (%front' & %Φ1 & %Φ2 & Hwinner₁ & Hwinner₂')".
      iApply (inf_ws_deque_winner₂_exclusive with "Hwinner₂ Hwinner₂'").
    Qed.
    #[local] Lemma inf_ws_deque_winner_agree {γ front1 Φ1 front2 Φ2} v :
      inf_ws_deque_winner₁ γ front1 Φ1 -∗
      inf_ws_deque_winner₂ γ front2 Φ2 -∗
        ⌜front1 = front2⌝ ∗
        ▷ (Φ1 v ≡ Φ2 v) ∗
        inf_ws_deque_winner₁ γ front1 Φ1 ∗
        inf_ws_deque_winner₂ γ front1 Φ2.
    Proof.
      iIntros "Hwinner₁ Hwinner₂".
      iDestruct (twins_agree with "Hwinner₂ Hwinner₁") as "#HΦ".
      rewrite prod_equivI /=. iDestruct "HΦ" as "(% & HΦ)". simplify.
      iFrame. iSplit; first iSteps.
      rewrite discrete_fun_equivI. iDestruct ("HΦ" $! v) as "HΦv". rewrite later_equivI.
      iModIntro. iRewrite "HΦv". iSteps.
    Qed.
    #[local] Lemma inf_ws_deque_winner_update {γ front1 Φ1 front2 Φ2} front Φ :
      inf_ws_deque_winner₁ γ front1 Φ1 -∗
      inf_ws_deque_winner₂ γ front2 Φ2 ==∗
        inf_ws_deque_winner₁ γ front Φ ∗
        inf_ws_deque_winner₂ γ front Φ.
    Proof.
      iIntros "Hwinner₁ Hwinner₂".
      iMod (twins_update (twins_G := inf_ws_deque_G_winner_G) (front, Next ∘ Φ) with "Hwinner₂ Hwinner₁") as "($ & $)"; first done.
      iSteps.
    Qed.
    #[local] Lemma inf_ws_deque_winner₁_state γ ι front front' back hist model prophs Φ :
      inf_ws_deque_winner₁ γ front Φ -∗
      inf_ws_deque_state γ ι front' back hist model prophs -∗
        ⌜front' = front⌝ ∗
        ⌜back = front⌝ ∗
        inf_ws_deque_lock γ ∗
        inf_ws_deque_hist_auth γ hist ∗
        ⌜length hist = S front⌝ ∗
          ∃ Φ',
          ⌜head $ filter (λ '(front', _), front' = front) prophs = None⌝ ∗
          inf_ws_deque_winner₁ γ front Φ ∗
          inf_ws_deque_winner₂ γ front Φ'.
    Proof.
      unfold_state. iIntros "Hwinner₁ [Hstate | [Hstate | Hstate]]".
      - iDestruct "Hstate" as "(_ & _ & _ & Hstate)".
        iDestruct (inf_ws_deque_winner₁_exclusive' with "Hwinner₁ Hstate") as %[].
      - iDestruct "Hstate" as "(_ & _ & _ & Hstate)".
        unfold_state. destruct (head $ filter _ _) as [(_front' & id) |].
        + iDestruct "Hstate" as "[Hstate | (_ & % & Hwinner₁' & _)]".
          * iDestruct (inf_ws_deque_winner₁_exclusive' with "Hwinner₁ Hstate") as %[].
          * iDestruct (inf_ws_deque_winner₁_exclusive with "Hwinner₁ Hwinner₁'") as %[].
        + iDestruct (inf_ws_deque_winner₁_exclusive' with "Hwinner₁ Hstate") as %[].
      - iDestruct "Hstate" as "(Hlock & [(<- & Hhist_auth & -> & Hstate) | (_ & _ & _ & Hstate)])".
        + unfold_state. destruct (head $ filter _ _) as [proph |] eqn:Hprophs.
          * iDestruct "Hstate" as "(% & Hwinner₁' & _)".
            iDestruct (inf_ws_deque_winner₁_exclusive with "Hwinner₁ Hwinner₁'") as %[].
          * iDestruct "Hstate" as "(%Φ' & Hwinner₂)".
            iDestruct (inf_ws_deque_winner_agree inhabitant with "Hwinner₁ Hwinner₂") as "(<- & _ & Hwinner₁ & Hwinner₂)".
            iSteps.
        + iDestruct (inf_ws_deque_winner₁_exclusive' with "Hwinner₁ Hstate") as %[].
    Qed.
    #[local] Lemma inf_ws_deque_winner₂_state γ ι front front' back hist model prophs Φ :
      inf_ws_deque_winner₂ γ front Φ -∗
      inf_ws_deque_state γ ι front' back hist model prophs -∗
        ⌜front' = front⌝ ∗
        ( ⌜(front < back)%Z⌝ ∗
          inf_ws_deque_hist_auth γ (hist ++ [model !!! 0]) ∗
          ⌜length hist = front⌝ ∗
          ( ∃ id Φ',
            ⌜head $ filter (λ '(front', _), front' = front) prophs = Some (front, id)⌝ ∗
            inf_ws_deque_winner₁ γ front Φ' ∗
            inf_ws_deque_winner₂ γ front Φ ∗
            identifier_model id ∗
            inf_ws_deque_atomic_update γ ι Φ'
          )
        ∨ ⌜back = front⌝ ∗
          inf_ws_deque_lock γ ∗
          inf_ws_deque_hist_auth γ hist ∗
          ⌜length hist = S front⌝ ∗
          ( ∃ id Φ',
            ⌜head $ filter (λ '(front', _), front' = front) prophs = Some (front, id)⌝ ∗
            inf_ws_deque_winner₁ γ front Φ' ∗
            inf_ws_deque_winner₂ γ front Φ ∗
            Φ' ’Some{ hist !!! front }
          )
        ).
    Proof.
      unfold_state. iIntros "Hwinner₂ [Hstate | [Hstate | Hstate]]".
      - iDestruct "Hstate" as "(_ & _ & _ & Hstate)".
        iDestruct (inf_ws_deque_winner₂_exclusive' with "Hwinner₂ Hstate") as %[].
      - iDestruct "Hstate" as "(%Hstate & Hhist_auth & -> & Hstate)".
        unfold_state. destruct (head $ filter _ _) as [(_front' & id) |] eqn:Hprophs.
        + iDestruct "Hstate" as "[Hstate | (Hid & %Φ' & Hwinner₁ & HΦ')]".
          * iDestruct (inf_ws_deque_winner₂_exclusive' with "Hwinner₂ Hstate") as %[].
          * iDestruct (inf_ws_deque_winner_agree inhabitant with "Hwinner₁ Hwinner₂") as "(-> & _ & Hwinner₁ & Hwinner₂)".
            pose proof Hprophs as (-> & _)%head_Some_elem_of%elem_of_list_filter. iSteps.
        + iDestruct (inf_ws_deque_winner₂_exclusive' with "Hwinner₂ Hstate") as %[].
      - iDestruct "Hstate" as "(Hlock & [(<- & Hhist_auth & -> & Hstate) | (_ & _ & _ & Hstate)])".
        + unfold_state. destruct (head $ filter _ _) as [(_front' & id) |] eqn:Hprophs.
          * iDestruct "Hstate" as "(%Φ' & Hwinner₁ & HΦ')".
            iDestruct (inf_ws_deque_winner_agree inhabitant with "Hwinner₁ Hwinner₂") as "(-> & _ & Hwinner₁ & Hwinner₂)".
            pose proof Hprophs as (-> & _)%head_Some_elem_of%elem_of_list_filter. iSteps.
          * iDestruct "Hstate" as "(%Φ' & Hwinner₂')".
            iDestruct (inf_ws_deque_winner₂_exclusive with "Hwinner₂ Hwinner₂'") as %[].
        + iDestruct (inf_ws_deque_winner₂_exclusive' with "Hwinner₂ Hstate") as %[].
    Qed.
    #[local] Lemma inf_ws_deque_winner₂_state' γ ι front front' hist model prophs Φ :
      inf_ws_deque_winner₂ γ front Φ -∗
      inf_ws_deque_state γ ι front' front hist model prophs -∗
        ⌜front' = front⌝ ∗
        inf_ws_deque_lock γ ∗
        inf_ws_deque_hist_auth γ hist ∗
        ⌜length hist = S front⌝ ∗
          ∃ id Φ',
          ⌜head $ filter (λ '(front', _), front' = front) prophs = Some (front, id)⌝ ∗
          inf_ws_deque_winner₁ γ front Φ' ∗
          inf_ws_deque_winner₂ γ front Φ ∗
          Φ' ’Some{ hist !!! front }.
    Proof.
      iIntros "Hwinner₂ Hstate".
      iDestruct (inf_ws_deque_winner₂_state with "Hwinner₂ Hstate") as "($ & [Hstate | Hstate])".
      - iDestruct "Hstate" as "(%Hstate & _)". lia.
      - iSteps.
    Qed.

    Lemma inf_ws_deque_owner_exclusive t :
      inf_ws_deque_owner t -∗
      inf_ws_deque_owner t -∗
      False.
    Proof.
      iIntros "(%l & %γ & %back & %priv & -> & #Hmeta & Hctl₂1 & Hlock1) (%_l & %_γ & %_back & %_priv & %Heq & #_Hmeta & Hctl₂2 & Hlock2)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %->. iClear "_Hmeta".
      iApply (inf_ws_deque_lock_exclusive with "Hlock1 Hlock2").
    Qed.

    #[local] Lemma inf_ws_deque_wp_get_hist l γ ι i v :
      {{{
        inf_array_inv γ.(inf_ws_deque_meta_data) ∗
        inv ι (inf_ws_deque_inv_inner l γ ι) ∗
        l.[data] ↦□ γ.(inf_ws_deque_meta_data) ∗
        inf_ws_deque_hist_elem γ i v
      }}}
        inf_array_get !#l.[data] #i
      {{{
        RET v; True
      }}}.
    Proof.
      iIntros "%Φ (#Harray_inv & #Hinv & #Hdata & #Hhist_elem) HΦ".

      (* → [!#l.[data]] *)
      wp_load.

      (* → [array.(inf_array_get) data #i] *)
      awp_apply (inf_array_get_spec with "Harray_inv") without "HΦ"; first lia.
      (* open invariant *)
      iInv "Hinv" as "(%front & %back & %hist & %model & %priv & %past & %prophs & Hfront & Hback & Hctl₁ & Hfront_auth & >Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast & Hstate)".
      (* we have [(hist ++ model) !! i = Some v] *)
      iAssert (◇ ⌜(hist ++ model) !! i = Some v⌝)%I as "#>%Hlookup".
      { unfold_state. iDestruct "Hstate" as "[Hstate | [Hstate | (_ & [Hstate | Hstate])]]";
          iDestruct "Hstate" as "(>%Hstate & >Hhist_auth & >%Hhist & _)";
          iModIntro;
          iDestruct (inf_ws_deque_hist_agree with "Hhist_auth Hhist_elem") as %?;
          iPureIntro.
        - erewrite lookup_app_l_Some; done.
        - destruct model as [| w model]; simpl in *; first lia.
          rewrite (assoc (++) hist [w]). erewrite lookup_app_l_Some; done.
        - rewrite (nil_length_inv model); first lia. list_simplifier. done.
        - rewrite (nil_length_inv model); first lia. erewrite lookup_app_l_Some; done.
      }
      iAaccIntro with "Harray_model"; iIntros "Harray_model".
      { iModIntro. rewrite right_id. repeat iExists _. iFrame. iSteps. }
      (* close invariant *)
      iModIntro. iSplitL.
      { repeat iExists _. iFrame. iSteps. }
      iIntros "_ HΦ".
      clear- Hlookup.

      rewrite Nat2Z.id decide_True; first eauto using lookup_lt_Some.
      erewrite list_lookup_total_correct; last done.
      iApply ("HΦ" with "[//]").
    Qed.
    #[local] Lemma inf_ws_deque_wp_get_priv l γ ι back priv i :
      (back ≤ i)%Z →
      {{{
        inf_array_inv γ.(inf_ws_deque_meta_data) ∗
        inv ι (inf_ws_deque_inv_inner l γ ι) ∗
        l.[data] ↦□ γ.(inf_ws_deque_meta_data) ∗
        inf_ws_deque_ctl₂ γ back priv ∗
        inf_ws_deque_lock γ
      }}}
        inf_array_get !#l.[data] #i
      {{{
        RET priv (Z.to_nat (i - back));
        inf_ws_deque_ctl₂ γ back priv ∗
        inf_ws_deque_lock γ
      }}}.
    Proof.
      iIntros "%Hi %Φ (#Harray_inv & #Hinv & #Hdata & Hctl₂ & Hlock) HΦ".

      (* → [!#l.[data]] *)
      wp_load.

      (* open invariant *)
      iApply fupd_wp. iMod (inv_acc with "Hinv") as "((%front & %_back & %hist & %model & %_priv & %past & %prophs & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast & Hstate) & Hclose)"; first done.
      iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
      (* we have [0 ≤ back] *)
      iAssert (◇ ⌜0 ≤ back⌝)%I%Z as "#>%Hback".
      { (* we have lock, hence we are in state 1 or in state 2 *)
        iDestruct (inf_ws_deque_lock_state with "Hlock Hstate") as "(Hlock & [Hstate | Hstate])";
          iDestruct "Hstate" as "(>%Hstate & _)"; auto with lia.
      }
      (* close invariant *)
      iMod ("Hclose" with "[- Hctl₂ Hlock HΦ]") as "_".
      { repeat iExists _. iFrame. done. }
      iModIntro.
      clear- Hi Hback.

      (* → [array.(inf_array_get) data #i] *)
      awp_apply (inf_array_get_spec' with "Harray_inv"); first lia.
      (* open invariant *)
      iInv "Hinv" as "(%front & %_back & %hist & %model & %_priv & %past & %prophs & Hfront & Hback & >Hctl₁ & Hfront_auth & >Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast & Hstate)".
      iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
      (* we have [back = length (hist ++ model)] *)
      iAssert (◇ ⌜back = length (hist ++ model)⌝)%I%Z as "#>%Hback'".
      { (* we have lock, hence we are in state 1 or in state 2 *)
        iDestruct (inf_ws_deque_lock_state with "Hlock Hstate") as "(Hlock & [Hstate | Hstate])";
          iDestruct "Hstate" as "(>%Hstate & _ & >%Hhist & _)";
          rewrite app_length; auto with lia.
      }
      iAaccIntro with "Harray_model"; iIntros "Harray_model".
      { iModIntro. iFrame. repeat iExists _. iFrame. done. }
      (* close invariant *)
      iModIntro. iSplitR "Hctl₂ Hlock HΦ".
      { repeat iExists _. iFrame. done. }
      iIntros "_".
      clear- Hi Hback Hback'.

      rewrite decide_False; first lia.
      assert (Z.to_nat i - length (hist ++ model) = Z.to_nat (i - back)) as -> by lia.
      iApply "HΦ". iFrame.
    Qed.

    #[local] Lemma inf_ws_deque_wp_resolve_inconsistent_1 l γ ι front id prophs_lb (front1 front2 : Z) :
      head $ filter (λ '(front', _), front' = front) prophs_lb = None →
      {{{
        inf_array_inv γ.(inf_ws_deque_meta_data) ∗
        inv ι (inf_ws_deque_inv_inner l γ ι) ∗
        wise_prophet_lb inf_ws_deque_prophet γ.(inf_ws_deque_meta_prophet_name) prophs_lb
      }}}
        Resolve (Cas #l.[front] #front1 #front2) #γ.(inf_ws_deque_meta_prophet) (#front, #id)%V
      {{{ v,
        RET v; False
      }}}.
    Proof.
      iIntros (Hprophs_lb%head_None) "%Φ (#Harray_inv & #Hinv & #Hprophet_lb) HΦ".

      (* open invariant *)
      iInv "Hinv" as "(%front' & %back & %hist & %model & %priv & %past & %prophs & Hfront & Hback & Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & >Hprophet_model & >%Hpast & Hstate)".
      (* current prophecies are a suffix of prophet lower bound *)
      iDestruct (wise_prophet_model_lb_valid with "Hprophet_model Hprophet_lb") as %(past1 & past2 & -> & ->).
      (* do resolve *)
      wp_apply (wise_prophet_wp_resolve inf_ws_deque_prophet(front, id) with "Hprophet_model"); [done.. |].
      (* whether Cas succeed or not, we reach a contradiction *)
      wp_cas as _ | _ _.
      all: iModIntro; iIntros "%prophs' ->".
      all: eelim (filter_nil_not_elem_of _ _ (front, id)); [done.. |].
      all: apply elem_of_app; right; apply elem_of_cons; naive_solver.
    Qed.
    #[local] Lemma inf_ws_deque_wp_resolve_loser l γ ι front _front id id' prophs_lb v :
      head $ filter (λ '(front', _), front' = front) prophs_lb = Some (_front, id') →
      id ≠ id' →
      {{{
        inf_array_inv γ.(inf_ws_deque_meta_data) ∗
        inv ι (inf_ws_deque_inv_inner l γ ι) ∗
        inf_ws_deque_front_lb γ front ∗
        wise_prophet_lb inf_ws_deque_prophet γ.(inf_ws_deque_meta_prophet_name) prophs_lb
      }}}
        Resolve (Cas #l.[front] #front v) #γ.(inf_ws_deque_meta_prophet) (#front, #id)%V
      {{{
        RET #false;
        inf_ws_deque_front_lb γ (S front)
      }}}.
    Proof.
      iIntros "%Hprophs_lb %Hid %Φ (#Harray_inv & #Hinv & #Hfront_lb & #Hprophet_lb) HΦ".

      (* open invariant *)
      iInv "Hinv" as "(%front' & %back & %hist & %model & %priv & %past & %prophs & Hfront & Hback & Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & >Hprophet_model & >%Hpast & Hstate)".
      (* current prophecies are a suffix of prophet lower bound *)
      iDestruct (wise_prophet_model_lb_valid with "Hprophet_model Hprophet_lb") as %(past1 & past2 & -> & ->).
      (* do resolve *)
      wp_apply (wise_prophet_wp_resolve inf_ws_deque_prophet (front, id) with "Hprophet_model"); [done.. |].
      (* Cas must fail as we are not the winner: [id ≠ id'] *)
      wp_cas as _Hfront | ? _; last simplify; last first.
      { iModIntro. iIntros "%prophs' -> Hprophet_model".
        rewrite filter_app filter_cons_True // in Hprophs_lb.
        destruct (filter _ past2) as [| (__front & id'')] eqn:Hpast2; first naive_solver.
        apply (f_equal head), head_Some_elem_of, elem_of_list_filter in Hpast2 as (-> & Hpast2).
        rewrite Forall_app !Forall_forall in Hpast. naive_solver lia.
      }
      iAssert ⌜front < front'⌝%I as %Hfront; last clear _Hfront.
      { iDestruct (inf_ws_deque_front_valid with "Hfront_auth Hfront_lb") as %?.
        iPureIntro. assert (front ≠ front') by naive_solver. lia.
      }
      iModIntro. iIntros "%prophs' -> Hprophet_model".
      (* emit front fragment at [S front] *)
      iClear "Hfront_lb".
      iDestruct (inf_ws_deque_front_lb_get with "Hfront_auth") as "#_Hfront_lb".
      iDestruct (inf_ws_deque_front_lb_le (S front) with "_Hfront_lb") as "#Hfront_lb"; first lia.
      iClear "_Hfront_lb".
      (* close invariant *)
      iModIntro. iSplitR "HΦ".
      { iExists front', back, hist, model, priv, _, prophs'. iFrame.
        iSplit; first done.
        iSplit. { iPureIntro. decompose_Forall; done. }
        unfold_state. iDestruct "Hstate" as "[Hstate | [(%Hstate & Hstate) | (Hlock & [(%Hstate & Hstate) | Hstate])]]".
        - iLeft. done.
        - iRight. iLeft. iFrame. iSplit; first done.
          unfold_state. rewrite filter_cons_False //. lia.
        - do 2 iRight. iFrame. iLeft. iFrame. iSplit; first done.
          unfold_state. rewrite filter_cons_False //. lia.
        - do 2 iRight. iFrame.
      }
      clear.

      iApply ("HΦ" with "Hfront_lb").
    Qed.
    #[local] Lemma inf_ws_deque_wp_resolve_inconsistent_2 l γ ι front _front priv Ψ id id' prophs_lb v :
      head $ filter (λ '(front', _), front' = front) prophs_lb = Some (_front, id') →
      id ≠ id' →
      {{{
        inf_array_inv γ.(inf_ws_deque_meta_data) ∗
        inv ι (inf_ws_deque_inv_inner l γ ι) ∗
        inf_ws_deque_ctl₂ γ front priv ∗
        inf_ws_deque_front_lb γ front ∗
        wise_prophet_lb inf_ws_deque_prophet γ.(inf_ws_deque_meta_prophet_name) prophs_lb ∗
        inf_ws_deque_winner₂ γ front Ψ
      }}}
        Resolve (Cas #l.[front] #front v) #γ.(inf_ws_deque_meta_prophet) (#front, #id)%V
      {{{
        RET #false; False
      }}}.
    Proof.
      iIntros "%Hprophs_lb %Hid %Φ (#Harray_inv & #Hinv & Hctl₂ & #Hfront_lb & #Hprophet_lb & Hwinner₂) HΦ".

      (* do resolve *)
      iApply wp_fupd.
      wp_apply (inf_ws_deque_wp_resolve_loser with "[$Harray_inv $Hinv $Hfront_lb $Hprophet_lb]"); [done.. |]. iClear "Hfront_lb". iIntros "#Hfront_lb".

      (* open invariant *)
      iMod (inv_acc with "Hinv") as "((%front' & %_back & %hist & %model & %_priv & %past & %prophs & Hfront & Hback & >Hctl₁ & >Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast & Hstate) & Hclose)"; first done.
      iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as "(-> & ->)".
      (* we are in state 3.1, hence [front' = front] *)
      iAssert (◇ ⌜front' = front⌝)%I as "#>->".
      { iDestruct (inf_ws_deque_winner₂_state' with "Hwinner₂ Hstate") as "(>-> & _)". done. }
      (* contradiction: front authority is strictly less than front lower bound *)
      iDestruct (inf_ws_deque_front_valid with "Hfront_auth Hfront_lb") as %?. lia.
    Qed.

    Lemma inf_ws_deque_create_spec ι :
      {{{ True }}}
        inf_ws_deque_create ()
      {{{ t,
        RET t;
        inf_ws_deque_inv t ι ∗
        inf_ws_deque_model t [] ∗
        inf_ws_deque_owner t
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.

      (* → [inf_array_create ()] *)
      wp_apply (inf_array_create_spec with "[//]") as "%data (#Harray_inv & Harray_model)".

      (* → [Proph] *)
      wp_apply (wise_prophet_wp_proph with "[//]") as "%pid %γ_prophet %prophs Hprophet_model".

      (* → [{ #0; #0; data; #pid }] *)
      wp_record l as "Hmeta" "(Hfront & Hback & Hdata & Hpid & _)".
      iMod (pointsto_persist with "Hdata") as "#Hdata".
      iMod (pointsto_persist with "Hpid") as "#Hpid".

      iApply "HΦ".

      iMod inf_ws_deque_ctl_alloc as "(%γ_ctl & Hctl₁ & Hctl₂)".
      iMod inf_ws_deque_front_alloc as "(%γ_front & Hfront_auth)".
      iMod inf_ws_deque_hist_alloc as "(%γ_hist & Hhist_auth)".
      iMod inf_ws_deque_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iMod inf_ws_deque_lock_alloc as "(%γ_lock & Hlock)".
      iMod inf_ws_deque_winner_alloc as "(%γ_winner & Hwinner)".

      set γ := {|
        inf_ws_deque_meta_data := data ;
        inf_ws_deque_meta_prophet := pid ;
        inf_ws_deque_meta_ctl := γ_ctl ;
        inf_ws_deque_meta_front := γ_front ;
        inf_ws_deque_meta_hist := γ_hist ;
        inf_ws_deque_meta_model := γ_model ;
        inf_ws_deque_meta_lock := γ_lock ;
        inf_ws_deque_meta_prophet_name := γ_prophet ;
        inf_ws_deque_meta_winner := γ_winner ;
      |}.
      iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

      iSplitR "Hctl₂ Hmodel₂ Hlock".
      { repeat iExists _. iFrame "#∗". iSplitR; first done.
        iApply inv_alloc. iExists 0, 0%Z, [], [], (λ _, ()%V), [], prophs. iFrame.
        do 2 (iSplit; first done).
        unfold_state. iLeft. iFrame. unfold_state. iFrame. done.
      }
      iSplitL "Hmodel₂".
      { iExists l, γ. naive_solver. }
      iExists l, γ, 0%Z, (λ _, ()%V). iFrame "#∗". done.
    Qed.

    Lemma inf_ws_deque_push_spec t ι v :
      <<<
        inf_ws_deque_inv t ι ∗
        inf_ws_deque_owner t
      | ∀∀ model,
        inf_ws_deque_model t model
      >>>
        inf_ws_deque_push t v @ ↑ι
      <<<
        inf_ws_deque_model t (model ++ [v])
      | RET ();
        inf_ws_deque_owner t
      >>>.
    Proof.
      iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hdata & #Hpid & #Harray_inv & #Hinv) & (%_l & %_γ & %back & %priv & %Heq & #_Hmeta & Hctl₂ & Hlock)) HΦ". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

      wp_rec. wp_pures.

      (* → [!#l.[back]] *)
      wp_bind (!#l.[back])%E.
      (* open invariant *)
      iInv "Hinv" as "(%front & %_back & %hist & %model & %_priv & %past & %prophs & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast & Hstate)".
      iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
      (* do load back *)
      wp_load.
      (* we have lock, hence we are in state 1 or state 2, hence [0 ≤ back] *)
      iAssert ⌜0 ≤ back⌝%I%Z as %Hback.
      { iDestruct (inf_ws_deque_lock_state with "Hlock Hstate") as "(_ & [Hstate | Hstate])";
          iDestruct "Hstate" as "(%Hstate & _)"; iPureIntro; lia.
      }
      (* close invariant *)
      iModIntro. iSplitR "Hctl₂ Hlock HΦ".
      { repeat iExists _. iFrame. done. }
      clear- Hback.

      (* → [!#l.[data]] *)
      wp_load.

      (* → [array.(inf_array_set) data #back v] *)
      awp_apply (inf_array_set_spec' with "Harray_inv") without "HΦ"; first done.
      (* open invariant *)
      iInv "Hinv" as "(%front & %_back & %hist & %model & %_priv & %past & %prophs & Hfront & Hback & >Hctl₁ & Hfront_auth & >Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast & Hstate)".
      iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
      iAaccIntro with "Harray_model"; iIntros "Harray_model".
      { iFrame. repeat iExists _. iFrame. done. }
      (* update private values in control tokens *)
      set (priv' := <[0 := v]> priv).
      iMod (inf_ws_deque_ctl_update back priv' with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
      (* we have lock, hence we are in state 1 or state 2 *)
      iDestruct (inf_ws_deque_lock_state with "Hlock Hstate") as "(Hlock & Hstate)".
      (* hence [front ≤ back] and [length hist = front] *)
      iAssert (◇ ⌜front ≤ back ∧ length hist = front⌝%Z)%I as "#>%".
      { iDestruct "Hstate" as "[Hstate | Hstate]";
          iDestruct "Hstate" as "(>%Hstate & _ & >%Hhist & _)";
          iPureIntro; lia.
      }
      (* hence [back = length (hist ++ model)] *)
      assert (Z.to_nat back = length (hist ++ model)) as Heq. { rewrite app_length. lia. }
      rewrite Heq decide_False; first lia. rewrite Nat.sub_diag.
      (* close invariant *)
      iModIntro. iSplitR "Hctl₂ Hlock".
      { iExists front, back, hist, model, priv', past, prophs. iFrame.
        do 2 (iSplit; first auto).
        unfold_state. iDestruct "Hstate" as "[Hstate | Hstate]"; [iLeft | iRight; iLeft]; done.
      }
      iIntros "_ HΦ".
      clear.

      wp_pures.

      (* → [#l <-{back} #(back + 1)] *)
      (* open invariant *)
      iInv "Hinv" as "(%front & %_back & %hist & %model & %_priv & %past & %prophs & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast & Hstate)".
      iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
      (* do increment back *)
      wp_store.
      (* update private values in control tokens *)
      set (priv'' i := priv (S i)).
      iMod (inf_ws_deque_ctl_update (back + 1) priv'' with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
      (* begin transaction *)
      iMod "HΦ" as "(%_model & (%_l & %_γ & %Heq & _Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
      (* update model values *)
      set (model' := model ++ [v]).
      iMod (inf_ws_deque_model_update model' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      (* end transaction *)
      iMod ("HΦ" with "[Hmodel₂]") as "HΦ".
      { repeat iExists _. iFrame "#∗". done. }
      (* update data model *)
      iDestruct (inf_array_model'_shift_l with "Harray_model") as "Harray_model"; first by intros [].
      rewrite -(assoc (++)) -/model'.
      (* we have lock, hence we are in state 1 or state 2 *)
      iDestruct (inf_ws_deque_lock_state with "Hlock Hstate") as "(Hlock & [Hstate | Hstate])".

      - iDestruct "Hstate" as "(%Hstate & Hhist_auth & %Hhist & Hstate)".
        destruct (nil_or_length_pos model) as [-> |]; last lia.
        (* update history values *)
        iMod (inf_ws_deque_hist_update v with "Hhist_auth") as "Hhist_auth".
        (* close invariant *)
        iModIntro. iSplitR "Hctl₂ Hlock HΦ".
        { iExists front, (back + 1)%Z, hist, model', priv'', past, prophs. iFrame.
          do 2 (iSplit; first (simpl; auto with lia)).
          unfold_state. iRight. iLeft. iFrame. iSplit; first auto with lia.
          unfold_state. destruct (head $ filter _ _) as [[] |]; auto.
        }
        clear.

        iApply "HΦ". repeat iExists _. iFrame "#∗". done.

      - iDestruct "Hstate" as "(%Hstate & Hhist_auth & %Hhist & Hstate)".
        destruct model as [| w model]; first naive_solver lia.
        (* close invariant *)
        iModIntro. iSplitR "Hctl₂ Hlock HΦ".
        { iExists front, (back + 1)%Z, hist, model', priv'', past, prophs. iFrame.
          iSplit. { iPureIntro. rewrite app_length. simpl in *. lia. }
          iSplit; first done.
          unfold_state. iRight. iLeft. iFrame. auto with lia.
        }
        clear.

        iApply "HΦ". repeat iExists _. iFrame "#∗". done.
    Qed.

    Lemma inf_ws_deque_steal_spec t ι :
      <<<
        inf_ws_deque_inv t ι
      | ∀∀ model,
        inf_ws_deque_model t model
      >>>
        inf_ws_deque_steal t @ ↑ι
      <<<
        inf_ws_deque_model t (tail model)
      | RET head model; True
      >>>.
    Proof.
      iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hdata & #Hpid & #Harray_inv & #Hinv) HΦ".
      iLöb as "IH".

      wp_rec.

      (* → [Id] *)
      wp_smart_apply (wp_id with "[//]") as "%id Hid".

      wp_pures.

      (* → [!#l.[front]] *)
      wp_bind (!#l.[front])%E.
      (* open invariant *)
      iInv "Hinv" as "(%front1 & %back1 & %hist & %model & %priv & %past1 & %prophs1 & Hfront & Hback & Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast1 & Hstate)".
      (* do load front *)
      wp_load.
      (* emit front fragment at [front1] *)
      iDestruct (inf_ws_deque_front_lb_get with "Hfront_auth") as "#Hfront_lb".
      (* close invariant *)
      iModIntro. iSplitR "Hid HΦ".
      { repeat iExists _. iFrame. done. }
      clear.

      wp_pures.

      (* → [!#l.[back]] *)
      wp_bind (!#l.[back])%E.
      (* open invariant *)
      iInv "Hinv" as "(%front2 & %back2 & %hist & %model & %priv & %past2 & %prophs2 & Hfront & Hback & Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast2 & Hstate)".
      (* do load back *)
      wp_load.
      (* we have [front1 ≤ front2] *)
      iDestruct (inf_ws_deque_front_valid with "Hfront_auth Hfront_lb") as %Hfront2.
      (* branching 1: enforce [front1 < back2] *)
      destruct (decide (front1 < back2)%Z) as [Hbranch1 | Hbranch1]; last first.
      { (* we have [model = []] *)
        assert (length model = 0) as ->%nil_length_inv by lia.
        (* begin transaction *)
        iMod "HΦ" as "(%_model & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
        (* end transation *)
        iMod ("HΦ" with "[Hmodel₂] [//]") as "HΦ".
        { repeat iExists _. naive_solver. }
        (* close invariant *)
        iModIntro. iSplitR "Hid HΦ".
        { repeat iExists _. iFrame. done. }
        clear- Hbranch1.

        wp_pures.

        (* → [if: #(bool_decide (front1 < back2))] *)
        rewrite bool_decide_eq_false_2; first done.

        wp_pures.

        iApply "HΦ".
      }
      (* branching 2: enforce [front2 = front1] *)
      rewrite Nat.le_lteq in Hfront2. destruct Hfront2 as [Hbranch2 | <-].
      { (* emit front fragment at [front2] *)
        iClear "Hfront_lb". iDestruct (inf_ws_deque_front_lb_get with "Hfront_auth") as "#Hfront_lb".
        (* close invariant *)
        iModIntro. iSplitR "Hid HΦ".
        { repeat iExists _. iFrame. done. }
        clear- Hbranch1 Hbranch2.

        wp_pures.

        (* → [if: #(bool_decide (front1 < back2))] *)
        rewrite bool_decide_eq_true_2; first done.

        (* → [!#l.[prophet]] *)
        wp_load.

        wp_pures.

        (* → [Resolve (Cas #l.[front] #front1 #(front1 + 1)) #γ.(inf_ws_deque_meta_prophet) (#front1, #id)] *)
        wp_bind (Resolve (Cas #l.[front] #front1 #(front1 + 1)) #γ.(inf_ws_deque_meta_prophet) (#front1, #id)%V).
        (* open invariant *)
        iInv "Hinv" as "(%front3 & %back3 & %hist & %model & %priv & %past3 & %prophs3 & Hfront & Hback & Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & >Hprophet_model & >%Hpast3 & Hstate)".
        (* do resolve *)
        wp_apply (wise_prophet_wp_resolve inf_ws_deque_prophet (front1, id) with "Hprophet_model"); [done.. |].
        (* branching 3: Cas must fail as we have seen [front2] such that [front1 < front2] *)
        wp_cas as _Hbranch3 | ? _; last simplify; last first.
        { iDestruct (inf_ws_deque_front_valid with "Hfront_auth Hfront_lb") as %?.
          lia.
        }
        iAssert ⌜front1 < front3⌝%I as %Hbranch3; last clear _Hbranch3.
        { iDestruct (inf_ws_deque_front_valid with "Hfront_auth Hfront_lb") as %?.
          auto with lia.
        }
        iModIntro. iIntros "%prophs3' -> Hprophet_model".
        (* close invariant *)
        iModIntro. iSplitR "Hid HΦ".
        { iExists front3, back3, hist, model, priv, (past3 ++ [_]), prophs3'. iFrame.
          iSplit; first done.
          iSplit. { iPureIntro. decompose_Forall; done. }
          unfold_state. iDestruct "Hstate" as "[Hstate | [(%Hstate & Hhist_auth & %Hhist & Hstate) | (Hlock & [(%Hstate & Hhist_auth & %Hhist & Hstate) | Hstate])]]".
          - iLeft. done.
          - iRight. iLeft. iFrame. do 2 (iSplit; first done).
            unfold_state. rewrite filter_cons_False //. lia.
          - do 2 iRight. iFrame. iLeft. iFrame. do 2 (iSplit; first done).
            unfold_state. rewrite filter_cons_False //. lia.
          - do 2 iRight. iFrame.
        }
        clear- Hbranch1 Hbranch2 Hbranch3.

        (* → [inf_ws_deque_steal #l] *)
        wp_smart_apply ("IH" with "HΦ").
      }
      (* we are in state 2 *)
      unfold_state. iDestruct "Hstate" as "[(%Hstate & _) | [(_ & Hhist_auth & %Hhist & Hstate) | (_ & [(%Hstate & _) | (%Hstate & _)])]]"; try lia.
      (* hence there is at least one model value *)
      destruct model as [| v model]; first naive_solver lia.
      (* emit history fragment at [front1] *)
      iDestruct (inf_ws_deque_hist_elem_get front1 v with "Hhist_auth") as "#Hhist_elem".
      { rewrite lookup_app_r; first lia. rewrite Hhist Nat.sub_diag //. }
      (* emit prophet lower bound at [prophs2] *)
      iDestruct (wise_prophet_lb_get with "Hprophet_model") as "#Hprophet_lb".
      (* branching 3: enforce [filter (λ '(_, _, front', _), front' = front1) prophs2 ≠ []] *)
      unfold_state. destruct (head $ filter _ prophs2) as [(_front1 & id') |] eqn:Hbranch3; first last.
      { (* close invariant *)
        iModIntro. iSplitR "Hid HΦ".
        { iExists front1, back2, hist, (v :: model), priv, past2, prophs2. iFrame.
          do 2 (iSplit; first done).
          unfold_state. iRight. iLeft. iFrame. do 2 (iSplit; first done).
          unfold_state. rewrite Hbranch3 //.
        }
        clear- Hbranch1 Hbranch3.

        wp_pures.

        (* → [if: #(bool_decide (front1 < back2))] *)
        rewrite bool_decide_eq_true_2; first done.

        (* → [!#l.[prophet]] *)
        wp_load.

        (* inconsistent prophecy resolution *)
        wp_smart_apply (inf_ws_deque_wp_resolve_inconsistent_1 with "[$Harray_inv $Hinv $Hprophet_lb]") as "% []"; first done.
      }
      (* branching 4: enforce [id' = id] *)
      destruct (decide (id' = id)) as [-> | Hbranch4]; first last.
      { (* close invariant *)
        iModIntro. iSplitR "Hid HΦ".
        { iExists front1, back2, hist, (v :: model), priv, past2, prophs2. iFrame.
          do 2 (iSplit; first done).
          unfold_state. iRight. iLeft. iFrame. do 2 (iSplit; first done).
          unfold_state. rewrite Hbranch3 //.
        }
        clear- Hbranch1 Hbranch3 Hbranch4.

        wp_pures.

        (* → [if: #(bool_decide (front1 < back2))] *)
        rewrite bool_decide_eq_true_2; first done.

        (* → [!#l.[prophet]] *)
        wp_load.

        (* Cas must fail as we are not the winner *)
        wp_smart_apply (inf_ws_deque_wp_resolve_loser with "[$Harray_inv $Hinv $Hfront_lb $Hprophet_lb]") as "_"; [done.. |].

        (* → [inf_ws_deque_steal #l] *)
        wp_smart_apply ("IH" with "HΦ").
      }
      (* we now know we are the next winner *)
      (* we own the winner tokens *)
      iDestruct "Hstate" as "[(% & % & % & Hwinner₁ & Hwinner₂) | (Hid' & _)]"; last first.
      { iDestruct (identifier_model_exclusive with "Hid Hid'") as %[]. }
      (* update winner tokens *)
      iMod (inf_ws_deque_winner_update front1 Φ with "Hwinner₁ Hwinner₂") as "(Hwinner₁ & Hwinner₂)".
      (* close invariant *)
      iModIntro. iSplitR "Hwinner₂".
      { iExists front1, back2, hist, (v :: model), priv, past2, prophs2. iFrame.
        do 2 (iSplit; first done).
        unfold_state. iRight. iLeft. iFrame. do 2 (iSplit; first done).
        unfold_state. rewrite Hbranch3. iRight. iFrame. iExists Φ. iFrame.
        iModIntro. rewrite /inf_ws_deque_atomic_update. iAuIntro.
        iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%_model (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iAaccIntro with "Hmodel₂".
        { iIntros "Hmodel₂ !>". iSplitL "Hmodel₂"; last auto.
          repeat iExists _. iFrame "#∗". done.
        }
        iIntros "%w %model' (-> & Hmodel₂) !>". iSplitL.
        - repeat iExists _. iSplit; first done. repeat iExists _. naive_solver.
        - iIntros "HΦ". iApply ("HΦ" with "[//]").
      }
      clear- Hbranch1 Hbranch3.

      wp_pures.

      (* → [if: #(bool_decide (front1 < back2))] *)
      rewrite bool_decide_eq_true_2; first done.

      (* → [!#l.[prophet]] *)
      wp_load.

      wp_pures.

      (* → [Resolve (Cas #l.[front] #front1 #(front1 + 1)) #γ.(inf_ws_deque_meta_prophet) (#front1, #id)] *)
      wp_bind (Resolve (Cas #l.[front] #front1 #(front1 + 1)) #γ.(inf_ws_deque_meta_prophet) (#front1, #id)%V).
      (* open invariant *)
      iInv "Hinv" as "(%front3 & %back3 & %hist & %model & %priv & %past3 & %prophs3 & Hfront & Hback & Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & >Hprophet_model & >%Hpast3 & Hstate)".
      (* we are in state 2 or state 3.1 *)
      iDestruct (inf_ws_deque_winner₂_state with "Hwinner₂ Hstate") as "(>-> & Hstate)".
      (* do resolve *)
      wp_apply (wise_prophet_wp_resolve inf_ws_deque_prophet (front1, id) with "Hprophet_model"); [done.. |].
      (* Cas must succeed as we are the next winner *)
      wp_cas_suc.
      (* branching 5 *)
      iDestruct "Hstate" as "[Hstate | Hstate]".

      (* branch 5.1: state 2 *)
      - iDestruct "Hstate" as "(%Hstate & Hhist_auth & %Hhist & %id' & %Φ' & %Hprophs3 & Hwinner₁ & Hwinner₂ & Hid' & HΦ')".
        iDestruct (inf_ws_deque_winner_agree ’Some{ v } with "Hwinner₁ Hwinner₂") as "(_ & HΦ & Hwinner₁ & Hwinner₂)".
        iModIntro. iIntros "%prophs3' -> Hprophet_model".
        (* update front *)
        iMod (inf_ws_deque_front_auth_update (S front1) with "Hfront_auth") as "Hfront_auth"; first lia.
        (* begin transaction *)
        iMod "HΦ'" as "(%_model & Hmodel₂ & _ & HΦ')".
        iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
        (* update model values *)
        destruct model as [| _v model]; first naive_solver lia.
        iAssert ⌜_v = v⌝%I as %->.
        { (* exploit history fragment *)
          iDestruct (inf_ws_deque_hist_agree with "Hhist_auth Hhist_elem") as %Hlookup.
          iPureIntro.
          rewrite lookup_app_r in Hlookup; first lia.
          rewrite list_lookup_singleton_Some in Hlookup. naive_solver.
        }
        iMod (inf_ws_deque_model_update model with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        (* end transaction *)
        iMod ("HΦ'" with "[$Hmodel₂ //]") as "HΦ'".
        (* close invariant *)
        iSplitR "HΦ HΦ'".
        { simpl in Hmodel.
          iExists (S front1), back3, (hist ++ [v]), model, priv, (past3 ++ [_]), prophs3'. iFrame.
          iSplitL "Hfront". { assert (front1 + 1 = S front1)%Z as -> by lia. done. }
          iSplitL "Harray_model". { rewrite -(assoc (++)) //. }
          iSplitR; first auto with lia.
          iSplitR.
          { iPureIntro. rewrite Forall_app Forall_singleton. split; last lia.
            eapply Forall_impl; first done. intros (? & ?) ?. lia.
          }
          unfold_state. destruct model as [| w model]; simpl in Hmodel.
          - iModIntro. iLeft. iFrame. iSplit; first auto with lia.
            iSplit. { rewrite app_length /=. auto with lia. }
            repeat iExists _. iFrame.
          - iMod (inf_ws_deque_hist_update w with "Hhist_auth") as "Hhist_auth".
            iModIntro. iRight. iLeft. iFrame. iSplit; first auto with lia.
            iSplit. { rewrite app_length /=. auto with lia. }
            unfold_state. destruct (head $ filter _ prophs3') as [[] |].
            + iLeft. repeat iExists _. iFrame.
            + repeat iExists _. iFrame.
        }
        iModIntro.
        clear- Hbranch1 Hbranch3.

        (* → [array.(inf_array_get) !#l.[data] #front1] *)
        wp_smart_apply (inf_ws_deque_wp_get_hist with "[$Harray_inv $Hinv $Hdata $Hhist_elem]") as "_".

        wp_pures.

        iRewrite -"HΦ". done.

      (* branch 5.2: state 3.1 *)
      - iDestruct "Hstate" as "(-> & Hlock & Hhist_auth & %Hhist & %id' & %Φ' & %Hprophs3 & Hwinner₁ & Hwinner₂ & HΦ')".
        iDestruct (inf_ws_deque_winner_agree ’Some{ v } with "Hwinner₁ Hwinner₂") as "(_ & HΦ & Hwinner₁ & Hwinner₂)".
        iModIntro. iIntros "%prophs3' -> Hprophet_model".
        (* we know there is no model value and [hist !!! front1 = v] *)
        destruct (nil_or_length_pos model) as [-> |]; last lia.
        iAssert ⌜hist !!! front1 = v⌝%I as %->.
        { (* exploit history fragment *)
          iDestruct (inf_ws_deque_hist_agree with "Hhist_auth Hhist_elem") as %Hlookup.
          iPureIntro. apply list_lookup_total_correct. done.
        }
        (* update front *)
        iMod (inf_ws_deque_front_auth_update (S front1) with "Hfront_auth") as "Hfront_auth"; first lia.
        (* close invariant *)
        iModIntro. iSplitR "HΦ HΦ'".
        { iExists (S front1), front1, hist, [], priv, (past3 ++ [_]), prophs3'. iFrame.
          iSplitL "Hfront". { assert (front1 + 1 = S front1)%Z as -> by lia. done. }
          iSplit; first auto with lia.
          iSplitR.
          { iPureIntro. rewrite Forall_app Forall_singleton. split; last lia.
            eapply Forall_impl; first done. intros (? & ?) ?. lia.
          }
          unfold_state. do 2 iRight. iFrame. iRight. do 2 (iSplit; first auto with lia).
          repeat iExists _. iFrame.
        }
        clear- Hbranch1 Hbranch3.

        (* → [array.(inf_array_get) !#l.[data] #front1] *)
        wp_smart_apply (inf_ws_deque_wp_get_hist with "[$Harray_inv $Hinv $Hdata $Hhist_elem]") as "_".

        wp_pures.

        iRewrite -"HΦ". done.
    Qed.

    Lemma inf_ws_deque_pop_spec t ι :
      <<<
        inf_ws_deque_inv t ι ∗
        inf_ws_deque_owner t
      | ∀∀ model,
        inf_ws_deque_model t model
      >>>
        inf_ws_deque_pop t @ ↑ι
      <<<
        ∃∃ o,
        match o with
        | None =>
            ⌜model = []⌝ ∗
            inf_ws_deque_model t []
        | Some v =>
            ∃ model',
            ⌜model = model' ++ [v]⌝ ∗
            inf_ws_deque_model t model'
        end
      | RET o;
        inf_ws_deque_owner t
      >>>.
    Proof.
      iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hdata & #Hpid & #Harray_inv & #Hinv) & (%_l & %_γ & %back & %priv & %Heq & #_Hmeta & Hctl₂ & Hlock)) HΦ". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

      wp_rec.

      (* → [Id] *)
      wp_apply (wp_id with "[//]") as "%id Hid".

      wp_pures.

      (* → [!#l.[back]] *)
      wp_bind (!#l.[back])%E.
      (* open invariant *)
      iInv "Hinv" as "(%front1 & %_back & %hist & %model & %_priv & %past1 & %prophs1 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast1 & Hstate)".
      iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
      (* do load back *)
      wp_load.
      (* close invariant *)
      iModIntro. iSplitR "Hctl₂ Hlock Hid HΦ".
      { repeat iExists _. iFrame. done. }
      clear.

      wp_pures.

      (* → [#l.[back] <- #(back - 1)] *)
      wp_bind (#l.[back] <- #(back - 1))%E.
      (* open invariant *)
      iInv "Hinv" as "(%front2 & %_back & %hist & %model & %_priv & %past2 & %prophs2 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast2 & Hstate)".
      iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
      (* do decrement back *)
      wp_store.
      (* update back in control tokens *)
      iMod (inf_ws_deque_ctl_update (back - 1) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
      (* branching 1 *)
      (* we have lock, hence we are in state 1 or in state 2 *)
      (* if we are in state 2, there is either one model value or strictly more than one model value *)
      iDestruct (inf_ws_deque_lock_state with "Hlock Hstate") as "(Hlock & [Hstate | Hstate])";
        iDestruct "Hstate" as "(%Hstate & Hhist_auth & %Hhist & Hstate)";
        last (destruct (Z.lt_total (S front2) back) as [Hstate' | [Hstate' |]]; last lia).

      (* branch 1.1: [front2 = back]; empty deque *)
      - subst back.
        (* emit front fragment at [front2] *)
        iDestruct (inf_ws_deque_front_lb_get with "Hfront_auth") as "#Hfront_lb".
        (* hence there is no model value *)
        destruct (nil_or_length_pos model) as [-> |]; last lia.
        (* begin transaction *)
        iMod "HΦ" as "(%_model & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
        (* end transaction *)
        iMod ("HΦ" $! None with "[Hmodel₂]") as "HΦ".
        { iSplit; first done. repeat iExists _. naive_solver. }
        (* close invariant *)
        iModIntro. iSplitR "Hctl₂ HΦ".
        { iExists front2, (front2 - 1)%Z, hist, [], priv, past2, prophs2. iFrame.
          do 2 (iSplit; first auto with lia).
          unfold_state. do 2 iRight. iFrame. iRight. iSplit; first auto with lia. naive_solver.
        }
        clear.

        wp_pures.

        (* → [!#l.[front]] *)
        wp_bind (!#l.[front])%E.
        (* open invariant *)
        iInv "Hinv" as "(%front3 & %_back & %hist & %model & %_priv & %past3 & %prophs3 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast3 & Hstate)".
        iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
        (* do load front *)
        wp_load.
        (* we are in state 3.2 *)
        iDestruct (inf_ws_deque_front_state₃₂ with "Hfront_auth Hfront_lb Hstate") as "(-> & Hfront_auth & Hlock & Hstate)"; first done.
        (* close invariant *)
        iModIntro. iSplitR "Hctl₂ HΦ".
        { iExists front2, (front2 - 1)%Z, hist, model, priv, past3, prophs3. iFrame.
          do 2 (iSplit; first auto with lia).
          unfold_state. do 2 iRight. iFrame.
        }
        clear.

        wp_pures.

        (* → [if: #(bool_decide (back - 1 < back))] *)
        rewrite bool_decide_eq_true_2; first lia.

        wp_pures.

        (* → [#l.[back] <- #front2] *)
        wp_bind (#l.[back] <- #front2)%E.
        (* open invariant *)
        iInv "Hinv" as "(%front4 & %_back & %hist & %model & %_priv & %past4 & %prophs4 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast4 & Hstate)".
        iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
        (* do increment back *)
        wp_store.
        (* update back in control tokens *)
        iMod (inf_ws_deque_ctl_update front2 priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
        (* we are in state 3.2 *)
        iDestruct (inf_ws_deque_front_state₃₂ with "Hfront_auth Hfront_lb Hstate") as "(-> & Hfront_auth & Hlock & (%state & Hhist_auth & %Hhist & Hstate))"; first done.
        (* close invariant *)
        iModIntro. iSplitR "Hctl₂ Hlock HΦ".
        { iExists front2, front2, hist, model, priv, past4, prophs4. iFrame.
          do 2 (iSplit; first auto with lia).
          unfold_state. iLeft. iFrame. unfold_state. iFrame. done.
        }
        clear.

        wp_pures.

        iApply "HΦ". repeat iExists _. iFrame "#∗". done.

      (* branch 1.2: front2 + 1 < back; no conflict *)
      - (* there is stricly more than one model value *)
        rename model into _model. destruct (rev_elim _model) as [-> | (model & v & ->)]; first naive_solver lia.
        destruct model as [| w model]; rewrite app_length /= in Hmodel; first lia.
        (* update data model *)
        iEval (rewrite assoc) in "Harray_model".
        iDestruct (inf_array_model'_shift_r with "Harray_model") as "Harray_model".
        (* update private values in control tokens *)
        set (priv' := λ i, match i with 0 => v | S i => priv i end).
        iMod (inf_ws_deque_ctl_update (back - 1) priv' with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
        (* begin transaction *)
        iMod "HΦ" as "(%_model & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂) & (_ & HΦ))". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
        (* update model values *)
        iMod (inf_ws_deque_model_update (w :: model) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        (* end transaction *)
        iMod ("HΦ" $! (Some v) with "[Hmodel₂]") as "HΦ".
        { repeat iExists _. iSplit; first done. repeat iExists _. naive_solver. }
        (* close invariant *)
        iModIntro. iSplitR "Hctl₂ Hlock HΦ".
        { iExists front2, (back - 1)%Z, hist, (w :: model), priv', past2, prophs2. iFrame.
          do 2 (iSplit; first (simpl; auto with lia)).
          unfold_state. iRight. iLeft. iFrame. iSplit; auto with lia.
        }
        clear.

        wp_pures.

        (* → [!#l.[front]] *)
        wp_bind (!#l.[front])%E.
        (* open invariant *)
        iInv "Hinv" as "(%front3 & %_back & %hist & %model & %_priv & %past3 & %prophs3 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast3 & Hstate)".
        iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
        (* do load front *)
        wp_load.
        (* we have lock, hence we are in state 1 or in state 2, hence [front3 ≤ back - 1] *)
        iAssert ⌜front3 ≤ back - 1⌝%I%Z as %Hfront3.
        { iDestruct (inf_ws_deque_lock_state with "Hlock Hstate") as "(Hlock & [Hstate | Hstate])";
            iDestruct "Hstate" as "(%Hstate & _)"; auto with lia.
        }
        (* emit front fragment at [front3] *)
        iDestruct (inf_ws_deque_front_lb_get with "Hfront_auth") as "#Hfront_lb".
        (* close invariant *)
        iModIntro. iSplitR "Hctl₂ Hlock HΦ".
        { repeat iExists _. iFrame. done. }
        clear- Hfront3.

        wp_pures.

        (* → [if: #(bool_decide (back - 1 < front3))] *)
        rewrite bool_decide_eq_false_2; first lia.

        wp_pures.

        (* branching 2 *)
        (* we may or may not have seen an empty deque *)
        rewrite Z.le_lteq in Hfront3. destruct Hfront3 as [Hfront3 | <-].

        (* branch 2.1: [front3 < back - 1] *)
        + (* → [if: #(bool_decide (back - 1 < front3))] *)
          rewrite bool_decide_eq_true_2; first lia.

          (* → [array.(inf_array_get) !#l.[data] #(back - 1)] *)
          wp_smart_apply (inf_ws_deque_wp_get_priv with "[$Harray_inv $Hinv $Hdata $Hctl₂ $Hlock]") as "(Hctl₂ & Hlock)"; first done.

          wp_pures.

          rewrite Z.sub_diag /=.
          iApply "HΦ". repeat iExists _. iFrame "#∗". done.

        (* branch 2.2: [front3 = back - 1] *)
        + (* → [if: #(bool_decide (front3 < front3))] *)
          rewrite bool_decide_eq_false_2; first lia.

          (* → [!#l.[prophet]] *)
          wp_load.

          wp_pures.

          (* → [Resolve (Cas #l.[front] #front3 #(front3 + 1)) #γ.(inf_ws_deque_meta_prophet) (#front3, #id)] *)
          wp_bind (Resolve (Cas #l.[front] #front3 #(front3 + 1)) #γ.(inf_ws_deque_meta_prophet) (#front3, #id)%V).
          (* open invariant *)
          iInv "Hinv" as "(%front4 & %_back & %hist & %model & %_priv & %past4 & %prophs4 & Hfront & Hback & >Hctl₁ & >Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & >Hprophet_model & >%Hpast4 & Hstate)".
          iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
          (* we have lock, hence we are in state 1 or in state 2 *)
          iDestruct (inf_ws_deque_lock_state with "Hlock Hstate") as "(Hlock & [Hstate | Hstate])";
            iDestruct "Hstate" as "(>%Hstate & Hhist_auth & >%Hhist & Hstate)";
            last first.
          { (* state 2 is actually impossible *)
            iDestruct (inf_ws_deque_front_valid with "Hfront_auth Hfront_lb") as %?.
            lia.
          }
          apply (inj _) in Hstate as ->.
          (* do resolve *)
          wp_apply (wise_prophet_wp_resolve inf_ws_deque_prophet (front3, id) with "Hprophet_model"); [done.. |].
          (* Cas must succeed *)
          wp_cas_suc.
          iModIntro. iIntros "%prophs4' -> Hprophet_model".
          (* update front authority *)
          iMod (inf_ws_deque_front_auth_update (S front3) with "Hfront_auth") as "Hfront_auth"; first lia.
          (* emit front fragment at [front3 + 1] *)
          iClear "Hfront_lb".
          iDestruct (inf_ws_deque_front_lb_get with "Hfront_auth") as "#Hfront_lb".
          (* we know there is no model value *)
          destruct (nil_or_length_pos model) as [-> |]; last lia.
          (* update history values *)
          set (hist' := hist ++ [v]).
          iMod (inf_ws_deque_hist_update v with "Hhist_auth") as "Hhist_auth".
          (* emit history fragment at [front3] *)
          iDestruct (inf_ws_deque_hist_elem_get front3 v with "Hhist_auth") as "#Hhist_elem".
          { rewrite lookup_app_r; first lia. rewrite Hhist Nat.sub_diag //. }
          (* update private values in control tokens *)
          iMod (inf_ws_deque_ctl_update front3 priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
          (* update data model *)
          iDestruct (inf_array_model'_shift_l with "Harray_model") as "Harray_model"; first by intros [].
          (* close invariant *)
          iModIntro. iSplitR "Hctl₂ HΦ".
          { iExists (S front3), front3, (hist ++ [v]), [], priv, (past4 ++ [_]), prophs4'. iFrame.
            iSplitL "Hfront". { assert (front3 + 1 = S front3)%Z as -> by lia. done. }
            iSplitL "Harray_model"; first rewrite !right_id //.
            iSplit; first auto with lia.
            iSplit.
            { iPureIntro. rewrite Forall_app Forall_singleton. split; last lia.
              eapply Forall_impl; first done. intros (? & ?) ?. lia.
            }
            unfold_state. do 2 iRight. iFrame. iRight. iFrame. iSplit; first auto with lia.
            rewrite app_length /=. auto with lia.
          }
          clear.

          wp_pures.

          (* → [#l.[back] <- #(front3 + 1)] *)
          wp_bind (#l.[back] <- #(front3 + 1))%E.
          (* open invariant *)
          iInv "Hinv" as "(%front5 & %_back & %hist & %model & %_priv & %past5 & %prophs5 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast5 & Hstate)".
          iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
          (* do increment back *)
          wp_store.
          (* update [back] in control tokens *)
          iMod (inf_ws_deque_ctl_update (front3 + 1) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
          (* we are in state 3.2 *)
          iDestruct (inf_ws_deque_front_state₃₂ with "Hfront_auth Hfront_lb Hstate") as "(-> & Hfront_auth & Hlock & (%Hstate & Hhist_auth & %Hhist & Hstate))"; first lia.
          (* close invariant *)
          iModIntro. iSplitR "Hctl₂ Hlock HΦ".
          { iExists (S front3), (front3 + 1)%Z, hist, model, priv, past5, prophs5. iFrame.
            do 2 (iSplit; first auto with lia).
            unfold_state. iLeft. iFrame. iSplit; first auto with lia. unfold_state. iFrame. done.
          }
          clear.

          (* → [array.(inf_array_get) !#l.[data] #front3] *)
          wp_smart_apply (inf_ws_deque_wp_get_hist with "[$Harray_inv $Hinv $Hdata $Hhist_elem]") as "_".

          wp_pures.

          iApply "HΦ". repeat iExists _. iFrame "#∗". done.

      (* branch 1.3: [front2 + 1 = back]; potential conflict *)
      - subst back.
        assert (S front2 - 1 = front2)%Z as -> by lia.
        destruct model as [| v model]; simpl in Hmodel; first lia.
        destruct model; simpl in Hmodel; last lia.
        (* emit front fragment at [front2] *)
        iDestruct (inf_ws_deque_front_lb_get with "Hfront_auth") as "#Hfront_lb".
        (* emit history fragment at [front2] *)
        iDestruct (inf_ws_deque_hist_elem_get front2 v with "Hhist_auth") as "#Hhist_elem".
        { rewrite lookup_app_r; first lia. rewrite Hhist Nat.sub_diag //. }
        (* emit prophet lower bound at [prophs2] *)
        iDestruct (wise_prophet_lb_get with "Hprophet_model") as "#Hprophet_lb".
        (* branching 2: enforce [filter (λ '(_, _, front', _), front' = front2) prophs2 ≠ []] *)
        unfold_state. destruct (head $ filter _ prophs2) as [(_front2 & id') |] eqn:Hbranch2; first last.
        { (* begin transaction *)
          iMod "HΦ" as "(%_model & (%_l & %_γ & %Heq & _Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
          (* update model values *)
          iMod (inf_ws_deque_model_update [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iDestruct "Hstate" as "(% & % & % & Hwinner₁ & Hwinner₂)".
          (* end transaction *)
          iMod ("HΦ" $! (Some v) with "[Hmodel₂]") as "_".
          { iExists []. iSplit; first done. repeat iExists _. naive_solver. }
          (* update winner tokens *)
          iMod (inf_ws_deque_winner_update front2 Φ with "Hwinner₁ Hwinner₂") as "(Hwinner₁ & Hwinner₂)".
          (* close invariant *)
          iModIntro. iSplitR "Hctl₂ Hwinner₁".
          { iExists front2, front2, (hist ++ [v]), [], priv, past2, prophs2. iFrame.
            iSplitL "Harray_model". { list_simplifier. done. }
            iSplit. { list_simplifier. auto with lia. }
            iSplit; first done.
            unfold_state. do 2 iRight. iFrame. iLeft. iSplit; first done.
            iSplit. { rewrite app_length /=. auto with lia. }
            unfold_state. rewrite Hbranch2. naive_solver.
          }
          clear- Hbranch2.

          wp_pures.

          (* → [!#l.[front]] *)
          wp_bind (!#l.[front])%E.
          (* open invariant *)
          iInv "Hinv" as "(%front3 & %_back & %hist & %model & %_priv & %past3 & %prophs3 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast3 & Hstate)".
          iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
          (* do load front *)
          wp_load.
          (* we are in state 3.1 *)
          iDestruct (inf_ws_deque_winner₁_state with "Hwinner₁ Hstate") as "(-> & _ & Hlock & Hhist_auth & %Hhist & %Φ' & %Hprophs3 & Hwinner₁ & Hwinner₂)".
          (* close invariant *)
          iModIntro. iSplitR "Hctl₂ Hwinner₁".
          { iExists front2, front2, hist, model, priv, past3, prophs3. iFrame.
            do 2 (iSplit; first done).
            unfold_state. do 2 iRight. iFrame. iLeft. do 2 (iSplit; first done).
            unfold_state. rewrite Hprophs3. naive_solver.
          }
          clear- Hbranch2.

          wp_pures.

          (* → [if: #(bool_decide (front2 < front2))] *)
          rewrite bool_decide_eq_false_2; first lia.

          wp_pures.

          (* → [if: #(bool_decide (front2 < front2))] *)
          rewrite bool_decide_eq_false_2; first lia.

          (* → [!#l.[prophet]] *)
          wp_load.

          (* inconsistent prophecy resolution *)
          wp_smart_apply (inf_ws_deque_wp_resolve_inconsistent_1 with "[$Harray_inv $Hinv $Hprophet_lb]") as "% []"; first done.
        }
        (* branching 3 *)
        destruct (decide (id' = id)) as [-> | Hbranch3].

        (* branch 3.1: [id = id']; we are the next winner *)
        + (* begin transaction *)
          iMod "HΦ" as "(%_model & (%_l & %_γ & %Heq & _Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
          (* update model values *)
          iMod (inf_ws_deque_model_update [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          (* end transaction *)
          iMod ("HΦ" $! (Some v) with "[Hmodel₂]") as "HΦ".
          { iExists []. iSplit; first done. repeat iExists _. naive_solver. }
          (* we own the winner tokens *)
          iDestruct "Hstate" as "[(% & % & % & Hwinner₁ & Hwinner₂) | (Hid' & _)]"; last first.
          { iDestruct (identifier_model_exclusive with "Hid Hid'") as %[]. }
          (* update winner tokens *)
          set Ψ := (λ v, inf_ws_deque_owner #l -∗ Φ v)%I.
          iMod (inf_ws_deque_winner_update front2 Ψ with "Hwinner₁ Hwinner₂") as "(Hwinner₁ & Hwinner₂)".
          (* close invariant *)
          iModIntro. iSplitR "Hctl₂ Hwinner₂".
          { iExists front2, front2, (hist ++ [v]), [], priv, past2, prophs2. iFrame.
            iSplitL "Harray_model". { list_simplifier. done. }
            do 2 (iSplit; first (simpl; auto with lia)).
            unfold_state. do 2 iRight. iFrame. iLeft. iSplit; first done.
            iSplit. { rewrite app_length /=. auto with lia. }
            unfold_state. rewrite Hbranch2. iFrame. iExists Ψ. iFrame.
            rewrite lookup_total_app_r; first lia. rewrite Hhist Nat.sub_diag //.
          }
          clear- Hbranch2.

          wp_pures.

          (* → [!#l.[front]] *)
          wp_bind (!#l.[front])%E.
          (* open invariant *)
          iInv "Hinv" as "(%front3 & %_back & %hist & %model & %_priv & %past3 & %prophs3 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast3 & Hstate)".
          iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
          (* do load front *)
          wp_load.
          (* we are in state 3.1, hence [front3 = front2] *)
          iAssert ⌜front3 = front2⌝%I as %->.
          { iDestruct (inf_ws_deque_winner₂_state' with "Hwinner₂ Hstate") as "($ & _)". }
          (* close invariant *)
          iModIntro. iSplitR "Hctl₂ Hwinner₂".
          { repeat iExists front2, front2, hist, model, priv, past3, prophs3. iFrame. done. }
          clear- Hbranch2.

          wp_pures.

          (* → [if: #(bool_decide (front2 < front2))] *)
          rewrite bool_decide_eq_false_2; first lia.

          wp_pures.

          (* → [if: #(bool_decide (front2 < front2))] *)
          rewrite bool_decide_eq_false_2; first lia.

          (* → [!#l.[prophet]] *)
          wp_load.

          wp_pures.

          (* → [Resolve (Cas #l.[front] #front2 #(front2 + 1)) #γ.(inf_ws_deque_meta_prophet) (#front2, #id)] *)
          wp_bind (Resolve (Cas #l.[front] #front2 #(front2 + 1)) #γ.(inf_ws_deque_meta_prophet) (#front2, #id)%V).
          (* open invariant *)
          iInv "Hinv" as "(%front4 & %_back & %hist & %model & %_priv & %past4 & %prophs4 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & >Hprophet_model & >%Hpast4 & Hstate)".
          iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
          (* we are in state 3.1 *)
          iDestruct (inf_ws_deque_winner₂_state' with "Hwinner₂ Hstate") as "(>-> & Hlock & >Hhist_auth & >%Hhist & %id' & %Ψ' & >%Hprophs4 & Hwinner₁ & Hwinner₂ & HΨ')".
          iDestruct (inf_ws_deque_winner_agree ’Some{ v } with "Hwinner₁ Hwinner₂") as "(_ & HΨ & Hwinner₁ & Hwinner₂)".
          (* exploit history fragment *)
          iDestruct (inf_ws_deque_hist_agree with "Hhist_auth Hhist_elem") as %->%list_lookup_total_correct.
          (* do resolve *)
          wp_apply (wise_prophet_wp_resolve inf_ws_deque_prophet (front2, id) with "Hprophet_model"); [done.. |].
          (* Cas must succeed *)
          wp_cas_suc.
          iModIntro. iIntros "%prophs4' -> Hprophet_model".
          (* update front authority *)
          iMod (inf_ws_deque_front_auth_update (S front2) with "Hfront_auth") as "Hfront_auth"; first lia.
          (* emit front fragment at [front2 + 1] *)
          iClear "Hfront_lb".
          iDestruct (inf_ws_deque_front_lb_get with "Hfront_auth") as "#Hfront_lb".
          (* close invariant *)
          iModIntro. iSplitR "Hctl₂ HΨ HΨ'".
          { iExists (S front2), front2, hist, model, priv, (past4 ++ [_]), prophs4'. iFrame.
            iSplitL "Hfront". { assert (front2 + 1 = S front2)%Z as -> by lia. done. }
            iSplit; first auto with lia.
            iSplit.
            { iPureIntro. rewrite Forall_app Forall_singleton. split; last lia.
              eapply Forall_impl; first done. intros (? & ?) ?. lia.
            }
            unfold_state. do 2 iRight. iFrame. iRight. do 2 (iSplit; first auto with lia). repeat iExists _. iFrame.
          }
          clear- Hbranch2.

          wp_pures.

          (* → [#l.[back] <- #(front2 + 1)] *)
          wp_bind (#l.[back] <- #(front2 + 1))%E.
          (* open invariant *)
          iInv "Hinv" as "(%front5 & %_back & %hist & %model & %_priv & %past5 & %prophs5 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast5 & Hstate)".
          iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
          (* do increment back *)
          wp_store.
          (* update [back] in control tokens *)
          iMod (inf_ws_deque_ctl_update (front2 + 1) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
          (* we are in state 3.2 *)
          iDestruct (inf_ws_deque_front_state₃₂ with "Hfront_auth Hfront_lb Hstate") as "(-> & Hfront_auth & Hlock & (%Hstate & Hhist_auth & %Hhist & Hstate))"; first lia.
          (* close invariant *)
          iModIntro. iSplitR "Hctl₂ Hlock HΨ HΨ'".
          { iExists (S front2), (front2 + 1)%Z, hist, model, priv, past5, prophs5. iFrame.
            do 2 (iSplit; first auto with lia).
            unfold_state. iLeft. iFrame. iSplit; first auto with lia. unfold_state. iFrame. done.
          }
          clear- Hbranch2.

          (* → [array.(inf_array_get) !#l.[data] #front2] *)
          wp_smart_apply (inf_ws_deque_wp_get_hist with "[$Harray_inv $Hinv $Hdata $Hhist_elem]") as "_".

          wp_pures.

          iRewrite "HΨ" in "HΨ'". iApply "HΨ'". repeat iExists _. iFrame "#∗". done.

        (* branch 3.2: [id ≠ id']; we are not the next winner *)
        + (* branching 4 *)
          iDestruct "Hstate" as "[Hstate | Hstate]".

          (* branch 4.1: winning thief did not show up; contradiction *)
          * iDestruct "Hstate" as "(% & % & % & Hwinner₁ & Hwinner₂)".
            (* begin transaction *)
            iMod "HΦ" as "(%_model & (%_l & %_γ & %Heq & _Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
            iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
            iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
            (* update model values *)
            iMod (inf_ws_deque_model_update [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
            (* end transaction *)
            iMod ("HΦ" $! (Some v) with "[Hmodel₂]") as "HΦ".
            { iExists []. iSplit; first done. repeat iExists _. naive_solver. }
            (* update winner tokens *)
            set Ψ := (λ v, inf_ws_deque_owner #l -∗ Φ v)%I.
            iMod (inf_ws_deque_winner_update front2 Ψ with "Hwinner₁ Hwinner₂") as "(Hwinner₁ & Hwinner₂)".
            (* close invariant *)
            iModIntro. iSplitR "Hctl₂ Hwinner₂".
            { iExists front2, front2, (hist ++ [v]), [], priv, past2, prophs2. iFrame.
              iSplitL "Harray_model". { list_simplifier. done. }
              iSplit. { list_simplifier. auto with lia. }
              iSplit; first done.
              unfold_state. do 2 iRight. iFrame. iLeft. iSplit; first done.
              iSplit. { rewrite app_length /=. auto with lia. }
              unfold_state. rewrite Hbranch2. iFrame. iExists Ψ. iFrame.
              rewrite lookup_total_app_r; first lia. rewrite Hhist Nat.sub_diag //.
            }
            clear- Hbranch2 Hbranch3.

            wp_pures.

            (* → [!#l.[front]] *)
            wp_bind (!#l.[front])%E.
            (* open invariant *)
            iInv "Hinv" as "(%front3 & %_back & %hist & %model & %_priv & %past3 & %prophs3 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast3 & Hstate)".
            iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
            (* do load front *)
            wp_load.
            (* we are in state 3.1, hence [front3 = front2] *)
            iAssert ⌜front3 = front2⌝%I as %->.
            { iDestruct (inf_ws_deque_winner₂_state' with "Hwinner₂ Hstate") as "($ & _)". }
            (* close invariant *)
            iModIntro. iSplitR "Hctl₂ Hwinner₂".
            { repeat iExists front2, front2, hist, model, priv, past3, prophs3. iFrame. done. }
            clear- Hbranch2 Hbranch3.

            wp_pures.

            (* → [if: #(bool_decide (front2 < front2))] *)
            rewrite bool_decide_eq_false_2; first lia.

            wp_pures.

            (* → [if: #(bool_decide (front2 < front2))] *)
            rewrite bool_decide_eq_false_2; first lia.

            (* → [!#l.[prophet]] *)
            wp_load.

            (* inconsistent prophecy resolution *)
            wp_smart_apply (inf_ws_deque_wp_resolve_inconsistent_2 with "[$Harray_inv $Hinv $Hctl₂ $Hfront_lb $Hprophet_lb $Hwinner₂]"); [done.. |]. iIntros "[]".

          (* branch 4.2: winning thief did show up *)
          * iDestruct "Hstate" as "(Hid' & %Φ' & Hwinner₁ & HΦ')".
            (* begin transaction *)
            iMod "HΦ'" as "(%_model & Hmodel₂ & _ & HΦ')".
            iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
            (* update model values *)
            iMod (inf_ws_deque_model_update [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
            (* end transaction *)
            iMod ("HΦ'" $! v with "[$Hmodel₂ //]") as "HΦ'".
            (* begin transaction *)
            iMod "HΦ" as "(%_model & (%_l & %_γ & %Heq & _Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
            iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
            iDestruct (inf_ws_deque_model_agree with "Hmodel₁ Hmodel₂") as %<-.
            (* end transaction *)
            iMod ("HΦ" $! None with "[Hmodel₂]") as "HΦ".
            { iSplit; first done. repeat iExists _. iFrame "#∗". done. }
            (* close invariant *)
            iModIntro. iSplitR "Hctl₂ HΦ".
            { iExists front2, front2, (hist ++ [v]), [], priv, past2, prophs2. iFrame.
              iSplitL "Harray_model". { list_simplifier. done. }
              iSplit. { list_simplifier. auto with lia. }
              iSplit; first done.
              unfold_state. do 2 iRight. iFrame. iLeft. iSplit; first done.
              iSplit. { rewrite app_length /=. auto with lia. }
              unfold_state. rewrite Hbranch2. iFrame. iExists Φ'. iFrame.
              rewrite lookup_total_app_r; first lia. rewrite Hhist Nat.sub_diag //.
            }
            clear- Hbranch2 Hbranch3.

            wp_pures.

            (* → [!#l.[front]] *)
            wp_bind (!#l.[front])%E.
            (* open invariant *)
            iInv "Hinv" as "(%front3 & %_back & %hist & %model & %_priv & %past3 & %prophs3 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast3 & Hstate)".
            iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
            (* do load front *)
            wp_load.
            (* we are in state 3 *)
            unfold_state. iDestruct "Hstate" as "[Hstate | [Hstate | Hstate]]";
              [iDestruct "Hstate" as "(%Hstate & Hhist_auth & %Hhist & Hstate)".. |].
            { simplify- front3.
              (* exploit history fragment *)
              iDestruct (inf_ws_deque_hist_agree with "Hhist_auth Hhist_elem") as %?%lookup_lt_Some.
              lia.
            } {
              iDestruct (inf_ws_deque_front_valid with "Hfront_auth Hfront_lb") as %?.
              lia.
            }
            (* branching 5 *)
            iDestruct "Hstate" as "(Hlock & [Hstate | Hstate])";
              iDestruct "Hstate" as "(%Hstate & Hhist_auth & %Hhist & Hstate)".

            (* branch 5.1: state 3.1; winning thief has not won yet *)
            --- apply (inj _) in Hstate as ->.
                (* close invariant *)
                iModIntro. iSplitR "Hctl₂ HΦ".
                { iExists front2, front2, hist, model, priv, past3, prophs3. iFrame.
                  do 2 (iSplit; first done).
                  unfold_state. do 2 iRight. iFrame. iLeft. auto with iFrame.
                }
                clear- Hbranch2 Hbranch3.

                wp_pures.

                (* → [if: #(bool_decide (front2 < front2))] *)
                rewrite bool_decide_eq_false_2; first lia.

                wp_pures.

                (* → [if: #(bool_decide (front2 < front2))] *)
                rewrite bool_decide_eq_false_2; first lia.

                (* → [!#l.[prophet]] *)
                wp_load.

                (* Cas must fail as we are not the winner *)
                wp_smart_apply (inf_ws_deque_wp_resolve_loser with "[$Harray_inv $Hinv $Hfront_lb $Hprophet_lb]"); [done.. |]. iClear "Hfront_lb". iIntros "Hfront_lb".

                wp_pures.

                (* → [#l.[back] <- #(front2 + 1)] *)
                wp_bind (#l.[back] <- #(front2 + 1))%E.
                (* open invariant *)
                iInv "Hinv" as "(%front5 & %_back & %hist & %model & %_priv & %past5 & %prophs5 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast5 & Hstate)".
                iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
                (* do increment back *)
                wp_store.
                (* update back in control tokens *)
                iMod (inf_ws_deque_ctl_update (S front2) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
                (* we are in state 3.2 *)
                iDestruct (inf_ws_deque_front_state₃₂ with "Hfront_auth Hfront_lb Hstate") as "(-> & Hfront_auth & Hlock & (%state & Hhist_auth & %Hhist & Hstate))"; first lia.
                (* close invariant *)
                iModIntro. iSplitR "Hctl₂ Hlock HΦ".
                { iExists (S front2), (S front2), hist, model, priv, past5, prophs5. iFrame.
                  iSplitL "Hback". { assert (front2 + 1 = S front2)%Z as -> by lia. done. }
                  do 2 (iSplit; first auto with lia).
                  unfold_state. iLeft. iFrame. unfold_state. iFrame. done.
                }
                clear- Hbranch2 Hbranch3.

                wp_pures.

                iApply "HΦ". repeat iExists _. iFrame "#∗". done.

            (* branch 5.2: state 3.2; winning thief has already won *)
            --- assert (front3 = S front2) as -> by lia.
                (* emit front fragment at [front2 + 1] *)
                iClear "Hfront_lb".
                iDestruct (inf_ws_deque_front_lb_get with "Hfront_auth") as "#Hfront_lb".
                (* close invariant *)
                iModIntro. iSplitR "Hctl₂ HΦ".
                { iExists (S front2), front2, hist, model, priv, past3, prophs3. iFrame.
                  do 2 (iSplit; first done).
                  unfold_state. do 2 iRight. iFrame. iRight. auto with iFrame.
                }
                clear- Hbranch2 Hbranch3.

                wp_pures.

                (* → [if: #(bool_decide (front2 < front2 + 1))] *)
                rewrite bool_decide_eq_true_2; first lia.

                wp_pures.

                (* → [#l.[back] <- #(front2 + 1)] *)
                wp_bind (#l.[back] <- #(S front2))%E.
                (* open invariant *)
                iInv "Hinv" as "(%front4 & %_back & %hist & %model & %_priv & %past4 & %prophs4 & Hfront & Hback & >Hctl₁ & Hfront_auth & Harray_model & Hmodel₁ & >%Hmodel & Hprophet_model & >%Hpast4 & Hstate)".
                iDestruct (inf_ws_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
                (* do increment back *)
                wp_store.
                (* update back in control tokens *)
                iMod (inf_ws_deque_ctl_update (S front2) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
                (* we are in state 3.2 *)
                iDestruct (inf_ws_deque_front_state₃₂ with "Hfront_auth Hfront_lb Hstate") as "(-> & Hfront_auth & Hlock & (%state & Hhist_auth & %Hhist & Hstate))"; first lia.
                (* close invariant *)
                iModIntro. iSplitR "Hctl₂ Hlock HΦ".
                { iExists (S front2), (S front2), hist, model, priv, past4, prophs4. iFrame.
                  do 2 (iSplit; first auto with lia).
                  unfold_state. iLeft. iFrame. unfold_state. iFrame. done.
                }
                clear- Hbranch2 Hbranch3.

                wp_pures.

                iApply "HΦ". repeat iExists _. iFrame "#∗". done.
    Qed.
  End inf_ws_deque_G.

  #[global] Opaque inf_ws_deque_create.
  #[global] Opaque inf_ws_deque_push.
  #[global] Opaque inf_ws_deque_steal.
  #[global] Opaque inf_ws_deque_pop.

  #[global] Opaque inf_ws_deque_inv.
  #[global] Opaque inf_ws_deque_model.
  #[global] Opaque inf_ws_deque_owner.
End raw.

Definition inf_ws_deque_create :=
  raw.inf_ws_deque_create.

Definition inf_ws_deque_push : val :=
  λ: "t" "v",
    raw.inf_ws_deque_push "t" (ref "v").

Definition inf_ws_deque_steal : val :=
  λ: "t",
    match: raw.inf_ws_deque_steal "t" with
    | None =>
        None
    | Some "slot" =>
        ‘Some{ !"slot" }
    end.

Definition inf_ws_deque_pop : val :=
  λ: "t",
    match: raw.inf_ws_deque_pop "t" with
    | None =>
        None
    | Some "slot" =>
        ‘Some{ !"slot" }
    end.

Section inf_ws_deque_G.
  Context `{inf_ws_deque_G : InfWsDequeG Σ}.

  Definition inf_ws_deque_inv t :=
    raw.inf_ws_deque_inv t.

  Definition inf_ws_deque_model t vs : iProp Σ :=
      ∃ slots,
      raw.inf_ws_deque_model t (#@{location} <$> slots) ∗
      [∗ list] slot; v ∈ slots; vs,
        slot ↦ v.

  Definition inf_ws_deque_owner t :=
    raw.inf_ws_deque_owner t.

  #[global] Instance inf_ws_deque_model_timeless t model :
    Timeless (inf_ws_deque_model t model).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_ws_deque_owner_timeless t :
    Timeless (inf_ws_deque_owner t).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_ws_deque_inv_persistent t ι :
    Persistent (inf_ws_deque_inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma inf_ws_deque_owner_exclusive t :
    inf_ws_deque_owner t -∗
    inf_ws_deque_owner t -∗
    False.
  Proof.
    apply raw.inf_ws_deque_owner_exclusive.
  Qed.

  Lemma inf_ws_deque_create_spec ι :
    {{{ True }}}
      inf_ws_deque_create ()
    {{{ t,
      RET t;
      inf_ws_deque_inv t ι ∗
      inf_ws_deque_model t [] ∗
      inf_ws_deque_owner t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (raw.inf_ws_deque_create_spec with "[//]") as (t) "(#Hinv & Hmodel & Howner)".
    iSteps. iExists []. iSteps.
  Qed.

  Lemma inf_ws_deque_push_spec t ι v :
    <<<
      inf_ws_deque_inv t ι ∗
      inf_ws_deque_owner t
    | ∀∀ model,
      inf_ws_deque_model t model
    >>>
      inf_ws_deque_push t v @ ↑ι
    <<<
      inf_ws_deque_model t (model ++ [v])
    | RET ();
      inf_ws_deque_owner t
    >>>.
  Proof.
    iIntros "!> %Φ (#Hinv & Howner) HΦ".
    wp_rec. wp_alloc slot as "Hslot".
    awp_apply (raw.inf_ws_deque_push_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%slots & Hmodel & Hslots)".
    iAaccIntro with "Hmodel"; iIntros "Hmodel !>"; first iSteps.
    iSplitL; last iSteps. rewrite -fmap_snoc. iExists _. auto with iFrame.
  Qed.

  Lemma inf_ws_deque_steal_spec t ι :
    <<<
      inf_ws_deque_inv t ι
    | ∀∀ model,
      inf_ws_deque_model t model
    >>>
      inf_ws_deque_steal t @ ↑ι
    <<<
      inf_ws_deque_model t (tail model)
    | RET head model; True
    >>>.
  Proof.
    iIntros "!> %Φ #Hinv HΦ".
    wp_rec.
    awp_smart_apply (raw.inf_ws_deque_steal_spec with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%slots & Hmodel & Hslots)".
    iAaccIntro with "Hmodel"; iIntros "Hmodel !>"; first iSteps.
    destruct slots as [| slot slots], vs as [| v vs]; try done.
    - iSplitL; last iSteps. iExists _. auto.
    - iDestruct "Hslots" as "(Hslot & Hslots)".
      iSplitR "Hslot"; first iSteps. iIntros "HΦ !> _".
      wp_load. iSteps.
  Qed.

  Lemma inf_ws_deque_pop_spec t ι :
    <<<
      inf_ws_deque_inv t ι ∗
      inf_ws_deque_owner t
    | ∀∀ model,
      inf_ws_deque_model t model
    >>>
      inf_ws_deque_pop t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜model = []⌝ ∗
          inf_ws_deque_model t []
      | Some v =>
          ∃ model',
          ⌜model = model' ++ [v]⌝ ∗
          inf_ws_deque_model t model'
      end
    | RET o;
      inf_ws_deque_owner t
    >>>.
  Proof.
    iIntros "!> %Φ (#Hinv & Howner) HΦ".
    wp_rec.
    awp_smart_apply (raw.inf_ws_deque_pop_spec with "[$Hinv $Howner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%slots & Hmodel & Hslots)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([w |]).
    - iIntros "(%ws & %Heq & Hmodel) !>".
      destruct (rev_elim slots) as [-> | (slots' & slot & ->)].
      { rewrite fmap_nil in Heq. edestruct app_cons_not_nil. done. }
      rewrite fmap_app app_inj_tail_iff in Heq. destruct Heq as (<- & <-).
      destruct (rev_elim vs) as [-> | (vs' & v & ->)].
      { iDestruct (big_sepL2_nil_inv_r with "Hslots") as %?.
        edestruct app_cons_not_nil. done.
      }
      iDestruct (big_sepL2_snoc with "Hslots") as "(Hslots & Hslot)".
      iExists (Some v). iSplitR "Hslot"; first iSteps. iIntros "HΦ !> Howner".
      wp_load. iSteps.
    - iIntros "(%Heq & Hmodel) !>".
      apply fmap_nil_inv in Heq as ->. iDestruct (big_sepL2_nil_inv_l with "Hslots") as %->.
      iExists None. iSplitL; last iSteps. iSplit; first iSteps. iExists _. auto.
  Qed.
End inf_ws_deque_G.

#[global] Opaque inf_ws_deque_create.
#[global] Opaque inf_ws_deque_push.
#[global] Opaque inf_ws_deque_steal.
#[global] Opaque inf_ws_deque_pop.

#[global] Opaque inf_ws_deque_inv.
#[global] Opaque inf_ws_deque_model.
#[global] Opaque inf_ws_deque_owner.
