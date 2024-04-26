(* Based on:
   https://github.com/ocaml-multicore/domainslib/blob/731f08891c87e788f2cc95f2a600328f6682a5e2/lib/multi_channel.ml
*)

From zebre Require Import
  prelude.
From zebre.common Require Import
  list.
From zebre.iris.bi Require Import
  big_op.
From zebre.iris.base_logic Require Import
  lib.twins.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  math
  opt
  array
  random_round.
From zebre.saturn Require Import
  mpmc_queue_1.
From zebre.parabstr Require Export
  base.
From zebre.parabstr Require Import
  ws_deques
  waiters.
From zebre Require Import
  options.

Implicit Types yield : bool.
Implicit Types l : location.
Implicit Types v t : val.
Implicit Types vs : gmultiset val.

#[local] Notation "'deques'" := (
in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'foreign'" := (
  in_type "t" 1
)(in custom zebre_field
).
#[local] Notation "'rounds'" := (
  in_type "t" 2
)(in custom zebre_field
).
#[local] Notation "'waiters'" := (
  in_type "t" 3
)(in custom zebre_field
).

Section ws_deques.
  Context `{zebre_G : !ZebreG Σ}.
  Context (ws_deques : ws_deques Σ).

  Definition ws_hub_create : val :=
    λ: "sz",
      { ws_deques.(ws_deques_create) "sz";
        mpmc_queue_create ();
        array_init "sz" (λ: <>, random_round_create (positive_part ("sz" - #1)));
        waiters_create ()
      }.

  #[local] Definition ws_hub_notify : val :=
    λ: "t",
      waiters_notify "t".{waiters}.

  Definition ws_hub_push : val :=
    λ: "t" "i" "v",
      ws_deques.(ws_deques_push) "t".{deques} "i" "v" ;;
      ws_hub_notify "t".

  #[using="ws_deques"]
  Definition ws_hub_push_foreign : val :=
    λ: "t" "v",
      mpmc_queue_push "t".{foreign} "v" ;;
      ws_hub_notify "t".

  Definition ws_hub_pop : val :=
    λ: "t" "i",
      ws_deques.(ws_deques_pop) "t".{deques} "i".

  #[local] Definition ws_hub_try_steal_once : val :=
    λ: "t" "i",
      let: "round" := array_unsafe_get "t".{rounds} "i" in
      random_round_reset "round" ;;
      ws_deques_steal_as ws_deques "t".{deques} "i" "round".

  #[local] Definition ws_hub_try_steal_aux yield : val :=
    rec: "ws_hub_try_steal_aux" "t" "i" "max_round" :=
      if: "max_round" ≤ #0 then (
        §None
      ) else (
        match: mpmc_queue_pop "t".{foreign} with
        | Some <> as "res" =>
            "res"
        | None =>
            match: ws_hub_try_steal_once "t" "i" with
            | Some <> as "res" =>
                "res"
            | None =>
                (if yield then Yield else ()) ;;
                "ws_hub_try_steal_aux" "t" "i" ("max_round" - #1)
            end
        end
      ).
  Definition ws_hub_try_steal : val :=
    λ: "t" "i" "max_round",
      match: ws_hub_try_steal_aux false "t" "i" "max_round".<0> with
      | Some <> as "res" =>
          "res"
      | None =>
          ws_hub_try_steal_aux true "t" "i" "max_round".<1>
      end.

  Definition ws_hub_pop_try_steal : val :=
    λ: "t" "i" "max_round",
      match: ws_hub_pop "t" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          ws_hub_try_steal "t" "i" "max_round"
      end.

  Definition ws_hub_steal : val :=
    rec: "ws_hub_steal" "t" "i" "max_round" :=
      match: ws_hub_try_steal "t" "i" "max_round" with
      | Some "v" =>
          "v"
      | None =>
          let: "waiters" := "t".{waiters} in
          let: "waiter" := waiters_prepare_wait "waiters" in
          match: ws_hub_try_steal_once "t" "i" with
          | Some "v" =>
              waiters_cancel_wait "waiters" "waiter" ;;
              "v"
          | None =>
              waiters_commit_wait "waiters" "waiter" ;;
              "ws_hub_steal" "t" "i" "max_round"
          end
      end.

  Definition ws_hub_pop_steal : val :=
    λ: "t" "i" "max_round",
      match: ws_hub_pop "t" "i" with
      | Some "v" =>
          "v"
      | None =>
          ws_hub_steal "t" "i" "max_round"
      end.
End ws_deques.

Class WsHubG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] ws_hub_G_queue_G :: MpmcQueueG Σ ;
  #[local] ws_hub_G_waiters_G :: WaitersG Σ ;
  #[local] ws_hub_G_model_G :: TwinsG Σ (leibnizO (gmultiset val)) ;
}.

Definition ws_hub_Σ := #[
  mpmc_queue_Σ ;
  waiters_Σ ;
  twins_Σ (leibnizO (gmultiset val))
].
#[global] Instance subG_ws_hub_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG ws_hub_Σ Σ →
  WsHubG Σ.
Proof.
  solve_inG.
Qed.

Section ws_hub_G.
  Context `{ws_hub_G : WsHubG Σ}.
  Context (ws_deques : ws_deques Σ).

  Record ws_hub_meta := {
    ws_hub_meta_size : nat ;
    ws_hub_meta_deques : val ;
    ws_hub_meta_foreign : val ;
    ws_hub_meta_rounds : val ;
    ws_hub_meta_waiters : val ;
    ws_hub_meta_model : gname ;
  }.
  Implicit Types γ : ws_hub_meta.

  #[local] Instance ws_hub_meta_eq_dec :
    EqDecision ws_hub_meta.
  Proof.
    solve_decision.
  Qed.
  #[local] Instance ws_hub_meta_countable :
    Countable ws_hub_meta.
  Proof.
    pose encode γ := (
      γ.(ws_hub_meta_size),
      γ.(ws_hub_meta_deques),
      γ.(ws_hub_meta_foreign),
      γ.(ws_hub_meta_rounds),
      γ.(ws_hub_meta_waiters),
      γ.(ws_hub_meta_model)
    ).
    pose decode := λ '(γ_size, γ_deques, γ_foreign, γ_rounds, γ_waiters, γ_model), {|
      ws_hub_meta_size := γ_size ;
      ws_hub_meta_deques := γ_deques ;
      ws_hub_meta_foreign := γ_foreign ;
      ws_hub_meta_rounds := γ_rounds ;
      ws_hub_meta_waiters := γ_waiters ;
      ws_hub_meta_model := γ_model ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition ws_hub_model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition ws_hub_model₁ γ vs :=
    ws_hub_model₁' γ.(ws_hub_meta_model) vs.
  #[local] Definition ws_hub_model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition ws_hub_model₂ γ vs :=
    ws_hub_model₂' γ.(ws_hub_meta_model) vs.

  #[local] Definition ws_hub_inv_inner γ : iProp Σ :=
    ∃ vs vss vs_foreign,
    ⌜vs = foldr (λ vs_deques vs, list_to_set_disj vs_deques ⊎ vs) (list_to_set_disj vs_foreign) vss⌝ ∗
    ws_deques.(ws_deques_model) γ.(ws_hub_meta_deques) vss ∗
    mpmc_queue_model γ.(ws_hub_meta_foreign) vs_foreign ∗
    ws_hub_model₂ γ vs.
  Definition ws_hub_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[deques] ↦□ γ.(ws_hub_meta_deques) ∗
    l.[foreign] ↦□ γ.(ws_hub_meta_foreign) ∗
    l.[waiters] ↦□ γ.(ws_hub_meta_waiters) ∗
    ws_deques.(ws_deques_inv) γ.(ws_hub_meta_deques) (ι.@"deques") γ.(ws_hub_meta_size) ∗
    mpmc_queue_inv γ.(ws_hub_meta_foreign) (ι.@"foreign") ∗
    waiters_inv γ.(ws_hub_meta_waiters) ∗
    inv (ι.@"inv") (ws_hub_inv_inner γ).

  #[using="ws_deques"]
  Definition ws_hub_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ws_hub_model₁ γ vs.

  Definition ws_hub_owner t i : iProp Σ :=
    ∃ l γ round n,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[rounds] ↦□ γ.(ws_hub_meta_rounds) ∗
    ws_deques.(ws_deques_owner) γ.(ws_hub_meta_deques) i ∗
    array_slice γ.(ws_hub_meta_rounds) γ.(ws_hub_meta_size) i DfracDiscarded [round] ∗
    random_round_model' round (γ.(ws_hub_meta_size) - 1) n.

  #[global] Instance ws_hub_model_timeless t vs :
    Timeless (ws_hub_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_hub_inv_persistent t ι :
    Persistent (ws_hub_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma ws_hub_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      ws_hub_model₁' γ_model ∅ ∗
      ws_hub_model₂' γ_model ∅.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma ws_hub_model_agree γ vs1 vs2 :
    ws_hub_model₁ γ vs1 -∗
    ws_hub_model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma ws_hub_model_update {γ vs1 vs2} vs :
    ws_hub_model₁ γ vs1 -∗
    ws_hub_model₂ γ vs2 ==∗
      ws_hub_model₁ γ vs ∗
      ws_hub_model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  Lemma ws_hub_owner_exclusive t i :
    ws_hub_owner t i -∗
    ws_hub_owner t i -∗
    False.
  Proof.
    iIntros "(%l & %γ & %rounds & %n & -> & #Hmeta & _ & Howner1 & _) (%_l & %_γ & %_rounds & %_n & %Heq & #_Hmeta & _ & Howner2 & _)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iApply (ws_deques_owner_exclusive with "Howner1 Howner2").
  Qed.

  Lemma ws_hub_create_spec ι sz :
    (0 ≤ sz)%Z →
    {{{ True }}}
      ws_hub_create ws_deques #sz
    {{{ t,
      RET t;
      ws_hub_inv t ι ∗
      ws_hub_model t ∅ ∗
      [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ws_hub_owner t i
    }}}.
  Proof.
    set sz' := Z.to_nat sz.

    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.

    wp_smart_apply (ws_deques_create_spec with "[//]") as (deques) "(#Hdeques_inv & Hdeques_model & Hdeques_owner)"; first done.
    wp_apply (mpmc_queue_create_spec with "[//]") as (foreign) "(#Hforeign_inv & Hforeign_model)".
    wp_smart_apply (array_init_spec_disentangled (λ _ round, random_round_model' round (sz' - 1) (sz' - 1))) as (v_rounds rounds) "(%Hrounds & Hv_rounds & Hrounds)"; first done.
    { iIntros "!> %i %Hi".
      wp_smart_apply positive_part_spec.
      wp_apply (random_round_create_spec' with "[//]"); first lia.
      rewrite Nat2Z.id. assert (Z.to_nat (sz - 1) = sz' - 1) as -> by lia.
      iSteps.
    }
    wp_apply (waiters_create_spec with "[//]") as (waiters) "#Hwaiters_inv".

    wp_record l as "Hmeta" "(Hl_deques & Hl_foreign & Hl_rounds & Hl_waiters & _)".
    iMod (pointsto_persist with "Hl_deques") as "#Hl_deques".
    iMod (pointsto_persist with "Hl_foreign") as "#Hl_foreign".
    iMod (pointsto_persist with "Hl_rounds") as "#Hl_rounds".
    iMod (pointsto_persist with "Hl_waiters") as "#Hl_waiters".

    iMod ws_hub_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      ws_hub_meta_size := sz' ;
      ws_hub_meta_deques := deques ;
      ws_hub_meta_foreign := foreign ;
      ws_hub_meta_rounds := v_rounds ;
      ws_hub_meta_waiters := waiters ;
      ws_hub_meta_model := γ_model ;
    |}.

    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hdeques_owner Hv_rounds Hrounds"; iSteps.
    - assert (∀ sz, foldr (λ vs_deques vs, list_to_set_disj vs_deques ⊎ vs) ∅ (replicate sz []) = ∅) as ->.
      { clear. induction sz as [| sz IH]; first done. rewrite /= left_id //. }
      iSteps.
    - iMod (array_model_persist with "Hv_rounds") as "Hv_rounds".
      iDestruct (array_model_atomize with "Hv_rounds") as "Hv_rounds".
      iDestruct (big_sepL_sep_2 with "Hv_rounds Hrounds") as "Hrounds".
      iDestruct (big_sepL_seq_index rounds with "Hdeques_owner") as "Hdeques_owner"; first done.
      iDestruct (big_sepL_sep_2 with "Hdeques_owner Hrounds") as "H".
      iApply (big_sepL_seq_index rounds); first done.
      iApply (big_sepL_impl with "H").
      rewrite Hrounds. iSteps.
  Qed.

  #[local] Lemma ws_hub_notify_spec t ι :
    {{{
      ws_hub_inv t ι
    }}}
      ws_hub_notify t
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & -> & #Hmeta & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv) HΦ".

    wp_rec. wp_load.
    wp_apply (waiters_notify_spec with "Hwaiters_inv HΦ").
  Qed.

  Lemma ws_hub_push_spec t ι i v :
    (0 ≤ i)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t (Z.to_nat i)
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_push ws_deques t #i v @ ↑ι
    <<<
      ws_hub_model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
    iIntros "%Hi !> %Φ ((%l & %γ & -> & #Hmeta & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv) & (%_l & %_γ & %round & %n & %Heq & _Hmeta & #Hl_rounds & Hdeques_owner & #Hv_rounds & Hround)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_load.

    awp_apply (ws_deques_push_spec with "[$Hdeques_inv $Hdeques_owner]") without "Hround"; first done.
    iInv "Hinv" as "(%vs & %vss & %vs_foreign & >%Hvs & >Hdeques_model & Hforeign_model & >Hmodel₂)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%_vs (%_l & %_γ & %Heq & _Hmeta & Hmodel₁)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (ws_hub_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hdeques_model".
    { iIntros "Hdeques_model !>".
      iSplitL "Hmodel₁"; first iSteps. iIntros "$ !>".
      iSteps.
    }
    iIntros "%vs' (%Hlookup & Hdeques_model)".
    iMod (ws_hub_model_update ({[+v+]} ⊎ vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iSplitL "Hmodel₁"; first iSteps. iIntros "!> HΦ !>".
    iSplitR "HΦ".
    { repeat iExists _. iFrame. iPureIntro.
      rewrite (foldr_insert_strong _ (flip (++))) //.
      { set_solver by lia. }
      { rewrite list_to_set_disj_app. multiset_solver. }
      set_solver.
    }
    iIntros "Hdeques_owner Hround". clear.

    wp_smart_apply ws_hub_notify_spec; iSteps.
  Qed.

  Lemma ws_hub_push_foreign_spec t ι v :
    <<<
      ws_hub_inv t ι
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_push_foreign ws_deques t v @ ↑ι
    <<<
      ws_hub_model t ({[+v+]} ⊎ vs)
    | RET (); True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv) HΦ".

    wp_rec. wp_load.

    awp_smart_apply (mpmc_queue_push_spec with "Hforeign_inv").
    iInv "Hinv" as "(%vs & %vss & %vs_foreign & >%Hvs & Hdeques_model & >Hforeign_model & >Hmodel₂)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%_vs (%_l & %_γ & %Heq & _Hmeta & Hmodel₁)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (ws_hub_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hforeign_model".
    { iIntros "Hforeign_model !>".
      iSplitL "Hmodel₁"; first iSteps. iIntros "$ !>".
      iSteps.
    }
    iIntros "Hforeign_model".
    iMod (ws_hub_model_update ({[+v+]} ⊎ vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iSplitL "Hmodel₁"; first iSteps. iIntros "!> HΦ !>".
    iSplitR "HΦ".
    { repeat iExists _. iFrame. iPureIntro.
      rewrite {}Hvs list_to_set_disj_app -foldr_comm_acc_strong; first set_solver by lia.
      f_equal. set_solver by lia.
    }
    iIntros "_". clear.

    wp_smart_apply ws_hub_notify_spec; iSteps.
  Qed.

  Lemma ws_hub_pop_spec t ι i :
    (0 ≤ i)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t (Z.to_nat i)
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_pop ws_deques t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model t vs'
      end
    | RET o;
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
    iIntros "%Hi !> %Φ ((%l & %γ & -> & #Hmeta & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv) & (%_l & %_γ & %round & %n & %Heq & _Hmeta & #Hl_rounds & Hdeques_owner & #Hv_rounds & Hround)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_load.

    awp_smart_apply (ws_deques_pop_spec with "[$Hdeques_inv $Hdeques_owner]") without "Hround"; first done.
    iInv "Hinv" as "(%vs & %vss & %vs_foreign & >%Hvs & >Hdeques_model & Hforeign_model & >Hmodel₂)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%_vs (%_l & %_γ & %Heq & _Hmeta & Hmodel₁)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (ws_hub_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hdeques_model".
    { iIntros "Hdeques_model !>".
      iSplitL "Hmodel₁"; iSteps.
    }
    iIntros ([v |]) "Hdeques_model".

    - iDestruct "Hdeques_model" as "(%ws & %Hlookup & Hdeques_model)".
      set vs' := vs ∖ {[+v+]}.
      iMod (ws_hub_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iExists (Some v).
      iSplitL "Hmodel₁".
      { iExists vs'. iSteps. iPureIntro.
        apply gmultiset_disj_union_difference'.
        rewrite {}Hvs -(take_drop_middle vss (Z.to_nat i) (ws ++ [v])) // foldr_app /=.
        rewrite foldr_comm_acc_strong; first multiset_solver.
        rewrite gmultiset_elem_of_disj_union list_to_set_disj_app.
        set_solver.
      }
      iIntros "!> HΦ !>".
      iSplitR "HΦ".
      { repeat iExists _. iFrame. iPureIntro.
        rewrite /vs' Hvs -{1}(take_drop_middle vss (Z.to_nat i) (ws ++ [v])) // insert_take_drop.
        { eapply lookup_lt_Some. done. }
        rewrite !foldr_app /= !foldr_comm_acc_strong; [multiset_solver.. |].
        rewrite list_to_set_disj_app. multiset_solver.
      }
      iSteps.

    - iDestruct "Hdeques_model" as "(%Hlookup & Hdeques_model)".
      iExists None.
      iSplitL "Hmodel₁"; iSteps.
  Qed.

  #[local] Lemma ws_hub_try_steal_once_spec t ι i :
    (0 ≤ i)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t (Z.to_nat i)
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_try_steal_once ws_deques t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model t vs'
      end
    | RET o;
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
    iIntros "%Hi !> %Φ ((%l & %γ & -> & #Hmeta & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv) & (%_l & %_γ & %round & %n & %Heq & _Hmeta & #Hl_rounds & Hdeques_owner & #Hv_rounds & Hround)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_load.
    wp_apply (array_unsafe_get_spec_cell with "Hv_rounds") as "_"; first lia.
    wp_smart_apply (random_round_reset_spec' with "Hround") as "Hround".
    wp_load.

    iDestruct (ws_deques_owner_valid with "Hdeques_inv Hdeques_owner") as %?.
    awp_apply (ws_deques_steal_as_spec with "[$Hdeques_inv $Hround]") without "Hdeques_owner"; first lia.
    iInv "Hinv" as "(%vs & %vss & %vs_foreign & >%Hvs & >Hdeques_model & Hforeign_model & >Hmodel₂)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%_vs (%_l & %_γ & %Heq & _Hmeta & Hmodel₁)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (ws_hub_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hdeques_model".
    { iIntros "Hdeques_model !>".
      iSplitL "Hmodel₁"; iSteps.
    }
    iIntros ([v |]) "Hdeques_model".

    - iDestruct "Hdeques_model" as "(%j & %ws & %Hj & %Hlookup & Hdeques_model)".
      set vs' := vs ∖ {[+v+]}.
      iMod (ws_hub_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iExists (Some v).
      iSplitL "Hmodel₁".
      { iExists vs'. iSteps. iPureIntro.
        apply gmultiset_disj_union_difference'.
        rewrite {}Hvs -(take_drop_middle vss j (v :: ws)) // foldr_app /=.
        rewrite foldr_comm_acc_strong; first multiset_solver.
        set_solver.
      }
      iIntros "!> HΦ !>".
      iSplitR "HΦ".
      { repeat iExists _. iFrame. iPureIntro.
        rewrite /vs' Hvs -{1}(take_drop_middle vss j (v :: ws)) // insert_take_drop.
        { eapply lookup_lt_Some. done. }
        rewrite !foldr_app /= !foldr_comm_acc_strong; [multiset_solver.. |].
        multiset_solver.
      }
      iSteps.

    - iExists None.
      iSplitL "Hmodel₁"; iSteps.
  Qed.

  #[local] Lemma ws_hub_try_steal_aux_spec yield t ι i max_round :
    (0 ≤ i)%Z →
    (0 ≤ max_round)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t (Z.to_nat i)
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_try_steal_aux ws_deques yield t #i #max_round @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model t vs'
      end
    | RET o;
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
    intros Hi.
    iLöb as "HLöb" forall (max_round).

    iIntros "%Hmax_round !> %Φ ((%l & %γ & -> & #Hmeta & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv) & (%_l & %_γ & %round & %n & %Heq & _Hmeta & #Hl_rounds & Hdeques_owner & #Hv_rounds & Hround)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! None with "Hmodel").
      iSteps.

    - wp_load.

      awp_smart_apply (mpmc_queue_pop_spec with "Hforeign_inv") without "Hdeques_owner Hround".
      iInv "Hinv" as "(%vs & %vss & %vs_foreign & >%Hvs & Hdeques_model & >Hforeign_model & >Hmodel₂)".
      iApply (aacc_aupd with "HΦ"); first solve_ndisj. iIntros "%_vs (%_l & %_γ & %Heq & _Hmeta & Hmodel₁)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (ws_hub_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iAaccIntro with "Hforeign_model".
      { iIntros "Hforeign_model !>".
        iSplitL "Hmodel₁"; iSteps.
      }
      iIntros "Hforeign_model".
      destruct vs_foreign as [| v vs_foreign].

      + iLeft. iSplitL "Hmodel₁"; first iSteps. iIntros "!> HΦ !>".
        iSplitR "HΦ"; first iSteps.
        iIntros "_ (Hdeques_owner & Hround)". clear- Hi Hmax_round Hcase.

        awp_smart_apply (ws_hub_try_steal_once_spec with "[Hdeques_owner Hround]"); [done | iSteps |].
        iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
        iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

        * iRight. iExists (Some v). iFrame.
          iIntros "HΦ !> Howner". clear.

          iSpecialize ("HΦ" with "Howner").
          iSteps.

        * iLeft. iFrame.
          iIntros "HΦ !> Howner". clear- Hi Hmax_round Hcase.

          wp_pures.
          wp_bind (subst _ _ _).
          wp_apply (wp_wand _ _ (λ res, ⌜res = ()%V⌝)%I) as (res) "->".
          { destruct yield; iSteps. }
          wp_smart_apply ("HLöb" with "[] [$Howner] HΦ"); iSteps.

      + set vs' := vs ∖ {[+v+]}.
        iMod (ws_hub_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iRight. iExists (Some v).
        iSplitL "Hmodel₁".
        { iExists vs'. iSteps. iPureIntro.
          apply gmultiset_disj_union_difference'.
          rewrite {}Hvs foldr_comm_acc_strong; first set_solver by lia.
          set_solver.
        }
        iIntros "!> HΦ !>".
        iSplitR "HΦ".
        { repeat iExists _. iFrame. iPureIntro.
          rewrite /vs' Hvs /= foldr_comm_acc_strong; first set_solver by lia.
          multiset_solver.
        }
        iSteps.
  Qed.
  Lemma ws_hub_try_steal_spec t ι i max_round_noyield max_round_yield :
    (0 ≤ i)%Z →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t (Z.to_nat i)
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_try_steal ws_deques t #i (#max_round_noyield, #max_round_yield)%V @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model t vs'
      end
    | RET o;
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
    iIntros "%Hi %Hmax_round_noyield %Hmax_round_yield !> %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_try_steal_aux_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iRight. iExists (Some v). iFrame.
      iIntros "HΦ !> Howner". clear.

      iSpecialize ("HΦ" with "Howner").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hi Hmax_round_yield.

      wp_smart_apply (ws_hub_try_steal_aux_spec with "[$Hinv $Howner] HΦ"); done.
  Qed.

  Lemma ws_hub_pop_try_steal_spec t ι i max_round_noyield max_round_yield :
    (0 ≤ i)%Z →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t (Z.to_nat i)
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_pop_try_steal ws_deques t #i (#max_round_noyield, #max_round_yield)%V @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model t vs'
      end
    | RET o;
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
    iIntros "%Hi %Hmax_round_noyield %Hmax_round_yield !> %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iRight. iExists (Some v). iFrame.
      iIntros "HΦ !> Howner". clear.

      iSpecialize ("HΦ" with "Howner").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hi Hmax_round_noyield Hmax_round_yield.

      wp_smart_apply (ws_hub_try_steal_spec with "[$Hinv $Howner] HΦ"); done.
  Qed.

  Lemma ws_hub_steal_spec t ι i max_round_noyield max_round_yield :
    (0 ≤ i)%Z →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t (Z.to_nat i)
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_steal ws_deques t #i (#max_round_noyield, #max_round_yield)%V @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
      ws_hub_model t vs'
    | RET v;
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
    iIntros "%Hi %Hmax_round_noyield %Hmax_round_yield !> %Φ (#Hinv & Howner) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_smart_apply (ws_hub_try_steal_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists v, vs'. iFrame. iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hi.

      iDestruct "Hinv" as "(%l & %γ & -> & #Hmeta & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv)".

      wp_load.
      wp_smart_apply (waiters_prepare_wait_spec with "Hwaiters_inv") as (waiter) "Hwaiter".

      awp_smart_apply (ws_hub_try_steal_once_spec with "[$Howner]") without "Hwaiter"; [done.. | iSteps |].
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

      + iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
        iRight. iExists v, vs'. iFrame. iSplitL; first iSteps.
        iIntros "HΦ !> Howner Hwaiter". clear- Hi.

        wp_smart_apply (waiters_cancel_wait_spec with "[$Hwaiters_inv $Hwaiter]") as "_".
        wp_pures.
        iApply ("HΦ" with "Howner").

      + iLeft. iFrame.
        iIntros "HΦ !> Howner Hwaiter". clear- Hi.

        wp_smart_apply (waiters_commit_wait_spec with "[$Hwaiters_inv $Hwaiter]") as "_".
        wp_smart_apply ("HLöb" with "Howner HΦ").
  Qed.

  Lemma ws_hub_pop_steal_spec t ι i max_round_noyield max_round_yield :
    (0 ≤ i)%Z →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t (Z.to_nat i)
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_pop_steal ws_deques t #i (#max_round_noyield, #max_round_yield)%V @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
      ws_hub_model t vs'
    | RET v;
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
    iIntros "%Hi %Hmax_round_noyield %Hmax_round_yield !> %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists v, vs'. iFrame. iStep.
      iIntros "HΦ !> Howner". clear.

      iSpecialize ("HΦ" with "Howner").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hi Hmax_round_noyield Hmax_round_yield.

      wp_smart_apply (ws_hub_steal_spec with "[$Hinv $Howner] HΦ"); done.
  Qed.
End ws_hub_G.

#[global] Opaque ws_hub_create.
#[global] Opaque ws_hub_push.
#[global] Opaque ws_hub_push_foreign.
#[global] Opaque ws_hub_pop.
#[global] Opaque ws_hub_try_steal.
#[global] Opaque ws_hub_pop_try_steal.
#[global] Opaque ws_hub_steal.
#[global] Opaque ws_hub_pop_steal.

#[global] Opaque ws_hub_inv.
#[global] Opaque ws_hub_model.
#[global] Opaque ws_hub_owner.
