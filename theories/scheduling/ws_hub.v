(* Based on:
   https://github.com/ocaml-multicore/domainslib/blob/731f08891c87e788f2cc95f2a600328f6682a5e2/lib/multi_channel.ml
*)

From zebre Require Import
  prelude.
From zebre.common Require Import
  list.
From zebre.iris.base_logic Require Import
  lib.twins.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  mpsc_latch1.
From zebre.saturn Require Import
  mpmc_queue.
From zebre.scheduling Require Export
  base.
From zebre.scheduling Require Import
  ws_deques.
From zebre Require Import
  options.

Implicit Types num_round : nat.
Implicit Types l : location.
Implicit Types v t : val.
Implicit Types vs : gmultiset val.
Implicit Types γ : gname.

#[local] Notation "'num_round'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'deques'" := (
  in_type "t" 1
)(in custom zebre_field
).
#[local] Notation "'foreign'" := (
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
    λ: "sz" "num_round",
      { "num_round";
        ws_deques.(ws_deques_create) "sz";
        mpmc_queue_create ();
        mpmc_queue_create ()
      }.

  #[local] Definition ws_hub_check_waiters : val :=
    rec: "ws_hub_check_waiters" "t" :=
      match: mpmc_queue_pop "t".{waiters} with
      | None =>
          ()
      | Some "waiter" =>
          if: mpsc_latch1_signal "waiter" then
            "ws_hub_check_waiters" "t"
      end.

  Definition ws_hub_push : val :=
    λ: "t" "i" "v",
      ws_deques.(ws_deques_push) "t".{deques} "i" "v" ;;
      ws_hub_check_waiters "t".

  #[using="ws_deques"]
  Definition ws_hub_push_foreign : val :=
    λ: "t" "v",
      mpmc_queue_push "t".{foreign} "v" ;;
      ws_hub_check_waiters "t".

  Definition ws_hub_try_pop : val :=
    λ: "t" "i",
      let: "deques" := "t".{deques} in
      match: ws_deques.(ws_deques_pop) "deques" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          match: mpmc_queue_pop "t".{foreign} with
          | Some <> as "res" =>
              "res"
          | None =>
              ws_deques_try_steal_as ws_deques "deques" "i" #1
          end
      end.

  #[local] Definition ws_hub_pop_aux : val :=
    rec: "ws_hub_pop_aux" "t" "i" "n" :=
      if: "n" ≤ #0 then (
        §None
      ) else (
        match: ws_hub_try_pop "t" "i" with
        | Some <> as "res" =>
            "res"
        | None =>
            "ws_hub_pop_aux" "t" "i" ("n" - #1)
        end
      ).
  Definition ws_hub_pop : val :=
    rec: "ws_hub_pop" "t" "i" :=
      match: ws_hub_pop_aux "t" "i" "t".{num_round} with
      | Some "v" =>
          "v"
      | None =>
          let: "waiter" := mpsc_latch1_create () in
          mpmc_queue_push "t".{waiters} "waiter" ;;
          match: ws_hub_try_pop "t" "i" with
          | Some "v" =>
              if: mpsc_latch1_signal "waiter" then (
                ws_hub_check_waiters "t"
              ) ;;
              "v"
          | None =>
              mpsc_latch1_wait "waiter" ;;
              "ws_hub_pop" "t" "i"
          end
      end.
End ws_deques.

Class WsHubG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] ws_hub_G_queue_G :: MpmcQueueG Σ ;
  #[local] ws_hub_G_latch1_G :: MpscLatch1G Σ ;
  #[local] ws_hub_G_model_G :: TwinsG Σ (leibnizO (gmultiset val)) ;
}.

Definition ws_hub_Σ := #[
  mpmc_queue_Σ ;
  mpsc_latch1_Σ ;
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

  #[local] Definition ws_hub_model₁ γ vs :=
    twins_twin1 γ (DfracOwn 1) vs.
  #[local] Definition ws_hub_model₂ γ vs :=
    twins_twin2 γ vs.

  #[local] Definition ws_hub_inv_inner γ deques foreign waiters : iProp Σ :=
    ∃ vs vss vs_foreign latches,
    ⌜vs = foldr (λ vs_deques vs, list_to_set_disj vs_deques ⊎ vs) ∅ vss ⊎ list_to_set_disj vs_foreign⌝ ∗
    ws_deques.(ws_deques_model) deques vss ∗
    mpmc_queue_model foreign vs_foreign ∗
    mpmc_queue_model waiters latches ∗
    ( [∗ list] latch ∈ latches,
      mpsc_latch1_inv latch True
    ) ∗
    ws_hub_model₂ γ vs.
  Definition ws_hub_inv t ι : iProp Σ :=
    ∃ l γ num_round deques foreign waiters sz,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[num_round] ↦□ #num_round ∗
    l.[deques] ↦□ deques ∗
    l.[foreign] ↦□ foreign ∗
    l.[waiters] ↦□ waiters ∗
    ws_deques.(ws_deques_inv) deques (ι.@"deques") sz ∗
    mpmc_queue_inv foreign (ι.@"foreign") ∗
    mpmc_queue_inv waiters (ι.@"waiters") ∗
    inv (ι.@"inv") (ws_hub_inv_inner γ deques foreign waiters).

  #[using="ws_deques"]
  Definition ws_hub_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ws_hub_model₁ γ vs.

  Definition ws_hub_owner t i : iProp Σ :=
    ∃ l γ deques,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[deques] ↦□ deques ∗
    ws_deques.(ws_deques_owner) deques i.

  #[global] Instance ws_hub_model_timeless t vs :
    Timeless (ws_hub_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_hub_owner_timeless t i :
    Timeless (ws_hub_owner t i).
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
      ∃ γ,
      ws_hub_model₁ γ ∅ ∗
      ws_hub_model₂ γ ∅.
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
    iIntros "(%l & %γ & %deques & -> & _ & #Hl_deques & Howner1) (%_l & %_γ & %_deques & %Heq & _ & _Hl_deques & Howner2)". injection Heq as <-.
    iDestruct (pointsto_agree with "Hl_deques _Hl_deques") as %<-. iClear "_Hl_deques".
    iApply (ws_deques_owner_exclusive with "Howner1 Howner2").
  Qed.

  Lemma ws_hub_create_spec ι sz (num_round : Z) :
    (0 ≤ sz)%Z →
    (0 ≤ num_round)%Z →
    {{{ True }}}
      ws_hub_create ws_deques #sz #num_round
    {{{ t,
      RET t;
      ws_hub_inv t ι ∗
      ws_hub_model t ∅ ∗
      [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ws_hub_owner t i
    }}}.
  Proof.
    iIntros "%Hsz %Hnum_round %Φ _ HΦ".

    wp_rec.

    wp_smart_apply (ws_deques_create_spec with "[//]") as (deques) "(#Hdeques_inv & Hdeques_model & Hdeques_owner)"; first done.
    wp_apply (mpmc_queue_create_spec with "[//]") as (foreign) "(#Hforeign_inv & Hforeign_model)".
    wp_apply (mpmc_queue_create_spec with "[//]") as (waiters) "(#Hwaiters_inv & Haiters_model)".

    wp_record l as "Hmeta" "(Hl_num_round & Hl_deques & Hl_foreign & Hl_waiters & _)".
    iMod (pointsto_persist with "Hl_num_round") as "#Hl_num_round".
    iMod (pointsto_persist with "Hl_deques") as "#Hl_deques".
    iMod (pointsto_persist with "Hl_foreign") as "#Hl_foreign".
    iMod (pointsto_persist with "Hl_waiters") as "#Hl_waiters".

    iMod ws_hub_model_alloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hdeques_owner".
    - rewrite -(Z2Nat.id num_round) //.
      iSteps.
      rewrite right_id.
      assert (∀ sz, foldr (λ vs_deques vs, list_to_set_disj vs_deques ⊎ vs) ∅ (replicate sz []) = ∅) as ->.
      { clear. induction sz as [| sz IH]; first done. rewrite /= left_id //. }
      iSteps.
    - iSteps.
      iApply (big_sepL_impl with "Hdeques_owner").
      iSteps.
  Qed.

  #[local] Lemma ws_hub_check_waiters_spec t ι :
    {{{
      ws_hub_inv t ι
    }}}
      ws_hub_check_waiters t
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %num_round & %deques & %foreign & %waiters & %sz & -> & #Hmeta & #Hl_num_round & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec. wp_load.

    awp_apply (mpmc_queue_pop_spec with "Hwaiters_inv") without "HΦ".
    iInv "Hinv" as "(%vs & %vss & %vs_foreign & %latches & >%Hvs & Hdeques_model & Hforeign_model & >Hwaiters_model & Hlatches_inv & Hmodel₂)".
    iAaccIntro with "Hwaiters_model"; first iSteps. iIntros "Hwaiters_model !>".
    destruct latches as [| latches]; first iSteps.
    iDestruct "Hlatches_inv" as "(#Hlatch_inv & Hlatches_inv)".
    iSplitL; first iSteps.
    iIntros "_ HΦ".

    wp_smart_apply (mpsc_latch1_signal_spec with "[$Hlatch_inv]") as ([]) "_"; last iSteps.
    wp_smart_apply ("HLöb" with "HΦ").
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
    iIntros "%Hi !> %Φ ((%l & %γ & %num_round & %deques & %foreign & %waiters & %sz & -> & #Hmeta & #Hl_num_round & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv) & (%_l & %_γ & %_deques & %Heq & _Hmeta & _Hl_deques & Hdeques_owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (pointsto_agree with "Hl_deques _Hl_deques") as %<-. iClear "_Hl_deques".

    wp_rec. wp_load.

    awp_apply (ws_deques_push_spec with "[$Hdeques_inv $Hdeques_owner]"); first done.
    iInv "Hinv" as "(%vs & %vss & %vs_foreign & %latches & >%Hvs & >Hdeques_model & Hforeign_model & Hwaiters_model & Hlatches_inv & >Hmodel₂)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%_vs (%_l & %_γ & %Heq & _Hmeta & Hmodel₁)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (ws_hub_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hdeques_model".
    { iIntros "Hdeques_model !>".
      iSplitL "Hmodel₁"; first iSteps.
      iIntros "$ !>". iSteps.
    }
    iIntros "%vs' (%Hlookup & Hdeques_model)".
    iMod (ws_hub_model_update ({[+v+]} ⊎ vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iSplitL "Hmodel₁"; first iSteps. iIntros "!> HΦ !>".
    iSplitR "HΦ".
    { repeat iExists _. iFrame. iPureIntro.
      rewrite {}Hvs assoc. f_equal.
      rewrite (foldr_insert_strong _ (flip (++))) //.
      { set_solver by lia. }
      { rewrite list_to_set_disj_app. multiset_solver. }
      set_solver.
    }
    iIntros "Hdeques_owner".

    wp_smart_apply ws_hub_check_waiters_spec; iSteps.
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
    iIntros "!> %Φ (%l & %γ & %num_round & %deques & %foreign & %waiters & %sz & -> & #Hmeta & #Hl_num_round & #Hl_deques & #Hl_foreign & #Hl_waiters & #Hdeques_inv & #Hforeign_inv & #Hwaiters_inv & #Hinv) HΦ".

    wp_rec. wp_load.

    awp_smart_apply (mpmc_queue_push_spec with "Hforeign_inv").
    iInv "Hinv" as "(%vs & %vss & %vs_foreign & %latches & >%Hvs & Hdeques_model & >Hforeign_model & Hwaiters_model & Hlatches_inv & >Hmodel₂)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%_vs (%_l & %_γ & %Heq & _Hmeta & Hmodel₁)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (ws_hub_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hforeign_model".
    { iIntros "Hforeign_model !>".
      iSplitL "Hmodel₁"; first iSteps.
      iIntros "$ !>". iSteps.
    }
    iIntros "Hforeign_model".
    iMod (ws_hub_model_update ({[+v+]} ⊎ vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iSplitL "Hmodel₁"; first iSteps. iIntros "!> HΦ !>".
    iSplitR "HΦ".
    { repeat iExists _. iFrame. iPureIntro.
      rewrite (comm (⊎)) {}Hvs -assoc. f_equal.
      rewrite list_to_set_disj_app /= right_id //.
    }
    iIntros "_".

    wp_smart_apply ws_hub_check_waiters_spec; iSteps.
  Qed.

  Lemma ws_hub_try_pop_spec t ι i :
    (0 ≤ i)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t (Z.to_nat i)
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_try_pop ws_deques t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model t vs
      | Some v =>
          ∃ v vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model t vs'
      end
    | RET o;
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
  Admitted.

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
      ∃∃ v vs',
      ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
      ws_hub_model t vs'
    | RET v;
      ws_hub_owner t (Z.to_nat i)
    >>>.
  Proof.
  Admitted.
End ws_hub_G.

#[global] Opaque ws_hub_create.
#[global] Opaque ws_hub_push.
#[global] Opaque ws_hub_push_foreign.
#[global] Opaque ws_hub_try_pop.
#[global] Opaque ws_hub_pop.

#[global] Opaque ws_hub_inv.
#[global] Opaque ws_hub_model.
#[global] Opaque ws_hub_owner.
