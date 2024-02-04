(*
   Based on:
   https://github.com/ocaml-multicore/picos/blob/07d6c2d391e076b490098c0379d01208b3a9cc96/test/lib/foundation/mpsc_queue.ml
*)

From iris.algebra Require Import
  list.

From zebre Require Import
  prelude.
From zebre.common Require Import
  list.
From zebre.iris.base_logic Require Import
  lib.auth_excl.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  lst.
From zebre.saturn Require Export
  base.
From zebre Require Import
  options.

Implicit Types l : loc.
Implicit Types v t : val.
Implicit Types vs front back : list val.
Implicit Types o : option val.

#[local] Notation "'front'" :=
  0
( in custom zebre_field
).
#[local] Notation "'back'" :=
  1
( in custom zebre_field
).

Definition mpsc_queue_create : val :=
  λ: <>,
    { §Nil; §Nil }.

Definition mpsc_queue_push : val :=
  rec: "mpsc_queue_push" "t" "v" :=
    let: "back" := "t".{back} in
    if: Cas "t".[back] "back" ‘Cons{ "v", "back" } then (
      ()
    ) else (
      "mpsc_queue_push" "t" "v"
    ).

Definition mpsc_queue_pop : val :=
  λ: "t",
    match: "t".{front} with
    | Nil =>
        match: lst_rev (Xchg "t".[back] §Nil) with
        | Nil =>
            §None
        | Cons "v" "front" =>
            "t" <-{front} "front" ;;
            ‘Some{ "v" }
        end
    | Cons "v" "front" =>
        "t" <-{front} "front" ;;
        ‘Some{ "v" }
    end.

Class MpscQueueG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] mpsc_queue_G_auth_excl_G :: AuthExclG Σ (listO val) ;
}.

Definition mpsc_queue_Σ := #[
  auth_excl_Σ (listO val)
].
#[global] Instance subG_mpsc_queue_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG mpsc_queue_Σ Σ →
  MpscQueueG Σ.
Proof.
  solve_inG.
Qed.

Section mpsc_queue_G.
  Context `{mpsc_queue_G : MpscQueueG Σ}.

  Record mpsc_queue_meta := {
    mpsc_queue_meta_model : gname ;
    mpsc_queue_meta_front : gname ;
  }.
  Implicit Types γ : mpsc_queue_meta.

  #[local] Instance mpsc_queue_meta_eq_dec : EqDecision mpsc_queue_meta :=
    ltac:(solve_decision).
  #[local] Instance mpsc_queue_meta_countable :
    Countable mpsc_queue_meta.
  Proof.
    pose encode γ := (
      γ.(mpsc_queue_meta_model),
      γ.(mpsc_queue_meta_front)
    ).
    pose decode := λ '(γ_model, γ_front), {|
      mpsc_queue_meta_model := γ_model ;
      mpsc_queue_meta_front := γ_front ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition mpsc_queue_model₁' γ_model vs :=
    auth_excl_auth γ_model (DfracOwn 1) vs.
  #[local] Definition mpsc_queue_model₁ γ vs :=
    mpsc_queue_model₁' γ.(mpsc_queue_meta_model) vs.
  #[local] Definition mpsc_queue_model₂' γ_model vs :=
    auth_excl_frag γ_model vs.
  #[local] Definition mpsc_queue_model₂ γ vs :=
    mpsc_queue_model₂' γ.(mpsc_queue_meta_model) vs.

  #[local] Definition mpsc_queue_front₁' γ_front front :=
    auth_excl_auth γ_front (DfracOwn 1) front.
  #[local] Definition mpsc_queue_front₁ γ front :=
    mpsc_queue_front₁' γ.(mpsc_queue_meta_front) front.
  #[local] Definition mpsc_queue_front₂' γ_model front :=
    auth_excl_frag γ_model front.
  #[local] Definition mpsc_queue_front₂ γ front :=
    mpsc_queue_front₂' γ.(mpsc_queue_meta_front) front.

  #[local] Definition mpsc_queue_inv_inner l γ : iProp Σ :=
    ∃ front back,
    mpsc_queue_front₂ γ front ∗
    l.[back] ↦ lst_to_val back ∗
    mpsc_queue_model₂ γ (back ++ reverse front).
  Definition mpsc_queue_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (mpsc_queue_inv_inner l γ).

  Definition mpsc_queue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    mpsc_queue_model₁ γ vs.

  Definition mpsc_queue_consumer t : iProp Σ :=
    ∃ l γ front,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[front] ↦ lst_to_val front ∗
    mpsc_queue_front₁ γ front.

  #[global] Instance mpsc_queue_model_timeless t vs :
    Timeless (mpsc_queue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_consumer_timeless t :
    Timeless (mpsc_queue_consumer t ).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_inv_persistent t ι :
    Persistent (mpsc_queue_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma mpsc_queue_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      mpsc_queue_model₁' γ_model [] ∗
      mpsc_queue_model₂' γ_model [].
  Proof.
    apply auth_excl_alloc'.
  Qed.
  #[local] Lemma mpsc_queue_model_agree γ vs1 vs2 :
    mpsc_queue_model₁ γ vs1 -∗
    mpsc_queue_model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: auth_excl_agree_L.
  Qed.
  #[local] Lemma mpsc_queue_model_update {γ vs1 vs2} vs :
    mpsc_queue_model₁ γ vs1 -∗
    mpsc_queue_model₂ γ vs2 ==∗
      mpsc_queue_model₁ γ vs ∗
      mpsc_queue_model₂ γ vs.
  Proof.
    apply auth_excl_update'.
  Qed.

  #[local] Lemma mpsc_queue_front_alloc :
    ⊢ |==>
      ∃ γ_front,
      mpsc_queue_front₁' γ_front [] ∗
      mpsc_queue_front₂' γ_front [].
  Proof.
    apply auth_excl_alloc'.
  Qed.
  #[local] Lemma mpsc_queue_front_agree γ front1 front2 :
    mpsc_queue_front₁ γ front1 -∗
    mpsc_queue_front₂ γ front2 -∗
    ⌜front1 = front2⌝.
  Proof.
    apply: auth_excl_agree_L.
  Qed.
  #[local] Lemma mpsc_queue_front_update {γ front1 front2} front :
    mpsc_queue_front₁ γ front1 -∗
    mpsc_queue_front₂ γ front2 ==∗
      mpsc_queue_front₁ γ front ∗
      mpsc_queue_front₂ γ front.
  Proof.
    apply auth_excl_update'.
  Qed.

  Lemma mpsc_queue_consumer_exclusive t :
    mpsc_queue_consumer t -∗
    mpsc_queue_consumer t -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma mpsc_queue_create_spec ι :
    {{{ True }}}
      mpsc_queue_create ()
    {{{ t,
      RET t;
      mpsc_queue_inv t ι ∗
      mpsc_queue_model t [] ∗
      mpsc_queue_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_record l as "Hmeta" "(Hfront & Hback & _)".

    iMod mpsc_queue_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod mpsc_queue_front_alloc as "(%γ_front & Hfront₁ & Hfront₂)".

    pose γ := {|
      mpsc_queue_meta_model := γ_model ;
      mpsc_queue_meta_front := γ_front ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hfront Hfront₁".
    - iExists l, γ. iStep 2. iApply inv_alloc. iExists [], []. iSteps.
    - iSplitL "Hmodel₁"; first iSteps. iExists l, γ, []. iSteps.
  Qed.

  Lemma mpsc_queue_push_spec t ι v :
    <<<
      mpsc_queue_inv t ι
    | ∀∀ vs,
      mpsc_queue_model t vs
    >>>
      mpsc_queue_push t v @ ↑ι
    <<<
      mpsc_queue_model t (v :: vs)
    | RET (); True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%front & %back & Hfront₂ & Hback & Hmodel₂)".
    wp_load.
    iSplitR "HΦ"; first iSteps.
    iModIntro. clear.

    wp_pures.

    wp_bind (Cas _ _ _).
    iInv "Hinv" as "(%front & %back' & Hfront₂ & Hback & Hmodel₂)".
    wp_cas as _ | ->%(inj _); first iSteps.
    iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (mpsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %Hvs.
    iMod (mpsc_queue_model_update (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iExists front, (v :: back). rewrite Hvs. iSteps. }
    iSteps.
  Qed.

  Lemma mpsc_queue_pop_spec t ι :
    <<<
      mpsc_queue_inv t ι ∗
      mpsc_queue_consumer t
    | ∀∀ vs,
      mpsc_queue_model t vs
    >>>
      mpsc_queue_pop t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          mpsc_queue_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          mpsc_queue_model t vs'
      end
    | RET o;
      mpsc_queue_consumer t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %front & %Heq & _Hmeta & Hfront & Hfront₁)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_load.
    destruct front as [| v front]; wp_pures.

    - wp_bind (Xchg _ _).
      iInv "Hinv" as "(%_front & %back & Hfront₂ & Hback & Hmodel₂)".
      wp_xchg.
      iDestruct (mpsc_queue_front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %Hvs.
      destruct (rev_elim back) as [-> | (back' & v & ->)].

      + iMod ("HΦ" $! None with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hfront Hfront₁ HΦ". { iExists [], []. iSteps. }
        iModIntro. clear.

        wp_apply (lst_rev_spec _ [] with "[//]") as "%back ->".
        wp_pures.

        iApply "HΦ".
        iExists l, γ, []. iSteps.

      + rewrite reverse_nil right_id /= in Hvs |- *.
        set front := reverse back'.
        iMod (mpsc_queue_front_update front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
        iMod (mpsc_queue_model_update back' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hfront Hfront₁ HΦ".
        { iExists front, []. rewrite reverse_involutive. iSteps. }
        iModIntro. clear.

        wp_apply (lst_rev_spec with "[//]") as "%back ->". rewrite reverse_snoc.
        iSteps.

    - wp_store.
      iApply fupd_wp. iInv "Hinv" as "(%_front & %back & >Hfront₂ & Hback & >Hmodel₂)".
      iDestruct (mpsc_queue_front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod (mpsc_queue_front_update with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %Hvs.
      set vs' := back ++ reverse front.
      iMod (mpsc_queue_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ".
      { iExists vs'. iSteps. rewrite Hvs reverse_cons assoc //. }
      iSteps.
  Qed.
End mpsc_queue_G.

#[global] Opaque mpsc_queue_create.
#[global] Opaque mpsc_queue_push.
#[global] Opaque mpsc_queue_pop.

#[global] Opaque mpsc_queue_inv.
#[global] Opaque mpsc_queue_model.
#[global] Opaque mpsc_queue_consumer.
