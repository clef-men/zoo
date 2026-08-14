Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.bstack_mpmc__code.
Require Import zoo_saturn.bstack_mpmc__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type cap sz : nat.
Implicit Type l : location.
Implicit Type v t front : val.
Implicit Type vs : list val.

Class BstackMpmcG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] bstack_mpmc۰G۰model۰G :: TwinsG Σ (leibnizO (list val))
  }.

Definition bstack_mpmc۰Σ :=
  #[twins۰Σ (leibnizO (list val))
  ].
#[global] Instance subGｰbstack_mpmc۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG bstack_mpmc۰Σ Σ →
  BstackMpmcG Σ.
Proof.
  solve_inG.
Qed.

Section bstack_mpmc۰G.
  Context `{bstack_mpmc۰G : BstackMpmcG Σ}.

  Record metadata :=
    { metadata۰capacity : nat
    ; metadata۰model : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadataｰeq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadataｰcountable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Fixpoint list۰to_val sz vs :=
    match vs with
    | [] =>
        §Nil%V
    | v :: vs =>
        ‘Cons[ #sz, v, list۰to_val (sz - 1) vs ]%V
    end.

  #[local] Instance list۰to_valｰinjｰsimilar sz :
    Inj (=) (≈@{val}) (list۰to_val sz).
  Proof.
    intros vs1. move: sz. induction vs1 as [| v1 vs1 IH]; intros sz [| v2 vs2]; [done.. |].
    intros (_ & _ & [= <- <-%valｰsimilarｰrefl%IH]). done.
  Qed.
  #[local] Instance list۰to_valｰinj sz :
    Inj (=) (=) (list۰to_val sz).
  Proof.
    intros ?* ->%valｰsimilarｰrefl%(inj _). done.
  Qed.

  Lemma list۰to_valｰinj' vs1 vs2 :
    list۰to_val (length vs1) vs1 ≈ list۰to_val (length vs2) vs2 →
    vs1 = vs2.
  Proof.
    destruct vs1, vs2; try done.
    intros (_ & _ & [= ->%(inj _) -> ?%(inj _)]). naive_solver.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata۰model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins۰twin₂ γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata۰model) vs.

  #[local] Definition inv۰inner l γ : iProp Σ :=
    ∃ vs,
    l.[front] ↦ list۰to_val (length vs) vs ∗
    model₂ γ vs.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %vs{}
      & Hl_front
      & Hmodel₂
      )
    ".
  Definition bstack_mpmc۰inv t ι cap : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    ⌜cap = γ.(metadata۰capacity)⌝ ∗
    ⌜0 < γ.(metadata۰capacity)⌝ ∗
    l.[capacity] ↦□ #γ.(metadata۰capacity) ∗
    inv ι (inv۰inner l γ).
  #[local] Instance : CustomIpat "inv" :=
    " ( %l
      & %γ
      & ->
      & #Hmeta
      & ->
      & %Hcapacity
      & #Hl_capacity
      & #Hinv
      )
    ".

  Definition bstack_mpmc۰model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    ⌜length vs ≤ γ.(metadata۰capacity)⌝ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & Hmeta_{}
      & %Hvs{}
      & Hmodel₁{_{}}
      )
    ".

  #[global] Instance bstack_mpmc۰modelｰtimeless t vs :
    Timeless (bstack_mpmc۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance bstack_mpmc۰invｰpersistent t ι cap :
    Persistent (bstack_mpmc۰inv t ι cap).
  Proof.
    apply _.
  Qed.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply: twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twinsｰupdate.
  Qed.

  Lemma bstack_mpmc۰modelｰvalid t ι cap vs :
    bstack_mpmc۰inv t ι cap -∗
    bstack_mpmc۰model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv) (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iSteps.
  Qed.
  Lemma bstack_mpmc۰modelｰexclusive t vs1 vs2 :
    bstack_mpmc۰model t vs1 -∗
    bstack_mpmc۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma bstack_mpmc٠createｰspec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      bstack_mpmc٠create #cap
    {{{
      t
    , RET t;
      bstack_mpmc۰inv t ι ₊cap ∗
      bstack_mpmc۰model t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp۰rec.
    wp۰block l as "Hmeta" "#Hl_capacity Hl_front".
    rewrite -{1}(Z2Nat.id cap); first lia.

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ :=
      {|metadata۰capacity := ₊cap
      ; metadata۰model := γ_model
      |}.
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iStep 5. iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma bstack_mpmc٠sizeｰspec t ι cap :
    <<<
      bstack_mpmc۰inv t ι cap
    | ∀∀ vs,
      bstack_mpmc۰model t vs
    >>>
      bstack_mpmc٠size t @ ↑ι
    <<<
      bstack_mpmc۰model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.

    wp۰bind (_.{front})%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    destruct vs as [| v vs]; iSteps.
  Qed.

  Lemma bstack_mpmc٠is_emptyｰspec t ι cap :
    <<<
      bstack_mpmc۰inv t ι cap
    | ∀∀ vs,
      bstack_mpmc۰model t vs
    >>>
      bstack_mpmc٠is_empty t @ ↑ι
    <<<
      bstack_mpmc۰model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.

    wp۰bind (_.{front})%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    destruct vs as [| v vs]; iSteps.
  Qed.

  #[local] Lemma bstack_mpmc٠push_aux_pushｰspec t ι cap v :
    ⊢ (
      ∀ (sz : Z) front ws,
      <<<
        ⌜sz = length ws⌝ ∗
        ⌜front = list۰to_val (length ws) ws⌝ ∗
        ⌜length ws < cap⌝ ∗
        bstack_mpmc۰inv t ι cap
      | ∀∀ vs,
        bstack_mpmc۰model t vs
      >>>
        bstack_mpmc٠push_aux t #sz v front @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        bstack_mpmc۰model t (if b then v :: vs else vs)
      | RET #b;
        True
      >>>
    ) ∧ (
      <<<
        bstack_mpmc۰inv t ι cap
      | ∀∀ vs,
        bstack_mpmc۰model t vs
      >>>
        bstack_mpmc٠push t v @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        bstack_mpmc۰model t (if b then v :: vs else vs)
      | RET #b;
        True
      >>>
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHpush_aux & IHpush)".
    iSplit.

    - iIntros "%sz %front %ws %Φ (-> & -> & %Hws & (:inv)) HΦ".

      wp۰rec. wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰cas as _ | <-%list۰to_valｰinj'.

      + iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      + iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod (modelｰupdate (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        rewrite bool_decide_eq_true_2 //.
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.
        rewrite Z.add_1_r -Nat2Z.inj_succ.
        iSplitR "HΦ".
        { iFrameSteps. rewrite Nat.sub_0_r //. }
        iSteps.

    - iIntros "%Φ (:inv) HΦ".

      wp۰rec. wp۰pures.

      wp۰bind (_.{front})%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      destruct_decide (γ.(metadata۰capacity) ≤ length vs) as Hlen.

      + iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        rewrite bool_decide_eq_false_2; first lia.
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hcapacity Hlen}".

        destruct vs as [| w vs]; first naive_solver lia.
        wp۰load. wp۰pures.
        rewrite bool_decide_eq_true_2; first naive_solver lia.
        iSteps.

      + iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%- Hlen}".

        destruct vs as [| w vs]; wp۰pures.

        * wp۰apply ("IHpush_aux" $! _ _ [] with "[] HΦ"); first iSteps.

        * simpl in Hlen.
          wp۰load. wp۰pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp۰apply+ ("IHpush_aux" $! _ _ (w :: vs) with "[] HΦ"); first iSteps.
  Qed.
  Lemma bstack_mpmc٠pushｰspec t ι cap v :
    <<<
      bstack_mpmc۰inv t ι cap
    | ∀∀ vs,
      bstack_mpmc۰model t vs
    >>>
      bstack_mpmc٠push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      bstack_mpmc۰model t (if b then v :: vs else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iPoseProof bstack_mpmc٠push_aux_pushｰspec as "(_ & H)".
    iApply "H".
  Qed.

  Lemma bstack_mpmc٠popｰspec t ι cap :
    <<<
      bstack_mpmc۰inv t ι cap
    | ∀∀ vs,
      bstack_mpmc۰model t vs
    >>>
      bstack_mpmc٠pop t @ ↑ι
    <<<
      bstack_mpmc۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec.

    wp۰bind (_.{front})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    destruct vs1 as [| v vs1].

    - iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iSplitR "HΦ". { iFrameSteps. }
      iIntros "{%} !>".

      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰cas as _ | Hcas; first iSteps.
      destruct vs2; first done.
      destruct Hcas as (_ & _ & [= ->%(inj _) -> ->%(inj _)]).
      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate vs1 with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ".
      { simpl in Hvs. iSteps. }
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
End bstack_mpmc۰G.

Require zoo_saturn.bstack_mpmc__opaque.

#[global] Opaque bstack_mpmc۰inv.
#[global] Opaque bstack_mpmc۰model.
