Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.mpmc_bstack__code.
Require Import zoo_saturn.mpmc_bstack__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type cap sz : nat.
Implicit Type l : location.
Implicit Type v t front : val.
Implicit Type vs : list val.

Class MpmcBstackG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpmc_bstack۰G۰model۰G :: TwinsG Σ (leibnizO (list val))
  }.

Definition mpmc_bstack۰Σ :=
  #[twins۰Σ (leibnizO (list val))
  ].
#[global] Instance subG𑁒mpmc_bstack۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpmc_bstack۰Σ Σ →
  MpmcBstackG Σ.
Proof.
  solve_inG.
Qed.

Section mpmc_bstack۰G.
  Context `{mpmc_bstack۰G : MpmcBstackG Σ}.

  Record metadata :=
    { metadata۰capacity : nat
    ; metadata۰model : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadata𑁒eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata𑁒countable :
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

  #[local] Instance list۰to_val𑁒inj𑁒similar sz :
    Inj (=) (≈@{val}) (list۰to_val sz).
  Proof.
    intros vs1. move: sz. induction vs1 as [| v1 vs1 IH]; intros sz [| v2 vs2]; [done.. |].
    intros (_ & _ & [= <- <-%val𑁒similar𑁒refl%IH]). done.
  Qed.
  #[local] Instance list۰to_val𑁒inj sz :
    Inj (=) (=) (list۰to_val sz).
  Proof.
    intros ?* ->%val𑁒similar𑁒refl%(inj _). done.
  Qed.

  Lemma list۰to_val𑁒inj' vs1 vs2 :
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
  Definition mpmc_bstack۰inv t ι cap : iProp Σ :=
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

  Definition mpmc_bstack۰model t vs : iProp Σ :=
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

  #[global] Instance mpmc_bstack۰model𑁒timeless t vs :
    Timeless (mpmc_bstack۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpmc_bstack۰inv𑁒persistent t ι cap :
    Persistent (mpmc_bstack۰inv t ι cap).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model𑁒alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply twins𑁒alloc'.
  Qed.
  #[local] Lemma model₁𑁒exclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply: twins۰twin₁𑁒exclusive.
  Qed.
  #[local] Lemma model𑁒agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins𑁒agree𑁒L.
  Qed.
  #[local] Lemma model𑁒update {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twins𑁒update.
  Qed.

  Lemma mpmc_bstack۰model𑁒valid t ι cap vs :
    mpmc_bstack۰inv t ι cap -∗
    mpmc_bstack۰model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv) (:model)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iSteps.
  Qed.
  Lemma mpmc_bstack۰model𑁒exclusive t vs1 vs2 :
    mpmc_bstack۰model t vs1 -∗
    mpmc_bstack۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁𑁒exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma mpmc_bstack٠create𑁒spec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      mpmc_bstack٠create #cap
    {{{
      t
    , RET t;
      mpmc_bstack۰inv t ι ₊cap ∗
      mpmc_bstack۰model t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp۰rec.
    wp۰block l as "Hmeta" "(Hl_capacity & Hl_front & _)".
    iMod (pointsto𑁒persist with "Hl_capacity") as "#Hl_capacity".
    rewrite -{1}(Z2Nat.id cap); first lia.

    iMod model𑁒alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ :=
      {|metadata۰capacity := ₊cap
      ; metadata۰model := γ_model
      |}.
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iStep 5. iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma mpmc_bstack٠size𑁒spec t ι cap :
    <<<
      mpmc_bstack۰inv t ι cap
    | ∀∀ vs,
      mpmc_bstack۰model t vs
    >>>
      mpmc_bstack٠size t @ ↑ι
    <<<
      mpmc_bstack۰model t vs
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
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    destruct vs as [| v vs]; iSteps.
  Qed.

  Lemma mpmc_bstack٠is_empty𑁒spec t ι cap :
    <<<
      mpmc_bstack۰inv t ι cap
    | ∀∀ vs,
      mpmc_bstack۰model t vs
    >>>
      mpmc_bstack٠is_empty t @ ↑ι
    <<<
      mpmc_bstack۰model t vs
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
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    destruct vs as [| v vs]; iSteps.
  Qed.

  #[local] Lemma mpmc_bstack٠push_aux_push𑁒spec t ι cap v :
    ⊢ (
      ∀ (sz : Z) front ws,
      <<<
        ⌜sz = length ws⌝ ∗
        ⌜front = list۰to_val (length ws) ws⌝ ∗
        ⌜length ws < cap⌝ ∗
        mpmc_bstack۰inv t ι cap
      | ∀∀ vs,
        mpmc_bstack۰model t vs
      >>>
        mpmc_bstack٠push_aux t #sz v front @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        mpmc_bstack۰model t (if b then v :: vs else vs)
      | RET #b;
        True
      >>>
    ) ∧ (
      <<<
        mpmc_bstack۰inv t ι cap
      | ∀∀ vs,
        mpmc_bstack۰model t vs
      >>>
        mpmc_bstack٠push t v @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        mpmc_bstack۰model t (if b then v :: vs else vs)
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

      wp۰bind (CAS _ _ _).
      iInv "Hinv" as "(:inv۰inner)".
      wp۰cas as _ | <-%list۰to_val𑁒inj'.

      + iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      + iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model𑁒update (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
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
        iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
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
  Lemma mpmc_bstack٠push𑁒spec t ι cap v :
    <<<
      mpmc_bstack۰inv t ι cap
    | ∀∀ vs,
      mpmc_bstack۰model t vs
    >>>
      mpmc_bstack٠push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      mpmc_bstack۰model t (if b then v :: vs else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iPoseProof mpmc_bstack٠push_aux_push𑁒spec as "(_ & H)".
    iApply "H".
  Qed.

  Lemma mpmc_bstack٠pop𑁒spec t ι cap :
    <<<
      mpmc_bstack۰inv t ι cap
    | ∀∀ vs,
      mpmc_bstack۰model t vs
    >>>
      mpmc_bstack٠pop t @ ↑ι
    <<<
      mpmc_bstack۰model t (tail vs)
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
      iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iSplitR "HΦ". { iFrameSteps. }
      iIntros "{%} !>".

      wp۰pures.

      wp۰bind (CAS _ _ _).
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰cas as _ | Hcas; first iSteps.
      destruct vs2; first done.
      destruct Hcas as (_ & _ & [= ->%(inj _) -> ->%(inj _)]).
      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model𑁒update vs1 with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ".
      { simpl in Hvs. iSteps. }
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
End mpmc_bstack۰G.

Require zoo_saturn.mpmc_bstack__opaque.

#[global] Opaque mpmc_bstack۰inv.
#[global] Opaque mpmc_bstack۰model.
