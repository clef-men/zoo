Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.relations.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.auth_twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.ws_bdeque_2__code.
Require Import zoo_saturn.ws_bdeque_1.
Require Import zoo.options.

Import ws_bdeque_1.base.

Implicit Type b : bool.
Implicit Type slot : location.
Implicit Type slots : list location.
Implicit Type v : val.
Implicit Type vs ws : list val.

Class WsBdeque2G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] ws_bdeque_2۰G۰base۰G :: WsBdeque1G Σ
  ; #[local] ws_bdeque_2۰G۰model۰G :: AuthTwinsG Σ (leibnizO (list val)) suffix
  }.

Definition ws_bdeque_2۰Σ :=
  #[ws_bdeque_1۰Σ
  ; auth_twins۰Σ (leibnizO (list val)) suffix
  ].
#[global] Instance subG𑁒ws_bdeque_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG ws_bdeque_2۰Σ Σ →
  WsBdeque2G Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section ws_bdeque_2۰G.
    Context `{ws_bdeque_2۰G : WsBdeque2G Σ}.

    Implicit Type t : location.

    Record ws_bdeque_2۰name :=
      { ws_bdeque_2۰name۰capacity : nat
      ; ws_bdeque_2۰name۰base : ws_bdeque_1۰name
      ; ws_bdeque_2۰name۰model : auth_twins۰name
      }.
    Implicit Type γ : ws_bdeque_2۰name.

    #[global] Instance ws_bdeque_2۰name𑁒eq_dec : EqDecision ws_bdeque_2۰name :=
      ltac:(solve_decision).
    #[global] Instance ws_bdeque_2۰name𑁒countable :
      Countable ws_bdeque_2۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      auth_twins۰twin₁ _ γ_model vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(ws_bdeque_2۰name۰model).
    #[local] Definition model₂' γ_model vs :=
      auth_twins۰twin₂ _ γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(ws_bdeque_2۰name۰model).

    #[local] Definition owner' γ_owner ws :=
      auth_twins۰auth _ γ_owner ws.
    #[local] Definition owner γ :=
      owner' γ.(ws_bdeque_2۰name۰model).

    #[local] Definition inv۰inner γ : iProp Σ :=
      ∃ vs slots,
      ws_bdeque_1۰model γ.(ws_bdeque_2۰name۰base) (#*@{location} slots) ∗
      model₂ γ vs ∗
      [∗ list] slot; v ∈ slots; vs, slot ↦ᵣ v.
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %vs{}
        & %slots{}
        & >Hbase_model
        & >Hmodel₂
        & >Hslots
        )
      ".
    Definition ws_bdeque_2۰inv t γ ι cap : iProp Σ :=
      ⌜cap = γ.(ws_bdeque_2۰name۰capacity)⌝ ∗
      ws_bdeque_1۰inv t γ.(ws_bdeque_2۰name۰base) (ι.@"base") cap ∗
      inv (ι.@"inv") (inv۰inner γ).
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & #Hbase_inv
        & #Hinv
        )
      ".

    Definition ws_bdeque_2۰model γ vs : iProp Σ :=
      model₁ γ vs ∗
      ⌜length vs ≤ γ.(ws_bdeque_2۰name۰capacity)⌝.
    #[local] Instance : CustomIpat "model" :=
      " ( Hmodel₁{_{}}
        & %Hvs{}
        )
      ".

    Definition ws_bdeque_2۰owner t γ ws : iProp Σ :=
      ∃ slots_owner,
      ws_bdeque_1۰owner t γ.(ws_bdeque_2۰name۰base) (#*@{location} slots_owner) ∗
      owner γ ws.
    #[local] Instance : CustomIpat "owner" :=
      " ( %slots_owner{_{}}
        & Hbase_owner{_{}}
        & Howner{_{}}
        )
      ".

    #[global] Instance ws_bdeque_2۰model𑁒timeless γ vs :
      Timeless (ws_bdeque_2۰model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ws_bdeque_2۰owner𑁒timeless t γ ws :
      Timeless (ws_bdeque_2۰owner t γ ws).
    Proof.
      apply _.
    Qed.

    #[global] Instance ws_bdeque_2۰inv𑁒persistent t γ ι cap :
      Persistent (ws_bdeque_2۰inv t γ ι cap).
    Proof.
      apply _.
    Qed.

    #[local] Lemma model𑁒owner𑁒alloc :
      ⊢ |==>
        ∃ γ_model,
        model₁' γ_model [] ∗
        model₂' γ_model [] ∗
        owner' γ_model [].
    Proof.
      iMod (auth_twins𑁒alloc (auth_twins۰G := ws_bdeque_2۰G۰model۰G) _ []) as "(%γ_model & $ & $ & $)".
      iSteps.
    Qed.
    #[local] Lemma model₁𑁒valid γ ws vs :
      owner γ ws -∗
      model₁ γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      rewrite -preorder𑁒rtc.
      apply: auth_twins𑁒valid₁.
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
    #[local] Lemma model𑁒owner𑁒agree γ ws vs1 vs2 :
      owner γ ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
        ⌜vs1 `suffix_of` ws⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Howner Hmodel₁ Hmodel₂".
      iDestruct (model₁𑁒valid with "Howner Hmodel₁") as %Hsuffix.
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iSteps.
    Qed.
    #[local] Lemma model𑁒push {γ ws vs1 vs2} v :
      owner γ ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner γ (vs1 ++ [v]) ∗
        model₁ γ (vs1 ++ [v]) ∗
        model₂ γ (vs1 ++ [v]).
    Proof.
      apply auth_twins𑁒update𑁒auth.
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
    #[local] Lemma model𑁒pop γ ws vs1 vs2 :
      owner γ ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner γ (removelast vs1) ∗
        model₁ γ (removelast vs1) ∗
        model₂ γ (removelast vs1).
    Proof.
      apply auth_twins𑁒update𑁒auth.
    Qed.

    #[local] Lemma owner𑁒update γ ws vs :
      owner γ ws -∗
      model₁ γ vs -∗
      model₂ γ vs ==∗
        owner γ vs ∗
        model₁ γ vs ∗
        model₂ γ vs.
    Proof.
      apply auth_twins𑁒update𑁒auth.
    Qed.
    #[local] Lemma owner𑁒exclusive γ ws1 ws2 :
      owner γ ws1 -∗
      owner γ ws2 -∗
      False.
    Proof.
      apply: auth_twins۰auth𑁒exclusive.
    Qed.

    Lemma ws_bdeque_2۰model𑁒valid t γ ι cap vs :
      ws_bdeque_2۰inv t γ ι cap -∗
      ws_bdeque_2۰model γ vs -∗
      ⌜length vs ≤ cap⌝.
    Proof.
      iSteps.
    Qed.
    Lemma ws_bdeque_2۰model𑁒exclusive γ vs1 vs2 :
      ws_bdeque_2۰model γ vs1 -∗
      ws_bdeque_2۰model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁𑁒exclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    Lemma ws_bdeque_2۰owner𑁒exclusive t γ ws1 ws2 :
      ws_bdeque_2۰owner t γ ws1 -∗
      ws_bdeque_2۰owner t γ ws2 -∗
      False.
    Proof.
      iIntros "(:owner =1) (:owner =2)".
      iApply (owner𑁒exclusive with "Howner_1 Howner_2").
    Qed.
    Lemma ws_bdeque_2𑁒owner𑁒model t γ ws vs :
      ws_bdeque_2۰owner t γ ws -∗
      ws_bdeque_2۰model γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:owner =1) (:model =2)".
      iApply (model₁𑁒valid with "Howner_1 Hmodel₁_2").
    Qed.

    Lemma ws_bdeque_2٠create𑁒spec ι (cap : Z) :
      (0 < cap)%Z →
      {{{
        True
      }}}
        ws_bdeque_2٠create #cap
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        ws_bdeque_2۰inv t γ ι ₊cap ∗
        ws_bdeque_2۰model γ [] ∗
        ws_bdeque_2۰owner t γ []
      }}}.
    Proof.
      iIntros "%Hcap %Φ _ HΦ".

      iApply wp𑁒fupd.
      wp۰apply (ws_bdeque_1٠create𑁒spec with "[//]") as (t γ_base) "(Hmeta & #Hbase_inv & Hbase_model & Hbase_owner)". 1: done.

      iMod model𑁒owner𑁒alloc as "(%γ_model & Hmodel₁ & Hmodel₂ & Howner)".

      pose γ :=
        {|ws_bdeque_2۰name۰capacity := ₊cap
        ; ws_bdeque_2۰name۰base := γ_base
        ; ws_bdeque_2۰name۰model := γ_model
        |}.

      iApply ("HΦ" $! t γ).
      iFrame "#∗". iSplitR "Hbase_owner"; iStep.
      - iApply inv_alloc.
        iExists [], []. iFrameSteps.
      - iExists []. iFrameSteps.
    Qed.

    Lemma ws_bdeque_2٠size𑁒spec t γ ι cap ws :
      <<<
        ws_bdeque_2۰inv t γ ι cap ∗
        ws_bdeque_2۰owner t γ ws
      | ∀∀ vs,
        ws_bdeque_2۰model γ vs
      >>>
        ws_bdeque_2٠size #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_2۰model γ vs
      | RET #(length vs);
        ws_bdeque_2۰owner t γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      awp۰apply (ws_bdeque_1٠size𑁒spec with "[$]").
      iInv "Hinv" as "(:inv۰inner)".
      iApply (aacc𑁒aupd𑁒commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps.
      iDestruct (model𑁒owner𑁒agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (owner𑁒update with "Howner Hmodel₁ Hmodel₂") as "(Howner & $ & Hmodel₂)".
      rewrite length_fmap.
      iDestruct (big_sepL2_length with "Hslots") as %->.
      iSteps.
    Qed.

    Lemma ws_bdeque_2٠is_empty𑁒spec t γ ι cap ws :
      <<<
        ws_bdeque_2۰inv t γ ι cap ∗
        ws_bdeque_2۰owner t γ ws
      | ∀∀ vs,
        ws_bdeque_2۰model γ vs
      >>>
        ws_bdeque_2٠is_empty #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_2۰model γ vs
      | RET #(bool_decide (vs = []%list));
        ws_bdeque_2۰owner t γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      awp۰apply (ws_bdeque_1٠is_empty𑁒spec with "[$]").
      iInv "Hinv" as "(:inv۰inner)".
      iApply (aacc𑁒aupd𑁒commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps.
      iDestruct (model𑁒owner𑁒agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (owner𑁒update with "Howner Hmodel₁ Hmodel₂") as "(Howner & $ & Hmodel₂)".
      erewrite (bool_decide_ext (_ <$> _ = []) (length _ = 0)). 2: rewrite length_zero_iff_nil //.
      rewrite length_fmap.
      iDestruct (big_sepL2_length with "Hslots") as %->.
      erewrite (bool_decide_ext (length _ = 0)). 2: apply length_zero_iff_nil.
      iSteps.
    Qed.

    Lemma ws_bdeque_2٠push𑁒spec t γ ι cap ws v :
      <<<
        ws_bdeque_2۰inv t γ ι cap ∗
        ws_bdeque_2۰owner t γ ws
      | ∀∀ vs,
        ws_bdeque_2۰model γ vs
      >>>
        ws_bdeque_2٠push #t v @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_2۰model γ (if b then vs ++ [v] else vs)
      | RET #b;
        ws_bdeque_2۰owner t γ (if b then vs ++ [v] else ws)
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      wp۰rec.
      wp۰ref slot as "Hslot".

      awp۰apply (ws_bdeque_1٠push𑁒spec with "[$]").
      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (big_sepL2_length with "Hslots") as %Hlength.
      iApply (aacc𑁒aupd𑁒commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps. iIntros "%b (-> & _ & Hbase_model)".
      iDestruct (model𑁒owner𑁒agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iEval (simpl_length) in "Hbase_model" |- *.
      case_bool_decide.

      - iExists true.
        iMod (model𑁒push with "Howner Hmodel₁ Hmodel₂") as "(Howner & $ & Hmodel₂)".
        iDestruct (big_sepL2𑁒snoc₂ with "Hslots Hslot") as "Hslots".
        rewrite -fmap_snoc. iSteps; iPureIntro.
        { rewrite bool_decide_eq_true_2 //. 1: lia. }
        { simpl_length/=. lia. }

      - iExists false. iFrameSteps. iPureIntro.
        rewrite bool_decide_eq_false_2 //. 1: lia.
    Qed.

    Lemma ws_bdeque_2٠steal𑁒spec t γ ι cap :
      <<<
        ws_bdeque_2۰inv t γ ι cap
      | ∀∀ vs,
        ws_bdeque_2۰model γ vs
      >>>
        ws_bdeque_2٠steal #t @ ↑ι
      <<<
        ws_bdeque_2۰model γ (tail vs)
      | RET head vs;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec.

      awp۰apply (ws_bdeque_1٠steal𑁒spec with "[$]").
      iInv "Hinv" as "(:inv۰inner)".
      iApply (aacc𑁒aupd𑁒commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps. iIntros "Hbase_model".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model𑁒steal with "Hmodel₁ Hmodel₂") as "($ & Hmodel₂)".
      iSplitR.
      { iPureIntro. etrans. 2: done. apply length𑁒tail. }
      iIntros "!> HΦ !>".
      destruct slots as [| slot slots], vs as [| v vs] => //.
      all: iFrameSteps.
    Qed.

    Lemma ws_bdeque_2٠pop𑁒spec t γ ι cap ws :
      <<<
        ws_bdeque_2۰inv t γ ι cap ∗
        ws_bdeque_2۰owner t γ ws
      | ∀∀ vs,
        ws_bdeque_2۰model γ vs
      >>>
        ws_bdeque_2٠pop #t @ ↑ι
      <<<
        ∃∃ o ws',
        ⌜vs `suffix_of` ws⌝ ∗
        match o with
        | None =>
            ⌜vs = []⌝ ∗
            ⌜ws' = []⌝ ∗
            ws_bdeque_2۰model γ []
        | Some v =>
            ∃ vs',
            ⌜vs = vs' ++ [v]⌝ ∗
            ⌜ws' = vs'⌝ ∗
            ws_bdeque_2۰model γ vs'
        end
      | RET o;
        ws_bdeque_2۰owner t γ ws'
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      wp۰rec.

      awp۰apply+ (ws_bdeque_1٠pop𑁒spec with "[$]").
      iInv "Hinv" as "(:inv۰inner)".
      iApply (aacc𑁒aupd𑁒commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps. iIntros "%o %𝑠𝑙𝑜𝑡s_owner (_ & Ho)".
      iDestruct (model𑁒owner𑁒agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (model𑁒pop with "Howner Hmodel₁ Hmodel₂") as "(Howner & Hmodel₁ & Hmodel₂)".
      destruct o as [𝑠𝑙𝑜𝑡 |].

      - iDestruct "Ho" as "(%𝑠𝑙𝑜𝑡s' & %Hslots & -> & Hbase_model)".
        apply fmap𑁒snoc𑁒inv in Hslots as (slots' & slot & -> & -> & ->).
        iDestruct (big_sepL2𑁒snoc𑁒inv𑁒l with "Hslots") as "(%vs' & %v & -> & Hslots & Hslot)".
        rewrite removelast_last.
        iExists (Some v), vs'. iFrameSteps. iPureIntro.
        etrans. 2: done. simpl_length. lia.

      - iDestruct "Ho" as "(%Hslots & -> & Hbase_model)".
        apply fmap_nil_inv in Hslots as ->.
        iDestruct (big_sepL2_nil_inv_l with "Hslots") as %->.
        iExists None. iFrameSteps. do 2 (iExists []; iSteps).
    Qed.
  End ws_bdeque_2۰G.

  #[global] Opaque ws_bdeque_2۰inv.
  #[global] Opaque ws_bdeque_2۰model.
  #[global] Opaque ws_bdeque_2۰owner.
End base.

Require zoo_saturn.ws_bdeque_2__opaque.

Section ws_bdeque_2۰G.
  Context `{ws_bdeque_2۰G : WsBdeque2G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition ws_bdeque_2۰inv t ι cap : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ws_bdeque_2۰inv 𝑡 γ ι cap.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition ws_bdeque_2۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ws_bdeque_2۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition ws_bdeque_2۰owner t ws : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ws_bdeque_2۰owner 𝑡 γ ws.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Howner{_{}}
      )
    ".

  #[global] Instance ws_bdeque_2۰model𑁒timeless γ vs :
    Timeless (ws_bdeque_2۰model γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_bdeque_2۰owner𑁒timeless γ ws :
    Timeless (ws_bdeque_2۰owner γ ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_bdeque_2۰inv𑁒persistent t ι cap :
    Persistent (ws_bdeque_2۰inv t ι cap).
  Proof.
    apply _.
  Qed.

  Lemma ws_bdeque_2۰model𑁒valid t ι cap vs :
    ws_bdeque_2۰inv t ι cap -∗
    ws_bdeque_2۰model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_2۰model𑁒valid with "Hinv_1 Hmodel_2").
  Qed.
  Lemma ws_bdeque_2۰model𑁒exclusive t vs1 vs2 :
    ws_bdeque_2۰model t vs1 -∗
    ws_bdeque_2۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_2۰model𑁒exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma ws_bdeque_2۰owner𑁒exclusive t ws1 ws2 :
    ws_bdeque_2۰owner t ws1 -∗
    ws_bdeque_2۰owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_2۰owner𑁒exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma ws_bdeque_2𑁒owner𑁒model γ ws vs :
    ws_bdeque_2۰owner γ ws -∗
    ws_bdeque_2۰model γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_2𑁒owner𑁒model with "Howner_1 Hmodel_2").
  Qed.

  Lemma ws_bdeque_2٠create𑁒spec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      ws_bdeque_2٠create #cap
    {{{
      t
    , RET t;
      ws_bdeque_2۰inv t ι ₊cap ∗
      ws_bdeque_2۰model t [] ∗
      ws_bdeque_2۰owner t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.ws_bdeque_2٠create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)". 1: done.
    iMod (meta𑁒set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma ws_bdeque_2٠size𑁒spec t ι cap ws :
    <<<
      ws_bdeque_2۰inv t ι cap ∗
      ws_bdeque_2۰owner t ws
    | ∀∀ vs,
      ws_bdeque_2۰model t vs
    >>>
      ws_bdeque_2٠size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_2۰model t vs
    | RET #(length vs);
      ws_bdeque_2۰owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_bdeque_2٠size𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_2٠is_empty𑁒spec t ι cap ws :
    <<<
      ws_bdeque_2۰inv t ι cap ∗
      ws_bdeque_2۰owner t ws
    | ∀∀ vs,
      ws_bdeque_2۰model t vs
    >>>
      ws_bdeque_2٠is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_2۰model t vs
    | RET #(bool_decide (vs = []%list));
      ws_bdeque_2۰owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_bdeque_2٠is_empty𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_2٠push𑁒spec t ι cap ws v :
    <<<
      ws_bdeque_2۰inv t ι cap ∗
      ws_bdeque_2۰owner t ws
    | ∀∀ vs,
      ws_bdeque_2۰model t vs
    >>>
      ws_bdeque_2٠push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_2۰model t (if b then vs ++ [v] else vs)
    | RET #b;
      ws_bdeque_2۰owner t (if b then vs ++ [v] else ws)
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_bdeque_2٠push𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_2٠steal𑁒spec t ι cap :
    <<<
      ws_bdeque_2۰inv t ι cap
    | ∀∀ vs,
      ws_bdeque_2۰model t vs
    >>>
      ws_bdeque_2٠steal t @ ↑ι
    <<<
      ws_bdeque_2۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.ws_bdeque_2٠steal𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_2٠pop𑁒spec t ι cap ws :
    <<<
      ws_bdeque_2۰inv t ι cap ∗
      ws_bdeque_2۰owner t ws
    | ∀∀ vs,
      ws_bdeque_2۰model t vs
    >>>
      ws_bdeque_2٠pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_bdeque_2۰model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          ws_bdeque_2۰model t vs'
      end
    | RET o;
      ws_bdeque_2۰owner t ws'
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.ws_bdeque_2٠pop𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1". 1: iSteps. iIntros "%o %ws' ($ & Ho)".
      iExists o, ws'. destruct o.
      all: iDecompose "Ho".
      all: iFrameSteps.
    }
  Qed.
End ws_bdeque_2۰G.

#[global] Opaque ws_bdeque_2۰inv.
#[global] Opaque ws_bdeque_2۰model.
#[global] Opaque ws_bdeque_2۰owner.
