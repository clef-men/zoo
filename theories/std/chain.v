From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Implicit Types l : loc.
Implicit Types v w t hd tl dst : val.

#[local] Notation "'head'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'tail'" := (
  in_type "t" 1
)(in custom zebre_field
).

Definition chain_cons : val :=
  λ: "v" "t",
    { "v"; "t" }.

Definition chain_head : val :=
  λ: "t",
    "t".{head}.
Definition chain_tail : val :=
  λ: "t",
    "t".{tail}.

Definition chain_set_head : val :=
  λ: "t" "v",
    "t" <-{head} "v".
Definition chain_set_tail : val :=
  λ: "t" "v",
    "t" <-{tail} "v".

Definition chain_advance : val :=
  rec: "chain_advance" "t" "i" :=
    if: "i" = #0 then (
      "t"
    ) else (
      "chain_advance" (chain_tail "t") ("i" - #1)
    ).

Definition chain_get : val :=
  λ: "t" "i",
    chain_head (chain_advance "t" "i").
Definition chain_set : val :=
  λ: "t" "i" "v",
    chain_set_head (chain_advance "t" "i") "v".

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Fixpoint chain_model t dq vs dst : iProp Σ :=
    match vs with
    | [] =>
        ⌜t = dst⌝
    | v :: vs =>
        ∃ l t',
        ⌜t = #l⌝ ∗
        l.[head] ↦{dq} v ∗
        l.[tail] ↦{dq} t' ∗
        chain_model t' dq vs dst
    end.
  #[global] Arguments chain_model _ _ !_ _ / : assert.

  Lemma chain_physical t dq vs dst :
    0 < length vs →
    chain_model t dq vs dst ⊢
    ⌜val_physical t⌝.
  Proof.
    intros Hlen. destruct vs as [| v vs]; first naive_solver lia.
    iSteps.
  Qed.
  Lemma chain_physically_distinct t1 dq1 vs1 dst1 t2 dq2 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    val_neq t1 t2 →
    chain_model t1 dq1 vs1 dst1 -∗
    chain_model t2 dq2 vs2 dst2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros Hlen1 Hlen2. destruct vs1, vs2; [naive_solver lia.. |].
    iSteps.
  Qed.
  Lemma chain_physically_distinct' t dq vs dst :
    0 < length vs →
    val_neq t t →
    chain_model t dq vs dst ⊢
    False.
  Proof.
    intros Hlen1 Hlen2. destruct vs; first naive_solver lia.
    iIntros "(%l & %t' & -> & _) //".
  Qed.
  Lemma wp_equal_chain t1 dq1 vs1 dst1 t2 dq2 vs2 dst2 Φ :
    0 < length vs1 →
    0 < length vs2 →
    chain_model t1 dq1 vs1 dst1 -∗
    chain_model t2 dq2 vs2 dst2 -∗
    ( chain_model t1 dq1 vs1 dst1 -∗
      chain_model t2 dq2 vs2 dst2 -∗
        (⌜t1 ≠ t2⌝ -∗ Φ #false) ∧
        (⌜t1 = t2⌝ -∗ Φ #true)
    ) -∗
    WP t1 = t2 {{ Φ }}.
  Proof.
    intros Hlen1 Hlen2.
    destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2]; [naive_solver lia.. |].
    iIntros "(%l1 & %t1' & -> & Hmodel1') (%l2 & %t2' & -> & Hmodel2') HΦ".
    wp_pures.
    iDestruct ("HΦ" with "[Hmodel1'] [Hmodel2']") as "HΦ"; [iSteps.. |].
    case_bool_decide.
    - iDestruct "HΦ" as "(_ & HΦ)". iSteps.
    - iDestruct "HΦ" as "(HΦ & _)". iSteps.
  Qed.

  #[global] Instance chain_model_timeless t dq vs dst :
    Timeless (chain_model t dq vs dst).
  Proof.
    move: t. induction vs; apply _.
  Qed.
  #[global] Instance chain_model_persistent t vs dst :
    Persistent (chain_model t DfracDiscarded vs dst).
  Proof.
    move: t. induction vs; apply _.
  Qed.

  #[global] Instance chain_model_fractional t vs dst :
    Fractional (λ q, chain_model t (DfracOwn q) vs dst).
  Proof.
    intros q1 q2. move: t. induction vs as [| v vs IH] => t /=; first iSteps.
    setoid_rewrite IH. setoid_rewrite pointsto_fractional.
    iSplit.
    - iIntros "(%l & %t' & -> & (Hhd1 & Hhd2) & (Htl1 & Htl2) & Hmodel1 & Hmodel2)".
      iSteps.
    - iIntros "((%l & %t' & -> & Hhd1 & Htl1 & Hmodel1) & (%_l & %_t' & %Heq & Hhd2 & Htl2 & Hmodel2))". injection Heq as <-.
      iDestruct (pointsto_agree with "Htl1 Htl2") as %<-.
      iSteps.
  Qed.
  #[global] Instance chain_model_as_fractional t q vs dst :
    AsFractional (chain_model t (DfracOwn q) vs dst) (λ q, chain_model t (DfracOwn q) vs dst) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma chain_model_nil t dq dst :
    ⌜t = dst⌝ ⊣⊢
    chain_model t dq [] dst.
  Proof.
    iSteps.
  Qed.
  Lemma chain_model_nil_1 v dq :
    ⊢ chain_model v dq [] v.
  Proof.
    iSteps.
  Qed.
  Lemma chain_model_nil_2 t dq dst :
    chain_model t dq [] dst ⊢
    ⌜t = dst⌝.
  Proof.
    iSteps.
  Qed.

  Lemma chain_model_app_1 dq t1 vs1 t2 vs2 dst :
    chain_model t1 dq vs1 t2 -∗
    chain_model t2 dq vs2 dst -∗
    chain_model t1 dq (vs1 ++ vs2) dst.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1); iSteps.
  Qed.
  Lemma chain_model_app_2 vs1 vs2 t dq vs dst :
    vs = vs1 ++ vs2 →
    chain_model t dq vs dst ⊢
      ∃ t',
      chain_model t dq vs1 t' ∗
      chain_model t' dq vs2 dst.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t vs); first iSteps.
    iIntros (->). rewrite -app_comm_cons. iIntros "(%l & %t' & -> & Hhd & Htl & Hmodel')".
    iDestruct ("IH" with "[//] Hmodel'") as "(%t'' & Hmodel' & Hmodel'')".
    iSteps.
  Qed.
  Lemma chain_model_app t dq vs1 vs2 dst :
    (∃ t', chain_model t dq vs1 t' ∗ chain_model t' dq vs2 dst) ⊣⊢
    chain_model t dq (vs1 ++ vs2) dst.
  Proof.
    iSplit.
    - iIntros "(%t' & Hmodel & Hmodel')".
      iApply (chain_model_app_1 with "Hmodel Hmodel'").
    - iApply chain_model_app_2; first done.
  Qed.

  Lemma chain_model_valid t dq vs dst :
    0 < length vs →
    chain_model t dq vs dst ⊢
    ⌜✓ dq⌝.
  Proof.
    intros Hlen. destruct vs as [| v vs]; first naive_solver lia.
    iIntros "(%l & %t' & -> & Hhd & Htl & Hmodel')".
    iApply (pointsto_valid with "Hhd").
  Qed.
  Lemma chain_model_combine t dq1 vs1 dst1 dq2 vs2 dst2 :
    length vs1 ≤ length vs2 →
    chain_model t dq1 vs1 dst1 -∗
    chain_model t dq2 vs2 dst2 -∗
      chain_model t (dq1 ⋅ dq2) vs1 dst1 ∗
      chain_model dst1 dq2 (drop (length vs1) vs2) dst2 ∗
      ⌜vs1 = take (length vs1) vs2⌝.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t vs2); first iSteps.
    destruct vs2 as [| v2 vs2].
    - iSteps. lia.
    - iIntros "%Hlen (%l & %t' & -> & Hhd1 & Htl1 & Hmodel'1) (%_l & %_t' & %Heq & Hhd2 & Htl2 & Hmodel'2)". injection Heq as <-.
      simpl in Hlen. apply le_S_n in Hlen.
      iDestruct (pointsto_combine with "Hhd1 Hhd2") as "(Hhd & <-)".
      iDestruct (pointsto_combine with "Htl1 Htl2") as "(Htl & <-)".
      iDestruct ("IH" with "[] Hmodel'1 Hmodel'2") as "(Hmodel' & Hmodel'2 & ->)"; first done.
      rewrite /= take_length min_l //. iSteps.
  Qed.
  Lemma chain_model_combine' t dq1 vs1 dst1 dq2 vs2 dst2 :
    length vs1 = length vs2 →
    chain_model t dq1 vs1 dst1 -∗
    chain_model t dq2 vs2 dst2 -∗
      chain_model t (dq1 ⋅ dq2) vs1 dst1 ∗
      ⌜vs1 = vs2 ∧ dst1 = dst2⌝.
  Proof.
    iIntros "%Hlen Hmodel1 Hmodel2".
    iDestruct (chain_model_combine with "Hmodel1 Hmodel2") as "($ & Hmodel2 & ->)"; first lia.
    rewrite Hlen take_length min_l; first lia.
    rewrite drop_all. iDestruct "Hmodel2" as %->.
    rewrite take_ge //.
  Qed.
  Lemma chain_model_valid_2 t dq1 vs1 dst1 dq2 vs2 dst2 :
    0 < length vs1 ≤ length vs2 →
    chain_model t dq1 vs1 dst1 -∗
    chain_model t dq2 vs2 dst2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = take (length vs1) vs2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (chain_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & _ & %)"; first lia.
    iDestruct (chain_model_valid with "Hmodel") as %?; first lia.
    iSteps.
  Qed.
  Lemma chain_model_valid_2' t dq1 vs1 dst1 dq2 vs2 dst2 :
    0 < length vs1 →
    length vs1 = length vs2 →
    chain_model t dq1 vs1 dst1 -∗
    chain_model t dq2 vs2 dst2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2 ∧ dst1 = dst2⌝.
  Proof.
    iIntros "% % Hmodel1 Hmodel2".
    iDestruct (chain_model_combine' with "Hmodel1 Hmodel2") as "(Hmodel & <- & <-)"; first done.
    iDestruct (chain_model_valid with "Hmodel") as %?; first done.
    iSteps.
  Qed.
  Lemma chain_model_agree t dq1 vs1 dst1 dq2 vs2 dst2 :
    length vs1 = length vs2 →
    chain_model t dq1 vs1 dst1 -∗
    chain_model t dq2 vs2 dst2 -∗
    ⌜vs1 = vs2 ∧ dst1 = dst2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (chain_model_combine' with "Hmodel1 Hmodel2") as "(_ & <- & <-)"; first done.
    iSteps.
  Qed.
  Lemma chain_model_dfrac_ne t1 dq1 vs1 dst1 t2 dq2 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    ¬ ✓ (dq1 ⋅ dq2) →
    chain_model t1 dq1 vs1 dst1 -∗
    chain_model t2 dq2 vs2 dst2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros. destruct vs1, vs2; [naive_solver lia.. |].
    iIntros "(%l1 & %t1' & %Heq1 & Hhd1 & _) (%l2 & %t2' & %Heq2 & Hhd2 & _) %Heq". simplify.
    iCombine "Hhd1 Hhd2" gives %(? & _). done.
  Qed.
  Lemma chain_model_ne t1 vs1 dst1 t2 dq2 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    chain_model t1 (DfracOwn 1) vs1 dst1 -∗
    chain_model t2 dq2 vs2 dst2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros.
    iApply chain_model_dfrac_ne; [done.. | intros []%exclusive_l; apply _].
  Qed.
  Lemma chain_model_exclusive t vs1 dst1 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    chain_model t (DfracOwn 1) vs1 dst1 -∗
    chain_model t (DfracOwn 1) vs2 dst2 -∗
    False.
  Proof.
    iIntros "% % Hmodel1 Hmodel2".
    iDestruct (chain_model_ne with "Hmodel1 Hmodel2") as %?; done.
  Qed.
  Lemma chain_model_persist t dq vs dst :
    chain_model t dq vs dst ⊢ |==>
    chain_model t DfracDiscarded vs dst.
  Proof.
    iInduction vs as [| v vs] "IH" forall (t); iSteps.
  Qed.
  Lemma chain_model_relax {t vs dst} dq :
    ✓ dq →
    chain_model t (DfracOwn 1) vs dst ⊢ |==>
    chain_model t dq vs dst.
  Proof.
    iInduction vs as [| v vs] "IH" forall (t); first iSteps.
    iIntros "%Hdq (%l & %t' & -> & Hhd & Htl & Hmodel')".
    iMod (pointsto_relax with "Hhd") as "Hhd"; first done.
    iMod (pointsto_relax with "Htl") as "Htl"; first done.
    iSteps.
  Qed.

  Lemma chain_cons_spec' t dq vs dst v :
    {{{
      chain_model t dq vs dst
    }}}
      chain_cons v t
    {{{ t',
      RET t';
      chain_model t' (DfracOwn 1) [v] t ∗
      chain_model t dq vs dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma chain_cons_spec t dq vs dst v :
    ✓ dq →
    {{{
      chain_model t dq vs dst
    }}}
      chain_cons v t
    {{{ t',
      RET t';
      chain_model t' dq (v :: vs) dst
    }}}.
  Proof.
    iIntros "%Hdq %Φ Hmodel HΦ".
    iApply wp_fupd.
    wp_apply (chain_cons_spec' with "Hmodel") as (t') "(Hmodel' & Hmodel)".
    iMod (chain_model_relax with "Hmodel'") as "Hmodel'"; first done.
    iDestruct (chain_model_app_1 with "Hmodel' Hmodel") as "Hmodel'".
    iApply ("HΦ" with "Hmodel'").
  Qed.

  Lemma chain_head_spec t dq v vs dst :
    {{{
      chain_model t dq (v :: vs) dst
    }}}
      chain_head t
    {{{
      RET v;
      chain_model t dq (v :: vs) dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma chain_tail_spec t dq v vs dst :
    {{{
      chain_model t dq (v :: vs) dst
    }}}
      chain_tail t
    {{{ t',
      RET t';
      chain_model t dq [v] t' ∗
      chain_model t' dq vs dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain_set_head_spec t v vs dst w :
    {{{
      chain_model t (DfracOwn 1) (v :: vs) dst
    }}}
      chain_set_head t w
    {{{
      RET ();
      chain_model t (DfracOwn 1) (w :: vs) dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma chain_set_tail_spec t v vs dst w :
    {{{
      chain_model t (DfracOwn 1) (v :: vs) dst
    }}}
      chain_set_tail t w
    {{{ t',
      RET ();
      chain_model t (DfracOwn 1) [v] w ∗
      chain_model t' (DfracOwn 1) vs dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain_advance_spec t dq vs dst (i : Z) :
    (0 ≤ i ≤ length vs)%Z →
    {{{
      chain_model t dq vs dst
    }}}
      chain_advance t #i
    {{{ t',
      RET t';
      chain_model t dq (take (Z.to_nat i) vs) t' ∗
      chain_model t' dq (drop (Z.to_nat i) vs) dst
    }}}.
  Proof.
    intros (Hi1 & Hi2). Z_to_nat i. move: Hi2 {Hi1}. rewrite -Nat2Z.inj_le Nat2Z.id.
    iInduction i as [| i] "IH" forall (t vs).
    all: iIntros "%Hi %Φ Hmodel HΦ"; wp_rec.
    1: iSteps.
    destruct vs as [| v vs]; simpl in Hi; first lia.
    wp_smart_apply (chain_tail_spec with "Hmodel") as (t') "(Hmodel & Hmodel')".
    assert (S i - 1 = i)%Z as -> by lia.
    wp_apply ("IH" with "[] Hmodel'") as (t'') "(Hmodel' & Hmodel'')"; first iSteps.
    iApply "HΦ". iFrame.
    iApply (chain_model_app_1 with "Hmodel Hmodel'").
  Qed.

  Lemma chain_get_spec t dq vs dst (i : Z) v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      chain_model t dq vs dst
    }}}
      chain_get t #i
    {{{
      RET v;
      chain_model t dq vs dst
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ Hmodel HΦ".
    Z_to_nat i. clear Hi. rewrite Nat2Z.id in Hlookup.
    opose proof* (lookup_lt_Some vs i); first done.
    wp_rec.
    wp_smart_apply (chain_advance_spec with "Hmodel") as (t') "(Hmodel & Hmodel')"; first lia.
    rewrite Nat2Z.id.
    rewrite -(take_drop i vs) lookup_app_r in Hlookup; first (rewrite take_length; lia).
    rewrite take_length min_l in Hlookup; first lia.
    rewrite Nat.sub_diag in Hlookup.
    destruct (drop i vs) as [| _v vs'] eqn:Heq; first done. apply (inj Some) in Hlookup as ->.
    wp_apply (chain_head_spec with "Hmodel'") as "Hmodel'".
    iApply "HΦ".
    iEval (rewrite -(take_drop i vs) Heq). iApply (chain_model_app_1 with "Hmodel Hmodel'").
  Qed.
  Lemma chain_set_spec t vs dst (i : Z) v w :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      chain_model t (DfracOwn 1) vs dst
    }}}
      chain_set t #i w
    {{{
      RET ();
      chain_model t (DfracOwn 1) (<[Z.to_nat i := w]> vs) dst
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ Hmodel HΦ".
    Z_to_nat i. clear Hi. rewrite Nat2Z.id in Hlookup.
    opose proof* (lookup_lt_Some vs i); first done.
    wp_rec.
    wp_smart_apply (chain_advance_spec with "Hmodel") as (t') "(Hmodel & Hmodel')"; first lia.
    rewrite Nat2Z.id.
    rewrite -(take_drop i vs) lookup_app_r in Hlookup; first (rewrite take_length; lia).
    rewrite take_length min_l in Hlookup; first lia.
    rewrite Nat.sub_diag in Hlookup.
    destruct (drop i vs) as [| _v vs'] eqn:Heq; first done. apply (inj Some) in Hlookup as ->.
    wp_apply (chain_set_head_spec with "Hmodel'") as "Hmodel'".
    iApply "HΦ".
    iEval (rewrite -(take_drop i vs) Heq).
    rewrite insert_app_r_alt; first (rewrite take_length; lia).
    rewrite take_length min_l; first lia.
    rewrite Nat.sub_diag.
    iApply (chain_model_app_1 with "Hmodel Hmodel'").
  Qed.
End zebre_G.

#[global] Opaque chain_cons.
#[global] Opaque chain_head.
#[global] Opaque chain_tail.
#[global] Opaque chain_set_head.
#[global] Opaque chain_set_tail.
#[global] Opaque chain_advance.
#[global] Opaque chain_get.
#[global] Opaque chain_set.

#[global] Opaque chain_model.
