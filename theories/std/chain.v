From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v w t hd tl dst : val.

#[local] Notation "'head'" := (
  in_type "t" 0
)(in custom zoo_field
).
#[local] Notation "'tail'" := (
  in_type "t" 1
)(in custom zoo_field
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

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Fixpoint chain_model t vs dst : iProp Σ :=
    match vs with
    | [] =>
        ⌜t = dst⌝
    | v :: vs =>
        ∃ l t',
        ⌜t = #l⌝ ∗
        l.[head] ↦ v ∗
        l.[tail] ↦ t' ∗
        chain_model t' vs dst
    end.
  #[global] Arguments chain_model _ !_ _ / : assert.

  Lemma chain_physical t vs dst :
    0 < length vs →
    chain_model t vs dst ⊢
    ⌜val_physical t⌝.
  Proof.
    intros Hlen. destruct vs as [| v vs]; first naive_solver lia.
    iSteps.
  Qed.
  Lemma chain_physically_distinct t1 vs1 dst1 t2 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    val_neq t1 t2 →
    chain_model t1 vs1 dst1 -∗
    chain_model t2 vs2 dst2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros Hlen1 Hlen2. destruct vs1, vs2; [naive_solver lia.. |].
    iSteps.
  Qed.
  Lemma chain_physically_distinct' t vs dst :
    0 < length vs →
    val_neq t t →
    chain_model t vs dst ⊢
    False.
  Proof.
    intros Hlen1 Hlen2. destruct vs; first naive_solver lia.
    iIntros "(%l & %t' & -> & _) //".
  Qed.
  Lemma wp_equal_chain t1 vs1 dst1 t2 vs2 dst2 Φ :
    0 < length vs1 →
    0 < length vs2 →
    chain_model t1 vs1 dst1 -∗
    chain_model t2 vs2 dst2 -∗
    ( chain_model t1 vs1 dst1 -∗
      chain_model t2 vs2 dst2 -∗
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

  #[global] Instance chain_model_timeless t vs dst :
    Timeless (chain_model t vs dst).
  Proof.
    move: t. induction vs; apply _.
  Qed.

  Lemma chain_model_nil t dst :
    ⌜t = dst⌝ ⊣⊢
    chain_model t [] dst.
  Proof.
    iSteps.
  Qed.
  Lemma chain_model_nil_1 v :
    ⊢ chain_model v [] v.
  Proof.
    iSteps.
  Qed.
  Lemma chain_model_nil_2 t dst :
    chain_model t [] dst ⊢
    ⌜t = dst⌝.
  Proof.
    iSteps.
  Qed.

  Lemma chain_model_app_1 vs1 vs2 t vs dst :
    vs = vs1 ++ vs2 →
    chain_model t vs dst ⊢
      ∃ t',
      chain_model t vs1 t' ∗
      chain_model t' vs2 dst.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t vs); first iSteps.
    iIntros (->). rewrite -app_comm_cons. iIntros "(%l & %t' & -> & Hhd & Htl & Hmodel')".
    iDestruct ("IH" with "[//] Hmodel'") as "(%t'' & Hmodel' & Hmodel'')".
    iSteps.
  Qed.
  Lemma chain_model_app_2 t1 vs1 t2 vs2 dst :
    chain_model t1 vs1 t2 -∗
    chain_model t2 vs2 dst -∗
    chain_model t1 (vs1 ++ vs2) dst.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1); iSteps.
  Qed.
  Lemma chain_model_app t vs1 vs2 dst :
    chain_model t (vs1 ++ vs2) dst ⊣⊢
      ∃ t',
      chain_model t vs1 t' ∗
      chain_model t' vs2 dst.
  Proof.
    iSplit.
    - iApply chain_model_app_1; first done.
    - iIntros "(%t' & Hmodel & Hmodel')".
      iApply (chain_model_app_2 with "Hmodel Hmodel'").
  Qed.

  Lemma chain_model_exclusive t vs1 dst1 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    chain_model t vs1 dst1 -∗
    chain_model t vs2 dst2 -∗
    False.
  Proof.
    intros.
    destruct vs1, vs2; [naive_solver lia.. |].
    iIntros "(%l1 & %t1' & %Heq1 & Hhd1 & _) (%l2 & %t2' & %Heq2 & Hhd2 & _)". simplify.
    iCombine "Hhd1 Hhd2" gives %(? & _). done.
  Qed.

  Lemma chain_cons_spec t vs dst v :
    {{{
      chain_model t vs dst
    }}}
      chain_cons v t
    {{{ t',
      RET t';
      chain_model t' (v :: vs) dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain_head_spec t v vs dst :
    {{{
      chain_model t (v :: vs) dst
    }}}
      chain_head t
    {{{
      RET v;
      chain_model t (v :: vs) dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain_tail_spec t v vs dst :
    {{{
      chain_model t (v :: vs) dst
    }}}
      chain_tail t
    {{{ t',
      RET t';
      chain_model t [v] t' ∗
      chain_model t' vs dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain_set_head_spec t v vs dst w :
    {{{
      chain_model t (v :: vs) dst
    }}}
      chain_set_head t w
    {{{
      RET ();
      chain_model t (w :: vs) dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma chain_set_tail_spec t v vs dst w :
    {{{
      chain_model t (v :: vs) dst
    }}}
      chain_set_tail t w
    {{{ t',
      RET ();
      chain_model t [v] w ∗
      chain_model t' vs dst
    }}}.
  Proof.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque chain_cons.
#[global] Opaque chain_head.
#[global] Opaque chain_tail.
#[global] Opaque chain_set_head.
#[global] Opaque chain_set_tail.

#[global] Opaque chain_model.
