From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base
  chain__types.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v w t hd tl dst : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Fixpoint chain_model t vs dst : iProp Σ :=
    match vs with
    | [] =>
        ⌜t = dst⌝
    | v :: vs =>
        ∃ l t',
        ⌜t = #l⌝ ∗
        l.[chain_head] ↦ v ∗
        l.[chain_tail] ↦ t' ∗
        chain_model t' vs dst
    end.
  #[global] Arguments chain_model _ !_ _ / : assert.

  #[global] Instance chain_model_timeless t vs dst :
    Timeless (chain_model t vs dst).
  Proof.
    move: t. induction vs; apply _.
  Qed.

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
    WP t1 == t2 {{ Φ }}.
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
  Lemma chain_model_app t vs vs1 vs2 dst :
    vs = vs1 ++ vs2 →
    chain_model t vs dst ⊣⊢
      ∃ t',
      chain_model t vs1 t' ∗
      chain_model t' vs2 dst.
  Proof.
    intros ->.
    iSplit.
    - iApply chain_model_app_1; first done.
    - iIntros "(%t' & Hmodel & Hmodel')".
      iApply (chain_model_app_2 with "Hmodel Hmodel'").
  Qed.

  Lemma chain_model_snoc t vs vs' v dst :
    vs = vs' ++ [v] →
    chain_model t vs dst ⊣⊢
      ∃ t',
      chain_model t vs' t' ∗
      chain_model t' [v] dst.
  Proof.
    intros ->. rewrite chain_model_app //.
  Qed.
  Lemma chain_model_snoc_1 t vs vs' v dst :
    vs = vs' ++ [v] →
    chain_model t (vs ++ [v]) dst ⊢
      ∃ t',
      chain_model t vs t' ∗
      chain_model t' [v] dst.
  Proof.
    intros ->. rewrite chain_model_snoc //.
  Qed.
  Lemma chain_model_snoc_2 t1 vs t2 v dst :
    chain_model t1 vs t2 -∗
    chain_model t2 [v] dst -∗
    chain_model t1 (vs ++ [v]) dst.
  Proof.
    rewrite (chain_model_snoc _ (vs ++ [v])) //. iSteps.
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
      { v, t }
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
      t.{chain_head}
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
      t.{chain_tail}
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
      t <-{chain_head} w
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
      t <-{chain_tail} w
    {{{ t',
      RET ();
      chain_model t [v] w ∗
      chain_model t' vs dst
    }}}.
  Proof.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque chain_model.
