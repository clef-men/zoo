From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  chain__types.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v w t dst : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Fixpoint chain_model tag t vs dst : iProp Σ :=
    match vs with
    | [] =>
        ⌜t = dst⌝
    | v :: vs =>
        ∃ l t',
        ⌜t = #l⌝ ∗
        from_option (λ tag, l ↦ₕ Header tag 2) True tag ∗
        l.[chain_next] ↦ t' ∗
        l.[chain_data] ↦ v ∗
        chain_model tag t' vs dst
    end.
  #[global] Arguments chain_model _ _ !_ _ / : assert.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l{} &
      %t{}' &
      {%Heq{eq}=->} &
      Hl{}_hdr &
      Hl{}_next &
      Hl{}_data &
      Hmodel{}'
    )".

  #[global] Instance chain_model_timeless tag t vs dst :
    Timeless (chain_model tag t vs dst).
  Proof.
    move: t. induction vs; apply _.
  Qed.

  Lemma chain_physical tag t vs dst :
    0 < length vs →
    chain_model tag t vs dst ⊢
    ⌜val_physical t⌝.
  Proof.
    intros Hlen. destruct vs as [| v vs]; first naive_solver lia.
    iSteps.
  Qed.
  Lemma chain_physically_distinct tag1 t1 vs1 dst1 tag2 t2 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    val_neq t1 t2 →
    chain_model tag1 t1 vs1 dst1 -∗
    chain_model tag2 t2 vs2 dst2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros Hlen1 Hlen2. destruct vs1, vs2; [naive_solver lia.. |].
    iSteps.
  Qed.
  Lemma chain_physically_distinct' tag t vs dst :
    0 < length vs →
    val_neq t t →
    chain_model tag t vs dst ⊢
    False.
  Proof.
    intros Hlen1 Hlen2. destruct vs; first naive_solver lia.
    iIntros "(:model) //".
  Qed.
  Lemma wp_equal_chain tag1 t1 vs1 dst1 tag2 t2 vs2 dst2 Φ :
    0 < length vs1 →
    0 < length vs2 →
    chain_model tag1 t1 vs1 dst1 -∗
    chain_model tag2 t2 vs2 dst2 -∗
    ( chain_model tag1 t1 vs1 dst1 -∗
      chain_model tag2 t2 vs2 dst2 -∗
        (⌜t1 ≠ t2⌝ -∗ Φ #false) ∧
        (⌜t1 = t2⌝ -∗ Φ #true)
    ) -∗
    WP t1 == t2 {{ Φ }}.
  Proof.
    intros Hlen1 Hlen2.
    destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2]; [naive_solver lia.. |].
    iIntros "(:model =1) (:model =2) HΦ".
    wp_pures.
    iDestruct ("HΦ" with "[$Hl1_hdr $Hl1_next $Hl1_data $Hmodel1' //] [$Hl2_hdr $Hl2_next $Hl2_data $Hmodel2' //]") as "HΦ".
    case_bool_decide.
    - iDestruct "HΦ" as "(_ & HΦ)". iSteps.
    - iDestruct "HΦ" as "(HΦ & _)". iSteps.
  Qed.

  Lemma chain_model_tag tag t vs dst :
    length vs ≠ 0 →
    chain_model (Some tag) t vs dst ⊢
      ∃ l,
      ⌜t = #l⌝ ∗
      l ↦ₕ Header tag 2.
  Proof.
    destruct vs as [| v vs]; first done.
    iSteps.
  Qed.

  Lemma chain_model_nil tag t dst :
    ⌜t = dst⌝ ⊣⊢
    chain_model tag t [] dst.
  Proof.
    iSteps.
  Qed.
  Lemma chain_model_nil_1 tag v :
    ⊢ chain_model tag v [] v.
  Proof.
    iSteps.
  Qed.
  Lemma chain_model_nil_2 tag t dst :
    chain_model tag t [] dst ⊢
    ⌜t = dst⌝.
  Proof.
    iSteps.
  Qed.

  Lemma chain_model_app_1 vs1 vs2 tag t vs dst :
    vs = vs1 ++ vs2 →
    chain_model tag t vs dst ⊢
      ∃ t',
      chain_model tag t vs1 t' ∗
      chain_model tag t' vs2 dst.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t vs); first iSteps.
    iIntros (->). rewrite -app_comm_cons. iIntros "(:model)".
    iDestruct ("IH" with "[//] Hmodel'") as "(%t'' & Hmodel' & Hmodel'')".
    iSteps.
  Qed.
  Lemma chain_model_app_2 tag t1 vs1 t2 vs2 dst :
    chain_model tag t1 vs1 t2 -∗
    chain_model tag t2 vs2 dst -∗
    chain_model tag t1 (vs1 ++ vs2) dst.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1); iSteps.
  Qed.
  Lemma chain_model_app tag t vs vs1 vs2 dst :
    vs = vs1 ++ vs2 →
    chain_model tag t vs dst ⊣⊢
      ∃ t',
      chain_model tag t vs1 t' ∗
      chain_model tag t' vs2 dst.
  Proof.
    intros ->.
    iSplit.
    - iApply chain_model_app_1; first done.
    - iIntros "(%t' & Hmodel & Hmodel')".
      iApply (chain_model_app_2 with "Hmodel Hmodel'").
  Qed.

  Lemma chain_model_snoc tag t vs vs' v dst :
    vs = vs' ++ [v] →
    chain_model tag t vs dst ⊣⊢
      ∃ t',
      chain_model tag t vs' t' ∗
      chain_model tag t' [v] dst.
  Proof.
    intros ->. rewrite chain_model_app //.
  Qed.
  Lemma chain_model_snoc_1 tag t vs vs' v dst :
    vs = vs' ++ [v] →
    chain_model tag t (vs ++ [v]) dst ⊢
      ∃ t',
      chain_model tag t vs t' ∗
      chain_model tag t' [v] dst.
  Proof.
    intros ->. rewrite chain_model_snoc //.
  Qed.
  Lemma chain_model_snoc_2 tag t1 vs t2 v dst :
    chain_model tag t1 vs t2 -∗
    chain_model tag t2 [v] dst -∗
    chain_model tag t1 (vs ++ [v]) dst.
  Proof.
    rewrite (chain_model_snoc _ _ (vs ++ [v])) //. iSteps.
  Qed.

  Lemma chain_model_exclusive t tag1 vs1 dst1 tag2 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    chain_model tag1 t vs1 dst1 -∗
    chain_model tag2 t vs2 dst2 -∗
    False.
  Proof.
    intros.
    destruct vs1, vs2; [naive_solver lia.. |].
    iIntros "(:model =1 eq=1) (:model =2 eq=2)". simplify.
    iCombine "Hl1_next Hl2_next" gives %(? & _). done.
  Qed.

  Lemma chain_block_spec tag t vs dst v :
    {{{
      chain_model tag t vs dst
    }}}
      Block Mutable (default 0 tag) [Val t; Val v]
    {{{ t',
      RET t';
      chain_model tag t' (v :: vs) dst
    }}}.
  Proof.
    destruct tag; iSteps.
  Qed.

  Lemma chain_data_spec tag t v vs dst :
    {{{
      chain_model tag t (v :: vs) dst
    }}}
      t.{chain_data}
    {{{
      RET v;
      chain_model tag t (v :: vs) dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain_next_spec tag t v vs dst :
    {{{
      chain_model tag t (v :: vs) dst
    }}}
      t.{chain_next}
    {{{ t',
      RET t';
      chain_model tag t [v] t' ∗
      chain_model tag t' vs dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma chain_next_spec_singleton tag t v dst :
    {{{
      chain_model tag t [v] dst
    }}}
      t.{chain_next}
    {{{
      RET dst;
      chain_model tag t [v] dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain_set_data_spec tag t v vs dst w :
    {{{
      chain_model tag t (v :: vs) dst
    }}}
      t <-{chain_data} w
    {{{
      RET ();
      chain_model tag t (w :: vs) dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain_set_next_spec tag t v vs dst v' :
    {{{
      chain_model tag t (v :: vs) dst
    }}}
      t <-{chain_next} v'
    {{{ t',
      RET ();
      chain_model tag t [v] v' ∗
      chain_model tag t' vs dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma chain_set_next_spec_singleton tag t v dst dst' :
    {{{
      chain_model tag t [v] dst
    }}}
      t <-{chain_next} dst'
    {{{
      RET ();
      chain_model tag t [v] dst'
    }}}.
  Proof.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque chain_model.
