Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.chain__types.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type v w t dst : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Fixpoint chain۰model tag t vs dst : iProp Σ :=
    match vs with
    | [] =>
        ⌜t = dst⌝
    | v :: vs =>
        ∃ l t',
        ⌜t = #l⌝ ∗
        from_option (λ tag, l ↦ₕ Header tag 2) True tag ∗
        l.[chain_next] ↦ t' ∗
        l.[chain_data] ↦ v ∗
        chain۰model tag t' vs dst
    end.
  #[global] Arguments chain۰model _ _ !_ _ / : assert.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{}
      & %t{}'
      & {%Heq{eq};->}
      & Hl{}_header
      & Hl{}_next
      & Hl{}_data
      & Hmodel{}'
      )
    ".

  #[global] Instance chain۰model𑁒timeless tag t vs dst :
    Timeless (chain۰model tag t vs dst).
  Proof.
    move: t. induction vs; apply _.
  Qed.

  Lemma chain𑁒physically𑁒distinct tag1 t1 vs1 dst1 tag2 t2 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    t1 ≉ t2 →
    chain۰model tag1 t1 vs1 dst1 -∗
    chain۰model tag2 t2 vs2 dst2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros Hlen1 Hlen2. destruct vs1, vs2; [naive_solver lia.. |].
    iSteps.
  Qed.
  Lemma chain𑁒physically𑁒distinct' tag t vs dst :
    0 < length vs →
    t ≉ t →
    chain۰model tag t vs dst ⊢
    False.
  Proof.
    intros Hlen1 Hlen2. destruct vs; first naive_solver lia.
    iIntros "(:model) //".
  Qed.
  Lemma wp𑁒equal𑁒chain tag1 t1 vs1 dst1 tag2 t2 vs2 dst2 Φ :
    0 < length vs1 →
    0 < length vs2 →
    chain۰model tag1 t1 vs1 dst1 -∗
    chain۰model tag2 t2 vs2 dst2 -∗
    ( chain۰model tag1 t1 vs1 dst1 -∗
      chain۰model tag2 t2 vs2 dst2 -∗
        (⌜t1 ≠ t2⌝ -∗ Φ false%V) ∧
        (⌜t1 = t2⌝ -∗ Φ true%V)
    ) -∗
    WP t1 == t2 {{ Φ }}.
  Proof.
    intros Hlen1 Hlen2.
    destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2]; [naive_solver lia.. |].
    iIntros "(:model =1) (:model =2) HΦ".
    wp۰pures.
    iDestruct ("HΦ" with "[$Hl1_header $Hl1_next $Hl1_data $Hmodel1' //] [$Hl2_header $Hl2_next $Hl2_data $Hmodel2' //]") as "HΦ".
    case_bool_decide.
    - iDestruct "HΦ" as "(_ & HΦ)". iSteps.
    - iDestruct "HΦ" as "(HΦ & _)". iSteps.
  Qed.

  Lemma chain۰model𑁒tag tag t vs dst :
    length vs ≠ 0 →
    chain۰model (Some tag) t vs dst ⊢
      ∃ l,
      ⌜t = #l⌝ ∗
      l ↦ₕ Header tag 2.
  Proof.
    destruct vs as [| v vs]; first done.
    iSteps.
  Qed.

  Lemma chain۰model𑁒nil tag t dst :
    ⌜t = dst⌝ ⊣⊢
    chain۰model tag t [] dst.
  Proof.
    iSteps.
  Qed.
  Lemma chain۰model𑁒nil₁ tag v :
    ⊢ chain۰model tag v [] v.
  Proof.
    iSteps.
  Qed.
  Lemma chain۰model𑁒nil₂ tag t dst :
    chain۰model tag t [] dst ⊢
    ⌜t = dst⌝.
  Proof.
    iSteps.
  Qed.

  Lemma chain۰model𑁒app₁ vs1 vs2 tag t vs dst :
    vs = vs1 ++ vs2 →
    chain۰model tag t vs dst ⊢
      ∃ t',
      chain۰model tag t vs1 t' ∗
      chain۰model tag t' vs2 dst.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t vs); first iSteps.
    iIntros (->). rewrite -app_comm_cons. iIntros "(:model)".
    iDestruct ("IH" with "[//] Hmodel'") as "(%t'' & Hmodel' & Hmodel'')".
    iSteps.
  Qed.
  Lemma chain۰model𑁒app₂ tag t1 vs1 t2 vs2 dst :
    chain۰model tag t1 vs1 t2 -∗
    chain۰model tag t2 vs2 dst -∗
    chain۰model tag t1 (vs1 ++ vs2) dst.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1); iSteps.
  Qed.
  Lemma chain۰model𑁒app tag t vs vs1 vs2 dst :
    vs = vs1 ++ vs2 →
    chain۰model tag t vs dst ⊣⊢
      ∃ t',
      chain۰model tag t vs1 t' ∗
      chain۰model tag t' vs2 dst.
  Proof.
    intros ->.
    iSplit.
    - iApply chain۰model𑁒app₁; first done.
    - iIntros "(%t' & Hmodel & Hmodel')".
      iApply (chain۰model𑁒app₂ with "Hmodel Hmodel'").
  Qed.

  Lemma chain۰model𑁒snoc tag t vs vs' v dst :
    vs = vs' ++ [v] →
    chain۰model tag t vs dst ⊣⊢
      ∃ t',
      chain۰model tag t vs' t' ∗
      chain۰model tag t' [v] dst.
  Proof.
    intros ->. rewrite chain۰model𑁒app //.
  Qed.
  Lemma chain۰model𑁒snoc₁ tag t vs vs' v dst :
    vs = vs' ++ [v] →
    chain۰model tag t (vs ++ [v]) dst ⊢
      ∃ t',
      chain۰model tag t vs t' ∗
      chain۰model tag t' [v] dst.
  Proof.
    intros ->. rewrite chain۰model𑁒snoc //.
  Qed.
  Lemma chain۰model𑁒snoc₂ tag t1 vs t2 v dst :
    chain۰model tag t1 vs t2 -∗
    chain۰model tag t2 [v] dst -∗
    chain۰model tag t1 (vs ++ [v]) dst.
  Proof.
    rewrite (chain۰model𑁒snoc _ _ (vs ++ [v])) //. iSteps.
  Qed.

  Lemma chain۰model𑁒exclusive t tag1 vs1 dst1 tag2 vs2 dst2 :
    0 < length vs1 →
    0 < length vs2 →
    chain۰model tag1 t vs1 dst1 -∗
    chain۰model tag2 t vs2 dst2 -∗
    False.
  Proof.
    intros.
    destruct vs1, vs2; [naive_solver lia.. |].
    iIntros "(:model =1 eq=1) (:model =2 eq=2)". simplify.
    iCombine "Hl1_next Hl2_next" gives %(? & _). done.
  Qed.

  Lemma chain٠block𑁒spec tag t vs dst v :
    {{{
      chain۰model tag t vs dst
    }}}
      Block Mutable (default 0%nat tag) [Val t; Val v]
    {{{
      t'
    , RET t';
      chain۰model tag t' (v :: vs) dst
    }}}.
  Proof.
    destruct tag; iSteps.
  Qed.

  Lemma chain٠data𑁒spec tag t v vs dst :
    {{{
      chain۰model tag t (v :: vs) dst
    }}}
      t.{chain_data}
    {{{
      RET v;
      chain۰model tag t (v :: vs) dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain٠next𑁒spec tag t v vs dst :
    {{{
      chain۰model tag t (v :: vs) dst
    }}}
      t.{chain_next}
    {{{
      t'
    , RET t';
      chain۰model tag t [v] t' ∗
      chain۰model tag t' vs dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma chain٠next𑁒spec𑁒singleton tag t v dst :
    {{{
      chain۰model tag t [v] dst
    }}}
      t.{chain_next}
    {{{
      RET dst;
      chain۰model tag t [v] dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain٠set_data𑁒spec tag t v vs dst w :
    {{{
      chain۰model tag t (v :: vs) dst
    }}}
      t <-{chain_data} w
    {{{
      RET ();
      chain۰model tag t (w :: vs) dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma chain٠set_next𑁒spec tag t v vs dst v' :
    {{{
      chain۰model tag t (v :: vs) dst
    }}}
      t <-{chain_next} v'
    {{{
      t'
    , RET ();
      chain۰model tag t [v] v' ∗
      chain۰model tag t' vs dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma chain٠set_next𑁒spec𑁒singleton tag t v dst dst' :
    {{{
      chain۰model tag t [v] dst
    }}}
      t <-{chain_next} dst'
    {{{
      RET ();
      chain۰model tag t [v] dst'
    }}}.
  Proof.
    iSteps.
  Qed.
End zoo۰G.

#[global] Opaque chain۰model.
