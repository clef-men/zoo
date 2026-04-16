From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.saved_prop.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  ivar_4__code.
From zoo_std Require Import
  ivar_3
  ivar_4__types
  lst
  option.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v t ctx waiter : val.
Implicit Types waiters : list val.
Implicit Types ω : gname.
Implicit Types ωs : list gname.

Class Ivar4G Σ `{zoo_G : !ZooG Σ} :=
  { #[local] ivar_4_G_ivar_3_G :: Ivar3G Σ gname
  ; #[local] ivar_4_G_saved_prop_G :: SavedPropG Σ
  }.

Definition ivar_4_Σ := #[
  ivar_3_Σ gname ;
  saved_prop_Σ
].
#[global] Instance subG_ivar_4_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ivar_4_Σ Σ →
  Ivar4G Σ.
Proof.
  solve_inG.
Qed.

Section ivar_4_G.
  Context `{ivar_4_G : Ivar4G Σ}.
  Context `{context_name : Type}.

  Implicit Types 𝑐𝑡𝑥 : context_name.
  Implicit Types P : iProp Σ.
  Implicit Types Ps : list $ iProp Σ.
  Implicit Types Ψ Χ Ξ : val → iProp Σ.
  Implicit Types Γ : val → context_name → iProp Σ.

  #[local] Definition waiter_model_1 Γ t waiter P : iProp Σ :=
    ∀ ctx 𝑐𝑡𝑥 v,
    Γ ctx 𝑐𝑡𝑥 -∗
    ivar_3_result t v -∗
    WP waiter ctx v {{ res,
      ⌜res = ()%V⌝ ∗
      Γ ctx 𝑐𝑡𝑥 ∗
      ▷ □ P
    }}.
  #[local] Definition waiter_model_2 Γ t waiter ω : iProp Σ :=
    ∃ P,
    saved_prop ω P ∗
    waiter_model_1 Γ t waiter P.

  Definition ivar_4_inv t Ψ Ξ Γ :=
    ivar_3_inv t Ψ Ξ (waiter_model_2 Γ).

  Definition ivar_4_producer :=
    ivar_3_producer.

  Definition ivar_4_consumer :=
    ivar_3_consumer.

  Definition ivar_4_result :=
    ivar_3_result.
  Definition ivar_4_resolved t : iProp Σ :=
    ∃ v,
    ivar_4_result t v.

  Definition ivar_4_waiters t waiters Ps : iProp Σ :=
    ∃ ωs,
    ivar_3_waiters t waiters ωs ∗
    [∗ list] ω; P ∈ ωs; Ps, saved_prop ω P.
  #[local] Instance : CustomIpat "waiters" :=
    " ( %ωs
      & #Hwaiters
      & #Hωs
      )
    ".

  Definition ivar_4_waiter t waiter P : iProp Σ :=
    ∃ ω,
    ivar_3_waiter t waiter ω ∗
    saved_prop ω P.
  #[local] Instance : CustomIpat "waiter" :=
    " ( %ω
      & #Hwaiter
      & #Hω
      )
    ".

  #[global] Instance ivar_4_inv_contractive t n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ (≡{n}≡)) ==>
      (≡{n}≡)
    ) (ivar_4_inv t).
  Proof.
    rewrite /ivar_4_inv /waiter_model_2 /waiter_model_1.
    intros Ψ1 Ψ2 HΨ Ξ1 Ξ2 HΞ Γ1 Γ2 HΓ.
    f_equiv. 1,2: solve_proper.
    do 3 f_equiv.
    apply dist_dist_later.
    solve_proper.
  Qed.
  #[global] Instance ivar_4_inv_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_4_inv t).
  Proof.
    rewrite /ivar_4_inv /waiter_model_2 /waiter_model_1.
    solve_proper.
  Qed.
  #[global] Instance ivar_4_consumer_contractive t n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_4_consumer t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_4_consumer_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_4_consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ivar_4_producer_timeless t :
    Timeless (ivar_4_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_4_result_timeless t v :
    Timeless (ivar_4_result t v).
  Proof.
    apply _.
  Qed.

  #[global] Instance ivar_4_inv_persistent t Ψ Ξ Γ :
    Persistent (ivar_4_inv t Ψ Ξ Γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_4_result_persistent t v :
    Persistent (ivar_4_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_4_waiters_persistent t waiters Ps :
    Persistent (ivar_4_waiters t waiters Ps).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_4_waiter_persistent t waiter P :
    Persistent (ivar_4_waiter t waiter P).
  Proof.
    apply _.
  Qed.

  Lemma ivar_4_producer_exclusive t :
    ivar_4_producer t -∗
    ivar_4_producer t -∗
    False.
  Proof.
    apply ivar_3_producer_exclusive.
  Qed.

  Lemma ivar_4_consumer_wand {t Ψ Ξ Γ Χ1} Χ2 :
    ivar_4_inv t Ψ Ξ Γ -∗
    ivar_4_consumer t Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    ivar_4_consumer t Χ2.
  Proof.
    apply ivar_3_consumer_wand.
  Qed.
  Lemma ivar_4_consumer_divide {t Ψ Ξ Γ} Χs :
    ivar_4_inv t Ψ Ξ Γ -∗
    ivar_4_consumer t (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_4_consumer t Χ.
  Proof.
    apply ivar_3_consumer_divide.
  Qed.
  Lemma ivar_4_consumer_split {t Ψ Ξ Γ} Χ1 Χ2 :
    ivar_4_inv t Ψ Ξ Γ -∗
    ivar_4_consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_4_consumer t Χ1 ∗
      ivar_4_consumer t Χ2.
  Proof.
    apply ivar_3_consumer_split.
  Qed.

  Lemma ivar_4_result_agree t v1 v2 :
    ivar_4_result t v1 -∗
    ivar_4_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_3_result_agree.
  Qed.

  Lemma ivar_4_producer_result t v :
    ivar_4_producer t -∗
    ivar_4_result t v -∗
    False.
  Proof.
    apply ivar_3_producer_result.
  Qed.

  Lemma ivar_4_inv_result t Ψ Ξ Γ v :
    ivar_4_inv t Ψ Ξ Γ -∗
    ivar_4_result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    apply ivar_3_inv_result.
  Qed.
  Lemma ivar_4_inv_result' t Ψ Ξ Γ v :
    £ 1 -∗
    ivar_4_inv t Ψ Ξ Γ -∗
    ivar_4_result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    apply ivar_3_inv_result'.
  Qed.
  Lemma ivar_4_inv_result_consumer t Ψ Ξ Γ v Χ :
    ivar_4_inv t Ψ Ξ Γ -∗
    ivar_4_result t v -∗
    ivar_4_consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    apply ivar_3_inv_result_consumer.
  Qed.
  Lemma ivar_4_inv_result_consumer' t Ψ Ξ Γ v Χ :
    £ 2 -∗
    ivar_4_inv t Ψ Ξ Γ -∗
    ivar_4_result t v -∗
    ivar_4_consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    apply ivar_3_inv_result_consumer'.
  Qed.

  Lemma ivar_4_waiter_valid t waiters Ps waiter P :
    ivar_4_waiters t waiters Ps -∗
    ivar_4_waiter t waiter P -∗
      ∃ i P_,
      ⌜waiters !! i = Some waiter⌝ ∗
      ⌜Ps !! i = Some P_⌝ ∗
      ▷ (P ≡ P_).
  Proof.
    iIntros "(:waiters) (:waiter)".
    iDestruct (ivar_3_waiter_valid with "Hwaiters Hwaiter") as "(%i & %Hwaiters_lookup & %Hωs_lookup)".
    iDestruct (big_sepL2_lookup_l with "Hωs") as "(%P_ & %HPs_lookup & Hω_)". 1: done.
    iDestruct (saved_prop_agree with "Hω Hω_") as "Heq".
    iFrame "%#".
  Qed.

  Lemma ivar_4_create𑁒spec Ψ Ξ Γ :
    {{{
      True
    }}}
      ivar_4_create ()
    {{{
      t
    , RET t;
      ivar_4_inv t Ψ Ξ Γ ∗
      ivar_4_producer t ∗
      ivar_4_consumer t Ψ
    }}}.
  Proof.
    apply ivar_3_create𑁒spec.
  Qed.

  Lemma ivar_4_make𑁒spec Ψ Ξ Γ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_4_make v
    {{{
      t
    , RET t;
      ivar_4_inv t Ψ Ξ Γ ∗
      ivar_4_consumer t Ψ ∗
      ivar_4_result t v ∗
      ivar_4_waiters t [] []
    }}}.
  Proof.
    iIntros "%Φ (HΨ & HΞ) HΦ".

    wp_apply (ivar_3_make𑁒spec with "[$HΨ $HΞ]").
    iSteps.
  Qed.

  Lemma ivar_4_is_unset𑁒spec t Ψ Ξ Γ :
    {{{
      ivar_4_inv t Ψ Ξ Γ
    }}}
      ivar_4_is_unset t
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        ivar_4_resolved t
    }}}.
  Proof.
    apply ivar_3_is_unset𑁒spec.
  Qed.
  Lemma ivar_4_is_unset𑁒spec_result t Ψ Ξ Γ v :
    {{{
      ivar_4_inv t Ψ Ξ Γ ∗
      ivar_4_result t v
    }}}
      ivar_4_is_unset t
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    apply ivar_3_is_unset𑁒spec_result.
  Qed.

  Lemma ivar_4_is_set𑁒spec t Ψ Ξ Γ :
    {{{
      ivar_4_inv t Ψ Ξ Γ
    }}}
      ivar_4_is_set t
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        ivar_4_resolved t
      else
        True
    }}}.
  Proof.
    apply ivar_3_is_set𑁒spec.
  Qed.
  Lemma ivar_4_is_set𑁒spec_result t Ψ Ξ Γ v :
    {{{
      ivar_4_inv t Ψ Ξ Γ ∗
      ivar_4_result t v
    }}}
      ivar_4_is_set t
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    apply ivar_3_is_set𑁒spec_result.
  Qed.

  Lemma ivar_4_try_get𑁒spec t Ψ Ξ Γ :
    {{{
      ivar_4_inv t Ψ Ξ Γ
    }}}
      ivar_4_try_get t
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_4_result t v
      else
        True
    }}}.
  Proof.
    apply ivar_3_try_get𑁒spec.
  Qed.
  Lemma ivar_4_try_get𑁒spec_result t Ψ Ξ Γ v :
    {{{
      ivar_4_inv t Ψ Ξ Γ ∗
      ivar_4_result t v
    }}}
      ivar_4_try_get t
    {{{
      RET Some v;
      £ 2
    }}}.
  Proof.
    apply ivar_3_try_get𑁒spec_result.
  Qed.

  Lemma ivar_4_get𑁒spec t Ψ Ξ Γ v :
    {{{
      ivar_4_inv t Ψ Ξ Γ ∗
      ivar_4_result t v
    }}}
      ivar_4_get t
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    apply ivar_3_get𑁒spec.
  Qed.

  Lemma ivar_4_wait𑁒spec P Q t Ψ Ξ Γ waiter :
    {{{
      ivar_4_inv t Ψ Ξ Γ ∗
      Q ∗
      ( ∀ ctx 𝑐𝑡𝑥 v,
        Q -∗
        Γ ctx 𝑐𝑡𝑥 -∗
        ivar_3_result t v -∗
        WP waiter ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          Γ ctx 𝑐𝑡𝑥 ∗
          ▷ □ P
        }}
      )
    }}}
      ivar_4_wait t waiter
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_4_result t v ∗
        Q
      else
        ivar_4_waiter t waiter P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HQ & Hwaiter) HΦ".

    iMod (saved_prop_alloc P) as "(%ω & #Hω)".
    wp_apply (ivar_3_wait𑁒spec ω Q with "[$Hinv $HQ Hwaiter]") as (o) "Ho". 1: iSteps.

    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.

  Lemma ivar_4_set𑁒spec t Ψ Ξ Γ v :
    {{{
      ivar_4_inv t Ψ Ξ Γ ∗
      ivar_4_producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_4_set t v
    {{{
      waiters Ps
    , RET lst_to_val waiters;
      ivar_4_result t v ∗
      ivar_4_waiters t waiters Ps ∗
      [∗ list] waiter; P ∈ waiters; Ps,
        ∀ ctx 𝑐𝑡𝑥 v,
        Γ ctx 𝑐𝑡𝑥 -∗
        ivar_3_result t v -∗
        WP waiter ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          Γ ctx 𝑐𝑡𝑥 ∗
          ▷ □ P
        }}
    }}}.
  Proof.
    iIntros "%Φ (Hinv & Hproducer & HΨ & HΞ) HΦ".

    wp_apply (ivar_3_set𑁒spec _ Ψ Ξ with "[$]") as (waiters ωs) "(Hresult & Hwaiters & Hωs)".

    iDestruct (big_sepL2_exists with "Hωs") as "(%Ps & _ & _ & Hωs)".
    iDestruct (big_sepL3_sep with "Hωs") as "(Hωs & HPs)".
    iDestruct (big_sepL3_const_sepL2_1 with "Hωs") as "(_ & _ & Hωs)".
    iDestruct (big_sepL3_const_sepL2_2 with "HPs") as "(_ & _ & HPs)".
    iSteps.
  Qed.

  Lemma ivar_4_notify𑁒spec {t Ψ Ξ Γ ctx} 𝑐𝑡𝑥 v :
    {{{
      ivar_4_inv t Ψ Ξ Γ ∗
      ivar_4_producer t ∗
      Γ ctx 𝑐𝑡𝑥 ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_4_notify t ctx v
    {{{
      waiters Ps
    , RET ();
      ivar_4_result t v ∗
      ivar_4_waiters t waiters Ps ∗
      Γ ctx 𝑐𝑡𝑥 ∗
      [∗ list] P ∈ Ps, □ P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hproducer & HΓ & HΨ & HΞ) HΦ".

    wp_rec.
    wp_apply+ (ivar_4_set𑁒spec with "[$Hinv $Hproducer $HΨ $HΞ]") as (waiters Ps) "(#Hresult & #Hwaiters & HPs)".

    iDestruct (big_sepL2_length with "HPs") as %Hlength.

    wp_apply+ (lst_iter𑁒spec (λ i _,
      Γ ctx 𝑐𝑡𝑥 ∗
      ([∗ list] P ∈ take i Ps, □ P) ∗
      ( [∗ list] waiter; P ∈ drop i waiters; drop i Ps,
        waiter_model_1 Γ t waiter P
      )
    )%I with "[$HΓ HPs]") as "(HΓ & HPs & _)". 1: done.
    { iStep.
      iIntros "!> %i %waiter %Hwaiters_lookup (HΓ & HPs_1 & HPs_2)".

      iEval (rewrite (drop_S waiters waiter) //) in "HPs_2".
      iDestruct (big_sepL2_cons_inv_l with "HPs_2") as "(%P & %Ps' & %Heq & HP & HPs_2)".
      apply drop_cons_inv in Heq as (HPs_lookup & ->).

      wp_apply+ (wp_wand with "(HP HΓ Hresult)") as (res) "(-> & HΓ & HP)".

      iFrameStep.
      iEval (rewrite (take_S_r _ _ P) //).
      iApply big_sepL_snoc.
      iFrame.
    }
    iEval (rewrite Hlength firstn_all) in "HPs".

    iApply "HΦ".
    iFrame "#∗".
  Qed.
End ivar_4_G.

From zoo_std Require
  ivar_4__opaque.

#[global] Opaque ivar_4_inv.
#[global] Opaque ivar_4_producer.
#[global] Opaque ivar_4_consumer.
#[global] Opaque ivar_4_result.
#[global] Opaque ivar_4_waiter.
#[global] Opaque ivar_4_waiters.
