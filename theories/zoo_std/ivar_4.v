Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.saved_prop.
Require Import zoo.base.
Require Export zoo_std.ivar_4__code.
Require Import zoo_std.ivar_3.
Require Import zoo_std.ivar_4__types.
Require Import zoo_std.list.
Require Import zoo_std.option.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v t ctx waiter : val.
Implicit Type waiters : list val.
Implicit Type ω : gname.
Implicit Type ωs : list gname.

Class Ivar4G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] ivar_4۰G۰ivar_3۰G :: Ivar3G Σ gname
  ; #[local] ivar_4۰G۰saved_prop۰G :: SavedPropG Σ
  }.

Definition ivar_4۰Σ :=
  #[ivar_3۰Σ gname
  ; saved_prop۰Σ
  ].
#[global] Instance subG𑁒ivar_4۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG ivar_4۰Σ Σ →
  Ivar4G Σ.
Proof.
  solve_inG.
Qed.

Section ivar_4۰G.
  Context `{ivar_4۰G : Ivar4G Σ}.
  Context `{context_name : Type}.

  Implicit Type 𝑐𝑡𝑥 : context_name.
  Implicit Type P : iProp Σ.
  Implicit Type Ps : list $ iProp Σ.
  Implicit Type Ψ Χ Ξ : val → iProp Σ.
  Implicit Type Γ : val → context_name → iProp Σ.

  #[local] Definition waiter۰model₁ Γ t waiter P : iProp Σ :=
    ∀ ctx 𝑐𝑡𝑥 v,
    Γ ctx 𝑐𝑡𝑥 -∗
    ivar_3۰result t v -∗
    WP waiter ctx v {{ res,
      ⌜res = ()%V⌝ ∗
      Γ ctx 𝑐𝑡𝑥 ∗
      ▷ □ P
    }}.
  #[local] Definition waiter۰model₂ Γ t waiter ω : iProp Σ :=
    ∃ P,
    saved_prop ω P ∗
    waiter۰model₁ Γ t waiter P.

  Definition ivar_4۰inv t Ψ Ξ Γ :=
    ivar_3۰inv t Ψ Ξ (waiter۰model₂ Γ).

  Definition ivar_4۰producer :=
    ivar_3۰producer.

  Definition ivar_4۰consumer :=
    ivar_3۰consumer.

  Definition ivar_4۰result :=
    ivar_3۰result.
  Definition ivar_4۰resolved t : iProp Σ :=
    ∃ v,
    ivar_4۰result t v.

  Definition ivar_4۰waiters t waiters Ps : iProp Σ :=
    ∃ ωs,
    ivar_3۰waiters t waiters ωs ∗
    [∗ list] ω; P ∈ ωs; Ps, saved_prop ω P.
  #[local] Instance : CustomIpat "waiters" :=
    " ( %ωs
      & #Hwaiters
      & #Hωs
      )
    ".

  Definition ivar_4۰waiter t waiter P : iProp Σ :=
    ∃ ω,
    ivar_3۰waiter t waiter ω ∗
    saved_prop ω P.
  #[local] Instance : CustomIpat "waiter" :=
    " ( %ω
      & #Hwaiter
      & #Hω
      )
    ".

  #[global] Instance ivar_4۰inv𑁒contractive t n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ (≡{n}≡)) ==>
      (≡{n}≡)
    ) (ivar_4۰inv t).
  Proof.
    rewrite /ivar_4۰inv /waiter۰model₂ /waiter۰model₁.
    intros Ψ1 Ψ2 HΨ Ξ1 Ξ2 HΞ Γ1 Γ2 HΓ.
    f_equiv. 1,2: solve_proper.
    do 3 f_equiv.
    apply dist_dist_later.
    solve_proper.
  Qed.
  #[global] Instance ivar_4۰inv𑁒proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_4۰inv t).
  Proof.
    rewrite /ivar_4۰inv /waiter۰model₂ /waiter۰model₁.
    solve_proper.
  Qed.
  #[global] Instance ivar_4۰consumer𑁒contractive t n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_4۰consumer t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_4۰consumer𑁒proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_4۰consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ivar_4۰producer𑁒timeless t :
    Timeless (ivar_4۰producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_4۰result𑁒timeless t v :
    Timeless (ivar_4۰result t v).
  Proof.
    apply _.
  Qed.

  #[global] Instance ivar_4۰inv𑁒persistent t Ψ Ξ Γ :
    Persistent (ivar_4۰inv t Ψ Ξ Γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_4۰result𑁒persistent t v :
    Persistent (ivar_4۰result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_4۰waiters𑁒persistent t waiters Ps :
    Persistent (ivar_4۰waiters t waiters Ps).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_4۰waiter𑁒persistent t waiter P :
    Persistent (ivar_4۰waiter t waiter P).
  Proof.
    apply _.
  Qed.

  Lemma ivar_4۰producer𑁒exclusive t :
    ivar_4۰producer t -∗
    ivar_4۰producer t -∗
    False.
  Proof.
    apply ivar_3۰producer𑁒exclusive.
  Qed.

  Lemma ivar_4۰consumer𑁒wand {t Ψ Ξ Γ Χ1} Χ2 :
    ivar_4۰inv t Ψ Ξ Γ -∗
    ivar_4۰consumer t Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    ivar_4۰consumer t Χ2.
  Proof.
    apply ivar_3۰consumer𑁒wand.
  Qed.
  Lemma ivar_4۰consumer𑁒divide {t Ψ Ξ Γ} Χs :
    ivar_4۰inv t Ψ Ξ Γ -∗
    ivar_4۰consumer t (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_4۰consumer t Χ.
  Proof.
    apply ivar_3۰consumer𑁒divide.
  Qed.
  Lemma ivar_4۰consumer𑁒split {t Ψ Ξ Γ} Χ1 Χ2 :
    ivar_4۰inv t Ψ Ξ Γ -∗
    ivar_4۰consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_4۰consumer t Χ1 ∗
      ivar_4۰consumer t Χ2.
  Proof.
    apply ivar_3۰consumer𑁒split.
  Qed.

  Lemma ivar_4۰result𑁒agree t v1 v2 :
    ivar_4۰result t v1 -∗
    ivar_4۰result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_3۰result𑁒agree.
  Qed.

  Lemma ivar_4𑁒producer𑁒result t v :
    ivar_4۰producer t -∗
    ivar_4۰result t v -∗
    False.
  Proof.
    apply ivar_3𑁒producer𑁒result.
  Qed.

  Lemma ivar_4𑁒inv𑁒result t Ψ Ξ Γ v :
    ivar_4۰inv t Ψ Ξ Γ -∗
    ivar_4۰result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    apply ivar_3𑁒inv𑁒result.
  Qed.
  Lemma ivar_4𑁒inv𑁒result' t Ψ Ξ Γ v :
    £ 1 -∗
    ivar_4۰inv t Ψ Ξ Γ -∗
    ivar_4۰result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    apply ivar_3𑁒inv𑁒result'.
  Qed.
  Lemma ivar_4𑁒inv𑁒result𑁒consumer t Ψ Ξ Γ v Χ :
    ivar_4۰inv t Ψ Ξ Γ -∗
    ivar_4۰result t v -∗
    ivar_4۰consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    apply ivar_3𑁒inv𑁒result𑁒consumer.
  Qed.
  Lemma ivar_4𑁒inv𑁒result𑁒consumer' t Ψ Ξ Γ v Χ :
    £ 2 -∗
    ivar_4۰inv t Ψ Ξ Γ -∗
    ivar_4۰result t v -∗
    ivar_4۰consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    apply ivar_3𑁒inv𑁒result𑁒consumer'.
  Qed.

  Lemma ivar_4۰waiter𑁒valid t waiters Ps waiter P :
    ivar_4۰waiters t waiters Ps -∗
    ivar_4۰waiter t waiter P -∗
      ∃ i P_,
      ⌜waiters !! i = Some waiter⌝ ∗
      ⌜Ps !! i = Some P_⌝ ∗
      ▷ (P ≡ P_).
  Proof.
    iIntros "(:waiters) (:waiter)".
    iDestruct (ivar_3۰waiter𑁒valid with "Hwaiters Hwaiter") as "(%i & %Hwaiters_lookup & %Hωs_lookup)".
    iDestruct (big_sepL2_lookup_l with "Hωs") as "(%P_ & %HPs_lookup & Hω_)". 1: done.
    iDestruct (saved_prop𑁒agree with "Hω Hω_") as "Heq".
    iFrame "%#".
  Qed.

  Lemma ivar_4٠create𑁒spec Ψ Ξ Γ :
    {{{
      True
    }}}
      ivar_4٠create ()
    {{{
      t
    , RET t;
      ivar_4۰inv t Ψ Ξ Γ ∗
      ivar_4۰producer t ∗
      ivar_4۰consumer t Ψ
    }}}.
  Proof.
    apply ivar_3٠create𑁒spec.
  Qed.

  Lemma ivar_4٠make𑁒spec Ψ Ξ Γ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_4٠make v
    {{{
      t
    , RET t;
      ivar_4۰inv t Ψ Ξ Γ ∗
      ivar_4۰consumer t Ψ ∗
      ivar_4۰result t v ∗
      ivar_4۰waiters t [] []
    }}}.
  Proof.
    iIntros "%Φ (HΨ & HΞ) HΦ".

    wp۰apply (ivar_3٠make𑁒spec with "[$HΨ $HΞ]").
    iSteps.
  Qed.

  Lemma ivar_4٠is_unset𑁒spec t Ψ Ξ Γ :
    {{{
      ivar_4۰inv t Ψ Ξ Γ
    }}}
      ivar_4٠is_unset t
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        ivar_4۰resolved t
    }}}.
  Proof.
    apply ivar_3٠is_unset𑁒spec.
  Qed.
  Lemma ivar_4٠is_unset𑁒spec𑁒result t Ψ Ξ Γ v :
    {{{
      ivar_4۰inv t Ψ Ξ Γ ∗
      ivar_4۰result t v
    }}}
      ivar_4٠is_unset t
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    apply ivar_3٠is_unset𑁒spec𑁒result.
  Qed.

  Lemma ivar_4٠is_set𑁒spec t Ψ Ξ Γ :
    {{{
      ivar_4۰inv t Ψ Ξ Γ
    }}}
      ivar_4٠is_set t
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        ivar_4۰resolved t
      else
        True
    }}}.
  Proof.
    apply ivar_3٠is_set𑁒spec.
  Qed.
  Lemma ivar_4٠is_set𑁒spec𑁒result t Ψ Ξ Γ v :
    {{{
      ivar_4۰inv t Ψ Ξ Γ ∗
      ivar_4۰result t v
    }}}
      ivar_4٠is_set t
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    apply ivar_3٠is_set𑁒spec𑁒result.
  Qed.

  Lemma ivar_4٠try_get𑁒spec t Ψ Ξ Γ :
    {{{
      ivar_4۰inv t Ψ Ξ Γ
    }}}
      ivar_4٠try_get t
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_4۰result t v
      else
        True
    }}}.
  Proof.
    apply ivar_3٠try_get𑁒spec.
  Qed.
  Lemma ivar_4٠try_get𑁒spec𑁒result t Ψ Ξ Γ v :
    {{{
      ivar_4۰inv t Ψ Ξ Γ ∗
      ivar_4۰result t v
    }}}
      ivar_4٠try_get t
    {{{
      RET Some v;
      £ 2
    }}}.
  Proof.
    apply ivar_3٠try_get𑁒spec𑁒result.
  Qed.

  Lemma ivar_4٠get𑁒spec t Ψ Ξ Γ v :
    {{{
      ivar_4۰inv t Ψ Ξ Γ ∗
      ivar_4۰result t v
    }}}
      ivar_4٠get t
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    apply ivar_3٠get𑁒spec.
  Qed.

  Lemma ivar_4٠wait𑁒spec P Q t Ψ Ξ Γ waiter :
    {{{
      ivar_4۰inv t Ψ Ξ Γ ∗
      Q ∗
      ( ∀ ctx 𝑐𝑡𝑥 v,
        Q -∗
        Γ ctx 𝑐𝑡𝑥 -∗
        ivar_3۰result t v -∗
        WP waiter ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          Γ ctx 𝑐𝑡𝑥 ∗
          ▷ □ P
        }}
      )
    }}}
      ivar_4٠wait t waiter
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_4۰result t v ∗
        Q
      else
        ivar_4۰waiter t waiter P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HQ & Hwaiter) HΦ".

    iMod (saved_prop𑁒alloc P) as "(%ω & #Hω)".
    wp۰apply (ivar_3٠wait𑁒spec ω Q with "[$Hinv $HQ Hwaiter]") as (o) "Ho". 1: iSteps.

    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.

  Lemma ivar_4٠set𑁒spec t Ψ Ξ Γ v :
    {{{
      ivar_4۰inv t Ψ Ξ Γ ∗
      ivar_4۰producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_4٠set t v
    {{{
      waiters Ps
    , RET list۰to_val waiters;
      ivar_4۰result t v ∗
      ivar_4۰waiters t waiters Ps ∗
      [∗ list] waiter; P ∈ waiters; Ps,
        ∀ ctx 𝑐𝑡𝑥 v,
        Γ ctx 𝑐𝑡𝑥 -∗
        ivar_3۰result t v -∗
        WP waiter ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          Γ ctx 𝑐𝑡𝑥 ∗
          ▷ □ P
        }}
    }}}.
  Proof.
    iIntros "%Φ (Hinv & Hproducer & HΨ & HΞ) HΦ".

    wp۰apply (ivar_3٠set𑁒spec _ Ψ Ξ with "[$]") as (waiters ωs) "(Hresult & Hwaiters & Hωs)".

    iDestruct (big_sepL2𑁒exists with "Hωs") as "(%Ps & _ & _ & Hωs)".
    iDestruct (big_sepL3𑁒sep with "Hωs") as "(Hωs & HPs)".
    iDestruct (big_sepL3𑁒const𑁒sepL2₁ with "Hωs") as "(_ & _ & Hωs)".
    iDestruct (big_sepL3𑁒const𑁒sepL2₂ with "HPs") as "(_ & _ & HPs)".
    iSteps.
  Qed.

  Lemma ivar_4٠notify𑁒spec {t Ψ Ξ Γ ctx} 𝑐𝑡𝑥 v :
    {{{
      ivar_4۰inv t Ψ Ξ Γ ∗
      ivar_4۰producer t ∗
      Γ ctx 𝑐𝑡𝑥 ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_4٠notify t ctx v
    {{{
      waiters Ps
    , RET ();
      ivar_4۰result t v ∗
      ivar_4۰waiters t waiters Ps ∗
      Γ ctx 𝑐𝑡𝑥 ∗
      [∗ list] P ∈ Ps, □ P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hproducer & HΓ & HΨ & HΞ) HΦ".

    wp۰rec.
    wp۰apply+ (ivar_4٠set𑁒spec with "[$Hinv $Hproducer $HΨ $HΞ]") as (waiters Ps) "(#Hresult & #Hwaiters & HPs)".

    iDestruct (big_sepL2_length with "HPs") as %Hlength.

    wp۰apply+ (list٠iter𑁒spec (λ i _,
      Γ ctx 𝑐𝑡𝑥 ∗
      ([∗ list] P ∈ take i Ps, □ P) ∗
      ( [∗ list] waiter; P ∈ drop i waiters; drop i Ps,
        waiter۰model₁ Γ t waiter P
      )
    )%I with "[$HΓ HPs]") as "(HΓ & HPs & _)". 1: done.
    { iStep.
      iIntros "!> %i %waiter %Hwaiters_lookup (HΓ & HPs_1 & HPs_2)".

      iEval (rewrite (drop_S waiters waiter) //) in "HPs_2".
      iDestruct (big_sepL2_cons_inv_l with "HPs_2") as "(%P & %Ps' & %Heq & HP & HPs_2)".
      apply drop𑁒cons𑁒inv in Heq as (HPs_lookup & ->).

      wp۰apply+ (wp𑁒wand with "(HP HΓ Hresult)") as (res) "(-> & HΓ & HP)".

      iFrameStep.
      iEval (rewrite (take_S_r _ _ P) //).
      iApply big_sepL_snoc.
      iFrame.
    }
    iEval (rewrite Hlength firstn_all) in "HPs".

    iApply "HΦ".
    iFrame "#∗".
  Qed.
End ivar_4۰G.

Require zoo_std.ivar_4__opaque.

#[global] Opaque ivar_4۰inv.
#[global] Opaque ivar_4۰producer.
#[global] Opaque ivar_4۰consumer.
#[global] Opaque ivar_4۰result.
#[global] Opaque ivar_4۰waiter.
#[global] Opaque ivar_4۰waiters.
