Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.saved_prop.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_std.ivar_4__code.
Require Import zoo_std.ivar_4__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v ctx waiter : val.
Implicit Type waiters : list val.
Implicit Type ω : gname.
Implicit Type ωs : list gname.

Zoo name :=
  { base : ivar_3۰name
  }.

Zoo global :=
  { ivar_3 : ivar_3 gname
  ; saved_prop : saved_prop
  }.

Section ivar_4۰G.
  Context `{ivar_4۰G : Ivar4G Σ}.
  Context `{context_name : Type}.

  Implicit Type 𝑐𝑡𝑥 : context_name.
  Implicit Type P : iProp Σ.
  Implicit Type Ps : list $ iProp Σ.
  Implicit Type Ψ Χ Ξ : val → iProp Σ.
  Implicit Type Γ : val → context_name → iProp Σ.

  #[local] Definition waiter۰model₁ Γ γ۰base waiter P : iProp Σ :=
    ∀ ctx 𝑐𝑡𝑥 v,
    Γ ctx 𝑐𝑡𝑥 -∗
    ivar_3۰result γ۰base v -∗
    WP waiter ctx v {{ res,
      ⌜res = ()%V⌝ ∗
      Γ ctx 𝑐𝑡𝑥 ∗
      ▷ □ P
    }}.
  #[local] Definition waiter۰model₂ Γ γ۰base waiter ω : iProp Σ :=
    ∃ P,
    saved_prop ω P ∗
    waiter۰model₁ Γ γ۰base waiter P.

  Please Definition ivar_4۰inv γ Ψ Ξ Γ :=
    ivar_3۰inv γ.(ivar_4۰name۰base) Ψ Ξ (waiter۰model₂ Γ).

  Please Definition ivar_4۰producer γ :=
    ivar_3۰producer γ.(ivar_4۰name۰base).

  Please Definition ivar_4۰consumer γ :=
    ivar_3۰consumer γ.(ivar_4۰name۰base).

  Please Definition ivar_4۰result γ :=
    ivar_3۰result γ.(ivar_4۰name۰base).
  Definition ivar_4۰resolved γ : iProp Σ :=
    ∃ v,
    ivar_4۰result γ v.

  Please Definition ivar_4۰waiters γ waiters Ps : iProp Σ :=
    ∃ ωs,
    ivar_3۰waiters γ.(ivar_4۰name۰base) waiters ωs ∗
    [∗ list] ω; P ∈ ωs; Ps, saved_prop ω P.
  #[local] Instance : CustomIpat "waiters" :=
    " ( %ωs
      & #Hwaiters
      & #Hωs
      )
    ".

  Please Definition ivar_4۰waiter γ waiter P : iProp Σ :=
    ∃ ω,
    ivar_3۰waiter γ.(ivar_4۰name۰base) waiter ω ∗
    saved_prop ω P.
  #[local] Instance : CustomIpat "waiter" :=
    " ( %ω
      & #Hwaiter
      & #Hω
      )
    ".

  #[global] Instance ivar_4۰invｰcontractive γ n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ (≡{n}≡)) ==>
      (≡{n}≡)
    ) (ivar_4۰inv γ).
  Proof.
    rewrite /ivar_4۰inv /waiter۰model₂ /waiter۰model₁.
    solve_proper.
  Qed.
  #[global] Instance ivar_4۰invｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      pointwise_relation _ (≡) ==>
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_4۰inv γ).
  Proof.
    rewrite /ivar_4۰inv /waiter۰model₂ /waiter۰model₁.
    solve_proper.
  Qed.
  #[global] Instance ivar_4۰consumerｰcontractive γ n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_4۰consumer γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_4۰consumerｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      (≡)
    ) (ivar_4۰consumer γ).
  Proof.
    solve_proper.
  Qed.

  Zoo derive Timeless for ivar_4۰producer.
  Zoo derive Timeless for ivar_4۰result.

  Zoo derive Persistent for ivar_4۰inv.
  Zoo derive Persistent for ivar_4۰result.
  Zoo derive Persistent for ivar_4۰waiters.
  Zoo derive Persistent for ivar_4۰waiter.

  Lemma ivar_4۰producerｰexclusive γ :
    ivar_4۰producer γ -∗
    ivar_4۰producer γ -∗
    False.
  Proof.
    apply ivar_3۰producerｰexclusive.
  Qed.

  Lemma ivar_4۰consumerｰwand {γ Ψ Ξ Γ Χ1} Χ2 :
    ivar_4۰inv γ Ψ Ξ Γ -∗
    ivar_4۰consumer γ Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    ivar_4۰consumer γ Χ2.
  Proof.
    apply ivar_3۰consumerｰwand.
  Qed.
  Lemma ivar_4۰consumerｰdivide {γ Ψ Ξ Γ} Χs :
    ivar_4۰inv γ Ψ Ξ Γ -∗
    ivar_4۰consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_4۰consumer γ Χ.
  Proof.
    apply ivar_3۰consumerｰdivide.
  Qed.
  Lemma ivar_4۰consumerｰsplit {γ Ψ Ξ Γ} Χ1 Χ2 :
    ivar_4۰inv γ Ψ Ξ Γ -∗
    ivar_4۰consumer γ (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_4۰consumer γ Χ1 ∗
      ivar_4۰consumer γ Χ2.
  Proof.
    apply ivar_3۰consumerｰsplit.
  Qed.

  Lemma ivar_4۰resultｰagree γ v1 v2 :
    ivar_4۰result γ v1 -∗
    ivar_4۰result γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_3۰resultｰagree.
  Qed.

  Lemma ivar_4ｰproducerｰresult γ v :
    ivar_4۰producer γ -∗
    ivar_4۰result γ v -∗
    False.
  Proof.
    apply ivar_3ｰproducerｰresult.
  Qed.

  Lemma ivar_4ｰinvｰresult γ Ψ Ξ Γ v :
    ivar_4۰inv γ Ψ Ξ Γ -∗
    ivar_4۰result γ v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    apply ivar_3ｰinvｰresult.
  Qed.
  Lemma ivar_4ｰinvｰresult' γ Ψ Ξ Γ v :
    £ 1 -∗
    ivar_4۰inv γ Ψ Ξ Γ -∗
    ivar_4۰result γ v ={⊤}=∗
    □ Ξ v.
  Proof.
    apply ivar_3ｰinvｰresult'.
  Qed.
  Lemma ivar_4ｰinvｰresultｰconsumer γ Ψ Ξ Γ v Χ :
    ivar_4۰inv γ Ψ Ξ Γ -∗
    ivar_4۰result γ v -∗
    ivar_4۰consumer γ Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    apply ivar_3ｰinvｰresultｰconsumer.
  Qed.
  Lemma ivar_4ｰinvｰresultｰconsumer' γ Ψ Ξ Γ v Χ :
    £ 2 -∗
    ivar_4۰inv γ Ψ Ξ Γ -∗
    ivar_4۰result γ v -∗
    ivar_4۰consumer γ Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    apply ivar_3ｰinvｰresultｰconsumer'.
  Qed.

  Lemma ivar_4۰waiterｰvalid γ waiters Ps waiter P :
    ivar_4۰waiters γ waiters Ps -∗
    ivar_4۰waiter γ waiter P -∗
      ∃ i P_,
      ⌜waiters !! i = Some waiter⌝ ∗
      ⌜Ps !! i = Some P_⌝ ∗
      ▷ (P ≡ P_).
  Proof.
    iIntros "(:waiters) (:waiter)".
    iDestruct (ivar_3۰waiterｰvalid with "Hwaiters Hwaiter") as "(%i & %Hwaiters_lookup & %Hωs_lookup)".
    iDestruct (big_sepL2_lookup_l with "Hωs") as "(%P_ & %HPs_lookup & Hω_)". 1: done.
    iDestruct (saved_propｰagree with "Hω Hω_") as "Heq".
    iFrame "%#".
  Qed.

  Lemma ivar_4٠createｰspec Ψ Ξ Γ :
    {{{
      True
    }}}
      ivar_4٠create ()
    {{{
      γ
    , RET γ;
      ivar_4۰inv γ Ψ Ξ Γ ∗
      ivar_4۰producer γ ∗
      ivar_4۰consumer γ Ψ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰apply (ivar_3٠createｰspec with "[//]") as (γ۰base) "(Hinv & Hproducer & Hconsumer)".

    pose γ :=
      {|ivar_4۰name۰base := γ۰base
      |}.

    iApply ("HΦ" $! γ with "[$]").
  Qed.

  Lemma ivar_4٠makeｰspec Ψ Ξ Γ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_4٠make v
    {{{
      γ
    , RET γ;
      ivar_4۰inv γ Ψ Ξ Γ ∗
      ivar_4۰consumer γ Ψ ∗
      ivar_4۰result γ v ∗
      ivar_4۰waiters γ [] []
    }}}.
  Proof.
    iIntros "%Φ (HΨ & HΞ) HΦ".

    wp۰apply (ivar_3٠makeｰspec with "[$HΨ $HΞ]") as (γ۰base) "(Hinv & Hconsumer & Hresult & Hwaiters)".

    pose γ :=
      {|ivar_4۰name۰base := γ۰base
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.

  Lemma ivar_4٠is_unsetｰspec γ Ψ Ξ Γ :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ
    }}}
      ivar_4٠is_unset γ
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        ivar_4۰resolved γ
    }}}.
  Proof.
    apply ivar_3٠is_unsetｰspec.
  Qed.
  Lemma ivar_4٠is_unsetｰspecｰresult γ Ψ Ξ Γ v :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ ∗
      ivar_4۰result γ v
    }}}
      ivar_4٠is_unset γ
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    apply ivar_3٠is_unsetｰspecｰresult.
  Qed.

  Lemma ivar_4٠is_setｰspec γ Ψ Ξ Γ :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ
    }}}
      ivar_4٠is_set γ
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        ivar_4۰resolved γ
      else
        True
    }}}.
  Proof.
    apply ivar_3٠is_setｰspec.
  Qed.
  Lemma ivar_4٠is_setｰspecｰresult γ Ψ Ξ Γ v :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ ∗
      ivar_4۰result γ v
    }}}
      ivar_4٠is_set γ
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    apply ivar_3٠is_setｰspecｰresult.
  Qed.

  Lemma ivar_4٠try_getｰspec γ Ψ Ξ Γ :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ
    }}}
      ivar_4٠try_get γ
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_4۰result γ v
      else
        True
    }}}.
  Proof.
    apply ivar_3٠try_getｰspec.
  Qed.
  Lemma ivar_4٠try_getｰspecｰresult γ Ψ Ξ Γ v :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ ∗
      ivar_4۰result γ v
    }}}
      ivar_4٠try_get γ
    {{{
      RET Some v;
      £ 2
    }}}.
  Proof.
    apply ivar_3٠try_getｰspecｰresult.
  Qed.

  Lemma ivar_4٠getｰspec γ Ψ Ξ Γ v :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ ∗
      ivar_4۰result γ v
    }}}
      ivar_4٠get γ
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    apply ivar_3٠getｰspec.
  Qed.

  Lemma ivar_4٠waitｰspec P Q γ Ψ Ξ Γ waiter :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ ∗
      Q ∗
      ( ∀ ctx 𝑐𝑡𝑥 v,
        Q -∗
        Γ ctx 𝑐𝑡𝑥 -∗
        ivar_4۰result γ v -∗
        WP waiter ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          Γ ctx 𝑐𝑡𝑥 ∗
          ▷ □ P
        }}
      )
    }}}
      ivar_4٠wait γ waiter
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_4۰result γ v ∗
        Q
      else
        ivar_4۰waiter γ waiter P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HQ & Hwaiter) HΦ".

    iMod (saved_propｰalloc P) as "(%ω & #Hω)".
    wp۰apply (ivar_3٠waitｰspec ω Q with "[$Hinv $HQ Hwaiter]") as (o) "Ho". 1: iSteps.

    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.

  Lemma ivar_4٠setｰspec γ Ψ Ξ Γ v :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ ∗
      ivar_4۰producer γ ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_4٠set γ v
    {{{
      waiters Ps
    , RET list۰to_val waiters;
      ivar_4۰result γ v ∗
      ivar_4۰waiters γ waiters Ps ∗
      [∗ list] waiter; P ∈ waiters; Ps,
        ∀ ctx 𝑐𝑡𝑥 v,
        Γ ctx 𝑐𝑡𝑥 -∗
        ivar_4۰result γ v -∗
        WP waiter ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          Γ ctx 𝑐𝑡𝑥 ∗
          ▷ □ P
        }}
    }}}.
  Proof.
    iIntros "%Φ (Hinv & Hproducer & HΨ & HΞ) HΦ".

    wp۰apply (ivar_3٠setｰspec _ Ψ Ξ with "[$]") as (waiters ωs) "(Hresult & Hwaiters & Hωs)".

    iDestruct (big_sepL2ｰexists with "Hωs") as "(%Ps & _ & _ & Hωs)".
    iDestruct (big_sepL3ｰsep with "Hωs") as "(Hωs & HPs)".
    iDestruct (big_sepL3ｰconstｰsepL2₁ with "Hωs") as "(_ & _ & Hωs)".
    iDestruct (big_sepL3ｰconstｰsepL2₂ with "HPs") as "(_ & _ & HPs)".
    iSteps.
  Qed.

  Lemma ivar_4٠notifyｰspec {γ Ψ Ξ Γ ctx} 𝑐𝑡𝑥 v :
    {{{
      ivar_4۰inv γ Ψ Ξ Γ ∗
      ivar_4۰producer γ ∗
      Γ ctx 𝑐𝑡𝑥 ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_4٠notify γ ctx v
    {{{
      waiters Ps
    , RET ();
      ivar_4۰result γ v ∗
      ivar_4۰waiters γ waiters Ps ∗
      Γ ctx 𝑐𝑡𝑥 ∗
      [∗ list] P ∈ Ps, □ P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hproducer & HΓ & HΨ & HΞ) HΦ".

    wp۰rec.
    wp۰apply+ (ivar_4٠setｰspec with "[$Hinv $Hproducer $HΨ $HΞ]") as (waiters Ps) "(#Hresult & #Hwaiters & HPs)".

    iDestruct (big_sepL2_length with "HPs") as %Hlength.

    wp۰apply+ (list٠iterｰspec (λ i _,
      Γ ctx 𝑐𝑡𝑥 ∗
      ([∗ list] P ∈ take i Ps, □ P) ∗
      ( [∗ list] waiter; P ∈ drop i waiters; drop i Ps,
        waiter۰model₁ Γ γ.(ivar_4۰name۰base) waiter P
      )
    )%I with "[$HΓ HPs]") as "(HΓ & HPs & _)". 1: done.
    { iStep.
      iIntros "!> %i %waiter %Hwaiters_lookup (HΓ & HPs_1 & HPs_2)".

      iEval (rewrite (drop_S waiters waiter) //) in "HPs_2".
      iDestruct (big_sepL2_cons_inv_l with "HPs_2") as "(%P & %Ps' & %Heq & HP & HPs_2)".
      apply dropｰconsｰinv in Heq as (HPs_lookup & ->).

      wp۰apply+ (wpｰwand with "(HP HΓ Hresult)") as (res) "(-> & HΓ & HP)".

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

Please opacify.
