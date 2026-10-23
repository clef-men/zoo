Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Export zoo.program_logic.biglater.
Require Export zoo_parabs.base.
Require Export zoo_parabs.future__code.
Require Import zoo_parabs.future__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type depth : nat.
Implicit Type v pool ctx task waiter : val.
Implicit Type scope : pool۰scope.
Implicit Type ω : gname.
Implicit Type ωs : list gname.

Zoo name :=
  { ivar : ivar_4۰name
  }.

Zoo global ⟨pool⟩ :=
  { ivar : ivar_4
  }.

Section future۰G.
  Context `{future۰G : FutureG Σ}.

  Implicit Type P : iProp Σ.
  Implicit Type Ψ Χ Ξ : val → iProp Σ.

  #[local] Definition finished γ : iProp Σ :=
    ∃ waiters Ps,
    ivar_4۰resolved γ.(future۰name۰ivar) ∗
    ivar_4۰waiters γ.(future۰name۰ivar) waiters Ps ∗
    [∗ list] P ∈ Ps, □ P.
  #[local] Instance : CustomIpat "finished" :=
    " ( %waiters
      & %Ps
      & #Hresolved
      & #Hwaiters
      & #HPs
      )
    ".

  Please Definition future۰inv pool γ Ψ Ξ : iProp Σ :=
    ∃ depth,
    ivar_4۰inv γ.(future۰name۰ivar) Ψ Ξ (pool۰context pool) ∗
    ⧖ depth ∗
    □ (
      pool۰finished pool -∗
      ▷^(2 * depth + 1) finished γ
    ).
  #[local] Instance : CustomIpat "inv" :=
    " ( %depth{}
      & #Hinv{_{}}
      & #H⧖{_{}}
      & #Htermination{_{}}
      )
    ".

  Please Definition future۰obligation pool P : iProp Σ :=
    ∃ depth,
    ⧖ depth ∗
    □ (
      pool۰finished pool -∗
      ▷^(2 * depth + 2) □ P
    ).
  #[local] Instance : CustomIpat "obligation" :=
    " ( %depth
      & #H⧖
      & #Htermination
      )
    ".

  Please Definition future۰consumer γ :=
    ivar_4۰consumer γ.(future۰name۰ivar).

  Please Definition future۰result γ :=
    ivar_4۰result γ.(future۰name۰ivar).
  Definition future۰resolved γ : iProp Σ :=
    ∃ v,
    future۰result γ v.

  #[global] Instance future۰invｰproper pool γ :
    Proper (
      pointwise_relation _ (≡) ==>
      pointwise_relation _ (≡) ==>
      (≡)
    ) (future۰inv pool γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance future۰obligationｰproper pool :
    Proper (
      (≡) ==>
      (≡)
    ) (future۰obligation pool).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance future۰consumerｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      (≡)
    ) (future۰consumer γ).
  Proof.
    apply _.
  Qed.

  Zoo derive Timeless for future۰result.

  Zoo derive Persistent for future۰inv.
  Zoo derive Persistent for future۰obligation.
  Zoo derive Persistent for future۰result.

  #[local] Ltac solve_biglater :=
    iFrame "#";
    iApply bi.laterN_le;
    last iFrame "#∗";
    apply Nat.add_le_mono;
    [ auto using Nat.mul_le_mono_r
    | etrans;
      last apply later۰constant_lb;
      lia
    ].

  Lemma future۰invｰfinished pool γ Ψ Ξ :
    future۰inv pool γ Ψ Ξ -∗
    pool۰finished pool -∗
    ▶ future۰resolved γ.
  Proof.
    iIntros "(:inv) #Hpool_finished".
    iDestruct ("Htermination" with "Hpool_finished") as "(:finished)".
    solve_biglater.
  Qed.

  Lemma future۰obligationｰfinished pool P :
    future۰obligation pool P -∗
    pool۰finished pool -∗
    ▶ □ P.
  Proof.
    iIntros "(:obligation) Hpool_finished".
    iDestruct ("Htermination" with "Hpool_finished") as "HP".
    solve_biglater.
  Qed.

  Lemma future۰consumerｰwand {pool γ Ψ Ξ Χ1} Χ2 :
    future۰inv pool γ Ψ Ξ -∗
    future۰consumer γ Χ1 -∗
    (∀ x, Χ1 x -∗ Χ2 x) ={⊤}=∗
    future۰consumer γ Χ2.
  Proof.
    iIntros "(:inv)".
    iApply (ivar_4۰consumerｰwand with "Hinv").
  Qed.
  Lemma future۰consumerｰdivide {pool γ Ψ Ξ} Χs :
    future۰inv pool γ Ψ Ξ -∗
    future۰consumer γ (λ x, [∗ list] Χ ∈ Χs, Χ x) ={⊤}=∗
    [∗ list] Χ ∈ Χs, future۰consumer γ Χ.
  Proof.
    iIntros "(:inv)".
    iApply (ivar_4۰consumerｰdivide with "Hinv").
  Qed.
  Lemma future۰consumerｰsplit {pool γ Ψ Ξ} Χ1 Χ2 :
    future۰inv pool γ Ψ Ξ -∗
    future۰consumer γ (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      future۰consumer γ Χ1 ∗
      future۰consumer γ Χ2.
  Proof.
    iIntros "(:inv)".
    iApply (ivar_4۰consumerｰsplit with "Hinv").
  Qed.

  Lemma future۰resultｰagree γ v1 v2 :
    future۰result γ v1 -∗
    future۰result γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_4۰resultｰagree.
  Qed.

  Lemma futureｰinvｰresult pool γ Ψ Ξ v :
    future۰inv pool γ Ψ Ξ -∗
    future۰result γ v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) Hresult".
    iApply (ivar_4ｰinvｰresult with "Hinv Hresult").
  Qed.
  Lemma futureｰinvｰresult' pool γ Ψ Ξ v :
    £ 1 -∗
    future۰inv pool γ Ψ Ξ -∗
    future۰result γ v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hfut_inv Hfut_result".
    iMod (futureｰinvｰresult with "Hfut_inv Hfut_result") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma futureｰinvｰresultｰconsumer pool γ Ψ Ξ v Χ :
    future۰inv pool γ Ψ Ξ -∗
    future۰result γ v -∗
    future۰consumer γ Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) Hresult Hconsumer".
    iApply (ivar_4ｰinvｰresultｰconsumer with "Hinv Hresult Hconsumer").
  Qed.
  Lemma futureｰinvｰresultｰconsumer' pool γ Ψ Ξ v Χ :
    £ 2 -∗
    future۰inv pool γ Ψ Ξ -∗
    future۰result γ v -∗
    future۰consumer γ Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hfut_inv Hfut_result Hfut_consumer".
    iMod (futureｰinvｰresultｰconsumer with "Hfut_inv Hfut_result Hfut_consumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma future٠returnｰspec pool Ψ Ξ v :
    {{{
      Ψ v ∗
      □ Ξ v
    }}}
      future٠return v
    {{{
      γ
    , RET γ;
      future۰inv pool γ Ψ Ξ ∗
      future۰consumer γ Ψ ∗
      future۰result γ v
    }}}.
  Proof.
    iIntros "%Φ (HΨ & HΞ) HΦ".

    iMod steps۰lbｰ0 as "#H⧖".

    wp۰apply (ivar_4٠makeｰspec Ψ Ξ with "[$]") as (γ۰ivar) "(#Hinv & Hconsumer & #Hresult & #Hwaiters)".

    pose γ :=
      {|future۰name۰ivar := γ۰ivar
      |}.

    iApply ("HΦ" $! γ).
    iFrame "#∗". iSteps.
  Qed.

  #[local] Lemma future٠setｰspec pool ctx scope γ Ψ Ξ v :
    {{{
      pool۰context pool ctx scope ∗
      ivar_4۰inv γ.(future۰name۰ivar) Ψ Ξ (pool۰context pool) ∗
      ivar_4۰producer γ.(future۰name۰ivar) ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      future٠set ctx γ v
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      finished γ
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hinv & Hproducer & HΨ & HΞ) HΦ".

    wp۰rec.
    wp۰apply+ (ivar_4٠notifyｰspec with "[$Hinv $Hproducer $Hctx $HΨ $HΞ]").
    iSteps.
  Qed.

  Lemma future٠asyncｰspec Ψ Ξ pool ctx scope task :
    {{{
      pool۰context pool ctx scope ∗
      ( ∀ ctx scope,
        pool۰context pool ctx scope -∗
        WP task ctx {{ v,
          pool۰context pool ctx scope ∗
          ▷ Ψ v ∗
          ▷ □ Ξ v
        }}
      )
    }}}
      future٠async ctx task
    {{{
      γ
    , RET γ;
      pool۰context pool ctx scope ∗
      future۰inv pool γ Ψ Ξ ∗
      future۰consumer γ Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Htask) HΦ".

    iMod steps۰lbｰ0 as "#H⧖".

    wp۰rec.
    wp۰apply+ (ivar_4٠createｰspec Ψ Ξ (pool۰context pool) with "[//]") as (ivar) "(#Hinv & Hproducer & Hconsumer)".

    pose γ :=
      {|future۰name۰ivar := ivar
      |}.

    wp۰apply+ (pool٠asyncｰspec
      True
      (finished γ)
    with "[$Hctx Htask Hproducer]") as "(Hctx & _ & #Hpool_obligation)".
    { iIntros "{%} %ctx %scope Hctx".
      wp۰apply+ (wpｰwand with "(Htask Hctx)") as (v) "(Hctx & HΨ & HΞ)".
      wp۰apply (future٠setｰspec _ _ _ γ Ψ with "[$]") as "($ & #$) //".
    }

    wp۰pures.

    iApply ("HΦ" $! γ).
    iFrame "#∗". iIntros "!> !> Hpool_finished".
    iDestruct (pool۰obligationｰfinished with "Hpool_obligation Hpool_finished") as "#Hfinished".
    iNext => //.
  Qed.

  Lemma future٠waitｰspec pool ctx scope γ Ψ Ξ :
    {{{
      pool۰context pool ctx scope ∗
      future۰inv pool γ Ψ Ξ
    }}}
      future٠wait ctx γ
    {{{
      v
    , RET v;
      £ 2 ∗
      pool۰context pool ctx scope ∗
      future۰result γ v
    }}}.
  Proof.
    iIntros "%Φ (Hctx & (:inv)) HΦ".

    wp۰rec.

    wp۰apply+ (pool٠wait_ivarｰspec with "[$Hctx $Hinv]") as "(_ & Hctx & %v & #Hresult)". 1: iSteps.
    wp۰apply+ (ivar_4٠getｰspec with "[$Hinv $Hresult]") as "H£".
    iSteps.
  Qed.

  Lemma future٠iterｰspec P pool ctx scope γ Ψ Ξ task :
    {{{
      pool۰context pool ctx scope ∗
      future۰inv pool γ Ψ Ξ ∗
      ( ∀ ctx scope v,
        pool۰context pool ctx scope -∗
        future۰result γ v -∗
        WP task ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          ▷ □ P
        }}
      )
    }}}
      future٠iter ctx γ task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      future۰obligation pool P
    }}}.
  Proof.
    iIntros "%Φ (Hctx & (:inv) & Htask) HΦ".

    wp۰rec steps:"H⧖" credit:"H£".

    lazymatch iTypeOf "Htask" with
    | Some (_, ?P) =>
        pose P_task := P
    end.
    wp۰apply+ (ivar_4٠waitｰspec P P_task with "[$Hinv $Htask]") as ([v |]) "H".
    { iIntros "{%} %ctx %scope %v Htask Hctx #Hresult".
      wp۰apply (wpｰwand with "(Htask Hctx Hresult)").
      iSteps.
    }

    - iDestruct "H" as "(_ & #Hresult & Htask)".

      iApply wpｰfupd.
      wp۰apply+ (wpｰwand with "(Htask Hctx Hresult)") as (res) "(-> & Hctx & HP)".

      iApply "HΦ".
      iMod (lc_fupd_elim_later with "H£ HP") as "#HP".
      iFrameSteps.

    - iDestruct "H" as "#Hwaiter".

      wp۰pures.

      iApply "HΦ".
      iFrame "#∗". iIntros "!> !> #Hpool_finished".
      iDestruct ("Htermination" with "Hpool_finished") as "Hfinished".
      iEval (replace (2 * depth + 2) with ((2 * depth + 1) + 1) by lia).
      iEval (rewrite bi.laterN_add).
      iNext.
      iDestruct "Hfinished" as "(:finished)".
      iDestruct (ivar_4۰waiterｰvalid with "Hwaiters Hwaiter") as "(%i & %P_ & _ & %HPs_lookup & Heq)".
      iDestruct (big_sepL_lookup with "HPs") as "HP". 1: done.
      iNext.
      iRewrite -"Heq" in "HP" => //.
  Qed.

  Lemma future٠mapｰspec {pool ctx scope γ1 Ψ1 Ξ1} Ψ2 Ξ2 task :
    {{{
      pool۰context pool ctx scope ∗
      future۰inv pool γ1 Ψ1 Ξ1 ∗
      ( ∀ ctx scope v1,
        pool۰context pool ctx scope -∗
        future۰result γ1 v1 -∗
        WP task ctx v1 {{ v2,
          pool۰context pool ctx scope ∗
          ▷ Ψ2 v2 ∗
          ▷ □ Ξ2 v2
        }}
      )
    }}}
      future٠map ctx γ1 task
    {{{
      γ2
    , RET γ2;
      pool۰context pool ctx scope ∗
      future۰inv pool γ2 Ψ2 Ξ2 ∗
      future۰consumer γ2 Ψ2
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hinv_1 & Htask) HΦ".

    wp۰rec.
    wp۰apply+ (ivar_4٠createｰspec Ψ2 Ξ2 (pool۰context pool) with "[//]") as (ivar2) "(#Hinv_2 & Hproducer_2 & Hconsumer_2)".

    pose γ2 :=
      {|future۰name۰ivar := ivar2
      |}.

    wp۰apply+ (future٠iterｰspec (
      pool۰obligation pool (finished γ2)
    ) with "[$Hctx $Hinv_1 Htask Hproducer_2]") as "(Hctx & (:obligation))".
    { iIntros "{%} %ctx %scope %v1 Hctx #Hresult_1".
      wp۰apply+ (pool٠asyncｰspec
        True
        (finished γ2)
      with "[$Hctx Htask Hproducer_2]") as "($ & _ & #$) //".
      { iIntros "{%} %ctx %scope Hctx".
        wp۰apply+ (wpｰwand with "(Htask Hctx Hresult_1)") as (v2) "(Hctx & HΨ2 & HΞ2)".
        wp۰apply (future٠setｰspec _ _ _ γ2 Ψ2 with "[$]") as "($ & #$) //".
      }
    }

    wp۰pures steps:"H⧖".

    iApply ("HΦ" $! γ2).
    iFrame "#∗". iIntros "!> !> #Hpool_finished".
    iDestruct ("Htermination" with "Hpool_finished") as "Hpool_obligation".
    iEval (replace (2 * ˖depth + 1) with ((2 * depth + 2) + 1) by lia).
    iEval (rewrite bi.laterN_add).
    iNext.
    iDestruct (pool۰obligationｰfinished with "Hpool_obligation Hpool_finished") as "Hfinished".
    iNext => //.
  Qed.
End future۰G.

Require zoo_parabs.future__opaque.

Please opacify.
