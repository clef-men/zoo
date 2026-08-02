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
Implicit Type v t pool ctx task waiter : val.
Implicit Type scope : pool۰scope.
Implicit Type ω : gname.
Implicit Type ωs : list gname.

Class FutureG Σ `{pool۰G : PoolG Σ} :=
  { #[local] future۰G۰ivar۰G :: Ivar4G Σ
  }.

Definition future۰Σ :=
  #[ivar_4۰Σ
  ].
#[global] Instance subGｰfuture۰Σ Σ `{pool۰G : PoolG Σ} :
  subG future۰Σ Σ →
  FutureG Σ.
Proof.
  solve_inG.
Qed.

Section future۰G.
  Context `{future۰G : FutureG Σ}.

  Implicit Type P : iProp Σ.
  Implicit Type Ψ Χ Ξ : val → iProp Σ.

  #[local] Definition finished t : iProp Σ :=
    ∃ waiters Ps,
    ivar_4۰resolved t ∗
    ivar_4۰waiters t waiters Ps ∗
    [∗ list] P ∈ Ps, □ P.
  #[local] Instance : CustomIpat "finished" :=
    " ( %waiters
      & %Ps
      & #Hresolved
      & #Hwaiters
      & #HPs
      )
    ".

  Definition future۰inv pool t Ψ Ξ : iProp Σ :=
    ∃ depth,
    ivar_4۰inv t Ψ Ξ (pool۰context pool) ∗
    ⧖ depth ∗
    □ (
      pool۰finished pool -∗
      ▷^(2 * depth + 1) finished t
    ).
  #[local] Instance : CustomIpat "inv" :=
    " ( %depth{}
      & #Hinv{_{}}
      & #H⧖{_{}}
      & #Htermination{_{}}
      )
    ".

  Definition future۰obligation pool P : iProp Σ :=
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

  Definition future۰consumer :=
    ivar_4۰consumer.

  Definition future۰result :=
    ivar_4۰result.
  Definition future۰resolved t : iProp Σ :=
    ∃ v,
    future۰result t v.

  #[global] Instance future۰invｰproper pool t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (future۰inv pool t).
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
  #[global] Instance future۰consumerｰproper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (future۰consumer t).
  Proof.
    apply _.
  Qed.

  #[global] Instance future۰resultｰtimeless t v :
    Timeless (future۰result t v).
  Proof.
    apply _.
  Qed.

  #[global] Instance future۰invｰpersistent pool t Ψ Ξ :
    Persistent (future۰inv pool t Ψ Ξ).
  Proof.
    apply _.
  Qed.
  #[global] Instance future۰obligationｰpersistent pool P :
    Persistent (future۰obligation pool P).
  Proof.
    apply _.
  Qed.
  #[global] Instance future۰resultｰpersistent t v :
    Persistent (future۰result t v).
  Proof.
    apply _.
  Qed.

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

  Lemma future۰invｰfinished pool t Ψ Ξ :
    future۰inv pool t Ψ Ξ -∗
    pool۰finished pool -∗
    ▶ future۰resolved t.
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

  Lemma future۰consumerｰwand {pool t Ψ Ξ Χ1} Χ2 :
    future۰inv pool t Ψ Ξ -∗
    future۰consumer t Χ1 -∗
    (∀ x, Χ1 x -∗ Χ2 x) ={⊤}=∗
    future۰consumer t Χ2.
  Proof.
    iIntros "(:inv)".
    iApply (ivar_4۰consumerｰwand with "Hinv").
  Qed.
  Lemma future۰consumerｰdivide {pool t Ψ Ξ} Χs :
    future۰inv pool t Ψ Ξ -∗
    future۰consumer t (λ x, [∗ list] Χ ∈ Χs, Χ x) ={⊤}=∗
    [∗ list] Χ ∈ Χs, future۰consumer t Χ.
  Proof.
    iIntros "(:inv)".
    iApply (ivar_4۰consumerｰdivide with "Hinv").
  Qed.
  Lemma future۰consumerｰsplit {pool t Ψ Ξ} Χ1 Χ2 :
    future۰inv pool t Ψ Ξ -∗
    future۰consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      future۰consumer t Χ1 ∗
      future۰consumer t Χ2.
  Proof.
    iIntros "(:inv)".
    iApply (ivar_4۰consumerｰsplit with "Hinv").
  Qed.

  Lemma future۰resultｰagree t v1 v2 :
    future۰result t v1 -∗
    future۰result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ivar_4۰resultｰagree.
  Qed.

  Lemma futureｰinvｰresult pool t Ψ Ξ v :
    future۰inv pool t Ψ Ξ -∗
    future۰result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) Hresult".
    iApply (ivar_4ｰinvｰresult with "Hinv Hresult").
  Qed.
  Lemma futureｰinvｰresult' pool t Ψ Ξ v :
    £ 1 -∗
    future۰inv pool t Ψ Ξ -∗
    future۰result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hfut_inv Hfut_result".
    iMod (futureｰinvｰresult with "Hfut_inv Hfut_result") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma futureｰinvｰresultｰconsumer pool t Ψ Ξ v Χ :
    future۰inv pool t Ψ Ξ -∗
    future۰result t v -∗
    future۰consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) Hresult Hconsumer".
    iApply (ivar_4ｰinvｰresultｰconsumer with "Hinv Hresult Hconsumer").
  Qed.
  Lemma futureｰinvｰresultｰconsumer' pool t Ψ Ξ v Χ :
    £ 2 -∗
    future۰inv pool t Ψ Ξ -∗
    future۰result t v -∗
    future۰consumer t Χ ={⊤}=∗
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
      t
    , RET t;
      future۰inv pool t Ψ Ξ ∗
      future۰consumer t Ψ ∗
      future۰result t v
    }}}.
  Proof.
    iIntros "%Φ (HΨ & HΞ) HΦ".

    iMod steps۰lbｰ0 as "#H⧖".

    wp۰apply (ivar_4٠makeｰspec Ψ Ξ with "[$]") as (t) "(#Hinv & Hconsumer & #Hresult & #Hwaiters)".

    iApply "HΦ".
    iFrame "#∗". iSteps.
  Qed.

  #[local] Lemma future٠setｰspec pool ctx scope t Ψ Ξ v :
    {{{
      pool۰context pool ctx scope ∗
      ivar_4۰inv t Ψ Ξ (pool۰context pool) ∗
      ivar_4۰producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      future٠set ctx t v
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      finished t
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
      t
    , RET t;
      pool۰context pool ctx scope ∗
      future۰inv pool t Ψ Ξ ∗
      future۰consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ (Hctx & Htask) HΦ".

    iMod steps۰lbｰ0 as "#H⧖".

    wp۰rec.
    wp۰apply+ (ivar_4٠createｰspec Ψ Ξ (pool۰context pool) with "[//]") as (t) "(#Hinv & Hproducer & Hconsumer)".

    wp۰apply+ (pool٠asyncｰspec
      True
      (finished t)
    with "[$Hctx Htask Hproducer]") as "(Hctx & _ & #Hpool_obligation)".
    { iIntros "{%} %ctx %scope Hctx".
      wp۰apply+ (wpｰwand with "(Htask Hctx)") as (v) "(Hctx & HΨ & HΞ)".
      wp۰apply (future٠setｰspec _ _ _ _ Ψ with "[$]") as "($ & #$) //".
    }

    iStep 6. iFrame "#∗". iIntros "!> !> Hpool_finished".
    iDestruct (pool۰obligationｰfinished with "Hpool_obligation Hpool_finished") as "#Hfinished".
    iNext => //.
  Qed.

  Lemma future٠waitｰspec pool ctx scope t Ψ Ξ :
    {{{
      pool۰context pool ctx scope ∗
      future۰inv pool t Ψ Ξ
    }}}
      future٠wait ctx t
    {{{
      v
    , RET v;
      £ 2 ∗
      pool۰context pool ctx scope ∗
      future۰result t v
    }}}.
  Proof.
    iIntros "%Φ (Hctx & (:inv)) HΦ".

    wp۰rec.

    wp۰apply+ (pool٠wait_ivarｰspec with "[$Hctx $Hinv]") as "(_ & Hctx & %v & #Hresult)". 1: iSteps.
    wp۰apply+ (ivar_4٠getｰspec with "[$Hinv $Hresult]") as "H£".
    iSteps.
  Qed.

  Lemma future٠iterｰspec P pool ctx scope t Ψ Ξ task :
    {{{
      pool۰context pool ctx scope ∗
      future۰inv pool t Ψ Ξ ∗
      ( ∀ ctx scope v,
        pool۰context pool ctx scope -∗
        future۰result t v -∗
        WP task ctx v {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          ▷ □ P
        }}
      )
    }}}
      future٠iter ctx t task
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

  Lemma future٠mapｰspec {pool ctx scope t1 Ψ1 Ξ1} Ψ2 Ξ2 task :
    {{{
      pool۰context pool ctx scope ∗
      future۰inv pool t1 Ψ1 Ξ1 ∗
      ( ∀ ctx scope v1,
        pool۰context pool ctx scope -∗
        future۰result t1 v1 -∗
        WP task ctx v1 {{ v2,
          pool۰context pool ctx scope ∗
          ▷ Ψ2 v2 ∗
          ▷ □ Ξ2 v2
        }}
      )
    }}}
      future٠map ctx t1 task
    {{{
      t2
    , RET t2;
      pool۰context pool ctx scope ∗
      future۰inv pool t2 Ψ2 Ξ2 ∗
      future۰consumer t2 Ψ2
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hinv_1 & Htask) HΦ".

    wp۰rec.
    wp۰apply+ (ivar_4٠createｰspec Ψ2 Ξ2 (pool۰context pool) with "[//]") as (t2) "(#Hinv_2 & Hproducer_2 & Hconsumer_2)".

    wp۰apply+ (future٠iterｰspec (
      pool۰obligation pool (finished t2)
    ) with "[$Hctx $Hinv_1 Htask Hproducer_2]") as "(Hctx & (:obligation))".
    { iIntros "{%} %ctx %scope %v1 Hctx #Hresult_1".
      wp۰apply+ (pool٠asyncｰspec
        True
        (finished t2)
      with "[$Hctx Htask Hproducer_2]") as "($ & _ & #$) //".
      { iIntros "{%} %ctx %scope Hctx".
        wp۰apply+ (wpｰwand with "(Htask Hctx Hresult_1)") as (v2) "(Hctx & HΨ2 & HΞ2)".
        wp۰apply (future٠setｰspec _ _ _ _ Ψ2 with "[$]") as "($ & #$) //".
      }
    }

    wp۰pures steps:"H⧖".

    iApply "HΦ".
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

#[global] Opaque future۰inv.
#[global] Opaque future۰obligation.
#[global] Opaque future۰consumer.
#[global] Opaque future۰result.
