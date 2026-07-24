Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.fupd.
Require Import zoo.iris.base_logic.lib.saved_prop.
Require Import zoo.base.
Require Import zoo_std.ivar_4.
Require Import zoo_parabs.pool.
Require Import zoo_parabs.vertex.
Require Export examples.fibonacci.
Require Export examples.vertex_fibonacci__code.
Require Import zoo.options.

Implicit Type r : location.
Implicit Type v ctx vtx : val.

Class VertexFibonacciG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] vertex_fibonacci۰G۰pool۰G :: PoolG Σ
  ; #[local] vertex_fibonacci۰G۰vertex۰G :: VertexG Σ
  ; #[local] vertex_fibonacci۰G۰ivar۰G :: Ivar4G Σ
  ; #[local] vertex_fibonacci۰G۰saved_prop۰G :: SavedPropG Σ
  }.

Definition vertex_fibonacci۰Σ :=
  #[pool۰Σ
  ; vertex۰Σ
  ; ivar_4۰Σ
  ; saved_prop۰Σ
  ].
#[global] Instance subG𑁒vertex_fibonacci۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG vertex_fibonacci۰Σ Σ →
  VertexFibonacciG Σ.
Proof.
  base.solve_inG.
Qed.

Section vertex_fibonacci۰G.
  Context `{vertex_fibonacci۰G : VertexFibonacciG Σ}.

  #[local] Lemma vertex_fibonacci٠main₀𑁒spec vtx iter r n :
    vertex۰inv vtx (r ↦ᵣ #(fibonacci n)) True -∗
    r ↦ᵣ 0 -∗
    vertex۰wp
      vtx
      (r ↦ᵣ #(fibonacci n))
      True
      (fun: "ctx" => vertex_fibonacci٠main₀ "ctx" vtx #r #n)
      iter.
  Proof.
    iLöb as "HLöb" forall (vtx iter r n).

    iEval (setoid_rewrite vertex۰wp𑁒unfold).
    iIntros "#Hvtx_inv Hr %pool %ctx %scope %iter' Hctx _ Hvtx_model".

    wp۰pures. wp۰rec. wp۰pures.
    case_bool_decide as Hif; wp۰pures.

    - iSteps. iPureIntro.
      rewrite fibonacci𑁒base //. 1: lia.

    - wp۰ref r1 as "Hr1".
      wp۰apply+ (vertex٠create𑁒spec
        (r1 ↦ᵣ #(fibonacci (n - 1)))
        True
        None
      with "[//]") as (vtx1 iter1) "(#Hvtx1_inv & Hvtx1_model & Hvtx1_output)".
      wp۰apply+ (vertex٠set_task𑁒spec with "Hvtx1_model") as "Hvtx1_model".
      wp۰apply+ (vertex٠release𑁒spec with "[$Hctx $Hvtx1_model Hr1]") as "Hctx".
      { iFrame "#".
        iEval (replace (n - 1)%Z with ⁺(n - 1) by lia).
        iApply ("HLöb" with "Hvtx1_inv Hr1").
      }

      wp۰ref r2 as "Hr2".
      wp۰apply+ (vertex٠create𑁒spec
        (r2 ↦ᵣ #(fibonacci (n - 2)))
        True
        None
      with "[//]") as (vtx2 iter2) "(#Hvtx2_inv & Hvtx2_model & Hvtx2_output)".
      wp۰apply+ (vertex٠set_task𑁒spec with "Hvtx2_model") as "Hvtx2_model".
      wp۰apply+ (vertex٠release𑁒spec with "[$Hctx $Hvtx2_model Hr2]") as "Hctx".
      { iFrame "#".
        iEval (replace (n - 2)%Z with ⁺(n - 2) by lia).
        iApply ("HLöb" with "Hvtx2_inv Hr2").
      }

      wp۰apply+ (vertex٠precede𑁒spec with "[$Hvtx_model]") as "(Hvtx_model & #Hvtx1_predecessor)". 1: iFrame "#".
      wp۰apply+ (vertex٠precede𑁒spec with "[$Hvtx_model]") as "(Hvtx_model & #Hvtx2_predecessor)". 1: iFrame "#".
      wp۰apply+ (vertex٠yield𑁒spec with "[$Hvtx_model]") as "Hvtx_model".
      iStep 4.

      iEval (rewrite vertex۰wp𑁒unfold).
      iIntros "{%- Hif} %pool %ctx %scope %iter'' Hctx #Hvtx_ready Hvtx_model".

      wp۰pures credits:"H£".
      iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

      iDestruct (vertex𑁒predecessor𑁒finished with "Hvtx1_predecessor Hvtx_ready") as "#Hvtx1_finished".
      iMod (vertex𑁒inv𑁒finished𑁒output with "Hvtx1_inv Hvtx1_finished Hvtx1_output") as "Hr1".

      iDestruct (vertex𑁒predecessor𑁒finished with "Hvtx2_predecessor Hvtx_ready") as "#Hvtx2_finished".
      iMod (vertex𑁒inv𑁒finished𑁒output with "Hvtx2_inv Hvtx2_finished Hvtx2_output") as "Hr2".

      iMod (lc𑁒fupd𑁒elim𑁒laterN _ (_ ∗ _) with "H£ [Hr1 Hr2]") as "(Hr1 & Hr2)".
      { iNext. iAccu. }

      iSteps. iPureIntro.
      rewrite (fibonacci𑁒recursive n). 1: lia.
      rewrite -Nat2Z.inj_add //.
  Qed.

  Lemma vertex_fibonacci٠main𑁒spec (num_dom n : nat) :
    {{{
      True
    }}}
      vertex_fibonacci٠main #num_dom #n
    {{{
      RET #(fibonacci n);
      True
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.

    wp۰apply+ (pool٠run𑁒spec (λ pool v,
      ⌜v = #_⌝
    )%I) as (pool ?) "(_ & ->)". 1: lia.
    { iIntros "%pool %ctx %scope _ Hctx".

      wp۰ref r as "Hr".
      wp۰apply+ (vertex٠create𑁒spec
        (r ↦ᵣ #(fibonacci n))
        True
        None
      with "[//]") as (vtx1 iter) "(#Hvtx1_inv & Hvtx1_model & Hvtx1_output)".
      wp۰apply+ (vertex٠set_task𑁒spec with "Hvtx1_model") as "Hvtx1_model".
      wp۰apply+ (vertex٠release𑁒spec with "[$Hctx $Hvtx1_inv $Hvtx1_model Hr]") as "Hctx".
      { iApply (vertex_fibonacci٠main₀𑁒spec with "Hvtx1_inv Hr"). }

      wp۰apply+ (ivar_4٠create𑁒spec
        (λ _, r ↦ᵣ #(fibonacci n))%I
        (λ _, True)%I
        (λ _ (_ : unit), True)%I
      with "[//]") as (ivar) "(#Hivar_inv & Hivar_producer & Hivar_consumer)".

      wp۰apply+ (vertex٠create'𑁒spec
        True
        True
      with "[//]") as (vtx2 iter2) "(#Hvtx2_inv & Hvtx2_model & _)".
      wp۰apply+ (vertex٠precede𑁒spec with "[$Hvtx2_model]") as "(Hvtx2_model & #Hvtx1_predecessor)". 1: iFrame "#".
      wp۰apply+ (vertex٠release𑁒spec' with "[$Hctx $Hvtx2_model Hvtx1_output Hivar_producer]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx #Hvtx2_ready".

        wp۰pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

        iDestruct (vertex𑁒predecessor𑁒finished with "Hvtx1_predecessor Hvtx2_ready") as "#Hvtx1_finished".
        iMod (vertex𑁒inv𑁒finished𑁒output' with "H£ Hvtx1_inv Hvtx1_finished Hvtx1_output") as "Hr".

        wp۰apply+ (ivar_4٠notify𑁒spec () with "[$Hivar_inv $Hivar_producer $Hr]"). 1: iSteps.
        iSteps.
      }

      wp۰apply+ (pool٠wait_ivar𑁒spec with "[$Hctx $Hivar_inv]") as "(H£ & $ & (%v & #Hivar_result))". 1: iSteps.
      iMod (ivar_4𑁒inv𑁒result𑁒consumer' with "H£ Hivar_inv Hivar_result Hivar_consumer") as "(Hr & _)".
      iSteps.
    }

    iSteps.
  Qed.
End vertex_fibonacci۰G.

Require examples.vertex_fibonacci__opaque.
