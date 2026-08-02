Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.fupd.
Require Import zoo.iris.base_logic.lib.saved_prop.
Require Import zoo.base.
Require Export examples.vertex_simple__code.
Require Import examples.vertex_simple__types.
Require Import zoo.options.

Implicit Type v ctx a b c d : val.

Class VertexSimpleG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] vertex_simple۰G۰pool۰G :: PoolG Σ
  ; #[local] vertex_simple۰G۰vertex۰G :: VertexG Σ
  ; #[local] vertex_simple۰G۰ivar۰G :: Ivar4G Σ
  ; #[local] vertex_simple۰G۰saved_prop۰G :: SavedPropG Σ
  }.

Definition vertex_simple۰Σ :=
  #[pool۰Σ
  ; vertex۰Σ
  ; ivar_4۰Σ
  ; saved_prop۰Σ
  ].
#[global] Instance subGｰvertex_simple۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG vertex_simple۰Σ Σ →
  VertexSimpleG Σ.
Proof.
  base.solve_inG.
Qed.

Section vertex_simple۰G.
  Context `{vertex_simple۰G : VertexSimpleG Σ}.

  Implicit Type P_ab P_ac P_b P_c P_d : iProp Σ.

  Lemma vertex_simple٠mainｰspec P_ab P_ac P_b P_c P_d (num_dom : nat) a b c d :
    {{{
      WP a () {{ res, ⌜res = ()%V⌝ ∗ P_ab ∗ P_ac }} ∗
      (P_ab -∗ WP b () {{ res, ⌜res = ()%V⌝ ∗ P_b }}) ∗
      (P_ac -∗ WP c () {{ res, ⌜res = ()%V⌝ ∗ P_c }}) ∗
      (P_b -∗ P_c -∗ WP d () {{ res, ⌜res = ()%V⌝ ∗ P_d }})
    }}}
      vertex_simple٠main #num_dom a b c d
    {{{
      RET ();
      P_d
    }}}.
  Proof.
    iIntros "%Φ (Ha & Hb & Hc & Hd) HΦ".

    wp۰rec.

    wp۰apply+ (ivar_4٠createｰspec
      (λ _, P_d)
      (λ _, True)%I
      (λ _ (_ : unit), True)%I
    with "[//]") as (ivar) "(#Hivar_inv & Hivar_producer & Hivar_consumer)".

    wp۰apply+ (vertex٠create'ｰspec
      (P_ab ∗ P_ac)
      True
    with "[//]") as (vtx_a iter_a) "(#Hvtx_a_inv & Hvtx_a_model & Hvtx_a_output)".
    iMod (vertex۰outputｰsplit with "Hvtx_a_inv Hvtx_a_output") as "(Hvtx_a_output_b & Hvtx_a_output_c)".
    wp۰apply+ (vertex٠create'ｰspec
      P_b
      True
    with "[//]") as (vtx_b iter_b) "(#Hvtx_b_inv & Hvtx_b_model & Hvtx_b_output)".
    wp۰apply+ (vertex٠create'ｰspec
      P_c
      True
    with "[//]") as (vtx_c iter_c) "(#Hvtx_c_inv & Hvtx_c_model & Hvtx_c_output)".
    wp۰apply+ (vertex٠create'ｰspec
      True
      True
    with "[//]") as (vtx_d iter_d) "(#Hvtx_d_inv & Hvtx_d_model & _)".

    wp۰apply+ (vertex٠precedeｰspec with "[$Hvtx_b_model]") as "(Hvtx_b_model & #Hvtx_a_predecessor_b)". 1: iFrame "#".
    wp۰apply+ (vertex٠precedeｰspec with "[$Hvtx_c_model]") as "(Hvtx_c_model & #Hvtx_a_predecessor_c)". 1: iFrame "#".
    wp۰apply+ (vertex٠precedeｰspec with "[$Hvtx_d_model]") as "(Hvtx_d_model & #Hvtx_b_predecessor)". 1: iFrame "#".
    wp۰apply+ (vertex٠precedeｰspec with "[$Hvtx_d_model]") as "(Hvtx_d_model & #Hvtx_c_predecessor)". 1: iFrame "#".

    wp۰apply+ (pool٠runｰspec (λ pool res,
      ⌜res = ()%V⌝ ∗
      P_d
    )%I with "[- HΦ]") as (pool ?) "(_ & -> & HP_d)". 1: lia.
    { iIntros "%pool %ctx %scope _ Hctx".

      wp۰apply+ (vertex٠releaseｰspec' with "[$Hctx $Hvtx_d_model Hvtx_b_output Hvtx_c_output Hd Hivar_producer]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx #Hvtx_d_ready".

        wp۰pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

        iDestruct (vertexｰpredecessorｰfinished with "Hvtx_b_predecessor Hvtx_d_ready") as "#Hvtx_b_finished".
        iMod (vertexｰinvｰfinishedｰoutput with "Hvtx_b_inv Hvtx_b_finished Hvtx_b_output") as "HP_b".

        iDestruct (vertexｰpredecessorｰfinished with "Hvtx_c_predecessor Hvtx_d_ready") as "#Hvtx_c_finished".
        iMod (vertexｰinvｰfinishedｰoutput with "Hvtx_c_inv Hvtx_c_finished Hvtx_c_output") as "HP_c".

        iMod (lcｰfupdｰelimｰlaterN _ (P_b ∗ P_c) with "H£ [$]") as "(HP_b & HP_c)".
        wp۰apply (wpｰwand with "(Hd HP_b HP_c)") as (res) "(-> & HP_d)".

        wp۰apply+ (ivar_4٠notifyｰspec () with "[$Hivar_inv $Hivar_producer $HP_d]"). 1: iSteps.
        iSteps.
      }

      wp۰apply+ (vertex٠releaseｰspec' with "[$Hctx $Hvtx_c_model Hvtx_a_output_c Hc]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx #Hvtx_c_ready".

        wp۰pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

        iDestruct (vertexｰpredecessorｰfinished with "Hvtx_a_predecessor_c Hvtx_c_ready") as "#Hvtx_a_finished".
        iMod (vertexｰinvｰfinishedｰoutput' with "H£ Hvtx_a_inv Hvtx_a_finished Hvtx_a_output_c") as "HP_ac".

        wp۰apply (wpｰwand with "(Hc HP_ac)") as (res) "(-> & $)".
        iSteps => //.
      }

      wp۰apply+ (vertex٠releaseｰspec' with "[$Hctx $Hvtx_b_model Hvtx_a_output_b Hb]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx #Hvtx_b_ready".

        wp۰pures credits:"H£".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.

        iDestruct (vertexｰpredecessorｰfinished with "Hvtx_a_predecessor_b Hvtx_b_ready") as "#Hvtx_a_finished".
        iMod (vertexｰinvｰfinishedｰoutput' with "H£ Hvtx_a_inv Hvtx_a_finished Hvtx_a_output_b") as "HP_ab".

        wp۰apply (wpｰwand with "(Hb HP_ab)") as (res) "(-> & $)".
        iSteps => //.
      }

      wp۰apply+ (vertex٠releaseｰspec' with "[$Hctx $Hvtx_a_model Ha]") as "Hctx".
      { iFrame "#". iIntros "{%} %pool %ctx %scope Hctx Hvtx_a_ready".

        wp۰apply+ (wpｰwand with "Ha") as (res) "(-> & $)".
        iSteps => //.
      }

      iApply wpｰfupd.
      wp۰apply+ (pool٠wait_ivarｰspec with "[$Hctx $Hivar_inv]") as "(H£ & $ & (%v & #Hivar_result))". 1: iSteps.
      iMod (ivar_4ｰinvｰresultｰconsumer' with "H£ Hivar_inv Hivar_result Hivar_consumer") as "($ & _)" => //.
    }

    iSteps.
  Qed.
End vertex_simple۰G.

Require examples.vertex_simple__opaque.
