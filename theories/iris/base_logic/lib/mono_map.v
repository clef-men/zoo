From iris.algebra Require Import
  auth
  gmap
  agree.

From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Export
  lib.base.
From zebre.iris Require Import
  diaframe.
From zebre Require Import
  options.

Class MonoMapG Σ K V `{Countable K} := {
  #[local] mono_map_G_inG :: inG Σ (authUR $ gmapUR K $ agreeR V) ;
}.

Definition mono_map_Σ K V `{Countable K} := #[
  GFunctor (authUR $ gmapUR K $ agreeR V)
].
#[global] Instance subG_mono_map_Σ Σ K V `{Countable K} :
  subG (mono_map_Σ K V) Σ →
  MonoMapG Σ K V.
Proof.
  solve_inG.
Qed.

Section mono_map_G.
  Context `{mono_map_G : MonoMapG Σ K V}.

  Definition mono_map_auth γ σ :=
    @own _ _ mono_map_G_inG γ (● (to_agree <$> σ)).
  Definition mono_map_elem γ i v :=
    @own _ _ mono_map_G_inG γ (◯ {[i := to_agree v]}).

  #[global] Instance mono_map_elem_timeless γ i v :
    Discrete v →
    Timeless (mono_map_elem γ i v).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_map_elem_persistent γ i v :
    Persistent (mono_map_elem γ i v).
  Proof.
    apply _.
  Qed.

  Lemma mono_map_alloc α :
    ⊢ |==>
      ∃ γ,
      mono_map_auth γ α.
  Proof.
    iApply own_alloc. apply auth_auth_valid.
    intros i. rewrite lookup_fmap. by destruct (α !! i).
  Qed.

  Lemma mono_map_insert γ σ i v :
    σ !! i = None →
    mono_map_auth γ σ ⊢ |==>
      mono_map_auth γ (<[i:=v]> σ) ∗
      mono_map_elem γ i v.
  Proof.
    iIntros (Hi) "?". rewrite /mono_map_elem /mono_map_auth.
    rewrite -own_op. iApply (own_update with "[$]").
    apply auth_update_alloc. rewrite fmap_insert. apply alloc_singleton_local_update.
    { rewrite lookup_fmap Hi //. }
    done.
  Qed.

  Lemma mono_map_extract γ σ i v :
    σ !! i = Some v ->
    mono_map_auth γ σ ⊢ |==>
      mono_map_auth γ σ ∗
      mono_map_elem γ i v.
  Proof.
    iIntros (Hi) "He". rewrite /mono_map_elem /mono_map_auth.
    rewrite -own_op. iApply (own_update with "[$]").
    apply auth_update_alloc.
    apply local_update_unital. intros n z Hv Hz.
    rewrite mixin_ucmra_unit_left_id in Hz; first apply gmap_ucmra_mixin.
    split. eauto.
    rewrite -Hz.
    rewrite -{2}(insert_id σ i v) // fmap_insert -insert_op.
    rewrite agree_idemp left_id // insert_id //.
    rewrite lookup_fmap Hi //.
  Qed.

  Lemma mono_map_lookup `{!LeibnizEquiv V} `{OfeDiscrete V} γ σ i v :
    mono_map_auth γ σ -∗
    mono_map_elem γ i v -∗
    ⌜σ !! i = Some v⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
    iPureIntro.
    apply auth_both_valid_discrete in Hv. destruct Hv as (Hv&_).
    apply singleton_included_l in Hv. destruct Hv as (y,(Hv1&Hv2)).
    rewrite lookup_fmap in Hv1.
    destruct (σ !! i) as [w|] eqn:Hw.
    2:{ exfalso. inversion Hv1. }
    simpl in Hv1. rewrite -Hv1 in Hv2.
    assert (v ≡ w ) as Hv.
    { apply Some_included in Hv2. destruct Hv2 as [Hv2|Hv2].
      - by apply to_agree_inj in Hv2.
      - by apply to_agree_included in Hv2.
    }
    apply leibniz_equiv in Hv. naive_solver.
  Qed.
End mono_map_G.

#[global] Opaque mono_map_auth.
#[global] Opaque mono_map_elem.
