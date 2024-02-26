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

Class MonoMapG (Σ : gFunctors) (K V : Type) `{Countable K} := {
    #[local] mono_map_G_inG :: inG Σ (authUR $ gmapUR K $ agreeR $ leibnizO V) ;
}.

Definition mono_map_Σ (K V : Type) `{Countable K} := #[
  GFunctor (authUR $ gmapUR K $ agreeR $ leibnizO V)
].
#[global] Instance subG_mono_map_Σ Σ K V `{Countable K} :
  subG (mono_map_Σ K V) Σ →
  MonoMapG Σ K V.
Proof.
  solve_inG.
Qed.

Section mono_map_G.
  Context `{mono_map_G : MonoMapG Σ K V}.

  Implicit Types γ : gname.
  Implicit Types m : gmap K V.

  Definition mono_map_auth γ m :=
    @own _ _ mono_map_G_inG γ (● (to_agree <$> m)).
  Definition mono_map_lb γ m :=
    @own _ _ mono_map_G_inG γ (◯ (to_agree <$> m)).

  #[global] Instance mono_map_lb_persistent γ m :
    Persistent (mono_map_lb γ m).
  Proof. apply _. Qed.

  Lemma mono_map_alloc m :
    ⊢ |==>
      ∃ γ,
      mono_map_auth γ m.
  Proof.
    iApply own_alloc. apply auth_auth_valid.
    intros i. rewrite lookup_fmap. by destruct (m !! i).
  Qed.

  Lemma mono_map_insert {γ m} i v :
    m !! i = None →
    mono_map_auth γ m ⊢ |==>
    mono_map_auth γ (<[i := v]> m).
  Proof.
    iIntros (Hi) "?". iApply (own_update with "[$]").
    rewrite fmap_insert. apply auth_update_auth with (b':={[i:=to_agree v]}).
    apply (@alloc_singleton_local_update K _ _ ( agreeR $ leibnizO V) (to_agree <$> m) i (to_agree v)).
    { rewrite lookup_fmap Hi //. }
    done.
  Qed.

  Lemma mono_map_lb_get γ m :
    mono_map_auth γ m ==∗
    mono_map_auth γ m  ∗ mono_map_lb γ m.
  Proof.
    rewrite /mono_map_auth /mono_map_lb -own_op.
    iApply own_update. apply auth_update_alloc.
    apply local_update_unital. intros n z Hv Hz.
    rewrite mixin_ucmra_unit_left_id in Hz. apply gmap_ucmra_mixin.
    split. eauto.
    rewrite -Hz gmap_op.
    intros l. rewrite lookup_merge lookup_fmap.
    destruct (m !! l); last done. simpl. rewrite -Some_op agree_idemp //.
  Qed.

  Lemma mono_map_valid γ m1 m2 :
    mono_map_auth γ m1 -∗
    mono_map_lb γ m2 -∗
    ⌜m2 ⊆ m1⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
    iPureIntro.
    apply auth_both_valid_discrete in Hv. destruct Hv as (Hv&_).
    intros i. eapply lookup_included with (i:=i) in Hv.
    rewrite !lookup_fmap in Hv.
    destruct (m1!!i),(m2!!i); try done; simpl in *.
    { apply Some_included in Hv. simpl. eapply (@leibniz_equiv (leibnizO V)). apply _.
      destruct Hv as [Hv|Hv].
      - by apply to_agree_inj.
      - by apply to_agree_included. }
    { apply Some_included_is_Some in Hv. by inversion Hv. }
  Qed.
End mono_map_G.

#[global] Opaque mono_map_auth.
#[global] Opaque mono_map_lb.
