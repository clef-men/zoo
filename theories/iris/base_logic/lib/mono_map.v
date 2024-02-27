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

#[local] Definition mono_map_UR K V `{Countable K} :=
  authUR $ gmapUR K $ agreeR $ leibnizO V.

Class MonoMapG Σ K V `{Countable K} := {
  #[local] mono_map_G_inG :: inG Σ (mono_map_UR K V) ;
}.

Definition mono_map_Σ K V `{Countable K} := #[
  GFunctor (mono_map_UR K V)
].
#[global] Instance subG_mono_map_Σ Σ K V `{Countable K} :
  subG (mono_map_Σ K V) Σ →
  MonoMapG Σ K V.
Proof.
  solve_inG.
Qed.

Section mono_map_G.
  Context `{mono_map_G : MonoMapG Σ K V}.

  Implicit Types m : gmap K V.

  #[local] Canonical V_O :=
    leibnizO V.

  Definition mono_map_auth γ m :=
    @own _ _ mono_map_G_inG γ (● (to_agree <$> m)).
  Definition mono_map_lb γ m :=
    @own _ _ mono_map_G_inG γ (◯ (to_agree <$> m)).
  Definition mono_map_elem γ i v :=
    mono_map_lb γ {[i := v]}.

  #[global] Instance mono_map_auth_timeless γ m :
    Timeless (mono_map_auth γ m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_map_lb_timeless γ m :
    Timeless (mono_map_lb γ m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_map_lb_persistent γ m :
    Persistent (mono_map_lb γ m).
  Proof.
    apply _.
  Qed.

  Lemma mono_map_alloc m :
    ⊢ |==>
      ∃ γ,
      mono_map_auth γ m.
  Proof.
    iApply own_alloc. apply auth_auth_valid.
    intros i. rewrite lookup_fmap. by destruct (m !! i).
  Qed.

  Lemma mono_map_lb_valid γ m1 m2 :
    mono_map_auth γ m1 -∗
    mono_map_lb γ m2 -∗
    ⌜m2 ⊆ m1⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
    iPureIntro.
    apply auth_both_valid_discrete in Hv. destruct Hv as (Hv&_).
    intros i. eapply lookup_included with (i := i) in Hv.
    rewrite !lookup_fmap in Hv.
    destruct (m1 !! i), (m2 !! i); try done; simpl in *.
    - apply Some_included in Hv. simpl. eapply (@leibniz_equiv (leibnizO V)). apply _.
      destruct Hv as [Hv|Hv].
      + by apply to_agree_inj.
      + by apply to_agree_included.
    - apply Some_included_is_Some in Hv. by inversion Hv.
  Qed.
  Lemma mono_map_elem_valid γ m i v :
    mono_map_auth γ m -∗
    mono_map_elem γ i v -∗
    ⌜m !! i = Some v⌝.
  Proof.
    iIntros "Hauth Helem".
    iDestruct (mono_map_lb_valid with "Hauth Helem") as %?%map_singleton_subseteq_l.
    iSteps.
  Qed.

  Lemma mono_map_lb_get' {γ m} m' :
    m' ⊆ m →
    mono_map_auth γ m ⊢ |==>
      mono_map_auth γ m ∗
      mono_map_lb γ m'.
  Proof.
    intros Hm'. rewrite -own_op.
    apply own_update, auth_update_alloc.
    apply local_update_unital. intros n z Hv Hz.
    rewrite mixin_ucmra_unit_left_id in Hz; first apply gmap_ucmra_mixin.
    split; eauto.
    rewrite -Hz.
    intros k. rewrite lookup_merge !lookup_fmap.
    destruct (m' !! k) eqn:Hm'_lookup; simpl.
    - eapply lookup_weaken in Hm'_lookup as ->; last done.
      rewrite -Some_op agree_idemp //.
    - destruct (m !! k); done.
  Qed.
  Lemma mono_map_lb_get γ m :
    mono_map_auth γ m ⊢ |==>
      mono_map_auth γ m ∗
      mono_map_lb γ m.
  Proof.
    apply mono_map_lb_get'. done.
  Qed.
  Lemma mono_map_elem_get {γ m} i v :
    m !! i = Some v →
    mono_map_auth γ m ⊢ |==>
      mono_map_auth γ m ∗
      mono_map_elem γ i v.
  Proof.
    intros. apply mono_map_lb_get'. rewrite map_singleton_subseteq_l //.
  Qed.

  Lemma mono_map_insert {γ m} i v :
    m !! i = None →
    mono_map_auth γ m ⊢ |==>
    mono_map_auth γ (<[i := v]> m).
  Proof.
    iIntros (Hi) "?". iApply (own_update with "[$]").
    rewrite fmap_insert. apply auth_update_auth with (b':={[i:=to_agree v]}).
    apply (@alloc_singleton_local_update K _ _ (agreeR $ leibnizO V) (to_agree <$> m) i (to_agree v)).
    { rewrite lookup_fmap Hi //. }
    done.
  Qed.
  Lemma mono_map_insert' {γ m} i v :
    m !! i = None →
    mono_map_auth γ m ⊢ |==>
      mono_map_auth γ (<[i:=v]> m) ∗
      mono_map_elem γ i v.
  Proof.
    iIntros "%Hlookup Hauth".
    iMod (mono_map_insert with "Hauth") as "Hauth"; first done.
    iApply (mono_map_elem_get with "Hauth"); first rewrite lookup_insert //.
  Qed.
End mono_map_G.

#[global] Opaque mono_map_auth.
#[global] Opaque mono_map_lb.
