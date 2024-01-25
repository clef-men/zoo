From iris.prelude Require Import prelude.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.algebra Require Import ofe gmap agree.

Class map_agreeG Σ K V `{Countable K}  := map_agreeG_inG : inG Σ (authUR (gmapUR K (agreeR V))).
Local Existing Instance map_agreeG_inG.

Definition map_agreeΣ K V `{Countable K} : gFunctors :=
  #[ GFunctor (authUR (gmapUR K (agreeR V))) ].

Global Instance subG_map_agreeΣ Σ K V `{Countable K} :
  subG (map_agreeΣ K V) Σ → map_agreeG Σ K V.
Proof. solve_inG. Qed.

Section map_agree.
Context `{V:ofe, map_agreeG Σ K V}.

Definition map_agree_auth γ σ :=
  @own _ _ map_agreeG_inG γ (● (to_agree <$> σ)).

Definition map_agree_elem γ i v :=
  @own _ _ map_agreeG_inG γ (◯ {[i:=to_agree v]}).

Lemma map_agree_alloc α :
  ⊢ |==> ∃ γ, map_agree_auth γ α.
Proof.
  iApply own_alloc. apply auth_auth_valid.
  intros i. rewrite lookup_fmap. by destruct (α !! i).
Qed.

Lemma map_agree_insert γ σ i v :
  σ !! i = None ->
  map_agree_auth γ σ ==∗ map_agree_auth γ (<[i:=v]> σ) ∗ map_agree_elem γ i v.
Proof.
  iIntros (Hi) "?". rewrite /map_agree_elem /map_agree_auth.
  rewrite -own_op. iApply (own_update with "[$]").
  apply auth_update_alloc. rewrite fmap_insert. apply alloc_singleton_local_update.
  { rewrite lookup_fmap Hi //. }
  easy.
Qed.

Lemma map_agree_extract γ σ i v :
  σ !! i = Some v ->
  map_agree_auth γ σ ==∗ map_agree_auth γ σ ∗ map_agree_elem γ i v.
Proof.
  iIntros (Hi) "He". rewrite /map_agree_elem /map_agree_auth.
  rewrite -own_op. iApply (own_update with "[$]").
  apply auth_update_alloc.
  apply local_update_unital. intros n z Hv Hz.
  rewrite mixin_ucmra_unit_left_id in Hz; last apply gmap_ucmra_mixin.
  split. eauto.
  rewrite -Hz.
  rewrite -{2}(insert_id σ i v) // fmap_insert -insert_op.
  rewrite agree_idemp left_id // insert_id //.
  rewrite lookup_fmap Hi //.
Qed.

Lemma map_agree_lookup `{!LeibnizEquiv V} `{OfeDiscrete V} γ σ (i:K) (v:V) :
  map_agree_auth γ σ -∗ map_agree_elem γ i v -∗ ⌜σ !! i = Some v⌝.
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
    now apply to_agree_inj in Hv2. now apply to_agree_included in Hv2. }
  apply leibniz_equiv in Hv. naive_solver.
Qed.
End map_agree.
