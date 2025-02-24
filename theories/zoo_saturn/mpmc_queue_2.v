From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  relations.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.auth_mono.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From zoo_saturn Require Export
  base
  mpmc_queue_2__code.
From zoo_saturn Require Import
  mpmc_queue_2__types.
From zoo Require Import
  options.

Implicit Types l back : location.
Implicit Types backs : gmap location nat.
Implicit Types v t : val.
Implicit Types vs move : list val.

Inductive emptiness :=
  | Empty
  | Nonempty.
Implicit Types empty : emptiness.

#[local] Instance emptiness_inhabited : Inhabited emptiness :=
  populate Empty.

Inductive lstatus :=
  | Stable empty
  | Unstable back move.
Implicit Types lstatus : lstatus.

#[local] Instance lstatus_inhabited : Inhabited lstatus :=
  populate (Stable inhabitant).

Record lstate := {
  lstate_backs : gmap location nat ;
  lstate_index : nat ;
  lstate_lstatus : lstatus ;
}.
Implicit Types lstate : lstate.

#[local] Definition lstate_with_lstatus lstate lstatus :=
  {|lstate_backs := lstate.(lstate_backs) ;
    lstate_index := lstate.(lstate_index) ;
    lstate_lstatus := lstatus ;
  |}.

#[local] Definition lstate_le lstate1 lstate2 :=
  lstate1.(lstate_backs) ⊆ lstate2.(lstate_backs) ∧
  lstate1.(lstate_index) ≤ lstate2.(lstate_index).

#[local] Instance lstate_inhabited : Inhabited lstate :=
  populate {|
    lstate_backs := inhabitant ;
    lstate_index := inhabitant ;
    lstate_lstatus := inhabitant ;
  |}.

#[local] Instance lstate_le_reflexive :
  Reflexive lstate_le.
Proof.
  done.
Qed.
#[local] Instance lstate_le_transitive :
  Transitive lstate_le.
Proof.
  intros lstate1 lstate2 lstate3 (? & ?) (? & ?).
  split.
  - etrans; done.
  - lia.
Qed.

Inductive lstep : relation lstate :=
  | lstep_empty lstate1 lstate2 :
      lstate1.(lstate_lstatus) = Stable Nonempty →
      lstate2 = lstate_with_lstatus lstate1 (Stable Empty) →
      lstep lstate1 lstate2
  | lstep_destabilize lstate1 lstate2 back move :
      lstate1.(lstate_lstatus) = Stable Empty →
      lstate2 = lstate_with_lstatus lstate1 (Unstable back move) →
      lstep lstate1 lstate2
  | lstep_stabilize lstate1 lstate2 back move :
      lstate1.(lstate_lstatus) = Unstable back move →
      back ∉ dom lstate1.(lstate_backs) →
      lstate2 =
        {|lstate_backs := <[back := lstate1.(lstate_index) + length move]> lstate1.(lstate_backs) ;
          lstate_index := lstate1.(lstate_index) + length move ;
          lstate_lstatus := Stable Nonempty ;
        |} →
      lstep lstate1 lstate2.
#[local] Hint Constructors lstep : core.

#[local] Definition lsteps :=
  rtc lstep.

#[local] Lemma lstep_mono lstate1 lstate2 :
  lstep lstate1 lstate2 →
  lstate_le lstate1 lstate2.
Proof.
  intros Hlstep. invert Hlstep; [done.. |].
  split.
  - apply insert_subseteq, not_elem_of_dom. done.
  - simpl. lia.
Qed.
#[local] Lemma lsteps_mono lstate1 lstate2 :
  lsteps lstate1 lstate2 →
  lstate_le lstate1 lstate2.
Proof.
  intros Hlsteps.
  rewrite -preorder_rtc.
  apply (rtc_congruence (R := lstep) id); last done.
  apply lstep_mono.
Qed.

Class MpmcQueue2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_queue_2_G_model :: TwinsG Σ (leibnizO (list val)) ;
  #[local] mpmc_queue_2_G_lstate :: AuthMonoG (A := leibnizO lstate) Σ lstep ;
}.

Definition mpmc_queue_2_Σ := #[
  twins_Σ (leibnizO (list val)) ;
  auth_mono_Σ (A := leibnizO lstate) lstep
].
#[global] Instance subG_mpmc_queue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_queue_2_Σ Σ →
  MpmcQueue2G Σ.
Proof.
  solve_inG.
Qed.

Section mpmc_queue_2_G.
  Context `{mpmc_queue_2_G : MpmcQueue2G Σ}.

  Record metadata := {
    metadata_model : gname ;
    metadata_lstate : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata_model).
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata_model).

  #[local] Definition lstate_auth' γ_lstate backs i lstatus :=
    auth_mono_auth _ γ_lstate (DfracOwn 1)
      {|lstate_backs := backs ;
        lstate_index := i ;
        lstate_lstatus := lstatus ;
      |}.
  #[local] Definition lstate_auth γ backs i lstatus :=
    lstate_auth' γ.(metadata_lstate) backs i lstatus.
  #[local] Definition lstate_lb γ backs i lstatus :=
    auth_mono_lb _ γ.(metadata_lstate)
      {|lstate_backs := backs ;
        lstate_index := i ;
        lstate_lstatus := lstatus ;
      |}.

  #[local] Fixpoint frontlst_to_val (i : nat) vs :=
    match vs with
    | [] =>
        ‘Front( #i )%V
    | v :: vs =>
        ‘Cons( #i, v, frontlst_to_val (S i) vs )%V
    end.

  #[local] Fixpoint backlst_to_val (i : nat) back vs :=
    match vs with
    | [] =>
        #back
    | v :: vs =>
        ‘Snoc( #(i + length vs), v, backlst_to_val i back vs )%V
    end.

  #[local] Definition back_model back (i : nat) v_move : iProp Σ :=
    back ↦ₕ Header §Back 2 ∗
    back.[index] ↦□ #i ∗
    back.[move] ↦ v_move.
  #[local] Definition back_model' back i : iProp Σ :=
    ∃ v_move,
    back_model back i v_move.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ backs i lstatus i_front vs_front i_back back vs_back vs,
    l.[front] ↦ frontlst_to_val i_front vs_front ∗
    l.[back] ↦ backlst_to_val i_back back vs_front ∗
    ([∗ map] back ↦ i ∈ backs, back_model' back i) ∗
    model₂ γ vs ∗
    lstate_auth γ backs i lstatus ∗
    ⌜(i_front + length vs_front)%nat = S i⌝ ∗
    match lstatus with
    | Stable empty =>
        ⌜i_back = i⌝ ∗
        ⌜backs !! back = Some i_back⌝ ∗
        ⌜vs = vs_front ++ reverse vs_back⌝ ∗
        ⌜if empty then vs_front = [] else 0 < length vs_front⌝
    | Unstable back_ move =>
        ∃ back',
        ⌜back_ = back⌝ ∗
        ⌜backs !! back' = Some i⌝ ∗
        ⌜i_back = (i + length move)%nat⌝ ∗
        ⌜vs_front = []⌝ ∗
        ⌜vs_back = []⌝ ∗
        back_model back i_back (backlst_to_val i back' move)
    end.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %backs{} &
      %i{} &
      %lstatus{} &
      %i_front{} &
      %vs_front{} &
      %i_back{} &
      %back{} &
      %vs_back{} &
      %vs{} &
      Hl_front &
      Hl_back &
      Hbacks &
      Hmodel₂ &
      >Hlstate_auth &
      >% &
      Hlstatus
    )".
  #[local] Instance : CustomIpatFormat "inv_inner_stable" :=
    "(
      % &
      %Hbacks_lookup &
      % &
      %
    )".
  #[local] Instance : CustomIpatFormat "inv_inner_unstable" :=
    "(
      %back' &
      % &
      %Hbacks_lookup &
      % &
      % &
      % &
      Hback
    )".
  Definition mpmc_queue_2_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (inv_inner l γ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      #Hmeta &
      #Hinv
    )".

  Definition mpmc_queue_2_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l &
      %γ &
      -> &
      #Hmeta &
      Hmodel₁
    )".

  #[global] Instance mpmc_queue_2_model_timeless t vs :
    Timeless (mpmc_queue_2_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_queue_2_inv_persistent t ι :
    Persistent (mpmc_queue_2_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma lstate_lb_valid γ backs1 i1 lstatus1 backs2 i2 lstatus2 :
    lstate_auth γ backs1 i1 lstatus1 -∗
    lstate_lb γ backs2 i2 lstatus2 -∗
      ⌜backs2 ⊆ backs1⌝ ∗
      ⌜i2 ≤ i2⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %(? & ?)%lsteps_mono. done.
  Qed.
  #[local] Lemma lstate_lb_header l γ ι backs i lstatus back :
    back ∈ dom backs →
    inv ι (inv_inner l γ) -∗
    lstate_lb γ backs i lstatus -∗
      |={⊤}=>
      back ↦ₕ Header §Back 2.
  Proof.
    iIntros ((j & Hbacks_lookup)%elem_of_dom) "#Hinv #Hlstate_lb".
    iInv "Hinv" as "(:inv_inner =')".
    iAssert (▷ back ↦ₕ Header §Back 2)%I as "#>$".
    { iDestruct (lstate_lb_valid with "Hlstate_auth Hlstate_lb") as %(? & _).
      iDestruct (big_sepM_lookup with "Hbacks") as "(%v_move & $ & _)".
      { eapply lookup_weaken; done. }
    }
    iFrameSteps.
  Qed.

  Lemma mpmc_queue_2_create_spec ι :
    {{{
      True
    }}}
      mpmc_queue_2_create ()
    {{{ t,
      RET t;
      mpmc_queue_2_inv t ι ∗
      mpmc_queue_2_model t []
    }}}.
  Proof.
  Admitted.

  Lemma mpmc_queue_2_size_spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_size t @ ↑ι
    <<<
      mpmc_queue_2_model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_queue_2_is_empty_spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_is_empty t @ ↑ι
    <<<
      mpmc_queue_2_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
  Admitted.

  #[local] Lemma mpmc_queue_2_finish_spec l γ ι backs i lstatus back :
    back ∈ dom backs →
    {{{
      meta l nroot γ ∗
      inv ι (inv_inner l γ) ∗
      lstate_lb γ backs i lstatus
    }}}
      mpmc_queue_2_finish #back
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hback %Φ (#Hmeta & #Hinv & #Hlstate_lb) HΦ".

    iMod (lstate_lb_header with "Hinv Hlstate_lb") as "#Hback_header"; first done.
    apply elem_of_dom in Hback as (j & Hbacks_lookup).

    wp_rec. wp_match.

    iInv "Hinv" as "(:inv_inner =')".
    iDestruct (lstate_lb_valid with "Hlstate_auth Hlstate_lb") as %(? & _).
    iDestruct (big_sepM_lookup_acc with "Hbacks") as "((%v_move & (_ & Hback_index & Hback_move)) & Hbacks)".
    { eapply lookup_weaken; done. }
    wp_store.
    iDestruct ("Hbacks" with "[$Hback_index Hback_move]") as "Hbacks"; first iSteps.
    iFrameSteps.
  Qed.

  Lemma mpmc_queue_2_push_back_spec t ι v :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_push_back t v @ ↑ι
    <<<
      mpmc_queue_2_model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_queue_2_push_front_spec t ι v :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_push_front t v @ ↑ι
    <<<
      mpmc_queue_2_model t (v :: vs)
    | RET ();
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_queue_2_pop_spec t ι :
    <<<
      mpmc_queue_2_inv t ι
    | ∀∀ vs,
      mpmc_queue_2_model t vs
    >>>
      mpmc_queue_2_pop t @ ↑ι
    <<<
      mpmc_queue_2_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
  Admitted.
End mpmc_queue_2_G.

#[global] Opaque mpmc_queue_2_create.
#[global] Opaque mpmc_queue_2_push_back.
#[global] Opaque mpmc_queue_2_pop.

#[global] Opaque mpmc_queue_2_inv.
#[global] Opaque mpmc_queue_2_model.
