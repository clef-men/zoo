From iris.algebra Require Import
  lib.frac_auth
  numbers
  auth.
From iris.bi Require Import
  bi
  telescopes.

From diaframe Require Import
  proofmode_base
  steps.pure_solver
  lib.persistently
  lib.intuitionistically.

From zoo Require Import
  prelude.
From zoo.iris Require Import
  proofmode.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  wp.
From zoo Require Import
  options.

Section instances.
  Context `{zoo_G : !ZooG Σ}.

  Section mergable.
    #[global] Instance mergable_consume_pointsto_persist l v1 v2 :
      MergableConsume
        (l ↦□ v1)%I
        true
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦□ v2)) $
          TCEq Pout (l ↦□ v1 ∗ ⌜v1 = v2⌝)
        )%I
    | 40.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStep as "Hl1 Hl2".
      iCombine "Hl1 Hl2" gives %[_ ->].
      iSteps.
    Qed.

    #[global] Instance mergable_consume_pointsto_own q1 q2 q l v1 v2 :
      MergableConsume
        (l ↦{#q1} v1)%I
        true
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{#q2} v2)) $
          TCAnd (proofmode_classes.IsOp (A := fracR) q q1 q2) $
          TCEq Pout (l ↦{#q} v1 ∗ ⌜v1 = v2⌝ ∗ ⌜q ≤ 1⌝%Qp)
        )%I
    | 30.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> [+ ->]].
      rewrite bi.intuitionistically_if_elim => Hq.
      iStep as "Hl1 Hl2".
      iCombine "Hl1 Hl2" as "H" gives %[Hl ->].
      rewrite dfrac_op_own Hq.
      rewrite dfrac_valid_own in Hl.
      iSteps.
    Qed.

    #[global] Instance mergable_persist_pointsto_dfrac_own q1 dq2 l v1 v2 :
      MergablePersist
        (l ↦{#q1} v1)%I
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{dq2} v2)) $
          TCEq Pout ⌜v1 = v2 ∧ q1 < 1⌝%Qp
        )%I
    | 50.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStep as "Hl1 Hl2".
      iCombine "Hl1 Hl2" gives %[?%dfrac_valid_own_l ->].
      iSteps.
    Qed.

    #[global] Instance mergable_persist_pointsto_dfrac_own2 q1 dq2 l v1 v2 :
      MergablePersist
        (l ↦{dq2} v1)%I
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{#q1} v2)) $
          TCEq Pout ⌜v1 = v2 ∧ q1 < 1⌝%Qp
        )%I
    | 50.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iSteps.
    Qed.

    #[global] Instance mergable_persist_pointsto_last_resort dq1 dq2 l v1 v2 :
      MergablePersist
        (l ↦{dq1} v1)%I
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{dq2} v2)) $
          TCEq Pout ⌜v1 = v2⌝
        )%I
    | 99.
    Proof.
      rewrite /MergableConsume => p Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iStep as "Hl1 Hl2".
      iCombine "Hl1 Hl2" gives %[_ ->].
      iSteps.
    Qed.

    #[global] Instance proph_exclusive pid prophs prophs' :
      MergableConsume
        (prophet_model pid prophs)
        true
        (λ b Pin Pout,
          TCAnd (TCEq Pin (prophet_model pid prophs')) $
          TCEq Pout (False%I)
        ).
    Proof.
      move => b Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      iIntros "[Hp1 Hp2]". by iApply (prophet_model_exclusive with "[$]").
    Qed.

    #[global] Instance prophs_are_ne pid prophs pid' prophs' :
      MergablePersist
      (prophet_model pid prophs)
      (λ b Pin Pout,
        TCAnd (TCEq Pin (prophet_model pid' prophs')) $
        TCEq Pout ⌜pid ≠ pid'⌝
      )%I.
    Proof.
      move => b Pin Pout [-> ->].
      rewrite bi.intuitionistically_if_elim.
      destruct (decide (pid = pid')) as [-> | Hneq]; iSteps.
    Qed.
  End mergable.

  Section biabds_pointsto.
    #[global] Instance pointsto_val_may_need_more (l : location) (v1 v2 : val) (q1 q2 : Qp) mq q :
      FracSub q2 q1 mq →
      TCEq mq (Some q) →
      HINT l ↦{#q1} v1 ✱ [v'; ⌜v1 = v2⌝ ∗ l ↦{#q} v'] ⊫ [id]; l ↦{#q2} v2 ✱ [⌜v1 = v2⌝ ∗ ⌜v' = v1⌝]
    | 55.
    Proof.
      rewrite /FracSub => <- -> v' /=.
      iSteps.
    Qed.

    #[global] Instance pointsto_val_have_enough (l : location) (v1 v2 : val) (q1 q2 : Qp) mq :
      FracSub q1 q2 mq →
      HINT l ↦{#q1} v1 ✱ [- ; ⌜v1 = v2⌝] ⊫ [id]; l ↦{#q2}v2 ✱ [⌜v1 = v2⌝ ∗ match mq with | Some q => l ↦{#q} v1 | _ => True end]
    | 54.
    Proof.
      rewrite /= /FracSub => <-.
      destruct mq; iSteps as "Hl".
      iDestruct "Hl" as "[Hl Hl']".
      iSteps.
    Qed.

    #[global] Instance as_persistent_pointsto p l q v :
      HINT □⟨p⟩ l ↦{q} v ✱ [- ; emp] ⊫ [bupd]; l ↦□ v ✱ [l ↦□ v]
    | 100.
    Proof.
      iIntros "Hl" => /=.
      rewrite /= right_id bi.intuitionistically_if_elim.
      iMod (pointsto_persist with "Hl") as "#Hl".
      iSteps.
    Qed.
  End biabds_pointsto.

  Section biabds_pointsto_array.
    Class BaseLoc li lb i :=
      offset_location_eq : li = lb +ₗ i.
    #[global] Hint Mode BaseLoc + - - : typeclass_instances.

    #[global] Instance base_location_default l :
      BaseLoc l l 0 | 50.
    Proof.
      unfold BaseLoc. by rewrite location_add_0.
    Qed.

    #[global] Instance base_location_add li j1 lb j2 :
      BaseLoc li lb j2 →
      BaseLoc (li +ₗ j1) lb (j2 + j1)
    | 30.
    Proof.
      unfold BaseLoc => ->. by rewrite location_add_assoc.
    Qed.

    Class ComputeOffsetLoc lb j lo :=
      compute_offset_location_eq : lb +ₗ j = lo.
    #[global] Hint Mode ComputeOffsetLoc + + - : typeclass_instances.

    Lemma compute_offset_from_base_location li ji lb i :
      BaseLoc li lb i →
      ComputeOffsetLoc li ji (lb +ₗ (i + ji)).
    Proof.
      rewrite /BaseLoc /ComputeOffsetLoc -location_add_assoc => -> //.
    Qed.

    #[global] Instance compute_offset_location_default0 l :
      ComputeOffsetLoc l 0 l
    | 10.
    Proof.
      rewrite /ComputeOffsetLoc location_add_0 //.
    Qed.

    #[global] Instance compute_offset_location_default1 l i :
      ComputeOffsetLoc l i (l +ₗ i)
    | 100.
    Proof.
      done.
    Qed.

    #[global] Instance compute_offset_location_default2 l j i :
      ComputeOffsetLoc (l +ₗ j) i (l +ₗ (j + i))
    | 50.
    Proof.
      rewrite /ComputeOffsetLoc -location_add_assoc //.
    Qed.

    #[global] Instance compute_offset_location_offset_add l i j lo1 lo2 :
      ComputeOffsetLoc l i lo1 →
      ComputeOffsetLoc lo1 j lo2 →
      ComputeOffsetLoc l (i + j) lo2
    | 30.
    Proof.
      rewrite /ComputeOffsetLoc -location_add_assoc => <- <- //.
    Qed.

    Class SharedBaseLoc l1 l2 lb j1 j2 := {
      shared_base_location_eq1 : BaseLoc l1 lb j1;
      shared_base_location_eq2 : BaseLoc l2 lb j2
    }.
    #[global] Hint Mode SharedBaseLoc + + - - - : typeclass_instances.

    #[global] Instance shared_base_location_gen l1 lb1 j1 l2 lb2 j2 :
      TCNoBackTrack (BaseLoc l1 lb1 j1) →
      TCNoBackTrack (BaseLoc l2 lb2 j2) →
      TCEq lb1 lb2 →
      SharedBaseLoc l1 l2 lb1 j1 j2.
    Proof.
      move => ? ? /TCEq_eq; split; subst; eapply tc_no_backtrack.
    Qed.

    (* #[global] Instance array_pointsto_index l1 vs l2 v lb j1 j2 lo q : *)
    (*   SharedBaseLoc l1 l2 lb j1 j2 → *)
    (*   SolveSepSideCondition (j1 ≤ j2 < j1 + length vs)%Z → *)
    (*   ComputeOffsetLoc lb (Z.succ j2) lo → *)
    (*   HINT l1 ↦∗{q} vs ✱ [- ; ⌜vs !! (Z.to_nat (j2 - j1)) = Some v⌝ ] ⊫ [id]; *)
    (*        l2 ↦{q} v   ✱ [ l1 ↦∗{q} take (Z.to_nat (j2 - j1)) vs ∗ *)
    (*                        lo ↦∗{q} drop (S (Z.to_nat (j2 - j1))) vs ∗ *)
    (*                        ⌜vs !! (Z.to_nat (j2 - j1)) = Some v⌝]. *)
    (* Proof. *)
    (*   move => [-> ->] [? ?] <-. *)
    (*   iStep as (Hvs) "Hlvs". *)
    (*   rewrite -{1}(take_drop_middle _ _ _ Hvs). *)
    (*   rewrite array_app array_cons. *)
    (*   iDecompose "Hlvs" as "Hlhd Hlv Hltl". *)
    (*   rewrite length_take min_l; last lia. *)
    (*   rewrite !location_add_assoc. replace (j1 + Z.to_nat (j2 - j1))%Z with j2 by lia. *)
    (*   iSteps. *)
    (* Qed. *)

    (* Lemma array_pointsto_head l v vs q l' : *)
    (*   ComputeOffsetLoc l 1 l' → *)
    (*   HINT l ↦∗{q} vs ✱ [- ; ⌜vs !! 0 = Some v⌝] ⊫ [id]; l ↦{q} v ✱ [l' ↦∗{q} tail vs ∗ ⌜vs !! 0 = Some v⌝]. *)
    (* Proof. *)
    (*   rewrite /= /ComputeOffsetLoc => <-. *)
    (*   iStep as (Hvs) "Hl". destruct vs; first naive_solver. *)
    (*   iSteps. *)
    (* Qed. *)

    (* #[global] Instance head_pointsto_array_better l1 l2 lb j1 j2 v vs q l' : *)
    (*   SharedBaseLoc l1 l2 lb j1 j2 → *)
    (*   SolveSepSideCondition (j1 = j2) → (1* i.e., l1 and l2 are aliases up to lia *1) *)
    (*   ComputeOffsetLoc lb (Z.succ j1) l' → *)
    (*   HINT l1 ↦{q} v ✱ [- ; ⌜vs !! 0 = Some v⌝ ∗ l' ↦∗{q} tail vs] ⊫ [id]; l2 ↦∗{q} vs ✱ [⌜vs !! 0 = Some v⌝]. *)
    (* Proof. *)
    (*   move => [-> ->] -> /= <-. *)
    (*   iIntros "(H & % & Htl) /=". *)
    (*   destruct vs => //. *)
    (*   case: H => ->. *)
    (*   rewrite array_cons location_add_assoc. *)
    (*   iSteps. *)
    (* Qed. *)

    (* Lemma head_pointsto_array l v vs q l' : *)
    (*   ComputeOffsetLoc l 1 l' → *)
    (*   HINT l ↦{q} v ✱ [- ; ⌜vs !! 0 = Some v⌝ ∗ l' ↦∗{q} tail vs] ⊫ [id]; l ↦∗{q} vs ✱ [emp]. *)
    (* Proof. *)
    (*   rewrite /= => <-. *)
    (*   iSteps. *)
    (* Qed. *)

    (* Lemma array_pointsto_head_offset l v vs q i l': *)
    (*   SolveSepSideCondition (0 ≤ i < length vs)%Z → *)
    (*   ComputeOffsetLoc l (Z.succ i) l' → *)
    (*   HINT l ↦∗{q} vs ✱ [ - ; ⌜vs !! Z.to_nat i = Some v⌝] ⊫ [id]; (l +ₗ i) ↦{q} v ✱ [ *)
    (*        (l ↦∗{q} take (Z.to_nat i) vs) ∗ ⌜vs !! Z.to_nat i = Some v⌝ ∗ (l' ↦∗{q} drop (S $ Z.to_nat i) vs)]. *)
    (* Proof. *)
    (*   rewrite /SolveSepSideCondition /= => Hi <-. *)
    (*   iStep as (Hvs) "Hl". iStep. replace (0 + i - 0)%Z with i by lia. iSteps. *)
    (*   Unshelve. replace (0 + i - 0)%Z with i by lia. iSteps. *)
    (* Qed. *)

    (* #[global] Instance empty_array_solve l q : *)
    (*   HINT ε₁ ✱ [- ; emp] ⊫ [id]; l ↦∗{q} [] ✱ [emp]. *)
    (* Proof. *)
    (*   iSteps. rewrite array_nil. iSteps. *)
    (* Qed. *)

    (* #[global] Instance array_from_overlapping_array vs1 vs2 l1 l2 q lb j1 j2 l2t l1t : *)
    (*   SharedBaseLoc l1 l2 lb j1 j2 → *)
    (*   let jub := ((j1 + length vs1) `min` (j2 + length vs2))%Z in *)
    (*   let jlb := (j1 `max` j2)%Z in *)
    (*   SolveSepSideCondition (jlb < jub)%Z → *)
    (*   ComputeOffsetLoc lb (j1 + length vs1) l2t → *)
    (*   ComputeOffsetLoc lb (j2 + length vs2) l1t → *)
    (*   HINT l1 ↦∗{q} vs1 ✱ [- ; *)
    (*           ⌜take (Z.to_nat (jub - jlb)) (drop (Z.to_nat (j2 - j1)) vs1) = take (Z.to_nat (jub - jlb)) (drop (Z.to_nat (j1 - j2)) vs2)⌝ ∗ *)
    (*           l2 ↦∗{q} (take (Z.to_nat (j1 - j2)) vs2) ∗ *)
    (*           l2t ↦∗{q} (drop (Z.to_nat (j1 + length vs1 - j2)) vs2) *)
    (*        ]  ⊫ [id]; *)
    (*        l2 ↦∗{q} vs2 ✱ [ *)
    (*           l1 ↦∗{q} (take (Z.to_nat (j2 - j1)) vs1) ∗ *)
    (*           l1t ↦∗{q} (drop (Z.to_nat (j2 + length vs2 - j1)) vs1) *)
    (*        ] | 51. *)
    (* Proof. *)
    (*   move => [-> ->] jub jlb. *)
    (*   rewrite /SolveSepSideCondition => Hjs <- <-. *)
    (*   iStep as (Hvs) "Hj1 Hl2h Hl2t". *)
    (*   rewrite -{3}(take_drop (Z.to_nat (j1 - j2)) vs2) array_app -assoc location_add_assoc. *)
    (*   iStep. rewrite -{1}(take_drop (Z.to_nat (j2 - j1)) vs1) array_app location_add_assoc. *)
    (*   iDestruct "Hj1" as "[$ Hjtl]". *)
    (*   rewrite -{1}(take_drop (Z.to_nat (jub - jlb)) (drop _ vs1)) array_app location_add_assoc {1}Hvs. *)
    (*   iDestruct "Hjtl" as "[Hjtl1 Hjtl2]". *)
    (*   rewrite -{2}(take_drop (Z.to_nat (jub - jlb)) (drop (Z.to_nat (j1 - j2)) vs2)) array_app location_add_assoc. *)
    (*   rewrite -bi.sep_assoc. *)
    (*   rewrite !length_take !length_drop. *)
    (*   replace ( (j1 + (Z.to_nat (j2 - j1) `min` length vs1)%nat))%Z with (j2 + (Z.to_nat (j1 - j2) `min` length vs2)%nat)%Z by lia. *)
    (*   iFrame "Hjtl1". *)
    (*   rewrite !drop_drop. (1* and now comes the part with non-trivial integer arithmetic *1) *)
    (*   destruct (decide (length vs1 ≤ j2 + length vs2 - j1)%Z) as [Hnotail1 | Htail1]; last *)
    (*     destruct (decide (length vs2 ≤ j1 + length vs1 - j2)%Z) as [Hnotail2 | Htail2]. *)
    (*   - rewrite drop_ge; last lia. *)
    (*     rewrite array_nil. *)
    (*     rewrite (drop_ge vs1); last lia. *)
    (*     rewrite array_nil right_id. *)
    (*     replace ((j2 + (Z.to_nat (j1 - j2) `min` length vs2)%nat + (Z.to_nat (jub - jlb) `min` (length vs2 - Z.to_nat (j1 - j2)))%nat))%Z with *)
    (*       (j1 + length vs1)%Z by lia. *)
    (*     replace (Z.to_nat (j1 + length vs1 - j2)) with (Z.to_nat (j1 - j2) + Z.to_nat (jub - jlb)) by lia. *)
    (*     iSteps. *)
    (*   - rewrite (drop_ge vs2); last lia. rewrite array_nil. *)
    (*     rewrite (drop_ge vs2); last lia. rewrite array_nil. *)
    (*     replace ((j2 + (Z.to_nat (j1 - j2) `min` length vs2)%nat + (Z.to_nat (jub - jlb) `min` (length vs1 - Z.to_nat (j2 - j1)))%nat))%Z with *)
    (*       (j2 + length vs2)%Z by lia. *)
    (*     replace (Z.to_nat (j2 + length vs2 - j1)) with (Z.to_nat (j2 - j1) + Z.to_nat (jub - jlb)) by lia. *)
    (*     iSteps. *)
    (*   - assert (j1 = j2) by lia; subst. *)
    (*     assert (length vs1 = length vs2) as Hlen by lia. rewrite !Hlen. *)
    (*     rewrite drop_ge; last lia. *)
    (*     rewrite drop_ge; last lia. *)
    (*     rewrite drop_ge; last lia. *)
    (*     rewrite drop_ge; last lia. *)
    (*     rewrite !array_nil. iSteps. *)
    (* Qed. *)

    (* Lemma array_from_shorter vs1 vs2 l l' q : *)
    (*   SolveSepSideCondition (0 < length vs1 ≤ length vs2) → *)
    (*   ComputeOffsetLoc l (length vs1) l' → *)
    (*   HINT l ↦∗{q} vs1 ✱ [- ; ⌜take (length vs1) vs2 = vs1⌝ ∗ l' ↦∗{q} (list.drop (length vs1) vs2) ] ⊫ [id]; *)
    (*        l ↦∗{q} vs2 ✱ [emp]. *)
    (* Proof. *)
    (*   rewrite /SolveSepSideCondition => Hl <- /=. *)
    (*   iStep as (Hvs) "Hl Hvs". enough (0 < length vs1). *)
    (*   iStep. replace (Z.to_nat (0 + length vs1 - 0)) with (length vs1) by lia. *)
    (*   iSteps. lia. *)
    (*   Unshelve. rewrite !drop_0. *)
    (*   rewrite !Z.max_l; last lia. *)
    (*   rewrite Z.min_l; last lia. *)
    (*   replace (Z.to_nat (0 + length vs1 - 0)) with (length vs1) by lia. *)
    (*   rewrite firstn_all. iSteps. *)
    (* Qed. *)
  End biabds_pointsto_array.

  Section abds.
    #[global] Instance fork_abduct e (Φ : val → iPropI Σ) E :
      HINT1 ε₁ ✱ [▷ Φ ()%V ∗ ▷ WP e @ ⊤ {{ _, True }}] ⊫ [id]; WP Fork e @ E {{ Φ }}.
    Proof.
      iSteps as "HΦ HWP". iApply (wp_fork with "HWP"). iSteps.
    Qed.
  End abds.
End instances.

Section side_condition_lemmas.
  Lemma val_neq_lit_neq lit1 lit2 :
    lit1 ≠ lit2 →
    ValLit lit1 ≠ ValLit lit2.
  Proof.
    congruence.
  Qed.

  Lemma lit_neq_Z_neq n1 n2 :
    n1 ≠ n2 →
    LitInt n1 ≠ LitInt n2.
  Proof.
    congruence.
  Qed.

  Lemma lit_neq_bool_neq b1 b2 :
    b1 ≠ b2 →
    LitBool b1 ≠ LitBool b2.
  Proof.
    congruence.
  Qed.

  Lemma val_block_neq bid1 tag1 vs1 bid2 tag2 vs2 :
    bid1 ≠ bid2 →
    tag1 ≠ tag2 →
    vs1 ≠ vs2 →
    ValBlock bid1 tag1 vs1 ≠ ValBlock bid2 tag2 vs2.
  Proof.
    congruence.
  Qed.

  #[global] Instance simplify_lit_location_neq l1 l2 :
    SimplifyPureHypSafe
      (ValLit l1 ≠ ValLit l2)
      (l1 ≠ l2).
  Proof.
    split; congruence.
  Qed.

  #[global] Instance simplify_lit_int_neq n1 n2 :
    SimplifyPureHypSafe
      (LitInt n1 ≠ LitInt n2)
      (n1 ≠ n2).
  Proof.
    split; congruence.
  Qed.

  #[global] Instance simplify_lit_bool_neq b1 b2 :
    SimplifyPureHypSafe
      (LitBool b1 ≠ LitBool b2)
      (b1 ≠ b2).
  Proof.
    split; congruence.
  Qed.

  #[global] Instance simplify_block_neq bid1 tag1 vs1 bid2 tag2 vs2 :
    SimplifyPureHypSafe
      (ValBlock bid1 tag1 vs1 ≠ ValBlock bid2 tag2 vs2)
      (bid1 ≠ bid2 ∨ tag1 ≠ tag2 ∨ vs1 ≠ vs2).
  Proof.
    split.
    - rewrite -!not_and_l. naive_solver.
    - naive_solver.
  Qed.
End side_condition_lemmas.

Ltac solveValEq :=
  (progress f_equal); trySolvePureEq.

Ltac trySolvePureEqAdd1 :=
  lazymatch goal with
  | |- @eq ?T ?l ?r =>
      match constr:((T, l)) with
      | (val, _) =>
          solveValEq
      | (literal, _) =>
          solveValEq
      end
  end.

#[global] Hint Extern 4 (
  _ = _
) =>
  trySolvePureEqAdd1
: solve_pure_eq_add.

Ltac trySolvePureAdd1 :=
  match goal with
  | |- ValLit ?lit1 ≠ ValLit ?lit2 =>
      assert_fails (has_evar lit1);
      assert_fails (has_evar lit2);
      eapply val_neq_lit_neq; solve [pure_solver.trySolvePure]
  | |- LitInt ?n1 ≠ LitInt ?n2 =>
      assert_fails (has_evar n1);
      assert_fails (has_evar n2);
      eapply lit_neq_Z_neq; solve [pure_solver.trySolvePure]
  | |- LitBool ?b1 ≠ LitBool ?b2 =>
      assert_fails (has_evar b1);
      assert_fails (has_evar b2);
      eapply lit_neq_bool_neq; solve [pure_solver.trySolvePure]
  | |- ValBlock ?bid1 ?tag1 ?vs1 ≠ ValBlock ?bid2 ?tag2 ?vs2 =>
      assert_fails (has_evar bid1);
      assert_fails (has_evar bid2);
      assert_fails (has_evar tag1);
      assert_fails (has_evar tag2);
      assert_fails (has_evar vs1);
      assert_fails (has_evar vs2);
      eapply val_block_neq; solve [pure_solver.trySolvePure]
  end.

#[global] Hint Extern 4 =>
  trySolvePureAdd1
: solve_pure_add.

#[global] Hint Extern 4 (
  length _ ≤ length _
) =>
  simpl;
  solve [pure_solver.trySolvePure]
: solve_pure_add.
