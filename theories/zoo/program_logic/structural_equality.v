From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  wp.
From zoo.diaframe Require Import
  diaframe.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types tag : nat.
Implicit Types n : Z.
Implicit Types l : location.
Implicit Types gen : generativity.
Implicit Types v w : val.
Implicit Types vs : list val.
Implicit Types lv : lowval.

#[local] Definition __zoo_recs := (
  recs: "structeq" "v1" "v2" =>
    if: IsImmediate "v1" then
      if: IsImmediate "v2" then
        "v1" == "v2"
      else
        #false
    else if: IsImmediate "v2" then
      #false
    else (
      GetTag "v1" == GetTag "v2" and
      let: "sz" := GetSize "v1" in
      "sz" == GetSize "v2" and
      "structeq_aux" "v1" "v2" "sz"
    )
  and: "structeq_aux" "v1" "v2" "i" =>
    if: "i" == #0 then
      #true
    else
      let: "i" := "i" - #1 in
      "structeq" (Load "v1" "i") (Load "v2" "i") and
      "structeq_aux" "v1" "v2" "i"
)%zoo_recs.
Definition structeq :=
  ValRecs 0 __zoo_recs.
#[local] Definition structeq_aux :=
  ValRecs 1 __zoo_recs.
#[global] Instance :
  AsValRecs' structeq 0 __zoo_recs [
    structeq ;
    structeq_aux
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' structeq_aux 1 __zoo_recs [
    structeq ;
    structeq_aux
  ].
Proof.
  done.
Qed.

Notation "e1 = e2" := (
  App (App (Val structeq) e1%E) e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 ≠ e2" := (
  Unop UnopNeg (App (App (Val structeq) e1%E) e2%E)
)(at level 70,
  no associativity
) : expr_scope.

Record structeq_field := StructeqField {
  structeq_field_dfrac : dfrac ;
  structeq_field_val : val ;
}.
Add Printing Constructor structeq_field.
Implicit Types fld : structeq_field.

#[global] Instance structeq_field_inhabited : Inhabited structeq_field :=
  populate
    {|structeq_field_dfrac := inhabitant ;
      structeq_field_val := inhabitant ;
    |}.

Record structeq_block := StructeqBlock {
  structeq_block_tag : nat ;
  structeq_block_fields : list structeq_field ;
}.
Add Printing Constructor structeq_block.
Implicit Types blk : structeq_block.
Implicit Types footprint : gmap location structeq_block.

#[global] Instance structeq_block_inhabited : Inhabited structeq_block :=
  populate
    {|structeq_block_tag := inhabitant ;
      structeq_block_fields := inhabitant ;
    |}.

Fixpoint val_traversable footprint v :=
  match v with
  | ValBool _
  | ValInt _ =>
      True
  | ValLoc l =>
      l ∈ dom footprint
  | ValBlock _ _ vs =>
      Forall' (val_traversable footprint) vs
  | _ =>
      False
  end.
#[global] Arguments val_traversable _ !_ / : assert.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition structeq_footprint footprint : iProp Σ :=
    [∗ map] l ↦ blk ∈ footprint,
      l ↦ₕ Header blk.(structeq_block_tag) (length blk.(structeq_block_fields)) ∗
      [∗ list] i ↦ fld ∈ blk.(structeq_block_fields),
        (l +ₗ i) ↦{fld.(structeq_field_dfrac)} fld.(structeq_field_val) ∗
        ⌜val_traversable footprint fld.(structeq_field_val)⌝.

  Lemma structeq_footprint_empty :
    ⊢ structeq_footprint ∅.
  Proof.
    rewrite /structeq_footprint big_sepM_empty //.
  Qed.

  Lemma structeq_footprint_header {footprint} l blk :
    footprint !! l = Some blk →
    structeq_footprint footprint ⊢
    l ↦ₕ Header blk.(structeq_block_tag) (length blk.(structeq_block_fields)).
  Proof.
    iIntros "%Hlookup Hfootprint".
    iDestruct (big_sepM_lookup with "Hfootprint") as "($ & _)"; first done.
  Qed.

  Lemma structeq_footprint_lookup {footprint} l blk (i : nat) fld :
    footprint !! l = Some blk →
    blk.(structeq_block_fields) !! i = Some fld →
    structeq_footprint footprint ⊢
      (l +ₗ i) ↦{fld.(structeq_field_dfrac)} fld.(structeq_field_val) ∗
      ⌜val_traversable footprint fld.(structeq_field_val)⌝ ∗
      ( (l +ₗ i) ↦{fld.(structeq_field_dfrac)} fld.(structeq_field_val) -∗
        structeq_footprint footprint
      ).
  Proof.
    iIntros "%Hfootprint_lookup %Hfields_lookup Hfootprint".
    iDestruct (big_sepM_lookup_acc with "Hfootprint") as "((#Hl_header & Hblk) & Hfootprint)"; first done.
    iDestruct (big_sepL_lookup_acc with "Hblk") as "(HHfld & Hblk)"; first done.
    iSteps.
  Qed.
  Lemma structeq_footprint_lookup' {footprint} l blk i :
    footprint !! l = Some blk →
    i < length blk.(structeq_block_fields) →
    structeq_footprint footprint ⊢
      ∃ fld,
      ⌜blk.(structeq_block_fields) !! i = Some fld⌝ ∗
      (l +ₗ i) ↦{fld.(structeq_field_dfrac)} fld.(structeq_field_val) ∗
      ⌜val_traversable footprint fld.(structeq_field_val)⌝ ∗
      ( (l +ₗ i) ↦{fld.(structeq_field_dfrac)} fld.(structeq_field_val) -∗
        structeq_footprint footprint
      ).
  Proof.
    iIntros "%Hfootprint_lookup %Hi Hfootprint".
    destruct (lookup_lt_is_Some_2 blk.(structeq_block_fields) i) as (fld & Hfields_lookup); first done.
    iExists fld. iStep.
    iApply (structeq_footprint_lookup with "Hfootprint"); done.
  Qed.

  Lemma structeq_footprint_wp_tag {footprint} l blk :
    footprint !! l = Some blk →
    {{{
      structeq_footprint footprint
    }}}
      GetTag #l
    {{{
      RET #(encode_tag blk.(structeq_block_tag));
      structeq_footprint footprint
    }}}.
  Proof.
    iIntros "%Hlookup %Φ Hfootprint HΦ".

    iDestruct (structeq_footprint_header with "Hfootprint") as "#Hl_header"; first done.
    iSteps.
  Qed.
  Lemma structeq_footprint_wp_size {footprint} l blk :
    footprint !! l = Some blk →
    {{{
      structeq_footprint footprint
    }}}
      GetSize #l
    {{{
      RET #(length blk.(structeq_block_fields));
      structeq_footprint footprint
    }}}.
  Proof.
    iIntros "%Hlookup %Φ Hfootprint HΦ".

    iDestruct (structeq_footprint_header with "Hfootprint") as "#Hl_header"; first done.
    iSteps.
  Qed.

  Lemma structeq_footprint_wp_load {footprint} l blk (i : nat) fld :
    footprint !! l = Some blk →
    blk.(structeq_block_fields) !! i = Some fld →
    {{{
      structeq_footprint footprint
    }}}
      Load #l #i
    {{{
      RET fld.(structeq_field_val);
      ⌜val_traversable footprint fld.(structeq_field_val)⌝ ∗
      structeq_footprint footprint
    }}}.
  Proof.
    iIntros "%Hfootprint_lookup %Hfields_lookup %Φ Hfootprint HΦ".

    iDestruct (structeq_footprint_lookup with "Hfootprint") as "(Hl & %Htraversable & Hfootprint)"; [done.. |].
    iSteps.
  Qed.
  Lemma structeq_footprint_wp_load' {footprint} l blk i :
    footprint !! l = Some blk →
    i < length blk.(structeq_block_fields) →
    {{{
      structeq_footprint footprint
    }}}
      Load #l #i
    {{{ fld,
      RET fld.(structeq_field_val);
      ⌜blk.(structeq_block_fields) !! i = Some fld⌝ ∗
      ⌜val_traversable footprint fld.(structeq_field_val)⌝ ∗
      structeq_footprint footprint
    }}}.
  Proof.
    iIntros "%Hfootprint_lookup %Hi %Φ Hfootprint HΦ".

    iDestruct (structeq_footprint_lookup' with "Hfootprint") as "(%fld & %Hfields_lookup & Hl & %Htraversable & Hfootprint)"; [done.. |].
    iSteps.
  Qed.
End zoo_G.

Fixpoint val_reachable footprint src path dst :=
  match path with
  | [] =>
      src = dst
  | i :: path =>
      match src with
      | ValLoc l =>
          match footprint !! l with
          | None =>
              False
          | Some blk =>
              match blk.(structeq_block_fields) !! i with
              | None =>
                  False
              | Some fld =>
                  val_reachable footprint fld.(structeq_field_val) path dst
              end
          end
      | ValBlock _ _ vs =>
          match vs !! i with
          | None =>
              False
          | Some src =>
              val_reachable footprint src path dst
          end
      | _ =>
          False
      end
  end.
#[global] Arguments val_reachable _ !_ !_ / _ : assert.

#[global] Instance val_reachable_dec footprint src path dst :
  Decision (val_reachable footprint src path dst).
Proof.
  move: src path.
  refine (
    fix go src path {struct path} :=
      match path with
      | [] =>
          cast_if (decide (src = dst))
      | i :: path =>
          match src with
          | ValLoc l =>
              (match footprint !! l as x return _ = x → _ with
              | None => λ Hfootprint_lookup,
                  right _
              | Some blk => λ Hfootprint_lookup,
                  (match blk.(structeq_block_fields) !! i as x return _ = x → _ with
                  | None => λ Hfields_lookup,
                      right _
                  | Some fld => λ Hfields_lookup,
                      cast_if (go fld.(structeq_field_val) path)
                  end) (eq_refl (blk.(structeq_block_fields) !! i))
              end) (eq_refl (footprint !! l))
          | ValBlock _ _ vs =>
              (match vs !! i as x return _ = x → _ with
              | None => λ Hvs_lookup,
                  right _
              | Some src => λ Hvs_lookup,
                  cast_if (go src path)
              end) (eq_refl (vs !! i))
          | _ =>
              right _
          end
      end
  ).
  all:
    abstract (
      rewrite /= ?Hfootprint_lookup ?Hfields_lookup ?Hvs_lookup;
      congruence
    ).
Defined.

Definition lowval_compatible footprint lv1 lv2 :=
  match lv1 with
  | LowvalLit lit1 =>
      match lit1 with
      | LowlitLoc l1 =>
          match lv2 with
          | LowvalLoc l2 =>
              let blk1 := footprint !!! l1 in
              let blk2 := footprint !!! l2 in
              blk1.(structeq_block_tag) ≟ blk2.(structeq_block_tag) &&
              length blk1.(structeq_block_fields) ≟ length blk2.(structeq_block_fields)
          | LowvalBlock _ tag2 vs2 _ =>
              let blk1 := footprint !!! l1 in
              blk1.(structeq_block_tag) ≟ tag2 &&
              length blk1.(structeq_block_fields) ≟ length vs2
          | _ =>
              false
          end
      | _ =>
          bool_decide (lv2 = LowvalLit lit1)
      end
  | LowvalRecs =>
      bool_decide (lv2 = LowvalRecs)
  | LowvalBlock _ tag1 vs1 _ =>
      match lv2 with
      | LowvalLoc l2 =>
          let blk2 := footprint !!! l2 in
          tag1 ≟ blk2.(structeq_block_tag) &&
          length vs1 ≟ length blk2.(structeq_block_fields)
      | LowvalBlock _ tag2 vs2 _ =>
          tag1 ≟ tag2 &&
          length vs1 ≟ length vs2
      | _ =>
          false
      end
  end.
#[global] Arguments lowval_compatible _ !_ !_ / : assert.

Definition val_compatible footprint v1 v2 :=
  lowval_compatible footprint (val_to_low v1) (val_to_low v2).

Definition val_structeq footprint v1 v2 :=
  ∀ path v1' v2',
  val_reachable footprint v1 path v1' →
  val_reachable footprint v2 path v2' →
  val_compatible footprint v1' v2' = true.

Definition val_structneq footprint v1 v2 :=
  ∃ path v1' v2',
  val_reachable footprint v1 path v1' ∧
  val_reachable footprint v2 path v2' ∧
  val_compatible footprint v1' v2' = false.

Lemma val_immediate_structeq footprint v1 v2 :
  val_immediate v1 →
  val_immediate v2 →
  v1 ≈ v2 →
  val_structeq footprint v1 v2.
Proof.
  intros Himmediate1 Himmediate2 Hsimilar.
  intros path v1_ v2_ Hreachable1 Hreachable2.
  destruct v1 as [[b1 | n1 | l1 | |] | | gen1 tag1 []]; try done.
  all: destruct v2 as [[b2 | n2 | l2 | |] | | gen2 tag2 []]; try done.
  all: destruct path; last done.
  all: simplify.
  all: cbn.
  all: rewrite bool_decide_eq_true_2 //.
Qed.
Lemma val_immediate_structneq footprint v1 v2 :
  val_immediate v1 →
  val_immediate v2 →
  v1 ≉ v2 →
  val_structneq footprint v1 v2.
Proof.
  intros Himmediate1 Himmediate2 Hnonsimilar.
  eexists [], v1, v2. split_and!; try done.
  destruct v1 as [[b1 | n1 | l1 | |] | | gen1 tag1 []]; try done.
  all: destruct v2 as [[b2 | n2 | l2 | |] | | gen2 tag2 []]; try done.
  all: cbn.
  all: rewrite bool_decide_eq_false_2 //.
  all: naive_solver.
Qed.

Lemma val_structeq_refl footprint v :
  val_immediate v →
  val_structeq footprint v v.
Proof.
  intros Himmediate.
  apply val_immediate_structeq; done.
Qed.
Lemma val_structeq_refl' footprint v1 v2 :
  v1 = v2 →
  val_immediate v1 →
  val_structeq footprint v1 v2.
Proof.
  intros ->.
  apply val_structeq_refl.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Lemma structeq_spec_aux :
    ⊢ (
      ∀ v1 v2 footprint,
      {{{
        ⌜val_traversable footprint v1⌝ ∗
        ⌜val_traversable footprint v2⌝ ∗
        structeq_footprint footprint
      }}}
        v1 = v2
      {{{ b,
        RET #b;
        ⌜(if b then val_structeq else val_structneq) footprint v1 v2⌝ ∗
        structeq_footprint footprint
      }}}
    ) ∧ (
      ∀ l1 blk1 l2 blk2 footprint i,
      {{{
        ⌜0 ≤ i ≤ length blk1.(structeq_block_fields)⌝%Z ∗
        ⌜footprint !! l1 = Some blk1⌝ ∗
        ⌜footprint !! l2 = Some blk2⌝ ∗
        ⌜blk1.(structeq_block_tag) = blk2.(structeq_block_tag)⌝ ∗
        ⌜length blk1.(structeq_block_fields) = length blk2.(structeq_block_fields)⌝ ∗
        structeq_footprint footprint ∗
        ⌜ ∀ j fld1 fld2,
          blk1.(structeq_block_fields) !! j = Some fld1 →
          blk2.(structeq_block_fields) !! j = Some fld2 →
          ₊i ≤ j →
          val_structeq footprint fld1.(structeq_field_val) fld2.(structeq_field_val)
        ⌝
      }}}
        structeq_aux #l1 #l2 #i
      {{{ b,
        RET #b;
        ⌜(if b then val_structeq else val_structneq) footprint #l1 #l2⌝ ∗
        structeq_footprint footprint
      }}}
    ) ∧ (
      ∀ l1 blk1 gen2 tag2 vs2 footprint i,
      let v2 := ValBlock gen2 tag2 vs2 in
      {{{
        ⌜0 ≤ i ≤ length vs2⌝%Z ∗
        ⌜footprint !! l1 = Some blk1⌝ ∗
        ⌜blk1.(structeq_block_tag) = tag2⌝ ∗
        ⌜length blk1.(structeq_block_fields) = length vs2⌝ ∗
        ⌜0 < length vs2⌝ ∗
        ⌜val_traversable footprint v2⌝ ∗
        structeq_footprint footprint ∗
        ⌜ ∀ j fld1 v2,
          blk1.(structeq_block_fields) !! j = Some fld1 →
          vs2 !! j = Some v2 →
          ₊i ≤ j →
          val_structeq footprint fld1.(structeq_field_val) v2
        ⌝
      }}}
        structeq_aux #l1 v2 #i
      {{{ b,
        RET #b;
        ⌜(if b then val_structeq else val_structneq) footprint #l1 v2⌝ ∗
        structeq_footprint footprint
      }}}
    ) ∧ (
      ∀ gen1 tag1 vs1 l2 blk2 footprint i,
      let v1 := ValBlock gen1 tag1 vs1 in
      {{{
        ⌜0 ≤ i ≤ length vs1⌝%Z ∗
        ⌜footprint !! l2 = Some blk2⌝ ∗
        ⌜tag1 = blk2.(structeq_block_tag)⌝ ∗
        ⌜length vs1 = length blk2.(structeq_block_fields)⌝ ∗
        ⌜0 < length vs1⌝ ∗
        ⌜val_traversable footprint v1⌝ ∗
        structeq_footprint footprint ∗
        ⌜ ∀ j v1 fld2,
          vs1 !! j = Some v1 →
          blk2.(structeq_block_fields) !! j = Some fld2 →
          ₊i ≤ j →
          val_structeq footprint v1 fld2.(structeq_field_val)
        ⌝
      }}}
        structeq_aux v1 #l2 #i
      {{{ b,
        RET #b;
        ⌜(if b then val_structeq else val_structneq) footprint v1 #l2⌝ ∗
        structeq_footprint footprint
      }}}
    ) ∧ (
      ∀ gen1 tag1 vs1 gen2 tag2 vs2 footprint i,
      let v1 := ValBlock gen1 tag1 vs1 in
      let v2 := ValBlock gen2 tag2 vs2 in
      {{{
        ⌜0 ≤ i ≤ length vs1⌝%Z ∗
        ⌜tag1 = tag2⌝ ∗
        ⌜length vs1 = length vs2⌝ ∗
        ⌜0 < length vs1⌝ ∗
        ⌜val_traversable footprint v1⌝ ∗
        ⌜val_traversable footprint v2⌝ ∗
        structeq_footprint footprint ∗
        ⌜ ∀ j v1 v2,
          vs1 !! j = Some v1 →
          vs2 !! j = Some v2 →
          ₊i ≤ j →
          val_structeq footprint v1 v2
        ⌝
      }}}
        structeq_aux v1 v2 #i
      {{{ b,
        RET #b;
        ⌜(if b then val_structeq else val_structneq) footprint v1 v2⌝ ∗
        structeq_footprint footprint
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHstructeq & IHstructeq_aux_loc_loc & IHstructeq_aux_loc_block & IHstructeq_aux_block_loc & IHstructeq_aux_block_block)".
    repeat iSplit.

    { iClear "IHstructeq".
      iIntros "%v1 %v2 %footprint !> %Φ (%Htraversable1 & %Htraversable2 & Hfootprint) HΦ".

      wp_rec. wp_pures.

      all: destruct v1 as [[b1 | n1 | l1 | |] | | gen1 tag1 [| v1 vs1]].
      all: try done.
      all: wp_pures.

      all: destruct v2 as [[b2 | n2 | l2 | |] | | gen2 tag2 [| v2 vs2]].
      all: try done.
      all: wp_pures.

      all:
        try match goal with |- _ _ (WP _ == _ {{ _ }})%I =>
          wp_apply wp_equal_nobranch as (b) "%Hb"
        end.
      Time all:
        try match goal with |- _ _ ?P =>
          tryif eunify P (wp _ _ _ _) then idtac else
            iSteps
        end.
      all:
        try (
          iPureIntro;
          try (eexists [], _, _; done);
          try (
            destruct b; cbn in Hb;
            [ apply val_immediate_structeq; done
            | apply val_immediate_structneq; done
            ]
          );
          try (
            case_bool_decide;
            [ apply val_structeq_refl'; naive_solver
            | apply val_immediate_structneq; [done.. |];
              cbn; naive_solver
            ]
          )
        ).

      - apply elem_of_dom in Htraversable1 as (blk1 & Hfootprint_lookup_1).
        apply elem_of_dom in Htraversable2 as (blk2 & Hfootprint_lookup_2).
        wp_apply (structeq_footprint_wp_tag with "Hfootprint") as "Hfootprint"; first done.
        wp_apply (structeq_footprint_wp_tag with "Hfootprint") as "Hfootprint"; first done.
        wp_pures.
        case_bool_decide; wp_pures.
        + wp_apply (structeq_footprint_wp_size with "Hfootprint") as "Hfootprint"; first done.
          wp_smart_apply (structeq_footprint_wp_size with "Hfootprint") as "Hfootprint"; first done.
          wp_pures.
          case_bool_decide; wp_pures.
          * wp_apply ("IHstructeq_aux_loc_loc" with "[$Hfootprint] HΦ").
            iPureIntro. split_and!; [naive_solver lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and!; try done.
            cbn. erewrite !lookup_total_correct; [| done..].
            rewrite andb_false_iff !beq_spec'. naive_solver.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and!; try done.
          cbn. erewrite !lookup_total_correct; [| done..].
          rewrite andb_false_iff !beq_spec'. naive_solver.

      - apply elem_of_dom in Htraversable1 as (blk1 & Hfootprint_lookup_1).
        wp_apply (structeq_footprint_wp_tag with "Hfootprint") as "Hfootprint"; first done.
        wp_pures.
        case_bool_decide; wp_pures.
        + wp_apply (structeq_footprint_wp_size with "Hfootprint") as "Hfootprint"; first done.
          wp_pures.
          case_bool_decide; wp_pures.
          * wp_apply ("IHstructeq_aux_loc_block" with "[$Hfootprint] HΦ").
            iPureIntro. split_and!; [naive_solver lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. simpl in Hj. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and!; try done.
            cbn. erewrite !lookup_total_correct; [| done..].
            rewrite andb_false_iff !beq_spec'. naive_solver.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and!; try done.
          cbn. erewrite !lookup_total_correct; [| done..].
          rewrite andb_false_iff !beq_spec'. naive_solver.

      - apply elem_of_dom in Htraversable2 as (blk2 & Hfootprint_lookup_2).
        wp_apply (structeq_footprint_wp_tag with "Hfootprint") as "Hfootprint"; first done.
        wp_pures.
        case_bool_decide; wp_pures.
        + wp_apply (structeq_footprint_wp_size with "Hfootprint") as "Hfootprint"; first done.
          wp_pures.
          case_bool_decide; wp_pures.
          * wp_apply ("IHstructeq_aux_block_loc" with "[$Hfootprint] HΦ").
            iPureIntro. split_and!; [naive_solver lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and!; try done.
            cbn. erewrite !lookup_total_correct; [| done..].
            rewrite andb_false_iff !beq_spec'. naive_solver.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and!; try done.
          cbn. erewrite !lookup_total_correct; [| done..].
          rewrite andb_false_iff !beq_spec'. naive_solver.

      - case_bool_decide; wp_pures.
        + case_bool_decide; wp_pures.
          * wp_apply ("IHstructeq_aux_block_block" with "[$Hfootprint] HΦ").
            iPureIntro. split_and!; [naive_solver lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. simpl in Hj. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and!; try done.
            rewrite andb_false_iff !beq_spec'. naive_solver.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and!; try done.
          rewrite andb_false_iff !beq_spec'. naive_solver.
    }

    { iClear "IHstructeq_aux_loc_block IHstructeq_aux_block_loc IHstructeq_aux_block_block".
      iIntros "%l1 %blk1 %l2 %blk2 %footprint %i !> %Φ (%Hi & %Hfootprint_lookup_1 & %Hfootprint_lookup_2 & % & % & Hfootprint & %Hstructeq) HΦ".

      wp_rec. wp_pures.
      case_bool_decide; wp_pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simplify.

        + rewrite andb_true_iff !beq_spec.
          erewrite !lookup_total_correct; done.

        + rewrite Hfootprint_lookup_1 in Hreachable1.
          destruct (blk1.(structeq_block_fields) !! j) as [fld1 |] eqn:Hfields1_lookup; last done.
          rewrite Hfootprint_lookup_2 in Hreachable2.
          destruct (blk2.(structeq_block_fields) !! j) as [fld2 |] eqn:Hfields2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        wp_apply (structeq_footprint_wp_load' with "Hfootprint") as (fld2) "(%Hfields2_lookup & %Htraversable2 & Hfootprint)"; [done | lia |].
        wp_apply (structeq_footprint_wp_load' with "Hfootprint") as (fld1) "(%Hfields1_lookup & %Htraversable1 & Hfootprint)"; [done | lia |].
        wp_smart_apply ("IHstructeq" with "[$Hfootprint]") as (b) "(%Hb & Hfootprint)"; first iSteps.
        destruct b; wp_pures.

        + wp_apply ("IHstructeq_aux_loc_loc" with "[$Hfootprint] HΦ").
          iPureIntro. split_and!; try done; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive_solver lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hfootprint_lookup_1 Hfields1_lookup //.
          * rewrite /= Hfootprint_lookup_2 Hfields2_lookup //.
    }

    { iClear "IHstructeq_aux_loc_loc IHstructeq_aux_block_loc IHstructeq_aux_block_block".
      iIntros "%l1 %blk1 %gen2 %tag2 %vs2 %footprint %i !> %Φ (%Hi & %Hfootprint_lookup_1 & % & % & % & %Htraversable2 & Hfootprint & %Hstructeq) HΦ".

      wp_rec. wp_pures.
      case_bool_decide; wp_pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simplify.

        + destruct vs2 as [| v2 vs2]; first naive_solver lia.
          rewrite andb_true_iff !beq_spec.
          erewrite !lookup_total_correct; done.

        + rewrite Hfootprint_lookup_1 in Hreachable1.
          destruct (blk1.(structeq_block_fields) !! j) as [fld1 |] eqn:Hfields1_lookup; last done.
          destruct (vs2 !! j) as [v2 |] eqn:Hvs2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        destruct (lookup_lt_is_Some_2 vs2 (₊i - 1)) as (v2 & Hvs2_lookup); first lia.

        wp_pures.
        wp_apply (structeq_footprint_wp_load' with "Hfootprint") as (fld1) "(%Hfields1_lookup & %Htraversable1 & Hfootprint)"; [done | lia |].
        wp_smart_apply ("IHstructeq" with "[$Hfootprint]") as (b) "(%Hb & Hfootprint)"; first iSteps.
        { iPureIntro.
          rewrite /= Forall'_Forall Forall_lookup in Htraversable2.
          naive_solver.
        }
        destruct b; wp_pures.

        + wp_apply ("IHstructeq_aux_loc_block" with "[$Hfootprint] HΦ").
          iPureIntro. split_and!; try done; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive_solver lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hfootprint_lookup_1 Hfields1_lookup //.
          * rewrite /= Hvs2_lookup //.
    }

    { iClear "IHstructeq_aux_loc_loc IHstructeq_aux_loc_block IHstructeq_aux_block_block".
      iIntros "%gen1 %tag1 %vs1 %l2 %blk2 %footprint %i !> %Φ (%Hi & %Hfootprint_lookup_2 & % & % & % & %Htraversable1 & Hfootprint & %Hstructeq) HΦ".

      wp_rec. wp_pures.
      case_bool_decide; wp_pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simplify.

        + destruct vs1 as [| v1 vs1]; first naive_solver lia.
          rewrite andb_true_iff !beq_spec.
          erewrite !lookup_total_correct; done.

        + destruct (vs1 !! j) as [v1 |] eqn:Hvs1_lookup; last done.
          rewrite Hfootprint_lookup_2 in Hreachable2.
          destruct (blk2.(structeq_block_fields) !! j) as [fld2 |] eqn:Hfields2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        destruct (lookup_lt_is_Some_2 vs1 (₊i - 1)) as (v1 & Hvs1_lookup); first lia.

        wp_pures.
        wp_apply (structeq_footprint_wp_load' with "Hfootprint") as (fld2) "(%Hfields2_lookup & %Htraversable2 & Hfootprint)"; [done | lia |].
        wp_smart_apply ("IHstructeq" with "[$Hfootprint]") as (b) "(%Hb & Hfootprint)"; first iSteps.
        { iPureIntro.
          rewrite /= Forall'_Forall Forall_lookup in Htraversable1.
          naive_solver.
        }
        destruct b; wp_pures.

        + wp_apply ("IHstructeq_aux_block_loc" with "[$Hfootprint] HΦ").
          iPureIntro. split_and!; try done; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive_solver lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hvs1_lookup //.
          * rewrite /= Hfootprint_lookup_2 Hfields2_lookup //.
    }

    { iClear "IHstructeq_aux_loc_loc IHstructeq_aux_loc_block IHstructeq_aux_block_loc".
      iIntros "%gen1 %tag1 %vs1 %gen2 %tag2 %vs2 %footprint %i !> %Φ (%Hi & -> & % & % & %Htraversable1 & %Htraversable2 & Hfootprint & %Hstructeq) HΦ".

      wp_rec. wp_pures.
      case_bool_decide; wp_pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simplify.

        + destruct vs1 as [| v1 vs1]; first naive_solver lia.
          destruct vs2 as [| v2 vs2]; first naive_solver lia.
          rewrite andb_true_iff !beq_spec //.

        + destruct (vs1 !! j) as [v1 |] eqn:Hvs1_lookup; last done.
          destruct (vs2 !! j) as [v2 |] eqn:Hvs2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        destruct (lookup_lt_is_Some_2 vs1 (₊i - 1)) as (v1 & Hvs1_lookup); first lia.
        destruct (lookup_lt_is_Some_2 vs2 (₊i - 1)) as (v2 & Hvs2_lookup); first lia.

        wp_pures.
        wp_smart_apply ("IHstructeq" with "[$Hfootprint]") as (b) "(%Hb & Hfootprint)".
        { iPureIntro.
          rewrite /= !Forall'_Forall !Forall_lookup in Htraversable1 Htraversable2.
          naive_solver.
        }
        destruct b; wp_pures.

        + wp_apply ("IHstructeq_aux_block_block" with "[$Hfootprint] HΦ").
          iPureIntro. split_and!; try done; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive_solver lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hvs1_lookup //.
          * rewrite /= Hvs2_lookup //.
    }
  Qed.
  Lemma structeq_spec {v1 v2} footprint :
    val_traversable footprint v1 →
    val_traversable footprint v2 →
    {{{
      structeq_footprint footprint
    }}}
      v1 = v2
    {{{ b,
      RET #b;
      ⌜(if b then val_structeq else val_structneq) footprint v1 v2⌝ ∗
      structeq_footprint footprint
    }}}.
  Proof.
    iIntros "%Htraversable1 %Htraversable2 %Φ Hfootprint HΦ".
    iDestruct structeq_spec_aux as "(H & _)".
    iApply ("H" with "[$Hfootprint]"); iSteps.
  Qed.
End zoo_G.

#[global] Opaque structeq.

(* Abstract (tree-like) values *)

Fixpoint val_abstract v :=
  match v with
  | ValBool _
  | ValInt _ =>
      True
  | ValBlock Nongenerative _ vs =>
      Forall' val_abstract vs
  | _ =>
      False
  end.
#[global] Arguments val_abstract !_ / : assert.

Lemma val_abstract_traversable v :
  val_abstract v →
  val_traversable ∅ v.
Proof.
  induction v as [[] | | [] tag vs IH] => //.
  rewrite /= !Forall'_Forall !Forall_forall in IH |- *.
  naive_solver.
Qed.

Lemma val_compatible_refl_abstract footprint v1 v2 :
  val_abstract v1 →
  val_abstract v2 →
  v1 ≈ v2 →
  val_compatible footprint v1 v2 = true.
Proof.
  destruct v1 as [[] | | [] tag1 [| v1 vs1]] => //.
  all: destruct v2 as [[] | | [] tag2 [| v2 vs2]] => //.
  all: try rewrite bool_decide_eq_true //.
  intros Habstract1 Habstract2 Hsimilar.
  zoo_simplify in Hsimilar.
  rewrite andb_true_iff.
  split; apply beq_true; naive_solver.
Qed.

Lemma val_structeq_abstract_1 footprint v1 v2 :
  val_abstract v1 →
  val_abstract v2 →
  val_structeq footprint v1 v2 →
  v1 ≈ v2.
Proof.
  move: v2. induction v1 as [[] | | [] tag1 [| v1 vs1'] IH] => //.
  all: intros [[] | | [] tag2 [| v2 vs2']] => //.
  all: intros Habstract1 Habstract2 Hstructeq.
  all:
    try (
      ospecialize* (Hstructeq []) => //;
      apply bool_decide_eq_true in Hstructeq;
      naive_solver
    ).
  opose proof* (Hstructeq []) as Hcompatible => //.
  apply andb_prop in Hcompatible as (<-%beq_eq & Hlen%beq_eq).
  split; first done.
  set (vs1 := v1 :: vs1') in *. clearbody vs1 => {v1 vs1'}.
  set (vs2 := v2 :: vs2') in *. clearbody vs2 => {v2 vs2'}.
  rewrite Forall2'_Forall2 Forall2_fmap Forall2_same_length_lookup.
  split; first done. intros i v1 v2 Hlookup1 Hlookup2.
  rewrite /= !Forall'_Forall !Forall_lookup in IH Habstract1 Habstract2.
  eapply IH; [naive_solver.. |]. intros path v1' v2' Hreachable1 Hreachable2.
  apply (Hstructeq (i :: path)); rewrite /= ?Hlookup1 ?Hlookup2 //.
Qed.
Lemma val_structeq_abstract_2 v1 v2 :
  val_abstract v1 →
  val_abstract v2 →
  v1 ≈ v2 →
  val_structeq ∅ v1 v2.
Proof.
  move: v2. induction v1 as [[] | | [] tag1 [| v1 vs1'] IH] => //.
  all: intros [[] | | [] tag2 [| v2 vs2']] => //.
  all: intros Habstract1 Habstract2 Hsimilar.
  all:
    try (
      intros [] v1 v2; last done; intros <- <-;
      apply val_compatible_refl_abstract; done
    ).
  intros [| i path] w1 w2.
  - intros <- <-.
    apply val_compatible_refl_abstract; done.
  - destruct Hsimilar as (<- & Hsimilar).
    set (vs1 := v1 :: vs1') in *. clearbody vs1 => {v1 vs1'}.
    set (vs2 := v2 :: vs2') in *. clearbody vs2 => {v2 vs2'}.
    move=> /= Hreachable1 Hreachable2.
    destruct (vs1 !! i) as [v1 |] eqn:Hlookup1; last done.
    destruct (vs2 !! i) as [v2 |] eqn:Hlookup2; last done.
    rewrite /= !Forall'_Forall !Forall_lookup in IH Habstract1 Habstract2.
    rewrite Forall2'_Forall2 Forall2_fmap Forall2_same_length_lookup in Hsimilar.
    eapply IH; last done; naive_solver.
Qed.
Lemma val_structeq_abstract v1 v2 :
  val_abstract v1 →
  val_abstract v2 →
  val_structeq ∅ v1 v2 ↔
  v1 ≈ v2.
Proof.
  intros Habstract1 Habstract2. split.
  - apply val_structeq_abstract_1; done.
  - apply val_structeq_abstract_2; done.
Qed.

Lemma val_structneq_abstract v1 v2 :
  val_abstract v1 →
  val_abstract v2 →
  val_structneq ∅ v1 v2 →
  v1 ≉ v2.
Proof.
  move: v2. induction v1 as [[] | | [] tag1 [| v1 vs1'] IH] => //.
  all: intros [[] | | [] tag2 [| v2 vs2']] => //.
  all: intros Habstract1 Habstract2 (path & v1 & v2 & Hreachable1 & Hreachable2 & Hcompatible).
  all: destruct path; last done; simplify.
  all: rewrite bool_decide_eq_false in Hcompatible.
  all: cbn; naive_solver.
Qed.

Lemma structeq_spec_abstract `{zoo_G : !ZooG Σ} {v1 v2} :
  val_abstract v1 →
  val_abstract v2 →
  {{{
    True
  }}}
    v1 = v2
  {{{ b,
    RET #b;
    ⌜(if b then (≈) else (≉)) v1 v2⌝
  }}}.
Proof.
  iIntros "%Habstract1 %Habstract2 %Φ _ HΦ".
  wp_apply (structeq_spec ∅) as ([]) "(%H & _)".
  { apply val_abstract_traversable => //. }
  { apply val_abstract_traversable => //. }
  { iApply structeq_footprint_empty. }
  - apply val_structeq_abstract in H; [| done..].
    iSteps.
  - apply val_structneq_abstract in H; [| done..].
    iSteps.
Qed.
