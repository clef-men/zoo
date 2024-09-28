From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Export
  wp.
From zoo.language Require Import
  notations
  diaframe.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v : val.

Parameter structeq : val.

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

Record structeq_block := StructeqBlock {
  structeq_block_dfrac : dfrac ;
  structeq_block_tag : nat ;
  structeq_block_fields : list val ;
}.
Add Printing Constructor structeq_block.
Implicit Types blk : structeq_block.
Implicit Types footprint : gmap location structeq_block.

#[global] Instance structeq_block_inhabited : Inhabited structeq_block :=
  populate (StructeqBlock inhabitant inhabitant inhabitant).

Fixpoint val_traversable footprint v :=
  match v with
  | ValBool _
  | ValInt _ =>
      True
  | ValLoc l =>
      bool_decide (l ∈ dom footprint)
  | ValBlock _ _ vs =>
      Forall' (val_traversable footprint) vs
  | _ =>
      False
  end.
#[global] Arguments val_traversable _ !_ / : assert.

Definition structeq_footprint `{zoo_G : !ZooG Σ} footprint : iProp Σ :=
  [∗ map] l ↦ blk ∈ footprint,
    l ↦ₕ Header blk.(structeq_block_tag) (length blk.(structeq_block_fields)) ∗
    [∗ list] i ↦ v ∈ blk.(structeq_block_fields),
      (l +ₗ i) ↦{blk.(structeq_block_dfrac)} v ∗
      ⌜val_traversable footprint v⌝.

Lemma structeq_footprint_empty `{zoo_G : !ZooG Σ} :
  ⊢ structeq_footprint ∅.
Proof.
  setoid_rewrite big_sepM_empty => //.
Qed.

Fixpoint val_reachable footprint src path dst :=
  match path with
  | [] =>
      src = dst
  | pos :: path =>
      match src with
      | ValLoc l =>
          match (footprint !!! l).(structeq_block_fields) !! pos with
          | None =>
              False
          | Some src =>
              val_reachable footprint src path dst
          end
      | ValBlock _ _ vs =>
          match vs !! pos with
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

Definition val_similar footprint v1 v2 :=
  match v1 with
  | ValBool _
  | ValInt _ =>
      Some $ bool_decide (v1 = v2)
  | ValLoc l1 =>
      match v2 with
      | ValLoc l2 =>
          let blk1 := footprint !!! l1 in
          let blk2 := footprint !!! l2 in
          Some $ bool_decide (
            blk1.(structeq_block_tag) = blk2.(structeq_block_tag) ∧
            length blk1.(structeq_block_fields) = length blk2.(structeq_block_fields)
          )
      | ValBlock _ tag2 vs2 =>
          let blk1 := footprint !!! l1 in
          Some $ bool_decide (
            blk1.(structeq_block_tag) = tag2 ∧
            length blk1.(structeq_block_fields) = length vs2
          )
      | _ =>
          None
      end
  | ValBlock _ tag1 vs1 =>
      match v2 with
      | ValLoc l2 =>
          let blk2 := footprint !!! l2 in
          Some $ bool_decide (
            tag1 = blk2.(structeq_block_tag) ∧
            length vs1 = length blk2.(structeq_block_fields)
          )
      | ValBlock _ tag2 vs2 =>
          Some $ bool_decide (
            tag1 = tag2 ∧
            length vs1 = length vs2
          )
      | _ =>
          None
      end
  | _ =>
      None
  end.
#[global] Arguments val_similar _ !_ !_ / : assert.

Definition val_structeq footprint v1 v2 :=
  ∀ path v1' v2',
  val_reachable footprint v1 path v1' →
  val_reachable footprint v2 path v2' →
  val_similar footprint v1' v2' = Some true.

Definition val_structne footprint v1 v2 :=
  ∃ path v1' v2',
  val_reachable footprint v1 path v1' ∧
  val_reachable footprint v2 path v2' ∧
  val_similar footprint v1' v2' = Some false.

Axiom structeq_spec : ∀ `{zoo_G : !ZooG Σ} {v1 v2} footprint,
  val_traversable footprint v1 →
  val_traversable footprint v2 →
  {{{
    structeq_footprint footprint
  }}}
    v1 = v2
  {{{ b,
    RET #b;
    structeq_footprint footprint ∗
    ⌜ if b then
        val_structeq footprint v1 v2
      else
        val_structne footprint v1 v2
    ⌝
  }}}.

Fixpoint val_is_abstract v :=
  match v with
  | ValBool _
  | ValInt _ =>
      True
  | ValBlock None _ vs =>
      Forall' val_is_abstract vs
  | _ =>
      False
  end.
#[global] Arguments val_is_abstract !_ / : assert.

Lemma val_is_abstract_traversable v :
  val_is_abstract v →
  val_traversable ∅ v.
Proof.
  induction v as [[] | | [bid |] tag vs IH] => //.
  rewrite /= !Forall'_Forall !Forall_forall in IH |- *.
  naive_solver.
Qed.

Lemma val_is_abstract_structeq v1 v2 :
  val_is_abstract v1 →
  val_is_abstract v2 →
  val_structeq ∅ v1 v2 →
  v1 = v2.
Proof.
  move: v2. induction v1 as [[b1 | i1 | l1 | |]| | [bid1 |] tag1 vs1 IH] => //; intros [[b2 | i2 | l2 | |] | | [bid2 |] tag2 vs2] => // Habstract1 Habstract2 Hstructeq.
  all:
    try solve [
      ospecialize* (Hstructeq []) => //;
      injection Hstructeq as [= ?%bool_decide_eq_true] => //
    ].
  opose proof* (Hstructeq []) as Hsimilar => //.
  injection Hsimilar as [= (<- & Hlength)%bool_decide_eq_true].
  rewrite /= !Forall'_Forall in Habstract1 Habstract2.
  rewrite !Forall_lookup in IH Habstract1 Habstract2.
  destruct (proj2 (list_eq_Forall2 vs1 vs2)); last done.
  apply Forall2_same_length_lookup_2; first done. intros i v1 v2 Hlookup1 Hlookup2.
  eapply IH; [naive_solver.. |]. intros path v1' v2' Hreachable1 Hreachable2.
  apply (Hstructeq (i :: path)); rewrite /= ?Hlookup1 ?Hlookup2 //.
Qed.

Lemma val_is_abstract_structne v1 v2 :
  val_is_abstract v1 →
  val_is_abstract v2 →
  val_structne ∅ v1 v2 →
  v1 ≠ v2.
Proof.
  move: v2. induction v1 as [[b1 | i1 | l1 | |]| | [bid1 |] tag1 vs1 IH] => //; intros [[b2 | i2 | l2 | |] | | [bid2 |] tag2 vs2] => //; intros Habstract1 Habstract2 (path & v1 & v2 & Hreachable1 & Hreachable2 & Hsimilar).
  - intros [= [= <-]].
    destruct path; last done. simplify.
    rewrite bool_decide_eq_true_2 // in Hsimilar.
  - intros [= [= <-]].
    destruct path; last done. simplify.
    rewrite bool_decide_eq_true_2 // in Hsimilar.
  - intros [= <- <-].
    destruct path as [| i path]; simplify.
    + rewrite bool_decide_eq_true_2 // in Hsimilar.
    + destruct (vs1 !! i) as [v |] eqn:Hlookup; last done.
      rewrite Forall'_Forall in Habstract1.
      rewrite !Forall_lookup in Habstract1 IH.
      eapply IH => //; [naive_solver.. |].
      rewrite /val_structne. naive_solver.
Qed.

Lemma structeq_spec_abstract `{zoo_G : !ZooG Σ} v1 v2 Φ :
  val_is_abstract v1 →
  val_is_abstract v2 →
  Φ #(bool_decide (v1 = v2)) ⊢
  WP v1 = v2 {{ Φ }}.
Proof.
  iIntros "%Habstract1 %Habstract2 HΦ".
  wp_apply structeq_spec as ([]) "(_ & %Hb)".
  { apply val_is_abstract_traversable => //. }
  { apply val_is_abstract_traversable => //. }
  { iApply structeq_footprint_empty. }
  - rewrite bool_decide_eq_true_2 //.
    apply val_is_abstract_structeq => //.
  - rewrite bool_decide_eq_false_2 //.
    apply val_is_abstract_structne => //.
Qed.
