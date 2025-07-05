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
Implicit Types n : Z.
Implicit Types v : val.
Implicit Types lv : lowval.

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

Definition structeq_footprint `{zoo_G : !ZooG Σ} footprint : iProp Σ :=
  [∗ map] l ↦ blk ∈ footprint,
    l ↦ₕ Header blk.(structeq_block_tag) (length blk.(structeq_block_fields)) ∗
    [∗ list] i ↦ fld ∈ blk.(structeq_block_fields),
      (l +ₗ i) ↦{fld.(structeq_field_dfrac)} fld.(structeq_field_val) ∗
      ⌜val_traversable footprint fld.(structeq_field_val)⌝.

Lemma structeq_footprint_empty `{zoo_G : !ZooG Σ} :
  ⊢ structeq_footprint ∅.
Proof.
  setoid_rewrite big_sepM_empty. done.
Qed.

Fixpoint val_reachable footprint src path dst :=
  match path with
  | [] =>
      src = dst
  | pos :: path =>
      match src with
      | ValLoc l =>
          match footprint !! l with
          | None =>
              False
          | Some blk =>
              match blk.(structeq_block_fields) !! pos with
              | None =>
                  False
              | Some fld =>
                  val_reachable footprint fld.(structeq_field_val) path dst
              end
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

#[global] Instance val_reachable_dec footprint src path dst :
  Decision (val_reachable footprint src path dst).
Proof.
  move: src path.
  refine (
    fix go src path {struct path} :=
      match path with
      | [] =>
          cast_if (decide (src = dst))
      | pos :: path =>
          match src with
          | ValLoc l =>
              (match footprint !! l as x return _ = x → _ with
              | None => λ Hfootprint_lookup,
                  right _
              | Some blk => λ Hfootprint_lookup,
                  (match blk.(structeq_block_fields) !! pos as x return _ = x → _ with
                  | None => λ Hfields_lookup,
                      right _
                  | Some fld => λ Hfields_lookup,
                      cast_if (go fld.(structeq_field_val) path)
                  end) (eq_refl (blk.(structeq_block_fields) !! pos))
              end) (eq_refl (footprint !! l))
          | ValBlock _ _ vs =>
              (match vs !! pos as x return _ = x → _ with
              | None => λ Hvs_lookup,
                  right _
              | Some src => λ Hvs_lookup,
                  cast_if (go src path)
              end) (eq_refl (vs !! pos))
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

Axiom structeq_spec : ∀ `{zoo_G : !ZooG Σ} {v1 v2} footprint,
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
  remember (v1 :: vs1') as vs1 eqn:Hvs1 => {v1 vs1' Hvs1}.
  remember (v2 :: vs2') as vs2 eqn:Hvs2 => {v2 vs2' Hvs2}.
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
    remember (v1 :: vs1') as vs1 eqn:Hvs1 => {v1 vs1' Hvs1}.
    remember (v2 :: vs2') as vs2 eqn:Hvs2 => {v2 vs2' Hvs2}.
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
