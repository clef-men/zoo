From zoo Require Import
  prelude.
From zoo.language Require Export
  wp.
From zoo.language Require Import
  notations.
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

Fixpoint structeq_traversable' footprint v :=
  match v with
  | ValLit (LitBool _)
  | ValLit (LitInt _) =>
      true
  | ValLit (LitLoc l) =>
      bool_decide (l ∈ dom footprint)
  | ValBlock _ _ vs =>
      forallb (structeq_traversable' footprint) vs
  | _ =>
      false
  end.
#[global] Arguments structeq_traversable' _ !_ / : assert.

Definition structeq_traversable footprint v :=
  structeq_traversable' footprint v = true.

Definition structeq_footprint `{zoo_G : !ZooG Σ} footprint : iProp Σ :=
  [∗ map] l ↦ blk ∈ footprint,
    l ↦ₕ Header blk.(structeq_block_tag) (length blk.(structeq_block_fields)) ∗
    [∗ list] i ↦ v ∈ blk.(structeq_block_fields),
      (l +ₗ i) ↦{blk.(structeq_block_dfrac)} v ∗
      ⌜structeq_traversable footprint v⌝.

Fixpoint structeq_reachable footprint src path dst :=
  match path with
  | [] =>
      src = dst
  | pos :: path =>
      match src with
      | ValLit (LitLoc l) =>
          match (footprint !!! l).(structeq_block_fields) !! pos with
          | None =>
              False
          | Some src =>
              structeq_reachable footprint src path dst
          end
      | ValBlock _ _ vs =>
          match vs !! pos with
          | None =>
              False
          | Some src =>
              structeq_reachable footprint src path dst
          end
      | _ =>
          False
      end
  end.
#[global] Arguments structeq_reachable _ !_ !_ / _ : assert.

Definition structeq_similar footprint v1 v2 :=
  match v1 with
  | ValLit (LitBool _)
  | ValLit (LitInt _) =>
      Some $ bool_decide (v1 = v2)
  | ValLit (LitLoc l1) =>
      match v2 with
      | ValLit (LitLoc l2) =>
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
      | ValLit (LitLoc l2) =>
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
#[global] Arguments structeq_similar _ !_ !_ / : assert.

Axiom structeq_spec : ∀ `{zoo_G : !ZooG Σ} {v1 v2} footprint,
  structeq_traversable footprint v1 →
  structeq_traversable footprint v2 →
  {{{
    structeq_footprint footprint
  }}}
    v1 = v2
  {{{ b,
    RET #b;
    structeq_footprint footprint ∗
    ⌜ if b then
        ∀ path v1' v2',
        structeq_reachable footprint v1 path v1' →
        structeq_reachable footprint v2 path v2' →
        structeq_similar footprint v1' v2' = Some true
      else
        ∃ path v1' v2',
        structeq_reachable footprint v1 path v1' ∧
        structeq_reachable footprint v2 path v2' ∧
        structeq_similar footprint v1' v2' = Some false
    ⌝
  }}}.
