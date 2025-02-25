From zoo Require Import
  prelude.
From zoo.common Require Export
  typeclasses
  math.
From zoo.language Require Export
  syntax.
From zoo Require Import
  options.

Implicit Types i tag : nat.
Implicit Types n : Z.
Implicit Types l : location.
Implicit Types gen : generativity.
Implicit Types vs : list val.
Implicit Types recs : list recursive.

Definition literal_physical lit :=
  match lit with
  | LitBool _
  | LitInt _
  | LitLoc _ =>
      True
  | LitProph _
  | LitPoison =>
      False
  end.
#[global] Arguments literal_physical !_ / : simpl nomatch, assert.

Inductive lowliteral :=
  | LowlitInt n
  | LowlitLoc l
  | LowlitProph
  | LowlitPoison.
Implicit Types llit : lowliteral.

#[global] Instance lowliteral_eq_dec : EqDecision lowliteral :=
  ltac:(solve_decision).

Definition literal_to_low lit :=
  match lit with
  | LitBool b =>
      LowlitInt (Nat.b2n b)
  | LitInt n =>
      LowlitInt n
  | LitLoc l =>
      LowlitLoc l
  | LitProph _ =>
      LowlitProph
  | LitPoison =>
      LowlitPoison
  end.
#[global] Arguments literal_to_low !_ / : simpl nomatch, assert.

#[global] Instance lowliteral_nonsimilar : Nonsimilar lowliteral :=
  λ lit1 lit2,
    match lit1 with
    | LowlitInt n1 =>
        lit2 ≠ LowlitInt n1
    | LowlitLoc l1 =>
        lit2 ≠ LowlitLoc l1
    | _ =>
        True
    end.

#[global] Instance lowliteral_nonsimilar_dec : RelDecision (≉@{lowliteral}).
Proof.
  unshelve refine (
    λ lit1 lit2,
      match lit1 with
      | LowlitInt n1 =>
          decide (lit2 ≠ LowlitInt n1)
      | LowlitLoc l1 =>
          decide (lit2 ≠ LowlitLoc l1)
      | _ =>
          left _
      end
  ).
  all: abstract done.
Defined.

#[global] Instance lowliteral_nonsimilar_symmetric :
  Symmetric (≉@{lowliteral}).
Proof.
  intros [] []; done.
Qed.

Inductive lowval :=
  | LowvalLit llit
  | LowvalRecs
  | LowvalBlock gen tag vs.

#[global] Instance lowval_eq_dec : EqDecision lowval :=
  ltac:(solve_decision).

Definition val_to_low v :=
  match v with
  | ValLit lit =>
      LowvalLit (literal_to_low lit)
  | ValRecs _ _ =>
      LowvalRecs
  | ValBlock _ tag [] =>
      LowvalLit (LowlitInt tag)
  | ValBlock gen tag vs =>
      LowvalBlock gen tag vs
  end.
#[global] Arguments val_to_low !_ / : simpl nomatch, assert.

#[global] Instance lowval_nonsimilar : Nonsimilar lowval :=
  λ v1 v2,
    match v1 with
    | LowvalLit lit1 =>
        match v2 with
        | LowvalLit lit2 =>
            lit1 ≉ lit2
        | _ =>
            True
        end
    | LowvalBlock (Generative (Some bid1)) tag1 vs1 =>
        match v2 with
        | LowvalBlock (Generative (Some bid2)) tag2 vs2 =>
            bid1 ≠ bid2 ∨
            tag1 ≠ tag2 ∨
            vs1 ≠ vs2
        | _ =>
            True
        end
    | _ =>
        True
    end.

#[global] Instance lowval_nonsimilar_dec : RelDecision (≉@{lowval}).
Proof.
  unshelve refine (
    λ v1 v2,
      match v1 with
      | LowvalLit lit1 =>
          match v2 with
          | LowvalLit lit2 =>
              decide (lit1 ≉ lit2)
          | _ =>
              left _
          end
      | LowvalBlock (Generative (Some bid1)) tag1 vs1 =>
          match v2 with
          | LowvalBlock (Generative (Some bid2)) tag2 vs2 =>
              cast_if_or3
                (decide (bid1 ≠ bid2))
                (decide (tag1 ≠ tag2))
                (decide (vs1 ≠ vs2))
          | _ =>
              left _
          end
      | _ =>
          left _
      end
  ).
  all: abstract naive_solver.
Defined.

#[global] Instance lowval_similar : Similar lowval :=
  λ v1 v2,
    match v1 with
    | LowvalLit lit1 =>
        v2 = LowvalLit lit1
    | LowvalRecs =>
        v2 = LowvalRecs
    | LowvalBlock gen1 tag1 vs1 =>
        match v2 with
        | LowvalBlock gen2 tag2 vs2 =>
            match gen1, gen2 with
            | Generative bid1, Generative bid2 =>
                bid1 = bid2 ∧
                tag1 = tag2 ∧
                vs1 = vs2
            | Nongenerative, Nongenerative =>
                tag1 = tag2 ∧
                length vs1 = length vs2
            | _, _ =>
                False
            end
        | _ =>
            False
        end
    end.

#[global] Instance lowval_similar_dec : RelDecision (≈@{lowval}).
Proof.
  unshelve refine (
    λ v1 v2,
      match v1 with
      | LowvalLit lit1 =>
          decide (v2 = LowvalLit lit1)
      | LowvalRecs =>
          decide (v2 = LowvalRecs)
      | LowvalBlock gen1 tag1 vs1 =>
          match v2 with
          | LowvalBlock gen2 tag2 vs2 =>
              match gen1, gen2 with
              | Generative bid1, Generative bid2 =>
                  cast_if_and3
                    (decide (bid1 = bid2))
                    (decide (tag1 = tag2))
                    (decide (vs1 = vs2))
              | Nongenerative, Nongenerative =>
                  cast_if_and
                    (decide (tag1 = tag2))
                    (decide (length vs1 = length vs2))
              | _, _ =>
                  right _
              end
          | _ =>
              right _
          end
      end
  ).
  all: abstract naive_solver.
Defined.

#[global] Instance lowval_nonsimilar_symmetric :
  Symmetric (≉@{lowval}).
Proof.
  intros [| | [[] |]] [| | [[] |]]; naive_solver.
Qed.

#[global] Instance lowval_similar_reflexive :
  Reflexive (≈@{lowval}).
Proof.
  intros [| | []]; done.
Qed.
Lemma lowval_similar_refl v1 v2 :
  v1 = v2 →
  v1 ≈ v2.
Proof.
  naive_solver.
Qed.
#[global] Instance lowval_similar_symmetric :
  Symmetric (≈@{lowval}).
Proof.
  do 2 intros [| | []]; naive_solver.
Qed.
#[global] Instance lowval_similar_transitive :
  Transitive (≈@{lowval}).
Proof.
  do 3 intros [| | []]; naive_solver congruence.
Qed.

Lemma lowval_similar_or_nonsimilar v1 v2 :
  v1 ≈ v2 ∨ v1 ≉ v2.
Proof.
  destruct
    v1 as [[n1 | l1 | |] | | [[bid1 |] |] tag1 [| v1 vs1]],
    v2 as [[n2 | l2 | |] | | [[bid2 |] |] tag2 [| v2 vs2]].
  all: try destruct (decide (n1 = n2)).
  all: try destruct (decide (l1 = l2)).
  all: try destruct (decide (bid1 = bid2)).
  all: try destruct (decide (tag1 = tag2)).
  all: try destruct (decide (v1 = v2)).
  all: try destruct (decide (vs1 = vs2)).
  all: cbn; naive_solver.
Qed.
Lemma lowval_nonsimilar_similar (v1 v2 v3 : lowval) :
  v1 ≉ v2 →
  v2 ≈ v3 →
  v1 ≉ v3.
Proof.
  destruct v2 as [| | []], v3 as [| | []]; naive_solver.
Qed.

#[global] Instance val_nonsimilar : Nonsimilar val :=
  λ v1 v2,
    val_to_low v1 ≉ val_to_low v2.

#[global] Instance val_nonsimilar_dec : RelDecision (≉@{val}) :=
  ltac:(rewrite /nonsimilar /val_nonsimilar; solve_decision).

#[global] Instance val_similar : Similar val :=
  λ v1 v2,
    val_to_low v1 ≈ val_to_low v2.

#[global] Instance val_similar_dec : RelDecision (≈@{val}) :=
  ltac:(rewrite /similar /val_similar; solve_decision).

#[global] Instance val_nonsimilar_symmetric :
  Symmetric (≉@{val}).
Proof.
  rewrite /nonsimilar /val_nonsimilar /Symmetric //.
Qed.
Lemma val_nonsimilar_bool b1 b2 :
  ValBool b1 ≉ ValBool b2 →
  b1 ≠ b2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_int n1 n2 :
  ValInt n1 ≉ ValInt n2 →
  n1 ≠ n2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_nat (n1 n2 : nat) :
  ValNat n1 ≉ ValNat n2 →
  n1 ≠ n2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_location l1 l2 :
  ValLoc l1 ≉ ValLoc l2 →
  l1 ≠ l2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_block_empty gen1 tag1 gen2 tag2 :
  ValBlock gen1 tag1 [] ≉ ValBlock gen2 tag2 [] →
  tag1 ≠ tag2.
Proof.
  naive_solver.
Qed.
Lemma val_nonsimilar_block_generative bid1 tag1 vs1 bid2 tag2 vs2 :
  tag1 = tag2 →
  vs1 = vs2 →
  ValBlock (Generative (Some bid1)) tag1 vs1 ≉ ValBlock (Generative (Some bid2)) tag2 vs2 →
  length vs1 = 0 ∨ bid1 ≠ bid2.
Proof.
  intros <- <-.
  destruct vs1; first done.
  cbn. naive_solver.
Qed.

#[global] Instance val_similar_reflexive :
  Reflexive (≈@{val}).
Proof.
  rewrite /similar /val_similar /Reflexive //.
Qed.
Lemma val_similar_refl v1 v2 :
  v1 = v2 →
  v1 ≈ v2.
Proof.
  naive_solver.
Qed.
#[global] Instance val_similar_symmetric :
  Symmetric (≈@{val}).
Proof.
  rewrite /similar /val_similar /Symmetric //.
Qed.
#[global] Instance val_similar_transitive :
  Transitive (≈@{val}).
Proof.
  rewrite /similar /val_similar /Transitive.
  firstorder. etrans; done.
Qed.
Lemma val_similar_bool b1 b2 :
  ValLit (LitBool b1) ≈ ValLit (LitBool b2) →
  b1 = b2.
Proof.
  intros [= ->%(inj _)%(inj _)]. done.
Qed.
Lemma val_similar_int n1 n2 :
  ValLit (LitInt n1) ≈ ValLit (LitInt n2) →
  n1 = n2.
Proof.
  intros [= ->]. done.
Qed.
Lemma val_similar_nat (n1 n2 : nat) :
  ValLit (LitInt n1) ≈ ValLit (LitInt n2) →
  n1 = n2.
Proof.
  intros <-%val_similar_int%(inj _). done.
Qed.
Lemma val_similar_location l1 l2 :
  ValLit (LitLoc l1) ≈ ValLit (LitLoc l2) →
  l1 = l2.
Proof.
  intros [= ->]. done.
Qed.
Lemma val_similar_block_empty gen1 tag1 gen2 tag2 :
  ValBlock gen1 tag1 [] ≈ ValBlock gen2 tag2 [] →
  tag1 = tag2.
Proof.
  intros [= ->%(inj _)]. done.
Qed.
Lemma val_similar_block_empty_1 gen1 tag1 gen2 tag2 v2 vs2 :
  ¬ ValBlock gen1 tag1 [] ≈ ValBlock gen2 tag2 (v2 :: vs2).
Proof.
  done.
Qed.
Lemma val_similar_block_empty_2 gen1 tag1 v1 vs1 gen2 tag2 :
  ¬ ValBlock gen1 tag1 (v1 :: vs1) ≈ ValBlock gen2 tag2 [].
Proof.
  intros []%symmetry%val_similar_block_empty_1.
Qed.
Lemma val_similar_block_generative bid1 tag1 vs1 bid2 tag2 vs2 :
  length vs1 ≠ 0 ∨ length vs2 ≠ 0 →
  ValBlock (Generative bid1) tag1 vs1 ≈ ValBlock (Generative bid2) tag2 vs2 →
    bid1 = bid2 ∧
    tag1 = tag2 ∧
    vs1 = vs2.
Proof.
  destruct vs1, vs2; try done.
  simpl. lia.
Qed.
Lemma val_similar_block_nongenerative tag1 vs1 tag2 vs2 :
  ValBlock Nongenerative tag1 vs1 ≈ ValBlock Nongenerative tag2 vs2 →
    tag1 = tag2 ∧
    length vs1 = length vs2.
Proof.
  destruct vs1, vs2; try done.
  intros [= ->%(inj _)]. done.
Qed.
Lemma val_similar_location_block l gen tag vs :
  ¬ ValLit (LitLoc l) ≈ ValBlock gen tag vs.
Proof.
  destruct vs; done.
Qed.
Lemma val_similar_block_location gen tag vs l :
  ¬ ValBlock gen tag vs ≈ ValLit (LitLoc l).
Proof.
  intros []%symmetry%val_similar_location_block.
Qed.
Lemma val_similar_block_generative_nongenerative bid1 tag1 vs1 tag2 vs2 :
  length vs1 ≠ 0 ∨ length vs2 ≠ 0 →
  ¬ ValBlock (Generative bid1) tag1 vs1 ≈ ValBlock Nongenerative tag2 vs2.
Proof.
  destruct vs1, vs2; cbn; naive_solver lia.
Qed.
Lemma val_similar_block_nongenerative_generative tag1 vs1 bid2 tag2 vs2 :
  length vs1 ≠ 0 ∨ length vs2 ≠ 0 →
  ¬ ValBlock Nongenerative tag1 vs1 ≈ ValBlock (Generative bid2) tag2 vs2.
Proof.
  intros ? []%symmetry%val_similar_block_generative_nongenerative. naive_solver.
Qed.

Lemma val_similar_or_nonsimilar v1 v2 :
  v1 ≈ v2 ∨ v1 ≉ v2.
Proof.
  apply lowval_similar_or_nonsimilar.
Qed.
Lemma val_nonsimilar_similar v1 v2 v3 :
  v1 ≉ v2 →
  v2 ≈ v3 →
  v1 ≉ v3.
Proof.
  apply lowval_nonsimilar_similar.
Qed.
