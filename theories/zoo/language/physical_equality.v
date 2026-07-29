Require Import zoo.prelude.
Require Export zoo.common.typeclasses.
Require Export zoo.common.math.
Require Export zoo.common.list.
Require Export zoo.language.syntax.
Require Import zoo.options.

Implicit Type i tag : nat.
Implicit Type n : Z.
Implicit Type l : location.
Implicit Type gen : generativity.
Implicit Type lit : literal.
Implicit Type v : val.
Implicit Type vs : list val.

Variant lowliteral :=
  | LowlitInt n
  | LowlitLoc l
  | LowlitProph
  | LowlitPoison.
Implicit Type llit : lowliteral.

#[global] Instance lowliteralｰeq_dec : EqDecision lowliteral :=
  ltac:(solve_decision).

Definition literal۰to_low lit :=
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
#[global] Arguments literal۰to_low !_ / : simpl nomatch, assert.

#[global] Instance lowliteral۰nonsimilar : Nonsimilar lowliteral :=
  λ llit1 llit2,
    match llit1 with
    | LowlitInt n1 =>
        llit2 ≠ LowlitInt n1
    | LowlitLoc l1 =>
        llit2 ≠ LowlitLoc l1
    | _ =>
        True
    end.

#[global] Instance lowliteralｰnonsimilarｰdec :
  RelDecision (≉@{lowliteral}).
Proof.
  unshelve refine (
    λ llit1 llit2,
      match llit1 with
      | LowlitInt n1 =>
          decide (llit2 ≠ LowlitInt n1)
      | LowlitLoc l1 =>
          decide (llit2 ≠ LowlitLoc l1)
      | _ =>
          left _
      end
  ).
  all: abstract done.
Defined.

#[global] Instance lowliteralｰnonsimilarｰsymmetric :
  Symmetric (≉@{lowliteral}).
Proof.
  intros [] []; done.
Qed.

Unset Elimination Schemes.
Inductive lowval :=
  | LowvalLit llit
  | LowvalRecs
  | LowvalBlock gen tag vs (lvs : list lowval).
Set Elimination Schemes.
Implicit Type lv : lowval.
Implicit Type lvs : list lowval.

Section lowval۰ind.
  Variable P : lowval → Prop.

  Variable HLit :
    ∀ llit,
    P (LowvalLit llit).
  Variable HRecs :
    P LowvalRecs.
  Variable HBlock :
    ∀ gen tag vs,
    ∀ lvs, Forall P lvs →
    P (LowvalBlock gen tag vs lvs).

  Fixpoint lowval۰ind lv :=
    match lv with
    | LowvalLit llit =>
        HLit
          llit
    | LowvalRecs =>
        HRecs
    | LowvalBlock gen tag vs lvs =>
        HBlock
          gen tag vs
          lvs (Forall_true P lvs lowval۰ind)
    end.
End lowval۰ind.

Notation LowvalInt n := (
  LowvalLit (LowlitInt n)
)(only parsing
).
Notation LowvalLoc l := (
  LowvalLit (LowlitLoc l)
)(only parsing
).
Notation LowvalProph := (
  LowvalLit LowlitProph
)(only parsing
).
Notation LowvalPoison := (
  LowvalLit LowlitPoison
)(only parsing
).

#[global] Instance lowvalｰeq_dec : EqDecision lowval.
Proof.
  unshelve refine (
    fix go lv1 lv2 : Decision (lv1 = lv2) :=
      let fix go_list lvs1 lvs2 : Decision (lvs1 = lvs2) :=
        match lvs1, lvs2 with
        | [], [] =>
            left _
        | lv1 :: lvs1, lv2 :: lvs2 =>
            cast_if_and
              (decide (lv1 = lv2))
              (decide (lvs1 = lvs2))
        | _, _ =>
            right _
        end
      in
      match lv1, lv2 with
      | LowvalLit llit1, LowvalLit llit2 =>
          cast_if
            (decide (llit1 = llit2))
      | LowvalRecs, LowvalRecs =>
          left _
      | LowvalBlock gen1 tag1 vs1 lvs1, LowvalBlock gen2 tag2 vs2 lvs2 =>
          cast_if_and4
            (decide (gen1 = gen2))
            (decide (tag1 = tag2))
            (decide (vs1 = vs2))
            (decide (lvs1 = lvs2))
      | _, _ =>
          right _
      end
  ).
  all: abstract congruence.
Defined.

Fixpoint val۰to_low v :=
  match v with
  | ValLit llit =>
      LowvalLit (literal۰to_low llit)
  | ValRecs _ _ =>
      LowvalRecs
  | ValBlock _ tag [] =>
      LowvalLit (LowlitInt tag)
  | ValBlock gen tag vs =>
      LowvalBlock gen tag vs (val۰to_low <$> vs)
  end.
#[global] Arguments val۰to_low !_ / : simpl nomatch, assert.

#[global] Instance lowval۰nonsimilar : Nonsimilar lowval :=
  λ lv1 lv2,
    match lv1 with
    | LowvalLit llit1 =>
        match lv2 with
        | LowvalLit llit2 =>
            llit1 ≉ llit2
        | _ =>
            True
        end
    | LowvalBlock (Generative (Some bid1)) tag1 vs1 _ =>
        match lv2 with
        | LowvalBlock (Generative (Some bid2)) tag2 vs2 _ =>
            bid1 ≠ bid2 ∨
            tag1 ≠ tag2 ∨
            vs1 ≠ vs2
        | _ =>
            True
        end
    | _ =>
        True
    end.

#[global] Instance lowvalｰnonsimilarｰdec :
  RelDecision (≉@{lowval}).
Proof.
  unshelve refine (
    λ lv1 lv2,
      match lv1 with
      | LowvalLit llit1 =>
          match lv2 with
          | LowvalLit llit2 =>
              decide (llit1 ≉ llit2)
          | _ =>
              left _
          end
      | LowvalBlock (Generative (Some bid1)) tag1 vs1 _ =>
          match lv2 with
          | LowvalBlock (Generative (Some bid2)) tag2 vs2 _ =>
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

#[global] Instance lowval۰similar : Similar lowval :=
  fix go lv1 lv2 :=
    match lv1 with
    | LowvalLit llit1 =>
        lv2 = LowvalLit llit1
    | LowvalRecs =>
        lv2 = LowvalRecs
    | LowvalBlock gen1 tag1 vs1 lvs1 =>
        match lv2 with
        | LowvalBlock gen2 tag2 vs2 lvs2 =>
            match gen1, gen2 with
            | Generative bid1, Generative bid2 =>
                bid1 = bid2 ∧
                tag1 = tag2 ∧
                vs1 = vs2
            | Nongenerative, Nongenerative =>
                tag1 = tag2 ∧
                Forall2' go lvs1 lvs2
            | _, _ =>
                False
            end
        | _ =>
            False
        end
    end.

#[global] Instance lowvalｰsimilarｰdec :
  RelDecision (≈@{lowval}).
Proof.
  refine (
    fix go lv1 lv2 :=
      match lv1 with
      | LowvalLit llit1 =>
          decide (lv2 = LowvalLit llit1)
      | LowvalRecs =>
          decide (lv2 = LowvalRecs)
      | LowvalBlock gen1 tag1 vs1 lvs1 =>
          match lv2 with
          | LowvalBlock gen2 tag2 vs2 lvs2 =>
              match gen1, gen2 with
              | Generative bid1, Generative bid2 =>
                  cast_if_and3
                    (decide (bid1 = bid2))
                    (decide (tag1 = tag2))
                    (decide (vs1 = vs2))
              | Nongenerative, Nongenerative =>
                  cast_if_and
                    (decide (tag1 = tag2))
                    (@decide (Forall2' (≈) lvs1 lvs2) (@Forall2'ｰdec _ _ _ go _ _))
              | _, _ =>
                  right _
              end
          | _ =>
              right _
          end
      end
  ).
  all: simpl.
  all: abstract intuition.
Defined.

#[global] Instance lowvalｰnonsimilarｰsymmetric :
  Symmetric (≉@{lowval}).
Proof.
  do 2 intros [| | [[] |]]; naive_solver.
Qed.

#[global] Instance lowvalｰsimilarｰreflexive :
  Reflexive (≈@{lowval}).
Proof.
  rewrite /Reflexive. fix IH 1.
  intros [| | []].
  4: apply Forall2'ｰrefl in IH as ?.
  all: clear IH.
  all: naive_solver.
Qed.
Lemma lowvalｰsimilarｰrefl lv1 lv2 :
  lv1 = lv2 →
  lv1 ≈ lv2.
Proof.
  naive_solver.
Qed.
#[global] Instance lowvalｰsimilarｰsymmetric :
  Symmetric (≈@{lowval}).
Proof.
  rewrite /Symmetric. fix IH 1.
  do 2 intros [| | []].
  16: apply Forall2'ｰsym in IH as ?.
  all: clear IH.
  all: naive_solver.
Qed.
#[global] Instance lowvalｰsimilarｰtransitive :
  Transitive (≈@{lowval}).
Proof.
  rewrite /Transitive. fix IH 1.
  do 3 intros [| | []].
  64: apply Forall2'ｰtrans in IH as ?.
  all: clear IH.
  all: naive_solver.
Qed.

Lemma lowvalｰsimilarｰorｰnonsimilar lv1 lv2 :
  lv1 ≈ lv2 ∨ lv1 ≉ lv2.
Proof.
  all: destruct lv1 as [[n1 | l1 | |] | | [[bid1 |] |] tag1 [| v1 vs1]].
  all: destruct lv2 as [[n2 | l2 | |] | | [[bid2 |] |] tag2 [| v2 vs2]].
  all: try destruct_decide (n1 = n2).
  all: try destruct_decide (l1 = l2).
  all: try destruct_decide (bid1 = bid2).
  all: try destruct_decide (tag1 = tag2).
  all: try destruct_decide (v1 = v2).
  all: try destruct_decide (vs1 = vs2).
  all: cbn; naive_solver.
Qed.
Lemma lowvalｰnonsimilarｰsimilar lv1 lv2 lv3 :
  lv1 ≉ lv2 →
  lv2 ≈ lv3 →
  lv1 ≉ lv3.
Proof.
  all: destruct lv2 as [| | []].
  all: destruct lv3 as [| | []].
  all: naive_solver.
Qed.

#[global] Instance val۰nonsimilar : Nonsimilar val :=
  λ v1 v2,
    val۰to_low v1 ≉ val۰to_low v2.

#[global] Instance valｰnonsimilarｰdec : RelDecision (≉@{val}) :=
  ltac:(rewrite /nonsimilar /val۰nonsimilar; solve_decision).

#[global] Instance val۰similar : Similar val :=
  λ v1 v2,
    val۰to_low v1 ≈ val۰to_low v2.

#[global] Instance valｰsimilarｰdec : RelDecision (≈@{val}) :=
  ltac:(rewrite /similar /val۰similar; solve_decision).

#[global] Instance valｰnonsimilarｰsymmetric :
  Symmetric (≉@{val}).
Proof.
  rewrite /nonsimilar /val۰nonsimilar /Symmetric //.
Qed.
Lemma valｰnonsimilarｰbool b1 b2 :
  ValBool b1 ≉ ValBool b2 →
  b1 ≠ b2.
Proof.
  naive_solver.
Qed.
Lemma valｰnonsimilarｰint n1 n2 :
  ValInt n1 ≉ ValInt n2 →
  n1 ≠ n2.
Proof.
  naive_solver.
Qed.
Lemma valｰnonsimilarｰnat (n1 n2 : nat) :
  ValNat n1 ≉ ValNat n2 →
  n1 ≠ n2.
Proof.
  naive_solver.
Qed.
Lemma valｰnonsimilarｰlocation l1 l2 :
  ValLoc l1 ≉ ValLoc l2 →
  l1 ≠ l2.
Proof.
  naive_solver.
Qed.
Lemma valｰnonsimilarｰblockｰempty gen1 tag1 gen2 tag2 :
  ValBlock gen1 tag1 [] ≉ ValBlock gen2 tag2 [] →
  tag1 ≠ tag2.
Proof.
  naive_solver.
Qed.
Lemma valｰnonsimilarｰblockｰgenerative bid1 tag1 vs1 bid2 tag2 vs2 :
  tag1 = tag2 →
  vs1 = vs2 →
  ValBlock (Generative (Some bid1)) tag1 vs1 ≉ ValBlock (Generative (Some bid2)) tag2 vs2 →
  length vs1 = 0 ∨ bid1 ≠ bid2.
Proof.
  intros <- <-.
  destruct vs1; first done.
  cbn. naive_solver.
Qed.

#[global] Instance valｰsimilarｰreflexive :
  Reflexive (≈@{val}).
Proof.
  rewrite /similar /val۰similar /Reflexive //.
Qed.
Lemma valｰsimilarｰrefl v1 v2 :
  v1 = v2 →
  v1 ≈ v2.
Proof.
  naive_solver.
Qed.
#[global] Instance valｰsimilarｰsymmetric :
  Symmetric (≈@{val}).
Proof.
  rewrite /similar /val۰similar /Symmetric //.
Qed.
#[global] Instance valｰsimilarｰtransitive :
  Transitive (≈@{val}).
Proof.
  rewrite /similar /val۰similar /Transitive.
  firstorder. etrans; done.
Qed.
Lemma valｰsimilarｰbool b1 b2 :
  ValLit (LitBool b1) ≈ ValLit (LitBool b2) →
  b1 = b2.
Proof.
  intros [= ->%(inj _)%(inj _)]. done.
Qed.
Lemma valｰsimilarｰint n1 n2 :
  ValLit (LitInt n1) ≈ ValLit (LitInt n2) →
  n1 = n2.
Proof.
  intros [= ->]. done.
Qed.
Lemma valｰsimilarｰnat (n1 n2 : nat) :
  ValLit (LitInt n1) ≈ ValLit (LitInt n2) →
  n1 = n2.
Proof.
  intros <-%valｰsimilarｰint%(inj _). done.
Qed.
Lemma valｰsimilarｰlocation l1 l2 :
  ValLit (LitLoc l1) ≈ ValLit (LitLoc l2) →
  l1 = l2.
Proof.
  intros [= ->]. done.
Qed.
Lemma valｰsimilarｰblockｰempty gen1 tag1 gen2 tag2 :
  ValBlock gen1 tag1 [] ≈ ValBlock gen2 tag2 [] →
  tag1 = tag2.
Proof.
  intros [= ->%(inj _)]. done.
Qed.
Lemma valｰsimilarｰblockｰempty₁ gen1 tag1 gen2 tag2 v2 vs2 :
  ¬ ValBlock gen1 tag1 [] ≈ ValBlock gen2 tag2 (v2 :: vs2).
Proof.
  done.
Qed.
Lemma valｰsimilarｰblockｰempty₂ gen1 tag1 v1 vs1 gen2 tag2 :
  ¬ ValBlock gen1 tag1 (v1 :: vs1) ≈ ValBlock gen2 tag2 [].
Proof.
  intros []%symmetry%valｰsimilarｰblockｰempty₁.
Qed.
Lemma valｰsimilarｰblockｰgenerative bid1 tag1 vs1 bid2 tag2 vs2 :
  length vs1 ≠ 0 ∨ length vs2 ≠ 0 →
  ValBlock (Generative bid1) tag1 vs1 ≈ ValBlock (Generative bid2) tag2 vs2 →
    bid1 = bid2 ∧
    tag1 = tag2 ∧
    vs1 = vs2.
Proof.
  destruct vs1, vs2; naive_solver.
Qed.
Lemma valｰsimilarｰblockｰnongenerative tag1 vs1 tag2 vs2 :
  ValBlock Nongenerative tag1 vs1 ≈ ValBlock Nongenerative tag2 vs2 →
    tag1 = tag2 ∧
    length vs1 = length vs2.
Proof.
  destruct vs1, vs2; try done.
  - intros [= ->%(inj _)]. done.
  - intros (<- & Hlen%Forall2'ｰlength).
    simpl_length in Hlen.
Qed.
Lemma valｰsimilarｰlocationｰblock l gen tag vs :
  ¬ ValLit (LitLoc l) ≈ ValBlock gen tag vs.
Proof.
  destruct vs; done.
Qed.
Lemma valｰsimilarｰblockｰlocation gen tag vs l :
  ¬ ValBlock gen tag vs ≈ ValLit (LitLoc l).
Proof.
  intros []%symmetry%valｰsimilarｰlocationｰblock.
Qed.
Lemma valｰsimilarｰblockｰgenerativeｰnongenerative bid1 tag1 vs1 tag2 vs2 :
  length vs1 ≠ 0 ∨ length vs2 ≠ 0 →
  ¬ ValBlock (Generative bid1) tag1 vs1 ≈ ValBlock Nongenerative tag2 vs2.
Proof.
  destruct vs1, vs2; cbn; naive_solver lia.
Qed.
Lemma valｰsimilarｰblockｰnongenerativeｰgenerative tag1 vs1 bid2 tag2 vs2 :
  length vs1 ≠ 0 ∨ length vs2 ≠ 0 →
  ¬ ValBlock Nongenerative tag1 vs1 ≈ ValBlock (Generative bid2) tag2 vs2.
Proof.
  intros ? []%symmetry%valｰsimilarｰblockｰgenerativeｰnongenerative. naive_solver.
Qed.

Lemma valｰsimilarｰorｰnonsimilar v1 v2 :
  v1 ≈ v2 ∨ v1 ≉ v2.
Proof.
  apply lowvalｰsimilarｰorｰnonsimilar.
Qed.
Lemma valｰnonsimilarｰsimilar v1 v2 v3 :
  v1 ≉ v2 →
  v2 ≈ v3 →
  v1 ≉ v3.
Proof.
  apply lowvalｰnonsimilarｰsimilar.
Qed.
