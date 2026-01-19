From iris.bi Require Export
  lib.atomic.
From iris.base_logic Require Import
  lib.invariants.

From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Section aacc.
  Context `{BiFUpd PROP}.
  Context {TA TB : tele}.

  Implicit Types P : PROP.
  Implicit Types α : TA → PROP.
  Implicit Types β Φ : TA → TB → PROP.

  Lemma aacc_intro Eo Ei α P β Φ x :
    Ei ⊆ Eo →
    α x -∗
    ( α x ={Eo}=∗ P)
    ∧ (∀.. y : TB, β x y ={Eo}=∗ Φ x y
    ) -∗
    atomic_acc Eo Ei α P β Φ.
  Proof.
    intros.
    iApply aacc_intro; first done.
  Qed.
End aacc.

Tactic Notation "iAaccIntro" ne_open_constr_list_sep(xs, ",") "with" constr(H) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (atomic_acc ?Eo ?Ei ?α ?P ?β ?Φ) =>
      let go := ltac2val:(xs |-
        let xs := Option.get (Ltac1.to_list xs) in
        let xs := List.map (fun x => Option.get (Ltac1.to_constr x)) xs in
        let xs :=
          List.fold_right (fun x acc =>
            '(@TeleArgCons _ (λ x, _) $x $acc)
          ) xs 'TargO
        in
        Ltac1.of_constr xs
      ) in
      let xs := go xs in
      iApply (aacc_intro Eo Ei α P β Φ xs with H);
      [ try solve_ndisj
      |
      | iSplit
      ]
  | _ =>
      fail "iAaccIntro: goal is not an atomic accessor"
  end.
