From Coq.Strings Require Import
  Ascii.

From stdpp Require Import
  gmap.

From zoo Require Import
  prelude.
From zoo.common Require Import
  string.
From zoo Require Import
  options.

Implicit Types str pref suff var val : string.

Definition format_env :=
  gmap string string.
Implicit Types env : format_env.

Module parse.
  Notation assign :=
    "="%char.
  Notation sep :=
    ";"%char.
  Notation hole_beg :=
    "{"%char.
  Notation hole_end :=
    "}"%char.
  Notation forward_beg :=
    "/"%char.
  Notation forward_end :=
    "/"%char.

  Definition binding str :=
    let '(var, val) := split_on assign str in
    let val := default var val in
    (var, val).

  Inductive insideness :=
    | Inside
    | Outside.

  Fixpoint go env str res :=
    match str with
    | "" =>
        Some (String.rev res)
    | String hole_beg str =>
        hole env str res ""
    | String chr str =>
        go env str (String chr res)
    end
  with hole env str res acc :=
    match str with
    | "" =>
        None
    | String hole_beg str =>
        hole_variable env str res acc ""
    | String forward_beg str =>
        hole_forward env str res acc ""
    | String hole_end str =>
        match env !! String.rev acc with
        | None =>
            go env str (acc +:+ res)
        | Some val =>
            go env str (String.rev val +:+ res)
        end
    | String sep str =>
        match env !! String.rev acc with
        | None =>
            hole' env str res ""
        | Some val =>
            hole_finish env str (String.rev val +:+ res) Outside
        end
    | String chr str =>
        hole env str res (String chr acc)
    end
  with hole' env str res acc :=
    match str with
    | "" =>
        None
    | String hole_beg str =>
        hole_variable env str res acc ""
    | String forward_beg str =>
        hole_forward env str res acc ""
    | String hole_end str =>
        go env str (acc +:+ res)
    | String sep str =>
        hole_finish env str (acc +:+ res) Outside
    | String chr str =>
        hole' env str res (String chr acc)
    end
  with hole_variable env str res acc var :=
    match str with
    | "" =>
        None
    | String hole_end str =>
        match env !! String.rev var with
        | None =>
            hole_next env str res Outside
        | Some val =>
            hole' env str res (String.rev val +:+ acc)
        end
    | String chr str =>
        hole_variable env str res acc (String chr var)
    end
  with hole_forward env str res acc var :=
    match str with
    | "" =>
        None
    | String forward_end str =>
        match env !! String.rev var with
        | None =>
            hole' env str res acc
        | Some val =>
            hole' env str res (String.rev val +:+ String assign var +:+ acc)
        end
    | String chr str =>
        hole_forward env str res acc (String chr var)
    end
  with hole_finish env str res state :=
    match str with
    | "" =>
        None
    | String hole_beg str =>
        hole_finish env str res Inside
    | String hole_end str =>
        if state is Inside then
          hole_finish env str res Outside
        else
          go env str res
    | String _ str =>
        hole_finish env str res state
    end
  with hole_next env str res state :=
    match str with
    | "" =>
        None
    | String hole_beg str =>
        hole_next env str res Inside
    | String hole_end str =>
        if state is Inside then
          hole_next env str res Outside
        else
          go env str res
    | String sep str =>
        hole' env str res ""
    | String _ str =>
        hole_next env str res state
    end.
  Definition format env str :=
    go env str "".
End parse.

Definition format_env_of_bindings bdgs : format_env :=
  list_to_map bdgs.
Definition format_env_of_strings strs :=
  format_env_of_bindings (parse.binding <$> strs).
Definition format_env_of_string str :=
  format_env_of_strings (String.words str).

Definition format fmt env :=
  parse.format env fmt.

Goal format "{}" ∅ = Some "".
Proof. reflexivity. Qed.
Goal format "{}" {["":="!"]} = Some "!".
Proof. reflexivity. Qed.

Goal format "{1}" {["1":="one"]} = Some "one".
Proof. reflexivity. Qed.
Goal format "{1}" ∅ = Some "1".
Proof. reflexivity. Qed.

Goal format "{1} {2}" {["1":="one";"2":="two"]} = Some "one two".
Proof. reflexivity. Qed.

Goal format "{1;∅}" ∅ = Some "∅".
Proof. reflexivity. Qed.
Goal format "{1;∅}" {["1":="one"]} = Some "one".
Proof. reflexivity. Qed.

Goal format "{1;}" ∅ = Some "".
Proof. reflexivity. Qed.
Goal format "{1;}" {["1":="one"]} = Some "one".
Proof. reflexivity. Qed.

Goal format "{({1});∅}" ∅ = Some "∅".
Proof. reflexivity. Qed.
Goal format "{({1});∅}" {["1":="one"]} = Some "(one)".
Proof. reflexivity. Qed.

Goal format "{({1});({2})}" ∅ = Some "".
Proof. reflexivity. Qed.
Goal format "{({1});({2})}" {["1":="one"]} = Some "(one)".
Proof. reflexivity. Qed.
Goal format "{({1});({2})}" {["2":="two"]} = Some "(two)".
Proof. reflexivity. Qed.

Goal format "{({1});({2});∅}" ∅ = Some "∅".
Proof. reflexivity. Qed.
Goal format "{({1});({2});∅}" {["1":="one"]} = Some "(one)".
Proof. reflexivity. Qed.
Goal format "{({1});({2});∅}" {["2":="two"]} = Some "(two)".
Proof. reflexivity. Qed.

Goal format "{{1}-{2}}" ∅ = Some "".
Proof. reflexivity. Qed.
Goal format "{{1}-{2}}" {["1":="one"]} = Some "".
Proof. reflexivity. Qed.
Goal format "{{1}-{2}}" {["2":="two"]} = Some "".
Proof. reflexivity. Qed.
Goal format "{{1}-{2}}" {["1":="one";"2":="two"]} = Some "one-two".
Proof. reflexivity. Qed.

Goal format "{{1}-{2};∅}" ∅ = Some "∅".
Proof. reflexivity. Qed.
Goal format "{{1}-{2};∅}" {["1":="one"]} = Some "∅".
Proof. reflexivity. Qed.
Goal format "{{1}-{2};∅}" {["2":="two"]} = Some "∅".
Proof. reflexivity. Qed.
Goal format "{{1}-{2};∅}" {["1":="one";"2":="two"]} = Some "one-two".
Proof. reflexivity. Qed.

Goal format "{/1/}" {["1":="one"]} = Some "1=one".
Proof. reflexivity. Qed.
Goal format "{/1/}" ∅ = Some "".
Proof. reflexivity. Qed.
