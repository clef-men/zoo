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

#[local] Definition parse_binding str :=
  let '(var, val) := split_on "=" str in
  let val := default var val in
  (var, val).

Definition format_env_of_bindings bdgs : format_env :=
  list_to_map bdgs.
Definition format_env_of_strings strs :=
  format_env_of_bindings (parse_binding <$> strs).
Definition format_env_of_string str :=
  format_env_of_strings (String.words str).

Module parse.
  Fixpoint go env str pref suff :=
    match str with
    | "" =>
        Some (pref +:+ String.rev suff)
    | String "{" str =>
        hole env str pref suff ""
    | String chr str =>
        go env str pref (String chr suff)
    end
  with hole env str pref suff var :=
    match str with
    | "" =>
        None
    | String "=" str =>
        hole_default env str pref suff var ""
    | String "}" str =>
        let var := String.rev var in
        match env !! var with
        | None =>
            go env str (pref +:+ String.rev_app suff var) ""
        | Some val =>
            go env str (pref +:+ String.rev_app suff val) ""
        end
    | String chr str =>
        hole env str pref suff (String chr var)
    end
  with hole_default env str pref suff var default :=
    match str with
    | "" =>
        None
    | String "}" str =>
        let var := String.rev var in
        match env !! var with
        | None =>
            go env str pref (default +:+ suff)
        | Some val =>
            go env str (pref +:+ String.rev_app suff val) ""
        end
    | String chr str =>
        hole_default env str pref suff var (String chr default)
    end.

  Definition main env str :=
    go env str "" "".
End parse.

Definition format fmt env :=
  parse.main env fmt.
