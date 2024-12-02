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
  Fixpoint go env str res :=
    match str with
    | "" =>
        Some (String.rev res)
    | String "{" str =>
        hole env str res ""
    | String chr str =>
        go env str (String chr res)
    end
  with hole env str res acc :=
    match str with
    | "" =>
        None
    | String "{" str =>
        hole_variable env str res acc ""
    | String "=" str =>
        hole_default env str res "" acc "" ""
    | String "}" str =>
        match env !! String.rev acc with
        | None =>
            go env str (acc +:+ res)
        | Some val =>
            go env str (String.rev val +:+ res)
        end
    | String chr str =>
        hole env str res (String chr acc)
    end
  with hole_variable env str res pref var :=
    match str with
    | "" =>
        None
    | String "}" str =>
        hole_suffix env str res pref var ""
    | String chr str =>
        hole_variable env str res pref (String chr var)
    end
  with hole_suffix env str res pref var suff :=
    match str with
    | "" =>
        None
    | String "=" str =>
        hole_default env str res pref var suff ""
    | String "}" str =>
        match env !! String.rev var with
        | None =>
            go env str res
        | Some val =>
            go env str (suff +:+ String.rev val +:+ pref +:+ res)
        end
    | String chr str =>
        hole_suffix env str res pref var (String chr suff)
    end
  with hole_default env str res pref var suff default :=
    match str with
    | "" =>
        None
    | String "}" str =>
        match env !! String.rev var with
        | None =>
            go env str (default +:+ res)
        | Some val =>
            go env str (suff +:+ String.rev val +:+ pref +:+ res)
        end
    | String chr str =>
        hole_default env str res pref var suff (String chr default)
    end.

  Definition main env str :=
    go env str "".
End parse.

Definition format fmt env :=
  parse.main env fmt.
