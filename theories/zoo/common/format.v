From Coq.Strings Require Import
  Ascii
  String.

From stdpp Require Import
  stringmap.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Implicit Types str pref suff var val : string.
Implicit Types env : stringmap string.

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
    | String "}" str =>
        match env !! String.rev var with
        | None =>
            go env str pref suff
        | Some val =>
            go env str (pref +:+ String.rev_app suff val) ""
        end
    | String chr str =>
        hole env str pref suff (String chr var)
    end.

  Definition main env str :=
    go env str "" "".
End parse.

Module parse_env.
  Variant state :=
    | Var
    | Equal var
    | Val var.

  Fixpoint spaces env str st :=
    match str with
    | "" =>
        if st is Var then
          Some env
        else
          None
    | String chr str =>
        if Ascii.is_space chr then
          spaces env str st
        else
          match st with
          | Var =>
              variable env str (String chr "")
          | Equal var =>
              if chr is "="%char then
                spaces env str (Val var)
              else
                None
          | Val var =>
              value env str var (String chr "")
          end
    end
  with variable env str var :=
    match str with
    | "" =>
        None
    | String chr str =>
        if Ascii.is_space chr then
          spaces env str (Equal (String.rev var))
        else
          variable env str (String chr var)
    end
  with value env str var val :=
    match str with
    | "" =>
        Some (<[var := String.rev val]> env)
    | String chr str =>
        if Ascii.is_space chr then
          spaces (<[var := String.rev val]> env) str Var
        else
          value env str var (String chr val)
    end.

  Definition main str :=
    spaces ∅ str Var.
End parse_env.

Definition format fmt env :=
  parse.main env fmt.
Definition format' fmt (env : string) :=
  env ← parse_env.main env ;
  format fmt env.
