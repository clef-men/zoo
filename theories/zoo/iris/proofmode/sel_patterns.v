From stdpp Require Export
  strings.

From iris.proofmode Require Import
  base
  tokens.
From iris.prelude Require Import
  options.

Inductive sel_pat :=
  | SelPure : list string → sel_pat
  | SelPureInv : list string → sel_pat
  | SelIntuitionistic
  | SelSpatial
  | SelIdent : ident → sel_pat.

Fixpoint sel_pat_pure (ps : list sel_pat) : bool :=
  match ps with
  | [] =>
      false
  | SelPure _ :: ps =>
      true
  | SelPureInv _ :: ps =>
      true
  | _ :: ps =>
      sel_pat_pure ps
  end.

Module sel_pat.
  Fixpoint parse_go (ts : list token) (k : list sel_pat) : option (list sel_pat) :=
    match ts with
    | [] =>
        Some (reverse k)
    | TName s :: ts =>
        parse_go ts (SelIdent s :: k)
    | TPure None :: ts =>
        parse_go ts (SelPure [] :: k)
    | TIntuitionistic :: ts =>
        parse_go ts (SelIntuitionistic :: k)
    | TSep :: ts =>
        parse_go ts (SelSpatial :: k)
    | _ =>
        None
    end.
  Definition parse s :=
    parse_go (tokenize s) [].

  Ltac parse s :=
    lazymatch type of s with
    | sel_pat =>
        constr:([s])
    | list sel_pat =>
        s
    | ident =>
        constr:([SelIdent s])
    | list ident =>
        eval vm_compute in (SelIdent <$> s)
    | list string =>
        eval vm_compute in (SelIdent ∘ INamed <$> s)
    | string =>
       lazymatch eval vm_compute in (parse s) with
       | Some ?pats =>
           pats
       | _ =>
           fail "sel_pat.parse: cannot parse" s "as a selection pattern"
       end
    | ?X =>
        fail
          "sel_pat.parse: the term" s
         "is expected to be a selection pattern"
         "(usually a string),"
         "but has unexpected type" X
    end.
End sel_pat.
