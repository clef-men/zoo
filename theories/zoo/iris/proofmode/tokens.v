From iris.proofmode Require Import
  base.
From iris.prelude Require Import
  options.

Inductive token :=
  | TName : string → token
  | TNat : nat → token
  | TAnon : token
  | TFrame : token
  | TBar : token
  | TBracketL : token
  | TBracketR : token
  | TAmp : token
  | TParenL : token
  | TParenR : token
  | TBraceL : token
  | TBraceR : token
  | TPure : option string → token
  | TIntuitionistic : token
  | TModal : token
  | TPureIntro : token
  | TIntuitionisticIntro : token
  | TModalIntro : token
  | TSimpl : token
  | TDone : token
  | TForall : token
  | TAll : token
  | TMinus : token
  | TSep : token
  | TArrow : direction → token
  | TCustom : string → string → token.

Module tokenize.
  Inductive state :=
    | SName : string → state
    | SNat : nat → state
    | SPure : string -> state
    | SNone : state.

  Definition cons_state kn k :=
    match kn with
    | SNone =>
        k
    | SName s =>
        TName (String.rev s) :: k
    | SPure s =>
        TPure (if String.eqb s "" then None else Some (String.rev s)) :: k
    | SNat n =>
        TNat n :: k
    end.
  Fixpoint go s k kn :=
    match s with
    | "" =>
        Some (reverse (cons_state kn k))
    | String "?" s =>
        go s (TAnon :: cons_state kn k) SNone
    | String "$" s =>
        go s (TFrame :: cons_state kn k) SNone
    | String "[" s =>
        go s (TBracketL :: cons_state kn k) SNone
    | String "]" s =>
        go s (TBracketR :: cons_state kn k) SNone
    | String "|" s =>
        go s (TBar :: cons_state kn k) SNone
    | String "(" (String ":" s) =>
        custom s (cons_state kn k) ""
    | String "(" s =>
        go s (TParenL :: cons_state kn k) SNone
    | String ")" s =>
        go s (TParenR :: cons_state kn k) SNone
    | String "&" s =>
        go s (TAmp :: cons_state kn k) SNone
    | String "{" s =>
        go s (TBraceL :: cons_state kn k) SNone
    | String "}" s =>
        go s (TBraceR :: cons_state kn k) SNone
    | String "%" s =>
        go s (cons_state kn k) (SPure "")
    | String "#" s =>
        go s (TIntuitionistic :: cons_state kn k) SNone
    | String ">" s =>
        go s (TModal :: cons_state kn k) SNone
    | String "!" (String "%" s) =>
        go s (TPureIntro :: cons_state kn k) SNone
    | String "!" (String "#" s) =>
        go s (TIntuitionisticIntro :: cons_state kn k) SNone
    | String "!" (String ">" s) =>
        go s (TModalIntro :: cons_state kn k) SNone
    | String "/" (String "/" (String "=" s)) =>
        go s (TSimpl :: TDone :: cons_state kn k) SNone
    | String "/" (String "/" s) =>
        go s (TDone :: cons_state kn k) SNone
    | String "/" (String "=" s) =>
        go s (TSimpl :: cons_state kn k) SNone
    | String "*" (String "*" s) =>
        go s (TAll :: cons_state kn k) SNone
    | String "*" s =>
        go s (TForall :: cons_state kn k) SNone
    | String "-" (String ">" s) =>
        go s (TArrow Right :: cons_state kn k) SNone
    | String "<" (String "-" s) =>
        go s (TArrow Left :: cons_state kn k) SNone
    | String "-" s =>
        go s (TMinus :: cons_state kn k) SNone
    | String (Ascii.Ascii false true false false false true true true) (* unicode ∗ *)
        (String (Ascii.Ascii false false false true false false false true)
        (String (Ascii.Ascii true true true false true false false true) s)) =>
        go s (TSep :: cons_state kn k) SNone
    | String a s =>
       (* TODO: Complain about invalid characters, to future-proof this
       against making more characters special. *)
        if Ascii.is_space a then
          go s (cons_state kn k) SNone
        else
          match kn with
          | SNone =>
              match Ascii.is_nat a with
              | Some n =>
                  go s k (SNat n)
              | None =>
                  go s k (SName (String a ""))
              end
          | SName s' =>
              go s k (SName (String a s'))
          | SPure s' =>
              go s k (SPure (String a s'))
          | SNat n =>
              match Ascii.is_nat a with
              | Some n' =>
                  go s k (SNat (n' + 10 * n))
              | None =>
                  go s (TNat n :: k) (SName (String a ""))
              end
          end
    end
  with custom s k cust :=
    match s with
    | "" =>
        None
    | String ")" s =>
        go s (TCustom (String.rev cust) "" :: k) SNone
    | String chr s =>
        if Ascii.is_space chr then
          custom_arguments s k (String.rev cust) ""
        else
          custom s k (String chr cust)
    end
  with custom_arguments s k cust arg :=
    match s with
    | "" =>
        None
    | String ")" s =>
        go s (TCustom cust (String.rev arg) :: k) SNone
    | String chr s =>
        custom_arguments s k cust (String chr arg)
    end.

  Definition main s :=
    go s [] SNone.
End tokenize.

Definition tokenize :=
  tokenize.main.
