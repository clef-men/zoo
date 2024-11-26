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
  | TColon : token.

Inductive state :=
  | SName : string → state
  | SNat : nat → state
  | SPure : string -> state
  | SNone : state.

Definition cons_state (kn : state) (k : list token) : list token :=
  match kn with
  | SNone => k
  | SName s => TName (String.rev s) :: k
  | SPure s => TPure (if String.eqb s "" then None else Some (String.rev s)) :: k
  | SNat n => TNat n :: k
  end.

Fixpoint tokenize_go (s : string) (k : list token) (kn : state) : list token :=
  match s with
  | "" => reverse (cons_state kn k)
  | String "?" s => tokenize_go s (TAnon :: cons_state kn k) SNone
  | String "$" s => tokenize_go s (TFrame :: cons_state kn k) SNone
  | String "[" s => tokenize_go s (TBracketL :: cons_state kn k) SNone
  | String "]" s => tokenize_go s (TBracketR :: cons_state kn k) SNone
  | String "|" s => tokenize_go s (TBar :: cons_state kn k) SNone
  | String "(" s => tokenize_go s (TParenL :: cons_state kn k) SNone
  | String ")" s => tokenize_go s (TParenR :: cons_state kn k) SNone
  | String "&" s => tokenize_go s (TAmp :: cons_state kn k) SNone
  | String "{" s => tokenize_go s (TBraceL :: cons_state kn k) SNone
  | String "}" s => tokenize_go s (TBraceR :: cons_state kn k) SNone
  | String "%" s => tokenize_go s (cons_state kn k) (SPure "")
  | String "#" s => tokenize_go s (TIntuitionistic :: cons_state kn k) SNone
  | String ">" s => tokenize_go s (TModal :: cons_state kn k) SNone
  | String "!" (String "%" s) => tokenize_go s (TPureIntro :: cons_state kn k) SNone
  | String "!" (String "#" s) => tokenize_go s (TIntuitionisticIntro :: cons_state kn k) SNone
  | String "!" (String ">" s) => tokenize_go s (TModalIntro :: cons_state kn k) SNone
  | String "/" (String "/" (String "=" s)) =>
     tokenize_go s (TSimpl :: TDone :: cons_state kn k) SNone
  | String "/" (String "/" s) => tokenize_go s (TDone :: cons_state kn k) SNone
  | String "/" (String "=" s) => tokenize_go s (TSimpl :: cons_state kn k) SNone
  | String "*" (String "*" s) => tokenize_go s (TAll :: cons_state kn k) SNone
  | String "*" s => tokenize_go s (TForall :: cons_state kn k) SNone
  | String "-" (String ">" s) => tokenize_go s (TArrow Right :: cons_state kn k) SNone
  | String "<" (String "-" s) => tokenize_go s (TArrow Left :: cons_state kn k) SNone
  | String "-" s => tokenize_go s (TMinus :: cons_state kn k) SNone
  | String ":" s => tokenize_go s (TColon :: cons_state kn k) SNone
  | String (Ascii.Ascii false true false false false true true true) (* unicode ∗ *)
      (String (Ascii.Ascii false false false true false false false true)
      (String (Ascii.Ascii true true true false true false false true) s)) =>
     tokenize_go s (TSep :: cons_state kn k) SNone
  | String a s =>
     (* TODO: Complain about invalid characters, to future-proof this
     against making more characters special. *)
     if Ascii.is_space a then tokenize_go s (cons_state kn k) SNone else
     match kn with
     | SNone =>
        match Ascii.is_nat a with
        | Some n => tokenize_go s k (SNat n)
        | None => tokenize_go s k (SName (String a ""))
        end
     | SName s' => tokenize_go s k (SName (String a s'))
     | SPure s' => tokenize_go s k (SPure (String a s'))
     | SNat n =>
        match Ascii.is_nat a with
        | Some n' => tokenize_go s k (SNat (n' + 10 * n))
        | None => tokenize_go s (TNat n :: k) (SName (String a ""))
        end
     end
  end.
Definition tokenize (s : string) : list token := tokenize_go s [] SNone.
