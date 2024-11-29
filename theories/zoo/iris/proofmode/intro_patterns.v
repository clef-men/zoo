From stdpp Require Export
  strings.
From stdpp Require Import
  pretty.

From iris.proofmode Require Import
  base
  sel_patterns.
From zoo.iris.proofmode Require Import
  tokens.
From iris.prelude Require Import
  options.

Inductive gallina_ident :=
  | IGallinaNamed : string → gallina_ident
  | IGallinaAnon : gallina_ident.

Inductive intro_pat :=
  | IIdent : ident → intro_pat
  | IFresh : intro_pat
  | IDrop : intro_pat
  | IFrame : intro_pat
  | IList : list (list intro_pat) → intro_pat
  | IPure : gallina_ident → intro_pat
  | IIntuitionistic : intro_pat → intro_pat
  | ISpatial : intro_pat → intro_pat
  | IModalElim : intro_pat → intro_pat
  | IRewrite : direction → intro_pat
  | IPureIntro : intro_pat
  | IModalIntro : intro_pat
  | ISimpl : intro_pat
  | IDone : intro_pat
  | IForall : intro_pat
  | IAll : intro_pat
  | IClear : sel_pat → intro_pat
  | IClearFrame : sel_pat → intro_pat
  | ICustom : string → list string → intro_pat.

Module intro_pat.
Inductive stack_item :=
  | StPat : intro_pat → stack_item
  | StList : stack_item
  | StConjList : stack_item
  | StBar : stack_item
  | StAmp : stack_item
  | StIntuitionistic : stack_item
  | StSpatial : stack_item
  | StModalElim : stack_item.
Notation stack := (list stack_item).

Fixpoint close_list (k : stack)
    (ps : list intro_pat) (pss : list (list intro_pat)) : option stack :=
  match k with
  | StList :: k => Some (StPat (IList (ps :: pss)) :: k)
  | StPat pat :: k => close_list k (pat :: ps) pss
  | StIntuitionistic :: k =>
     '(p,ps) ← maybe2 (::) ps; close_list k (IIntuitionistic p :: ps) pss
  | StModalElim :: k =>
     '(p,ps) ← maybe2 (::) ps; close_list k (IModalElim p :: ps) pss
  | StBar :: k => close_list k [] (ps :: pss)
  | _ => None
  end.

Fixpoint big_conj (ps : list intro_pat) : intro_pat :=
  match ps with
  | [] => IList [[]]
  | [p] => IList [[ p ]]
  | [p1;p2] => IList [[ p1 ; p2 ]]
  | p :: ps => IList [[ p ; big_conj ps ]]
  end.

Fixpoint close_conj_list (k : stack)
    (cur : option intro_pat) (ps : list intro_pat) : option stack :=
  match k with
  | StConjList :: k =>
     ps ← match cur with
          | None => guard (ps = []);; Some [] | Some p => Some (p :: ps)
          end;
     Some (StPat (big_conj ps) :: k)
  | StPat pat :: k => guard (cur = None);; close_conj_list k (Some pat) ps
  | StIntuitionistic :: k => p ← cur; close_conj_list k (Some (IIntuitionistic p)) ps
  | StSpatial :: k => p ← cur; close_conj_list k (Some (ISpatial p)) ps
  | StModalElim :: k => p ← cur; close_conj_list k (Some (IModalElim p)) ps
  | StAmp :: k => p ← cur; close_conj_list k None (p :: ps)
  | _ => None
  end.

Fixpoint parse_go (ts : list token) (k : stack) : option stack :=
  match ts with
  | [] => Some k
  | TName "_" :: ts => parse_go ts (StPat IDrop :: k)
  | TName s :: ts => parse_go ts (StPat (IIdent s) :: k)
  | TAnon :: ts => parse_go ts (StPat IFresh :: k)
  | TFrame :: ts => parse_go ts (StPat IFrame :: k)
  | TBracketL :: ts => parse_go ts (StList :: k)
  | TBar :: ts => parse_go ts (StBar :: k)
  | TBracketR :: ts => close_list k [] [] ≫= parse_go ts
  | TParenL :: TColon :: TName custom :: ts => parse_custom custom [] ts k
  | TParenL :: ts => parse_go ts (StConjList :: k)
  | TAmp :: ts => parse_go ts (StAmp :: k)
  | TParenR :: ts => close_conj_list k None [] ≫= parse_go ts
  | TPure (Some s) :: ts => parse_go ts (StPat (IPure (IGallinaNamed s)) :: k)
  | TPure None :: ts => parse_go ts (StPat (IPure IGallinaAnon) :: k)
  | TIntuitionistic :: ts => parse_go ts (StIntuitionistic :: k)
  | TMinus :: TIntuitionistic :: ts => parse_go ts (StSpatial :: k)
  | TModal :: ts => parse_go ts (StModalElim :: k)
  | TArrow d :: ts => parse_go ts (StPat (IRewrite d) :: k)
  | TPureIntro :: ts => parse_go ts (StPat IPureIntro :: k)
  | (TModalIntro | TIntuitionisticIntro) :: ts => parse_go ts (StPat IModalIntro :: k)
  | TSimpl :: ts => parse_go ts (StPat ISimpl :: k)
  | TDone :: ts => parse_go ts (StPat IDone :: k)
  | TAll :: ts => parse_go ts (StPat IAll :: k)
  | TForall :: ts => parse_go ts (StPat IForall :: k)
  | TBraceL :: ts => parse_clear ts k
  | _ => None
  end
with parse_clear (ts : list token) (k : stack) : option stack :=
  match ts with
  | TFrame :: TName s :: ts => parse_clear ts (StPat (IClearFrame (SelIdent s)) :: k)
  | TFrame :: TPure None :: ts => parse_clear ts (StPat (IClearFrame SelPure) :: k)
  | TFrame :: TIntuitionistic :: ts => parse_clear ts (StPat (IClearFrame SelIntuitionistic) :: k)
  | TFrame :: TSep :: ts => parse_clear ts (StPat (IClearFrame SelSpatial) :: k)
  | TName s :: ts => parse_clear ts (StPat (IClear (SelIdent s)) :: k)
  | TPure None :: ts => parse_clear ts (StPat (IClear SelPure) :: k)
  | TIntuitionistic :: ts => parse_clear ts (StPat (IClear SelIntuitionistic) :: k)
  | TSep :: ts => parse_clear ts (StPat (IClear SelSpatial) :: k)
  | TBraceR :: ts => parse_go ts k
  | _ => None
  end
with parse_custom custom args ts k :=
  match ts with
  | TName arg :: ts =>
      parse_custom custom (arg :: args) ts k
  | TNat i :: ts =>
      parse_custom custom (pretty i :: args) ts k
  | TAnon :: ts =>
      parse_custom custom ("?" :: args) ts k
  | TFrame :: ts =>
      parse_custom custom ("$" :: args) ts k
  | TBar :: ts =>
      parse_custom custom ("|" :: args) ts k
  | TAmp :: ts =>
      parse_custom custom ("&" :: args) ts k
  | TPure str :: ts =>
      parse_custom custom (("%" +:+ default "" str) :: args) ts k
  | TIntuitionistic :: ts =>
      parse_custom custom ("#" :: args) ts k
  | TModal :: ts =>
      parse_custom custom (">" :: args) ts k
  | TPureIntro :: ts =>
      parse_custom custom ("!%" :: args) ts k
  | TIntuitionisticIntro :: ts =>
      parse_custom custom ("!#" :: args) ts k
  | TModalIntro :: ts =>
      parse_custom custom ("!>" :: args) ts k
  | TSimpl :: ts =>
      parse_custom custom ("/=" :: args) ts k
  | TDone :: ts =>
      parse_custom custom ("//" :: args) ts k
  | TForall :: ts =>
      parse_custom custom ("*" :: args) ts k
  | TAll :: ts =>
      parse_custom custom ("**" :: args) ts k
  | TMinus :: ts =>
      parse_custom custom ("-" :: args) ts k
  | TSep :: ts =>
      parse_custom custom ("∗" :: args) ts k
  | TArrow Left :: ts =>
      parse_custom custom ("<-" :: args) ts k
  | TArrow Right :: ts =>
      parse_custom custom ("->" :: args) ts k
  | TParenR :: ts =>
      parse_go ts (StPat (ICustom custom (rev args)) :: k)
  | _ => None
  end.

Fixpoint close (k : stack) (ps : list intro_pat) : option (list intro_pat) :=
  match k with
  | [] => Some ps
  | StPat pat :: k => close k (pat :: ps)
  | StIntuitionistic :: k => '(p,ps) ← maybe2 (::) ps; close k (IIntuitionistic p :: ps)
  | StSpatial :: k => '(p,ps) ← maybe2 (::) ps; close k (ISpatial p :: ps)
  | StModalElim :: k => '(p,ps) ← maybe2 (::) ps; close k (IModalElim p :: ps)
  | _ => None
  end.

Definition parse (s : string) : option (list intro_pat) :=
  k ← parse_go (tokenize s) []; close k [].

Ltac parse s :=
  lazymatch type of s with
  | list intro_pat => s
  | intro_pat => constr:([s])
  | list string =>
     lazymatch eval vm_compute in (mjoin <$> mapM parse s) with
     | Some ?pats => pats
     | _ => fail "intro_pat.parse: cannot parse" s "as an introduction pattern"
     end
  | string =>
     lazymatch eval vm_compute in (parse s) with
     | Some ?pats => pats
     | _ => fail "intro_pat.parse: cannot parse" s "as an introduction pattern"
     end
  | ident => constr:([IIdent s])
  | ?X => fail "intro_pat.parse: the term" s
     "is expected to be an introduction pattern"
     "(usually a string),"
     "but has unexpected type" X
  end.
Ltac parse_one s :=
  lazymatch type of s with
  | intro_pat => s
  | string =>
     lazymatch eval vm_compute in (parse s) with
     | Some [?pat] => pat
     | _ => fail "intro_pat.parse_one: cannot parse" s "as an introduction pattern"
     end
  | ?X => fail "intro_pat.parse_one: the term" s
     "is expected to be an introduction pattern"
     "(usually a string),"
     "but has unexpected type" X
  end.
End intro_pat.

Fixpoint intro_pat_intuitionistic (p : intro_pat) :=
  match p with
  | IPure _ => true
  | IRewrite _ => true
  | IIntuitionistic _ => true
  | IList pps => forallb (forallb intro_pat_intuitionistic) pps
  | ISimpl => true
  | IClear _ => true
  | IClearFrame _ => true
  | _ => false
  end.

Ltac intro_pat_intuitionistic p :=
  lazymatch type of p with
  | intro_pat => eval cbv in (intro_pat_intuitionistic p)
  | list intro_pat => eval cbv in (forallb intro_pat_intuitionistic p)
  | string =>
     let pat := intro_pat.parse p in
     eval cbv in (forallb intro_pat_intuitionistic pat)
  | ident => false
  | bool => p
  | ?X => fail "intro_pat_intuitionistic: the term" p
     "is expected to be an introduction pattern"
     "(usually a string),"
     "but has unexpected type" X
  end.
