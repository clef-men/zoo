From stdpp Require Import
  gmap.

From zoo Require Import
  prelude.
From zoo.language Require Export
  syntax.
From zoo Require Import
  options.

Implicit Types e : expr.
Implicit Types v : val.
Implicit Types env : gmap string val.

Fixpoint occurs x e :=
  match e with
  | Val _ =>
      false
  | Var y =>
      String.eqb x y
  | Rec f y e =>
      binder_neqb (BNamed x) f &&
      binder_neqb (BNamed x) f &&
      binder_neqb (BNamed x) y &&
      occurs x e
  | App e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | Let y e1 e2 =>
      occurs x e1 ||
        binder_neqb (BNamed x) y &&
        occurs x e2
  | Unop _ e =>
      occurs x e
  | Binop _ e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | Equal e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | If e0 e1 e2 =>
      occurs x e0 ||
      occurs x e1 ||
      occurs x e2
  | For e1 e2 e3 =>
      occurs x e1 ||
      occurs x e2 ||
      occurs x e3
  | Alloc e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | Block _ _ es =>
      existsb (occurs x) es
  | Reveal e =>
      occurs x e
  | Match e0 y e1 brs =>
      occurs x e0 ||
      binder_neqb (BNamed x) y && occurs x e1 ||
      existsb (λ br,
        let pat := br.1 in
        forallb (λ y, binder_neqb (BNamed x) y) pat.(pattern_fields) &&
        binder_neqb (BNamed x) pat.(pattern_as) &&
        occurs x br.2
      ) brs
  | GetTag e =>
      occurs x e
  | GetSize e =>
      occurs x e
  | Load e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | Store e1 e2 e3 =>
      occurs x e1 ||
      occurs x e2 ||
      occurs x e3
  | Xchg e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | CAS e0 e1 e2 =>
      occurs x e0 ||
      occurs x e1 ||
      occurs x e2
  | FAA e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | Fork e =>
      occurs x e
  | Yield =>
      false
  | Proph =>
      false
  | Resolve e0 e1 e2 =>
      occurs x e0 ||
      occurs x e1 ||
      occurs x e2
  end.

Definition val_recursive v :=
  match v with
  | ValRecs _ recs =>
      existsb (λ rec,
        match rec.1.1 with
        | BAnon =>
            false
        | BNamed f =>
            existsb (λ rec,
              binder_neqb (BNamed f) rec.1.2 &&
              occurs f rec.2
            ) recs
        end
      ) recs
  | _ =>
      false
  end.

Fixpoint subst (x : string) v e :=
  match e with
  | Val _ =>
      e
  | Var y =>
      if String.eqb x y then
        Val v
      else
        Var y
  | Rec f y e =>
      Rec
        f y
        ( if binder_eqb (BNamed x) f || binder_eqb (BNamed x) y then
            e
          else
            subst x v e
        )
  | App e1 e2 =>
      App
        (subst x v e1)
        (subst x v e2)
  | Let y e1 e2 =>
      Let
        y
        (subst x v e1)
        ( if binder_eqb (BNamed x) y then
            e2
          else
            subst x v e2
        )
  | Unop op e =>
      Unop
        op
        (subst x v e)
  | Binop op e1 e2 =>
      Binop
        op
        (subst x v e1)
        (subst x v e2)
  | Equal e1 e2 =>
      Equal
        (subst x v e1)
        (subst x v e2)
  | If e0 e1 e2 =>
      If
        (subst x v e0)
        (subst x v e1)
        (subst x v e2)
  | For e1 e2 e3 =>
      For
        (subst x v e1)
        (subst x v e2)
        (subst x v e3)
  | Alloc e1 e2 =>
      Alloc
        (subst x v e1)
        (subst x v e2)
  | Block mut tag es =>
      Block
        mut tag
        (subst x v <$> es)
  | Reveal e =>
      Reveal
        (subst x v e)
  | Match e0 y e1 brs =>
      Match
        (subst x v e0)
        y
        ( if binder_eqb (BNamed x) y then
            e1
          else
            subst x v e1
        )
        ( ( λ br,
              ( br.1,
                if
                  existsb (binder_eqb (BNamed x)) br.1.(pattern_fields) ||
                  binder_eqb (BNamed x) br.1.(pattern_as)
                then
                  br.2
                else
                  subst x v br.2
              )
          ) <$> brs
        )
  | GetTag e =>
      GetTag
        (subst x v e)
  | GetSize e =>
      GetSize
        (subst x v e)
  | Load e1 e2 =>
      Load
        (subst x v e1)
        (subst x v e2)
  | Store e1 e2 e3 =>
      Store
        (subst x v e1)
        (subst x v e2)
        (subst x v e3)
  | Xchg e1 e2 =>
      Xchg
        (subst x v e1)
        (subst x v e2)
  | CAS e0 e1 e2 =>
      CAS
        (subst x v e0)
        (subst x v e1)
        (subst x v e2)
  | FAA e1 e2 =>
      FAA
        (subst x v e1)
        (subst x v e2)
  | Fork e =>
      Fork
        (subst x v e)
  | Yield =>
      Yield
  | Proph =>
      Proph
  | Resolve e0 e1 e2 =>
      Resolve
        (subst x v e0)
        (subst x v e1)
        (subst x v e2)
  end.
#[global] Arguments subst _ _ !_ / : assert.
Definition subst' x v :=
  match x with
  | BNamed x =>
      subst x v
  | BAnon =>
      id
  end.
#[global] Arguments subst' !_ _ / _ : assert.

Fixpoint subst_list xs vs e :=
  match xs with
  | [] =>
      e
  | x :: xs =>
      match vs with
      | [] =>
          e
      | v :: vs =>
          subst' x v $ subst_list xs vs e
      end
  end.
#[global] Arguments subst_list !_ !_ _ / : assert.
