Require Import stdpp.gmap.

Require Import zoo.prelude.
Require Export zoo.language.syntax.
Require Import zoo.options.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type env : gmap string val.

Fixpoint occurs x e :=
  match e with
  | Val _ =>
      false
  | Var y =>
      x ≟ y
  | Rec f y e =>
      ￢ BNamed x ≟ f &&
      ￢ BNamed x ≟ f &&
      ￢ BNamed x ≟ y &&
      occurs x e
  | Apply e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | Let y e1 e2 =>
      occurs x e1 ||
        ￢ BNamed x ≟ y &&
        occurs x e2
  | If e0 e1 e2 =>
      occurs x e0 ||
      occurs x e1 ||
      occurs x e2
  | While e0 e1 =>
      occurs x e0 ||
      occurs x e1
  | For e1 e2 e3 =>
      occurs x e1 ||
      occurs x e2 ||
      occurs x e3
  | Match e0 y e1 brs =>
      occurs x e0 ||
      (￢ BNamed x ≟ y) && occurs x e1 ||
      existsb (λ br,
        let pat := br.1 in
        forallb (λ y, ￢ BNamed x ≟ y) pat.(pattern۰fields) &&
        ￢ BNamed x ≟ pat.(pattern۰as) &&
        occurs x br.2
      ) brs
  | Primitive0 _ =>
      false
  | Primitive1 _ e =>
      occurs x e
  | Primitive2 _ e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | Primitive3 _ e1 e2 e3 =>
      occurs x e1 ||
      occurs x e2 ||
      occurs x e3
  | Block _ _ es =>
      existsb (occurs x) es
  | Fork e =>
      occurs x e
  | Resolve e0 e1 e2 =>
      occurs x e0 ||
      occurs x e1 ||
      occurs x e2
  end.

Definition val۰recursive v :=
  match v with
  | ValRecs _ recs =>
      existsb (λ rec,
        match rec.1.1 with
        | BAnon =>
            false
        | BNamed f =>
            existsb (λ rec,
              ￢ BNamed f ≟ rec.1.2 &&
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
      if x ≟ y then
        Val v
      else
        Var y
  | Rec f y e =>
      Rec
        f y
        ( if BNamed x ≟ f || BNamed x ≟ y then
            e
          else
            subst x v e
        )
  | Apply e1 e2 =>
      Apply
        (subst x v e1)
        (subst x v e2)
  | Let y e1 e2 =>
      Let
        y
        (subst x v e1)
        ( if BNamed x ≟ y then
            e2
          else
            subst x v e2
        )
  | If e0 e1 e2 =>
      If
        (subst x v e0)
        (subst x v e1)
        (subst x v e2)
  | While e0 e1 =>
      While
        (subst x v e0)
        (subst x v e1)
  | For e1 e2 e3 =>
      For
        (subst x v e1)
        (subst x v e2)
        (subst x v e3)
  | Match e0 y e1 brs =>
      Match
        (subst x v e0)
        y
        ( if BNamed x ≟ y then
            e1
          else
            subst x v e1
        )
        ( ( λ br,
              ( br.1,
                if
                  existsb (BNamed x ≟.) br.1.(pattern۰fields) ||
                  BNamed x ≟ br.1.(pattern۰as)
                then
                  br.2
                else
                  subst x v br.2
              )
          ) <$> brs
        )
  | Primitive0 _ =>
      e
  | Primitive1 prim e =>
      Primitive1
        prim
        (subst x v e)
  | Primitive2 prim e1 e2 =>
      Primitive2
        prim
        (subst x v e1)
        (subst x v e2)
  | Primitive3 prim e1 e2 e3 =>
      Primitive3
        prim
        (subst x v e1)
        (subst x v e2)
        (subst x v e3)
  | Block mut tag es =>
      Block
        mut tag
        (subst x v <$> es)
  | Fork e =>
      Fork
        (subst x v e)
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

Lemma substｰval x v1 v2 :
  subst x v1 (Val v2) = Val v2.
Proof.
  done.
Qed.
Lemma subst'ｰval x v1 v2 :
  subst' x v1 (Val v2) = Val v2.
Proof.
  destruct x; done.
Qed.
