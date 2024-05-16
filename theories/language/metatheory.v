From zoo Require Import
  prelude.
From zoo.language Require Export
  language.
From zoo Require Import
  options.

Fixpoint occurs x e :=
  match e with
  | Val _ =>
      false
  | Var y =>
      bool_decide (x = y)
  | Rec f y e =>
      bool_decide (BNamed x ≠ f) &&
      bool_decide (BNamed x ≠ y) &&
      occurs x e
  | App e1 e2 =>
      occurs x e1 ||
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
  | Constr _ es =>
      existsb (occurs x) es
  | Proj _ e =>
      occurs x e
  | Match e0 y e1 brs =>
      occurs x e0 ||
      bool_decide (BNamed x ≠ y) && occurs x e1 ||
      existsb (λ br,
        let pat := br.1 in
        forallb (λ y, bool_decide (BNamed x ≠ y)) pat.(pattern_fields) &&
        bool_decide (BNamed x ≠ pat.(pattern_as)) &&
        occurs x br.2
      ) brs
  | Reveal e =>
      occurs x e
  | For e1 e2 e3 =>
      occurs x e1 ||
      occurs x e2 ||
      occurs x e3
  | Record es =>
      existsb (occurs x) es
  | Alloc e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | Load e =>
      occurs x e
  | Store l e =>
      occurs x l ||
      occurs x e
  | Xchg e1 e2 =>
      occurs x e1 ||
      occurs x e2
  | Cas e0 e1 e2 =>
      occurs x e0 ||
      occurs x e1 ||
      occurs x e2
  | Faa e1 e2 =>
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
  | ValRec (BNamed f) x e =>
      occurs f e
  | _ =>
      false
  end.
