From stdpp Require Import
  gmap
  stringmap.

From zebre Require Import
  prelude.
From zebre.language Require Export
  language.
From zebre Require Import
  options.

#[local] Definition set_binder_insert x X : stringset :=
  match x with
  | BAnon =>
      X
  | BNamed f =>
      {[f]} ∪ X
  end.

Fixpoint expr_closed X e :=
  match e with
  | Val v =>
      val_closed v
  | Var x =>
      bool_decide (x ∈ X)
  | Rec f x e =>
      expr_closed (set_binder_insert f (set_binder_insert x X)) e
  | Unop _ e
  | Proj _ e
  | Fork e
  | Load e =>
      expr_closed X e
  | App e1 e2
  | Binop _ e1 e2
  | Equal e1 e2
  | Alloc e1 e2
  | Store e1 e2
  | Xchg e1 e2
  | Faa e1 e2 =>
      expr_closed X e1 && expr_closed X e2
  | If e0 e1 e2
  | Cas e0 e1 e2
  | Resolve e0 e1 e2 =>
      expr_closed X e0 && expr_closed X e1 && expr_closed X e2
  | Tuple es
  | Constr _ es
  | Record es =>
      forallb (expr_closed X) es
  | Case e brs =>
      expr_closed X e && forallb (λ br, expr_closed X br.2) brs
  | Proph =>
      true
  end
with val_closed v :=
  match v with
  | ValLiteral _ =>
      true
  | ValRec f x e =>
      expr_closed (set_binder_insert f (set_binder_insert x ∅)) e
  | ValTuple vs =>
      forallb val_closed vs
  | ValConstr _ vs =>
      forallb val_closed vs
  end.

#[local] Instance set_unfold_elem_of_insert_binder x y X Q :
  SetUnfoldElemOf y X Q →
  SetUnfoldElemOf y (set_binder_insert x X) (Q ∨ BNamed y = x).
Proof.
  destruct 1; constructor; destruct x; set_solver.
Qed.

Lemma subst_closed X e x v :
  expr_closed X e →
  x ∉ X →
  subst x v e = e.
Proof.
  move: X. induction e => X /=;
    rewrite ?bool_decide_spec ?andb_True => ? ?;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
  all: select (Forall _ _) ltac:(fun H => induction H; first done).
  all: try select branch ltac:(fun br => destruct br).
  all: rewrite fmap_cons; repeat f_equal; naive_solver.
Qed.

Lemma subst_closed_empty e x v :
  expr_closed ∅ e →
  subst x v e = e.
Proof.
  intros. apply subst_closed with (∅ : stringset); set_solver.
Qed.

Lemma subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  intros. induction e; simpl; try (f_equal; auto; done);
    simplify_option_eq; auto using subst_closed_empty with f_equal.
  all: select (Forall _ _) ltac:(fun H => induction H).
  all: naive_solver congruence.
Qed.
Lemma subst_subst' e x v v' :
  subst' x v (subst' x v' e) = subst' x v' e.
Proof.
  destruct x; simpl; auto using subst_subst.
Qed.

Lemma subst_subst_ne e x y v v' :
  x ≠ y →
  subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_closed_empty with f_equal.
  all: select (Forall _ _) ltac:(fun H => induction H).
  all: naive_solver congruence.
Qed.
Lemma subst_subst_ne' e x y v v' :
  x ≠ y →
  subst' x v (subst' y v' e) = subst' y v' (subst' x v e).
Proof.
  destruct x, y; simpl; auto using subst_subst_ne with congruence.
Qed.

Lemma subst_rec' f y e x v :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x v (Rec f y e) = Rec f y e.
Proof.
  intros. destruct x; simplify_option_eq; naive_solver.
Qed.
Lemma subst_rec_ne' f y e x v :
  (x ≠ f ∨ f = BAnon) →
  (x ≠ y ∨ y = BAnon) →
  subst' x v (Rec f y e) = Rec f y (subst' x v e).
Proof.
  intros. destruct x; simplify_option_eq; naive_solver.
Qed.
