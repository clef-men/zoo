From stdpp Require Import
  gmap
  stringmap.

From zebre Require Import
  prelude.
From zebre Require Export
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
  | Fst e
  | Snd e
  | Constr _ e
  | Fork e
  | Load e =>
     expr_closed X e
  | App e1 e2
  | Binop _ e1 e2
  | Equal e1 e2
  | Pair e1 e2
  | Alloc e1 e2
  | Store e1 e2
  | Xchg e1 e2
  | Faa e1 e2 =>
     expr_closed X e1 && expr_closed X e2
  | If e0 e1 e2
  | Case e0 e1 e2
  | Cas e0 e1 e2
  | Resolve e0 e1 e2 =>
     expr_closed X e0 && expr_closed X e1 && expr_closed X e2
  | Proph =>
      true
  end
with val_closed v :=
  match v with
  | ValLiteral _ =>
      true
  | ValRec f x e =>
      expr_closed (set_binder_insert f (set_binder_insert x ∅)) e
  | ValPair v1 v2 =>
      val_closed v1 && val_closed v2
  | ValConstr _ v =>
      val_closed v
  end.

Fixpoint subst_map (vs : gmap string val) e :=
  match e with
  | Val _ =>
      e
  | Var y =>
      if vs !! y is Some v then Val v else Var y
  | Rec f y e =>
      Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)
  | App e1 e2 =>
      App (subst_map vs e1) (subst_map vs e2)
  | Unop op e =>
      Unop op (subst_map vs e)
  | Binop op e1 e2 =>
      Binop op (subst_map vs e1) (subst_map vs e2)
  | Equal e1 e2 =>
      Equal (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 =>
      If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 =>
      Pair (subst_map vs e1) (subst_map vs e2)
  | Fst e =>
      Fst (subst_map vs e)
  | Snd e =>
      Snd (subst_map vs e)
  | Constr b e =>
      Constr b (subst_map vs e)
  | Case e0 e1 e2 =>
      Case (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Fork e =>
      Fork (subst_map vs e)
  | Alloc e1 e2 =>
      Alloc (subst_map vs e1) (subst_map vs e2)
  | Load e =>
      Load (subst_map vs e)
  | Store e1 e2 =>
      Store (subst_map vs e1) (subst_map vs e2)
  | Xchg e1 e2 =>
      Xchg (subst_map vs e1) (subst_map vs e2)
  | Cas e0 e1 e2 =>
      Cas (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Faa e1 e2 =>
      Faa (subst_map vs e1) (subst_map vs e2)
  | Proph =>
      Proph
  | Resolve e0 e1 e2 =>
      Resolve (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  end.

#[local] Instance set_unfold_elem_of_insert_binder x y X Q :
  SetUnfoldElemOf y X Q →
  SetUnfoldElemOf y (set_binder_insert x X) (Q ∨ BNamed y = x).
Proof.
  destruct 1; constructor; destruct x; set_solver.
Qed.

Lemma subst_closed X e x es :
  expr_closed X e →
  x ∉ X →
  subst x es e = e.
Proof.
  revert X. induction e=> X /=;
    rewrite ?bool_decide_spec ?andb_True => ? ?;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
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
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_closed_empty with f_equal.
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
