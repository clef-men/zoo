Require Import iris.algebra.ofe.

Require Import zoo.prelude.

Ltac f_equiv :=
  clean_flip;
  match goal with
  | |- _ ?x ?x =>
      fast_reflexivity
  (* [pointwise_relation] *)
  | |- pointwise_relation _ _ _ _ =>
      intros ?
  (* match *)
  | |- ?R (match ?x with _ => _ end) (match ?x with _ => _ end) =>
      destruct x
  | H: ?R ?x ?y |- ?R2 (match ?x with _ => _ end) (match ?y with _ => _ end) =>
      destruct_clear H
  (* same relation *)
    (* arity 0 *)
  | |- ?R (?f _) (?f _) =>
      apply (_ : Proper (R ==> R) f)
  | |- ?R (?f _ _) (?f _ _) =>
      apply (_ : Proper (R ==> R ==> R) f)
  | |- ?R (?f _ _ _) (?f _ _ _) =>
      apply (_ : Proper (R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _) (?f _ _ _ _) =>
      apply (_ : Proper (R ==> R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _ _) (?f _ _ _ _ _) =>
      apply (_ : Proper (R ==> R ==> R ==> R ==> R ==> R) f)
    (* arity 1 *)
  | |- ?R _ (?f _) (?f _) =>
      apply (_ : Proper (R _ ==> R _) f)
  | |- ?R _ (?f _ _) (?f _ _) =>
      apply (_ : Proper (R _ ==> R _ ==> R _) f)
  | |- ?R _ (?f _ _ _) (?f _ _ _) =>
      apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _) f)
  | |- ?R _ (?f _ _ _ _) (?f _ _ _ _) =>
      apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> R _) f)
  | |- ?R _ (?f _ _ _ _ _) (?f _ _ _ _ _) =>
      apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> R _ ==> R _) f)
    (* arity 2 *)
  | |- ?R _ _ (?f _) (?f _) =>
      apply (_ : Proper (R _ _ ==> R _ _) f)
  | |- ?R _ _ (?f _ _) (?f _ _) =>
      apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _) f)
  | |- ?R _ _ (?f _ _ _) (?f _ _ _) =>
      apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _) f)
  | |- ?R _ _ (?f _ _ _ _) (?f _ _ _ _) =>
      apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _) f)
  | |- ?R _ _ (?f _ _ _ _ _) (?f _ _ _ _ _) =>
      apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _) f)
    (* arity 3 *)
  | |- ?R _ _ _ (?f _) (?f _) =>
      apply (_ : Proper (R _ _ _ ==> R _ _ _) f)
  | |- ?R _ _ _ (?f _ _) (?f _ _) =>
      apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _) f)
  | |- ?R _ _ _ (?f _ _ _) (?f _ _ _) =>
      apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _) f)
  | |- ?R _ _ _ (?f _ _ _ _) (?f _ _ _ _) =>
      apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _) f)
  | |- ?R _ _ _ (?f _ _ _ _ _) (?f _ _ _ _ _) =>
      apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _) f)
  (* different function symbols but same arguments *)
  | H: _ ?f ?g |- ?R (?f ?x0) (?g ?x0) =>
      by apply H
  | H: _ ?f ?g |- ?R (?f ?x0 ?x1) (?g ?x0 ?x1) =>
      by apply H
  | H: _ ?f ?g |- ?R (?f ?x0 ?x1 ?x2) (?g ?x0 ?x1 ?x2) =>
      by apply H
  | H: _ ?f ?g |- ?R (?f ?x0 ?x1 ?x2 ?x3) (?g ?x0 ?x1 ?x2 ?x3) =>
      by apply H
  (* Iris fallback *)
  | |- dist_later _ _ _ =>
      apply dist_dist_later
  (* general fallback *)
  | |- ?R (?f _) _ =>
      apply (_ : Proper (_ ==> R) f)
  | |- ?R (?f _ _) _ =>
      apply (_ : Proper (_ ==> _ ==> R) f)
  | |- ?R (?f _ _ _) _ =>
      apply (_ : Proper (_ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _) _ =>
      apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _ _) _ =>
      apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  end;
  try fast_reflexivity.

Ltac solve_proper :=
  solve_proper_core ltac:(fun _ =>
    f_equiv
  ).

Ltac solve_contractive :=
  solve_proper_core ltac:(fun _ =>
    first
    [ f_contractive
    | f_equiv
    ]
  ).
