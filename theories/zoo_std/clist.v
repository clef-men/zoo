Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.clist__types.
Require Export zoo_std.clist__code.
Require Import zoo.options.

Implicit Type v t fn : val.

Inductive clist :=
  | ClistClosed
  | ClistOpen
  | ClistCons v (cvs : clist).
Implicit Type cvs : clist.

Fixpoint clist۰to_val cvs :=
  match cvs with
  | ClistClosed =>
      §ClistClosed
  | ClistOpen =>
      §ClistOpen
  | ClistCons v cvs =>
      ‘ClistCons[ v, clist۰to_val cvs ]
  end%V.
Coercion clist۰to_val : clist >-> val.

#[global] Instance clist۰to_valｰinjｰsimilar :
  Inj (=) (≈@{val}) clist۰to_val.
Proof.
  intros cvs1. induction cvs1 as [| | v1 cvs1 IH]; intros [| | v2 cvs2]; try done.
  intros (_ & _ & [= <- <-%valｰsimilarｰrefl%IH]). done.
Qed.
#[global] Instance clist۰to_valｰinj :
  Inj (=) (=) clist۰to_val.
Proof.
  intros ?* ->%valｰsimilarｰrefl%(inj _). done.
Qed.

Fixpoint list۰to_clist_open vs :=
  match vs with
  | [] =>
      ClistOpen
  | v :: vs =>
      ClistCons v (list۰to_clist_open vs)
  end.
Fixpoint list۰to_clist_closed vs :=
  match vs with
  | [] =>
      ClistClosed
  | v :: vs =>
      ClistCons v (list۰to_clist_closed vs)
  end.

#[global] Instance list۰to_clist_openｰinj :
  Inj (=) (=) list۰to_clist_open.
Proof.
  intros vs1. induction vs1 as [| v1 vs1 IH]; intros [| v2 vs2]; naive_solver.
Qed.
#[global] Instance list۰to_clist_closedｰinj :
  Inj (=) (=) list۰to_clist_closed.
Proof.
  intros vs1. induction vs1 as [| v1 vs1 IH]; intros [| v2 vs2]; naive_solver.
Qed.
Lemma list۰to_clistｰopenｰclosed vs1 vs2 :
  list۰to_clist_open vs1 ≠ list۰to_clist_closed vs2.
Proof.
  move: vs2. induction vs1; destruct vs2; naive_solver.
Qed.
Lemma list۰to_clist_openｰnotｰclosed vs :
  list۰to_clist_open vs ≠ ClistClosed.
Proof.
  apply (list۰to_clistｰopenｰclosed vs []).
Qed.
Lemma list۰to_clist_openｰnotｰclosed' vs :
  ClistClosed ≠ list۰to_clist_open vs.
Proof.
  symmetry. apply list۰to_clist_openｰnotｰclosed.
Qed.

Fixpoint clist۰app vs1 cvs2 :=
  match vs1 with
  | [] =>
      cvs2
  | v :: vs1 =>
      ClistCons v (clist۰app vs1 cvs2)
  end.

Lemma clist۰appｰopen {vs1 cvs2} vs2 :
  cvs2 = list۰to_clist_open vs2 →
  clist۰app vs1 cvs2 = list۰to_clist_open (vs1 ++ vs2).
Proof.
  move: cvs2 vs2. induction vs1; first done.
  intros * ->. f_equal/=. naive_solver.
Qed.
Lemma clist۰appｰClistOpen vs :
  clist۰app vs ClistOpen = list۰to_clist_open vs.
Proof.
  rewrite (clist۰appｰopen []) // right_id //.
Qed.
Lemma clist۰appｰclosed {vs1 cvs2} vs2 :
  cvs2 = list۰to_clist_closed vs2 →
  clist۰app vs1 cvs2 = list۰to_clist_closed (vs1 ++ vs2).
Proof.
  move: cvs2 vs2. induction vs1; first done.
  intros * ->. f_equal/=. naive_solver.
Qed.
Lemma clist۰appｰClistClosed vs :
  clist۰app vs ClistClosed = list۰to_clist_closed vs.
Proof.
  rewrite (clist۰appｰclosed []) // right_id //.
Qed.
Lemma clist۰appｰassoc vs1 vs2 cvs :
  clist۰app (vs1 ++ vs2) cvs = clist۰app vs1 (clist۰app vs2 cvs).
Proof.
  induction vs1; f_equal/=; done.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma wpｰmatchｰclistｰopen vs e1 x2 e2 Φ :
    WP subst' x2 (list۰to_clist_open vs) e2 {{ Φ }} ⊢
    WP 𝗺𝗮𝘁𝗰𝗵 list۰to_clist_open vs 𝘄𝗶𝘁𝗵 ClistClosed -> e1 | ⎽ 𝗮𝘀: x2 -> e2 𝗲𝗻𝗱 {{ Φ }}.
  Proof.
    destruct vs; iSteps.
  Qed.

  Lemma clist٠appｰspec {t1} vs1 {t2} cvs2 :
    t1 = list۰to_clist_open vs1 →
    t2 = cvs2 →
    {{{
      True
    }}}
      clist٠app t1 t2
    {{{
      RET clist۰app vs1 cvs2;
      True
    }}}.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1 t2 cvs2).
    all: iIntros (-> ->) "%Φ _ HΦ".
    all: wp۰rec.
    - iSteps.
    - wp۰apply+ ("IH" with "[//]"); iSteps.
  Qed.

  Lemma clist٠rev_appｰspec {t1} vs1 {t2} cvs2 :
    t1 = list۰to_clist_open vs1 →
    t2 = cvs2 →
    {{{
      True
    }}}
      clist٠rev_app t1 t2
    {{{
      RET clist۰app (reverse vs1) cvs2;
      True
    }}}.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1 t2 cvs2).
    all: iIntros (-> ->) "%Φ _ HΦ".
    all: wp۰rec.
    - iSteps.
    - wp۰pures.
      wp۰apply+ ("IH" $! _ _ (ClistCons v1 cvs2) with "[//]"); iSteps.
      rewrite reverse_cons clist۰appｰassoc. iSteps.
  Qed.

  #[local] Lemma clist٠iterｰspecｰaux vs_left Ψ vs fn t vs_right :
    vs = vs_left ++ vs_right →
    t = list۰to_clist_open vs_right →
    {{{
      ▷ Ψ vs_left ∗
      ( [∗ list] i ↦ v ∈ vs_right,
        Ψ (vs_left ++ take i vs_right) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (vs_left ++ take i vs_right ++ [v])
        }}
      )
    }}}
      clist٠iter fn t
    {{{
      RET ();
      Ψ vs
    }}}.
  Proof.
    iIntros "%Hvs %Ht %Φ (HΨ & Hfn) HΦ".
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left t Hvs Ht).
    all: subst; simpl; rewrite right_id; wp۰rec.
    1: iSteps.
    iDestruct "Hfn" as "(H & Hfn)".
    wp۰apply+ (wpｰwand with "(H HΨ)") as (res) "(-> & HΨ)".
    wp۰apply+ ("IH" $! (vs_left ++ [v]) with "[] [//] HΨ [Hfn]").
    { rewrite -assoc //. }
    { iApply (big_sepL_impl with "Hfn"). iIntros "!> %i %w %Hlookup Hfn HΨ".
      rewrite -!assoc. iSteps.
    }
    iSteps.
  Qed.
  Lemma clist٠iterｰspec Ψ t vs fn :
    t = list۰to_clist_open vs →
    {{{
      ▷ Ψ [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (take i vs ++ [v])
        }}
      )
    }}}
      clist٠iter fn t
    {{{
      RET ();
      Ψ vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    iApply (clist٠iterｰspecｰaux [] Ψ with "[$HΨ $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma clist٠iterｰspecｰdisentangled Ψ t vs fn :
    t = list۰to_clist_open vs →
    {{{
      [∗ list] v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ v
        }}
    }}}
      clist٠iter fn t
    {{{
      RET ();
      [∗ list] v ∈ vs,
        Ψ v
    }}}.
  Proof.
    iIntros "%Ht %Φ Hfn HΦ".
    iInduction vs as [| v vs] "IH" forall (t Ht).
    all: subst; simpl; wp۰rec.
    1: iSteps.
    iDestruct "Hfn" as "(H & Hfn)".
    wp۰apply+ (wpｰwand with "H") as (res) "(-> & HΨ)".
    wp۰apply+ ("IH" with "[//] Hfn").
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.clist__opaque.
