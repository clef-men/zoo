From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  clst__types
  clst__code.
From zoo Require Import
  options.

Implicit Types v t fn : val.

Inductive clist :=
  | ClistClosed
  | ClistOpen
  | ClistCons v (cvs : clist).
Implicit Types cvs : clist.

Fixpoint clist_to_val cvs :=
  match cvs with
  | ClistClosed =>
      §ClstClosed
  | ClistOpen =>
      §ClstOpen
  | ClistCons v cvs =>
      ‘ClstCons( v, clist_to_val cvs )
  end%V.
Coercion clist_to_val : clist >-> val.

#[global] Instance clist_to_val_inj :
  Inj (=) (≈@{val}) clist_to_val.
Proof.
  intros cvs1. induction cvs1 as [| | v1 cvs1 IH]; intros [| | v2 cvs2]; [naive_solver.. |].
  intros (_ & _ & [= -> ->%val_similar_refl%IH]) => //.
Qed.
#[global] Instance clist_to_val_physical cvs :
  ValPhysical (clist_to_val cvs).
Proof.
  destruct cvs => //.
Qed.

Fixpoint list_to_clist_open vs :=
  match vs with
  | [] =>
      ClistOpen
  | v :: vs =>
      ClistCons v (list_to_clist_open vs)
  end.
Fixpoint list_to_clist_closed vs :=
  match vs with
  | [] =>
      ClistClosed
  | v :: vs =>
      ClistCons v (list_to_clist_closed vs)
  end.

#[global] Instance list_to_clist_open_inj :
  Inj (=) (=) list_to_clist_open.
Proof.
  intros vs1. induction vs1 as [| v1 vs1 IH]; intros [| v2 vs2]; naive_solver.
Qed.
#[global] Instance list_to_clist_closed_inj :
  Inj (=) (=) list_to_clist_closed.
Proof.
  intros vs1. induction vs1 as [| v1 vs1 IH]; intros [| v2 vs2]; naive_solver.
Qed.
Lemma list_to_clist_open_closed vs1 vs2 :
  list_to_clist_open vs1 ≠ list_to_clist_closed vs2.
Proof.
  move: vs2. induction vs1; destruct vs2; naive_solver.
Qed.
Lemma list_to_clist_open_not_closed vs :
  list_to_clist_open vs ≠ ClistClosed.
Proof.
  apply (list_to_clist_open_closed vs []).
Qed.
Lemma list_to_clist_open_not_closed' vs :
  ClistClosed ≠ list_to_clist_open vs.
Proof.
  symmetry. apply list_to_clist_open_not_closed.
Qed.

Fixpoint clist_app vs1 cvs2 :=
  match vs1 with
  | [] =>
      cvs2
  | v :: vs1 =>
      ClistCons v (clist_app vs1 cvs2)
  end.

Lemma clist_app_open {vs1 cvs2} vs2 :
  cvs2 = list_to_clist_open vs2 →
  clist_app vs1 cvs2 = list_to_clist_open (vs1 ++ vs2).
Proof.
  move: cvs2 vs2. induction vs1; first done.
  intros * ->. f_equal/=. naive_solver.
Qed.
Lemma clist_app_ClistOpen vs :
  clist_app vs ClistOpen = list_to_clist_open vs.
Proof.
  rewrite (clist_app_open []) // right_id //.
Qed.
Lemma clist_app_closed {vs1 cvs2} vs2 :
  cvs2 = list_to_clist_closed vs2 →
  clist_app vs1 cvs2 = list_to_clist_closed (vs1 ++ vs2).
Proof.
  move: cvs2 vs2. induction vs1; first done.
  intros * ->. f_equal/=. naive_solver.
Qed.
Lemma clist_app_ClistClosed vs :
  clist_app vs ClistClosed = list_to_clist_closed vs.
Proof.
  rewrite (clist_app_closed []) // right_id //.
Qed.
Lemma clist_app_assoc vs1 vs2 cvs :
  clist_app (vs1 ++ vs2) cvs = clist_app vs1 (clist_app vs2 cvs).
Proof.
  induction vs1; f_equal/=; done.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma wp_match_clist_open vs e1 x2 e2 Φ :
    WP subst' x2 (list_to_clist_open vs) e2 {{ Φ }} ⊢
    WP match: list_to_clist_open vs with ClstClosed => e1 |_ as: x2 => e2 end {{ Φ }}.
  Proof.
    destruct vs; iSteps.
  Qed.

  Lemma clst_app_spec {t1} vs1 {t2} cvs2 :
    t1 = list_to_clist_open vs1 →
    t2 = cvs2 →
    {{{
      True
    }}}
      clst_app t1 t2
    {{{
      RET clist_app vs1 cvs2 : val;
      True
    }}}.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1 t2 cvs2).
    all: iIntros (-> ->) "%Φ _ HΦ".
    all: wp_rec.
    - iSteps.
    - wp_smart_apply ("IH" with "[//]"); iSteps.
  Qed.

  Lemma clst_rev_app_spec {t1} vs1 {t2} cvs2 :
    t1 = list_to_clist_open vs1 →
    t2 = cvs2 →
    {{{
      True
    }}}
      clst_rev_app t1 t2
    {{{
      RET clist_app (reverse vs1) cvs2 : val;
      True
    }}}.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1 t2 cvs2).
    all: iIntros (-> ->) "%Φ _ HΦ".
    all: wp_rec.
    - iSteps.
    - wp_pures.
      wp_smart_apply ("IH" $! _ _ (ClistCons v1 cvs2) with "[//]"); iSteps.
      rewrite reverse_cons clist_app_assoc. iSteps.
  Qed.

  #[local] Lemma clst_iter_spec_aux vs_left Ψ vs fn t vs_right :
    vs = vs_left ++ vs_right →
    t = list_to_clist_open vs_right →
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
      clst_iter fn t
    {{{
      RET ();
      Ψ vs
    }}}.
  Proof.
    iIntros "%Hvs %Ht %Φ (HΨ & Hfn) HΦ".
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left t Hvs Ht).
    all: subst; simpl; rewrite right_id; wp_rec.
    1: iSteps.
    iDestruct "Hfn" as "(H & Hfn)".
    wp_smart_apply (wp_wand with "(H HΨ)") as (res) "(-> & HΨ)".
    wp_smart_apply ("IH" $! (vs_left ++ [v]) with "[] [//] HΨ [Hfn]").
    { rewrite -assoc //. }
    { iApply (big_sepL_impl with "Hfn"). iIntros "!> %i %w %Hlookup Hfn HΨ".
      rewrite -!assoc. iSteps.
    }
    iSteps.
  Qed.
  Lemma clst_iter_spec Ψ t vs fn :
    t = list_to_clist_open vs →
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
      clst_iter fn t
    {{{
      RET ();
      Ψ vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    iApply (clst_iter_spec_aux [] Ψ with "[$HΨ $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma clst_iter_spec_disentangled Ψ t vs fn :
    t = list_to_clist_open vs →
    {{{
      [∗ list] v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ v
        }}
    }}}
      clst_iter fn t
    {{{
      RET ();
      [∗ list] v ∈ vs,
        Ψ v
    }}}.
  Proof.
    iIntros "%Ht %Φ Hfn HΦ".
    iInduction vs as [| v vs] "IH" forall (t Ht).
    all: subst; simpl; wp_rec.
    1: iSteps.
    iDestruct "Hfn" as "(H & Hfn)".
    wp_smart_apply (wp_wand with "H") as (res) "(-> & HΨ)".
    wp_smart_apply ("IH" with "[//] Hfn").
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque clst_app.
#[global] Opaque clst_rev_app.
#[global] Opaque clst_iter.
