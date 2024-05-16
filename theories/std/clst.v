From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base.
From zoo Require Import
  options.

Implicit Types v t fn : val.

Notation "'ClstClosed'" := (
  in_type "clst" 0
)(in custom zoo_tag
).
Notation "'ClstOpen'" := (
  in_type "clst" 1
)(in custom zoo_tag
).
Notation "'ClstCons'" := (
  in_type "clst" 2
)(in custom zoo_tag
).

Inductive clist :=
  | ClistClosed
  | ClistOpen
  | ClistCons v (cls : clist).
Implicit Types cls : clist.

Fixpoint clist_to_val cls :=
  match cls with
  | ClistClosed =>
      §ClstClosed
  | ClistOpen =>
      §ClstOpen
  | ClistCons v cls =>
      ’ClstCons{ v, clist_to_val cls }
  end.
Coercion clist_to_val : clist >-> val.

#[global] Instance clist_to_val_inj :
  Inj (=) val_eq clist_to_val.
Proof.
  intros cls1. induction cls1 as [| | v1 cls1 IH]; intros [| | v2 cls2]; [naive_solver.. |].
  intros (_ & [= -> ->%eq_val_eq%IH]). done.
Qed.
#[global] Instance clist_to_val_physical cls :
  ValPhysical (clist_to_val cls).
Proof.
  destruct cls; done.
Qed.

Fixpoint list_to_clist_open ls :=
  match ls with
  | [] =>
      ClistOpen
  | v :: ls =>
      ClistCons v (list_to_clist_open ls)
  end.
Fixpoint list_to_clist_closed ls :=
  match ls with
  | [] =>
      ClistClosed
  | v :: ls =>
      ClistCons v (list_to_clist_closed ls)
  end.

#[global] Instance list_to_clist_open_inj :
  Inj (=) (=) list_to_clist_open.
Proof.
  intros ls1. induction ls1 as [| v1 ls1 IH]; intros [| v2 ls2]; naive_solver.
Qed.
#[global] Instance list_to_clist_closed_inj :
  Inj (=) (=) list_to_clist_closed.
Proof.
  intros ls1. induction ls1 as [| v1 ls1 IH]; intros [| v2 ls2]; naive_solver.
Qed.
Lemma list_to_clist_open_closed ls1 ls2 :
  list_to_clist_open ls1 ≠ list_to_clist_closed ls2.
Proof.
  move: ls2. induction ls1; destruct ls2; naive_solver.
Qed.
Lemma list_to_clist_open_not_closed ls :
  list_to_clist_open ls ≠ ClistClosed.
Proof.
  apply (list_to_clist_open_closed ls []).
Qed.
Lemma list_to_clist_open_not_closed' ls :
  ClistClosed ≠ list_to_clist_open ls.
Proof.
  symmetry. apply list_to_clist_open_not_closed.
Qed.

Fixpoint clist_app ls1 cls2 :=
  match ls1 with
  | [] =>
      cls2
  | v :: ls1 =>
      ClistCons v (clist_app ls1 cls2)
  end.

Lemma clist_app_open {ls1 cls2} ls2 :
  cls2 = list_to_clist_open ls2 →
  clist_app ls1 cls2 = list_to_clist_open (ls1 ++ ls2).
Proof.
  move: cls2 ls2. induction ls1; first done.
  intros * ->. f_equal/=. naive_solver.
Qed.
Lemma clist_app_ClistOpen ls :
  clist_app ls ClistOpen = list_to_clist_open ls.
Proof.
  rewrite (clist_app_open []) // right_id //.
Qed.
Lemma clist_app_closed {ls1 cls2} ls2 :
  cls2 = list_to_clist_closed ls2 →
  clist_app ls1 cls2 = list_to_clist_closed (ls1 ++ ls2).
Proof.
  move: cls2 ls2. induction ls1; first done.
  intros * ->. f_equal/=. naive_solver.
Qed.
Lemma clist_app_ClistClosed ls :
  clist_app ls ClistClosed = list_to_clist_closed ls.
Proof.
  rewrite (clist_app_closed []) // right_id //.
Qed.
Lemma clist_app_assoc ls1 ls2 cls :
  clist_app (ls1 ++ ls2) cls = clist_app ls1 (clist_app ls2 cls).
Proof.
  induction ls1; f_equal/=; done.
Qed.

Definition clst_app : val :=
  rec: "clst_app" "t1" "t2" :=
    match: "t1" with
    | ClstOpen =>
        "t2"
    | ClstCons "v" "t1" =>
        ‘ClstCons{ "v", "clst_app" "t1" "t2" }
    end.

Definition clst_rev_app : val :=
  rec: "clst_rev_app" "t1" "t2" :=
    match: "t1" with
    | ClstOpen =>
        "t2"
    | ClstCons "v" "t1" =>
        "clst_rev_app" "t1" ‘ClstCons{ "v", "t2" }
    end.

Definition clst_iter : val :=
  rec: "clst_iter" "t" "fn" :=
    match: "t" with
    | ClstOpen =>
        ()
    | ClstCons "v" "t" =>
        "fn" "v" ;;
        "clst_iter" "t" "fn"
    end.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma wp_match_clist_open ls e1 x2 e2 Φ :
    WP subst' x2 (list_to_clist_open ls) e2 {{ Φ }} ⊢
    WP match: list_to_clist_open ls with ClstClosed => e1 |_ as: x2 => e2 end {{ Φ }}.
  Proof.
    destruct ls; iSteps.
  Qed.

  Lemma clst_app_spec {t1} ls1 {t2} cls2 :
    t1 = list_to_clist_open ls1 →
    t2 = cls2 →
    {{{ True }}}
      clst_app t1 t2
    {{{
      RET clist_app ls1 cls2 : val; True
    }}}.
  Proof.
    iInduction ls1 as [| v1 ls1] "IH" forall (t1 t2 cls2).
    all: iIntros (-> ->) "%Φ _ HΦ".
    all: wp_rec.
    - iSteps.
    - wp_smart_apply ("IH" with "[//]"); iSteps.
  Qed.

  Lemma clst_rev_app_spec {t1} ls1 {t2} cls2 :
    t1 = list_to_clist_open ls1 →
    t2 = cls2 →
    {{{ True }}}
      clst_rev_app t1 t2
    {{{
      RET clist_app (reverse ls1) cls2 : val; True
    }}}.
  Proof.
    iInduction ls1 as [| v1 ls1] "IH" forall (t1 t2 cls2).
    all: iIntros (-> ->) "%Φ _ HΦ".
    all: wp_rec.
    - iSteps.
    - wp_pures.
      wp_smart_apply ("IH" $! _ _ (ClistCons v1 cls2) with "[//]"); iSteps.
      rewrite reverse_cons clist_app_assoc. iSteps.
  Qed.

  #[local] Lemma clst_iter_spec_aux Ψ {t} ls ls_left ls_right fn :
    ls = ls_left ++ ls_right →
    t = list_to_clist_open ls_right →
    {{{
      ▷ Ψ ls_left ∗
      ( [∗ list] i ↦ v ∈ ls_right,
        Ψ (ls_left ++ take i ls_right) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (ls_left ++ take i ls_right ++ [v])
        }}
      )
    }}}
      clst_iter t fn
    {{{
      RET ();
      Ψ ls
    }}}.
  Proof.
    iIntros "%Hls %Ht %Φ (HΨ & Hfn) HΦ".
    iInduction ls_right as [| v ls_right] "IH" forall (t ls_left Hls Ht).
    all: subst; simpl; rewrite right_id; wp_rec.
    1: iSteps.
    iDestruct "Hfn" as "(H & Hfn)".
    wp_smart_apply (wp_wand with "(H HΨ)") as (res) "(-> & HΨ)".
    wp_smart_apply ("IH" $! _ (ls_left ++ [v]) with "[] [//] HΨ [Hfn]").
    { rewrite -assoc //. }
    { iApply (big_sepL_impl with "Hfn"). iIntros "!> %i %w %Hlookup Hfn HΨ".
      rewrite -!assoc. iSteps.
    }
    iSteps.
  Qed.
  Lemma clst_iter_spec Ψ {t} ls fn :
    t = list_to_clist_open ls →
    {{{
      ▷ Ψ [] ∗
      ( [∗ list] i ↦ v ∈ ls,
        Ψ (take i ls) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (take i ls ++ [v])
        }}
      )
    }}}
      clst_iter t fn
    {{{
      RET ();
      Ψ ls
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    iApply (clst_iter_spec_aux Ψ ls [] ls with "[$HΨ $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma clst_iter_spec_disentangled Ψ {t} ls fn :
    t = list_to_clist_open ls →
    {{{
      [∗ list] v ∈ ls,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ v
        }}
    }}}
      clst_iter t fn
    {{{
      RET ();
      [∗ list] v ∈ ls,
        Ψ v
    }}}.
  Proof.
    iIntros "%Ht %Φ Hfn HΦ".
    iInduction ls as [| v ls] "IH" forall (t Ht).
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
