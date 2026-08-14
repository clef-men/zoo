Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.base.
Require Export zoo_saturn.tqueue_mpmc_2__code.
Require Import zoo_saturn.tqueue_mpmc_2__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v : val.
Implicit Type vs : list val.

Class TqueueMpmc2G Σ `{zoo۰G : !ZooG Σ} :=
  {
  }.

Definition tqueue_mpmc_2۰Σ :=
  #[
  ].
#[global] Instance subGｰtqueue_mpmc_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG tqueue_mpmc_2۰Σ Σ →
  TqueueMpmc2G Σ.
Proof.
  (* solve_inG. *)
Qed.

Module base.
  Section tqueue_mpmc_2۰G.
    Context `{tqueue_mpmc_2۰G : TqueueMpmc2G Σ}.

    Implicit Type t : location.

    Record tqueue_mpmc_2۰name :=
      {
      }.
    Implicit Type γ : tqueue_mpmc_2۰name.

    #[global] Instance tqueue_mpmc_2۰nameｰeq_dec : EqDecision tqueue_mpmc_2۰name :=
      ltac:(solve_decision).
    #[global] Instance tqueue_mpmc_2۰nameｰcountable :
      Countable tqueue_mpmc_2۰name.
    Proof.
      solve_countable.
    Qed.

    Definition tqueue_mpmc_2۰inv t γ (ι : namespace) : iProp Σ.
    Admitted.

    Definition tqueue_mpmc_2۰model γ vs : iProp Σ.
    Admitted.

    Definition tqueue_mpmc_2۰full γ : iProp Σ.
    Admitted.

    Definition tqueue_mpmc_2۰nonfull γ : iProp Σ.
    Admitted.

    Definition tqueue_mpmc_2۰finished γ : iProp Σ.
    Admitted.

    #[global] Instance tqueue_mpmc_2۰modelｰtimeless γ vs :
      Timeless (tqueue_mpmc_2۰model γ vs).
    Proof.
    Admitted.

    #[global] Instance tqueue_mpmc_2۰invｰpersistent t γ ι :
      Persistent (tqueue_mpmc_2۰inv t γ ι).
    Proof.
    Admitted.
    #[global] Instance tqueue_mpmc_2۰fullｰpersistent γ :
      Persistent (tqueue_mpmc_2۰full γ).
    Proof.
    Admitted.
    #[global] Instance tqueue_mpmc_2۰finishedｰpersistent γ :
      Persistent (tqueue_mpmc_2۰finished γ).
    Proof.
    Admitted.

    Lemma tqueue_mpmc_2۰modelｰexclusive γ vs1 vs2 :
      tqueue_mpmc_2۰model γ vs1 -∗
      tqueue_mpmc_2۰model γ vs2 -∗
      False.
    Proof.
    Admitted.

    Lemma tqueue_mpmc_2ｰfullｰnonfull γ :
      tqueue_mpmc_2۰full γ -∗
      tqueue_mpmc_2۰nonfull γ -∗
      False.
    Proof.
    Admitted.

    Lemma tqueue_mpmc_2ｰmodelｰfinished t γ ι vs E :
      ↑ι ⊆ E →
      tqueue_mpmc_2۰inv t γ ι -∗
      tqueue_mpmc_2۰model γ vs -∗
      tqueue_mpmc_2۰finished γ ={E}=∗
        ⌜vs = []⌝ ∗
        tqueue_mpmc_2۰model γ vs.
    Proof.
    Admitted.

    Lemma tqueue_mpmc_2٠createｰspec ι cap :
      (0 ≤ cap)%Z →
      {{{
        True
      }}}
        tqueue_mpmc_2٠create #cap
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        tqueue_mpmc_2۰inv t γ ι ∗
        tqueue_mpmc_2۰model γ []
      }}}.
    Proof.
    Admitted.

    Lemma tqueue_mpmc_2٠makeｰspec ι cap v :
      (0 ≤ cap)%Z →
      {{{
        True
      }}}
        tqueue_mpmc_2٠make #cap v
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        tqueue_mpmc_2۰inv t γ ι ∗
        tqueue_mpmc_2۰model γ [v]
      }}}.
    Proof.
    Admitted.

    Lemma tqueue_mpmc_2٠is_emptyｰspec t γ ι :
      <<<
        tqueue_mpmc_2۰inv t γ ι
      | ∀∀ vs,
        tqueue_mpmc_2۰model γ vs
      >>>
        tqueue_mpmc_2٠is_empty #t @ ↑ι
      <<<
        tqueue_mpmc_2۰model γ vs
      | b,
        RET #b;
        ⌜if b then vs = [] else True⌝
      >>>.
    Proof.
    Admitted.

    Lemma tqueue_mpmc_2٠pushｰspec t γ ι v E Φ :
      tqueue_mpmc_2۰inv t γ ι -∗
      ▷ (
        |={⊤ ∖ ↑ι, E}=>
        ∃ vs,
        tqueue_mpmc_2۰model γ vs ∗
          ∀ b,
          ( if b then
              tqueue_mpmc_2۰model γ (vs ++ [v]) ∗
              tqueue_mpmc_2۰nonfull γ
            else
              tqueue_mpmc_2۰model γ vs ∗
              tqueue_mpmc_2۰full γ
          ) ={E}=∗
            ( if b then
                tqueue_mpmc_2۰nonfull γ
              else
                True
            ) ∗
              |={E, ⊤ ∖ ↑ι}=>
              Φ #b
      ) -∗
      WP tqueue_mpmc_2٠push #t v {{ Φ }}.
    Proof.
    Admitted.

    Lemma tqueue_mpmc_2٠popｰspec t γ ι :
      <<<
        tqueue_mpmc_2۰inv t γ ι
      | ∀∀ vs,
        tqueue_mpmc_2۰model γ vs
      >>>
        tqueue_mpmc_2٠pop #t @ ↑ι
      <<<
        ∃∃ o vs',
        tqueue_mpmc_2۰model γ vs' ∗
        ⌜ match o with
          | Something v =>
              vs = v :: vs'
          | Nothing =>
              vs' = vs
          | Anything =>
              vs = [] ∧
              vs' = vs
          end
        ⌝
      | RET o;
        if o is Anything then
          tqueue_mpmc_2۰finished γ
        else
          True
      >>>.
    Proof.
    Admitted.
  End tqueue_mpmc_2۰G.

  #[global] Opaque tqueue_mpmc_2۰inv.
  #[global] Opaque tqueue_mpmc_2۰model.
  #[global] Opaque tqueue_mpmc_2۰full.
  #[global] Opaque tqueue_mpmc_2۰nonfull.
  #[global] Opaque tqueue_mpmc_2۰finished.
End base.

Require zoo_saturn.tqueue_mpmc_2__opaque.

Section tqueue_mpmc_2۰G.
  Context `{tqueue_mpmc_2۰G : TqueueMpmc2G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition tqueue_mpmc_2۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.tqueue_mpmc_2۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition tqueue_mpmc_2۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.tqueue_mpmc_2۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition tqueue_mpmc_2۰full t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.tqueue_mpmc_2۰full γ.
  #[local] Instance : CustomIpat "full" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & Hmeta{_{}}
      & Hfull{_{}}
      )
    ".

  Definition tqueue_mpmc_2۰nonfull t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.tqueue_mpmc_2۰nonfull γ.
  #[local] Instance : CustomIpat "nonfull" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & Hmeta{_{}}
      & Hnonfull{_{}}
      )
    ".

  Definition tqueue_mpmc_2۰finished t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.tqueue_mpmc_2۰finished γ.
  #[local] Instance : CustomIpat "finished" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & Hmeta{_{}}
      & Hfinished{_{}}
      )
    ".

  #[global] Instance tqueue_mpmc_2۰modelｰtimeless t vs :
    Timeless (tqueue_mpmc_2۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance tqueue_mpmc_2۰invｰpersistent t ι :
    Persistent (tqueue_mpmc_2۰inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance tqueue_mpmc_2۰fullｰpersistent t :
    Persistent (tqueue_mpmc_2۰full t).
  Proof.
    apply _.
  Qed.
  #[global] Instance tqueue_mpmc_2۰finishedｰpersistent t :
    Persistent (tqueue_mpmc_2۰finished t).
  Proof.
    apply _.
  Qed.

  Lemma tqueue_mpmc_2۰modelｰexclusive t vs1 vs2 :
    tqueue_mpmc_2۰model t vs1 -∗
    tqueue_mpmc_2۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.tqueue_mpmc_2۰modelｰexclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma tqueue_mpmc_2ｰfullｰnonfull t :
    tqueue_mpmc_2۰full t -∗
    tqueue_mpmc_2۰nonfull t -∗
    False.
  Proof.
    iIntros "(:full =1) (:nonfull =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.tqueue_mpmc_2ｰfullｰnonfull with "Hfull_1 Hnonfull_2").
  Qed.

  Lemma tqueue_mpmc_2ｰmodelｰfinished t ι vs E :
    ↑ι ⊆ E →
    tqueue_mpmc_2۰inv t ι -∗
    tqueue_mpmc_2۰model t vs -∗
    tqueue_mpmc_2۰finished t ={E}=∗
      ⌜vs = []⌝ ∗
      tqueue_mpmc_2۰model t vs.
  Proof.
    iIntros "% (:inv =1) (:model =2) (:finished =3)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (metaｰagree with "Hmeta_2 Hmeta_3") as %<-.
    iMod (base.tqueue_mpmc_2ｰmodelｰfinished with "Hinv_1 Hmodel_2 Hfinished_3") as "($ & $)"; first done.
    iFrameSteps.
  Qed.

  Lemma tqueue_mpmc_2٠createｰspec ι cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      tqueue_mpmc_2٠create #cap
    {{{
      t
    , RET t;
      tqueue_mpmc_2۰inv t ι ∗
      tqueue_mpmc_2۰model t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.tqueue_mpmc_2٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)"; first done.
    iMod (metaｰset γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma tqueue_mpmc_2٠makeｰspec ι cap v :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      tqueue_mpmc_2٠make #cap v
    {{{
      t
    , RET t;
      tqueue_mpmc_2۰inv t ι ∗
      tqueue_mpmc_2۰model t [v]
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.tqueue_mpmc_2٠makeｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)"; first done.
    iMod (metaｰset γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma tqueue_mpmc_2٠is_emptyｰspec t ι :
    <<<
      tqueue_mpmc_2۰inv t ι
    | ∀∀ vs,
      tqueue_mpmc_2۰model t vs
    >>>
      tqueue_mpmc_2٠is_empty t @ ↑ι
    <<<
      tqueue_mpmc_2۰model t vs
    | b,
      RET #b;
      ⌜if b then vs = [] else True⌝
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.tqueue_mpmc_2٠is_emptyｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma tqueue_mpmc_2٠pushｰspec t ι v E Φ :
    tqueue_mpmc_2۰inv t ι -∗
    ▷ (
      |={⊤ ∖ ↑ι, E}=>
      ∃ vs,
      tqueue_mpmc_2۰model t vs ∗
        ∀ b,
        ( if b then
            tqueue_mpmc_2۰model t (vs ++ [v]) ∗
            tqueue_mpmc_2۰nonfull t
          else
            tqueue_mpmc_2۰model t vs ∗
            tqueue_mpmc_2۰full t
        ) ={E}=∗
          ( if b then
              tqueue_mpmc_2۰nonfull t
            else
              True
          ) ∗
            |={E, ⊤ ∖ ↑ι}=>
            Φ #b
    ) -∗
    WP tqueue_mpmc_2٠push t v {{ Φ }}.
  Proof.
    iIntros "(:inv) HΦ".

    wp۰apply (base.tqueue_mpmc_2٠pushｰspec _ _ _ _ E with "[$]").
    { iMod "HΦ" as (vs) "((:model =1) & HΦ)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iFrame. iIntros "!> %b Hb".
      iMod ("HΦ" $! b with "[Hb]") as "(Hb & $)".
      { destruct b; iSteps. }
      destruct b; last iSteps.
      iDestruct "Hb" as "(:nonfull =2)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_2") as %<-. iClear "Hmeta_2".
      iFrameSteps.
    }
  Qed.

  Lemma tqueue_mpmc_2٠popｰspec t ι :
    <<<
      tqueue_mpmc_2۰inv t ι
    | ∀∀ vs,
      tqueue_mpmc_2۰model t vs
    >>>
      tqueue_mpmc_2٠pop t @ ↑ι
    <<<
      ∃∃ o vs',
      tqueue_mpmc_2۰model t vs' ∗
      ⌜ match o with
        | Something v =>
            vs = v :: vs'
        | Nothing =>
            vs' = vs
        | Anything =>
            vs = [] ∧
            vs' = vs
        end
      ⌝
    | RET o;
      if o is Anything then
        tqueue_mpmc_2۰finished t
      else
        True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.tqueue_mpmc_2٠popｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; first iSteps. iIntros "%o %vs' (Hmodel & $)".
      iFrameSteps. destruct o; iSteps.
    }
  Qed.
End tqueue_mpmc_2۰G.

#[global] Opaque tqueue_mpmc_2۰inv.
#[global] Opaque tqueue_mpmc_2۰model.
#[global] Opaque tqueue_mpmc_2۰full.
#[global] Opaque tqueue_mpmc_2۰nonfull.
#[global] Opaque tqueue_mpmc_2۰finished.
