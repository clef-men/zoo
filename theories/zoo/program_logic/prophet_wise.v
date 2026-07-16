Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.agree.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.base.
Require Export zoo.program_logic.prophet_typed.
Require Import zoo.options.

Class ProphetWiseG Σ `{zoo۰G : !ZooG Σ} prophet :=
  { #[local] prophet_wise۰G۰full۰G :: AgreeG Σ (leibnizO (list prophet.(prophet_typed۰type)))
  ; #[local] prophet_wise۰G۰past۰G :: MonoListG Σ prophet.(prophet_typed۰type)
  }.

Definition prophet_wise۰Σ prophet :=
  #[agree۰Σ (leibnizO (list prophet.(prophet_typed۰type)))
  ; mono_list۰Σ prophet.(prophet_typed۰type)
  ].
#[global] Instance subG𑁒prophet_wise۰Σ Σ `{zoo۰G : !ZooG Σ} prophet :
  subG (prophet_wise۰Σ prophet) Σ →
  ProphetWiseG Σ prophet.
Proof.
  solve_inG.
Qed.

Section prophet_wise۰G.
  Context (prophet : prophet_typed).
  Context `{prophet_wise۰G : ProphetWiseG Σ prophet}.

  Implicit Types oproph : option prophet.(prophet_typed۰type).
  Implicit Types proph : prophet.(prophet_typed۰type).
  Implicit Types prophs : list prophet.(prophet_typed۰type).

  Record prophet_wise۰name :=
    { prophet_wise۰name۰full : gname
    ; prophet_wise۰name۰past : gname
    }.

  #[global] Instance prophet_wise۰name𑁒eq_dec : EqDecision prophet_wise۰name :=
    ltac:(solve_decision).
  #[global] Instance prophet_wise۰name𑁒countable :
    Countable prophet_wise۰name.
  Proof.
    solve_countable.
  Qed.

  Definition prophet_wise۰full γ prophs :=
    agree۰on γ.(prophet_wise۰name۰full) prophs.
  #[local] Instance : CustomIpat "full" :=
    " #Hfull{}
    ".

  Definition prophet_wise۰model pid γ past prophs : iProp Σ :=
    prophet_wise۰full γ (past ++ prophs) ∗
    mono_list۰auth γ.(prophet_wise۰name۰past) (DfracOwn 1) past ∗
    prophet_typed۰model prophet pid prophs.
  #[local] Instance : CustomIpat "model" :=
    " ( #Hfull{}
      & Hpast{}_auth
      & Hmodel{}
      )
    ".

  Definition prophet_wise۰snapshot γ past prophs : iProp Σ :=
    prophet_wise۰full γ (past ++ prophs) ∗
    mono_list۰lb γ.(prophet_wise۰name۰past) past.
  #[local] Instance : CustomIpat "snapshot" :=
    " ( #Hfull{suff}
      & #Hpast_lb
      )
    ".

  Definition prophet_wise۰lb γ lb : iProp Σ :=
    ∃ past,
    prophet_wise۰snapshot γ past lb.
  #[local] Instance : CustomIpat "lb" :=
    " ( %past{suff}
      & Hsnapshot
      )
    ".

  #[global] Instance prophet_wise۰full𑁒timeless γ prophs :
    Timeless (prophet_wise۰full γ prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰model𑁒timeless pid γ past prophs :
    Timeless (prophet_wise۰model pid γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰snapshot𑁒timeless γ past prophs :
    Timeless (prophet_wise۰snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰lb𑁒timeless γ lb :
    Timeless (prophet_wise۰lb γ lb).
  Proof.
    apply _.
  Qed.

  #[global] Instance prophet_wise۰full𑁒persistent γ prophs :
    Persistent (prophet_wise۰full γ prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰snapshot𑁒persistent γ past prophs :
    Persistent (prophet_wise۰snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰lb𑁒persistent γ lb :
    Persistent (prophet_wise۰lb γ lb).
  Proof.
    apply _.
  Qed.

  Lemma prophet_wise۰model𑁒exclusive pid γ1 past1 prophs1 γ2 past2 prophs2 :
    prophet_wise۰model pid γ1 past1 prophs1 -∗
    prophet_wise۰model pid γ2 past2 prophs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_typed۰model𑁒exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_wise۰full𑁒get pid γ past prophs :
    prophet_wise۰model pid γ past prophs ⊢
    prophet_wise۰full γ (past ++ prophs).
  Proof.
    iSteps.
  Qed.
  Lemma prophet_wise۰full𑁒get' pid γ past prophs :
    prophet_wise۰model pid γ past prophs ⊢
      ∃ prophs',
      prophet_wise۰full γ prophs'.
  Proof.
    rewrite prophet_wise۰full𑁒get. iSteps.
  Qed.
  Lemma prophet_wise۰full𑁒valid pid γ past prophs1 prophs2 :
    prophet_wise۰model pid γ past prophs1 -∗
    prophet_wise۰full γ prophs2 -∗
    ⌜prophs2 = past ++ prophs1⌝.
  Proof.
    iIntros "(:model =1) (:full =2)".
    iDestruct (agree۰on𑁒agree𑁒L with "Hfull1 Hfull2") as %<-.
    iSteps.
  Qed.
  Lemma prophet_wise۰full𑁒agree γ prophs1 prophs2 :
    prophet_wise۰full γ prophs1 -∗
    prophet_wise۰full γ prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    apply: agree۰on𑁒agree𑁒L.
  Qed.

  Lemma prophet_wise۰snapshot𑁒get pid γ past prophs :
    prophet_wise۰model pid γ past prophs ⊢
    prophet_wise۰snapshot γ past prophs.
  Proof.
    iIntros "(:model)".
    iStep.
    iApply (mono_list۰lb𑁒get with "Hpast_auth").
  Qed.
  Lemma prophet_wise۰snapshot𑁒valid pid γ past1 prophs1 past2 prophs2 :
    prophet_wise۰model pid γ past1 prophs1 -∗
    prophet_wise۰snapshot γ past2 prophs2 -∗
      ∃ past3,
      ⌜past1 = past2 ++ past3⌝ ∗
      ⌜prophs2 = past3 ++ prophs1⌝.
  Proof.
    iIntros "(:model) (:snapshot suff=')".
    iDestruct (agree۰on𑁒agree𑁒L with "Hfull Hfull'") as %Hfull.
    iDestruct (mono_list۰lb𑁒valid with "Hpast_auth Hpast_lb") as %(past3 & ->).
    iPureIntro. rewrite -assoc in Hfull. naive_solver.
  Qed.

  Lemma prophet_wise۰lb𑁒get pid γ past prophs :
    prophet_wise۰model pid γ past prophs ⊢
    prophet_wise۰lb γ prophs.
  Proof.
    rewrite prophet_wise۰snapshot𑁒get.
    iSteps.
  Qed.
  Lemma prophet_wise۰lb𑁒valid pid γ past prophs lb :
    prophet_wise۰model pid γ past prophs -∗
    prophet_wise۰lb γ lb -∗
      ∃ past1 past2,
      ⌜past = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophs⌝.
  Proof.
    iIntros "Hmodel (:lb suff=')".
    iExists past'.
    iApply (prophet_wise۰snapshot𑁒valid with "Hmodel Hsnapshot").
  Qed.

  Lemma prophet_wise𑁒wp𑁒proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{
      pid γ prophs
    , RET #pid;
      prophet_wise۰model pid γ [] prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp𑁒fupd. wp۰apply (prophet_typed𑁒wp𑁒proph with "[//]") as "%pid %prophs Hpid".
    iMod (agree𑁒alloc (agree۰G := prophet_wise۰G۰full۰G) prophs) as "(%γ_full & #Hfull)".
    iMod (mono_list𑁒alloc []) as "(%γ_past & Hpast_auth)".
    set γ :=
      {|prophet_wise۰name۰full := γ_full
      ; prophet_wise۰name۰past := γ_past
      |}.
    iApply ("HΦ" $! pid γ).
    iSteps.
  Qed.

  Lemma prophet_wise𑁒wp𑁒resolve e pid v γ past prophs E Φ :
    Atomic e →
    to_val e = None →
    prophet_wise۰model pid γ past prophs -∗
    WP e @ E {{ w,
      ∃ oproph,
      ⌜prophet.(prophet_typed۰of_val) w v = Some oproph⌝ ∗
      match oproph with
      | None =>
          prophet_wise۰model pid γ past prophs -∗
          Φ w
      | Some proph =>
          ∀ prophs',
          ⌜prophs = proph :: prophs'⌝ -∗
          prophet_wise۰model pid γ (past ++ [proph]) prophs' -∗
          Φ w
      end
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros "% % (:model) HΦ".
    wp۰apply (prophet_typed𑁒wp𑁒resolve with "Hmodel"); first done.
    iApply wp𑁒fupd. wp۰apply (wp𑁒wand with "HΦ") as "%w (%oproph & %Hoproph & HΦ)".
    iExists oproph. iSplitR. 1: done.
    destruct oproph as [proph |]. 2: iSteps.
    iMod (mono_list𑁒update𑁒snoc proph with "Hpast_auth") as "Hpast_auth".
    iIntros "!> %prophs' -> Hpid".
    iApply ("HΦ" with "[//]").
    rewrite (assoc _ _ [_]). iSteps.
  Qed.
End prophet_wise۰G.

#[global] Opaque prophet_wise۰full.
#[global] Opaque prophet_wise۰model.
#[global] Opaque prophet_wise۰snapshot.
#[global] Opaque prophet_wise۰lb.
