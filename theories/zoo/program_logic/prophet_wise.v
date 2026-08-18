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
#[global] Instance subGｰprophet_wise۰Σ Σ `{zoo۰G : !ZooG Σ} prophet :
  subG (prophet_wise۰Σ prophet) Σ →
  ProphetWiseG Σ prophet.
Proof.
  solve_inG.
Qed.

Section prophet_wise۰G.
  Context (prophet : prophet_typed).
  Context `{prophet_wise۰G : ProphetWiseG Σ prophet}.

  Implicit Type oproph : option prophet.(prophet_typed۰type).
  Implicit Type proph : prophet.(prophet_typed۰type).
  Implicit Type prophs : list prophet.(prophet_typed۰type).

  Record prophet_wise۰name :=
    { prophet_wise۰name۰full : gname
    ; prophet_wise۰name۰past : gname
    }.

  #[global] Instance prophet_wise۰nameｰeq_dec : EqDecision prophet_wise۰name :=
    ltac:(solve_decision).
  #[global] Instance prophet_wise۰nameｰcountable :
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

  #[global] Instance prophet_wise۰fullｰtimeless γ prophs :
    Timeless (prophet_wise۰full γ prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰modelｰtimeless pid γ past prophs :
    Timeless (prophet_wise۰model pid γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰snapshotｰtimeless γ past prophs :
    Timeless (prophet_wise۰snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰lbｰtimeless γ lb :
    Timeless (prophet_wise۰lb γ lb).
  Proof.
    apply _.
  Qed.

  #[global] Instance prophet_wise۰fullｰpersistent γ prophs :
    Persistent (prophet_wise۰full γ prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰snapshotｰpersistent γ past prophs :
    Persistent (prophet_wise۰snapshot γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_wise۰lbｰpersistent γ lb :
    Persistent (prophet_wise۰lb γ lb).
  Proof.
    apply _.
  Qed.

  Lemma prophet_wise۰modelｰexclusive pid γ1 past1 prophs1 γ2 past2 prophs2 :
    prophet_wise۰model pid γ1 past1 prophs1 -∗
    prophet_wise۰model pid γ2 past2 prophs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (prophet_typed۰modelｰexclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma prophet_wise۰fullｰget pid γ past prophs :
    prophet_wise۰model pid γ past prophs ⊢
    prophet_wise۰full γ (past ++ prophs).
  Proof.
    iSteps.
  Qed.
  Lemma prophet_wise۰fullｰget' pid γ past prophs :
    prophet_wise۰model pid γ past prophs ⊢
      ∃ prophs',
      prophet_wise۰full γ prophs'.
  Proof.
    rewrite prophet_wise۰fullｰget. iSteps.
  Qed.
  Lemma prophet_wise۰fullｰvalid pid γ past prophs1 prophs2 :
    prophet_wise۰model pid γ past prophs1 -∗
    prophet_wise۰full γ prophs2 -∗
    ⌜prophs2 = past ++ prophs1⌝.
  Proof.
    iIntros "(:model =1) (:full =2)".
    iDestruct (agree۰onｰagreeｰL with "Hfull1 Hfull2") as %<-.
    iSteps.
  Qed.
  Lemma prophet_wise۰fullｰagree γ prophs1 prophs2 :
    prophet_wise۰full γ prophs1 -∗
    prophet_wise۰full γ prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    apply: agree۰onｰagreeｰL.
  Qed.

  Lemma prophet_wise۰snapshotｰget pid γ past prophs :
    prophet_wise۰model pid γ past prophs ⊢
    prophet_wise۰snapshot γ past prophs.
  Proof.
    iIntros "(:model)".
    iStep.
    iApply (mono_list۰lbｰget with "Hpast_auth").
  Qed.
  Lemma prophet_wise۰snapshotｰvalid pid γ past1 prophs1 past2 prophs2 :
    prophet_wise۰model pid γ past1 prophs1 -∗
    prophet_wise۰snapshot γ past2 prophs2 -∗
      ∃ past3,
      ⌜past1 = past2 ++ past3⌝ ∗
      ⌜prophs2 = past3 ++ prophs1⌝.
  Proof.
    iIntros "(:model) (:snapshot suff=')".
    iDestruct (agree۰onｰagreeｰL with "Hfull Hfull'") as %Hfull.
    iDestruct (mono_list۰lbｰvalid with "Hpast_auth Hpast_lb") as %(past3 & ->).
    iPureIntro. rewrite -assoc in Hfull. naive_solver.
  Qed.

  Lemma prophet_wise۰lbｰget pid γ past prophs :
    prophet_wise۰model pid γ past prophs ⊢
    prophet_wise۰lb γ prophs.
  Proof.
    rewrite prophet_wise۰snapshotｰget.
    iSteps.
  Qed.
  Lemma prophet_wise۰lbｰvalid pid γ past prophs lb :
    prophet_wise۰model pid γ past prophs -∗
    prophet_wise۰lb γ lb -∗
      ∃ past1 past2,
      ⌜past = past1 ++ past2⌝ ∗
      ⌜lb = past2 ++ prophs⌝.
  Proof.
    iIntros "Hmodel (:lb suff=')".
    iExists past'.
    iApply (prophet_wise۰snapshotｰvalid with "Hmodel Hsnapshot").
  Qed.

  Lemma prophet_wiseｰwpｰproph E :
    {{{
      True
    }}}
      Proph
      @ E
    {{{
      pid γ prophs
    , RET #pid;
      prophet_wise۰model pid γ [] prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wpｰfupd. wp۰apply (prophet_typedｰwpｰproph with "[//]") as "%pid %prophs Hpid".
    iMod (agreeｰalloc (agree۰G := prophet_wise۰G۰full۰G) prophs) as "(%γ_full & #Hfull)".
    iMod (mono_listｰalloc []) as "(%γ_past & Hpast_auth)".
    set γ :=
      {|prophet_wise۰name۰full := γ_full
      ; prophet_wise۰name۰past := γ_past
      |}.
    iApply ("HΦ" $! pid γ).
    iSteps.
  Qed.

  Lemma prophet_wiseｰwpｰresolve e pid v γ past prophs E Φ :
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
    wp۰apply (prophet_typedｰwpｰresolve with "Hmodel"); first done.
    iApply wpｰfupd. wp۰apply (wpｰwand with "HΦ") as "%w (%oproph & %Hoproph & HΦ)".
    iExists oproph. iSplitR. 1: done.
    destruct oproph as [proph |]. 2: iSteps.
    iMod (mono_listｰupdateｰsnoc proph with "Hpast_auth") as "Hpast_auth".
    iIntros "!> %prophs' -> Hpid".
    iApply ("HΦ" with "[//]").
    rewrite (assoc _ _ [_]). iSteps.
  Qed.
End prophet_wise۰G.

#[global] Opaque prophet_wise۰full.
#[global] Opaque prophet_wise۰model.
#[global] Opaque prophet_wise۰snapshot.
#[global] Opaque prophet_wise۰lb.
