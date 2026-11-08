Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_wise.
Require Export zoo_saturn.svar__code.
Require Import zoo_saturn.svar__types.
Require Import zoo_saturn.svar__pure.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type g gₛ : nat.
Implicit Type v vₛ 𝑣 𝑣ₛ w : val.
Implicit Type id : identifier.
Implicit Type ι : namespace.

Implicit Type proph : prophecy.
Implicit Type prophs past q : list prophecy.
Implicit Type op : operation.
Implicit Type ops helped help : list operation.
Implicit Type waiter : waiter.
Implicit Type waiters : gmap identifier waiter.
Implicit Type snap : snap.
Implicit Type snaps : list snap.
Implicit Type mode : mode.

(* ------------------------------------------------------------------------ *)
(* Prophecies. *)

#[local] Definition prophet :=
  {|prophet_typed۰type :=
      prophecy
  ; prophet_typed۰of_val v w :=
      match w with
      | ValBlock _ Tag1 [ValId id] =>
          Some $ Some $ ProphecyOp id OpGet
      | ValBlock _ Tag3 [ValId id; v'] =>
          Some $ Some $ ProphecyOp id (OpSet v')
      | ValBlock _ Tag4 [ValId id; v1; v2] =>
          match v with
          | ValBool b =>
              Some $ Some $ ProphecyOp id (OpCas v1 v2 b)
          | _ =>
              None
          end
      | _ =>
          match v, w with
          | ValBool false, ValBlock _ Tag0 _ =>
              Some None
          | ValBool true, ValBlock _ Tag0 [v; ValInt g] =>
              Some $ Some $ ProphecyForward v ₊g
          | ()%V, ValBlock _ Tag2 [ValId id; v] =>
              Some $ Some $ ProphecyOp id (OpSet v)
          | _, _ =>
              None
          end
      end
  |}.

(* ------------------------------------------------------------------------ *)
(* Ghost state. *)

Zoo name :=
  { self : location
  ; prophet : prophet_wise۰name
  ; model : gname
  ; scanner : gname
  ; generation : gname
  ; snapshot : gname
  ; snaps : gname
  ; hist : gname
  ; doom : gname
  ; waiters : gname
  }.

Zoo global :=
  { prophet : prophet_wise prophet
  ; model : twins val_O
  ; scanner : twins (leibnizO (val * nat))
  ; generation : auth_nat_max
  ; snapshot : auth_nat_max
  ; snaps : mono_list snap
  ; hist : mono_list (val * nat)
  ; doom : auth_nat_max
  ; waiters : ghost_map identifier waiter : iris
  ; waiter۰post : saved_pred val
  }.

Section svar_G.
  Context `{svar_G : SvarG Σ}.

  Implicit Type P : iProp Σ.
  Implicit Type Φ : val → iProp Σ.

  #[local] Definition prophet۰model γ past prophs :=
    prophet_wise۰model prophet γ.(svar۰name۰prophet) past prophs.
  #[local] Definition prophet۰snapshot γ past prophs :=
    prophet_wise۰snapshot prophet γ.(svar۰name۰prophet) past prophs.

  #[local] Definition model₁' γ_model v :=
    twins۰twin₁ (twins۰G := svar۰G۰model۰G) γ_model Own v.
  #[local] Definition model₁ γ :=
    model₁' γ.(svar۰name۰model).
  #[local] Definition model₂' γ_model v :=
    twins۰twin₂ (twins۰G := svar۰G۰model۰G) γ_model v.
  #[local] Definition model₂ γ :=
    model₂' γ.(svar۰name۰model).

  #[local] Definition scanner₁' γ_scanner dq vₛ g :=
    twins۰twin₁ γ_scanner dq (vₛ, g).
  #[local] Definition scanner₁ γ :=
    scanner₁' γ.(svar۰name۰scanner).
  #[local] Definition scanner₂' γ_scanner vₛ g :=
    twins۰twin₂ γ_scanner (vₛ, g).
  #[local] Definition scanner₂ γ :=
    scanner₂' γ.(svar۰name۰scanner).

  #[local] Definition generation۰auth' γ_generation g :=
    auth_nat_max۰auth γ_generation Own g.
  #[local] Definition generation۰auth γ :=
    generation۰auth' γ.(svar۰name۰generation).
  #[local] Definition generation۰lb γ g :=
    auth_nat_max۰lb γ.(svar۰name۰generation) g.

  #[local] Definition snapshot۰auth' γ_snapshot gₛ :=
    auth_nat_max۰auth γ_snapshot Own gₛ.
  #[local] Definition snapshot۰auth γ :=
    snapshot۰auth' γ.(svar۰name۰snapshot).
  #[local] Definition snapshot۰lb γ gₛ :=
    auth_nat_max۰lb γ.(svar۰name۰snapshot) gₛ.

  #[local] Definition snaps۰auth' γ_snaps snaps :=
    mono_list۰auth γ_snaps (DfracOwn 1) snaps.
  #[local] Definition snaps۰auth γ :=
    snaps۰auth' γ.(svar۰name۰snaps).
  #[local] Definition snaps۰lb γ snaps :=
    mono_list۰lb γ.(svar۰name۰snaps) snaps.

  #[local] Definition hist۰auth' γ_hist (hist : list (val * nat)) :=
    mono_list۰auth γ_hist (DfracOwn 1) hist.
  #[local] Definition hist۰auth γ :=
    hist۰auth' γ.(svar۰name۰hist).
  #[local] Definition hist۰at γ h (vh : val) (idx : nat) :=
    mono_list۰at γ.(svar۰name۰hist) h (vh, idx).

  #[local] Definition doom۰auth' γ_doom n :=
    auth_nat_max۰auth γ_doom Own n.
  #[local] Definition doom۰auth γ :=
    doom۰auth' γ.(svar۰name۰doom).
  #[local] Definition doom۰lb γ :=
    auth_nat_max۰lb γ.(svar۰name۰doom) 1.

  #[local] Definition waiters۰auth' γ_waiters waiters : iProp Σ :=
    ghost_map_auth γ_waiters (DfracOwn 1) waiters ∗
    [∗ set] id ∈ dom waiters, identifier۰model id.
  #[local] Definition waiters۰auth γ :=
    waiters۰auth' γ.(svar۰name۰waiters).
  #[local] Definition waiters۰elem γ id waiter :=
    ghost_map_elem γ.(svar۰name۰waiters) id (DfracOwn 1) waiter.

  #[local] Definition waiter۰au γ ι waiter Ψ : iProp Σ :=
    AU <{
      ∃∃ v,
      model₁ γ v
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ∀∀ b,
      ⌜request۰rel waiter.(waiter۰request) b v⌝ ∗
      model₁ γ (request۰apply waiter.(waiter۰request) b v)
    , COMM
      Ψ (request۰result waiter.(waiter۰request) b v)
    }>.

  #[local] Definition waiters۰statuses γ ι waiters 𝑣 helped past : iProp Σ :=
    [∗ map] id ↦ waiter ∈ waiters,
      if bool_decide (id ∈ operations۰ids (prophecies۰ops past)) then
        waiters۰elem γ id waiter
      else
        ∃ Ψ,
        saved_pred waiter.(waiter۰post) Ψ ∗
        if bool_decide (id ∈ operations۰ids helped) then
          Ψ (helped۰result 𝑣 helped id)
        else
          waiter۰au γ ι waiter Ψ.

  #[local] Definition inv۰inner γ ι : iProp Σ :=
    ∃ 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode,
    γ.(svar۰name۰self).[value] ↦ 𝑣 ∗
    γ.(svar۰name۰self).[gen] ↦ #g ∗
    γ.(svar۰name۰self).[snapshot] ↦ snap۰to_val snap ∗
    model₂ γ v ∗
    scanner₂ γ vₛ g ∗
    generation۰auth γ g ∗
    snapshot۰auth γ snap.(snap۰gen) ∗
    snaps۰auth γ snaps ∗
    hist۰auth γ hist ∗
    doom۰auth γ (mode۰doomed mode) ∗
    waiters۰auth γ waiters ∗
    prophet۰model γ past prophs ∗
    waiters۰statuses γ ι waiters 𝑣 helped past ∗
    ⌜inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode⌝.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %𝑣{}
      & %g{}
      & %v{}
      & %vₛ{}
      & %snaps{}
      & %snap{}
      & %hist{}
      & %waiters{}
      & %helped{}
      & %past{}
      & %prophs{}
      & %mode{}
      & >Ht_value
      & >Ht_gen
      & >Ht_snapshot
      & >Hmodel₂
      & >Hscanner₂
      & >Hgeneration_auth
      & >Hsnapshot_auth
      & >Hsnaps_auth
      & >Hhist_auth
      & >Hdoom_auth
      & >Hwaiters_auth
      & >Hprophet_model
      & Hwaiters
      & >%Hinv{}
      )
    ".
  #[local] Definition inv' γ ι :=
    inv ι (inv۰inner γ ι).
  Please Definition svar۰inv γ ι : iProp Σ :=
    γ.(svar۰name۰self).[proph] ↦□ γ.(svar۰name۰prophet) ∗
    inv' γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( #Ht_proph
      & #Hinv
      )
    ".

  Please Definition svar۰model :=
    model₁.

  Please Definition svar۰scanner γ dq vₛ : iProp Σ :=
    ∃ g,
    scanner₁ γ dq vₛ g.
  #[local] Instance : CustomIpat "scanner" :=
    " ( %g{}
      & Hscanner₁{_{}}
      )
    ".

  Zoo derive Timeless for svar۰model.
  Zoo derive Timeless for svar۰scanner.

  Zoo derive Persistent for svar۰inv.
  Zoo derive Persistent for svar۰scanner:discarded.

  #[global] Instance svar۰scannerｰfractional γ vₛ :
    Fractional (λ (q : Qp), svar۰scanner γ (DfracOwn q) vₛ).
  Proof.
    intros q1 q2.
    iSplit.
    - iIntros "(:scanner)".
      iDestruct "Hscanner₁" as "($ & $)".
    - iIntros "((:scanner =1) & (:scanner =2))".
      iDestruct (twins۰twin₁ｰcombineｰL with "Hscanner₁_1 Hscanner₁_2") as "(% & $)".
  Qed.
  #[global] Instance svar۰scannerｰas_fractional γ (q : Qp) vₛ :
    AsFractional (svar۰scanner γ (DfracOwn q) vₛ) (λ (q : Qp), svar۰scanner γ (DfracOwn q) vₛ) q.
  Proof.
    split; [done | apply _].
  Qed.

  #[local] Lemma modelｰalloc v :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model v ∗
      model₂' γ_model v.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma modelｰagree γ v1 v2 :
    model₁ γ v1 -∗
    model₂ γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ v1 v2} v :
    model₁ γ v1 -∗
    model₂ γ v2 ==∗
      model₁ γ v ∗
      model₂ γ v.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma scannerｰalloc vₛ :
    ⊢ |==>
      ∃ γ_scanner,
      scanner₁' γ_scanner Own vₛ 0 ∗
      scanner₂' γ_scanner vₛ 0.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma scannerｰagree γ dq vₛ1 g1 vₛ2 g2 :
    scanner₁ γ dq vₛ1 g1 -∗
    scanner₂ γ vₛ2 g2 -∗
      ⌜vₛ1 = vₛ2⌝ ∗
      ⌜g1 = g2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (twinsｰagreeｰL with "H1 H2") as %[= -> ->] => //.
  Qed.
  #[local] Lemma scannerｰupdate {γ vₛ1 g1 vₛ2 g2} vₛ g :
    scanner₁ γ Own vₛ1 g1 -∗
    scanner₂ γ vₛ2 g2 ==∗
      scanner₁ γ Own vₛ g ∗
      scanner₂ γ vₛ g.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma generationｰalloc :
    ⊢ |==>
      ∃ γ_generation,
      generation۰auth' γ_generation 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma generation۰lbｰget γ g :
    generation۰auth γ g ⊢
    generation۰lb γ g.
  Proof.
    apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma generation۰lbｰvalid γ g1 g2 :
    generation۰auth γ g1 -∗
    generation۰lb γ g2 -∗
    ⌜g2 ≤ g1⌝.
  Proof.
    apply auth_nat_max۰lbｰvalid.
  Qed.
  #[local] Lemma generationｰupdate γ g :
    generation۰auth γ g ⊢ |==>
    generation۰auth γ (S g).
  Proof.
    apply auth_nat_maxｰupdate. lia.
  Qed.

  #[local] Lemma snapshotｰalloc :
    ⊢ |==>
      ∃ γ_snapshot,
      snapshot۰auth' γ_snapshot 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma snapshot۰lbｰget γ gₛ :
    snapshot۰auth γ gₛ ⊢
    snapshot۰lb γ gₛ.
  Proof.
    apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma snapshot۰lbｰvalid γ gₛ1 gₛ2 :
    snapshot۰auth γ gₛ1 -∗
    snapshot۰lb γ gₛ2 -∗
    ⌜gₛ2 ≤ gₛ1⌝.
  Proof.
    apply auth_nat_max۰lbｰvalid.
  Qed.
  #[local] Lemma snapshotｰupdate {γ gₛ} gₛ' :
    gₛ ≤ gₛ' →
    snapshot۰auth γ gₛ ⊢ |==>
    snapshot۰auth γ gₛ'.
  Proof.
    apply auth_nat_maxｰupdate.
  Qed.

  #[local] Lemma snapsｰalloc snaps :
    ⊢ |==>
      ∃ γ_snaps,
      snaps۰auth' γ_snaps snaps.
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma snaps۰lbｰget γ snaps :
    snaps۰auth γ snaps ⊢
    snaps۰lb γ snaps.
  Proof.
    apply mono_list۰lbｰget.
  Qed.
  #[local] Lemma snaps۰lbｰvalid γ snaps1 snaps2 :
    snaps۰auth γ snaps1 -∗
    snaps۰lb γ snaps2 -∗
    ⌜snaps2 `prefix_of` snaps1⌝.
  Proof.
    apply mono_list۰lbｰvalid.
  Qed.
  #[local] Lemma snapsｰupdate {γ snaps} snap :
    snaps۰auth γ snaps ⊢ |==>
    snaps۰auth γ (snaps ++ [snap]).
  Proof.
    apply mono_listｰupdateｰsnoc.
  Qed.

  #[local] Lemma histｰalloc hist :
    ⊢ |==>
      ∃ γ_hist,
      hist۰auth' γ_hist hist.
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma hist۰atｰget {γ hist} h vh idx :
    hist !! h = Some (vh, idx) →
    hist۰auth γ hist ⊢
    hist۰at γ h vh idx.
  Proof.
    apply mono_list۰atｰget.
  Qed.
  #[local] Lemma hist۰atｰvalid γ hist h vh idx :
    hist۰auth γ hist -∗
    hist۰at γ h vh idx -∗
    ⌜hist !! h = Some (vh, idx)⌝.
  Proof.
    apply mono_list۰atｰvalid.
  Qed.
  #[local] Lemma histｰupdate {γ hist} vh idx :
    hist۰auth γ hist ⊢ |==>
    hist۰auth γ (hist ++ [(vh, idx)]).
  Proof.
    apply mono_listｰupdateｰsnoc.
  Qed.

  #[local] Lemma doomｰalloc :
    ⊢ |==>
      ∃ γ_doom,
      doom۰auth' γ_doom 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma doom۰lbｰget γ mode :
    mode ≠ Good →
    doom۰auth γ (mode۰doomed mode) ⊢
    doom۰lb γ.
  Proof.
    destruct mode; first done.
    intros _. apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma doom۰lbｰvalid γ mode :
    doom۰auth γ (mode۰doomed mode) -∗
    doom۰lb γ -∗
    ⌜mode ≠ Good⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_nat_max۰lbｰvalid with "Hauth Hlb") as %?.
    iPureIntro. intros ->. simpl in *. lia.
  Qed.
  #[local] Lemma doomｰupdate {γ mode} mode' :
    mode۰doomed mode ≤ mode۰doomed mode' →
    doom۰auth γ (mode۰doomed mode) ⊢ |==>
    doom۰auth γ (mode۰doomed mode').
  Proof.
    apply auth_nat_maxｰupdate.
  Qed.

  #[local] Lemma waitersｰalloc :
    ⊢ |==>
      ∃ γ_waiters,
      waiters۰auth' γ_waiters ∅.
  Proof.
    iMod ghost_map_alloc_empty as "(%γ_waiters & $)".
    iApply big_sepS_empty => //.
  Qed.
  #[local] Lemma waiters۰elemｰexclusive γ id waiter1 waiter2 :
    waiters۰elem γ id waiter1 -∗
    waiters۰elem γ id waiter2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %(? & _). done.
  Qed.
  #[local] Lemma waiters۰elemｰvalid γ waiters id waiter :
    waiters۰auth γ waiters -∗
    waiters۰elem γ id waiter -∗
    ⌜waiters !! id = Some waiter⌝.
  Proof.
    iIntros "(Hauth & _) Helem".
    iApply (ghost_map_lookup with "Hauth Helem").
  Qed.
  #[local] Lemma waitersｰinsert {γ waiters} id waiter :
    waiters۰auth γ waiters -∗
    identifier۰model id ==∗
      ⌜waiters !! id = None⌝ ∗
      waiters۰auth γ (<[id := waiter]> waiters) ∗
      waiters۰elem γ id waiter.
  Proof.
    iIntros "(Hauth & Hids) Hid".
    destruct (waiters !! id) eqn:Hlookup.
    { iDestruct (big_sepS_elem_of with "Hids") as "Hid'".
      { apply elem_of_dom. naive. }
      iDestruct (identifier۰modelｰexclusive with "Hid Hid'") as %[].
    }
    iMod (ghost_map_insert with "Hauth") as "($ & $)"; first done.
    iModIntro. iSplitR; first done.
    rewrite dom_insert_L big_sepS_insert; first (apply not_elem_of_dom; done).
    iFrame.
  Qed.

  #[local] Instance waiters۰authｰtimeless γ waiters :
    Timeless (waiters۰auth γ waiters).
  Proof.
    apply _.
  Qed.

  Opaque waiters۰auth'.

  Lemma svar٠makeｰspec ι v :
    {{{
      True
    }}}
      svar٠make v
    {{{
      γ
    , RET γ;
      svar۰inv γ ι ∗
      svar۰model γ v ∗
      svar۰scanner γ Own v
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (prophet_wiseｰwpｰproph prophet with "[//]") as (pid prophs) "Hprophet_model".
    wp۰block۰generative bid.
    wp۰block t as "Ht_value Ht_gen Ht_snapshot #Ht_proph".

    iMod (modelｰalloc v) as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod (scannerｰalloc v) as "(%γ_scanner & Hscanner₁ & Hscanner₂)".
    iMod generationｰalloc as "(%γ_generation & Hgeneration_auth)".
    iMod snapshotｰalloc as "(%γ_snapshot & Hsnapshot_auth)".
    iMod (snapsｰalloc [Snap bid v 0 0]) as "(%γ_snaps & Hsnaps_auth)".
    iMod (histｰalloc [(v, 0)]) as "(%γ_hist & Hhist_auth)".
    iMod doomｰalloc as "(%γ_doom & Hdoom_auth)".
    iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ :=
      {|svar۰name۰self := t
      ; svar۰name۰prophet := pid
      ; svar۰name۰model := γ_model
      ; svar۰name۰scanner := γ_scanner
      ; svar۰name۰generation := γ_generation
      ; svar۰name۰snapshot := γ_snapshot
      ; svar۰name۰snaps := γ_snaps
      ; svar۰name۰hist := γ_hist
      ; svar۰name۰doom := γ_doom
      ; svar۰name۰waiters := γ_waiters
      |}.

    iApply ("HΦ" $! γ).
    iFrameStep.
    iApply inv_alloc.
    iExists v, 0, v, v, [Snap bid v 0 0], (Snap bid v 0 0), [(v, 0)], ∅, [], [], prophs, Good.
    iFrame. iSplitL. { rewrite /waiters۰statuses big_sepM_empty //. }
    iPureIntro. split.
    all: try done.
    all: try (intros [| []]; simpl; intros; simplify_eq/=; simpl; lia).
    all: try (intros [| []]; simpl; intros; simplify_eq/=; set_solver).
    all: try set_solver.
    all: try apply prefix_nil.
    all: try (exists 0; done).
    all: rewrite /inv۰state decide_True //.
  Qed.

  #[local] Definition reader γ n g 𝑣 : iProp Σ :=
    ( ∃ snaps',
      snaps۰lb γ snaps' ∗
      ⌜n < length snaps'⌝
    ) ∨ (
      generation۰lb γ (S g)
    ) ∨ (
      doom۰lb γ
    ) ∨ (
      ∃ past prophs,
      prophet۰snapshot γ past prophs ∗
      ⌜S (length (prophecies۰forwards past)) = n⌝ ∗
      ( ⌜head (prophecies۰forwards prophs) = Some (𝑣, g)⌝ →
        ∃ idx,
        hist۰at γ g 𝑣 idx
      )
    ).
  #[local] Instance readerｰpersistent γ n g 𝑣 :
    Persistent (reader γ n g 𝑣).
  Proof.
    apply _.
  Qed.

  #[local] Lemma invｰinit γ ι :
    inv' γ ι ={⊤}=∗
      snaps۰lb γ [] ∗
      ∃ vh idx,
      hist۰at γ 0 vh idx.
  Proof.
    iIntros "#Hinv".

    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb".
    destruct (hist !! 0) as [(vh & idx) |] eqn:Hhist_lookup; last first.
    { apply lookup_ge_None in Hhist_lookup.
      pose proof (inv۰pure۰hist_length _ _ _ _ _ _ _ _ _ _ _ _ Hinv). lia.
    }
    iDestruct (hist۰atｰget with "Hhist_auth") as "#Hhist_at"; first done.
    iSplitR "". { iFrameSteps. }
    iModIntro. iSplitL.
    - iApply (mono_list۰lbｰmono with "Hsnaps_lb"). apply prefix_nil.
    - iSteps.
  Qed.

  #[local] Lemma genｰspec γ ι g0 :
    {{{
      inv' γ ι ∗
      generation۰lb γ g0
    }}}
      γ.{gen}
    {{{
      g
    , RET #g;
      ⌜g0 ≤ g⌝ ∗
      generation۰lb γ g
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hg0) HΦ".

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg0") as %?.
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg".
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma genｰspecｰscanner γ ι dq vₛ g :
    {{{
      inv' γ ι ∗
      scanner₁ γ dq vₛ g
    }}}
      γ.{gen}
    {{{
      RET #g;
      scanner₁ γ dq vₛ g
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hscanner₁) HΦ".

    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
    iSplitR "Hscanner₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma snapshotｰspec γ ι g0 L h vh idx :
    {{{
      inv' γ ι ∗
      generation۰lb γ g0 ∗
      snaps۰lb γ L ∗
      hist۰at γ h vh idx
    }}}
      γ.{snapshot}
    {{{
      snaps snap
    , RET snap۰to_val snap;
      snaps۰lb γ snaps ∗
      ⌜L `prefix_of` snaps⌝ ∗
      ⌜last snaps = Some snap⌝ ∗
      ⌜snap.(snap۰gen) ≤ snap.(snap۰inst)⌝ ∗
      generation۰lb γ snap.(snap۰inst) ∗
      snapshot۰lb γ snap.(snap۰gen) ∗
      ⌜idx < pred (length snaps) → h ≤ snap.(snap۰inst)⌝ ∗
      ∃ gc vh' idx',
      hist۰at γ gc vh' idx' ∗
      ⌜g0 ≤ gc⌝ ∗
      ⌜idx' < length snaps⌝
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hg0 & #HL & #Hhist_at) HΦ".

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iDestruct (snaps۰lbｰvalid with "Hsnaps_auth HL") as %HL.
    iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb".
    iDestruct (hist۰atｰvalid with "Hhist_auth Hhist_at") as %Hhist_lookup.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg0") as %Hg0.
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg".
    iDestruct (snapshot۰lbｰget with "Hsnapshot_auth") as "#Hsnapshot_lb".
    pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as Hlast.
    pose proof Hlast as Hlast'%snapsｰlookup_last.
    opose proof* inv۰pure۰snaps_inst as (Hinst1 & Hinst2); [done.. |].
    opose proof* inv۰pure۰hist_last as (idx' & Hhist_last); first done.
    opose proof* inv۰pure۰hist_idx as Hidx'; [done.. |].
    iDestruct (hist۰atｰget with "Hhist_auth") as "#Hhist_at'"; first done.
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro. iApply "HΦ".
    iFrame "#". iSplitR; first done. iSplitR; first done. iSplitR; first done.
    iSplitR. { iApply (auth_nat_max۰lbｰle with "Hg"). done. }
    iSplitR.
    { iPureIntro. intros Hidx.
      eapply (inv۰pure۰hist_snaps _ _ _ _ _ _ _ _ _ _ _ _ Hinv); done.
    }
    iSteps.
  Qed.

  #[local] Lemma valueｰspec γ ι snaps snap g :
    {{{
      inv' γ ι ∗
      snaps۰lb γ snaps ∗
      ⌜last snaps = Some snap⌝ ∗
      ⌜snap.(snap۰gen) < g⌝ ∗
      generation۰lb γ g
    }}}
      γ.{value}
    {{{
      𝑣
    , RET 𝑣;
      reader γ (length snaps) g 𝑣
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hsnaps_lb & %Hlast & %Hgen & #Hg) HΦ".

    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (snaps۰lbｰvalid with "Hsnaps_auth Hsnaps_lb") as %Hsnaps.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg") as %Hg.
    iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb1".
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg1".
    iDestruct (prophet_wise۰snapshotｰget with "Hprophet_model") as "#Hprophet_snapshot".
    iAssert (if mode1 is Good then True else doom۰lb γ)%I as "#Hdoom".
    { destruct mode1; first done. iApply (doom۰lbｰget with "Hdoom_auth"). done. }
    opose proof* inv۰pure۰hist_last as (idx & Hhist_last); first done.
    iDestruct (hist۰atｰget with "Hhist_auth") as "#Hhist_at"; first done.
    iAssert (reader γ (length snaps) g 𝑣1)%I as "#Hreader".
    { destruct (decide (length snaps < length snaps1)).
      { iLeft. iExists snaps1. iFrame "#". done. }
      apply prefix_length_eq in Hsnaps as <-; last lia.
      assert (snap1 = snap) as ->.
      { pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv1). congruence. }
      destruct (decide (g < g1)).
      { iRight. iLeft.
        iApply (auth_nat_max۰lbｰle with "Hg1"). lia.
      }
      assert (g1 = g) as -> by lia.
      destruct mode1 as [| b g_d]; last first.
      { iRight. iRight. iLeft. done. }
      iRight. iRight. iRight.
      iExists past1, prophs1.
      iSplitR. { iApply "Hprophet_snapshot". }
      iSplitR. { iPureIntro. symmetry. apply (inv۰pure۰forwards _ _ _ _ _ _ _ _ _ _ _ _ Hinv1). }
      iIntros "%Hhead".
      opose proof* (inv۰pureｰreader Hinv1) as <-; [done.. |].
      iExists idx. done.
    }
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro. iApply "HΦ". done.
  Qed.

  #[local] Lemma waiters۰statusesｰforward γ ι waiters 𝑣' helped past 𝑣 g :
    waiters۰statuses γ ι waiters 𝑣' helped (past ++ [ProphecyForward 𝑣 g]) = waiters۰statuses γ ι waiters 𝑣' helped past.
  Proof.
    rewrite /waiters۰statuses prophecies۰opsｰapp /= right_id //.
  Qed.

  #[local] Lemma readerｰvalid γ snaps g hist vₛ idx mode past prophs n g' 𝑣 :
    length snaps = S (length (prophecies۰forwards past)) →
    hist !! g = Some (vₛ, idx) →
    snaps۰auth γ snaps -∗
    generation۰auth γ g -∗
    doom۰auth γ (mode۰doomed mode) -∗
    hist۰auth γ hist -∗
    prophet۰model γ past prophs -∗
    reader γ n g' 𝑣 -∗
    ⌜n = length snaps → head (prophecies۰forwards prophs) = Some (𝑣, g') → g' = g → mode = Good → vₛ = 𝑣⌝.
  Proof.
    iIntros "%Hforwards %Hhist_lookup Hsnaps_auth Hgeneration_auth Hdoom_auth Hhist_auth Hprophet_model Hreader".
    iIntros "%Hn %Hhead %Hg %Hmode". subst g' n.
    iDestruct "Hreader" as "[(%snaps' & #Hsnaps_lb & %Hsnaps') | [#Hg | [#Hdoom | (%past' & %prophs' & #Hprophet_snapshot & %Hforwards' & #Hhist)]]]".
    - iDestruct (snaps۰lbｰvalid with "Hsnaps_auth Hsnaps_lb") as %?%prefix_length. lia.
    - iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg") as %?. lia.
    - iDestruct (doom۰lbｰvalid with "Hdoom_auth Hdoom") as %?. done.
    - iDestruct (prophet_wise۰snapshotｰvalid with "Hprophet_model Hprophet_snapshot") as %(past3 & -> & ->).
      rewrite prophecies۰forwardsｰapp length_app in Hforwards.
      assert (prophecies۰forwards past3 = []) as Hpast3.
      { apply nil_length_inv. lia. }
      iDestruct ("Hhist" with "[]") as "(%idx' & Hhist_at)".
      { rewrite prophecies۰forwardsｰapp Hpast3 //. }
      iDestruct (hist۰atｰvalid with "Hhist_auth Hhist_at") as %?.
      naive.
  Qed.

  #[local] Lemma casｰspec γ ι snaps snap g 𝑣 :
    {{{
      svar۰inv γ ι ∗
      snaps۰lb γ snaps ∗
      ⌜last snaps = Some snap⌝ ∗
      ⌜snap.(snap۰gen) < g⌝ ∗
      ⌜snap.(snap۰inst) ≤ g⌝ ∗
      generation۰lb γ g ∗
      reader γ (length snaps) g 𝑣
    }}}
      𝗿𝗲𝘀𝗼𝗹𝘃𝗲
        (𝗰𝗮𝘀 γ.[snapshot] (snap۰to_val snap) ‘Snapshot@[ 𝑣, #g ])
        γ.{proph}
        (‘Forward( 𝑣, #g ))%V
    {{{
      b
    , RET #b;
      if b then
        snapshot۰lb γ g
      else
        ∃ snaps',
        snaps۰lb γ snaps' ∗
        ⌜snaps `prefix_of` snaps'⌝ ∗
        ⌜length snaps < length snaps'⌝ ∗
        snapshot۰lb γ snap.(snap۰inst)
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & #Hsnaps_lb & %Hlast & %Hgen & %Hinst & #Hg & #Hreader) HΦ".

    wp۰load. wp۰block۰generative bid. wp۰pures.

    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (snaps۰lbｰvalid with "Hsnaps_auth Hsnaps_lb") as %Hsnaps.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg") as %Hg.
    pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv1) as Hlast1.
    opose proof* inv۰pure۰hist_last as (idx & Hhist_last); first done.
    iDestruct (readerｰvalid with "Hsnaps_auth Hgeneration_auth Hdoom_auth Hhist_auth Hprophet_model Hreader") as %Hvₛ.
    { apply (inv۰pure۰forwards _ _ _ _ _ _ _ _ _ _ _ _ Hinv1). }
    { done. }
    pose proof Hlast as Hlast'%snapsｰlookup_last.
    pose proof Hlast' as Hlast''. eapply prefix_lookup_Some in Hlast''; last done.
    pose proof Hlast1 as Hlast1'%snapsｰlookup_last.
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰cas as Hcas | Hcas.

    - iExists None. iSplitR; first done. iIntros "!> Hprophet_model".
      assert (length snaps < length snaps1) as Hlen.
      { pose proof Hsnaps as Hlen%prefix_length.
        destruct (decide (length snaps = length snaps1)) as [Heq |]; last lia.
        apply prefix_length_eq in Hsnaps as <-; last lia.
        exfalso.
        assert (snap1 = snap) as -> by congruence.
        apply (snap۰to_valｰnonsimilar snap). done.
      }
      destruct (snaps1 !! length snaps) as [snap' |] eqn:Hlookup'; last first.
      { apply lookup_ge_None in Hlookup'. lia. }
      opose proof* (inv۰pure۰snaps_sorted _ _ _ _ _ _ _ _ _ _ _ _ Hinv1 (pred (length snaps)) snap snap') as (_ & Hsorted).
      { done. }
      { replace (S (pred (length snaps))) with (length snaps); first done.
        apply lookup_lt_Some in Hlast'. lia.
      }
      opose proof* (inv۰pureｰsnaps_le_last (length snaps) snap' Hinv1); first done.
      iDestruct (snapshot۰lbｰget with "Hsnapshot_auth") as "#Hsnapshot_lb".
      iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb1".
      iSplitR "HΦ". { iFrameSteps. }
      iModIntro. iApply "HΦ".
      iExists snaps1. iFrame "#". iSplitR; first done. iSplitR; first done.
      iApply (auth_nat_max۰lbｰle with "Hsnapshot_lb"). lia.

    - iExists (Some (ProphecyForward 𝑣 g)). iSplitR.
      { iPureIntro. rewrite /= Nat2Z.id //. }
      iIntros "!> %prophs' -> Hprophet_model".
      apply snap۰to_valｰsimilar in Hcas.
      assert (snaps1 = snaps) as ->.
      { opose proof* (inv۰pureｰsnaps_gen_inj _ _ _ _ Hinv1 Hlast1' Hlast''); first done.
        apply lookup_lt_Some in Hlast'.
        symmetry. apply prefix_length_eq; first done. lia.
      }
      assert (snap1 = snap) as -> by congruence.
      iMod (snapsｰupdate (Snap bid 𝑣 g g1) with "Hsnaps_auth") as "Hsnaps_auth".
      iMod (snapshotｰupdate g with "Hsnapshot_auth") as "Hsnapshot_auth"; first lia.
      iDestruct (snapshot۰lbｰget with "Hsnapshot_auth") as "#Hsnapshot_lb".
      iSplitR "HΦ".
      { iExists 𝑣1, g1, v1, vₛ1, (snaps ++ [Snap bid 𝑣 g g1]), (Snap bid 𝑣 g g1), hist1, waiters1, helped1, (past1 ++ [ProphecyForward 𝑣 g]), prophs', mode1.
        rewrite waiters۰statusesｰforward.
        iFrame. iPureIntro.
        apply (inv۰pureｰforward 𝑣 g bid Hinv1); [lia | lia | lia |].
        intros. eapply Hvₛ; done.
      }
      iSteps.
  Qed.

  Lemma svar٠forwardｰspec γ ι g0 :
    {{{
      svar۰inv γ ι ∗
      generation۰lb γ g0
    }}}
      svar٠forward γ
    {{{
      RET ();
      snapshot۰lb γ g0
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & #Hg0) HΦ".

    wp۰rec.

    iMod (invｰinit with "Hinv") as "(#Hsnaps_lb0 & %vh0 & %idx0 & #Hhist_at0)".
    wp۰apply (snapshotｰspec with "[$Hinv $Hg0 $Hsnaps_lb0 $Hhist_at0]") as (snaps1 snap1) "(#Hsnaps_lb1 & _ & %Hlast1 & %Hinst1 & #Hinst1_lb & #Hsnapshot_lb1 & _ & %gc1 & %vh1 & %idx1 & #Hhist_at1 & %Hgc1 & %Hidx1)".
    iDestruct (auth_nat_max۰lbｰmax with "Hg0 Hinst1_lb") as "#Hlb1".
    wp۰apply+ (genｰspec with "[$Hinv $Hlb1]") as (g1) "(%Hg1 & #Hg1_lb)".
    wp۰pures.
    case_bool_decide as Hsnap1; wp۰pures.
    { iApply "HΦ". iApply (auth_nat_max۰lbｰle with "Hsnapshot_lb1"). lia. }
    wp۰apply (valueｰspec _ _ snaps1 snap1 g1 with "[]") as (𝑣1) "#Hreader1".
    { iFrame "#". iPureIntro. split; [done | lia]. }
    wp۰apply+ (casｰspec _ _ snaps1 snap1 g1 𝑣1 with "[]") as ([]) "H".
    { iFrame "#". iPureIntro. split_and!; [done | lia | lia]. }
    { wp۰pures. iApply "HΦ". iApply (auth_nat_max۰lbｰle with "H"). lia. }
    iDestruct "H" as "(%snaps1' & #Hsnaps_lb1' & %Hpre1 & %Hlen1 & _)".

    wp۰apply+ (snapshotｰspec with "[$Hinv $Hg0 $Hsnaps_lb1' $Hhist_at1]") as (snaps2 snap2) "(#Hsnaps_lb2 & %Hpre2 & %Hlast2 & %Hinst2 & #Hinst2_lb & #Hsnapshot_lb2 & %Hhist2 & _)".
    assert (gc1 ≤ snap2.(snap۰inst)) as Hgc2.
    { apply Hhist2. apply prefix_length in Hpre2. lia. }
    iDestruct (auth_nat_max۰lbｰmax with "Hg0 Hinst2_lb") as "#Hlb2".
    wp۰apply+ (genｰspec with "[$Hinv $Hlb2]") as (g2) "(%Hg2 & #Hg2_lb)".
    wp۰pures.
    case_bool_decide as Hsnap2; wp۰pures.
    { iApply "HΦ". iApply (auth_nat_max۰lbｰle with "Hsnapshot_lb2"). lia. }
    wp۰apply (valueｰspec _ _ snaps2 snap2 g2 with "[]") as (𝑣2) "#Hreader2".
    { iFrame "#". iPureIntro. split; [done | lia]. }
    wp۰apply+ (casｰspec _ _ snaps2 snap2 g2 𝑣2 with "[]") as ([]) "H".
    { iFrame "#". iPureIntro. split_and!; [done | lia | lia]. }
    - wp۰pures. iApply "HΦ". iApply (auth_nat_max۰lbｰle with "H"). lia.
    - iDestruct "H" as "(%snaps2' & _ & _ & _ & #Hinst_lb)".
      wp۰pures. iApply "HΦ". iApply (auth_nat_max۰lbｰle with "Hinst_lb"). lia.
  Qed.

  #[local] Lemma waiters۰statusesｰinsert γ ι waiters 𝑣 helped past id waiter Ψ :
    id ∉ operations۰ids (prophecies۰ops past) →
    id ∉ operations۰ids helped →
    waiters !! id = None →
    waiters۰statuses γ ι waiters 𝑣 helped past -∗
    saved_pred waiter.(waiter۰post) Ψ -∗
    waiter۰au γ ι waiter Ψ -∗
    waiters۰statuses γ ι (<[id := waiter]> waiters) 𝑣 helped past.
  Proof.
    iIntros "%Hpast %Hhelped %Hlookup Hwaiters #Hpost Hau".
    iApply (big_sepM_insert with "[- $Hwaiters]"); first done.
    rewrite !bool_decide_eq_false_2 //.
    iSteps.
  Qed.

  #[local] Lemma waiters۰statusesｰwrite γ ι waiters 𝑣 𝑣' helped helped' past id (w : opkind) waiter :
    waiters !! id = Some waiter →
    id ∉ operations۰ids (prophecies۰ops past) →
    (∀ id', id' ≠ id → (id' ∈ operations۰ids helped' ↔ id' ∈ operations۰ids helped)) →
    (∀ id', id' ≠ id → id' ∈ operations۰ids helped → helped۰result 𝑣' helped' id' = helped۰result 𝑣 helped id') →
    waiters۰statuses γ ι waiters 𝑣 helped past -∗
    waiters۰elem γ id waiter -∗
      waiters۰statuses γ ι waiters 𝑣' helped' (past ++ [ProphecyOp id w]) ∗
      ∃ Ψ,
      saved_pred waiter.(waiter۰post) Ψ ∗
      if bool_decide (id ∈ operations۰ids helped) then
        Ψ (helped۰result 𝑣 helped id)
      else
        waiter۰au γ ι waiter Ψ.
  Proof.
    iIntros "%Hlookup %Hid %Hhelped %Hresult Hwaiters Helem".
    iDestruct (big_sepM_delete with "Hwaiters") as "(Hwaiter & Hwaiters)"; first done.
    rewrite bool_decide_eq_false_2 //.
    iSplitR "Hwaiter"; last done.
    iApply (big_sepM_delete _ _ id); first done.
    rewrite bool_decide_eq_true_2.
    { rewrite prophecies۰opsｰapp /operations۰ids fmap_app. set_solver. }
    iFrame.
    iApply (big_sepM_impl with "Hwaiters").
    iIntros "!> %id' %waiter' %Hlookup' H".
    apply lookup_delete_Some in Hlookup' as (Hne & _).
    rewrite (bool_decide_ext (id' ∈ operations۰ids (prophecies۰ops (past ++ [ProphecyOp id w]))) (id' ∈ operations۰ids (prophecies۰ops past))).
    { rewrite prophecies۰opsｰapp /operations۰ids fmap_app. set_solver. }
    rewrite (bool_decide_ext (id' ∈ operations۰ids helped') (id' ∈ operations۰ids helped)); first auto.
    destruct (bool_decide (id' ∈ operations۰ids (prophecies۰ops past))); first done.
    destruct (bool_decide_reflect (id' ∈ operations۰ids helped)) as [Hid' | Hid']; last done.
    rewrite Hresult //.
  Qed.

  #[local] Lemma waiters۰statusesｰhelp γ ι waiters 𝑣 past helped help v :
    v = ops۰apply helped 𝑣 →
    helpable waiters past helped help →
    waiters۰statuses γ ι waiters 𝑣 helped past -∗
    model₂ γ v ={⊤ ∖ ↑ι}=∗
      waiters۰statuses γ ι waiters 𝑣 (helped ++ help) past ∗
      model₂ γ (ops۰apply help v).
  Proof.
    iInduction help as [| op help] "IH" forall (helped v).
    - iIntros "_ _ Hwaiters Hmodel₂". rewrite right_id. iFrame. done.
    - iIntros "%Hv %Hhelpable Hwaiters Hmodel₂".
      destruct Hhelpable as ((waiter & Hlookup & Hval) & Hdone & Hhelped & Hhelpable).
      iDestruct (big_sepM_delete with "Hwaiters") as "(Hwaiter & Hwaiters)"; first done.
      rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2 //.
      iDestruct "Hwaiter" as "(%Ψ & #Hpost & Hau)".
      rewrite /waiter۰au Hval.
      iMod "Hau" as "(%v' & Hmodel₁ & _ & HΨ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate (opkind۰apply op.(operation۰kind) v) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΨ" $! (opkind۰outcome op.(operation۰kind) v) with "[Hmodel₁]") as "HΨ".
      { iSplitR; last iExact "Hmodel₁".
        iPureIntro. apply opkind۰outcomeｰrel.
      }
      iAssert (waiters۰statuses γ ι waiters 𝑣 (helped ++ [op]) past) with "[HΨ Hwaiters]" as "Hwaiters".
      { iApply (big_sepM_delete _ _ op.(operation۰id)); first done.
        rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2.
        { rewrite /operations۰ids fmap_app. set_solver. }
        rewrite helped۰resultｰapp_not_in // /= decide_True // -Hv.
        iFrame "#∗".
        iApply (big_sepM_impl with "Hwaiters").
        iIntros "!> %id' %waiter' %Hlookup' H".
        apply lookup_delete_Some in Hlookup' as (Hne & _).
        rewrite (bool_decide_ext (id' ∈ operations۰ids (helped ++ [op])) (id' ∈ operations۰ids helped)).
        { rewrite /operations۰ids fmap_app. set_solver. }
        destruct (bool_decide (id' ∈ operations۰ids (prophecies۰ops past))); first done.
        destruct (bool_decide_reflect (id' ∈ operations۰ids helped)) as [Hid' | Hid']; last done.
        rewrite helped۰resultｰapp_in //.
      }
      assert (opkind۰apply op.(operation۰kind) v = ops۰apply (helped ++ [op]) 𝑣) as Hv'.
      { rewrite ops۰applyｰapp -Hv //. }
      iMod ("IH" with "[//] [//] Hwaiters Hmodel₂") as "(Hwaiters & Hmodel₂)".
      rewrite -assoc /=.
      by iFrame.
  Qed.

  #[local] Lemma waiterｰregister γ ι id req Ψ :
    inv' γ ι -∗
    identifier۰model id -∗
    AU <{
      ∃∃ v',
      model₁ γ v'
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ∀∀ b,
      ⌜request۰rel req b v'⌝ ∗
      model₁ γ (request۰apply req b v')
    , COMM
      Ψ (request۰result req b v')
    }> ={⊤}=∗
      ∃ waiter,
      ⌜waiter.(waiter۰request) = req⌝ ∗
      waiters۰elem γ id waiter ∗
      saved_pred waiter.(waiter۰post) Ψ ∗
      generation۰lb γ waiter.(waiter۰gen).
  Proof.
    iIntros "#Hinv Hid Hau".

    iMod (saved_predｰalloc Ψ) as "(%γ_post & #Hpost)".

    iInv "Hinv" as "(:inv۰inner =1)".
    pose waiter :=
      {|waiter۰request := req
      ; waiter۰post := γ_post
      ; waiter۰gen := g1
      |}.
    iMod (waitersｰinsert id waiter with "Hwaiters_auth Hid") as "(%Hlookup & Hwaiters_auth & Helem)".
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hgen".
    destruct (inv۰pureｰfresh id Hinv1) as (Hpast & Hhelped); first done.
    iSplitR "Helem".
    { iModIntro. iNext.
      iExists 𝑣1, g1, v1, vₛ1, snaps1, snap1, hist1, (<[id := waiter]> waiters1), helped1, past1, prophs1, mode1.
      iFrame.
      iSplitL.
      - iApply (waiters۰statusesｰinsert _ _ _ _ _ _ id waiter Ψ Hpast Hhelped Hlookup with "Hwaiters Hpost Hau").
      - iPureIntro. apply inv۰pureｰregister; done.
    }
    iModIntro. iExists waiter. iFrame "#∗". done.
  Qed.

  (* The common linearization step of [get] and [set]: consuming the prophesied operation [id]. *)
  #[local] Lemma waiterｰconsume γ ι 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode id (w : opkind) waiter Ψ :
    inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past (ProphecyOp id w :: prophs) mode →
    waiter.(waiter۰request) = opkind۰request w →
    waiter.(waiter۰gen) ≤ snap.(snap۰gen) →
    waiters۰auth γ waiters -∗
    waiters۰elem γ id waiter -∗
    saved_pred waiter.(waiter۰post) Ψ -∗
    waiters۰statuses γ ι waiters 𝑣 helped past -∗
    model₂ γ v ={⊤ ∖ ↑ι}=∗
      waiters۰auth γ waiters ∗
      waiters۰statuses γ ι waiters (opkind۰apply w 𝑣) (tail helped) (past ++ [ProphecyOp id w]) ∗
      model₂ γ (if helped is [] then opkind۰apply w v else v) ∗
      ⌜inv۰pure (opkind۰apply w 𝑣) g (if helped is [] then opkind۰apply w v else v) vₛ snaps snap hist waiters (tail helped) (past ++ [ProphecyOp id w]) prophs mode⌝ ∗
      ▷ Ψ (opkind۰result w 𝑣).
  Proof.
    iIntros "%Hinv %Hval %Hgen Hwaiters_auth Helem #Hpost Hwaiters Hmodel₂".
    iDestruct (waiters۰elemｰvalid with "Hwaiters_auth Helem") as %Hlookup.
    destruct (decide (id ∈ operations۰ids (prophecies۰ops past))) as [Hdone | Hdone].
    { iDestruct (big_sepM_lookup with "Hwaiters") as "Hwaiter"; first done.
      rewrite bool_decide_eq_true_2 //.
      iDestruct (waiters۰elemｰexclusive with "Helem Hwaiter") as %[].
    }
    destruct (inv۰pureｰwrite id w waiter Hinv Hlookup Hval Hdone Hgen) as (Hhelped & Hinv').
    iDestruct (waiters۰statusesｰwrite _ _ _ 𝑣 (opkind۰apply w 𝑣) helped (tail helped) _ _ w with "Hwaiters Helem") as "(Hwaiters & %Ψ' & #Hpost' & HΨ)".
    { done. }
    { done. }
    { intros id' Hid'.
      destruct Hhelped as [-> | Hhead]; first done.
      destruct helped as [| op helped]; first done.
      injection Hhead as ->.
      rewrite /operations۰ids /= elem_of_cons. naive.
    }
    { intros id' Hid' Hhelped'.
      destruct Hhelped as [-> | Hhead]; first set_solver.
      destruct helped as [| op helped]; first done.
      injection Hhead as ->.
      rewrite /= decide_False //.
    }
    iFrame.
    iAssert (|={⊤ ∖ ↑ι}=> Ψ' (opkind۰result w 𝑣) ∗ model₂ γ (if helped is [] then opkind۰apply w v else v))%I with "[HΨ Hmodel₂]" as ">(HΨ & $)".
    { destruct Hhelped as [-> | Hhead].
      - assert (bool_decide (id ∈ operations۰ids []) = false) as -> by (apply bool_decide_eq_false_2, not_elem_of_nil).
        assert (v = 𝑣) as -> by rewrite (inv۰pure۰model _ _ _ _ _ _ _ _ _ _ _ _ Hinv) //.
        rewrite /waiter۰au Hval.
        iMod "HΨ" as "(%v' & Hmodel₁ & _ & HΨ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod (modelｰupdate (opkind۰apply w 𝑣) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΨ" $! (opkind۰outcome w 𝑣) with "[Hmodel₁]") as "$"; last done.
        iSplitR; last iExact "Hmodel₁".
        iPureIntro. apply opkind۰outcomeｰrel.
      - destruct helped as [| op helped]; first done.
        injection Hhead as ->.
        rewrite bool_decide_eq_true_2.
        { rewrite /operations۰ids /=. set_solver. }
        rewrite /= decide_True //.
        iFrame. done.
    }
    iDestruct (saved_predｰagree (opkind۰result w 𝑣) with "Hpost Hpost'") as "Heq".
    iModIntro. iSplitR; first done.
    iNext. iRewrite "Heq". done.
  Qed.

  Lemma svar٠getｰspec γ ι :
    <<<
      svar۰inv γ ι
    | ∀∀ v,
      svar۰model γ v
    >>>
      svar٠get γ
      @ ↑ι
    <<<
      svar۰model γ v
    | RET v;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credit:"H£".
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".

    iMod (waiterｰregister _ _ id RequestGet (λ v, True -∗ Φ v)%I with "Hinv Hid [HΦ]") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)".
    { iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%v Hmodel₁".
      iAaccIntro with "Hmodel₁"; iSteps.
    }

    wp۰apply+ (svar٠forwardｰspec with "[$Ht_proph $Hinv $Hgen]") as "#Hsnapshot_lb".
    wp۰load. wp۰pures.

    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰load.
    iExists (Some (ProphecyOp id OpGet)). iSplitR; first done.
    iIntros "!> %prophs' -> Hprophet_model".
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps. }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  Lemma svar٠setｰspec γ ι v :
    <<<
      svar۰inv γ ι
    | ∀∀ v',
      svar۰model γ v'
    >>>
      svar٠set γ v
      @ ↑ι
    <<<
      svar۰model γ v
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credit:"H£".
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".

    iMod (waiterｰregister _ _ id (RequestSet v) (λ _, True -∗ Φ ()%V)%I with "Hinv Hid [HΦ]") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)".
    { iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%v' Hmodel₁".
      iAaccIntro with "Hmodel₁"; iSteps.
    }

    wp۰apply+ (svar٠forwardｰspec with "[$Ht_proph $Hinv $Hgen]") as "#Hsnapshot_lb".
    wp۰load. wp۰pures.

    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰store.
    iExists (Some (ProphecyOp id (OpSet v))). iSplitR; first done.
    iIntros "!> %prophs' -> Hprophet_model".
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps. }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  Lemma svar٠xchgｰspec γ ι v :
    <<<
      svar۰inv γ ι
    | ∀∀ w,
      svar۰model γ w
    >>>
      svar٠xchg γ v
      @ ↑ι
    <<<
      svar۰model γ v
    | RET w;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credit:"H£".
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".

    iMod (waiterｰregister _ _ id (RequestSet v) (λ w, True -∗ Φ w)%I with "Hinv Hid [HΦ]") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)".
    { iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%w Hmodel₁".
      iAaccIntro with "Hmodel₁"; iSteps.
    }

    wp۰apply+ (svar٠forwardｰspec with "[$Ht_proph $Hinv $Hgen]") as "#Hsnapshot_lb".
    wp۰load. wp۰pures.

    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰xchg.
    iExists (Some (ProphecyOp id (OpSet v))). iSplitR; first done.
    iIntros "!> %prophs' -> Hprophet_model".
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps. }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  Lemma svar٠casｰspec γ ι v1 v2 :
    <<<
      svar۰inv γ ι
    | ∀∀ v,
      svar۰model γ v
    >>>
      svar٠cas γ v1 v2
      @ ↑ι
    <<<
      ∃∃ b,
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      svar۰model γ (if b then v2 else v)
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credit:"H£".
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".

    iMod (waiterｰregister _ _ id (RequestCas v1 v2) (λ w, True -∗ Φ w)%I with "Hinv Hid HΦ") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)".

    wp۰apply+ (svar٠forwardｰspec with "[$Ht_proph $Hinv $Hgen]") as "#Hsnapshot_lb".
    wp۰load. wp۰pures.

    iInv "Hinv" as "(:inv۰inner =0)".
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    iApply (wpｰcasｰnobranch' with "Ht_value"). iIntros "!> %b %Hcas Ht_value".
    iExists (Some (ProphecyOp id (OpCas v1 v2 b))). iSplitR; first done.
    iIntros "%prophs' -> Hprophet_model".
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    destruct (opkind۰applyｰcas 𝑣0 v1 v2 b Hcas) as (Happly & Hresult).
    rewrite Happly Hresult in Hinv' |- *.
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps. }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  Lemma svar٠clickｰspec γ ι vₛ :
    <<<
      svar۰inv γ ι ∗
      svar۰scanner γ Own vₛ
    | ∀∀ v,
      svar۰model γ v
    >>>
      svar٠click γ
      @ ↑ι
    <<<
      svar۰model γ v
    | RET ();
      svar۰scanner γ Own v
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:scanner)) HΦ".

    wp۰rec.
    wp۰apply (genｰspecｰscanner with "[$Hinv $Hscanner₁]") as "Hscanner₁".
    wp۰pures.

    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰store.
    iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
    destruct (inv۰pureｰclick Hinv1) as (help & mode' & Hhelpable & Hmode' & Hinv').
    iMod (waiters۰statusesｰhelp with "Hwaiters Hmodel₂") as "(Hwaiters & Hmodel₂)".
    { apply (inv۰pure۰model _ _ _ _ _ _ _ _ _ _ _ _ Hinv1). }
    { done. }
    set v' := ops۰apply help v1.
    iMod "HΦ" as "(%v_ & Hmodel₁ & _ & HΦ)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "Hmodel₁") as "HΦ".
    iMod (scannerｰupdate v' (S g) with "Hscanner₁ Hscanner₂") as "(Hscanner₁ & Hscanner₂)".
    iMod (generationｰupdate with "Hgeneration_auth") as "Hgeneration_auth".
    iMod (histｰupdate v' (pred (length snaps1)) with "Hhist_auth") as "Hhist_auth".
    iMod (doomｰupdate mode' with "Hdoom_auth") as "Hdoom_auth"; first done.
    iSplitR "Hscanner₁ HΦ".
    { iModIntro. iNext.
      iExists 𝑣1, (S g), v', v', snaps1, snap1, (hist1 ++ [(v', pred (length snaps1))]), waiters1, (helped1 ++ help), past1, prophs1, mode'.
      replace (⁺g + 1)%Z with (⁺(S g)) by lia.
      iFrame. done.
    }
    iModIntro. iApply "HΦ". iExists (S g). done.
  Qed.

  Lemma svar٠observeｰspec γ ι dq vₛ :
    {{{
      svar۰inv γ ι ∗
      svar۰scanner γ dq vₛ
    }}}
      svar٠observe γ
    {{{
      RET vₛ;
      svar۰scanner γ dq vₛ
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:scanner)) HΦ".

    wp۰rec.

    iAssert (|={⊤}=> generation۰lb γ g ∗ scanner₁ γ dq vₛ g)%I with "[Hscanner₁]" as ">(#Hg & Hscanner₁)".
    { iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
      iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg".
      iSplitR "Hscanner₁". { iFrameSteps. }
      iFrameSteps.
    }

    wp۰apply (svar٠forwardｰspec with "[$Ht_proph $Hinv $Hg]") as "#Hsnapshot_lb".
    wp۰pures.

    wp۰bind (_.{snapshot})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    destruct (inv۰pureｰstable Hinv1 Hgen) as (_ & Hval).
    iSplitR "Hscanner₁ HΦ". { iFrameSteps. }
    iModIntro.

    wp۰pures.
    rewrite Hval. iApply "HΦ". iFrameSteps.
  Qed.
End svar_G.

Require zoo_saturn.svar__opaque.

Please opacify.
