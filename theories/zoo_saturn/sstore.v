Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.mono_gset.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_wise.
Require Export zoo_saturn.sstore__code.
Require Import zoo_saturn.sstore__types.
Require Import zoo_saturn.svar__pure.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type g gₛ : nat.
Implicit Type v vₛ 𝑣 𝑣ₛ w : val.
Implicit Type id : identifier.
Implicit Type ι : namespace.
Implicit Type r : location.
Implicit Type vs ws : gmap location val.

Implicit Type proph : prophecy.
Implicit Type prophs past q : list prophecy.
Implicit Type op : operation.
Implicit Type ops helped help : list operation.
Implicit Type waiter : waiter.
Implicit Type waiters : gmap identifier waiter.
Implicit Type snap : snap.
Implicit Type snaps : list snap.
Implicit Type mode : mode.

(* The prophecies of all references are tangled in a single prophecy variable,
   indexed by references. *)

(* ------------------------------------------------------------------------ *)
(* Global prophecy. *)

#[local] Definition prophet :=
  {|prophet_typed۰type :=
      location * prophecy
  ; prophet_typed۰of_val v w :=
      match w with
      | ValBlock _ Tag1 [ValLoc r; ValId id] =>
          Some $ Some (r, ProphecyOp id OpGet)
      | ValBlock _ Tag3 [ValLoc r; ValId id; v'] =>
          Some $ Some (r, ProphecyOp id (OpSet v'))
      | ValBlock _ Tag4 [ValLoc r; ValId id; v1; v2] =>
          match v with
          | ValBool b =>
              Some $ Some (r, ProphecyOp id (OpCas v1 v2 b))
          | _ =>
              None
          end
      | _ =>
          match v, w with
          | ValBool false, ValBlock _ Tag0 _ =>
              Some None
          | ValBool true, ValBlock _ Tag0 [ValLoc r; v; ValInt g] =>
              Some $ Some (r, ProphecyForward v ₊g)
          | ()%V, ValBlock _ Tag2 [ValLoc r; ValId id; v] =>
              Some $ Some (r, ProphecyOp id (OpSet v))
          | _, _ =>
              None
          end
      end
  |}.

Implicit Type iproph : location * prophecy.
Implicit Type iprophs ipast : list (location * prophecy).

#[local] Definition untangle iprophs r :=
  (filter (λ iproph, iproph.1 = r) iprophs).*2.

#[local] Lemma untangleｰnil r :
  untangle [] r = [].
Proof.
  done.
Qed.
#[local] Lemma untangleｰcons iproph iprophs r :
  untangle (iproph :: iprophs) r = if decide (iproph.1 = r) then iproph.2 :: untangle iprophs r else untangle iprophs r.
Proof.
  rewrite /untangle filter_cons.
  case_decide; done.
Qed.
#[local] Lemma untangleｰconsｰTrue r proph iprophs :
  untangle ((r, proph) :: iprophs) r = proph :: untangle iprophs r.
Proof.
  rewrite untangleｰcons decide_True //.
Qed.
#[local] Lemma untangleｰconsｰFalse r r' proph iprophs :
  r ≠ r' →
  untangle ((r, proph) :: iprophs) r' = untangle iprophs r'.
Proof.
  intros. rewrite untangleｰcons decide_False //.
Qed.
#[local] Lemma untangleｰapp iprophs1 iprophs2 r :
  untangle (iprophs1 ++ iprophs2) r = untangle iprophs1 r ++ untangle iprophs2 r.
Proof.
  rewrite /untangle filter_app fmap_app //.
Qed.
#[local] Lemma untangleｰsnocｰTrue ipast r proph :
  untangle (ipast ++ [(r, proph)]) r = untangle ipast r ++ [proph].
Proof.
  rewrite untangleｰapp untangleｰconsｰTrue //.
Qed.
#[local] Lemma untangleｰsnocｰFalse ipast r r' proph :
  r ≠ r' →
  untangle (ipast ++ [(r, proph)]) r' = untangle ipast r'.
Proof.
  intros. rewrite untangleｰapp untangleｰconsｰFalse // right_id //.
Qed.
#[local] Lemma untangleｰfresh ipast r :
  (∀ iproph, iproph ∈ ipast → iproph.1 ≠ r) →
  untangle ipast r = [].
Proof.
  induction ipast as [| iproph ipast IH] => H; first done.
  rewrite untangleｰcons decide_False; first (apply H; set_solver).
  apply IH. set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* Creation of a reference. *)

(* A new reference is not observed by the scanner before the next click, so its
   scanner value is irrelevant: we choose the value the prophecy predicts. *)
#[local] Definition ref۰scanner v g prophs :=
  match future۰target g prophs with
  | Some (𝑣, g') =>
      if decide (g' = g ∧ g ≠ 0) then 𝑣 else v
  | None =>
      v
  end.

#[local] Lemma inv۰pureｰcreate bid v g prophs :
  let vₛ := ref۰scanner v g prophs in
  inv۰pure v g v vₛ [Snap bid v 0 0] (Snap bid v 0 0) (replicate g (v, 0) ++ [(vₛ, 0)]) ∅ [] [] prophs Good.
Proof.
  intros vₛ.
  assert (∀ h vh idx, (replicate g (v, 0) ++ [(vₛ, 0)]) !! h = Some (vh, idx) → idx = 0) as Hidx.
  { intros h vh idx [([= _ ->] & _)%lookup_replicate | (_ & (_ & [= _ ->])%list_lookup_singleton_Some)]%lookup_app_Some; done. }
  split.
  all: try done.
  all: try (rewrite length_app length_replicate /=; lia).
  all: try (exists 0; rewrite lookup_app_r length_replicate // Nat.sub_diag //).
  all: try (intros h vh idx ->%Hidx; simpl; lia).
  all: try (intros h vh idx [| []] ? ? ? ?; [lia | done..]).
  all: try apply prefix_nil.
  - intros [| i] snap'; [intros [= <-] => /=; lia | destruct i; done].
  - set_solver.
  - set_solver.
  - rewrite /inv۰state /=.
    case_decide as Hg.
    + split_and!; try done.
      rewrite /vₛ /ref۰scanner.
      destruct (future۰target g prophs) as [(? & ?) |]; last done.
      rewrite decide_False //. lia.
    + split; first lia. split; first done.
      intros 𝑣 Htarget _.
      rewrite /vₛ /ref۰scanner Htarget decide_True //.
Qed.

(* ------------------------------------------------------------------------ *)
(* Ghost state. *)

Record ref۰names := RefNames
  { ref۰names۰snapshot : gname
  ; ref۰names۰snaps : gname
  ; ref۰names۰hist : gname
  ; ref۰names۰doom : gname
  ; ref۰names۰waiters : gname
  }.
Add Printing Constructor ref۰names.

Zoo name :=
  { self : location
  ; prophet : prophet_wise۰name
  ; model : gname
  ; scanner : gname
  ; generation : gname
  ; refs : gname
  ; dom : gname
  }.

Zoo global :=
  { prophet : prophet_wise prophet
  ; model : twins (leibnizO (gmap location val))
  ; scanner : twins (leibnizO (gmap location val * nat))
  ; generation : auth_nat_max
  ; snapshot : auth_nat_max
  ; snaps : mono_list snap
  ; hist : mono_list (val * nat)
  ; doom : auth_nat_max
  ; refs : ghost_map location ref۰names : iris
  ; dom : mono_gset location
  ; waiters : ghost_map identifier waiter : iris
  ; waiter۰post : saved_pred val
  }.

Section sstore_G.
  Context `{sstore_G : SstoreG Σ}.

  Implicit Type ρ : ref۰names.
  Implicit Type refs : gmap location ref۰names.
  Implicit Type Ψ Φ : val → iProp Σ.

  #[local] Definition prophet۰model γ ipast iprophs :=
    prophet_wise۰model prophet γ.(sstore۰name۰prophet) ipast iprophs.
  #[local] Definition prophet۰snapshot γ ipast iprophs :=
    prophet_wise۰snapshot prophet γ.(sstore۰name۰prophet) ipast iprophs.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ (twins۰G := sstore۰G۰model۰G) γ_model Own vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(sstore۰name۰model).
  #[local] Definition model₂' γ_model vs :=
    twins۰twin₂ (twins۰G := sstore۰G۰model۰G) γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(sstore۰name۰model).

  #[local] Definition dom۰auth γ (s : gset location) :=
    mono_gset۰auth γ.(sstore۰name۰dom) (DfracOwn 1) s.
  #[local] Definition dom۰lb γ (s : gset location) :=
    mono_gset۰lb γ.(sstore۰name۰dom) s.
  #[local] Definition dom۰elem γ r :=
    mono_gset۰elem γ.(sstore۰name۰dom) r.

  (* The model also owns the set of allocated references. *)
  #[local] Definition model۰full γ vs : iProp Σ :=
    model₁ γ vs ∗
    dom۰auth γ (dom vs).

  #[local] Definition scanner₁' γ_scanner dq ws g :=
    twins۰twin₁ γ_scanner dq (ws, g).
  #[local] Definition scanner₁ γ :=
    scanner₁' γ.(sstore۰name۰scanner).
  #[local] Definition scanner₂' γ_scanner ws g :=
    twins۰twin₂ γ_scanner (ws, g).
  #[local] Definition scanner₂ γ :=
    scanner₂' γ.(sstore۰name۰scanner).

  #[local] Definition generation۰auth' γ_generation g :=
    auth_nat_max۰auth γ_generation Own g.
  #[local] Definition generation۰auth γ :=
    generation۰auth' γ.(sstore۰name۰generation).
  #[local] Definition generation۰lb γ g :=
    auth_nat_max۰lb γ.(sstore۰name۰generation) g.

  #[local] Definition refs۰auth' γ_refs refs :=
    ghost_map_auth γ_refs (DfracOwn 1) refs.
  #[local] Definition refs۰auth γ :=
    refs۰auth' γ.(sstore۰name۰refs).
  #[local] Definition ref۰elem γ r ρ :=
    ghost_map_elem γ.(sstore۰name۰refs) r DfracDiscarded ρ.

  #[local] Definition snapshot۰auth ρ gₛ :=
    auth_nat_max۰auth ρ.(ref۰names۰snapshot) Own gₛ.
  #[local] Definition snapshot۰lb ρ gₛ :=
    auth_nat_max۰lb ρ.(ref۰names۰snapshot) gₛ.

  #[local] Definition snaps۰auth ρ snaps :=
    mono_list۰auth ρ.(ref۰names۰snaps) (DfracOwn 1) snaps.
  #[local] Definition snaps۰lb ρ snaps :=
    mono_list۰lb ρ.(ref۰names۰snaps) snaps.

  #[local] Definition hist۰auth ρ (hist : list (val * nat)) :=
    mono_list۰auth ρ.(ref۰names۰hist) (DfracOwn 1) hist.
  #[local] Definition hist۰at ρ h (vh : val) (idx : nat) :=
    mono_list۰at ρ.(ref۰names۰hist) h (vh, idx).

  #[local] Definition doom۰auth ρ n :=
    auth_nat_max۰auth ρ.(ref۰names۰doom) Own n.
  #[local] Definition doom۰lb ρ :=
    auth_nat_max۰lb ρ.(ref۰names۰doom) 1.

  #[local] Definition waiters۰auth' γ_waiters waiters : iProp Σ :=
    ghost_map_auth γ_waiters (DfracOwn 1) waiters ∗
    [∗ set] id ∈ dom waiters, identifier۰model id.
  #[local] Definition waiters۰auth ρ :=
    waiters۰auth' ρ.(ref۰names۰waiters).
  #[local] Definition waiters۰elem ρ id waiter :=
    ghost_map_elem ρ.(ref۰names۰waiters) id (DfracOwn 1) waiter.

  #[local] Definition waiter۰au' γ ι r req Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      model۰full γ vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ∀∀ v b,
      ⌜vs !! r = Some v⌝ ∗
      ⌜request۰rel req b v⌝ ∗
      model۰full γ (<[r := request۰apply req b v]> vs)
    , COMM
      Ψ (request۰result req b v)
    }>.
  #[local] Definition waiter۰au γ ι r waiter Ψ :=
    waiter۰au' γ ι r waiter.(waiter۰request) Ψ.

  #[local] Definition waiters۰statuses γ ι r ρ waiters 𝑣 helped past : iProp Σ :=
    [∗ map] id ↦ waiter ∈ waiters,
      if bool_decide (id ∈ operations۰ids (prophecies۰ops past)) then
        waiters۰elem ρ id waiter
      else
        ∃ Ψ,
        saved_pred waiter.(waiter۰post) Ψ ∗
        if bool_decide (id ∈ operations۰ids helped) then
          Ψ (helped۰result 𝑣 helped id)
        else
          waiter۰au γ ι r waiter Ψ.

  #[local] Definition ref۰inv γ ι r ρ g v (wₛ : option val) past prophs : iProp Σ :=
    ∃ 𝑣 vₛ snaps snap hist waiters helped mode,
    r.[ref_value] ↦ 𝑣 ∗
    r.[ref_snapshot] ↦ snap۰to_val snap ∗
    snapshot۰auth ρ snap.(snap۰gen) ∗
    snaps۰auth ρ snaps ∗
    hist۰auth ρ hist ∗
    doom۰auth ρ (mode۰doomed mode) ∗
    waiters۰auth ρ waiters ∗
    waiters۰statuses γ ι r ρ waiters 𝑣 helped past ∗
    ⌜inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode⌝ ∗
    ⌜∀ w, wₛ = Some w → w = vₛ⌝.
  #[local] Instance : CustomIpat "ref۰inv" :=
    " ( %𝑣{}
      & %vₛ{}
      & %snaps{}
      & %snap{}
      & %hist{}
      & %waiters{}
      & %helped{}
      & %mode{}
      & >Hr_value
      & >Hr_snapshot
      & >Hsnapshot_auth
      & >Hsnaps_auth
      & >Hhist_auth
      & >Hdoom_auth
      & >Hwaiters_auth
      & Hwaiters
      & >%Hinv{}
      & >%Hwₛ{}
      )
    ".

  #[local] Definition refs۰inv γ ι refs g vs ws ipast iprophs : iProp Σ :=
    [∗ map] r ↦ ρ ∈ refs,
      ref۰inv γ ι r ρ g (vs !!! r) (ws !! r) (untangle ipast r) (untangle iprophs r).

  #[local] Definition inv۰inner γ ι : iProp Σ :=
    ∃ g vs ws refs ipast iprophs,
    γ.(sstore۰name۰self).[gen] ↦ #g ∗
    model₂ γ vs ∗
    scanner₂ γ ws g ∗
    generation۰auth γ g ∗
    refs۰auth γ refs ∗
    prophet۰model γ ipast iprophs ∗
    ⌜dom vs = dom refs⌝ ∗
    ⌜dom ws ⊆ dom refs⌝ ∗
    ⌜∀ iproph, iproph ∈ ipast → iproph.1 ∈ dom refs⌝ ∗
    refs۰inv γ ι refs g vs ws ipast iprophs.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %g{}
      & %vs{}
      & %ws{}
      & %refs{}
      & %ipast{}
      & %iprophs{}
      & >Ht_gen
      & >Hmodel₂
      & >Hscanner₂
      & >Hgeneration_auth
      & >Hrefs_auth
      & >Hprophet_model
      & >%Hvs{}
      & >%Hws{}
      & >%Hipast{}
      & Hrefs
      )
    ".
  #[local] Definition inv' γ ι :=
    inv ι (inv۰inner γ ι).
  Please Definition sstore۰inv γ ι : iProp Σ :=
    γ.(sstore۰name۰self).[proph] ↦□ γ.(sstore۰name۰prophet) ∗
    inv' γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( #Ht_proph
      & #Hinv
      )
    ".

  Please Definition sstore۰model :=
    model۰full.

  Please Definition sstore۰ref γ r : iProp Σ :=
    ∃ ρ,
    ref۰elem γ r ρ ∗
    dom۰elem γ r.
  #[local] Instance : CustomIpat "ref" :=
    " ( %ρ
      & #Hρ
      & #Hdom_elem
      )
    ".

  Please Definition sstore۰scanner γ dq ws : iProp Σ :=
    ∃ g,
    scanner₁ γ dq ws g ∗
    dom۰lb γ (dom ws).
  #[local] Instance : CustomIpat "scanner" :=
    " ( %g{}
      & Hscanner₁{_{}}
      & #Hdom_lb{_{}}
      )
    ".

  Zoo derive Timeless for sstore۰model.
  Zoo derive Timeless for sstore۰scanner.

  Zoo derive Persistent for sstore۰inv.
  Zoo derive Persistent for sstore۰ref.

  #[local] Lemma modelｰalloc vs :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model vs ∗
      model₂' γ_model vs.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma modelｰagree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma scannerｰalloc ws :
    ⊢ |==>
      ∃ γ_scanner,
      scanner₁' γ_scanner Own ws 0 ∗
      scanner₂' γ_scanner ws 0.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma scannerｰagree γ dq ws1 g1 ws2 g2 :
    scanner₁ γ dq ws1 g1 -∗
    scanner₂ γ ws2 g2 -∗
      ⌜ws1 = ws2⌝ ∗
      ⌜g1 = g2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (twinsｰagreeｰL with "H1 H2") as %[= -> ->] => //.
  Qed.
  #[local] Lemma scannerｰupdate {γ ws1 g1 ws2 g2} ws g :
    scanner₁ γ Own ws1 g1 -∗
    scanner₂ γ ws2 g2 ==∗
      scanner₁ γ Own ws g ∗
      scanner₂ γ ws g.
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

  #[local] Lemma refsｰalloc :
    ⊢ |==>
      ∃ γ_refs,
      refs۰auth' γ_refs ∅.
  Proof.
    iMod (ghost_map_alloc_empty (K := location) (V := ref۰names)) as "(%γ_refs & Hauth)".
    iExists γ_refs. done.
  Qed.
  #[local] Lemma ref۰elemｰvalid γ refs r ρ :
    refs۰auth γ refs -∗
    ref۰elem γ r ρ -∗
    ⌜refs !! r = Some ρ⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma refsｰinsert {γ refs} r ρ :
    refs !! r = None →
    refs۰auth γ refs ⊢ |==>
      refs۰auth γ (<[r := ρ]> refs) ∗
      ref۰elem γ r ρ.
  Proof.
    iIntros "%Hlookup Hauth".
    iMod (ghost_map_insert with "Hauth") as "($ & Helem)"; first done.
    iApply (ghost_map_elem_persist with "Helem").
  Qed.

  #[local] Lemma snapshotｰalloc :
    ⊢ |==>
      ∃ γ_snapshot,
      auth_nat_max۰auth γ_snapshot Own 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma snapshot۰lbｰget ρ gₛ :
    snapshot۰auth ρ gₛ ⊢
    snapshot۰lb ρ gₛ.
  Proof.
    apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma snapshot۰lbｰvalid ρ gₛ1 gₛ2 :
    snapshot۰auth ρ gₛ1 -∗
    snapshot۰lb ρ gₛ2 -∗
    ⌜gₛ2 ≤ gₛ1⌝.
  Proof.
    apply auth_nat_max۰lbｰvalid.
  Qed.
  #[local] Lemma snapshotｰupdate {ρ gₛ} gₛ' :
    gₛ ≤ gₛ' →
    snapshot۰auth ρ gₛ ⊢ |==>
    snapshot۰auth ρ gₛ'.
  Proof.
    apply auth_nat_maxｰupdate.
  Qed.

  #[local] Lemma snapsｰalloc snaps :
    ⊢ |==>
      ∃ γ_snaps,
      mono_list۰auth γ_snaps (DfracOwn 1) snaps.
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma snaps۰lbｰget ρ snaps :
    snaps۰auth ρ snaps ⊢
    snaps۰lb ρ snaps.
  Proof.
    apply mono_list۰lbｰget.
  Qed.
  #[local] Lemma snaps۰lbｰvalid ρ snaps1 snaps2 :
    snaps۰auth ρ snaps1 -∗
    snaps۰lb ρ snaps2 -∗
    ⌜snaps2 `prefix_of` snaps1⌝.
  Proof.
    apply mono_list۰lbｰvalid.
  Qed.
  #[local] Lemma snapsｰupdate {ρ snaps} snap :
    snaps۰auth ρ snaps ⊢ |==>
    snaps۰auth ρ (snaps ++ [snap]).
  Proof.
    apply mono_listｰupdateｰsnoc.
  Qed.

  #[local] Lemma histｰalloc hist :
    ⊢ |==>
      ∃ γ_hist,
      mono_list۰auth γ_hist (DfracOwn 1) hist.
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma hist۰atｰget {ρ hist} h vh idx :
    hist !! h = Some (vh, idx) →
    hist۰auth ρ hist ⊢
    hist۰at ρ h vh idx.
  Proof.
    apply mono_list۰atｰget.
  Qed.
  #[local] Lemma hist۰atｰvalid ρ hist h vh idx :
    hist۰auth ρ hist -∗
    hist۰at ρ h vh idx -∗
    ⌜hist !! h = Some (vh, idx)⌝.
  Proof.
    apply mono_list۰atｰvalid.
  Qed.
  #[local] Lemma histｰupdate {ρ hist} vh idx :
    hist۰auth ρ hist ⊢ |==>
    hist۰auth ρ (hist ++ [(vh, idx)]).
  Proof.
    apply mono_listｰupdateｰsnoc.
  Qed.

  #[local] Lemma doomｰalloc :
    ⊢ |==>
      ∃ γ_doom,
      auth_nat_max۰auth γ_doom Own 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma doom۰lbｰget ρ mode :
    mode ≠ Good →
    doom۰auth ρ (mode۰doomed mode) ⊢
    doom۰lb ρ.
  Proof.
    destruct mode; first done.
    intros _. apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma doom۰lbｰvalid ρ mode :
    doom۰auth ρ (mode۰doomed mode) -∗
    doom۰lb ρ -∗
    ⌜mode ≠ Good⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_nat_max۰lbｰvalid with "Hauth Hlb") as %?.
    iPureIntro. intros ->. simpl in *. lia.
  Qed.
  #[local] Lemma doomｰupdate {ρ mode} mode' :
    mode۰doomed mode ≤ mode۰doomed mode' →
    doom۰auth ρ (mode۰doomed mode) ⊢ |==>
    doom۰auth ρ (mode۰doomed mode').
  Proof.
    apply auth_nat_maxｰupdate.
  Qed.

  #[local] Lemma waitersｰalloc :
    ⊢ |==>
      ∃ γ_waiters,
      waiters۰auth' γ_waiters ∅.
  Proof.
    iMod (ghost_map_alloc_empty (K := identifier) (V := waiter)) as "(%γ_waiters & Hauth)".
    iExists γ_waiters. iFrame.
    iApply big_sepS_empty => //.
  Qed.
  #[local] Lemma waiters۰elemｰexclusive ρ id waiter1 waiter2 :
    waiters۰elem ρ id waiter1 -∗
    waiters۰elem ρ id waiter2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %(? & _). done.
  Qed.
  #[local] Lemma waiters۰elemｰvalid ρ waiters id waiter :
    waiters۰auth ρ waiters -∗
    waiters۰elem ρ id waiter -∗
    ⌜waiters !! id = Some waiter⌝.
  Proof.
    iIntros "(Hauth & _) Helem".
    iApply (ghost_map_lookup with "Hauth Helem").
  Qed.
  #[local] Lemma waitersｰinsert {ρ waiters} id waiter :
    waiters۰auth ρ waiters -∗
    identifier۰model id ==∗
      ⌜waiters !! id = None⌝ ∗
      waiters۰auth ρ (<[id := waiter]> waiters) ∗
      waiters۰elem ρ id waiter.
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

  #[local] Zoo derive Timeless for waiters۰auth.

  Opaque waiters۰auth'.

  #[local] Lemma refs۰invｰacc {γ ι refs g vs ws ipast iprophs} r ρ :
    refs !! r = Some ρ →
    refs۰inv γ ι refs g vs ws ipast iprophs ⊢
      ref۰inv γ ι r ρ g (vs !!! r) (ws !! r) (untangle ipast r) (untangle iprophs r) ∗
      ( ∀ vs' ipast' iprophs',
        ⌜∀ r', r' ≠ r → vs' !!! r' = vs !!! r'⌝ -∗
        ⌜∀ r', r' ≠ r → untangle ipast' r' = untangle ipast r'⌝ -∗
        ⌜∀ r', r' ≠ r → untangle iprophs' r' = untangle iprophs r'⌝ -∗
        ref۰inv γ ι r ρ g (vs' !!! r) (ws !! r) (untangle ipast' r) (untangle iprophs' r) -∗
        refs۰inv γ ι refs g vs' ws ipast' iprophs'
      ).
  Proof.
    iIntros "%Hlookup Hrefs".
    iDestruct (big_sepM_delete with "Hrefs") as "($ & Hrefs)"; first done.
    iIntros "%vs' %ipast' %iprophs' %Hvs %Hipast %Hiprophs Href".
    iApply (big_sepM_delete _ _ r); first done. iFrame.
    iApply (big_sepM_impl with "Hrefs").
    iIntros "!> %r' %ρ' %Hlookup' Href".
    apply lookup_delete_Some in Hlookup' as (Hne & _).
    rewrite Hvs; first congruence.
    rewrite Hipast; first congruence.
    rewrite Hiprophs; first congruence.
    done.
  Qed.
  #[local] Lemma refs۰invｰacc' {γ ι refs g vs ws ipast iprophs} r ρ :
    refs !! r = Some ρ →
    ▷ refs۰inv γ ι refs g vs ws ipast iprophs ⊢
      ▷ ref۰inv γ ι r ρ g (vs !!! r) (ws !! r) (untangle ipast r) (untangle iprophs r) ∗
      ▷ ( ∀ vs' ipast' iprophs',
          ⌜∀ r', r' ≠ r → vs' !!! r' = vs !!! r'⌝ -∗
          ⌜∀ r', r' ≠ r → untangle ipast' r' = untangle ipast r'⌝ -∗
          ⌜∀ r', r' ≠ r → untangle iprophs' r' = untangle iprophs r'⌝ -∗
          ref۰inv γ ι r ρ g (vs' !!! r) (ws !! r) (untangle ipast' r) (untangle iprophs' r) -∗
          refs۰inv γ ι refs g vs' ws ipast' iprophs'
        ).
  Proof.
    intros Hlookup.
    rewrite refs۰invｰacc // bi.later_sep //.
  Qed.

  Lemma sstoreｰmodelｰref γ vs r :
    sstore۰model γ vs -∗
    sstore۰ref γ r -∗
    ⌜r ∈ dom vs⌝.
  Proof.
    iIntros "(_ & Hdom_auth) (:ref)".
    iApply (mono_gset۰elemｰvalid with "Hdom_auth Hdom_elem").
  Qed.

  Lemma sstoreｰmodelｰscanner γ vs dq ws :
    sstore۰model γ vs -∗
    sstore۰scanner γ dq ws -∗
    ⌜dom ws ⊆ dom vs⌝.
  Proof.
    iIntros "(_ & Hdom_auth) (:scanner)".
    iApply (mono_gset۰lbｰvalid with "Hdom_auth Hdom_lb").
  Qed.

  Lemma sstore٠createｰspec ι :
    {{{
      True
    }}}
      sstore٠create ()
    {{{
      γ
    , RET γ;
      sstore۰inv γ ι ∗
      sstore۰model γ ∅ ∗
      sstore۰scanner γ Own ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (prophet_wiseｰwpｰproph prophet with "[//]") as (pid iprophs) "Hprophet_model".
    wp۰block t as "Ht_gen #Ht_proph".

    iMod (modelｰalloc ∅) as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod (scannerｰalloc ∅) as "(%γ_scanner & Hscanner₁ & Hscanner₂)".
    iMod generationｰalloc as "(%γ_generation & Hgeneration_auth)".
    iMod refsｰalloc as "(%γ_refs & Hrefs_auth)".
    iMod (mono_gsetｰalloc (A := location) ∅) as "(%γ_dom & Hdom_auth)".
    iDestruct (mono_gset۰lbｰget with "Hdom_auth") as "#Hdom_lb".

    pose γ :=
      {|sstore۰name۰self := t
      ; sstore۰name۰prophet := pid
      ; sstore۰name۰model := γ_model
      ; sstore۰name۰scanner := γ_scanner
      ; sstore۰name۰generation := γ_generation
      ; sstore۰name۰refs := γ_refs
      ; sstore۰name۰dom := γ_dom
      |}.

    iMod (inv_alloc ι _ (inv۰inner γ ι) with "[Ht_gen Hmodel₂ Hscanner₂ Hgeneration_auth Hrefs_auth Hprophet_model]") as "#Hinv".
    { iNext. iExists 0, ∅, ∅, ∅, [], iprophs.
      iFrame. rewrite /refs۰inv big_sepM_empty.
      iPureIntro. split_and!; set_solver.
    }
    iApply ("HΦ" $! γ).
    iFrame "#∗". done.
  Qed.

  Lemma sstore٠refｰspec γ ι v :
    <<<
      sstore۰inv γ ι
    | ∀∀ vs,
      sstore۰model γ vs
    >>>
      sstore٠ref γ v
      @ ↑ι
    <<<
      ∃∃ r,
      ⌜vs !! r = None⌝ ∗
      sstore۰model γ (<[r := v]> vs) ∗
      sstore۰ref γ r
    | RET #r;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    wp۰block۰generative bid.
    wp۰block r as "Hv Hs".
    iInv "Hinv" as "(:inv۰inner =1)".
    destruct (refs1 !! r) as [ρ |] eqn:Hrefs_lookup.
    { iDestruct (big_sepM_lookup with "Hrefs") as "(:ref۰inv)"; first done.
      iDestruct (pointstoｰexclusive with "Hv Hr_value") as %[].
    }
    assert (vs1 !! r = None) as Hvs_lookup.
    { apply not_elem_of_dom. rewrite Hvs1. apply not_elem_of_dom. done. }
    assert (ws1 !! r = None) as Hws_lookup.
    { apply not_elem_of_dom. intros (? & ?)%Hws1%elem_of_dom. congruence. }
    assert (untangle ipast1 r = []) as Hipast_r.
    { apply untangleｰfresh. intros iproph Hiproph <-.
      apply Hipast1, elem_of_dom in Hiproph as (? & ?). congruence.
    }

    iMod snapshotｰalloc as "(%γ_snapshot & Hsnapshot_auth)".
    iMod (snapsｰalloc [Snap bid v 0 0]) as "(%γ_snaps & Hsnaps_auth)".
    set vₛ := ref۰scanner v g1 (untangle iprophs1 r).
    iMod (histｰalloc (replicate g1 (v, 0) ++ [(vₛ, 0)])) as "(%γ_hist & Hhist_auth)".
    iMod doomｰalloc as "(%γ_doom & Hdoom_auth)".
    iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".
    pose ρ :=
      {|ref۰names۰snapshot := γ_snapshot
      ; ref۰names۰snaps := γ_snaps
      ; ref۰names۰hist := γ_hist
      ; ref۰names۰doom := γ_doom
      ; ref۰names۰waiters := γ_waiters
      |}.
    iMod (refsｰinsert r ρ with "Hrefs_auth") as "(Hrefs_auth & #Hρ)"; first done.

    iMod "HΦ" as "(%vs & (Hmodel₁ & Hdom_auth) & _ & HΦ)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod (modelｰupdate (<[r := v]> vs1) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod (mono_gsetｰinsert' r with "Hdom_auth") as "(Hdom_auth & #Hdom_elem)".
    iMod ("HΦ" $! r with "[$Hmodel₁ Hdom_auth]") as "HΦ".
    { iSplitR; first done. rewrite /dom۰auth dom_insert_L. iFrame. iExists ρ. iFrame "#". }

    iSplitR "HΦ".
    { iModIntro. iNext.
      iExists g1, (<[r := v]> vs1), ws1, (<[r := ρ]> refs1), ipast1, iprophs1.
      iFrame.
      iSplitR.
      { iPureIntro. rewrite !dom_insert_L. set_solver. }
      iSplitR.
      { iPureIntro. rewrite dom_insert_L. set_solver. }
      iSplitR.
      { iPureIntro. intros iproph Hiproph. rewrite dom_insert_L. apply Hipast1 in Hiproph. set_solver. }
      iApply (big_sepM_insert with "[-]"); first done.
      iSplitR "Hrefs".
      - iExists v, vₛ, [Snap bid v 0 0], (Snap bid v 0 0), (replicate g1 (v, 0) ++ [(vₛ, 0)]), ∅, [], Good.
        rewrite lookup_total_insert_eq Hipast_r Hws_lookup.
        iFrame. iSplitL.
        { rewrite /waiters۰statuses big_sepM_empty //. }
        iPureIntro. split; last done.
        apply inv۰pureｰcreate.
      - iApply (big_sepM_impl with "Hrefs").
        iIntros "!> %r' %ρ' %Hlookup' Href".
        rewrite lookup_total_insert_ne //. congruence.
    }
    iSteps.
  Qed.

  #[local] Definition reader γ r ρ n g 𝑣 : iProp Σ :=
    ( ∃ snaps',
      snaps۰lb ρ snaps' ∗
      ⌜n < length snaps'⌝
    ) ∨ (
      generation۰lb γ (S g)
    ) ∨ (
      doom۰lb ρ
    ) ∨ (
      ∃ ipast iprophs,
      prophet۰snapshot γ ipast iprophs ∗
      ⌜S (length (prophecies۰forwards (untangle ipast r))) = n⌝ ∗
      ( ⌜head (prophecies۰forwards (untangle iprophs r)) = Some (𝑣, g)⌝ →
        ∃ idx,
        hist۰at ρ g 𝑣 idx
      )
    ).
  #[local] Zoo derive Persistent for reader.

  #[local] Lemma invｰinit γ ι r ρ E :
    ↑ι ⊆ E →
    inv' γ ι -∗
    ref۰elem γ r ρ ={E}=∗
      snaps۰lb ρ [] ∗
      ∃ vh idx,
      hist۰at ρ 0 vh idx.
  Proof.
    iIntros "%HE #Hinv #Hρ".
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb".
    destruct (hist2 !! 0) as [(vh & idx) |] eqn:Hhist_lookup; last first.
    { apply lookup_ge_None in Hhist_lookup.
      pose proof (inv۰pure۰hist_length _ _ _ _ _ _ _ _ _ _ _ _ Hinv2). lia.
    }
    iDestruct (hist۰atｰget with "Hhist_auth") as "#Hhist_at"; first done.
    iSplitR "".
    { iModIntro. iNext. iFrameSteps. }
    iModIntro. iSplitL.
    - iApply (mono_list۰lbｰmono with "Hsnaps_lb"). apply prefix_nil.
    - iSteps.
  Qed.

  #[local] Lemma genｰspec γ ι g0 E :
    ↑ι ⊆ E →
    {{{
      inv' γ ι ∗
      generation۰lb γ g0
    }}}
      γ.{gen} @ E
    {{{
      g
    , RET #g;
      ⌜g0 ≤ g⌝ ∗
      generation۰lb γ g
    }}}.
  Proof.
    iIntros "%HE %Φ (#Hinv & #Hg0) HΦ".
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg0") as %?.
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg".
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma snapshotｰspec γ ι r ρ g0 L h vh idx E :
    ↑ι ⊆ E →
    {{{
      inv' γ ι ∗
      ref۰elem γ r ρ ∗
      generation۰lb γ g0 ∗
      snaps۰lb ρ L ∗
      hist۰at ρ h vh idx
    }}}
      (#r).{ref_snapshot} @ E
    {{{
      snaps snap
    , RET snap۰to_val snap;
      snaps۰lb ρ snaps ∗
      ⌜L `prefix_of` snaps⌝ ∗
      ⌜last snaps = Some snap⌝ ∗
      ⌜snap.(snap۰gen) ≤ snap.(snap۰inst)⌝ ∗
      generation۰lb γ snap.(snap۰inst) ∗
      snapshot۰lb ρ snap.(snap۰gen) ∗
      ⌜idx < pred (length snaps) → h ≤ snap.(snap۰inst)⌝ ∗
      ∃ gc vh' idx',
      hist۰at ρ gc vh' idx' ∗
      ⌜g0 ≤ gc⌝ ∗
      ⌜idx' < length snaps⌝
    }}}.
  Proof.
    iIntros "%HE %Φ (#Hinv & #Hρ & #Hg0 & #HL & #Hhist_at) HΦ".
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    wp۰load.
    iDestruct (snaps۰lbｰvalid with "Hsnaps_auth HL") as %HL.
    iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb".
    iDestruct (hist۰atｰvalid with "Hhist_auth Hhist_at") as %Hhist_lookup.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg0") as %Hg0.
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg".
    iDestruct (snapshot۰lbｰget with "Hsnapshot_auth") as "#Hsnapshot_lb".
    pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv2) as Hlast.
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
      eapply (inv۰pure۰hist_snaps _ _ _ _ _ _ _ _ _ _ _ _ Hinv2); done.
    }
    iSteps.
  Qed.

  #[local] Lemma valueｰspec γ ι r ρ snaps snap g E :
    ↑ι ⊆ E →
    {{{
      inv' γ ι ∗
      ref۰elem γ r ρ ∗
      snaps۰lb ρ snaps ∗
      ⌜last snaps = Some snap⌝ ∗
      ⌜snap.(snap۰gen) < g⌝ ∗
      generation۰lb γ g
    }}}
      (#r).{ref_value} @ E
    {{{
      𝑣
    , RET 𝑣;
      reader γ r ρ (length snaps) g 𝑣
    }}}.
  Proof.
    iIntros "%HE %Φ (#Hinv & #Hρ & #Hsnaps_lb & %Hlast & %Hgen & #Hg) HΦ".
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    wp۰load.
    iDestruct (snaps۰lbｰvalid with "Hsnaps_auth Hsnaps_lb") as %Hsnaps.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg") as %Hg.
    iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb2".
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg1".
    iDestruct (prophet_wise۰snapshotｰget with "Hprophet_model") as "#Hprophet_snapshot".
    iAssert (if mode2 is Good then True else doom۰lb ρ)%I as "#Hdoom".
    { destruct mode2; first done. iApply (doom۰lbｰget with "Hdoom_auth"). done. }
    opose proof* inv۰pure۰hist_last as (idx & Hhist_last); first done.
    iDestruct (hist۰atｰget with "Hhist_auth") as "#Hhist_at"; first done.
    iAssert (reader γ r ρ (length snaps) g 𝑣2)%I as "#Hreader".
    { destruct (decide (length snaps < length snaps2)).
      { iLeft. iExists snaps2. iFrame "#". done. }
      apply prefix_length_eq in Hsnaps as <-; last lia.
      assert (snap2 = snap) as ->.
      { pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv2). congruence. }
      destruct (decide (g < g1)).
      { iRight. iLeft.
        iApply (auth_nat_max۰lbｰle with "Hg1"). lia.
      }
      assert (g1 = g) as -> by lia.
      destruct mode2 as [| b g_d]; last first.
      { iRight. iRight. iLeft. done. }
      iRight. iRight. iRight.
      iExists ipast1, iprophs1.
      iSplitR. { iApply "Hprophet_snapshot". }
      iSplitR. { iPureIntro. symmetry. apply (inv۰pure۰forwards _ _ _ _ _ _ _ _ _ _ _ _ Hinv2). }
      iIntros "%Hhead".
      opose proof* (inv۰pureｰreader Hinv2) as <-; [done.. |].
      iExists idx. done.
    }
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro. iApply "HΦ". done.
  Qed.

  #[local] Lemma waiters۰statusesｰforward γ ι r ρ waiters 𝑣' helped past 𝑣 g :
    waiters۰statuses γ ι r ρ waiters 𝑣' helped (past ++ [ProphecyForward 𝑣 g]) = waiters۰statuses γ ι r ρ waiters 𝑣' helped past.
  Proof.
    rewrite /waiters۰statuses prophecies۰opsｰapp /= right_id //.
  Qed.

  #[local] Lemma readerｰvalid γ r ρ snaps g hist vₛ idx mode ipast iprophs n g' 𝑣 :
    length snaps = S (length (prophecies۰forwards (untangle ipast r))) →
    hist !! g = Some (vₛ, idx) →
    snaps۰auth ρ snaps -∗
    generation۰auth γ g -∗
    doom۰auth ρ (mode۰doomed mode) -∗
    hist۰auth ρ hist -∗
    prophet۰model γ ipast iprophs -∗
    reader γ r ρ n g' 𝑣 -∗
    ⌜n = length snaps → head (prophecies۰forwards (untangle iprophs r)) = Some (𝑣, g') → g' = g → mode = Good → vₛ = 𝑣⌝.
  Proof.
    iIntros "%Hforwards %Hhist_lookup Hsnaps_auth Hgeneration_auth Hdoom_auth Hhist_auth Hprophet_model Hreader".
    iIntros "%Hn %Hhead %Hg %Hmode". subst g' n.
    iDestruct "Hreader" as "[(%snaps' & #Hsnaps_lb & %Hsnaps') | [#Hg | [#Hdoom | (%ipast' & %iprophs' & #Hprophet_snapshot & %Hforwards' & #Hhist)]]]".
    - iDestruct (snaps۰lbｰvalid with "Hsnaps_auth Hsnaps_lb") as %?%prefix_length. lia.
    - iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg") as %?. lia.
    - iDestruct (doom۰lbｰvalid with "Hdoom_auth Hdoom") as %?. done.
    - iDestruct (prophet_wise۰snapshotｰvalid with "Hprophet_model Hprophet_snapshot") as %(ipast3 & -> & ->).
      rewrite untangleｰapp prophecies۰forwardsｰapp length_app in Hforwards.
      assert (prophecies۰forwards (untangle ipast3 r) = []) as Hipast3.
      { apply nil_length_inv. lia. }
      iDestruct ("Hhist" with "[]") as "(%idx' & Hhist_at)".
      { rewrite untangleｰapp prophecies۰forwardsｰapp Hipast3 //. }
      iDestruct (hist۰atｰvalid with "Hhist_auth Hhist_at") as %?.
      naive.
  Qed.

  #[local] Lemma casｰspec γ ι r ρ snaps snap g 𝑣 E :
    ↑ι ⊆ E →
    {{{
      sstore۰inv γ ι ∗
      ref۰elem γ r ρ ∗
      snaps۰lb ρ snaps ∗
      ⌜last snaps = Some snap⌝ ∗
      ⌜snap.(snap۰gen) < g⌝ ∗
      ⌜snap.(snap۰inst) ≤ g⌝ ∗
      generation۰lb γ g ∗
      reader γ r ρ (length snaps) g 𝑣
    }}}
      𝗿𝗲𝘀𝗼𝗹𝘃𝗲
        (𝗰𝗮𝘀 (#r).[ref_snapshot] (snap۰to_val snap) ‘Snapshot@[ 𝑣, #g ])
        γ.{proph}
        (‘Forward( #r, 𝑣, #g ))%V
      @ E
    {{{
      b
    , RET #b;
      if b then
        snapshot۰lb ρ g
      else
        ∃ snaps',
        snaps۰lb ρ snaps' ∗
        ⌜snaps `prefix_of` snaps'⌝ ∗
        ⌜length snaps < length snaps'⌝ ∗
        snapshot۰lb ρ snap.(snap۰inst)
    }}}.
  Proof.
    iIntros "%HE %Φ ((:inv) & #Hρ & #Hsnaps_lb & %Hlast & %Hgen & %Hinst & #Hg & #Hreader) HΦ".
    wp۰load. wp۰block۰generative bid. wp۰pures.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    iDestruct (snaps۰lbｰvalid with "Hsnaps_auth Hsnaps_lb") as %Hsnaps.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg") as %Hg.
    pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv2) as Hlast2.
    opose proof* inv۰pure۰hist_last as (idx & Hhist_last); first done.
    iDestruct (readerｰvalid with "Hsnaps_auth Hgeneration_auth Hdoom_auth Hhist_auth Hprophet_model Hreader") as %Hvₛ.
    { apply (inv۰pure۰forwards _ _ _ _ _ _ _ _ _ _ _ _ Hinv2). }
    { done. }
    pose proof Hlast as Hlast'%snapsｰlookup_last.
    pose proof Hlast' as Hlast''. eapply prefix_lookup_Some in Hlast''; last done.
    pose proof Hlast2 as Hlast2'%snapsｰlookup_last.
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰cas as Hcas | Hcas.
    - iExists None. iSplitR; first done. iIntros "!> Hprophet_model".
      assert (length snaps < length snaps2) as Hlen.
      { pose proof Hsnaps as Hlen%prefix_length.
        destruct (decide (length snaps = length snaps2)) as [Heq |]; last lia.
        apply prefix_length_eq in Hsnaps as <-; last lia.
        exfalso.
        assert (snap2 = snap) as -> by congruence.
        apply (snap۰to_valｰnonsimilar snap). done.
      }
      destruct (snaps2 !! length snaps) as [snap' |] eqn:Hlookup'; last first.
      { apply lookup_ge_None in Hlookup'. lia. }
      opose proof* (inv۰pure۰snaps_sorted _ _ _ _ _ _ _ _ _ _ _ _ Hinv2 (pred (length snaps)) snap snap') as (_ & Hsorted).
      { done. }
      { replace (S (pred (length snaps))) with (length snaps); first done.
        apply lookup_lt_Some in Hlast'. lia.
      }
      opose proof* (inv۰pureｰsnaps_le_last (length snaps) snap' Hinv2); first done.
      iDestruct (snapshot۰lbｰget with "Hsnapshot_auth") as "#Hsnapshot_lb".
      iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb2".
      iSplitR "HΦ". { iFrameSteps. }
      iModIntro. iApply "HΦ".
      iExists snaps2. iFrame "#". iSplitR; first done. iSplitR; first done.
      iApply (auth_nat_max۰lbｰle with "Hsnapshot_lb"). lia.
    - iExists (Some (r, ProphecyForward 𝑣 g)). iSplitR.
      { iPureIntro. rewrite /= Nat2Z.id //. }
      iIntros "!> %iprophs' -> Hprophet_model".
      rewrite untangleｰconsｰTrue in Hinv2 Hvₛ.
      apply snap۰to_valｰsimilar in Hcas.
      assert (snaps2 = snaps) as ->.
      { opose proof* (inv۰pureｰsnaps_gen_inj _ _ _ _ Hinv2 Hlast2' Hlast''); first done.
        apply lookup_lt_Some in Hlast'.
        symmetry. apply prefix_length_eq; first done. lia.
      }
      assert (snap2 = snap) as -> by congruence.
      iMod (snapsｰupdate (Snap bid 𝑣 g g1) with "Hsnaps_auth") as "Hsnaps_auth".
      iMod (snapshotｰupdate g with "Hsnapshot_auth") as "Hsnapshot_auth"; first lia.
      iDestruct (snapshot۰lbｰget with "Hsnapshot_auth") as "#Hsnapshot_lb".
      assert (∀ iproph, iproph ∈ ipast1 ++ [(r, ProphecyForward 𝑣 g)] → iproph.1 ∈ dom refs1) as Hipast1'.
      { intros iproph [Hiproph | ->%list_elem_of_singleton]%elem_of_app; first auto.
        apply elem_of_dom. naive.
      }
      iDestruct ("Hrefs" $! vs1 (ipast1 ++ [(r, ProphecyForward 𝑣 g)]) iprophs' with "[%] [%] [%] [Hr_value Hr_snapshot Hsnapshot_auth Hsnaps_auth Hhist_auth Hdoom_auth Hwaiters_auth Hwaiters]") as "Hrefs".
      { done. }
      { intros r' Hr'. apply untangleｰsnocｰFalse. congruence. }
      { intros r' Hr'. symmetry. apply untangleｰconsｰFalse. congruence. }
      { iExists 𝑣2, vₛ2, (snaps ++ [Snap bid 𝑣 g g1]), (Snap bid 𝑣 g g1), hist2, waiters2, helped2, mode2.
        rewrite untangleｰsnocｰTrue waiters۰statusesｰforward.
        iFrame. iPureIntro. split; last done.
        apply (inv۰pureｰforward 𝑣 g bid Hinv2); [lia | lia | lia |].
        intros. eapply Hvₛ; done.
      }
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.

  #[local] Lemma sstore٠forwardｰspec γ ι r ρ g0 E :
    ↑ι ⊆ E →
    {{{
      sstore۰inv γ ι ∗
      ref۰elem γ r ρ ∗
      generation۰lb γ g0
    }}}
      sstore٠forward γ #r @ E
    {{{
      RET ();
      snapshot۰lb ρ g0
    }}}.
  Proof.
    iIntros "%HE %Φ ((:inv) & #Hρ & #Hg0) HΦ".
    wp۰rec. wp۰pures.
    iMod (invｰinit with "Hinv Hρ") as "(#Hsnaps_lb0 & %vh0 & %idx0 & #Hhist_at0)"; first done.
    wp۰apply (snapshotｰspec with "[$Hinv $Hρ $Hg0 $Hsnaps_lb0 $Hhist_at0]") as (snaps1 snap1) "(#Hsnaps_lb1 & _ & %Hlast1 & %Hinst1 & #Hinst1_lb & #Hsnapshot_lb1 & _ & %gc1 & %vh1 & %idx1 & #Hhist_at1 & %Hgc1 & %Hidx1)"; first done.
    wp۰pures.
    iDestruct (auth_nat_max۰lbｰmax with "Hg0 Hinst1_lb") as "#Hlb1".
    wp۰apply (genｰspec with "[$Hinv $Hlb1]") as (g1) "(%Hg1 & #Hg1_lb)"; first done.
    wp۰pures.
    case_bool_decide as Hsnap1; wp۰pures.
    { iApply "HΦ". iApply (auth_nat_max۰lbｰle with "Hsnapshot_lb1"). lia. }
    wp۰apply (valueｰspec _ _ r ρ snaps1 snap1 g1 with "[]") as (𝑣1) "#Hreader1"; first done.
    { iFrame "#". iPureIntro. split; [done | lia]. }
    wp۰apply+ (casｰspec _ _ r ρ snaps1 snap1 g1 𝑣1 with "[]") as ([]) "H"; first done.
    { iFrame "#". iPureIntro. split_and!; [done | lia | lia]. }
    { wp۰pures. iApply "HΦ". iApply (auth_nat_max۰lbｰle with "H"). lia. }
    iDestruct "H" as "(%snaps1' & #Hsnaps_lb1' & %Hpre1 & %Hlen1 & _)".
    wp۰apply+ (snapshotｰspec with "[$Hinv $Hρ $Hg0 $Hsnaps_lb1' $Hhist_at1]") as (snaps2 snap2) "(#Hsnaps_lb2 & %Hpre2 & %Hlast2 & %Hinst2 & #Hinst2_lb & #Hsnapshot_lb2 & %Hhist2 & _)"; first done.
    assert (gc1 ≤ snap2.(snap۰inst)) as Hgc2.
    { apply Hhist2. apply prefix_length in Hpre2. lia. }
    iDestruct (auth_nat_max۰lbｰmax with "Hg0 Hinst2_lb") as "#Hlb2".
    wp۰apply+ (genｰspec with "[$Hinv $Hlb2]") as (g2) "(%Hg2 & #Hg2_lb)"; first done.
    wp۰pures.
    case_bool_decide as Hsnap2; wp۰pures.
    { iApply "HΦ". iApply (auth_nat_max۰lbｰle with "Hsnapshot_lb2"). lia. }
    wp۰apply (valueｰspec _ _ r ρ snaps2 snap2 g2 with "[]") as (𝑣2) "#Hreader2"; first done.
    { iFrame "#". iPureIntro. split; [done | lia]. }
    wp۰apply+ (casｰspec _ _ r ρ snaps2 snap2 g2 𝑣2 with "[]") as ([]) "H"; first done.
    { iFrame "#". iPureIntro. split_and!; [done | lia | lia]. }
    - wp۰pures. iApply "HΦ". iApply (auth_nat_max۰lbｰle with "H"). lia.
    - iDestruct "H" as "(%snaps2' & _ & _ & _ & #Hinst_lb)".
      wp۰pures. iApply "HΦ". iApply (auth_nat_max۰lbｰle with "Hinst_lb"). lia.
  Qed.

  #[local] Lemma waiters۰statusesｰinsert γ ι r ρ waiters 𝑣 helped past id waiter Ψ :
    id ∉ operations۰ids (prophecies۰ops past) →
    id ∉ operations۰ids helped →
    waiters !! id = None →
    waiters۰statuses γ ι r ρ waiters 𝑣 helped past -∗
    saved_pred waiter.(waiter۰post) Ψ -∗
    waiter۰au γ ι r waiter Ψ -∗
    waiters۰statuses γ ι r ρ (<[id := waiter]> waiters) 𝑣 helped past.
  Proof.
    iIntros "%Hpast %Hhelped %Hlookup Hwaiters #Hpost Hau".
    iApply (big_sepM_insert with "[- $Hwaiters]"); first done.
    rewrite !bool_decide_eq_false_2 //.
    iSteps.
  Qed.

  #[local] Lemma waiters۰statusesｰwrite γ ι r ρ waiters 𝑣 𝑣' helped helped' past id (w : opkind) waiter :
    waiters !! id = Some waiter →
    id ∉ operations۰ids (prophecies۰ops past) →
    (∀ id', id' ≠ id → (id' ∈ operations۰ids helped' ↔ id' ∈ operations۰ids helped)) →
    (∀ id', id' ≠ id → id' ∈ operations۰ids helped → helped۰result 𝑣' helped' id' = helped۰result 𝑣 helped id') →
    waiters۰statuses γ ι r ρ waiters 𝑣 helped past -∗
    waiters۰elem ρ id waiter -∗
      waiters۰statuses γ ι r ρ waiters 𝑣' helped' (past ++ [ProphecyOp id w]) ∗
      ∃ Ψ,
      saved_pred waiter.(waiter۰post) Ψ ∗
      if bool_decide (id ∈ operations۰ids helped) then
        Ψ (helped۰result 𝑣 helped id)
      else
        waiter۰au γ ι r waiter Ψ.
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

  #[local] Lemma waiters۰statusesｰhelp γ ι r ρ waiters 𝑣 past helped help vs v :
    vs !! r = Some v →
    v = ops۰apply helped 𝑣 →
    helpable waiters past helped help →
    waiters۰statuses γ ι r ρ waiters 𝑣 helped past -∗
    model₂ γ vs ={⊤ ∖ ↑ι}=∗
      waiters۰statuses γ ι r ρ waiters 𝑣 (helped ++ help) past ∗
      model₂ γ (<[r := ops۰apply help v]> vs).
  Proof.
    iInduction help as [| op help] "IH" forall (helped vs v).
    - iIntros "%Hvs _ _ Hwaiters Hmodel₂". rewrite right_id insert_id //. iFrame. done.
    - iIntros "%Hvs %Hv %Hhelpable Hwaiters Hmodel₂".
      destruct Hhelpable as ((waiter & Hlookup & Hval) & Hdone & Hhelped & Hhelpable).
      iDestruct (big_sepM_delete with "Hwaiters") as "(Hwaiter & Hwaiters)"; first done.
      rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2 //.
      iDestruct "Hwaiter" as "(%Ψ & #Hpost & Hau)".
      rewrite /waiter۰au /waiter۰au' Hval.
      iMod "Hau" as "(%vs' & (Hmodel₁ & Hdom_auth) & _ & HΨ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate (<[r := opkind۰apply op.(operation۰kind) v]> vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΨ" $! v (opkind۰outcome op.(operation۰kind) v) with "[Hmodel₁ Hdom_auth]") as "HΨ".
      { iSplitR; first done.
        iSplitR; first (iPureIntro; apply opkind۰outcomeｰrel).
        iSplitL "Hmodel₁"; first iExact "Hmodel₁".
        rewrite /dom۰auth dom_insert_lookup_L; first naive.
        iFrame.
      }
      iAssert (waiters۰statuses γ ι r ρ waiters 𝑣 (helped ++ [op]) past) with "[HΨ Hwaiters]" as "Hwaiters".
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
      iMod ("IH" with "[] [] [//] Hwaiters Hmodel₂") as "(Hwaiters & Hmodel₂)".
      { rewrite lookup_insert_eq //. }
      { rewrite ops۰applyｰapp -Hv //. }
      rewrite insert_insert_eq -assoc /=.
      by iFrame.
  Qed.

  #[local] Lemma waiterｰregister γ ι r ρ id req Ψ E :
    ↑ι ⊆ E →
    inv' γ ι -∗
    ref۰elem γ r ρ -∗
    identifier۰model id -∗
    waiter۰au' γ ι r req Ψ ={E}=∗
      ∃ waiter,
      ⌜waiter.(waiter۰request) = req⌝ ∗
      waiters۰elem ρ id waiter ∗
      saved_pred waiter.(waiter۰post) Ψ ∗
      generation۰lb γ waiter.(waiter۰gen).
  Proof.
    iIntros "%HE #Hinv #Hρ Hid Hau".
    iMod (saved_predｰalloc Ψ) as "(%γ_post & #Hpost)".
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    pose waiter :=
      {|waiter۰request := req
      ; waiter۰post := γ_post
      ; waiter۰gen := g1
      |}.
    iMod (waitersｰinsert id waiter with "Hwaiters_auth Hid") as "(%Hlookup & Hwaiters_auth & Helem)".
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hgen".
    destruct (inv۰pureｰfresh id Hinv2) as (Hpast & Hhelped); first done.
    iSplitR "Helem".
    { iModIntro. iNext.
      iDestruct ("Hrefs" $! vs1 ipast1 iprophs1 with "[//] [//] [//] [-Ht_gen Hmodel₂ Hscanner₂ Hgeneration_auth Hrefs_auth Hprophet_model]") as "Hrefs".
      { iExists 𝑣2, vₛ2, snaps2, snap2, hist2, (<[id := waiter]> waiters2), helped2, mode2.
        iFrame.
        iSplitL.
        - iApply (waiters۰statusesｰinsert _ _ _ _ _ _ _ _ id waiter Ψ Hpast Hhelped Hlookup with "Hwaiters Hpost Hau").
        - iPureIntro. split; last done. apply inv۰pureｰregister; done.
      }
      iFrameSteps.
    }
    iModIntro. iExists waiter. iFrame "#∗". done.
  Qed.

  (* The common linearization step of [get] and [set]: consuming the prophesied operation [id] on [r]. *)
  #[local] Lemma waiterｰconsume γ ι r ρ 𝑣 g vs v vₛ snaps snap hist waiters helped past prophs mode id (w : opkind) waiter Ψ :
    vs !! r = Some v →
    inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past (ProphecyOp id w :: prophs) mode →
    waiter.(waiter۰request) = opkind۰request w →
    waiter.(waiter۰gen) ≤ snap.(snap۰gen) →
    waiters۰auth ρ waiters -∗
    waiters۰elem ρ id waiter -∗
    saved_pred waiter.(waiter۰post) Ψ -∗
    waiters۰statuses γ ι r ρ waiters 𝑣 helped past -∗
    model₂ γ vs ={⊤ ∖ ↑ι}=∗
      waiters۰auth ρ waiters ∗
      waiters۰statuses γ ι r ρ waiters (opkind۰apply w 𝑣) (tail helped) (past ++ [ProphecyOp id w]) ∗
      model₂ γ (<[r := if helped is [] then opkind۰apply w v else v]> vs) ∗
      ⌜inv۰pure (opkind۰apply w 𝑣) g (if helped is [] then opkind۰apply w v else v) vₛ snaps snap hist waiters (tail helped) (past ++ [ProphecyOp id w]) prophs mode⌝ ∗
      ▷ Ψ (opkind۰result w 𝑣).
  Proof.
    iIntros "%Hvs %Hinv %Hval %Hgen Hwaiters_auth Helem #Hpost Hwaiters Hmodel₂".
    iDestruct (waiters۰elemｰvalid with "Hwaiters_auth Helem") as %Hlookup.
    destruct (decide (id ∈ operations۰ids (prophecies۰ops past))) as [Hdone | Hdone].
    { iDestruct (big_sepM_lookup with "Hwaiters") as "Hwaiter"; first done.
      rewrite bool_decide_eq_true_2 //.
      iDestruct (waiters۰elemｰexclusive with "Helem Hwaiter") as %[].
    }
    destruct (inv۰pureｰwrite id w waiter Hinv Hlookup Hval Hdone Hgen) as (Hhelped & Hinv').
    iDestruct (waiters۰statusesｰwrite _ _ _ _ _ 𝑣 (opkind۰apply w 𝑣) helped (tail helped) _ _ w with "Hwaiters Helem") as "(Hwaiters & %Ψ' & #Hpost' & HΨ)".
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
    iAssert (|={⊤ ∖ ↑ι}=> Ψ' (opkind۰result w 𝑣) ∗ model₂ γ (<[r := if helped is [] then opkind۰apply w v else v]> vs))%I with "[HΨ Hmodel₂]" as ">(HΨ & $)".
    { destruct Hhelped as [-> | Hhead].
      - assert (bool_decide (id ∈ operations۰ids []) = false) as -> by (apply bool_decide_eq_false_2, not_elem_of_nil).
        assert (v = 𝑣) as -> by rewrite (inv۰pure۰model _ _ _ _ _ _ _ _ _ _ _ _ Hinv) //.
        rewrite /waiter۰au /waiter۰au' Hval.
        iMod "HΨ" as "(%vs' & (Hmodel₁ & Hdom_auth) & _ & HΨ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod (modelｰupdate (<[r := opkind۰apply w 𝑣]> vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & $)".
        iMod ("HΨ" $! 𝑣 (opkind۰outcome w 𝑣) with "[Hmodel₁ Hdom_auth]") as "$"; last done.
        iSplitR; first done.
        iSplitR; first (iPureIntro; apply opkind۰outcomeｰrel).
        iSplitL "Hmodel₁"; first iExact "Hmodel₁".
        rewrite /dom۰auth dom_insert_lookup_L; first naive.
        iFrame.
      - destruct helped as [| op helped]; first done.
        injection Hhead as ->.
        rewrite bool_decide_eq_true_2.
        { rewrite /operations۰ids /=. set_solver. }
        rewrite /= decide_True // insert_id //.
        iFrame. done.
    }
    iDestruct (saved_predｰagree (opkind۰result w 𝑣) with "Hpost Hpost'") as "Heq".
    iModIntro. iSplitR; first done.
    iNext. iRewrite "Heq". done.
  Qed.

  Lemma sstore٠getｰspec γ ι r :
    <<<
      sstore۰inv γ ι ∗
      sstore۰ref γ r
    | ∀∀ vs,
      sstore۰model γ vs
    >>>
      sstore٠get γ #r
      @ ↑ι
    <<<
      ∃∃ v,
      ⌜vs !! r = Some v⌝ ∗
      sstore۰model γ vs
    | RET v;
      True
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:ref)) HΦ".
    wp۰rec credit:"H£". wp۰pures.
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
    iMod (waiterｰregister _ _ r ρ id RequestGet (λ v, True -∗ Φ v)%I with "Hinv Hρ Hid [HΦ]") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)"; first done.
    { rewrite /waiter۰au'. iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros "%v %b (%Hlookup & _ & Hmodel) !>".
      rewrite insert_id //. iSteps.
    }
    wp۰apply+ (sstore٠forwardｰspec with "[$Ht_proph $Hinv $Hρ $Hgen]") as "#Hsnapshot_lb"; first done.
    wp۰load. wp۰pures.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰load.
    iExists (Some (r, ProphecyOp id OpGet)). iSplitR; first done.
    iIntros "!> %iprophs' -> Hprophet_model".
    rewrite untangleｰconsｰTrue in Hinv2.
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    assert (r ∈ dom vs1) as Hr by (rewrite Hvs1; apply elem_of_dom; eauto).
    assert (vs1 !! r = Some (vs1 !!! r)) as Hvs_r.
    { apply elem_of_dom in Hr as (? & ?). by apply lookup_lookup_total. }
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    assert (∀ iproph, iproph ∈ ipast1 ++ [(r, ProphecyOp id OpGet)] → iproph.1 ∈ dom refs1) as Hipast1'.
    { intros iproph [Hiproph | ->%list_elem_of_singleton]%elem_of_app; first auto.
      apply elem_of_dom. naive.
    }
    iDestruct ("Hrefs" $! (<[r := if helped2 is [] then opkind۰apply OpGet (vs1 !!! r) else vs1 !!! r]> vs1) (ipast1 ++ [(r, ProphecyOp id OpGet)]) iprophs' with "[%] [%] [%] [Hr_value Hr_snapshot Hsnapshot_auth Hsnaps_auth Hhist_auth Hdoom_auth Hwaiters_auth Hwaiters]") as "Hrefs".
    { intros r' Hr'. rewrite lookup_total_insert_ne //. }
    { intros r' Hr'. apply untangleｰsnocｰFalse. congruence. }
    { intros r' Hr'. symmetry. apply untangleｰconsｰFalse. congruence. }
    { iExists 𝑣2, vₛ2, snaps2, snap2, hist2, waiters2, (tail helped2), mode2.
      rewrite lookup_total_insert_eq untangleｰsnocｰTrue.
      iFrame. done.
    }
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps.
      iPureIntro. rewrite dom_insert_L. set_solver.
    }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  Lemma sstore٠setｰspec γ ι r v :
    <<<
      sstore۰inv γ ι ∗
      sstore۰ref γ r
    | ∀∀ vs,
      sstore۰model γ vs
    >>>
      sstore٠set γ #r v
      @ ↑ι
    <<<
      ⌜r ∈ dom vs⌝ ∗
      sstore۰model γ (<[r := v]> vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:ref)) HΦ".
    wp۰rec credit:"H£". wp۰pures.
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
    iMod (waiterｰregister _ _ r ρ id (RequestSet v) (λ _, True -∗ Φ ()%V)%I with "Hinv Hρ Hid [HΦ]") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)"; first done.
    { rewrite /waiter۰au'. iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros "%w %b (%Hlookup & _ & Hmodel) !>".
      iSteps. iPureIntro. apply elem_of_dom. naive.
    }
    wp۰apply+ (sstore٠forwardｰspec with "[$Ht_proph $Hinv $Hρ $Hgen]") as "#Hsnapshot_lb"; first done.
    wp۰load. wp۰pures.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰store.
    iExists (Some (r, ProphecyOp id (OpSet v))). iSplitR; first done.
    iIntros "!> %iprophs' -> Hprophet_model".
    rewrite untangleｰconsｰTrue in Hinv2.
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    assert (r ∈ dom vs1) as Hr by (rewrite Hvs1; apply elem_of_dom; eauto).
    assert (vs1 !! r = Some (vs1 !!! r)) as Hvs_r.
    { apply elem_of_dom in Hr as (? & ?). by apply lookup_lookup_total. }
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    assert (∀ iproph, iproph ∈ ipast1 ++ [(r, ProphecyOp id (OpSet v))] → iproph.1 ∈ dom refs1) as Hipast1'.
    { intros iproph [Hiproph | ->%list_elem_of_singleton]%elem_of_app; first auto.
      apply elem_of_dom. naive.
    }
    iDestruct ("Hrefs" $! (<[r := if helped2 is [] then opkind۰apply (OpSet v) (vs1 !!! r) else vs1 !!! r]> vs1) (ipast1 ++ [(r, ProphecyOp id (OpSet v))]) iprophs' with "[%] [%] [%] [Hr_value Hr_snapshot Hsnapshot_auth Hsnaps_auth Hhist_auth Hdoom_auth Hwaiters_auth Hwaiters]") as "Hrefs".
    { intros r' Hr'. rewrite lookup_total_insert_ne //. }
    { intros r' Hr'. apply untangleｰsnocｰFalse. congruence. }
    { intros r' Hr'. symmetry. apply untangleｰconsｰFalse. congruence. }
    { iExists v, vₛ2, snaps2, snap2, hist2, waiters2, (tail helped2), mode2.
      rewrite lookup_total_insert_eq untangleｰsnocｰTrue.
      iFrame. done.
    }
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps.
      iPureIntro. rewrite dom_insert_L. set_solver.
    }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  Lemma sstore٠xchgｰspec γ ι r v :
    <<<
      sstore۰inv γ ι ∗
      sstore۰ref γ r
    | ∀∀ vs,
      sstore۰model γ vs
    >>>
      sstore٠xchg γ #r v
      @ ↑ι
    <<<
      ∃∃ w,
      ⌜vs !! r = Some w⌝ ∗
      sstore۰model γ (<[r := v]> vs)
    | RET w;
      True
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:ref)) HΦ".
    wp۰rec credit:"H£". wp۰pures.
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
    iMod (waiterｰregister _ _ r ρ id (RequestSet v) (λ w, True -∗ Φ w)%I with "Hinv Hρ Hid [HΦ]") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)"; first done.
    { rewrite /waiter۰au'. iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros "%w %b (%Hlookup & _ & Hmodel) !>".
      iSteps.
    }
    wp۰apply+ (sstore٠forwardｰspec with "[$Ht_proph $Hinv $Hρ $Hgen]") as "#Hsnapshot_lb"; first done.
    wp۰load. wp۰pures.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰xchg.
    iExists (Some (r, ProphecyOp id (OpSet v))). iSplitR; first done.
    iIntros "!> %iprophs' -> Hprophet_model".
    rewrite untangleｰconsｰTrue in Hinv2.
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    assert (r ∈ dom vs1) as Hr by (rewrite Hvs1; apply elem_of_dom; eauto).
    assert (vs1 !! r = Some (vs1 !!! r)) as Hvs_r.
    { apply elem_of_dom in Hr as (? & ?). by apply lookup_lookup_total. }
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    assert (∀ iproph, iproph ∈ ipast1 ++ [(r, ProphecyOp id (OpSet v))] → iproph.1 ∈ dom refs1) as Hipast1'.
    { intros iproph [Hiproph | ->%list_elem_of_singleton]%elem_of_app; first auto.
      apply elem_of_dom. naive.
    }
    iDestruct ("Hrefs" $! (<[r := if helped2 is [] then opkind۰apply (OpSet v) (vs1 !!! r) else vs1 !!! r]> vs1) (ipast1 ++ [(r, ProphecyOp id (OpSet v))]) iprophs' with "[%] [%] [%] [Hr_value Hr_snapshot Hsnapshot_auth Hsnaps_auth Hhist_auth Hdoom_auth Hwaiters_auth Hwaiters]") as "Hrefs".
    { intros r' Hr'. rewrite lookup_total_insert_ne //. }
    { intros r' Hr'. apply untangleｰsnocｰFalse. congruence. }
    { intros r' Hr'. symmetry. apply untangleｰconsｰFalse. congruence. }
    { iExists v, vₛ2, snaps2, snap2, hist2, waiters2, (tail helped2), mode2.
      rewrite lookup_total_insert_eq untangleｰsnocｰTrue.
      iFrame. done.
    }
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps.
      iPureIntro. rewrite dom_insert_L. set_solver.
    }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  Lemma sstore٠casｰspec γ ι r v1 v2 :
    <<<
      sstore۰inv γ ι ∗
      sstore۰ref γ r
    | ∀∀ vs,
      sstore۰model γ vs
    >>>
      sstore٠cas γ #r v1 v2
      @ ↑ι
    <<<
      ∃∃ b v,
      ⌜vs !! r = Some v⌝ ∗
      ⌜(if b then (≈) else (≉)) v v1⌝ ∗
      sstore۰model γ (if b then <[r := v2]> vs else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:ref)) HΦ".
    wp۰rec credit:"H£". wp۰pures.
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
    iMod (waiterｰregister _ _ r ρ id (RequestCas v1 v2) (λ w, True -∗ Φ w)%I with "Hinv Hρ Hid [HΦ]") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)"; first done.
    { rewrite /waiter۰au'. iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros "%v %b (%Hlookup & %Hrel & Hmodel) !>".
      simpl in Hrel. destruct b.
      - iSteps. iExists true. iSteps.
      - rewrite insert_id //. iSteps. iExists false. iSteps.
    }
    wp۰apply+ (sstore٠forwardｰspec with "[$Ht_proph $Hinv $Hρ $Hgen]") as "#Hsnapshot_lb"; first done.
    wp۰load. wp۰pures.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    iApply (wpｰcasｰnobranch' with "Hr_value"). iIntros "!> %b %Hcas Hr_value".
    iExists (Some (r, ProphecyOp id (OpCas v1 v2 b))). iSplitR; first done.
    iIntros "%iprophs' -> Hprophet_model".
    rewrite untangleｰconsｰTrue in Hinv2.
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    assert (r ∈ dom vs1) as Hr by (rewrite Hvs1; apply elem_of_dom; eauto).
    assert (vs1 !! r = Some (vs1 !!! r)) as Hvs_r.
    { apply elem_of_dom in Hr as (? & ?). by apply lookup_lookup_total. }
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    destruct (opkind۰applyｰcas 𝑣2 v1 v2 b Hcas) as (Happly & Hresult).
    rewrite Happly Hresult in Hinv' |- *.
    assert (∀ iproph, iproph ∈ ipast1 ++ [(r, ProphecyOp id (OpCas v1 v2 b))] → iproph.1 ∈ dom refs1) as Hipast1'.
    { intros iproph [Hiproph | ->%list_elem_of_singleton]%elem_of_app; first auto.
      apply elem_of_dom. naive.
    }
    iDestruct ("Hrefs" $! (<[r := if helped2 is [] then opkind۰apply (OpCas v1 v2 b) (vs1 !!! r) else vs1 !!! r]> vs1) (ipast1 ++ [(r, ProphecyOp id (OpCas v1 v2 b))]) iprophs' with "[%] [%] [%] [Hr_value Hr_snapshot Hsnapshot_auth Hsnaps_auth Hhist_auth Hdoom_auth Hwaiters_auth Hwaiters]") as "Hrefs".
    { intros r' Hr'. rewrite lookup_total_insert_ne //. }
    { intros r' Hr'. apply untangleｰsnocｰFalse. congruence. }
    { intros r' Hr'. symmetry. apply untangleｰconsｰFalse. congruence. }
    { iExists (if b then v2 else 𝑣2), vₛ2, snaps2, snap2, hist2, waiters2, (tail helped2), mode2.
      rewrite lookup_total_insert_eq untangleｰsnocｰTrue.
      iFrame. done.
    }
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps.
      iPureIntro. rewrite dom_insert_L. set_solver.
    }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  #[local] Lemma ref۰invｰclick γ ι r ρ g vs wₛ past prophs :
    r ∈ dom vs →
    ref۰inv γ ι r ρ g (vs !!! r) wₛ past prophs -∗
    model₂ γ vs ={⊤ ∖ ↑ι}=∗
      ∃ v',
      model₂ γ (<[r := v']> vs) ∗
      ref۰inv γ ι r ρ (S g) v' (Some v') past prophs.
  Proof.
    iIntros "%Hr Href Hmodel₂".
    iDestruct "Href" as (𝑣1 vₛ1 snaps1 snap1 hist1 waiters1 helped1 mode1) "(Hr_value & Hr_snapshot & Hsnapshot_auth & Hsnaps_auth & Hhist_auth & Hdoom_auth & Hwaiters_auth & Hwaiters & %Hinv1 & %Hwₛ1)".
    destruct (inv۰pureｰclick Hinv1) as (help & mode' & Hhelpable & Hmode' & Hinv').
    iMod (waiters۰statusesｰhelp with "Hwaiters Hmodel₂") as "(Hwaiters & Hmodel₂)".
    { apply elem_of_dom in Hr as (? & ?). by apply lookup_lookup_total. }
    { apply (inv۰pure۰model _ _ _ _ _ _ _ _ _ _ _ _ Hinv1). }
    { done. }
    set v' := ops۰apply help (vs !!! r).
    iMod (histｰupdate v' (pred (length snaps1)) with "Hhist_auth") as "Hhist_auth".
    iMod (doomｰupdate mode' with "Hdoom_auth") as "Hdoom_auth"; first done.
    iModIntro. iExists v'. iFrame.
    iExists v'. iPureIntro. split; first done.
    intros w [= ->]. done.
  Qed.

  #[local] Lemma refs۰invｰclick γ ι refs g ws ipast iprophs vs :
    dom refs ⊆ dom vs →
    ( [∗ map] r ↦ ρ ∈ refs,
        ref۰inv γ ι r ρ g (vs !!! r) (ws !! r) (untangle ipast r) (untangle iprophs r)
    ) -∗
    model₂ γ vs ={⊤ ∖ ↑ι}=∗
      ∃ vs',
      ⌜dom vs' = dom vs⌝ ∗
      ⌜∀ r, r ∉ dom refs → vs' !! r = vs !! r⌝ ∗
      model₂ γ vs' ∗
      [∗ map] r ↦ ρ ∈ refs,
        ref۰inv γ ι r ρ (S g) (vs' !!! r) (vs' !! r) (untangle ipast r) (untangle iprophs r).
  Proof.
    iInduction refs as [| r ρ refs Hr IH] "IH" using map_ind forall (vs).
    - iIntros "_ _ Hmodel₂".
      iExists vs. iFrame. rewrite big_sepM_empty. done.
    - iIntros "%Hdom Hrefs Hmodel₂".
      rewrite big_sepM_insert //.
      iDestruct "Hrefs" as "(Href & Hrefs)".
      iMod ("IH" $! vs with "[] Hrefs Hmodel₂") as "(%vs1 & %Hdom1 & %Hvs1 & Hmodel₂ & Hrefs)".
      { iPureIntro. rewrite dom_insert_L in Hdom. set_solver. }
      assert (r ∉ dom refs) as Hr' by (apply not_elem_of_dom; done).
      assert (vs1 !!! r = vs !!! r) as Hr1.
      { rewrite !lookup_total_alt Hvs1 //. }
      assert (r ∈ dom vs1) as Hr1'.
      { rewrite Hdom1. rewrite dom_insert_L in Hdom. set_solver. }
      iMod (ref۰invｰclick with "[Href] Hmodel₂") as "(%v' & Hmodel₂ & Href)"; first done.
      { rewrite Hr1. done. }
      iExists (<[r := v']> vs1). iFrame.
      iSplitR.
      { iPureIntro. rewrite dom_insert_L. set_solver. }
      iSplitR.
      { iPureIntro. intros r'. rewrite dom_insert_L => Hr''.
        rewrite lookup_insert_ne; first set_solver.
        apply Hvs1. set_solver.
      }
      iModIntro.
      iApply big_sepM_insert; first done.
      rewrite lookup_total_insert_eq lookup_insert_eq. iFrame.
      iApply (big_sepM_impl with "Hrefs").
      iIntros "!> %r' %ρ' %Hlookup' Href".
      assert (r ≠ r') as Hne by congruence.
      rewrite lookup_total_insert_ne // lookup_insert_ne //.
  Qed.

  Lemma sstore٠clickｰspec γ ι ws :
    <<<
      sstore۰inv γ ι ∗
      sstore۰scanner γ Own ws
    | ∀∀ vs,
      sstore۰model γ vs
    >>>
      sstore٠click γ
      @ ↑ι
    <<<
      sstore۰model γ vs
    | RET ();
      sstore۰scanner γ Own vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:scanner)) HΦ".
    wp۰rec. wp۰pures.
    wp۰bind (𝗳𝗮𝗮 _ _)%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰faa.
    iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(-> & ->).
    iMod (refs۰invｰclick with "Hrefs Hmodel₂") as "(%vs' & %Hdom' & _ & Hmodel₂ & Hrefs)".
    { rewrite Hvs1 //. }
    iMod "HΦ" as "(%vs_ & (Hmodel₁ & Hdom_auth) & _ & HΦ)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iDestruct (mono_gset۰lbｰget with "Hdom_auth") as "#Hdom_lb'".
    iMod ("HΦ" with "[$Hmodel₁ $Hdom_auth]") as "HΦ".
    iMod (scannerｰupdate vs' (S g1) with "Hscanner₁ Hscanner₂") as "(Hscanner₁ & Hscanner₂)".
    iMod (generationｰupdate with "Hgeneration_auth") as "Hgeneration_auth".
    iSplitR "Hscanner₁ HΦ".
    { iModIntro. iNext.
      iExists (S g1), vs', vs', refs1, ipast1, iprophs1.
      replace (⁺g1 + 1)%Z with (⁺(S g1)) by lia.
      iFrame. iPureIntro. split_and!; [set_solver | set_solver | done].
    }
    iModIntro. wp۰pures. iApply "HΦ". iExists (S g1). iFrame "#∗". done.
  Qed.

  Lemma sstore٠observeｰspec {γ ι dq ws r} w :
    ws !! r = Some w →
    {{{
      sstore۰inv γ ι ∗
      sstore۰scanner γ dq ws ∗
      sstore۰ref γ r
    }}}
      sstore٠observe γ #r
      @ ↑ι
    {{{
      RET w;
      sstore۰scanner γ dq ws
    }}}.
  Proof.
    iIntros "%Hws %Φ ((:inv) & (:scanner) & (:ref)) HΦ".
    wp۰rec. wp۰pures.
    iAssert (|={↑ι}=> generation۰lb γ g ∗ scanner₁ γ dq ws g)%I with "[Hscanner₁]" as ">(#Hg & Hscanner₁)".
    { iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
      iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg".
      iSplitR "Hscanner₁". { iFrameSteps. }
      iFrameSteps.
    }
    wp۰apply (sstore٠forwardｰspec with "[$Ht_proph $Hinv $Hρ $Hg]") as "#Hsnapshot_lb"; first done.
    wp۰pures.
    wp۰bind (_.{ref_snapshot})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (ref۰elemｰvalid with "Hrefs_auth Hρ") as %Hrefs_lookup.
    iDestruct (refs۰invｰacc' with "Hrefs") as "((:ref۰inv =2) & Hrefs)"; first done.
    wp۰load.
    iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    destruct (inv۰pureｰstable Hinv2 Hgen) as (_ & Hval).
    iSplitR "Hscanner₁ HΦ". { iFrameSteps. }
    iModIntro. wp۰pures.
    rewrite Hval -(Hwₛ2 w Hws). iApply "HΦ".
    iFrameSteps.
  Qed.
End sstore_G.

Require zoo_saturn.sstore__opaque.

Please opacify.
