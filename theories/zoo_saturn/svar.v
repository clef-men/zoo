Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.function.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.saved_prop.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo.program_logic.identifier.
Require Import zoo.program_logic.prophet_typed.
Require Export zoo_saturn.svar__code.
Require Import zoo_saturn.svar__types.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types g gₛ : nat.
Implicit Types v vₛ 𝑣 𝑣ₛ w : val.
Implicit Types id : identifier.
Implicit Types ι : namespace.

Variant prophecy :=
  | ProphecyForward v g
  | ProphecySet id v.
Implicit Types proph : prophecy.
Implicit Types prophs : list prophecy.

#[local] Definition prophet :=
  {|prophet_typed_type :=
      prophecy
  ; prophet_typed_of_val v w :=
      match v, w with
      | ValBool false, ValBlock _ 0 _ =>
          Some None
      | ValBool true, ValBlock _ 0 [v; ValInt g] =>
          Some $ Some $ ProphecyForward v ₊g
      | ()%V, ValBlock _ 1 [ValId id; v] =>
          Some $ Some $ ProphecySet id v
      | _, _ =>
          None
      end
  |}.

Record waiter :=
  { waiter_val : val
  ; waiter_post : gname
  }.
Implicit Types waiter : waiter.
Implicit Types waiters waitersₗ : gmap identifier waiter.

Class SvarG Σ `{zoo_G : !ZooG Σ} :=
  { #[local] svar_G_model_G :: TwinsG Σ val_O
  ; #[local] svar_G_scanner_G :: TwinsG Σ (leibnizO (val * nat))
  ; #[local] svar_G_generation_G :: AuthNatMaxG Σ
  ; #[local] svar_G_snapshot_G :: AuthNatMaxG Σ
  ; #[local] svar_G_waiters_G :: ghost_mapG Σ identifier waiter
  ; #[local] svar_G_waiter_post_G :: SavedPropG Σ
  }.

Definition svar_Σ :=
  #[twins_Σ val_O
  ; twins_Σ (leibnizO (val * nat))
  ; auth_nat_max_Σ
  ; auth_nat_max_Σ
  ; ghost_mapΣ identifier waiter
  ; saved_prop_Σ
  ].
#[global] Instance subG_svar_Σ Σ `{zoo_G : !ZooG Σ} :
  subG svar_Σ Σ →
  SvarG Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section svar_G.
    Context `{svar_G : SvarG Σ}.

    Implicit Types t : location.
    Implicit Types P : iProp Σ.
    Implicit Types Φ : val → iProp Σ.

    Record svar_name :=
      { svar_name_prophet : prophet_id
      ; svar_name_model : gname
      ; svar_name_scanner : gname
      ; svar_name_generation : gname
      ; svar_name_snapshot : gname
      ; svar_name_waiters : gname
      }.
    Implicit Types γ : svar_name.

    #[global] Instance svar_name_eq_dec : EqDecision svar_name :=
      ltac:(solve_decision).
    #[global] Instance svar_name_countable :
      Countable svar_name.
    Proof.
      solve_countable.
    Qed.

    Record operation := Operation
      { operation_id : identifier
      ; operation_val : val
      }.
    Add Printing Constructor operation.
    Implicit Types op : operation.
    Implicit Types ops : list operation.

    Record segment := Segment
      { segment_ops : list operation
      ; segment_val : val
      ; segment_gen : nat
      }.
    Add Printing Constructor segment.
    Implicit Types seg : segment.
    Implicit Types segs : list segment.

    #[local] Definition segment_update_ops f seg :=
      {|segment_ops := f seg.(segment_ops)
      ; segment_val := seg.(segment_val)
      ; segment_gen := seg.(segment_gen)
      |}.
    #[local] Definition segment_set_ops ops :=
      segment_update_ops $ const ops.

    #[local] Lemma segment𑁒reconstruct seg ops v g :
      seg.(segment_ops) = ops →
      seg.(segment_val) = v →
      seg.(segment_gen) = g →
      Segment ops v g = seg.
    Proof.
      intros <- <- <-.
      destruct seg => //.
    Qed.

    #[local] Lemma segment_update_ops𑁒id fn seg :
      fn ≡ᶠ id →
      segment_update_ops fn seg = seg.
    Proof.
      rewrite /segment_update_ops.
      intros ->.
      apply segment𑁒reconstruct => //.
    Qed.
    #[local] Lemma segment_update_ops𑁒congruence fn1 fn2 seg :
      fn1 ≡ᶠ fn2 →
      segment_update_ops fn1 seg = segment_update_ops fn2 seg.
    Proof.
      rewrite /segment_update_ops.
      intros ->.
      apply segment𑁒reconstruct => //.
    Qed.
    #[local] Lemma segment_update_ops𑁒compose fn1 fn2 seg :
      segment_update_ops fn2 $ segment_update_ops fn1 seg = segment_update_ops (fn2 ∘ fn1) seg.
    Proof.
      done.
    Qed.

    Record trace := Trace
      { trace_segs : list segment
      ; trace_ops : list operation
      }.
    Add Printing Constructor trace.
    Implicit Types tr : trace.

    #[local] Instance trace_inhabited : Inhabited trace :=
      populate
        {|trace_segs := inhabitant
        ; trace_ops := inhabitant
        |}.

    #[local] Definition trace_update_segs f tr :=
      {|trace_segs := f tr.(trace_segs)
      ; trace_ops := tr.(trace_ops)
      |}.
    #[local] Definition trace_update_ops f tr :=
      {|trace_segs := tr.(trace_segs)
      ; trace_ops := f tr.(trace_ops)
      |}.
    #[local] Definition trace_set_segs segs :=
      trace_update_segs $ const segs.
    #[local] Definition trace_set_ops ops :=
      trace_update_ops $ const ops.

    #[local] Lemma trace𑁒eq_alt tr1 tr2 :
      tr1 = tr2 ↔
        tr1.(trace_segs) = tr2.(trace_segs) ∧
        tr1.(trace_ops) = tr2.(trace_ops).
    Proof.
      destruct tr1, tr2. naive_solver.
    Qed.
    #[local] Lemma trace𑁒reconstruct tr segs ops :
      tr.(trace_segs) = segs →
      tr.(trace_ops) = ops →
      Trace segs ops = tr.
    Proof.
      intros <- <-.
      destruct tr => //.
    Qed.

    #[local] Lemma trace_update_segs𑁒id fn tr :
      fn ≡ᶠ id →
      trace_update_segs fn tr = tr.
    Proof.
      rewrite /trace_update_segs.
      intros ->.
      apply trace𑁒reconstruct => //.
    Qed.
    #[local] Lemma trace_update_segs𑁒compose fn1 fn2 tr :
      trace_update_segs fn2 $ trace_update_segs fn1 tr = trace_update_segs (fn2 ∘ fn1) tr.
    Proof.
      done.
    Qed.
    #[local] Lemma trace_set_segs𑁒compose segs1 segs2 tr :
      trace_set_segs segs2 $ trace_set_segs segs1 tr = trace_set_segs segs2 tr.
    Proof.
      done.
    Qed.
    #[local] Lemma trace_update_ops𑁒compose fn1 fn2 tr :
      trace_update_ops fn2 $ trace_update_ops fn1 tr = trace_update_ops (fn2 ∘ fn1) tr.
    Proof.
      done.
    Qed.
    #[local] Lemma trace_update_ops𑁒id fn tr :
      fn ≡ᶠ id →
      trace_update_ops fn tr = tr.
    Proof.
      rewrite /trace_update_ops.
      intros ->.
      apply trace𑁒reconstruct => //.
    Qed.

    #[local] Fixpoint trace_of_prophecies' segs ops prophs :=
      match prophs with
      | [] =>
          Trace segs ops
      | ProphecyForward v g :: prophs =>
          let seg := Segment ops v g in
          trace_of_prophecies' (segs ++ [seg]) [] prophs
      | ProphecySet id v :: prophs =>
          let op := Operation id v in
          let ops := ops ++ [op] in
          trace_of_prophecies' segs ops prophs
      end.
    #[local] Definition trace_of_prophecies prophs :=
      trace_of_prophecies' [] [] prophs.

    #[local] Definition prophet_model' pid tr : iProp Σ :=
      ∃ prophs,
      prophet_typed_model prophet pid prophs ∗
      ⌜tr = trace_of_prophecies prophs⌝.
    #[local] Definition prophet_model γ :=
      prophet_model' γ.(svar_name_prophet).
    #[local] Instance : CustomIpat "prophet_model" :=
      " ( %prophs
        & Hprophet_model
        & ->
        )
      ".

    #[local] Definition model₁' γ_model v :=
      twins_twin1 (twins_G := svar_G_model_G) γ_model Own v.
    #[local] Definition model₁ γ :=
      model₁' γ.(svar_name_model).
    #[local] Definition model₂' γ_model v :=
      twins_twin2 (twins_G := svar_G_model_G) γ_model v.
    #[local] Definition model₂ γ :=
      model₂' γ.(svar_name_model).

    #[local] Definition scanner₁' γ_scanner dq vₛ g :=
      twins_twin1 γ_scanner dq (vₛ, g).
    #[local] Definition scanner₁ γ :=
      scanner₁' γ.(svar_name_scanner).
    #[local] Definition scanner₂' γ_scanner vₛ g :=
      twins_twin2 γ_scanner (vₛ, g).
    #[local] Definition scanner₂ γ :=
      scanner₂' γ.(svar_name_scanner).

    #[local] Definition generation_auth' γ_generation g :=
      auth_nat_max_auth γ_generation Own g.
    #[local] Definition generation_auth γ :=
      generation_auth' γ.(svar_name_generation).
    #[local] Definition generation_lb γ g :=
      auth_nat_max_lb γ.(svar_name_generation) g.

    #[local] Definition snapshot_auth' γ_snapshot gₛ :=
      auth_nat_max_auth γ_snapshot Own gₛ.
    #[local] Definition snapshot_auth γ :=
      snapshot_auth' γ.(svar_name_snapshot).
    #[local] Definition snapshot_lb γ gₛ :=
      auth_nat_max_lb γ.(svar_name_snapshot) gₛ.

    #[local] Definition waiters_auth' γ_waiters waiters : iProp Σ :=
      ghost_map_auth γ_waiters 1 waiters ∗
      [∗ set] id ∈ dom waiters, identifier_model id.
    #[local] Definition waiters_auth γ :=
      waiters_auth' γ.(svar_name_waiters).
    #[local] Definition waiters_elem γ id waiter :=
      ghost_map_elem γ.(svar_name_waiters) id Own waiter.

    Variant consistency :=
      | Consistent
      | Inconsistent.
    Implicit Types consistent : consistency.

    #[local] Instance consistency_eq_dec : EqDecision consistency :=
      ltac:(solve_decision).

    Record future_operations_result := FutureOps
      { future_operations_consistent : consistency
      ; future_operations_val : val
      ; future_operations_waitersₗ : gmap identifier waiter
      ; future_operations_waiters : gmap identifier waiter
      }.
    Add Printing Constructor future_operations_result.
    #[local] Fixpoint future_operations 𝑣 waiters ops :=
      match ops with
      | [] =>
          FutureOps Consistent 𝑣 ∅ waiters
      | op :: ops =>
          match waiters !! op.(operation_id) with
          | None =>
              FutureOps Inconsistent 𝑣 ∅ waiters
          | Some waiter =>
              let 𝑣 := waiter.(waiter_val) in
              let waiters := delete op.(operation_id) waiters in
              let 'FutureOps consistent 𝑣 waitersₗ waiters := future_operations 𝑣 waiters ops in
              let waitersₗ := <[op.(operation_id) := waiter]> waitersₗ in
              FutureOps consistent 𝑣 waitersₗ waiters
          end
      end.

    Record future_segments_result := FutureSegs
      { future_segments_val : val
      ; future_segments_valₛ : val
      ; future_segments_waitersₗ : gmap identifier waiter
      ; future_segments_waiters : gmap identifier waiter
      }.
    Add Printing Constructor future_segments_result.
    #[local] Fixpoint future_segments 𝑣 𝑣ₛ gₛ g waiters segs :=
      match segs with
      | [] =>
          FutureSegs 𝑣 𝑣ₛ ∅ waiters
      | seg :: segs =>
          if decide (gₛ < seg.(segment_gen) ≤ g) then
            let 'FutureOps consistent 𝑣 waitersₗ_seg waiters := future_operations 𝑣 waiters seg.(segment_ops) in
            if decide (
              consistent = Consistent ∧
              ( 𝑣 = seg.(segment_val)
              ∨ Exists (λ op, op.(operation_val) = seg.(segment_val)) seg.(segment_ops)
              )
            ) then
              let 𝑣ₛ := seg.(segment_val) in
              let gₛ := seg.(segment_gen) in
              let 'FutureSegs 𝑣 𝑣ₛ waitersₗ waiters := future_segments 𝑣 𝑣ₛ gₛ g waiters segs in
              let waitersₗ := waitersₗ_seg ∪ waitersₗ in
              FutureSegs 𝑣 𝑣ₛ waitersₗ waiters
            else
              FutureSegs 𝑣 𝑣ₛ waitersₗ_seg waiters
          else
            FutureSegs 𝑣 𝑣ₛ ∅ waiters
      end.
    #[local] Definition future_segments' v 𝑣 𝑣ₛ gₛ g waiters segs :=
      match segs with
      | [] =>
          FutureSegs v 𝑣ₛ ∅ waiters
      | seg :: _ =>
          if decide (gₛ < seg.(segment_gen) ≤ g) then
            future_segments 𝑣 𝑣ₛ gₛ g waiters segs
          else
            FutureSegs v 𝑣ₛ ∅ waiters
      end.

    #[local] Definition waiters_posts γ waiters : iProp Σ :=
      [∗ map] _ ↦ waiter ∈ waiters,
        ∃ P,
        saved_prop waiter.(waiter_post) P ∗
        ▷ P.

    #[local] Definition waiter_au γ ι waiter P : iProp Σ :=
      AU <{
        ∃∃ v,
        model₁ γ v
      }> @ ⊤ ∖ ↑ι, ∅ <{
        model₁ γ waiter.(waiter_val)
      , COMM
        P
      }>.
    #[local] Definition waiters_aus γ ι waiters : iProp Σ :=
      [∗ map] _ ↦ waiter ∈ waiters,
        ∃ P,
        saved_prop waiter.(waiter_post) P ∗
        waiter_au γ ι waiter P.

    #[local] Definition future_stable γ ι 𝑣 𝑣ₛ v vₛ waiters : iProp Σ :=
      ⌜𝑣 = v⌝ ∗
      ⌜vₛ = v⌝ ∗
      ⌜𝑣ₛ = v⌝ ∗
      waiters_aus γ ι waiters.
    #[local] Instance : CustomIpat "future_stable" :=
      " ( ->
        & ->
        & ->
        & Hwaiters_aus
        )
      ".
    #[local] Definition future_unstable γ ι 𝑣 g 𝑣ₛ gₛ v waiters tr : iProp Σ :=
      let 'FutureSegs 𝑣' 𝑣ₛ' waitersₗ waiters := future_segments' v 𝑣 𝑣ₛ gₛ g waiters tr.(trace_segs) in
      ⌜𝑣 = 𝑣'⌝ ∗
      ⌜𝑣ₛ = 𝑣ₛ'⌝ ∗
      waiters_posts γ waitersₗ ∗
      waiters_aus γ ι waiters.
    #[local] Instance : CustomIpat "future_unstable" :=
      " ( ->
        & ->
        & Hwaiters_posts
        & Hwaiters_aus
        )
      ".
    #[local] Definition future γ ι 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr :=
      if decide (gₛ = g) then
        future_stable γ ι 𝑣 𝑣ₛ v vₛ waiters
      else
        future_unstable γ ι 𝑣 g 𝑣ₛ gₛ v waiters tr.

    #[local] Definition inv_inner t γ ι : iProp Σ :=
      ∃ 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr,
      t.[value] ↦ 𝑣 ∗
      t.[gen] ↦ #g ∗
      t.[snapshot] ↦ (𝑣ₛ, #gₛ) ∗
      model₂ γ v ∗
      scanner₂ γ vₛ g ∗
      generation_auth γ g ∗
      snapshot_auth γ gₛ ∗
      ⌜gₛ ≤ g⌝ ∗
      waiters_auth γ waiters ∗
      prophet_model γ tr ∗
      future γ ι 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr.
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %𝑣{}
        & %g{}
        & %𝑣ₛ{}
        & %gₛ{}
        & %v{}
        & %vₛ{}
        & %waiters{}
        & %tr{}
        & Ht_value
        & Ht_gen
        & Ht_snapshot
        & Hmodel₂
        & Hscanner₂
        & Hgeneration_auth
        & Hsnapshot_auth
        & >%Hgₛ
        & Hwaiters_auth
        & Hpropet_model
        & Hfuture
        )
      ".
    #[local] Definition inv' t γ ι :=
      inv ι (inv_inner t γ ι).
    Definition svar_inv t γ ι : iProp Σ :=
      t.[proph] ↦□ #γ.(svar_name_prophet) ∗
      inv' t γ ι.
    #[local] Instance : CustomIpat "inv" :=
      " ( #Ht_proph
        & #Hinv
        )
      ".

    Definition svar_model :=
      model₁.

    Definition svar_scanner γ dq vₛ : iProp Σ :=
      ∃ g,
      scanner₁ γ dq vₛ g.
    #[local] Instance : CustomIpat "scanner" :=
      " ( %g{}
        & Hscanner₁{_{}}
        )
      ".

    #[global] Instance svar_model_timeless γ v :
      Timeless (svar_model γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance svar_scanner_timeless γ dq vₛ :
      Timeless (svar_scanner γ dq vₛ).
    Proof.
      apply _.
    Qed.

    #[global] Instance svar_inv_persistent t γ ι :
      Persistent (svar_inv t γ ι).
    Proof.
      apply _.
    Qed.
    #[global] Instance svar_scanner_persistent γ vₛ :
      Persistent (svar_scanner γ DfracDiscarded vₛ).
    Proof.
      apply _.
    Qed.

    #[global] Instance svar_scanner_fractional γ vₛ :
      Fractional (λ q, svar_scanner γ (DfracOwn q) vₛ).
    Proof.
      intros q1 q2.
      iSplit.
      - iIntros "(:scanner)".
        iDestruct "Hscanner₁" as "($ & $)".
      - iIntros "((:scanner =1) & (:scanner =2))".
        iDestruct (twins_twin1_combine_L with "Hscanner₁_1 Hscanner₁_2") as "(% & $)".
    Qed.
    #[global] Instance svar_scanner_as_fractional γ q vₛ :
      AsFractional (svar_scanner γ (DfracOwn q) vₛ) (λ q, svar_scanner γ (DfracOwn q) vₛ) q.
    Proof.
      split; [done | apply _].
    Qed.

    #[local] Lemma trace_of_prophecies'𑁒segs_prefix tr segs ops prophs :
      tr = trace_of_prophecies' segs ops prophs →
      segs `prefix_of` tr.(trace_segs).
    Proof.
      move: segs ops. induction prophs as [| [v g | id v] prophs IH] => segs ops /= Htr.
      - naive_solver.
      - eauto using prefix_app_l.
      - naive_solver.
    Qed.
    #[local] Lemma trace_of_prophecies'𑁒decompose segs₀ ops prophs :
      trace_of_prophecies' segs₀ ops prophs =
        let tr := trace_of_prophecies prophs in
        match tr.(trace_segs) with
        | [] =>
            Trace segs₀ (ops ++ tr.(trace_ops))
        | seg :: segs =>
            trace_set_segs (segs₀ ++ segment_update_ops ((++) ops) seg :: segs) tr
        end.
    Proof.
      simpl.
      move: segs₀ ops. induction prophs as [| [v g | id v] prophs IH] => segs₀ ops; cbn.
      - rewrite right_id //.
      - rewrite !{}IH.
        destruct (trace_of_prophecies prophs).(trace_segs) as [| seg' segs'] => /=.
        + apply trace𑁒eq_alt => /=. split. 2: done.
          rewrite /segment_update_ops right_id //.
        + apply trace𑁒eq_alt => /=. split. 2: done.
          rewrite -assoc /=.
          rewrite /segment_update_ops right_id //.
      - rewrite !{}IH.
        destruct (trace_of_prophecies prophs).(trace_segs) as [| seg' segs'] => /=.
        + rewrite -assoc //.
        + rewrite trace_set_segs𑁒compose segment_update_ops𑁒compose.
          do 3 f_equal.
          apply segment_update_ops𑁒congruence => ops'.
          rewrite -assoc //.
    Qed.
    #[local] Lemma trace_of_prophecies'𑁒decompose' segs prophs :
      trace_of_prophecies' segs [] prophs = trace_update_segs ((++) segs) $ trace_of_prophecies prophs.
    Proof.
      rewrite trace_of_prophecies'𑁒decompose /=.
      destruct (trace_of_prophecies prophs).(trace_segs) as [| seg segs'] eqn:Htr_segs.
      all: apply trace𑁒eq_alt => /=.
      all: split; last done.
      - rewrite Htr_segs right_id //.
      - rewrite segment_update_ops𑁒id // Htr_segs //.
    Qed.
    #[local] Lemma trace_of_prophecies'𑁒app_segs tr segs1 segs2 ops prophs :
      tr = trace_of_prophecies' segs2 ops prophs →
      trace_of_prophecies' (segs1 ++ segs2) ops prophs = trace_update_segs ((++) segs1) tr.
    Proof.
      move: segs2 ops. induction prophs as [| [v g | id v] prophs IH] => segs2 ops /= Htr.
      - naive_solver.
      - rewrite -assoc. auto.
      - naive_solver.
    Qed.
    #[local] Lemma trace_of_prophecies'𑁒empty_segs₁ tr segs ops prophs :
      tr = trace_of_prophecies' segs ops prophs →
      tr.(trace_segs) = [] →
      segs = [].
    Proof.
      intros Hsegs%trace_of_prophecies'𑁒segs_prefix Htr_segs.
      rewrite Htr_segs in Hsegs.
      apply prefix_nil_inv => //.
    Qed.
    #[local] Lemma trace_of_prophecies'𑁒empty_segs₂ tr segs ops1 ops2 prophs :
      tr = trace_of_prophecies' segs ops2 prophs →
      tr.(trace_segs) = [] →
      trace_of_prophecies' segs (ops1 ++ ops2) prophs = Trace [] (ops1 ++ tr.(trace_ops)).
    Proof.
      move: ops2. induction prophs as [| [v g | id v] prophs IH] => ops2 /= Htr Htr_segs.
      - naive_solver.
      - apply trace_of_prophecies'𑁒empty_segs₁, app_not_nil in Htr as []; auto.
      - rewrite -assoc. auto.
    Qed.
    #[local] Lemma trace_of_prophecies'𑁒empty_segs₃ tr segs ops prophs :
      tr = trace_of_prophecies' segs ops prophs →
      tr.(trace_segs) = [] →
        ∃ ops',
        tr.(trace_ops) = ops ++ ops' ∧
        trace_of_prophecies prophs = Trace [] ops'.
    Proof.
      move: ops. induction prophs as [| [v g | id v] prophs IH] => ops /= Htr Htr_segs; cbn.
      - exists []. rewrite right_id.
        naive_solver.
      - apply trace_of_prophecies'𑁒empty_segs₁, app_not_nil in Htr as []; auto.
      - apply IH in Htr as (ops' & Htr_ops & Htr). 2: done.
        exists (Operation id v :: ops'). split.
        + rewrite -assoc // in Htr_ops.
        + rewrite -(app_nil_r [_]) (trace_of_prophecies'𑁒empty_segs₂ (Trace [] ops')) //.
    Qed.
    #[local] Lemma trace_of_prophecies'𑁒nonempty_segs tr ops prophs seg segs :
      tr = trace_of_prophecies' [] ops prophs →
      tr.(trace_segs) = seg :: segs →
        ∃ seg',
        seg = segment_update_ops ((++) ops) seg' ∧
        trace_of_prophecies prophs = trace_set_segs (seg' :: segs) tr.
    Proof.
      move: ops. induction prophs as [| [v g | id v] prophs IH] => ops /= Htr Htr_segs; cbn.
      - naive_solver.
      - odestruct (trace_of_prophecies'𑁒segs_prefix tr) as (segs_ & Htr_segs_). 1: done.
        rewrite Htr_segs /= in Htr_segs_. injection Htr_segs_ as [= -> <-].
        exists (Segment [] v g). split.
        + rewrite /segment_update_ops right_id //.
        + rewrite !trace_of_prophecies'𑁒decompose' in Htr |- *.
          naive_solver.
      - apply IH in Htr as (seg' & -> & Hprophs). 2: done.
        exists (segment_update_ops (cons $ Operation id v) seg'). split.
        + rewrite segment_update_ops𑁒compose.
          apply segment_update_ops𑁒congruence => ops'.
          rewrite -assoc //.
        + rewrite trace_of_prophecies'𑁒decompose Hprophs //.
    Qed.

    #[local] Lemma trace_of_prophecies𑁒ProphecyForward v g prophs :
      trace_of_prophecies (ProphecyForward v g :: prophs) = trace_update_segs (cons $ Segment [] v g) $ trace_of_prophecies prophs.
    Proof.
      cbn.
      rewrite -(app_nil_r [_]) (trace_of_prophecies'𑁒app_segs (trace_of_prophecies prophs)) //.
    Qed.
    #[local] Lemma trace_of_prophecies𑁒ProphecySet_empty_segs {tr} id v prophs :
      tr = trace_of_prophecies (ProphecySet id v :: prophs) →
      tr.(trace_segs) = [] →
        ∃ ops,
        tr.(trace_ops) = Operation id v :: ops ∧
        trace_of_prophecies prophs = trace_set_ops ops $ trace_of_prophecies $ ProphecySet id v :: prophs.
    Proof.
      cbn.
      intros Htr Htr_segs.
      pose proof Htr as (ops & Htr_ops & ->)%trace_of_prophecies'𑁒empty_segs₃. 2: done.
      exists ops. split.
      - done.
      - apply trace𑁒reconstruct; naive_solver.
    Qed.
    #[local] Lemma trace_of_prophecies𑁒ProphecySet_nonempty_segs {tr} id v prophs seg segs :
      tr = trace_of_prophecies (ProphecySet id v :: prophs) →
      tr.(trace_segs) = seg :: segs →
        ∃ seg',
        seg = segment_update_ops (cons $ Operation id v) seg' ∧
        trace_of_prophecies prophs = trace_set_segs (seg' :: segs) tr.
    Proof.
      cbn.
      apply trace_of_prophecies'𑁒nonempty_segs.
    Qed.

    Opaque trace_of_prophecies.

    #[local] Lemma wp_proph E :
      {{{
        True
      }}}
        Proph @ E
      {{{
        pid tr
      , RET #pid;
        prophet_model' pid tr
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_apply (prophet_typed_wp_proph prophet with "[//]") as (pid prophs) "Hprophet_model".
      iApply "HΦ".
      iExists prophs. iFrameSteps.
    Qed.

    #[local] Lemma wp_resolve e γ v tr E Φ :
      Atomic e →
      to_val e = None →
      prophet_model γ tr -∗
      WP e @ E {{ w,
        ∃ oproph,
        ⌜prophet.(prophet_typed_of_val) w v = Some oproph⌝ ∗
        match oproph with
        | None =>
            prophet_model γ tr -∗
            Φ w
        | Some (ProphecyForward v g) =>
            ⌜head tr.(trace_segs) = Some $ Segment [] v g⌝ -∗
            prophet_model γ (trace_update_segs tail tr) -∗
            Φ w
        | Some (ProphecySet id v) =>
            match tr.(trace_segs) with
            | [] =>
                ⌜head tr.(trace_ops) = Some $ Operation id v⌝ -∗
                prophet_model γ (trace_update_ops tail tr) -∗
                Φ w
            | seg :: segs =>
                ⌜head seg.(segment_ops) = Some $ Operation id v⌝ -∗
                prophet_model γ (trace_set_segs (segment_update_ops tail seg :: segs) tr) -∗
                Φ w
            end
        end
      }} -∗
      WP Resolve e #γ.(svar_name_prophet) v @ E {{ Φ }}.
    Proof.
      iIntros "% % (:prophet_model) HΦ".

      wp_apply (prophet_typed_wp_resolve prophet with "[$Hprophet_model]"). 1: done.
      wp_apply (wp_wand with "HΦ") as "%w (%oproph & -> & HΦ)".
      destruct oproph as [proph |]. 2: iSteps.
      iStep. iIntros "/= %prophs' -> Hprophet_model".
      destruct proph as [v' g | id v'].
      - iEval (rewrite trace_of_prophecies𑁒ProphecyForward /=) in "HΦ".
        iSteps. iPureIntro.
        rewrite trace_update_segs𑁒compose trace_update_segs𑁒id //.
      - destruct (trace_of_prophecies $ _ :: _) as [segs ops] eqn:Hprophs => /=.
        destruct segs as [| seg segs].
        + opose proof* (trace_of_prophecies𑁒ProphecySet_empty_segs id v' prophs') as (ops' & Htr_ops & Hprophs'). 1,2: done.
          simplify.
          iSteps. iPureIntro.
          rewrite Hprophs' Hprophs //.
        + opose proof* (trace_of_prophecies𑁒ProphecySet_nonempty_segs id v' prophs') as (seg' & -> & Hprophs'). 1,2: done.
          iSteps. iPureIntro.
          rewrite segment_update_ops𑁒compose segment_update_ops𑁒id //.
    Qed.

    Opaque prophet_model'.

    #[local] Lemma model_alloc v :
      ⊢ |==>
        ∃ γ_model,
        model₁' γ_model v ∗
        model₂' γ_model v.
    Proof.
      apply twins_alloc'.
    Qed.
    #[local] Lemma model₁_exclusive γ v1 v2 :
      model₁ γ v1 -∗
      model₁ γ v2 -∗
      False.
    Proof.
      apply twins_twin1_exclusive.
    Qed.
    #[local] Lemma model_agree γ v1 v2 :
      model₁ γ v1 -∗
      model₂ γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply: twins_agree_L.
    Qed.
    #[local] Lemma model_update {γ v1 v2} v :
      model₁ γ v1 -∗
      model₂ γ v2 ==∗
        model₁ γ v ∗
        model₂ γ v.
    Proof.
      apply twins_update.
    Qed.

    #[local] Lemma scanner_alloc vₛ :
      ⊢ |==>
        ∃ γ_scanner,
        scanner₁' γ_scanner Own vₛ 0 ∗
        scanner₂' γ_scanner vₛ 0.
    Proof.
      apply twins_alloc'.
    Qed.
    #[local] Lemma scanner₁_exclusive γ vₛ1 g1 dq2 vₛ2 g2 :
      scanner₁ γ Own vₛ1 g1 -∗
      scanner₁ γ dq2 vₛ2 g2 -∗
      False.
    Proof.
      apply twins_twin1_exclusive.
    Qed.
    #[local] Lemma scanner_agree γ dq vₛ1 g1 vₛ2 g2 :
      scanner₁ γ dq vₛ1 g1 -∗
      scanner₂ γ vₛ2 g2 -∗
        ⌜vₛ1 = vₛ2⌝ ∗
        ⌜g1 = g2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (twins_agree_L with "H1 H2") as %[= -> ->] => //.
    Qed.
    #[local] Lemma scanner_update {γ vₛ1 g1 vₛ2 g2} vₛ g :
      scanner₁ γ Own vₛ1 g1 -∗
      scanner₂ γ vₛ2 g2 ==∗
        scanner₁ γ Own vₛ g ∗
        scanner₂ γ vₛ g.
    Proof.
      iIntros "H1 H2".
      iDestruct (twins_agree_L with "H1 H2") as %[= -> ->].
      iApply (twins_update with "H1 H2").
    Qed.
    #[local] Lemma scanner_update_val {γ vₛ1 g1 vₛ2 g2} vₛ :
      scanner₁ γ Own vₛ1 g1 -∗
      scanner₂ γ vₛ2 g2 ==∗
        scanner₁ γ Own vₛ g1 ∗
        scanner₂ γ vₛ g2.
    Proof.
      iIntros "H1 H2".
      iDestruct (scanner_agree with "H1 H2") as %(-> & ->).
      iApply (scanner_update with "H1 H2").
    Qed.

    #[local] Lemma generation_alloc :
      ⊢ |==>
        ∃ γ_generation,
        generation_auth' γ_generation 0.
    Proof.
      apply auth_nat_max_alloc.
    Qed.
    #[local] Lemma generation_lb_get γ g :
      generation_auth γ g ⊢
      generation_lb γ g.
    Proof.
      apply auth_nat_max_lb_get.
    Qed.
    #[local] Lemma generation_lb_valid γ g1 g2 :
      generation_auth γ g1 -∗
      generation_lb γ g2 -∗
      ⌜g2 ≤ g1⌝.
    Proof.
      apply auth_nat_max_lb_valid.
    Qed.
    #[local] Lemma generation_update γ g :
      generation_auth γ g ⊢ |==>
      generation_auth γ ˖g.
    Proof.
      apply auth_nat_max_update. 1: lia.
    Qed.

    #[local] Lemma snapshot_alloc :
      ⊢ |==>
        ∃ γ_snapshot,
        snapshot_auth' γ_snapshot 0.
    Proof.
      apply auth_nat_max_alloc.
    Qed.
    #[local] Lemma snapshot_lb_get γ gₛ :
      snapshot_auth γ gₛ ⊢
      snapshot_lb γ gₛ.
    Proof.
      apply auth_nat_max_lb_get.
    Qed.
    #[local] Lemma snapshot_lb_valid γ gₛ1 gₛ2 :
      snapshot_auth γ gₛ1 -∗
      snapshot_lb γ gₛ2 -∗
      ⌜gₛ2 ≤ gₛ1⌝.
    Proof.
      apply auth_nat_max_lb_valid.
    Qed.
    #[local] Lemma snapshot_update {γ gₛ} gₛ' :
      gₛ ≤ gₛ' →
      snapshot_auth γ gₛ ⊢ |==>
      snapshot_auth γ gₛ'.
    Proof.
      apply auth_nat_max_update.
    Qed.

    #[local] Lemma waiters_alloc :
      ⊢ |==>
        ∃ γ_waiters,
        waiters_auth' γ_waiters ∅.
    Proof.
      iMod ghost_map_alloc as "(%γ_waiters & $ & _)".
      iApply big_sepS_empty => //.
    Qed.

    Opaque waiters_auth'.

    #[local] Lemma gen𑁒spec_scanner t γ ι dq vₛ g :
      {{{
        inv' t γ ι ∗
        scanner₁ γ dq vₛ g
      }}}
        (#t).{gen}
      {{{
        RET #g;
        scanner₁ γ dq vₛ g
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & Hscanner₁) HΦ".

      iInv "Hinv" as "(:inv_inner =1)".
      wp_load.
      iDestruct (scanner_agree with "Hscanner₁ Hscanner₂") as %(<- & <-).
      iSplitR "Hscanner₁ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma svar٠make𑁒spec ι v :
      {{{
        True
      }}}
        svar٠make v
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        svar_inv t γ ι ∗
        svar_model γ v ∗
        svar_scanner γ Own v
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_apply+ (wp_proph with "[//]") as (pid tr) "Hprophet_model".
      wp_block t as "Hmeta" "(Ht_value & Ht_gen & Ht_snapshot & Ht_proph & _)".
      iMod (pointsto_persist with "Ht_proph") as "#Ht_proph".

      iMod (model_alloc v) as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iMod (scanner_alloc v) as "(%γ_scanner & Hscanner₁ & Hscanner₂)".
      iMod generation_alloc as "(%γ_generation & Hgeneration_auth)".
      iMod snapshot_alloc as "(%γ_snapshot & Hsnapshot_auth)".
      iMod waiters_alloc as "(%γ_waiters & Hwaiters_auth)".

      pose γ :=
        {|svar_name_prophet := pid
        ; svar_name_model := γ_model
        ; svar_name_scanner := γ_scanner
        ; svar_name_generation := γ_generation
        ; svar_name_snapshot := γ_snapshot
        ; svar_name_waiters := γ_waiters
        |}.

      iApply ("HΦ" $! t γ).
      iFrameStep.
      iApply inv_alloc.
      iFrameSteps.
      iApply big_sepM_empty => //.
    Qed.

    (* Lemma svar٠get𑁒spec t γ ι : *)
    (*   <<< *)
    (*     svar_inv t γ ι *)
    (*   | ∀∀ v, *)
    (*     svar_model γ v *)
    (*   >>> *)
    (*     svar٠get #t @ ↑ι *)
    (*   <<< *)
    (*     svar_model γ v *)
    (*   | RET v; *)
    (*     True *)
    (*   >>>. *)
    (* Proof. *)
    (* Admitted. *)

    Lemma svar٠set𑁒spec t γ ι v :
      <<<
        svar_inv t γ ι
      | ∀∀ v',
        svar_model γ v'
      >>>
        svar٠set #t v @ ↑ι
      <<<
        svar_model γ v
      | RET ();
        True
      >>>.
    Proof.
    Admitted.

    #[local] Definition click_au γ ι Φ : iProp Σ :=
      AU <{
        ∃∃ v,
        model₁ γ v
      }> @ ⊤ ∖ ↑ι, ∅ <{
        model₁ γ v
      , COMM
        Φ v
      }>.
    #[local] Lemma future_stable_incr_gen {γ ι 𝑣 𝑣ₛ v vₛ waiters} gₛ tr Φ :
      future_stable γ ι 𝑣 𝑣ₛ v vₛ waiters -∗
      model₂ γ v -∗
      click_au γ ι Φ ==∗
        ∃ v vₛ,
        future γ ι 𝑣 ˖gₛ 𝑣ₛ gₛ v vₛ waiters tr ∗
        model₂ γ v ∗
        Φ vₛ.
    Proof.
      iIntros "(:future_stable) Hmodel₂ Hclick_au".
    Admitted.
    #[local] Lemma future_incr_gen γ ι 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr Φ :
      future γ ι 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr -∗
      model₂ γ v -∗
      click_au γ ι Φ ==∗
        ∃ v vₛ,
        future γ ι 𝑣 ˖g 𝑣ₛ gₛ v vₛ waiters tr ∗
        model₂ γ v ∗
        Φ vₛ.
    Proof.
      iIntros "Hfuture Hmodel₂ Hclick_au".

      iEval (rewrite /future) in "Hfuture".
      case_decide as [-> | Hgₛ].

      - iDestruct "Hfuture" as "(:future_stable)".
        admit.

      -
        admit.
    Admitted.
    Lemma svar٠click𑁒spec t γ ι vₛ :
      <<<
        svar_inv t γ ι ∗
        svar_scanner γ Own vₛ
      | ∀∀ v,
        svar_model γ v
      >>>
        svar٠click #t @ ↑ι
      <<<
        svar_model γ v
      | RET ();
        svar_scanner γ Own v
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:scanner)) HΦ".

      wp_rec.
      wp_apply (gen𑁒spec_scanner with "[$Hinv $Hscanner₁]") as "Hscanner₁".
      wp_pures.

      iInv "Hinv" as "(:inv_inner =1)".
      wp_store.
      iDestruct (scanner_agree with "Hscanner₁ Hscanner₂") as "(<- & <-)".
      iMod (future_incr_gen with "Hfuture Hmodel₂ HΦ") as "(%v' & %vₛ' & Hfuture & Hmodel₂ & HΦ)".
      iMod (scanner_update vₛ' ˖g with "Hscanner₁ Hscanner₂") as "(Hscanner₁ & Hscanner₂)".
      iMod (generation_update with "Hgeneration_auth") as "Hgeneration_auth".
      iSplitR "Hscanner₁ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma svar٠observe𑁒spec t γ ι dq vₛ :
      {{{
        svar_inv t γ ι ∗
        svar_scanner γ dq vₛ
      }}}
        svar٠observe #t
      {{{
        RET vₛ;
        svar_scanner γ dq vₛ
      }}}.
    Proof.
    Admitted.
  End svar_G.

  #[global] Opaque svar_inv.
  #[global] Opaque svar_model.
  #[global] Opaque svar_scanner.
End base.

Require zoo_saturn.svar__opaque.

Section svar_G.
  Context `{svar_G : SvarG Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition svar_inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.svar_inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition svar_model t v : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.svar_model γ v.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition svar_scanner t dq vₛ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.svar_scanner γ dq vₛ.
  #[local] Instance : CustomIpat "scanner" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hscanner{_{}}
      )
    ".

  #[global] Instance svar_model_timeless t v :
    Timeless (svar_model t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance svar_scanner_timeless t dq vₛ :
    Timeless (svar_scanner t dq vₛ).
  Proof.
    apply _.
  Qed.

  #[global] Instance svar_inv_persistent t ι :
    Persistent (svar_inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance svar_scanner_persistent t vₛ :
    Persistent (svar_scanner t DfracDiscarded vₛ).
  Proof.
    apply _.
  Qed.

  #[global] Instance svar_scanner_fractional t vₛ :
    Fractional (λ q, svar_scanner t (DfracOwn q) vₛ).
  Proof.
    intros q1 q2.
    iSplit.
    - iIntros "(:scanner)".
      iDestruct "Hscanner" as "($ & $)".
      iSteps.
    - iIntros "((:scanner =1) & (:scanner =2))". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
      iCombine "Hscanner_1 Hscanner_2" as "$".
      iSteps.
  Qed.
  #[global] Instance svar_scanner_as_fractional t q vₛ :
    AsFractional (svar_scanner t (DfracOwn q) vₛ) (λ q, svar_scanner t (DfracOwn q) vₛ) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma svar٠make𑁒spec ι v :
    {{{
      True
    }}}
      svar٠make v
    {{{
      t
    , RET t;
      svar_inv t ι ∗
      svar_model t v ∗
      svar_scanner t Own v
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.svar٠make𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel & Hscanner)".
    iMod (meta_set γ with "Hmeta"). 1: done.
    iSteps.
  Qed.

  (* Lemma svar٠get𑁒spec t ι : *)
  (*   <<< *)
  (*     svar_inv t ι *)
  (*   | ∀∀ v, *)
  (*     svar_model t v *)
  (*   >>> *)
  (*     svar٠get t @ ↑ι *)
  (*   <<< *)
  (*     svar_model t v *)
  (*   | RET v; *)
  (*     True *)
  (*   >>>. *)
  (* Proof. *)
  (* Qed. *)

  Lemma svar٠set𑁒spec t ι v :
    <<<
      svar_inv t ι
    | ∀∀ v',
      svar_model t v'
    >>>
      svar٠set t v @ ↑ι
    <<<
      svar_model t v
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.svar٠set𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"). 1: done. iIntros "%v' (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma svar٠click𑁒spec t ι vₛ :
    <<<
      svar_inv t ι ∗
      svar_scanner t Own vₛ
    | ∀∀ v,
      svar_model t v
    >>>
      svar٠click t @ ↑ι
    <<<
      svar_model t v
    | RET ();
      svar_scanner t Own v
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:scanner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.svar٠click𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"). 1: done. iIntros "%v (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma svar٠observe𑁒spec t ι dq vₛ :
    {{{
      svar_inv t ι ∗
      svar_scanner t dq vₛ
    }}}
      svar٠observe t
    {{{
      RET vₛ;
      svar_scanner t dq vₛ
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:scanner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.svar٠observe𑁒spec with "[$]").
    iSteps.
  Qed.
End svar_G.

#[global] Opaque svar_inv.
#[global] Opaque svar_model.
#[global] Opaque svar_scanner.
