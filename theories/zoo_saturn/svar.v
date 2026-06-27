Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.function.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.saved_prop.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_typed.
Require Export zoo_saturn.svar__code.
Require Import zoo_saturn.svar__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type g gₛ : nat.
Implicit Type v vₛ 𝑣 𝑣ₛ w : val.
Implicit Type id : identifier.
Implicit Type ι : namespace.

Variant prophecy :=
  | ProphecyForward v g
  | ProphecySet id v.
Implicit Type proph : prophecy.
Implicit Type prophs : list prophecy.

#[local] Definition prophet :=
  {|prophet_typed۰type :=
      prophecy
  ; prophet_typed۰of_val v w :=
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
  { waiter۰val : val
  ; waiter۰post : gname
  }.
Implicit Type waiter : waiter.
Implicit Type waiters waitersₗ waitersₚ : gmap identifier waiter.

Class SvarG Σ `{zoo_G : !ZooG Σ} :=
  { #[local] svar۰G۰model۰G :: TwinsG Σ val_O
  ; #[local] svar۰G۰scanner۰G :: TwinsG Σ (leibnizO (val * nat))
  ; #[local] svar۰G۰generation۰G :: AuthNatMaxG Σ
  ; #[local] svar۰G۰snapshot۰G :: AuthNatMaxG Σ
  ; #[local] svar۰G۰waiters۰G :: ghost_mapG Σ identifier waiter
  ; #[local] svar۰G۰waiter۰post۰G :: SavedPropG Σ
  }.

Definition svar۰Σ :=
  #[twins۰Σ val_O
  ; twins۰Σ (leibnizO (val * nat))
  ; auth_nat_max۰Σ
  ; auth_nat_max۰Σ
  ; ghost_mapΣ identifier waiter
  ; saved_prop۰Σ
  ].
#[global] Instance subGｰsvar۰Σ Σ `{zoo_G : !ZooG Σ} :
  subG svar۰Σ Σ →
  SvarG Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section svar_G.
    Context `{svar_G : SvarG Σ}.

    Implicit Type t : location.
    Implicit Type P : iProp Σ.
    Implicit Type Φ : val → iProp Σ.

    Record svar۰name :=
      { svar۰name۰prophet : prophet_id
      ; svar۰name۰model : gname
      ; svar۰name۰scanner : gname
      ; svar۰name۰generation : gname
      ; svar۰name۰snapshot : gname
      ; svar۰name۰waiters : gname
      }.
    Implicit Type γ : svar۰name.

    #[global] Instance svar۰nameｰeq_dec : EqDecision svar۰name :=
      ltac:(solve_decision).
    #[global] Instance svar۰nameｰcountable :
      Countable svar۰name.
    Proof.
      solve_countable.
    Qed.

    Record operation := Operation
      { operation۰id : identifier
      ; operation۰val : val
      }.
    Add Printing Constructor operation.
    Implicit Type op : operation.
    Implicit Type ops : list operation.

    Record segment := Segment
      { segment۰ops : list operation
      ; segment۰val : val
      ; segment۰gen : nat
      }.
    Add Printing Constructor segment.
    Implicit Type seg : segment.
    Implicit Type segs : list segment.

    #[local] Definition segment۰update_ops f seg :=
      {|segment۰ops := f seg.(segment۰ops)
      ; segment۰val := seg.(segment۰val)
      ; segment۰gen := seg.(segment۰gen)
      |}.
    #[local] Definition segment۰set_ops ops :=
      segment۰update_ops $ const ops.

    #[local] Lemma segmentｰreconstruct seg ops v g :
      seg.(segment۰ops) = ops →
      seg.(segment۰val) = v →
      seg.(segment۰gen) = g →
      Segment ops v g = seg.
    Proof.
      intros <- <- <-.
      destruct seg => //.
    Qed.

    #[local] Lemma segment۰update_opsｰid fn seg :
      fn ≡ᶠ id →
      segment۰update_ops fn seg = seg.
    Proof.
      rewrite /segment۰update_ops.
      intros ->.
      apply segmentｰreconstruct => //.
    Qed.
    #[local] Lemma segment۰update_opsｰcongruence fn1 fn2 seg :
      fn1 ≡ᶠ fn2 →
      segment۰update_ops fn1 seg = segment۰update_ops fn2 seg.
    Proof.
      rewrite /segment۰update_ops.
      intros ->.
      apply segmentｰreconstruct => //.
    Qed.
    #[local] Lemma segment۰update_opsｰcompose fn1 fn2 seg :
      segment۰update_ops fn2 $ segment۰update_ops fn1 seg = segment۰update_ops (fn2 ∘ fn1) seg.
    Proof.
      done.
    Qed.

    Record trace := Trace
      { trace۰segs : list segment
      ; trace۰ops : list operation
      }.
    Add Printing Constructor trace.
    Implicit Type tr : trace.

    #[local] Instance traceｰinhabited : Inhabited trace :=
      populate
        {|trace۰segs := inhabitant
        ; trace۰ops := inhabitant
        |}.

    #[local] Definition trace۰update_segs f tr :=
      {|trace۰segs := f tr.(trace۰segs)
      ; trace۰ops := tr.(trace۰ops)
      |}.
    #[local] Definition trace۰update_ops f tr :=
      {|trace۰segs := tr.(trace۰segs)
      ; trace۰ops := f tr.(trace۰ops)
      |}.
    #[local] Definition trace۰set_segs segs :=
      trace۰update_segs $ const segs.
    #[local] Definition trace۰set_ops ops :=
      trace۰update_ops $ const ops.

    #[local] Lemma traceｰeqｰalt tr1 tr2 :
      tr1 = tr2 ↔
        tr1.(trace۰segs) = tr2.(trace۰segs) ∧
        tr1.(trace۰ops) = tr2.(trace۰ops).
    Proof.
      destruct tr1, tr2. naive_solver.
    Qed.
    #[local] Lemma traceｰreconstruct tr segs ops :
      tr.(trace۰segs) = segs →
      tr.(trace۰ops) = ops →
      Trace segs ops = tr.
    Proof.
      intros <- <-.
      destruct tr => //.
    Qed.

    #[local] Lemma trace۰update_segsｰid fn tr :
      fn ≡ᶠ id →
      trace۰update_segs fn tr = tr.
    Proof.
      rewrite /trace۰update_segs.
      intros ->.
      apply traceｰreconstruct => //.
    Qed.
    #[local] Lemma trace۰update_segsｰcompose fn1 fn2 tr :
      trace۰update_segs fn2 $ trace۰update_segs fn1 tr = trace۰update_segs (fn2 ∘ fn1) tr.
    Proof.
      done.
    Qed.
    #[local] Lemma trace۰set_segsｰcompose segs1 segs2 tr :
      trace۰set_segs segs2 $ trace۰set_segs segs1 tr = trace۰set_segs segs2 tr.
    Proof.
      done.
    Qed.
    #[local] Lemma trace۰update_opsｰcompose fn1 fn2 tr :
      trace۰update_ops fn2 $ trace۰update_ops fn1 tr = trace۰update_ops (fn2 ∘ fn1) tr.
    Proof.
      done.
    Qed.
    #[local] Lemma trace۰update_opsｰid fn tr :
      fn ≡ᶠ id →
      trace۰update_ops fn tr = tr.
    Proof.
      rewrite /trace۰update_ops.
      intros ->.
      apply traceｰreconstruct => //.
    Qed.

    #[local] Fixpoint trace۰of_prophecies' segs ops prophs :=
      match prophs with
      | [] =>
          Trace segs ops
      | ProphecyForward v g :: prophs =>
          let seg := Segment ops v g in
          trace۰of_prophecies' (segs ++ [seg]) [] prophs
      | ProphecySet id v :: prophs =>
          let op := Operation id v in
          let ops := ops ++ [op] in
          trace۰of_prophecies' segs ops prophs
      end.
    #[local] Definition trace۰of_prophecies prophs :=
      trace۰of_prophecies' [] [] prophs.

    #[local] Definition prophet۰model' pid tr : iProp Σ :=
      ∃ prophs,
      prophet_typed۰model prophet pid prophs ∗
      ⌜tr = trace۰of_prophecies prophs⌝.
    #[local] Definition prophet۰model γ :=
      prophet۰model' γ.(svar۰name۰prophet).
    #[local] Instance : CustomIpat "prophet۰model" :=
      " ( %prophs
        & Hprophet_model
        & ->
        )
      ".

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

    #[local] Definition waiters۰auth' γ_waiters waiters : iProp Σ :=
      ghost_map_auth γ_waiters 1 waiters ∗
      [∗ set] id ∈ dom waiters, identifier۰model id.
    #[local] Definition waiters۰auth γ :=
      waiters۰auth' γ.(svar۰name۰waiters).
    #[local] Definition waiters۰elem γ id waiter :=
      ghost_map_elem γ.(svar۰name۰waiters) id Own waiter.

    Variant consistency :=
      | Consistent
      | Inconsistent.
    Implicit Type consistent : consistency.

    #[local] Instance consistencyｰeq_dec : EqDecision consistency :=
      ltac:(solve_decision).

    Record future۰operations۰result := FutureOps
      { future۰operations۰consistent : consistency
      ; future۰operations۰val : val
      ; future۰operations۰waitersₗ : gmap identifier waiter
      ; future۰operations۰waitersₚ : gmap identifier waiter
      }.
    Add Printing Constructor future۰operations۰result.
    #[local] Fixpoint future۰operations 𝑣 waiters ops :=
      match ops with
      | [] =>
          FutureOps Consistent 𝑣 ∅ waiters
      | op :: ops =>
          match waiters !! op.(operation۰id) with
          | None =>
              FutureOps Inconsistent 𝑣 ∅ waiters
          | Some waiter =>
              let 𝑣 := waiter.(waiter۰val) in
              let waiters := delete op.(operation۰id) waiters in
              let 'FutureOps consistent 𝑣 waitersₗ waitersₚ := future۰operations 𝑣 waiters ops in
              let waitersₗ := <[op.(operation۰id) := waiter]> waitersₗ in
              FutureOps consistent 𝑣 waitersₗ waitersₚ
          end
      end.

    Record future۰segments۰result := FutureSegs
      { future۰segments۰val : val
      ; future۰segments۰valₛ : val
      ; future۰segments۰waitersₗ : gmap identifier waiter
      ; future۰segments۰waitersₚ : gmap identifier waiter
      }.
    Add Printing Constructor future۰segments۰result.
    #[local] Fixpoint future۰segments 𝑣 g 𝑣ₛ gₛ waiters segs :=
      match segs with
      | [] =>
          FutureSegs 𝑣 𝑣ₛ ∅ waiters
      | seg :: segs =>
          if decide (gₛ < seg.(segment۰gen) ≤ g) then
            let 'FutureOps consistent 𝑣 waitersₗ_seg waiters := future۰operations 𝑣 waiters seg.(segment۰ops) in
            if decide (
              consistent = Consistent ∧
              ( 𝑣 = seg.(segment۰val)
              ∨ Exists (λ op, op.(operation۰val) = seg.(segment۰val)) seg.(segment۰ops)
              )
            ) then
              let 𝑣ₛ := seg.(segment۰val) in
              let gₛ := seg.(segment۰gen) in
              let 'FutureSegs 𝑣 𝑣ₛ waitersₗ waiters := future۰segments 𝑣 g 𝑣ₛ gₛ waiters segs in
              let waitersₗ := waitersₗ_seg ∪ waitersₗ in
              FutureSegs 𝑣 𝑣ₛ waitersₗ waiters
            else
              FutureSegs 𝑣 𝑣ₛ waitersₗ_seg waiters
          else
            FutureSegs 𝑣 𝑣ₛ ∅ waiters
      end.
    #[local] Definition future۰segments' 𝑣 g 𝑣ₛ gₛ v waiters segs :=
      match segs with
      | [] =>
          FutureSegs v 𝑣ₛ ∅ waiters
      | seg :: _ =>
          if decide (gₛ < seg.(segment۰gen) ≤ g) then
            future۰segments 𝑣 g 𝑣ₛ gₛ waiters segs
          else
            FutureSegs v 𝑣ₛ ∅ waiters
      end.

    #[local] Definition waiters۰posts γ waiters : iProp Σ :=
      [∗ map] _ ↦ waiter ∈ waiters,
        ∃ P,
        saved_prop waiter.(waiter۰post) P ∗
        ▷ P.

    #[local] Definition waiter۰au γ ι waiter P : iProp Σ :=
      AU <{
        ∃∃ v,
        model₁ γ v
      }> @ ⊤ ∖ ↑ι, ∅ <{
        model₁ γ waiter.(waiter۰val)
      , COMM
        P
      }>.
    #[local] Definition waiters۰aus γ ι waiters : iProp Σ :=
      [∗ map] _ ↦ waiter ∈ waiters,
        ∃ P,
        saved_prop waiter.(waiter۰post) P ∗
        waiter۰au γ ι waiter P.

    #[local] Definition future۰stable γ ι 𝑣 𝑣ₛ v vₛ waiters : iProp Σ :=
      ⌜𝑣 = v⌝ ∗
      ⌜vₛ = v⌝ ∗
      ⌜𝑣ₛ = v⌝ ∗
      waiters۰aus γ ι waiters.
    #[local] Instance : CustomIpat "future۰stable" :=
      " ( ->
        & ->
        & ->
        & Hwaiters_aus
        )
      ".
    #[local] Definition future۰unstable γ ι 𝑣 g 𝑣ₛ gₛ v waiters tr : iProp Σ :=
      let 'FutureSegs 𝑣' 𝑣ₛ' waitersₗ waitersₚ := future۰segments' 𝑣 g 𝑣ₛ gₛ v waiters tr.(trace۰segs) in
      ⌜𝑣 = 𝑣'⌝ ∗
      ⌜𝑣ₛ = 𝑣ₛ'⌝ ∗
      waiters۰posts γ waitersₗ ∗
      waiters۰aus γ ι waitersₚ.
    #[local] Instance : CustomIpat "future۰unstable" :=
      " ( ->
        & ->
        & Hwaiters_posts
        & Hwaiters_aus
        )
      ".
    #[local] Definition future γ ι 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr :=
      if decide (gₛ = g) then
        future۰stable γ ι 𝑣 𝑣ₛ v vₛ waiters
      else
        future۰unstable γ ι 𝑣 g 𝑣ₛ gₛ v waiters tr.

    #[local] Definition inv۰inner t γ ι : iProp Σ :=
      ∃ 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr,
      t.[value] ↦ 𝑣 ∗
      t.[gen] ↦ #g ∗
      t.[snapshot] ↦ (𝑣ₛ, #gₛ) ∗
      model₂ γ v ∗
      scanner₂ γ vₛ g ∗
      generation۰auth γ g ∗
      snapshot۰auth γ gₛ ∗
      ⌜gₛ ≤ g⌝ ∗
      waiters۰auth γ waiters ∗
      prophet۰model γ tr ∗
      future γ ι 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr.
    #[local] Instance : CustomIpat "inv۰inner" :=
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
      inv ι (inv۰inner t γ ι).
    Definition svar۰inv t γ ι : iProp Σ :=
      t.[proph] ↦□ #γ.(svar۰name۰prophet) ∗
      inv' t γ ι.
    #[local] Instance : CustomIpat "inv" :=
      " ( #Ht_proph
        & #Hinv
        )
      ".

    Definition svar۰model :=
      model₁.

    Definition svar۰scanner γ dq vₛ : iProp Σ :=
      ∃ g,
      scanner₁ γ dq vₛ g.
    #[local] Instance : CustomIpat "scanner" :=
      " ( %g{}
        & Hscanner₁{_{}}
        )
      ".

    #[global] Instance svar۰modelｰtimeless γ v :
      Timeless (svar۰model γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance svar۰scannerｰtimeless γ dq vₛ :
      Timeless (svar۰scanner γ dq vₛ).
    Proof.
      apply _.
    Qed.

    #[global] Instance svar۰inv۰persistent t γ ι :
      Persistent (svar۰inv t γ ι).
    Proof.
      apply _.
    Qed.
    #[global] Instance svar۰scanner۰persistent γ vₛ :
      Persistent (svar۰scanner γ DfracDiscarded vₛ).
    Proof.
      apply _.
    Qed.

    #[global] Instance svar۰scannerｰfractional γ vₛ :
      Fractional (λ q, svar۰scanner γ (DfracOwn q) vₛ).
    Proof.
      intros q1 q2.
      iSplit.
      - iIntros "(:scanner)".
        iDestruct "Hscanner₁" as "($ & $)".
      - iIntros "((:scanner =1) & (:scanner =2))".
        iDestruct (twins۰twin₁ｰcombineｰL with "Hscanner₁_1 Hscanner₁_2") as "(% & $)".
    Qed.
    #[global] Instance svar۰scannerｰas_fractional γ q vₛ :
      AsFractional (svar۰scanner γ (DfracOwn q) vₛ) (λ q, svar۰scanner γ (DfracOwn q) vₛ) q.
    Proof.
      split; [done | apply _].
    Qed.

    #[local] Lemma trace۰of_prophecies'ｰsegsｰprefix tr segs ops prophs :
      tr = trace۰of_prophecies' segs ops prophs →
      segs `prefix_of` tr.(trace۰segs).
    Proof.
      move: segs ops. induction prophs as [| [v g | id v] prophs IH] => segs ops /= Htr.
      - naive_solver.
      - eauto using prefix_app_l.
      - naive_solver.
    Qed.
    #[local] Lemma trace۰of_prophecies'ｰdecompose segs₀ ops prophs :
      trace۰of_prophecies' segs₀ ops prophs =
        let tr := trace۰of_prophecies prophs in
        match tr.(trace۰segs) with
        | [] =>
            Trace segs₀ (ops ++ tr.(trace۰ops))
        | seg :: segs =>
            trace۰set_segs (segs₀ ++ segment۰update_ops ((++) ops) seg :: segs) tr
        end.
    Proof.
      simpl.
      move: segs₀ ops. induction prophs as [| [v g | id v] prophs IH] => segs₀ ops; cbn.
      - rewrite right_id //.
      - rewrite !{}IH.
        destruct (trace۰of_prophecies prophs).(trace۰segs) as [| seg' segs'] => /=.
        + apply traceｰeqｰalt => /=. split. 2: done.
          rewrite /segment۰update_ops right_id //.
        + apply traceｰeqｰalt => /=. split. 2: done.
          rewrite -assoc /=.
          rewrite /segment۰update_ops right_id //.
      - rewrite !{}IH.
        destruct (trace۰of_prophecies prophs).(trace۰segs) as [| seg' segs'] => /=.
        + rewrite -assoc //.
        + rewrite trace۰set_segsｰcompose segment۰update_opsｰcompose.
          do 3 f_equal.
          apply segment۰update_opsｰcongruence => ops'.
          rewrite -assoc //.
    Qed.
    #[local] Lemma trace۰of_prophecies'ｰdecompose' segs prophs :
      trace۰of_prophecies' segs [] prophs = trace۰update_segs ((++) segs) $ trace۰of_prophecies prophs.
    Proof.
      rewrite trace۰of_prophecies'ｰdecompose /=.
      destruct (trace۰of_prophecies prophs).(trace۰segs) as [| seg segs'] eqn:Htr_segs.
      all: apply traceｰeqｰalt => /=.
      all: split; last done.
      - rewrite Htr_segs right_id //.
      - rewrite segment۰update_opsｰid // Htr_segs //.
    Qed.
    #[local] Lemma trace۰of_prophecies'ｰappｰsegs tr segs1 segs2 ops prophs :
      tr = trace۰of_prophecies' segs2 ops prophs →
      trace۰of_prophecies' (segs1 ++ segs2) ops prophs = trace۰update_segs ((++) segs1) tr.
    Proof.
      move: segs2 ops. induction prophs as [| [v g | id v] prophs IH] => segs2 ops /= Htr.
      - naive_solver.
      - rewrite -assoc. auto.
      - naive_solver.
    Qed.
    #[local] Lemma trace۰of_prophecies'ｰemptyｰsegs₁ tr segs ops prophs :
      tr = trace۰of_prophecies' segs ops prophs →
      tr.(trace۰segs) = [] →
      segs = [].
    Proof.
      intros Hsegs%trace۰of_prophecies'ｰsegsｰprefix Htr_segs.
      rewrite Htr_segs in Hsegs.
      apply prefix_nil_inv => //.
    Qed.
    #[local] Lemma trace۰of_prophecies'ｰemptyｰsegs₂ tr segs ops1 ops2 prophs :
      tr = trace۰of_prophecies' segs ops2 prophs →
      tr.(trace۰segs) = [] →
      trace۰of_prophecies' segs (ops1 ++ ops2) prophs = Trace [] (ops1 ++ tr.(trace۰ops)).
    Proof.
      move: ops2. induction prophs as [| [v g | id v] prophs IH] => ops2 /= Htr Htr_segs.
      - naive_solver.
      - apply trace۰of_prophecies'ｰemptyｰsegs₁, appｰnotｰnil in Htr as []; auto.
      - rewrite -assoc. auto.
    Qed.
    #[local] Lemma trace۰of_prophecies'ｰemptyｰsegs₃ tr segs ops prophs :
      tr = trace۰of_prophecies' segs ops prophs →
      tr.(trace۰segs) = [] →
        ∃ ops',
        tr.(trace۰ops) = ops ++ ops' ∧
        trace۰of_prophecies prophs = Trace [] ops'.
    Proof.
      move: ops. induction prophs as [| [v g | id v] prophs IH] => ops /= Htr Htr_segs; cbn.
      - exists []. rewrite right_id.
        naive_solver.
      - apply trace۰of_prophecies'ｰemptyｰsegs₁, appｰnotｰnil in Htr as []; auto.
      - apply IH in Htr as (ops' & Htr_ops & Htr). 2: done.
        exists (Operation id v :: ops'). split.
        + rewrite -assoc // in Htr_ops.
        + rewrite -(app_nil_r [_]) (trace۰of_prophecies'ｰemptyｰsegs₂ (Trace [] ops')) //.
    Qed.
    #[local] Lemma trace۰of_prophecies'ｰnonemptyｰsegs tr ops prophs seg segs :
      tr = trace۰of_prophecies' [] ops prophs →
      tr.(trace۰segs) = seg :: segs →
        ∃ seg',
        seg = segment۰update_ops ((++) ops) seg' ∧
        trace۰of_prophecies prophs = trace۰set_segs (seg' :: segs) tr.
    Proof.
      move: ops. induction prophs as [| [v g | id v] prophs IH] => ops /= Htr Htr_segs; cbn.
      - naive_solver.
      - odestruct (trace۰of_prophecies'ｰsegsｰprefix tr) as (segs_ & Htr_segs_). 1: done.
        rewrite Htr_segs /= in Htr_segs_. injection Htr_segs_ as [= -> <-].
        exists (Segment [] v g). split.
        + rewrite /segment۰update_ops right_id //.
        + rewrite !trace۰of_prophecies'ｰdecompose' in Htr |- *.
          naive_solver.
      - apply IH in Htr as (seg' & -> & Hprophs). 2: done.
        exists (segment۰update_ops (cons $ Operation id v) seg'). split.
        + rewrite segment۰update_opsｰcompose.
          apply segment۰update_opsｰcongruence => ops'.
          rewrite -assoc //.
        + rewrite trace۰of_prophecies'ｰdecompose Hprophs //.
    Qed.

    #[local] Lemma trace۰of_propheciesｰProphecyForward v g prophs :
      trace۰of_prophecies (ProphecyForward v g :: prophs) = trace۰update_segs (cons $ Segment [] v g) $ trace۰of_prophecies prophs.
    Proof.
      cbn.
      rewrite -(app_nil_r [_]) (trace۰of_prophecies'ｰappｰsegs (trace۰of_prophecies prophs)) //.
    Qed.
    #[local] Lemma trace۰of_propheciesｰProphecySetｰemptyｰsegs {tr} id v prophs :
      tr = trace۰of_prophecies (ProphecySet id v :: prophs) →
      tr.(trace۰segs) = [] →
        ∃ ops,
        tr.(trace۰ops) = Operation id v :: ops ∧
        trace۰of_prophecies prophs = trace۰set_ops ops $ trace۰of_prophecies $ ProphecySet id v :: prophs.
    Proof.
      cbn.
      intros Htr Htr_segs.
      pose proof Htr as (ops & Htr_ops & ->)%trace۰of_prophecies'ｰemptyｰsegs₃. 2: done.
      exists ops. split.
      - done.
      - apply traceｰreconstruct; naive_solver.
    Qed.
    #[local] Lemma trace۰of_propheciesｰProphecySetｰnonemptyｰsegs {tr} id v prophs seg segs :
      tr = trace۰of_prophecies (ProphecySet id v :: prophs) →
      tr.(trace۰segs) = seg :: segs →
        ∃ seg',
        seg = segment۰update_ops (cons $ Operation id v) seg' ∧
        trace۰of_prophecies prophs = trace۰set_segs (seg' :: segs) tr.
    Proof.
      cbn.
      apply trace۰of_prophecies'ｰnonemptyｰsegs.
    Qed.

    Opaque trace۰of_prophecies.

    #[local] Lemma wpｰproph E :
      {{{
        True
      }}}
        Proph @ E
      {{{
        pid tr
      , RET #pid;
        prophet۰model' pid tr
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰apply (prophet_typedｰwpｰproph prophet with "[//]") as (pid prophs) "Hprophet_model".
      iApply "HΦ".
      iExists prophs. iFrameSteps.
    Qed.

    #[local] Lemma wpｰresolve e γ v tr E Φ :
      Atomic e →
      to_val e = None →
      prophet۰model γ tr -∗
      WP e @ E {{ w,
        ∃ oproph,
        ⌜prophet.(prophet_typed۰of_val) w v = Some oproph⌝ ∗
        match oproph with
        | None =>
            prophet۰model γ tr -∗
            Φ w
        | Some (ProphecyForward v g) =>
            ⌜head tr.(trace۰segs) = Some $ Segment [] v g⌝ -∗
            prophet۰model γ (trace۰update_segs tail tr) -∗
            Φ w
        | Some (ProphecySet id v) =>
            match tr.(trace۰segs) with
            | [] =>
                ⌜head tr.(trace۰ops) = Some $ Operation id v⌝ -∗
                prophet۰model γ (trace۰update_ops tail tr) -∗
                Φ w
            | seg :: segs =>
                ⌜head seg.(segment۰ops) = Some $ Operation id v⌝ -∗
                prophet۰model γ (trace۰set_segs (segment۰update_ops tail seg :: segs) tr) -∗
                Φ w
            end
        end
      }} -∗
      WP Resolve e #γ.(svar۰name۰prophet) v @ E {{ Φ }}.
    Proof.
      iIntros "% % (:prophet۰model) HΦ".

      wp۰apply (prophet_typedｰwpｰresolve prophet with "[$Hprophet_model]"). 1: done.
      wp۰apply (wpｰwand with "HΦ") as "%w (%oproph & -> & HΦ)".
      destruct oproph as [proph |]. 2: iSteps.
      iStep. iIntros "/= %prophs' -> Hprophet_model".
      destruct proph as [v' g | id v'].
      - iEval (rewrite trace۰of_propheciesｰProphecyForward /=) in "HΦ".
        iSteps. iPureIntro.
        rewrite trace۰update_segsｰcompose trace۰update_segsｰid //.
      - destruct (trace۰of_prophecies $ _ :: _) as [segs ops] eqn:Hprophs => /=.
        destruct segs as [| seg segs].
        + opose proof* (trace۰of_propheciesｰProphecySetｰemptyｰsegs id v' prophs') as (ops' & Htr_ops & Hprophs'). 1,2: done.
          simp.
          iSteps. iPureIntro.
          rewrite Hprophs' Hprophs //.
        + opose proof* (trace۰of_propheciesｰProphecySetｰnonemptyｰsegs id v' prophs') as (seg' & -> & Hprophs'). 1,2: done.
          iSteps. iPureIntro.
          rewrite segment۰update_opsｰcompose segment۰update_opsｰid //.
    Qed.

    Opaque prophet۰model'.

    #[local] Lemma modelｰalloc v :
      ⊢ |==>
        ∃ γ_model,
        model₁' γ_model v ∗
        model₂' γ_model v.
    Proof.
      apply twinsｰalloc'.
    Qed.
    #[local] Lemma model₁ｰexclusive γ v1 v2 :
      model₁ γ v1 -∗
      model₁ γ v2 -∗
      False.
    Proof.
      apply twins۰twin₁ｰexclusive.
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
    #[local] Lemma scanner₁ｰexclusive γ vₛ1 g1 dq2 vₛ2 g2 :
      scanner₁ γ Own vₛ1 g1 -∗
      scanner₁ γ dq2 vₛ2 g2 -∗
      False.
    Proof.
      apply twins۰twin₁ｰexclusive.
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
      iIntros "H1 H2".
      iDestruct (twinsｰagreeｰL with "H1 H2") as %[= -> ->].
      iApply (twinsｰupdate with "H1 H2").
    Qed.
    #[local] Lemma scannerｰupdateｰval {γ vₛ1 g1 vₛ2 g2} vₛ :
      scanner₁ γ Own vₛ1 g1 -∗
      scanner₂ γ vₛ2 g2 ==∗
        scanner₁ γ Own vₛ g1 ∗
        scanner₂ γ vₛ g2.
    Proof.
      iIntros "H1 H2".
      iDestruct (scannerｰagree with "H1 H2") as %(-> & ->).
      iApply (scannerｰupdate with "H1 H2").
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
      generation۰auth γ ˖g.
    Proof.
      apply auth_nat_maxｰupdate. 1: lia.
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

    #[local] Lemma waitersｰalloc :
      ⊢ |==>
        ∃ γ_waiters,
        waiters۰auth' γ_waiters ∅.
    Proof.
      iMod ghost_map_alloc as "(%γ_waiters & $ & _)".
      iApply big_sepS_empty => //.
    Qed.

    Opaque waiters۰auth'.

    #[local] Lemma genｰspecｰscanner t γ ι dq vₛ g :
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

      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
      iSplitR "Hscanner₁ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma svar٠makeｰspec ι v :
      {{{
        True
      }}}
        svar٠make v
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        svar۰inv t γ ι ∗
        svar۰model γ v ∗
        svar۰scanner γ Own v
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰apply+ (wpｰproph with "[//]") as (pid tr) "Hprophet_model".
      wp۰block t as "Hmeta" "Ht_value Ht_gen Ht_snapshot #Ht_proph".

      iMod (modelｰalloc v) as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iMod (scannerｰalloc v) as "(%γ_scanner & Hscanner₁ & Hscanner₂)".
      iMod generationｰalloc as "(%γ_generation & Hgeneration_auth)".
      iMod snapshotｰalloc as "(%γ_snapshot & Hsnapshot_auth)".
      iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

      pose γ :=
        {|svar۰name۰prophet := pid
        ; svar۰name۰model := γ_model
        ; svar۰name۰scanner := γ_scanner
        ; svar۰name۰generation := γ_generation
        ; svar۰name۰snapshot := γ_snapshot
        ; svar۰name۰waiters := γ_waiters
        |}.

      iApply ("HΦ" $! t γ).
      iFrameStep.
      iApply inv_alloc.
      iFrameSteps.
    Qed.

    (* Lemma svar٠getｰspec t γ ι : *)
    (*   <<< *)
    (*     svar۰inv t γ ι *)
    (*   | ∀∀ v, *)
    (*     svar۰model γ v *)
    (*   >>> *)
    (*     svar٠get #t @ ↑ι *)
    (*   <<< *)
    (*     svar۰model γ v *)
    (*   | RET v; *)
    (*     True *)
    (*   >>>. *)
    (* Proof. *)
    (* Admitted. *)

    Lemma svar٠setｰspec t γ ι v :
      <<<
        svar۰inv t γ ι
      | ∀∀ v',
        svar۰model γ v'
      >>>
        svar٠set #t v @ ↑ι
      <<<
        svar۰model γ v
      | RET ();
        True
      >>>.
    Proof.
    Admitted.

    #[local] Definition click۰au γ ι Φ : iProp Σ :=
      AU <{
        ∃∃ v,
        model₁ γ v
      }> @ ⊤ ∖ ↑ι, ∅ <{
        model₁ γ v
      , COMM
        Φ v
      }>.

    #[local] Lemma future۰operationsｰlinearize {γ ι 𝑣 v waiters ops} consistent 𝑣' waitersₗ waitersₚ Φ :
      future۰operations 𝑣 waiters ops = FutureOps consistent 𝑣' waitersₗ waitersₚ →
      waiters۰aus γ ι waiters -∗
      model₂ γ v -∗
      click۰au γ ι Φ ={⊤}=∗
        ∃ v vₛ,
        waiters۰posts γ waitersₗ ∗
        waiters۰aus γ ι waitersₚ ∗
        model₂ γ v ∗
        Φ vₛ.
    Proof.
      iIntros "%Hops Hwaiters_aus Hmodel₂ Hclick_au".
      destruct ops as [| op ops].
      all: simpl in Hops.

      - injection Hops as [= <- <- <- <-].
        iMod "Hclick_au" as "(%v_ & Hmodel₁ & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
        iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "Hmodel₁") as "HΦ".
        iFrameSteps.

      - case_match eqn:Hwaiters_lookup.

        + admit.

        + admit.
    Admitted.

    #[local] Lemma future۰segmentsｰend 𝑣 g 𝑣ₛ gₛ waiters segs :
      g = gₛ →
      future۰segments 𝑣 g 𝑣ₛ gₛ waiters segs = FutureSegs 𝑣 𝑣ₛ ∅ waiters.
    Proof.
      intros <-.
      destruct segs as [| seg segs] => /=.
      - done.
      - rewrite decide_False //. 1: lia.
    Qed.
    #[local] Lemma future۰segmentsｰdestabilize {γ ι 𝑣 𝑣ₛ gₛ v waiters segs} 𝑣' 𝑣ₛ' waitersₗ waitersₚ Φ :
      future۰segments 𝑣 ˖gₛ 𝑣ₛ gₛ waiters segs = FutureSegs 𝑣' 𝑣ₛ' waitersₗ waitersₚ →
      waiters۰aus γ ι waiters -∗
      model₂ γ v -∗
      click۰au γ ι Φ ={⊤}=∗
        ∃ v vₛ,
        waiters۰posts γ waitersₗ ∗
        waiters۰aus γ ι waitersₚ ∗
        model₂ γ v ∗
        Φ vₛ.
    Proof.
      iIntros "%Hsegs Hwaiters_aus Hmodel₂ Hclick_au".
      destruct segs as [| seg segs].
      all: simpl in Hsegs.

      - injection Hsegs as [= <- <- <- <-].
        iMod "Hclick_au" as "(%v_ & Hmodel₁ & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
        iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "Hmodel₁") as "HΦ".
        iFrameSteps.

      - case_decide.

        + destruct (future۰operations 𝑣 waiters seg.(segment۰ops)) as [consistent 𝑣1 waitersₗ1 waitersₚ1] eqn:Hops.
          iMod (future۰operationsｰlinearize with "Hwaiters_aus Hmodel₂ Hclick_au") as "(%v1 & %vₛ1 & Hwaiters_posts & Hwaiters_aus & Hmodel₁ & HΦ)". 1: done.
          case_decide as [_ | _].

          * rewrite future۰segmentsｰend in Hsegs. 1: lia.
            rewrite right_id in Hsegs.
            injection Hsegs as [= <- <- <- <-].
            iFrameSteps.

          * injection Hsegs as [= <- <- <- <-].
            iFrameSteps.

        + injection Hsegs as [= <- <- <- <-].
          iMod "Hclick_au" as "(%v_ & Hmodel₁ & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "Hmodel₁") as "HΦ".
          iFrameSteps.
    Qed.

    #[local] Lemma future۰stableｰdestabilize {γ ι 𝑣 𝑣ₛ v vₛ waiters} gₛ tr Φ :
      future۰stable γ ι 𝑣 𝑣ₛ v vₛ waiters -∗
      model₂ γ v -∗
      click۰au γ ι Φ ={⊤}=∗
        ∃ v vₛ,
        future γ ι 𝑣 ˖gₛ 𝑣ₛ gₛ v vₛ waiters tr ∗
        model₂ γ v ∗
        Φ vₛ.
    Proof.
      iIntros "(:future۰stable) Hmodel₂ Hclick_au".

      iEval (rewrite /future /future۰unstable /future۰segments').
      iEval (setoid_rewrite decide_False; last done).
      destruct tr.(trace۰segs) as [| seg segs].

      - iMod "Hclick_au" as "(%v_ & Hmodel₁ & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
        iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "Hmodel₁") as "HΦ".
        iFrameSteps.

      - case_decide as Hseg.

        + admit.

        + iMod "Hclick_au" as "(%v_ & Hmodel₁ & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "Hmodel₁") as "HΦ".
          iFrameSteps.
    Admitted.

    #[local] Lemma futureｰdestabilize γ ι 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr Φ :
      future γ ι 𝑣 g 𝑣ₛ gₛ v vₛ waiters tr -∗
      model₂ γ v -∗
      click۰au γ ι Φ ==∗
        ∃ v vₛ,
        future γ ι 𝑣 ˖g 𝑣ₛ gₛ v vₛ waiters tr ∗
        model₂ γ v ∗
        Φ vₛ.
    Proof.
      iIntros "Hfuture Hmodel₂ Hclick_au".

      iEval (rewrite /future) in "Hfuture".
      case_decide as [-> | Hgₛ].

      - iDestruct "Hfuture" as "(:future۰stable)".
        admit.

      - admit.
    Admitted.

    Lemma svar٠clickｰspec t γ ι vₛ :
      <<<
        svar۰inv t γ ι ∗
        svar۰scanner γ Own vₛ
      | ∀∀ v,
        svar۰model γ v
      >>>
        svar٠click #t @ ↑ι
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
      iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as "(<- & <-)".
      iMod (futureｰdestabilize with "Hfuture Hmodel₂ HΦ") as "(%v' & %vₛ' & Hfuture & Hmodel₂ & HΦ)".
      iMod (scannerｰupdate vₛ' ˖g with "Hscanner₁ Hscanner₂") as "(Hscanner₁ & Hscanner₂)".
      iMod (generationｰupdate with "Hgeneration_auth") as "Hgeneration_auth".
      iSplitR "Hscanner₁ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma svar٠observeｰspec t γ ι dq vₛ :
      {{{
        svar۰inv t γ ι ∗
        svar۰scanner γ dq vₛ
      }}}
        svar٠observe #t
      {{{
        RET vₛ;
        svar۰scanner γ dq vₛ
      }}}.
    Proof.
    Admitted.
  End svar_G.

  #[global] Opaque svar۰inv.
  #[global] Opaque svar۰model.
  #[global] Opaque svar۰scanner.
End base.

Require zoo_saturn.svar__opaque.

Section svar_G.
  Context `{svar_G : SvarG Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition svar۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.svar۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition svar۰model t v : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.svar۰model γ v.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition svar۰scanner t dq vₛ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.svar۰scanner γ dq vₛ.
  #[local] Instance : CustomIpat "scanner" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hscanner{_{}}
      )
    ".

  #[global] Instance svar۰modelｰtimeless t v :
    Timeless (svar۰model t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance svar۰scannerｰtimeless t dq vₛ :
    Timeless (svar۰scanner t dq vₛ).
  Proof.
    apply _.
  Qed.

  #[global] Instance svar۰invｰpersistent t ι :
    Persistent (svar۰inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance svar۰scannerｰpersistent t vₛ :
    Persistent (svar۰scanner t DfracDiscarded vₛ).
  Proof.
    apply _.
  Qed.

  #[global] Instance svar۰scannerｰfractional t vₛ :
    Fractional (λ q, svar۰scanner t (DfracOwn q) vₛ).
  Proof.
    intros q1 q2.
    iSplit.
    - iIntros "(:scanner)".
      iDestruct "Hscanner" as "($ & $)".
      iSteps.
    - iIntros "((:scanner =1) & (:scanner =2))". simp.
      iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
      iCombine "Hscanner_1 Hscanner_2" as "$".
      iSteps.
  Qed.
  #[global] Instance svar۰scannerｰas_fractional t q vₛ :
    AsFractional (svar۰scanner t (DfracOwn q) vₛ) (λ q, svar۰scanner t (DfracOwn q) vₛ) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma svar٠makeｰspec ι v :
    {{{
      True
    }}}
      svar٠make v
    {{{
      t
    , RET t;
      svar۰inv t ι ∗
      svar۰model t v ∗
      svar۰scanner t Own v
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.svar٠makeｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel & Hscanner)".
    iMod (metaｰset γ with "Hmeta"). 1: done.
    iSteps.
  Qed.

  (* Lemma svar٠getｰspec t ι : *)
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

  Lemma svar٠setｰspec t ι v :
    <<<
      svar۰inv t ι
    | ∀∀ v',
      svar۰model t v'
    >>>
      svar٠set t v @ ↑ι
    <<<
      svar۰model t v
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.svar٠setｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"). 1: done. iIntros "%v' (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma svar٠clickｰspec t ι vₛ :
    <<<
      svar۰inv t ι ∗
      svar۰scanner t Own vₛ
    | ∀∀ v,
      svar۰model t v
    >>>
      svar٠click t @ ↑ι
    <<<
      svar۰model t v
    | RET ();
      svar۰scanner t Own v
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:scanner =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.svar٠clickｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"). 1: done. iIntros "%v (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma svar٠observeｰspec t ι dq vₛ :
    {{{
      svar۰inv t ι ∗
      svar۰scanner t dq vₛ
    }}}
      svar٠observe t
    {{{
      RET vₛ;
      svar۰scanner t dq vₛ
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:scanner =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.svar٠observeｰspec with "[$]").
    iSteps.
  Qed.
End svar_G.

#[global] Opaque svar۰inv.
#[global] Opaque svar۰model.
#[global] Opaque svar۰scanner.
