From Stdlib Require Import List Bool Arith Lia Classical_Prop Wf_nat.
Import ListNotations.

From PositionAutomata.Automata Require Import EpsilonNFA.

(** A verified semantic implementation of the paper's unified [Count]
    operation.  The visited list records the states already used in the
    current epsilon segment.  A counted trace must end in [targets] and must
    have no fresh epsilon-only continuation to another target.  Consequently
    [targets = final states] gives accepting-maximal ambiguity, a singleton
    target gives reach ambiguity, and [targets = all states] gives leaves. *)

Section AmbiguityCount.
  Context {A : Type}.

  Lemma forallb_ext_in :
    forall {B : Type} (f g : B -> bool) xs,
      (forall x, In x xs -> f x = g x) ->
      forallb f xs = forallb g xs.
  Proof.
    intros B f g xs Hext.
    induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - rewrite Hext by (simpl; auto).
      rewrite IH.
      + reflexivity.
      + intros y Hy. apply Hext. simpl. auto.
  Qed.

  Lemma forallb_true_filter_negb_empty :
    forall {B : Type} (p : B -> bool) xs,
      forallb p xs = true ->
      filter (fun x => negb (p x)) xs = [].
  Proof.
    intros B p xs Hforall.
    induction xs as [| x xs IH]; simpl in *.
    - reflexivity.
    - apply andb_true_iff in Hforall as [Hx Hxs].
      rewrite Hx. simpl. now apply IH.
  Qed.

  Definition enfa_strict_epsilon_closure_states_from
      (m : @finite_enfa A)
      (visited : list (enfa_state (fenfa_base m)))
      (st : started_trace m)
      : list (enfa_state (fenfa_base m)) :=
    let seen := epsilon_suffix_states m visited (snd st) in
    let q := started_end st in
    enfa_epsilon_closure_fuel
      m (enfa_epsilon_transition_bound m)
      seen
      (filter
         (fun q' => negb (state_inb m q' seen))
         (enfa_step (fenfa_base m) q None)).

  Definition enfa_target_maximal_epsilon_simpleb
      (m : @finite_enfa A)
      (visited targets : list (enfa_state (fenfa_base m)))
      (st : started_trace m) : bool :=
    forallb
      (fun q => negb (state_inb m q targets))
      (enfa_strict_epsilon_closure_states_from m visited st).

  Definition enfa_count_traceb
      (m : @finite_enfa A)
      (visited targets : list (enfa_state (fenfa_base m)))
      (st : started_trace m) : bool :=
    (state_inb m (started_end st) targets &&
       epsilon_simpleb_from m visited (snd st)) &&
    enfa_target_maximal_epsilon_simpleb m visited targets st.

  Definition enfa_count
      (m : @finite_enfa A)
      (q : enfa_state (fenfa_base m))
      (w : list A)
      (visited targets : list (enfa_state (fenfa_base m))) : nat :=
    length
      (filter
         (enfa_count_traceb m visited targets)
         (started_traces_from_start m q w)).

  Lemma enfa_epsilon_closure_fuel_fresh_from_initial_seen :
    forall (m : @finite_enfa A) fuel seen todo q,
      In q (enfa_epsilon_closure_fuel m fuel seen todo) ->
      state_inb m q seen = false.
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros seen todo q Hin.
    - simpl in Hin. contradiction.
    - destruct todo as [| r todo].
      + simpl in Hin. contradiction.
      + simpl in Hin.
        destruct (state_inb m r seen) eqn:Hr_seen.
        * eapply IH; eauto.
        * simpl in Hin.
          destruct Hin as [Heq | Hin].
          -- subst q. exact Hr_seen.
          -- pose proof
               (IH (r :: seen)
                  (enfa_step (fenfa_base m) r None ++ todo)
                  q Hin) as Hfresh.
             apply (state_inb_false_of_incl m q seen (r :: seen)).
             { intros x Hx. simpl. auto. }
             exact Hfresh.
  Qed.

  Lemma enfa_target_maximal_singleton_endpoint :
    forall (m : @finite_enfa A) s t q,
      trace_end s t = q ->
      enfa_target_maximal_epsilon_simpleb m [s] [q] (s, t) = true.
  Proof.
    intros m s t q Hend.
    unfold enfa_target_maximal_epsilon_simpleb.
    apply forallb_forall.
    intros x Hx.
    apply negb_true_iff.
    unfold enfa_strict_epsilon_closure_states_from in Hx.
    set (seen := epsilon_suffix_states m [s] t) in *.
    assert (Hfresh : state_inb m x seen = false).
    {
      eapply enfa_epsilon_closure_fuel_fresh_from_initial_seen.
      exact Hx.
    }
    eapply state_inb_false_of_incl with (ys := seen).
    - intros y Hy.
      simpl in Hy. destruct Hy as [Hy | []]. subst y.
      unfold seen. rewrite <- Hend.
      apply trace_end_in_epsilon_suffix_states.
      simpl. auto.
    - exact Hfresh.
  Qed.

  Lemma enfa_strict_epsilon_closure_states_from_singleton :
    forall (m : @finite_enfa A) s t,
      enfa_strict_epsilon_closure_states_from m [s] (s, t) =
      enfa_strict_epsilon_closure_states m (s, t).
  Proof.
    reflexivity.
  Qed.

  Lemma enfa_target_maximal_all_states_iff :
    forall (m : @finite_enfa A) st,
      finite_enfa_wf m ->
      In (started_end st) (fenfa_states m) ->
      (enfa_target_maximal_epsilon_simpleb
         m [fst st] (fenfa_states m) st = true <->
       maximal_epsilon_simpleb m st = true).
  Proof.
    intros m [s t] Hwf Hend.
    unfold enfa_target_maximal_epsilon_simpleb,
      enfa_strict_epsilon_closure_states_from,
      maximal_epsilon_simpleb.
    simpl in *.
    set (seen := epsilon_suffix_states m [s] t).
    set (q := trace_end s t).
    set (todo :=
      filter
        (fun q' => negb (state_inb m q' seen))
        (enfa_step (fenfa_base m) q None)).
    change (In (trace_end s t) (fenfa_states m)) in Hend.
    change
      (forallb
         (fun r => negb (state_inb m r (fenfa_states m)))
         (enfa_epsilon_closure_fuel
            m (enfa_epsilon_transition_bound m) seen todo) = true <->
       forallb (fun r => state_inb m r seen)
         (enfa_step (fenfa_base m) q None) = true).
    split; intro Htarget.
    - apply filter_negb_empty_forallb.
      change (todo = []).
      destruct todo as [| r todo'] eqn:Htodo; [reflexivity |].
      exfalso.
      assert (Hr_todo : In r (r :: todo')) by (simpl; auto).
      rewrite <- Htodo in Hr_todo.
      unfold todo in Hr_todo.
      apply filter_In in Hr_todo as [Hr_step Hr_fresh].
      apply negb_true_iff in Hr_fresh.
      assert (Hq_state : In q (fenfa_states m)).
      { unfold q. exact Hend. }
      assert (Hr_state : In r (fenfa_states m)).
      {
        eapply (fenfa_steps_in_states m Hwf).
        - exact Hq_state.
        - exact Hr_step.
      }
      assert (Htodo_states :
        forall x, In x (r :: todo') -> In x (fenfa_states m)).
      {
        intros x Hx.
        rewrite <- Htodo in Hx.
        unfold todo in Hx.
        apply filter_In in Hx as [Hx _].
        eapply (fenfa_steps_in_states m Hwf).
        - exact Hq_state.
        - exact Hx.
      }
      assert (Hreachable :
        enfa_fresh_epsilon_reachable m seen (r :: todo') r).
      {
        apply Fresh_epsilon_todo.
        - simpl. auto.
        - exact Hr_fresh.
      }
      assert (Hbound :
        enfa_epsilon_closure_work_bound m seen (r :: todo') <=
        enfa_epsilon_transition_bound m).
      {
        rewrite <- Htodo.
        unfold todo, seen, q.
        exact
          (enfa_strict_epsilon_closure_work_bound_le_transition_bound
             m (s, t) Hwf Hend).
      }
      assert (Hr_closure :
        In r
          (enfa_epsilon_closure_fuel
             m (enfa_epsilon_transition_bound m) seen (r :: todo'))).
      {
        eapply enfa_epsilon_closure_fuel_complete.
        - exact Hwf.
        - exact Htodo_states.
        - exact Hreachable.
        - exact Hbound.
      }
      rewrite forallb_forall in Htarget.
      specialize (Htarget r Hr_closure).
      apply negb_true_iff in Htarget.
      rewrite (state_inb_In_true m r (fenfa_states m) Hr_state) in Htarget.
      discriminate.
    - assert (Htodo : todo = []).
      {
        unfold todo.
        now apply forallb_true_filter_negb_empty.
      }
      rewrite Htodo.
      rewrite enfa_epsilon_closure_fuel_empty_todo.
      reflexivity.
  Qed.

  Theorem enfa_count_final_states_eq_da_prime :
    forall (m : @finite_enfa A) s w,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_count m s w [s] (enfa_final_states m) =
      enfa_da_prime_word m w.
  Proof.
    intros m s w Hwf Hstart.
    rewrite enfa_da_prime_word_flat by exact Hwf.
    unfold enfa_count, started_traces.
    rewrite Hstart. simpl. rewrite app_nil_r.
    apply f_equal.
    apply filter_ext_in.
    intros [s0 t] Hin.
    unfold started_traces_from_start in Hin.
    apply in_map_iff in Hin as [t0 [Heq Htrace]].
    inversion Heq; subst s0 t0; clear Heq.
    unfold enfa_count_traceb,
      enfa_target_maximal_epsilon_simpleb,
      enfa_accepting_maximal_started_traceb,
      enfa_accepting_maximal_epsilon_simpleb,
      epsilon_simpleb.
    rewrite enfa_strict_epsilon_closure_states_from_singleton.
    assert (Hs : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
    }
    assert (Hvalid :
      valid_trace m s t (trace_end s t)).
    {
      apply traces_from_fuel_valid in Htrace.
      exact (proj1 Htrace).
    }
    assert (Hend : In (trace_end s t) (fenfa_states m)).
    { eapply finite_enfa_wf_valid_trace_end_in_states; eauto. }
    rewrite state_inb_final_states by exact Hend.
    unfold accepted_traceb, started_end. simpl.
    f_equal.
    apply forallb_ext_in.
    intros q Hq.
    rewrite state_inb_final_states.
    - reflexivity.
    - eapply enfa_strict_epsilon_closure_states_in_states; eauto.
      unfold started_end. simpl. exact Hend.
  Qed.

  Theorem enfa_count_singleton_eq_dra_prime :
    forall (m : @finite_enfa A) s w q,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_count m s w [s] [q] = enfa_dra_prime_at m w q.
  Proof.
    intros m s w q Hwf Hstart.
    unfold enfa_count, enfa_dra_prime_at, started_traces.
    rewrite Hstart. simpl. rewrite app_nil_r.
    apply f_equal.
    apply filter_ext_in.
    intros [s0 t] Hin.
    unfold started_traces_from_start in Hin.
    apply in_map_iff in Hin as [t0 [Heq _]].
    inversion Heq; subst s0 t0; clear Heq.
    unfold enfa_count_traceb, ends_inb, started_end,
      epsilon_simpleb. simpl.
    destruct (fenfa_state_eqb m (trace_end s t) q) eqn:Hend;
      simpl.
    - apply fenfa_state_eqb_sound in Hend.
      rewrite enfa_target_maximal_singleton_endpoint by exact Hend.
      now destruct (epsilon_simpleb_from m [s] t).
    - reflexivity.
  Qed.

  Theorem enfa_count_all_states_eq_leaf_prime :
    forall (m : @finite_enfa A) s w,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_count m s w [s] (fenfa_states m) =
      enfa_leaf_prime_word m w.
  Proof.
    intros m s w Hwf Hstart.
    rewrite enfa_leaf_prime_word_flat by exact Hwf.
    unfold enfa_count, started_traces.
    rewrite Hstart. simpl. rewrite app_nil_r.
    apply f_equal.
    apply filter_ext_in.
    intros [s0 t] Hin.
    unfold started_traces_from_start in Hin.
    apply in_map_iff in Hin as [t0 [Heq Htrace]].
    inversion Heq; subst s0 t0; clear Heq.
    assert (Hs : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
    }
    apply traces_from_fuel_valid in Htrace as [Hvalid _].
    assert (Hend : In (trace_end s t) (fenfa_states m)).
    { eapply finite_enfa_wf_valid_trace_end_in_states; eauto. }
    unfold enfa_count_traceb, enfa_leaf_prime_started_traceb,
      epsilon_simpleb, started_end. simpl.
    rewrite (state_inb_In_true m (trace_end s t) (fenfa_states m) Hend).
    simpl.
    destruct (epsilon_simpleb_from m [s] t) eqn:Hsimple; simpl.
    - destruct
        (enfa_target_maximal_epsilon_simpleb
           m [s] (fenfa_states m) (s, t)) eqn:Htarget;
        destruct (maximal_epsilon_simpleb m (s, t)) eqn:Hmax;
        auto.
      + exfalso.
        pose proof
          (proj1
             (enfa_target_maximal_all_states_iff m (s, t) Hwf Hend)
             Htarget) as Hcontradiction.
        simpl in Hcontradiction.
        congruence.
      + exfalso.
        pose proof
          (proj2
             (enfa_target_maximal_all_states_iff m (s, t) Hwf Hend)
             Hmax) as Hcontradiction.
        simpl in Hcontradiction.
        congruence.
    - reflexivity.
  Qed.

  Theorem enfa_count_correct :
    forall (m : @finite_enfa A) s w q,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_count m s w [s] (enfa_final_states m) =
        enfa_da_prime_word m w /\
      enfa_count m s w [s] [q] = enfa_dra_prime_at m w q /\
      enfa_count m s w [s] (fenfa_states m) =
        enfa_leaf_prime_word m w.
  Proof.
    intros m s w q Hwf Hstart.
    repeat split.
    - now apply enfa_count_final_states_eq_da_prime.
    - now apply enfa_count_singleton_eq_dra_prime.
    - now apply enfa_count_all_states_eq_leaf_prime.
  Qed.

  Definition enfa_da_prime_degree
      (m : @finite_enfa A) (degree : nat) : Prop :=
    (forall w, enfa_da_prime_word m w <= degree) /\
    forall upper,
      (forall w, enfa_da_prime_word m w <= upper) ->
      degree <= upper.

  Definition enfa_dra_prime_at_degree
      (m : @finite_enfa A)
      (q : enfa_state (fenfa_base m))
      (degree : nat) : Prop :=
    (forall w, enfa_dra_prime_at m w q <= degree) /\
    forall upper,
      (forall w, enfa_dra_prime_at m w q <= upper) ->
      degree <= upper.

  Definition enfa_da_prime_degree_le
      (m : @finite_enfa A) (bound : nat) : Prop :=
    forall w, enfa_da_prime_word m w <= bound.

  Definition enfa_dra_prime_degree_le
      (m : @finite_enfa A) (bound : nat) : Prop :=
    forall w q,
      In q (fenfa_states m) ->
      enfa_dra_prime_at m w q <= bound.

  Definition enfa_leaf_prime_degree_le
      (m : @finite_enfa A) (bound : nat) : Prop :=
    forall w, enfa_leaf_prime_word m w <= bound.

  Definition enfa_dra_prime_degree
      (m : @finite_enfa A) (degree : nat) : Prop :=
    enfa_dra_prime_degree_le m degree /\
    forall upper,
      enfa_dra_prime_degree_le m upper ->
      degree <= upper.

  Definition enfa_leaf_prime_degree
      (m : @finite_enfa A) (degree : nat) : Prop :=
    (forall w, enfa_leaf_prime_word m w <= degree) /\
    forall upper,
      (forall w, enfa_leaf_prime_word m w <= upper) ->
      degree <= upper.

  (** A total supremum representation: a degree is either the least finite
      upper bound or is unbounded.  This is the direct formal counterpart of
      the paper's automaton-wide suprema. *)
  Inductive enfa_degree_value : Type :=
  | EnfaFiniteDegree : nat -> enfa_degree_value
  | EnfaInfiniteDegree : enfa_degree_value.

  Definition enfa_da_prime_extended_degree
      (m : @finite_enfa A) (degree : enfa_degree_value) : Prop :=
    match degree with
    | EnfaFiniteDegree n => enfa_da_prime_degree m n
    | EnfaInfiniteDegree =>
        forall bound, exists w, bound < enfa_da_prime_word m w
    end.

  Definition enfa_dra_prime_extended_degree
      (m : @finite_enfa A) (degree : enfa_degree_value) : Prop :=
    match degree with
    | EnfaFiniteDegree n => enfa_dra_prime_degree m n
    | EnfaInfiniteDegree =>
        forall bound, exists w q,
          In q (fenfa_states m) /\
          bound < enfa_dra_prime_at m w q
    end.

  Definition enfa_leaf_prime_extended_degree
      (m : @finite_enfa A) (degree : enfa_degree_value) : Prop :=
    match degree with
    | EnfaFiniteDegree n => enfa_leaf_prime_degree m n
    | EnfaInfiniteDegree =>
        forall bound, exists w, bound < enfa_leaf_prime_word m w
    end.

  Definition enfa_degree_value_le_one (degree : enfa_degree_value) : Prop :=
    match degree with
    | EnfaFiniteDegree n => n <= 1
    | EnfaInfiniteDegree => False
    end.

  Lemma nat_word_measure_extended_degree_exists :
    forall (measure : list A -> nat),
      exists degree,
        match degree with
        | EnfaFiniteDegree n =>
            (forall w, measure w <= n) /\
            forall upper,
              (forall w, measure w <= upper) -> n <= upper
        | EnfaInfiniteDegree =>
            forall bound, exists w, bound < measure w
        end.
  Proof.
    intro measure.
    destruct
      (classic (exists bound, forall w, measure w <= bound))
      as [Hbounded | Hunbounded].
    - destruct
        (dec_inh_nat_subset_has_unique_least_element
           (fun bound => forall w, measure w <= bound)
           (fun bound => classic (forall w, measure w <= bound))
           Hbounded)
        as [least [[Hleast Hleast_minimal] _]].
      exists (EnfaFiniteDegree least). split.
      + exact Hleast.
      + exact Hleast_minimal.
    - exists EnfaInfiniteDegree.
      intro bound.
      destruct (classic (exists w, bound < measure w)) as [H | Hnone].
      + exact H.
      + exfalso. apply Hunbounded. exists bound.
        intro w.
        destruct (le_gt_dec (measure w) bound); auto.
        exfalso. apply Hnone. exists w. lia.
  Qed.

  Theorem enfa_da_prime_extended_degree_exists :
    forall (m : @finite_enfa A),
      exists degree, enfa_da_prime_extended_degree m degree.
  Proof.
    intro m.
    exact
      (nat_word_measure_extended_degree_exists
         (fun w => enfa_da_prime_word m w)).
  Qed.

  Theorem enfa_leaf_prime_extended_degree_exists :
    forall (m : @finite_enfa A),
      exists degree, enfa_leaf_prime_extended_degree m degree.
  Proof.
    intro m.
    exact
      (nat_word_measure_extended_degree_exists
         (fun w => enfa_leaf_prime_word m w)).
  Qed.

  Theorem enfa_dra_prime_extended_degree_exists :
    forall (m : @finite_enfa A),
      exists degree, enfa_dra_prime_extended_degree m degree.
  Proof.
    intro m.
    destruct
      (classic (exists bound, enfa_dra_prime_degree_le m bound))
      as [Hbounded | Hunbounded].
    - destruct
        (dec_inh_nat_subset_has_unique_least_element
           (enfa_dra_prime_degree_le m)
           (fun bound => classic (enfa_dra_prime_degree_le m bound))
           Hbounded)
        as [least [[Hleast Hleast_minimal] _]].
      exists (EnfaFiniteDegree least). split.
      + exact Hleast.
      + exact Hleast_minimal.
    - exists EnfaInfiniteDegree.
      intro bound.
      destruct
        (classic
           (exists w q,
              In q (fenfa_states m) /\
              bound < enfa_dra_prime_at m w q))
        as [H | Hnone].
      + exact H.
      + exfalso. apply Hunbounded. exists bound.
        intros w q Hq.
        destruct (le_gt_dec (enfa_dra_prime_at m w q) bound); auto.
        exfalso. apply Hnone. exists w, q. auto.
  Qed.

  Theorem enfa_da_prime_extended_degree_unique :
    forall (m : @finite_enfa A) d1 d2,
      enfa_da_prime_extended_degree m d1 ->
      enfa_da_prime_extended_degree m d2 ->
      d1 = d2.
  Proof.
    intros m [n1 |] [n2 |]; simpl; intros H1 H2.
    - destruct H1 as [Hu1 Hl1]. destruct H2 as [Hu2 Hl2].
      f_equal. specialize (Hl1 n2 Hu2). specialize (Hl2 n1 Hu1). lia.
    - destruct H1 as [Hu1 _].
      destruct (H2 n1) as [w Hw]. specialize (Hu1 w). lia.
    - destruct H2 as [Hu2 _].
      destruct (H1 n2) as [w Hw]. specialize (Hu2 w). lia.
    - reflexivity.
  Qed.

  Theorem enfa_dra_prime_extended_degree_unique :
    forall (m : @finite_enfa A) d1 d2,
      enfa_dra_prime_extended_degree m d1 ->
      enfa_dra_prime_extended_degree m d2 ->
      d1 = d2.
  Proof.
    intros m [n1 |] [n2 |]; simpl; intros H1 H2.
    - destruct H1 as [Hu1 Hl1]. destruct H2 as [Hu2 Hl2].
      f_equal. specialize (Hl1 n2 Hu2). specialize (Hl2 n1 Hu1). lia.
    - destruct H1 as [Hu1 _].
      destruct (H2 n1) as [w [q [Hq Hw]]].
      specialize (Hu1 w q Hq). lia.
    - destruct H2 as [Hu2 _].
      destruct (H1 n2) as [w [q [Hq Hw]]].
      specialize (Hu2 w q Hq). lia.
    - reflexivity.
  Qed.

  Theorem enfa_leaf_prime_extended_degree_unique :
    forall (m : @finite_enfa A) d1 d2,
      enfa_leaf_prime_extended_degree m d1 ->
      enfa_leaf_prime_extended_degree m d2 ->
      d1 = d2.
  Proof.
    intros m [n1 |] [n2 |]; simpl; intros H1 H2.
    - destruct H1 as [Hu1 Hl1]. destruct H2 as [Hu2 Hl2].
      f_equal. specialize (Hl1 n2 Hu2). specialize (Hl2 n1 Hu1). lia.
    - destruct H1 as [Hu1 _].
      destruct (H2 n1) as [w Hw]. specialize (Hu1 w). lia.
    - destruct H2 as [Hu2 _].
      destruct (H1 n2) as [w Hw]. specialize (Hu2 w). lia.
    - reflexivity.
  Qed.

  Theorem enfa_ufa_iff_extended_degree_le_one :
    forall (m : @finite_enfa A),
      enfa_UFA m <->
      exists degree,
        enfa_da_prime_extended_degree m degree /\
        enfa_degree_value_le_one degree.
  Proof.
    intro m. split.
    - intro Hufa.
      destruct (enfa_da_prime_extended_degree_exists m) as [d Hd].
      exists d. split; auto.
      destruct d as [n |]; simpl in *.
      + destruct Hd as [_ Hleast]. apply Hleast. exact Hufa.
      + destruct (Hd 1) as [w Hw]. specialize (Hufa w). lia.
    - intros [[n |] [Hd Hle]]; simpl in *.
      + intros w. destruct Hd as [Hupper _]. specialize (Hupper w). lia.
      + contradiction.
  Qed.

  Theorem enfa_reachufa_iff_extended_degree_le_one :
    forall (m : @finite_enfa A),
      enfa_ReachUFA m <->
      exists degree,
        enfa_dra_prime_extended_degree m degree /\
        enfa_degree_value_le_one degree.
  Proof.
    intro m. split.
    - intro Hreach.
      destruct (enfa_dra_prime_extended_degree_exists m) as [d Hd].
      exists d. split; auto.
      destruct d as [n |]; simpl in *.
      + destruct Hd as [_ Hleast]. apply Hleast. exact Hreach.
      + destruct (Hd 1) as [w [q [Hq Hw]]].
        specialize (Hreach w q Hq). lia.
    - intros [[n |] [Hd Hle]]; simpl in *.
      + intros w q Hq. destruct Hd as [Hupper _].
        specialize (Hupper w q Hq). lia.
      + contradiction.
  Qed.

  Theorem enfa_leafufa_iff_extended_degree_le_one :
    forall (m : @finite_enfa A),
      enfa_LeafUFA m <->
      exists degree,
        enfa_leaf_prime_extended_degree m degree /\
        enfa_degree_value_le_one degree.
  Proof.
    intro m. split.
    - intro Hleaf.
      destruct (enfa_leaf_prime_extended_degree_exists m) as [d Hd].
      exists d. split; auto.
      destruct d as [n |]; simpl in *.
      + destruct Hd as [_ Hleast]. apply Hleast. exact Hleaf.
      + destruct (Hd 1) as [w Hw]. specialize (Hleaf w). lia.
    - intros [[n |] [Hd Hle]]; simpl in *.
      + intros w. destruct Hd as [Hupper _]. specialize (Hupper w). lia.
      + contradiction.
  Qed.

  Theorem enfa_ufa_iff_da_prime_degree_le_one :
    forall (m : @finite_enfa A),
      enfa_UFA m <-> enfa_da_prime_degree_le m 1.
  Proof.
    reflexivity.
  Qed.

  Theorem enfa_reachufa_iff_dra_prime_degree_le_one :
    forall (m : @finite_enfa A),
      enfa_ReachUFA m <-> enfa_dra_prime_degree_le m 1.
  Proof.
    reflexivity.
  Qed.

  Theorem enfa_leafufa_iff_leaf_prime_degree_le_one :
    forall (m : @finite_enfa A),
      enfa_LeafUFA m <-> enfa_leaf_prime_degree_le m 1.
  Proof.
    reflexivity.
  Qed.

  Lemma nat_word_measure_finite_degree_has_witness :
    forall (measure : list A -> nat) degree,
      (forall w, measure w <= degree) ->
      (forall upper, (forall w, measure w <= upper) -> degree <= upper) ->
      exists witness, measure witness = degree.
  Proof.
    intros measure [| degree] Hupper Hleast.
    - exists []. specialize (Hupper []). lia.
    - destruct
        (classic (exists witness, measure witness = S degree))
        as [Hwitness | Hnone].
      + exact Hwitness.
      + exfalso.
        assert (Hsmaller : forall w, measure w <= degree).
        {
          intro w.
          specialize (Hupper w).
          assert (Hneq : measure w <> S degree).
          { intro Heq. apply Hnone. now exists w. }
          lia.
        }
        specialize (Hleast degree Hsmaller). lia.
  Qed.

  Theorem enfa_finite_da_prime_degree_has_witness :
    forall (m : @finite_enfa A) degree,
      enfa_da_prime_degree m degree ->
      exists witness, enfa_da_prime_word m witness = degree.
  Proof.
    intros m degree [Hupper Hleast].
    eapply nat_word_measure_finite_degree_has_witness; eauto.
  Qed.

  Theorem enfa_finite_dra_prime_at_degree_has_witness :
    forall (m : @finite_enfa A) q degree,
      enfa_dra_prime_at_degree m q degree ->
      exists witness, enfa_dra_prime_at m witness q = degree.
  Proof.
    intros m q degree [Hupper Hleast].
    eapply nat_word_measure_finite_degree_has_witness; eauto.
  Qed.

  Theorem enfa_finite_dra_prime_degree_has_witness :
    forall (m : @finite_enfa A) s degree,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_dra_prime_degree m degree ->
      exists q witness,
        In q (fenfa_states m) /\
        enfa_dra_prime_at m witness q = degree.
  Proof.
    intros m s [| degree] Hwf Hstart [Hupper Hleast].
    - exists s, []. split.
      + eapply fenfa_starts_in_states; eauto.
        rewrite Hstart. simpl. auto.
      + specialize (Hupper [] s).
        assert (Hs : In s (fenfa_states m)).
        { eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto. }
        specialize (Hupper Hs). lia.
    - destruct
        (classic
           (exists q witness,
              In q (fenfa_states m) /\
              enfa_dra_prime_at m witness q = S degree))
        as [Hwitness | Hnone].
      + exact Hwitness.
      + exfalso.
        assert (Hsmaller : enfa_dra_prime_degree_le m degree).
        {
          intros w q Hq.
          specialize (Hupper w q Hq).
          assert (Hneq : enfa_dra_prime_at m w q <> S degree).
          {
            intro Heq. apply Hnone.
            exists q, w. auto.
          }
          lia.
        }
        specialize (Hleast degree Hsmaller). lia.
  Qed.

  Theorem enfa_finite_leaf_prime_degree_has_witness :
    forall (m : @finite_enfa A) degree,
      enfa_leaf_prime_degree m degree ->
      exists witness, enfa_leaf_prime_word m witness = degree.
  Proof.
    intros m degree [Hupper Hleast].
    eapply nat_word_measure_finite_degree_has_witness; eauto.
  Qed.

  Theorem enfa_finite_da_prime_degree_attained_within_a_length_bound :
    forall (m : @finite_enfa A) degree,
      enfa_da_prime_degree m degree ->
      exists bound witness,
        length witness <= bound /\
        enfa_da_prime_word m witness = degree /\
        forall x, length x <= bound ->
          enfa_da_prime_word m x <= degree.
  Proof.
    intros m degree Hdegree.
    destruct Hdegree as [Hupper Hleast].
    destruct
      (enfa_finite_da_prime_degree_has_witness
         m degree (conj Hupper Hleast))
      as [witness Hwitness].
    exists (length witness), witness.
    repeat split; auto.
  Qed.

  Theorem enfa_finite_dra_prime_at_degree_attained_within_a_length_bound :
    forall (m : @finite_enfa A) q degree,
      enfa_dra_prime_at_degree m q degree ->
      exists bound witness,
        length witness <= bound /\
        enfa_dra_prime_at m witness q = degree /\
        forall x, length x <= bound ->
          enfa_dra_prime_at m x q <= degree.
  Proof.
    intros m q degree Hdegree.
    destruct Hdegree as [Hupper Hleast].
    destruct
      (enfa_finite_dra_prime_at_degree_has_witness
         m q degree (conj Hupper Hleast))
      as [witness Hwitness].
    exists (length witness), witness.
    repeat split; auto.
  Qed.

  Theorem enfa_finite_dra_prime_degree_attained_within_a_length_bound :
    forall (m : @finite_enfa A) s degree,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_dra_prime_degree m degree ->
      exists bound q witness,
        In q (fenfa_states m) /\
        length witness <= bound /\
        enfa_dra_prime_at m witness q = degree /\
        forall x r,
          length x <= bound ->
          In r (fenfa_states m) ->
          enfa_dra_prime_at m x r <= degree.
  Proof.
    intros m s degree Hwf Hstart Hdegree.
    destruct Hdegree as [Hupper Hleast].
    destruct
      (enfa_finite_dra_prime_degree_has_witness
         m s degree Hwf Hstart (conj Hupper Hleast))
      as [q [witness [Hq Hwitness]]].
    exists (length witness), q, witness.
    repeat split; auto.
  Qed.

  Theorem enfa_finite_leaf_prime_degree_attained_within_a_length_bound :
    forall (m : @finite_enfa A) degree,
      enfa_leaf_prime_degree m degree ->
      exists bound witness,
        length witness <= bound /\
        enfa_leaf_prime_word m witness = degree /\
        forall x, length x <= bound ->
          enfa_leaf_prime_word m x <= degree.
  Proof.
    intros m degree Hdegree.
    destruct Hdegree as [Hupper Hleast].
    destruct
      (enfa_finite_leaf_prime_degree_has_witness
         m degree (conj Hupper Hleast))
      as [witness Hwitness].
    exists (length witness), witness.
    repeat split; auto.
  Qed.
End AmbiguityCount.

Arguments enfa_strict_epsilon_closure_states_from {A} _ _ _.
Arguments enfa_target_maximal_epsilon_simpleb {A} _ _ _ _.
Arguments enfa_count_traceb {A} _ _ _ _.
Arguments enfa_count {A} _ _ _ _ _.
Arguments enfa_da_prime_degree {A} _ _.
Arguments enfa_dra_prime_at_degree {A} _ _ _.
Arguments enfa_leaf_prime_degree {A} _ _.
Arguments enfa_da_prime_degree_le {A} _ _.
Arguments enfa_dra_prime_degree_le {A} _ _.
Arguments enfa_leaf_prime_degree_le {A} _ _.
Arguments enfa_dra_prime_degree {A} _ _.
Arguments enfa_da_prime_extended_degree {A} _ _.
Arguments enfa_dra_prime_extended_degree {A} _ _.
Arguments enfa_leaf_prime_extended_degree {A} _ _.
