From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Ambiguity Require Import DegreeofAmbiguity.

(** Section 4, Definitions 4--6: epsilon NFAs and the three
    ambiguity measures.

    The paper phrases the measures as cardinalities of trace sets.  This file
    keeps the same objects but makes the finite sets executable by enumerating
    all traces up to the standard epsilon-simple bound. *)

Section EpsilonNFA.
  Context {A : Type}.

  Record enfa : Type := {
    enfa_state : Type;
    enfa_start : list enfa_state;
    enfa_final : enfa_state -> bool;
    enfa_step : enfa_state -> option A -> list enfa_state
  }.

  Record finite_enfa : Type := {
    fenfa_base :> enfa;
    fenfa_states : list (enfa_state fenfa_base);
    fenfa_alphabet : list A;
    fenfa_state_eqb :
      enfa_state fenfa_base -> enfa_state fenfa_base -> bool;
    fenfa_state_eqb_sound :
      forall x y, fenfa_state_eqb x y = true -> x = y;
    fenfa_state_eqb_complete :
      forall x y, x = y -> fenfa_state_eqb x y = true
  }.

  Record finite_enfa_wf (m : finite_enfa) : Prop := {
    fenfa_states_nodup :
      NoDup (fenfa_states m);
    fenfa_starts_in_states :
      forall q,
        In q (enfa_start (fenfa_base m)) ->
        In q (fenfa_states m);
    fenfa_steps_in_states :
      forall q a q',
        In q (fenfa_states m) ->
        In q' (enfa_step (fenfa_base m) q a) ->
        In q' (fenfa_states m);
    fenfa_steps_in_alphabet :
      forall q a q',
        In q (fenfa_states m) ->
        In q' (enfa_step (fenfa_base m) q (Some a)) ->
        In a (fenfa_alphabet m);
    fenfa_step_targets_nodup :
      forall q a,
        In q (fenfa_states m) ->
        NoDup (enfa_step (fenfa_base m) q a)
  }.

  Definition enfa_edge (m : finite_enfa) : Type :=
    ((enfa_state (fenfa_base m) * option A) *
       enfa_state (fenfa_base m))%type.

  Definition enfa_trace (m : finite_enfa) : Type :=
    list (enfa_edge m).

  Definition edge_src {m : finite_enfa} (e : enfa_edge m) :=
    fst (fst e).

  Definition edge_label {m : finite_enfa} (e : enfa_edge m) :=
    snd (fst e).

  Definition edge_dst {m : finite_enfa} (e : enfa_edge m) :=
    snd e.

  Fixpoint trace_word {m : finite_enfa} (t : enfa_trace m) : list A :=
    match t with
    | [] => []
    | e :: t' =>
        match edge_label e with
        | None => trace_word t'
        | Some a => a :: trace_word t'
        end
    end.

  Fixpoint trace_end {m : finite_enfa}
      (p : enfa_state (fenfa_base m))
      (t : enfa_trace m) : enfa_state (fenfa_base m) :=
    match t with
    | [] => p
    | e :: t' => trace_end (edge_dst e) t'
    end.

  Inductive valid_trace (m : finite_enfa)
      : enfa_state (fenfa_base m) -> enfa_trace m ->
        enfa_state (fenfa_base m) -> Prop :=
  | Valid_nil :
      forall q, valid_trace m q [] q
  | Valid_cons :
      forall p l q r t,
        In q (enfa_step (fenfa_base m) p l) ->
        valid_trace m q t r ->
        valid_trace m p (((p, l), q) :: t) r.

  Definition started_trace (m : finite_enfa) : Type :=
    (enfa_state (fenfa_base m) * enfa_trace m)%type.

  Definition started_end {m : finite_enfa} (st : started_trace m) :=
    trace_end (fst st) (snd st).

  Definition started_word {m : finite_enfa} (st : started_trace m) :=
    trace_word (snd st).

  (* All traces from state [p] that read [w] within [fuel] edges. *)
  Fixpoint traces_from_fuel
      (m : finite_enfa)
      (fuel : nat)
      (p : enfa_state (fenfa_base m))
      (w : list A) : list (enfa_trace m) :=
    let stop :=
      match w with
      | [] => [[]]
      | _ :: _ => []
      end in
    match fuel with
    | O => stop
    | S fuel' =>
        stop ++
        concat
          (map
             (fun q =>
                map
                  (fun t => ((p, None), q) :: t)
                  (traces_from_fuel m fuel' q w))
             (enfa_step (fenfa_base m) p None)) ++
        match w with
        | [] => []
        | a :: w' =>
            concat
              (map
                 (fun q =>
                    map
                      (fun t => ((p, Some a), q) :: t)
                      (traces_from_fuel m fuel' q w'))
                 (enfa_step (fenfa_base m) p (Some a)))
        end
    end.

  Definition enfa_trace_bound (m : finite_enfa) (w : list A) : nat :=
    (length w + 1) * S (length (fenfa_states m)) + length w.

  Definition started_traces (m : finite_enfa) (w : list A)
      : list (started_trace m) :=
    concat
      (map
         (fun s =>
            map (fun t => (s, t))
              (traces_from_fuel m (enfa_trace_bound m w) s w))
         (enfa_start (fenfa_base m))).

  Definition started_traces_from_start
      (m : finite_enfa)
      (s : enfa_state (fenfa_base m))
      (w : list A) : list (started_trace m) :=
    map (fun t => (s, t))
      (traces_from_fuel m (enfa_trace_bound m w) s w).

  Definition state_inb
      (m : finite_enfa)
      (q : enfa_state (fenfa_base m))
      (xs : list (enfa_state (fenfa_base m))) : bool :=
    existsb (fenfa_state_eqb m q) xs.

  Fixpoint enfa_epsilon_closure_fuel
      (m : finite_enfa)
      (fuel : nat)
      (seen todo : list (enfa_state (fenfa_base m)))
      : list (enfa_state (fenfa_base m)) :=
    match fuel with
    | O => []
    | S fuel' =>
        match todo with
        | [] => []
        | q :: todo' =>
            if state_inb m q seen then
              enfa_epsilon_closure_fuel m fuel' seen todo'
            else
              q ::
              enfa_epsilon_closure_fuel
                m fuel' (q :: seen)
                (enfa_step (fenfa_base m) q None ++ todo')
        end
    end.

  Lemma enfa_epsilon_closure_fuel_empty_todo :
    forall (m : finite_enfa) fuel seen,
      enfa_epsilon_closure_fuel m fuel seen [] = [].
  Proof.
    intros m fuel.
    destruct fuel; reflexivity.
  Qed.

  Lemma enfa_epsilon_closure_fuel_in_states :
    forall (m : finite_enfa) fuel seen todo q,
      finite_enfa_wf m ->
      (forall r, In r todo -> In r (fenfa_states m)) ->
      In q (enfa_epsilon_closure_fuel m fuel seen todo) ->
      In q (fenfa_states m).
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros seen todo q Hwf Htodo Hin.
    - simpl in Hin. contradiction.
    - simpl in Hin.
      destruct todo as [| r todo']; simpl in Hin.
      + contradiction.
      + destruct (state_inb m r seen) eqn:Hseen.
        * eapply (IH seen todo' q Hwf).
          -- intros x Hx. apply Htodo. simpl. auto.
          -- exact Hin.
        * simpl in Hin.
          destruct Hin as [Hin | Hin].
          -- subst q. apply Htodo. simpl. auto.
          -- eapply (IH
                (r :: seen)
                (enfa_step (fenfa_base m) r None ++ todo')
                q Hwf).
             ++ intros x Hx.
             apply in_app_or in Hx as [Hx | Hx].
                ** eapply fenfa_steps_in_states; eauto.
                apply Htodo. simpl. auto.
                ** apply Htodo. simpl. auto.
             ++ exact Hin.
  Qed.

  Definition enfa_epsilon_transition_bound (m : finite_enfa) : nat :=
    sum_nats
      (map
         (fun q => length (enfa_step (fenfa_base m) q None))
         (fenfa_states m)).

  (* Definition 4 I: decide whether a trace is epsilon-simple. *)
  Fixpoint epsilon_simpleb_from
      (m : finite_enfa)
      (seen : list (enfa_state (fenfa_base m)))
      (t : enfa_trace m) : bool :=
    match t with
    | [] => true
    | e :: t' =>
        match edge_label e with
        | None =>
            negb (state_inb m (edge_dst e) seen)
            && epsilon_simpleb_from m (edge_dst e :: seen) t'
        | Some _ =>
            epsilon_simpleb_from m [edge_dst e] t'
        end
    end.

  Definition epsilon_simpleb (m : finite_enfa) (st : started_trace m) : bool :=
    epsilon_simpleb_from m [fst st] (snd st).

  (* Definition 4 I: states visited by the final epsilon suffix. *)
  Fixpoint epsilon_suffix_states
      (m : finite_enfa)
      (seen : list (enfa_state (fenfa_base m)))
      (t : enfa_trace m) : list (enfa_state (fenfa_base m)) :=
    match t with
    | [] => seen
    | e :: t' =>
        match edge_label e with
        | None => epsilon_suffix_states m (edge_dst e :: seen) t'
        | Some _ => epsilon_suffix_states m [edge_dst e] t'
        end
    end.

  (* Definition 4 I *)
  Definition maximal_epsilon_simpleb
      (m : finite_enfa)
      (st : started_trace m) : bool :=
    let seen := epsilon_suffix_states m [fst st] (snd st) in
    let q := started_end st in
    forallb
      (fun q' => state_inb m q' seen)
      (enfa_step (fenfa_base m) q None).

  Definition enfa_strict_epsilon_closure_states
      (m : finite_enfa)
      (st : started_trace m)
      : list (enfa_state (fenfa_base m)) :=
    let seen := epsilon_suffix_states m [fst st] (snd st) in
    let q := started_end st in
    enfa_epsilon_closure_fuel
      m (enfa_epsilon_transition_bound m)
      seen
      (filter
         (fun q' => negb (state_inb m q' seen))
         (enfa_step (fenfa_base m) q None)).

  Definition enfa_accepting_maximal_epsilon_simpleb
      (m : finite_enfa)
      (st : started_trace m) : bool :=
    forallb
      (fun q => negb (enfa_final (fenfa_base m) q))
      (enfa_strict_epsilon_closure_states m st).

  Lemma enfa_strict_epsilon_closure_states_in_states :
    forall (m : finite_enfa) st q,
      finite_enfa_wf m ->
      In (started_end st) (fenfa_states m) ->
      In q (enfa_strict_epsilon_closure_states m st) ->
      In q (fenfa_states m).
  Proof.
    intros m st q Hwf Hend Hq.
    unfold enfa_strict_epsilon_closure_states in Hq.
    eapply enfa_epsilon_closure_fuel_in_states with
      (seen := epsilon_suffix_states m [fst st] (snd st))
      (todo :=
         filter
           (fun q' => negb (state_inb m q' (epsilon_suffix_states m [fst st] (snd st))))
           (enfa_step (fenfa_base m) (started_end st) None))
      (fuel := enfa_epsilon_transition_bound m).
    - exact Hwf.
    - intros r Hr.
      apply filter_In in Hr as [Hr _].
      eapply fenfa_steps_in_states; eauto.
    - exact Hq.
  Qed.

  Definition ends_inb
      (m : finite_enfa)
      (q : enfa_state (fenfa_base m))
      (st : started_trace m) : bool :=
    fenfa_state_eqb m (started_end st) q.

  Definition accepted_traceb (m : finite_enfa) (st : started_trace m) : bool :=
    enfa_final (fenfa_base m) (started_end st).

  Definition enfa_final_states (m : finite_enfa)
      : list (enfa_state (fenfa_base m)) :=
    filter (enfa_final (fenfa_base m)) (fenfa_states m).

  (* Definition 5 I.i: dra_M(w, q), traces reading [w] and ending at [q]. *)
  Definition enfa_dra_at
      (m : finite_enfa)
      (w : list A)
      (q : enfa_state (fenfa_base m)) : nat :=
    length (filter (ends_inb m q) (started_traces m w)).

  (* Definition 5 I.ii: da_M(w), accepting traces for [w]. *)
  Definition enfa_da_word (m : finite_enfa) (w : list A) : nat :=
    sum_nats (map (enfa_dra_at m w) (enfa_final_states m)).

  (* Definition 5 I.iii: Leaf_M(w), all reach traces over every state. *)
  Definition enfa_leaf_word (m : finite_enfa) (w : list A) : nat :=
    sum_nats (map (enfa_dra_at m w) (fenfa_states m)).

  (* Definition 5 II.ii: dra'_M(w, q), epsilon-simple reach traces. *)
  Definition enfa_dra_prime_at
      (m : finite_enfa)
      (w : list A)
      (q : enfa_state (fenfa_base m)) : nat :=
    length
      (filter
         (fun st => ends_inb m q st && epsilon_simpleb m st)
         (started_traces m w)).

  Definition enfa_dra_prime_between
      (m : finite_enfa)
      (p : enfa_state (fenfa_base m))
      (w : list A)
      (q : enfa_state (fenfa_base m)) : nat :=
    length
      (filter
         (fun st => ends_inb m q st && epsilon_simpleb m st)
         (started_traces_from_start m p w)).

  Definition enfa_reach_fiber_maximal
      (m : finite_enfa)
      (w : list A)
      (q : enfa_state (fenfa_base m))
      (st : started_trace m) : Prop :=
    forall st' u,
      st' = (fst st, snd st ++ u) ->
      In st' (started_traces m w) ->
      ends_inb m q st' = true ->
      epsilon_simpleb m st' = true ->
      trace_word u = [] ->
      st' = st.

  Definition enfa_maximal_simple_reach_count
      (m : finite_enfa)
      (w : list A)
      (q : enfa_state (fenfa_base m)) : nat :=
    length
      (filter
         (fun st =>
            (ends_inb m q st && epsilon_simpleb m st)
            && maximal_epsilon_simpleb m st)
         (started_traces m w)).

  Definition enfa_accepting_maximal_simple_reach_count
      (m : finite_enfa)
      (w : list A)
      (q : enfa_state (fenfa_base m)) : nat :=
    length
      (filter
         (fun st =>
            (ends_inb m q st && epsilon_simpleb m st)
            && enfa_accepting_maximal_epsilon_simpleb m st)
         (started_traces m w)).

  (* Definition 5 II.i: da'_M(w), accepting-maximal epsilon-simple traces. *)
  Definition enfa_da_prime_word (m : finite_enfa) (w : list A) : nat :=
    sum_nats
      (map
         (enfa_accepting_maximal_simple_reach_count m w)
         (enfa_final_states m)).

  (* Definition 5 II.iii: Leaf'_M(w), maximal epsilon-simple leaves. *)
  Definition enfa_leaf_prime_word (m : finite_enfa) (w : list A) : nat :=
    sum_nats
      (map (enfa_maximal_simple_reach_count m w) (fenfa_states m)).

  Definition enfa_rejecting_states (m : finite_enfa)
      : list (enfa_state (fenfa_base m)) :=
    filter (fun q => negb (enfa_final (fenfa_base m) q)) (fenfa_states m).

  Definition enfa_accepting_leaf_prime_word
      (m : finite_enfa) (w : list A) : nat :=
    sum_nats
      (map (enfa_maximal_simple_reach_count m w) (enfa_final_states m)).

  Definition enfa_rejecting_leaf_prime_word
      (m : finite_enfa) (w : list A) : nat :=
    sum_nats
      (map (enfa_maximal_simple_reach_count m w) (enfa_rejecting_states m)).

  Definition enfa_epsilon_free (m : finite_enfa) : Prop :=
    forall q, enfa_step (fenfa_base m) q None = [].

  Definition enfa_single_start (m : finite_enfa) : Prop :=
    length (enfa_start (fenfa_base m)) <= 1.

  Definition enfa_deterministic (m : finite_enfa) : Prop :=
    forall q a,
      In q (fenfa_states m) ->
      length (enfa_step (fenfa_base m) q (Some a)) <= 1.

  Definition enfa_DFA_conditions (m : finite_enfa) : Prop :=
    enfa_epsilon_free m /\
    finite_enfa_wf m /\
    enfa_single_start m /\
    enfa_deterministic m.

  (* Definition 6 I. *)
  Definition enfa_UFA (m : finite_enfa) : Prop :=
    forall w, enfa_da_prime_word m w <= 1.

  (* Definition 6 II. *)
  Definition enfa_ReachUFA (m : finite_enfa) : Prop :=
    forall w q, In q (fenfa_states m) -> enfa_dra_prime_at m w q <= 1.

  Definition enfa_SUFA (m : finite_enfa) : Prop :=
    enfa_epsilon_free m /\ enfa_ReachUFA m.

  Definition enfa_stUFA (m : finite_enfa) : Prop :=
    forall p q w,
      In p (fenfa_states m) ->
      In q (fenfa_states m) ->
      enfa_dra_prime_between m p w q <= 1.

  (* Definition 6 III. *)
  Definition enfa_LeafUFA (m : finite_enfa) : Prop :=
    forall w, enfa_leaf_prime_word m w <= 1.

  Definition enfa_BiUFA (m : finite_enfa) : Prop :=
    forall w,
      enfa_accepting_leaf_prime_word m w +
      enfa_rejecting_leaf_prime_word m w <= 1.

  Lemma sum_nats_filter_partition :
    forall {B : Type} (p : B -> bool) (f : B -> nat) xs,
      sum_nats (map f xs) =
      sum_nats (map f (filter p xs)) +
      sum_nats (map f (filter (fun x => negb (p x)) xs)).
  Proof.
    intros B p f xs.
    induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - destruct (p x); simpl; rewrite IH; lia.
  Qed.

  Theorem enfa_leaf_prime_word_accept_reject_partition :
    forall (m : finite_enfa) w,
      enfa_leaf_prime_word m w =
      enfa_accepting_leaf_prime_word m w +
      enfa_rejecting_leaf_prime_word m w.
  Proof.
    intros m w.
    unfold enfa_leaf_prime_word,
      enfa_accepting_leaf_prime_word,
      enfa_rejecting_leaf_prime_word,
      enfa_final_states,
      enfa_rejecting_states.
    apply sum_nats_filter_partition.
  Qed.

  Theorem enfa_BiUFA_unique_accepting :
    forall (m : finite_enfa) w,
      enfa_BiUFA m ->
      enfa_accepting_leaf_prime_word m w <= 1.
  Proof.
    intros m w Hbi.
    specialize (Hbi w).
    lia.
  Qed.

  Theorem enfa_BiUFA_unique_rejecting :
    forall (m : finite_enfa) w,
      enfa_BiUFA m ->
      enfa_rejecting_leaf_prime_word m w <= 1.
  Proof.
    intros m w Hbi.
    specialize (Hbi w).
    lia.
  Qed.

  Theorem section4_leafufa_iff_biufa :
    forall (m : finite_enfa),
      enfa_LeafUFA m <-> enfa_BiUFA m.
  Proof.
    intros m. split; intros H w.
    - rewrite <- enfa_leaf_prime_word_accept_reject_partition.
      now apply H.
    - rewrite enfa_leaf_prime_word_accept_reject_partition.
      now apply H.
  Qed.

  Definition enfa_accepting_maximal_da_bounded_by_leaf
      (m : finite_enfa) : Prop :=
    forall w, enfa_da_prime_word m w <= enfa_leaf_prime_word m w.

  Definition enfa_accessible
      (m : finite_enfa)
      (q : enfa_state (fenfa_base m)) : Prop :=
    exists w,
      0 < enfa_dra_prime_at m w q.

  Definition enfa_coaccessible
      (m : finite_enfa)
      (q : enfa_state (fenfa_base m)) : Prop :=
    exists w st,
      fst st = q /\
      In st
        (map (fun t => (q, t))
           (traces_from_fuel m (enfa_trace_bound m w) q w)) /\
      accepted_traceb m st = true /\
      epsilon_simpleb m st = true /\
      maximal_epsilon_simpleb m st = true.

  Definition enfa_trim (m : finite_enfa) : Prop :=
    forall q, In q (fenfa_states m) ->
      enfa_accessible m q /\ enfa_coaccessible m q.

  Definition enfa_prime_extendable (m : finite_enfa) : Prop :=
    forall w q,
      In q (fenfa_states m) ->
      exists suffix,
        enfa_dra_prime_at m w q <=
        enfa_da_prime_word m (w ++ suffix).

  Definition enfa_unique_final (m : finite_enfa) : Prop :=
    exists f,
      In f (fenfa_states m) /\
      enfa_final (fenfa_base m) f = true /\
      forall q,
        In q (fenfa_states m) ->
        enfa_final (fenfa_base m) q = true ->
        q = f.

  Definition enfa_unique_terminating_state := enfa_unique_final.

  Definition enfa_MaximalReachUFA (m : finite_enfa) : Prop :=
    forall w q,
      In q (fenfa_states m) ->
      enfa_maximal_simple_reach_count m w q <= 1.

  Definition enfa_reachable_epsilon_simple_prefix
      (m : finite_enfa)
      (st : started_trace m) : Prop :=
    In st (started_traces m (started_word st)) /\
    epsilon_simpleb m st = true.

  Definition enfa_maximal_symbol_extension
      (m : finite_enfa)
      (st : started_trace m)
      (a : A)
      (st' : started_trace m) : Prop :=
    In st' (started_traces m (started_word st ++ [a])) /\
    exists u,
      fst st' = fst st /\
      snd st' = snd st ++ u /\
      trace_word u = [a] /\
      valid_trace m (started_end st) u (started_end st') /\
      epsilon_simpleb m st' = true /\
      maximal_epsilon_simpleb m st' = true.

  Definition enfa_fresh_epsilon_successors
      (m : finite_enfa)
      (st : started_trace m)
      : list (enfa_state (fenfa_base m)) :=
    let seen := epsilon_suffix_states m [fst st] (snd st) in
    filter
      (fun q => negb (state_inb m q seen))
      (enfa_step (fenfa_base m) (started_end st) None).

  Definition enfa_prefix_epsilon_closure_states
      (m : finite_enfa)
      (st : started_trace m)
      : list (enfa_state (fenfa_base m)) :=
    started_end st ::
    enfa_epsilon_closure_fuel
      m (length (fenfa_states m))
      (epsilon_suffix_states m [fst st] (snd st))
      (enfa_fresh_epsilon_successors m st).

  Definition enfa_epsilon_closure_extension
      (m : finite_enfa)
      (st st' : started_trace m) : Prop :=
    In st' (started_traces m (started_word st)) /\
    exists u,
      fst st' = fst st /\
      snd st' = snd st ++ u /\
      trace_word u = [] /\
      valid_trace m (started_end st) u (started_end st') /\
      epsilon_simpleb m st' = true.

  Definition enfa_maximal_epsilon_closure_extension
      (m : finite_enfa)
      (st st' : started_trace m) : Prop :=
    enfa_epsilon_closure_extension m st st' /\
    maximal_epsilon_simpleb m st' = true.

  Definition enfa_fresh_epsilon_branching_le_one
      (m : finite_enfa) : Prop :=
    forall st st1 st2,
      enfa_reachable_epsilon_simple_prefix m st ->
      enfa_maximal_epsilon_closure_extension m st st1 ->
      enfa_maximal_epsilon_closure_extension m st st2 ->
      st1 = st2.

  Definition enfa_epsilon_closure_symbol_branching_le_one
      (m : finite_enfa) : Prop :=
    forall st a st1 st2,
      enfa_reachable_epsilon_simple_prefix m st ->
      enfa_maximal_symbol_extension m st a st1 ->
      enfa_maximal_symbol_extension m st a st2 ->
      st1 = st2.

  Definition enfa_maximal_epsilon_closure_trace_unique
      (m : finite_enfa) : Prop :=
    forall w st1 st2,
      In st1 (started_traces m w) ->
      In st2 (started_traces m w) ->
      epsilon_simpleb m st1 = true ->
      maximal_epsilon_simpleb m st1 = true ->
      epsilon_simpleb m st2 = true ->
      maximal_epsilon_simpleb m st2 = true ->
      st1 = st2.

  Definition enfa_epsilon_closure_branching_deterministic
      (m : finite_enfa) : Prop :=
    enfa_LeafUFA m /\
    enfa_fresh_epsilon_branching_le_one m /\
    enfa_epsilon_closure_symbol_branching_le_one m /\
    enfa_maximal_epsilon_closure_trace_unique m.

  Definition enfa_maximal_epsilon_removed_deterministic
      (m : finite_enfa) : Prop :=
    forall st a st1 st2,
      enfa_reachable_epsilon_simple_prefix m st ->
      enfa_maximal_symbol_extension m st a st1 ->
      enfa_maximal_symbol_extension m st a st2 ->
      st1 = st2.

  Definition LeafUFA_implies_maximal_reach_statement
      (m : finite_enfa) : Prop :=
    enfa_LeafUFA m -> enfa_MaximalReachUFA m.

  Lemma filter_and_length_le_l :
    forall {B : Type} (p q : B -> bool) xs,
      length (filter (fun x => p x && q x) xs) <= length (filter p xs).
  Proof.
    intros B p q xs.
    induction xs as [| x xs IH]; simpl.
    - lia.
    - destruct (p x), (q x); simpl; lia.
  Qed.

  Lemma filter_and3_length_le_l :
    forall {B : Type} (p q r : B -> bool) xs,
      length (filter (fun x => (p x && q x) && r x) xs) <=
      length (filter (fun x => p x && q x) xs).
  Proof.
    intros B p q r xs.
    induction xs as [| x xs IH]; simpl.
    - lia.
    - destruct (p x), (q x), (r x); simpl; lia.
  Qed.

  Lemma enfa_maximal_simple_reach_le_dra_prime :
    forall (m : finite_enfa) w q,
      enfa_maximal_simple_reach_count m w q <=
      enfa_dra_prime_at m w q.
  Proof.
    intros m w q.
    unfold enfa_maximal_simple_reach_count, enfa_dra_prime_at.
    apply filter_and3_length_le_l.
  Qed.

  Lemma enfa_accepting_maximal_simple_reach_le_dra_prime :
    forall (m : finite_enfa) w q,
      enfa_accepting_maximal_simple_reach_count m w q <=
      enfa_dra_prime_at m w q.
  Proof.
    intros m w q.
    unfold enfa_accepting_maximal_simple_reach_count, enfa_dra_prime_at.
    apply filter_and3_length_le_l.
  Qed.

  (* Theorem 3. I. *)
  Theorem section4_theorem3_epsilon_free_leaf_sum_dra :
    forall (m : finite_enfa) w,
      enfa_leaf_word m w =
      sum_nats (map (enfa_dra_at m w) (fenfa_states m)).
  Proof.
    reflexivity.
  Qed.

  (* Theorem 3. II. *)
  Theorem section4_theorem3_prime_leaf_le_sum_dra :
    forall (m : finite_enfa) w,
      enfa_leaf_prime_word m w <=
      sum_nats (map (enfa_dra_prime_at m w) (fenfa_states m)).
  Proof.
    intros m w.
    unfold enfa_leaf_prime_word.
    induction (fenfa_states m) as [| q qs IH]; simpl.
    - lia.
    - pose proof (enfa_maximal_simple_reach_le_dra_prime m w q).
      lia.
  Qed.

  Lemma epsilon_simpleb_from_no_epsilon :
    forall (m : finite_enfa) seen t,
      (forall e, In e t -> exists a, edge_label e = Some a) ->
      epsilon_simpleb_from m seen t = true.
  Proof.
    intros m seen t.
    revert seen.
    induction t as [| e t IH]; intros seen H; simpl.
    - reflexivity.
    - destruct (H e (or_introl eq_refl)) as [a Ha].
      rewrite Ha.
      apply IH.
      intros e' He'. apply H. now right.
  Qed.

  Lemma traces_from_fuel_epsilon_free_no_epsilon :
    forall (m : finite_enfa) fuel p w t,
      enfa_epsilon_free m ->
      In t (traces_from_fuel m fuel p w) ->
      forall e, In e t -> exists a, edge_label e = Some a.
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros p w t Heps Hin e He.
    - simpl in Hin.
      destruct w as [| a w]; simpl in Hin.
      + destruct Hin as [Ht | []]. subst. contradiction.
      + contradiction.
    - simpl in Hin.
      destruct w as [| a w].
      + rewrite Heps in Hin. simpl in Hin.
        destruct Hin as [Ht | []]; subst; contradiction.
      + rewrite Heps in Hin. simpl in Hin.
        apply in_concat in Hin as [ts [Hts Ht]].
        apply in_map_iff in Hts as [q [Hts Hq]].
        subst ts.
        apply in_map_iff in Ht as [t' [Ht Ht']].
        subst t.
        simpl in He.
        destruct He as [He | He].
        * subst e. exists a. reflexivity.
        * eapply IH; eauto.
  Qed.

  (* Epsilon-free automata make every trace maximal. *)
  Lemma maximal_epsilon_simpleb_epsilon_free :
    forall (m : finite_enfa) st,
      enfa_epsilon_free m ->
      maximal_epsilon_simpleb m st = true.
  Proof.
    intros m st Heps.
    unfold maximal_epsilon_simpleb.
    rewrite Heps.
    reflexivity.
  Qed.

  Lemma enfa_accepting_maximal_epsilon_simpleb_epsilon_free :
    forall (m : finite_enfa) st,
      enfa_epsilon_free m ->
      enfa_accepting_maximal_epsilon_simpleb m st = true.
  Proof.
    intros m st Heps.
    unfold enfa_accepting_maximal_epsilon_simpleb,
      enfa_strict_epsilon_closure_states.
    rewrite Heps.
    rewrite enfa_epsilon_closure_fuel_empty_todo.
    reflexivity.
  Qed.

  (* Epsilon-free automata make every started trace epsilon-simple. *)
  Lemma epsilon_simpleb_epsilon_free :
    forall (m : finite_enfa) w st,
      enfa_epsilon_free m ->
      In st (started_traces m w) ->
      epsilon_simpleb m st = true.
  Proof.
    intros m w [s t] Heps Hin.
    unfold started_traces in Hin.
    apply in_concat in Hin as [ts [Hts Ht]].
    apply in_map_iff in Hts as [s' [Hts Hs']].
    subst ts.
    apply in_map_iff in Ht as [t' [Hst Ht']].
    inversion Hst; subst s' t'; clear Hst.
    unfold epsilon_simpleb.
    apply epsilon_simpleb_from_no_epsilon.
    eapply traces_from_fuel_epsilon_free_no_epsilon; eauto.
  Qed.

  Lemma filter_ext_true :
    forall {B : Type} (p q : B -> bool) xs,
      (forall x, In x xs -> q x = true) ->
      filter (fun x => p x && q x) xs = filter p xs.
  Proof.
    intros B p q xs.
    induction xs as [| x xs IH]; intros H; simpl.
    - reflexivity.
    - rewrite H by (simpl; auto).
      assert (Htail : forall y, In y xs -> q y = true).
      { intros y Hy. apply H. simpl. auto. }
      rewrite (IH Htail).
      destruct (p x); reflexivity.
  Qed.

  Lemma filter_ext_true3 :
    forall {B : Type} (p q r : B -> bool) xs,
      (forall x, In x xs -> q x = true) ->
      (forall x, In x xs -> r x = true) ->
      filter (fun x => (p x && q x) && r x) xs = filter p xs.
  Proof.
    intros B p q r xs.
    induction xs as [| x xs IH]; intros Hq Hr; simpl.
    - reflexivity.
    - rewrite Hq by (simpl; auto).
      rewrite Hr by (simpl; auto).
      assert (Hqtail : forall y, In y xs -> q y = true).
      { intros y Hy. apply Hq. simpl. auto. }
      assert (Hrtail : forall y, In y xs -> r y = true).
      { intros y Hy. apply Hr. simpl. auto. }
      rewrite (IH Hqtail Hrtail).
      destruct (p x); reflexivity.
  Qed.

  (* Lemma 1. dra *)
  Theorem section4_lemma1_dra :
    forall (m : finite_enfa) w q,
      enfa_epsilon_free m ->
      enfa_dra_at m w q = enfa_dra_prime_at m w q.
  Proof.
    intros m w q Heps.
    unfold enfa_dra_at, enfa_dra_prime_at.
    symmetry.
    f_equal.
    apply filter_ext_true.
    intros st Hin.
    now apply epsilon_simpleb_epsilon_free with (w := w).
  Qed.

  (* Lemma 1. da *)
  Theorem section4_lemma1_da :
    forall (m : finite_enfa) w,
      enfa_epsilon_free m ->
      enfa_da_word m w = enfa_da_prime_word m w.
  Proof.
    intros m w Heps.
    unfold enfa_da_word, enfa_da_prime_word.
    induction (enfa_final_states m) as [| q qs IH]; simpl.
    - reflexivity.
    - rewrite section4_lemma1_dra by exact Heps.
      rewrite IH.
      + unfold enfa_accepting_maximal_simple_reach_count, enfa_dra_prime_at.
        f_equal.
        f_equal.
        symmetry.
        apply filter_ext_true.
        intros st Hin.
        now apply enfa_accepting_maximal_epsilon_simpleb_epsilon_free.
  Qed.

  (* Lemma 1. leaf *)
  Theorem section4_lemma1_leaf :
    forall (m : finite_enfa) w,
      enfa_epsilon_free m ->
      enfa_leaf_word m w = enfa_leaf_prime_word m w.
  Proof.
    intros m w Heps.
    unfold enfa_leaf_word, enfa_leaf_prime_word.
    induction (fenfa_states m) as [| q qs IH]; simpl.
    - reflexivity.
    - rewrite section4_lemma1_dra by exact Heps.
      rewrite IH.
      + unfold enfa_maximal_simple_reach_count, enfa_dra_prime_at.
        f_equal.
        f_equal.
        symmetry.
        apply filter_ext_true.
        intros st Hin.
        now apply maximal_epsilon_simpleb_epsilon_free.
  Qed.

  Lemma sum_nats_map_filter_le :
    forall {B : Type} (p : B -> bool) (f : B -> nat) xs,
      sum_nats (map f (filter p xs)) <= sum_nats (map f xs).
  Proof.
    intros B p f xs.
    induction xs as [| x xs IH]; simpl.
    - lia.
    - destruct (p x); simpl; lia.
  Qed.

  Theorem section4_theorem2_leafufa_implies_ufa_under_accepting_maximal_da_leaf_bound :
    forall (m : finite_enfa),
      enfa_accepting_maximal_da_bounded_by_leaf m ->
      enfa_LeafUFA m -> enfa_UFA m.
  Proof.
    intros m Hbound Hleaf w.
    specialize (Hleaf w).
    specialize (Hbound w).
    lia.
  Qed.

  Theorem section4_theorem2_leafufa_implies_maximal_reachufa :
    forall (m : finite_enfa),
      enfa_LeafUFA m -> enfa_MaximalReachUFA m.
  Proof.
    intros m Hleaf w q Hq.
    specialize (Hleaf w).
    unfold enfa_leaf_prime_word in Hleaf.
    pose proof
      (sum_map_In_le
         (enfa_maximal_simple_reach_count m w)
         (fenfa_states m)
         q
         Hq) as Hle.
    lia.
  Qed.

  Theorem section4_lemma2_maximal_reachufa_leaf_bound :
    forall (m : finite_enfa) w,
      enfa_MaximalReachUFA m ->
      enfa_leaf_prime_word m w <= length (fenfa_states m).
  Proof.
    intros m w Hmax.
    unfold enfa_leaf_prime_word.
    rewrite <- length_map with
      (f := enfa_maximal_simple_reach_count m w)
      (l := fenfa_states m).
    apply sum_nats_all_le_one.
    intros n Hn.
    apply in_map_iff in Hn as [q [Hn Hq]].
    subst n.
    now apply Hmax.
  Qed.

  (* Lemma 2. *)
  Theorem section4_lemma2_reachufa_leaf_bound :
    forall (m : finite_enfa) w,
      enfa_ReachUFA m ->
      enfa_leaf_prime_word m w <= length (fenfa_states m).
  Proof.
    intros m w Hreach.
    apply section4_lemma2_maximal_reachufa_leaf_bound.
    intros u q Hq.
    pose proof (enfa_maximal_simple_reach_le_dra_prime m u q) as Hle.
    pose proof (Hreach u q Hq) as Hreach_q.
    lia.
  Qed.

  Lemma enfa_maximal_simple_reach_epsilon_free :
    forall (m : finite_enfa) w q,
      enfa_epsilon_free m ->
      enfa_maximal_simple_reach_count m w q =
      enfa_dra_prime_at m w q.
  Proof.
    intros m w q Heps.
    unfold enfa_maximal_simple_reach_count, enfa_dra_prime_at.
    f_equal.
    apply filter_ext_true.
    intros st Hin.
    now apply maximal_epsilon_simpleb_epsilon_free.
  Qed.

  (* Theorem 2 *)
  Theorem section4_theorem2_trim_extendable_ufa_implies_reachufa :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_trim m ->
      enfa_prime_extendable m ->
      enfa_UFA m ->
      enfa_ReachUFA m.
  Proof.
    intros m _ _ Hextend Hufa w q Hq.
    destruct (Hextend w q Hq) as [suffix Hle].
    pose proof (Hufa (w ++ suffix)) as Hacc.
    lia.
  Qed.

  Theorem section4_theorem2_epsilon_free_trim_extendable_ufa_implies_reachufa :
    forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_trim m ->
      enfa_prime_extendable m ->
      enfa_UFA m ->
      enfa_ReachUFA m.
  Proof.
    intros m _ Hwf Htrim Hextend Hufa.
    eapply section4_theorem2_trim_extendable_ufa_implies_reachufa; eauto.
  Qed.

  Lemma length_filter_pos_In :
    forall {B : Type} (p : B -> bool) xs,
      0 < length (filter p xs) ->
      exists x, In x xs /\ p x = true.
  Proof.
    intros B p xs.
    induction xs as [| x xs IH]; simpl; intros Hpos.
    - lia.
    - destruct (p x) eqn:Hp.
      + exists x. simpl. auto.
      + destruct (IH Hpos) as [y [Hy Hp_y]].
        exists y. simpl. auto.
  Qed.

  Lemma NoDup_cons_notin :
    forall {B : Type} (x : B) xs,
      NoDup (x :: xs) -> ~ In x xs.
  Proof.
    intros B x xs H.
    inversion H; subst; assumption.
  Qed.

  Lemma sum_map_two_pos_lower :
    forall {B : Type} (f : B -> nat) xs x y,
      NoDup xs ->
      In x xs ->
      In y xs ->
      x <> y ->
      0 < f x ->
      0 < f y ->
      2 <= sum_nats (map f xs).
  Proof.
    intros B f xs.
    induction xs as [| z zs IH]; intros x y Hnodup Hx Hy Hneq Hfx Hfy.
    - contradiction.
    - simpl in Hx, Hy.
      inversion Hnodup as [| z' zs' Hz_notin Hnodup_tail]; subst.
      destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy].
      + subst. contradiction.
      + subst x.
        pose proof (sum_map_In_le f zs y Hy) as Hle.
        assert (0 < sum_nats (map f zs)) as Htail_pos.
        { eapply Nat.lt_le_trans; [exact Hfy | exact Hle]. }
        assert (1 <= f z) by lia.
        assert (1 <= sum_nats (map f zs)) by lia.
        change (1 + 1 <= f z + sum_nats (map f zs)).
        now apply Nat.add_le_mono.
      + subst y.
        pose proof (sum_map_In_le f zs x Hx) as Hle.
        assert (0 < sum_nats (map f zs)) as Htail_pos.
        { eapply Nat.lt_le_trans; [exact Hfx | exact Hle]. }
        assert (1 <= f z) by lia.
        assert (1 <= sum_nats (map f zs)) by lia.
        change (1 + 1 <= f z + sum_nats (map f zs)).
        now apply Nat.add_le_mono.
      + specialize (IH x y Hnodup_tail Hx Hy Hneq Hfx Hfy).
        eapply Nat.le_trans; [exact IH | apply Nat.le_add_l].
  Qed.

  Lemma filter_length_pos_of_In :
    forall {B : Type} (p : B -> bool) xs x,
      In x xs ->
      p x = true ->
      0 < length (filter p xs).
  Proof.
    intros B p xs x Hin Hp.
    induction xs as [| y ys IH]; simpl in Hin |- *.
    - contradiction.
    - destruct Hin as [Heq | Hin].
      + subst. rewrite Hp. simpl. lia.
      + destruct (p y); simpl; specialize (IH Hin); lia.
  Qed.

  Lemma trace_word_app :
    forall (m : finite_enfa) (t1 t2 : enfa_trace m),
      trace_word (t1 ++ t2) = trace_word t1 ++ trace_word t2.
  Proof.
    intros m t1.
    induction t1 as [| e t1 IH]; intros t2; simpl.
    - reflexivity.
    - destruct (edge_label e); simpl; now rewrite IH.
  Qed.

  Lemma trace_end_app :
    forall (m : finite_enfa) p (t1 t2 : enfa_trace m),
      trace_end p (t1 ++ t2) = trace_end (trace_end p t1) t2.
  Proof.
    intros m p t1.
    revert p.
    induction t1 as [| e t1 IH]; intros p t2; simpl.
    - reflexivity.
    - apply IH.
  Qed.

  Lemma epsilon_suffix_states_app_none :
    forall (m : finite_enfa) seen (t : enfa_trace m) p q,
      epsilon_suffix_states m seen (t ++ [((p, None), q)]) =
      q :: epsilon_suffix_states m seen t.
  Proof.
    intros m seen t.
    revert seen.
    induction t as [| [[p0 l] q0] t IH]; intros seen p q; simpl.
    - reflexivity.
    - destruct l; simpl; apply IH.
  Qed.

  Lemma epsilon_simpleb_from_app_none :
    forall (m : finite_enfa) seen (t : enfa_trace m) p q,
      epsilon_simpleb_from m seen t = true ->
      state_inb m q (epsilon_suffix_states m seen t) = false ->
      epsilon_simpleb_from m seen (t ++ [((p, None), q)]) = true.
  Proof.
    intros m seen t.
    revert seen.
    induction t as [| [[p0 l] q0] t IH]; intros seen p q Hsimple Hfresh.
    - simpl in *. now rewrite Hfresh.
    - simpl in Hsimple |- *.
      destruct l as [a|].
      + eapply IH; eauto.
      + apply andb_true_iff in Hsimple as [Hhead Htail].
        rewrite Hhead. simpl.
        eapply IH; eauto.
  Qed.

  Lemma valid_trace_app :
    forall (m : finite_enfa) p t q u r,
      valid_trace m p t q ->
      valid_trace m q u r ->
      valid_trace m p (t ++ u) r.
  Proof.
    intros m p t q u r Ht Hu.
    induction Ht as [q| p l q r' t Hstep _ IH]; simpl.
    - exact Hu.
    - econstructor; eauto.
  Qed.

  Lemma finite_enfa_wf_valid_trace_end_in_states :
    forall (m : finite_enfa) p t q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      In q (fenfa_states m).
  Proof.
    intros m p t q Hwf Hp Htrace.
    induction Htrace as [q| p l q r t Hstep _ IH].
    - exact Hp.
    - apply IH.
      eapply fenfa_steps_in_states; eauto.
  Qed.

  Lemma valid_trace_app_edge :
    forall (m : finite_enfa) p t q l r,
      valid_trace m p t q ->
      In r (enfa_step (fenfa_base m) q l) ->
      valid_trace m p (t ++ [((q, l), r)]) r.
  Proof.
    intros m p t q l r Ht Hstep.
    eapply valid_trace_app; eauto.
    econstructor; eauto.
    constructor.
  Qed.

  Lemma traces_from_fuel_valid :
    forall (m : finite_enfa) fuel p w t,
      In t (traces_from_fuel m fuel p w) ->
      valid_trace m p t (trace_end p t) /\ trace_word t = w.
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros p w t Hin; simpl in Hin.
    - destruct w as [| a w]; simpl in Hin.
      + destruct Hin as [Ht | []]. subst. split; constructor.
      + contradiction.
    - destruct w as [| a w].
      + destruct Hin as [Ht | Hin].
        * subst. split; constructor.
        * rewrite app_nil_r in Hin. simpl in Hin.
          apply in_concat in Hin as [ts [Hts Ht]].
          apply in_map_iff in Hts as [q [Hts Hq]].
          subst ts.
          apply in_map_iff in Ht as [t' [Ht Ht']].
          subst t.
          destruct (IH q [] t' Ht') as [Hvalid Hword].
          split.
          -- simpl. econstructor; eauto.
          -- simpl. exact Hword.
      + apply in_app_or in Hin as [Hin | Hin].
        * contradiction.
        * apply in_app_or in Hin as [Hin | Hin].
          -- apply in_concat in Hin as [ts [Hts Ht]].
             apply in_map_iff in Hts as [q [Hts Hq]].
             subst ts.
             apply in_map_iff in Ht as [t' [Ht Ht']].
             subst t.
             destruct (IH q (a :: w) t' Ht') as [Hvalid Hword].
             split.
             ++ simpl. econstructor; eauto.
             ++ simpl. exact Hword.
          -- apply in_concat in Hin as [ts [Hts Ht]].
             apply in_map_iff in Hts as [q [Hts Hq]].
             subst ts.
             apply in_map_iff in Ht as [t' [Ht Ht']].
             subst t.
             destruct (IH q w t' Ht') as [Hvalid Hword].
             split.
             ++ simpl. econstructor; eauto.
             ++ simpl. now rewrite Hword.
  Qed.

  Lemma traces_from_fuel_length_le_fuel :
    forall (m : finite_enfa) fuel p w t,
      In t (traces_from_fuel m fuel p w) ->
      length t <= fuel.
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros p w t Hin; simpl in Hin.
    - destruct w as [| a w]; simpl in Hin.
      + destruct Hin as [Ht | []]. subst. simpl. lia.
      + contradiction.
    - destruct w as [| a w].
      + destruct Hin as [Ht | Hin].
        * subst. simpl. lia.
        * rewrite app_nil_r in Hin. simpl in Hin.
          apply in_concat in Hin as [ts [Hts Ht]].
          apply in_map_iff in Hts as [q [Hts Hq]].
          subst ts.
          apply in_map_iff in Ht as [t' [Ht Ht']].
          subst t. simpl.
          specialize (IH q [] t' Ht'). lia.
      + apply in_app_or in Hin as [Hin | Hin].
        * contradiction.
        * apply in_app_or in Hin as [Hin | Hin].
          -- apply in_concat in Hin as [ts [Hts Ht]].
             apply in_map_iff in Hts as [q [Hts Hq]].
             subst ts.
             apply in_map_iff in Ht as [t' [Ht Ht']].
             subst t. simpl.
             specialize (IH q (a :: w) t' Ht'). lia.
          -- apply in_concat in Hin as [ts [Hts Ht]].
             apply in_map_iff in Hts as [q [Hts Hq]].
             subst ts.
             apply in_map_iff in Ht as [t' [Ht Ht']].
             subst t. simpl.
             specialize (IH q w t' Ht'). lia.
  Qed.

  Lemma NoDup_map_injective_in :
    forall {B C : Type} (f : B -> C) xs,
      (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
      NoDup xs ->
      NoDup (map f xs).
  Proof.
    intros B C f xs Hinj Hnodup.
    induction Hnodup as [| x xs Hnotin Hnodup IH]; simpl.
    - constructor.
    - constructor.
      + intro Hin.
        apply in_map_iff in Hin as [y [Hfy Hy]].
        apply Hnotin.
        assert (x = y) as Hxy.
        {
          apply Hinj; simpl; auto.
        }
        now subst y.
      + apply IH.
        intros y z Hy Hz Heq.
        apply Hinj; simpl; auto.
  Qed.

  Lemma NoDup_concat_map :
    forall {B C : Type} (f : B -> list C) xs,
      NoDup xs ->
      (forall x, In x xs -> NoDup (f x)) ->
      (forall x y z,
        In x xs -> In y xs -> x <> y ->
        In z (f x) -> ~ In z (f y)) ->
      NoDup (concat (map f xs)).
  Proof.
    intros B C f xs Hnodup Hchunk Hdisjoint.
    induction Hnodup as [| x xs Hnotin Hnodup IH]; simpl.
    - constructor.
    - apply NoDup_app. repeat split.
      + apply Hchunk. simpl. auto.
      + apply IH.
        * intros y Hy. apply Hchunk. simpl. auto.
        * intros y z a Hy Hz Hneq Ha.
          eapply Hdisjoint with (x := y) (y := z) (z := a); simpl; eauto.
      + intros z Hz Hin_concat.
        apply in_concat in Hin_concat as [ys [Hys Hzys]].
        apply in_map_iff in Hys as [y [Hys Hy]].
        subst ys.
        assert (Hxy : x <> y).
        {
          intro Heq. subst y. contradiction.
        }
        eapply Hdisjoint with (x := x) (y := y) (z := z); simpl; eauto.
  Qed.

  Lemma traces_from_fuel_epsilon_free_NoDup :
    forall (m : finite_enfa) fuel p w,
      finite_enfa_wf m ->
      enfa_epsilon_free m ->
      In p (fenfa_states m) ->
      NoDup (traces_from_fuel m fuel p w).
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros p w Hwf Heps Hp; simpl.
    - destruct w as [| a w].
      + constructor.
        * intros [].
        * constructor.
      + constructor.
    - destruct w as [| a w].
      + rewrite Heps. simpl.
        constructor.
        * intros [].
        * constructor.
      + rewrite Heps. simpl.
        apply NoDup_concat_map.
        * eapply fenfa_step_targets_nodup; eauto.
        * intros q Hq.
          apply NoDup_map_injective_in.
          -- intros t1 t2 Ht1 Ht2 Heq.
             inversion Heq. reflexivity.
          -- apply IH; auto.
             eapply fenfa_steps_in_states; eauto.
        * intros q r x Hq Hr Hneq Hx Hxr.
          apply in_map_iff in Hx as [tq [Hx _]].
          apply in_map_iff in Hxr as [tr [Hxr _]].
          congruence.
  Qed.

  Lemma traces_from_fuel_NoDup :
    forall (m : finite_enfa) fuel p w,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      NoDup (traces_from_fuel m fuel p w).
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros p w Hwf Hp; simpl.
    - destruct w as [| a w].
      + constructor; [intros [] | constructor].
      + constructor.
    - destruct w as [| a w].
      + rewrite app_nil_r.
        constructor.
        * intro Hin.
          apply in_concat in Hin as [ts [Hts Ht]].
          apply in_map_iff in Hts as [q [Hts _]].
          subst ts.
          apply in_map_iff in Ht as [t [Ht _]].
          discriminate.
        * apply NoDup_concat_map.
          -- eapply fenfa_step_targets_nodup; eauto.
          -- intros q Hq.
             apply NoDup_map_injective_in.
             ++ intros t1 t2 _ _ Heq.
                inversion Heq. reflexivity.
             ++ apply IH; auto.
                eapply fenfa_steps_in_states; eauto.
          -- intros q r x Hq Hr Hneq Hx Hxr.
             apply in_map_iff in Hx as [tq [Hx _]].
             apply in_map_iff in Hxr as [tr [Hxr _]].
             congruence.
      + change (NoDup
          (concat
             (map
                (fun q =>
                   map
                     (fun t => ((p, None), q) :: t)
                     (traces_from_fuel m fuel q (a :: w)))
                (enfa_step (fenfa_base m) p None)) ++
           concat
             (map
                (fun q =>
                   map
                     (fun t => ((p, Some a), q) :: t)
                     (traces_from_fuel m fuel q w))
                (enfa_step (fenfa_base m) p (Some a))))).
        apply NoDup_app. repeat split.
        * apply NoDup_concat_map.
          -- eapply fenfa_step_targets_nodup; eauto.
          -- intros q Hq.
             apply NoDup_map_injective_in.
             ++ intros t1 t2 _ _ Heq.
                inversion Heq. reflexivity.
             ++ apply IH; auto.
                eapply fenfa_steps_in_states; eauto.
          -- intros q r x Hq Hr Hneq Hx Hxr.
             apply in_map_iff in Hx as [tq [Hx _]].
             apply in_map_iff in Hxr as [tr [Hxr _]].
             congruence.
        * apply NoDup_concat_map.
          -- eapply fenfa_step_targets_nodup; eauto.
          -- intros q Hq.
             apply NoDup_map_injective_in.
             ++ intros t1 t2 _ _ Heq.
                inversion Heq. reflexivity.
             ++ apply IH; auto.
                eapply fenfa_steps_in_states; eauto.
          -- intros q r x Hq Hr Hneq Hx Hxr.
             apply in_map_iff in Hx as [tq [Hx _]].
             apply in_map_iff in Hxr as [tr [Hxr _]].
             congruence.
        * intros x Hx Hx'.
          apply in_concat in Hx as [ts [Hts Hx]].
          apply in_map_iff in Hts as [q [Hts _]].
          subst ts.
          apply in_map_iff in Hx as [tq [Hx _]].
          apply in_concat in Hx' as [ts [Hts Hx']].
          apply in_map_iff in Hts as [r [Hts _]].
          subst ts.
          apply in_map_iff in Hx' as [tr [Hx' _]].
          congruence.
  Qed.

  Lemma trace_word_length_no_epsilon :
    forall (m : finite_enfa) (t : enfa_trace m),
      (forall e, In e t -> exists a, edge_label e = Some a) ->
      length t = length (trace_word t).
  Proof.
    intros m t.
    induction t as [| e t IH]; intros Hnoeps; simpl.
    - reflexivity.
    - destruct (Hnoeps e (or_introl eq_refl)) as [a Ha].
      rewrite Ha. simpl.
      f_equal.
      apply IH.
      intros e' He'. apply Hnoeps. now right.
  Qed.

  Lemma traces_from_fuel_epsilon_free_length_word :
    forall (m : finite_enfa) fuel p w t,
      enfa_epsilon_free m ->
      In t (traces_from_fuel m fuel p w) ->
      length t = length w.
  Proof.
    intros m fuel p w t Heps Hin.
    destruct (traces_from_fuel_valid m fuel p w t Hin) as [_ Hword].
    rewrite <- Hword.
    apply trace_word_length_no_epsilon.
    eapply traces_from_fuel_epsilon_free_no_epsilon; eauto.
  Qed.

  Lemma state_inb_false_not_In :
    forall (m : finite_enfa) q xs,
      state_inb m q xs = false ->
      ~ In q xs.
  Proof.
    intros m q xs Hfalse Hin.
    unfold state_inb in Hfalse.
    induction xs as [| x xs IH]; simpl in *.
    - contradiction.
    - destruct Hin as [Hin | Hin].
      + subst x.
        rewrite (fenfa_state_eqb_complete m q q eq_refl) in Hfalse.
        discriminate.
      + destruct (fenfa_state_eqb m q x); simpl in Hfalse; try discriminate.
        apply IH; auto.
  Qed.

  Lemma state_inb_In_true :
    forall (m : finite_enfa) q xs,
      In q xs ->
      state_inb m q xs = true.
  Proof.
    intros m q xs.
    induction xs as [| x xs IH]; simpl; intros Hin.
    - contradiction.
    - destruct Hin as [Hin | Hin].
      + subst x.
        rewrite (fenfa_state_eqb_complete m q q eq_refl).
        reflexivity.
      + destruct (fenfa_state_eqb m q x); simpl; auto.
  Qed.

  Lemma state_inb_true_In :
    forall (m : finite_enfa) q xs,
      state_inb m q xs = true ->
      In q xs.
  Proof.
    intros m q xs.
    induction xs as [| x xs IH]; simpl; intros H.
    - discriminate.
    - destruct (fenfa_state_eqb m q x) eqn:Heq.
      + apply fenfa_state_eqb_sound in Heq. subst x. simpl. auto.
      + simpl in H. right. now apply IH.
  Qed.

  Lemma state_inb_not_In_false :
    forall (m : finite_enfa) q xs,
      ~ In q xs ->
      state_inb m q xs = false.
  Proof.
    intros m q xs Hnot.
    destruct (state_inb m q xs) eqn:Hinb; auto.
    apply state_inb_true_In in Hinb.
    contradiction.
  Qed.

  Lemma state_inb_cons_neq :
    forall (m : finite_enfa) q r xs,
      q <> r ->
      state_inb m q (r :: xs) = state_inb m q xs.
  Proof.
    intros m q r xs Hneq.
    simpl.
    destruct (fenfa_state_eqb m q r) eqn:Heq.
    - apply fenfa_state_eqb_sound in Heq. contradiction.
    - reflexivity.
  Qed.

  Lemma state_inb_false_of_incl :
    forall (m : finite_enfa) q xs ys,
      (forall x, In x xs -> In x ys) ->
      state_inb m q ys = false ->
      state_inb m q xs = false.
  Proof.
    intros m q xs ys Hincl Hys.
    destruct (state_inb m q xs) eqn:Hxs; auto.
    apply state_inb_true_In in Hxs.
    pose proof (Hincl q Hxs) as Hqys.
    rewrite (state_inb_In_true m q ys Hqys) in Hys.
    discriminate.
  Qed.

  Lemma trace_end_in_epsilon_suffix_states :
    forall (m : finite_enfa) seen p t,
      In p seen ->
      In (trace_end p t) (epsilon_suffix_states m seen t).
  Proof.
    intros m seen p t.
    revert seen p.
    induction t as [| [[p0 l] q0] t IH]; intros seen p Hin; simpl.
    - exact Hin.
    - destruct l as [a|].
      + apply IH. simpl. auto.
      + apply IH. simpl. auto.
  Qed.

  Lemma filter_length_le :
    forall {B : Type} (p : B -> bool) xs,
      length (filter p xs) <= length xs.
  Proof.
    intros B p xs.
    induction xs as [| x xs IH]; simpl.
    - lia.
    - destruct (p x); simpl; lia.
  Qed.

  Lemma enfa_dra_prime_at_le_started_traces :
    forall (m : finite_enfa) w q,
      enfa_dra_prime_at m w q <= length (started_traces m w).
  Proof.
    intros m w q.
    unfold enfa_dra_prime_at.
    apply filter_length_le.
  Qed.

  Definition enfa_unseen_epsilon_transition_count
      (m : finite_enfa)
      (seen : list (enfa_state (fenfa_base m))) : nat :=
    sum_nats
      (map
         (fun q =>
            if state_inb m q seen
            then 0
            else length (enfa_step (fenfa_base m) q None))
         (fenfa_states m)).

  Definition enfa_epsilon_closure_work_bound
      (m : finite_enfa)
      (seen todo : list (enfa_state (fenfa_base m))) : nat :=
    length todo + enfa_unseen_epsilon_transition_count m seen.

  Lemma enfa_unseen_count_on_le_total :
    forall (m : finite_enfa) seen xs,
      sum_nats
        (map
           (fun q =>
              if state_inb m q seen
              then 0
              else length (enfa_step (fenfa_base m) q None)) xs) <=
      sum_nats
        (map
           (fun q => length (enfa_step (fenfa_base m) q None)) xs).
  Proof.
    intros m seen xs.
    induction xs as [| q xs IH]; simpl.
    - lia.
    - destruct (state_inb m q seen); simpl; lia.
  Qed.

  Lemma enfa_unseen_count_on_cons_absent :
    forall (m : finite_enfa) seen q xs,
      ~ In q xs ->
      sum_nats
        (map
           (fun x =>
              if state_inb m x (q :: seen)
              then 0
              else length (enfa_step (fenfa_base m) x None)) xs) =
      sum_nats
        (map
           (fun x =>
              if state_inb m x seen
              then 0
              else length (enfa_step (fenfa_base m) x None)) xs).
  Proof.
    intros m seen q xs Hnotin.
    induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - assert (Hxq : x <> q).
      { intro Hxq. subst x. apply Hnotin. simpl. auto. }
      destruct (fenfa_state_eqb m x q) eqn:Heq.
      {
        apply fenfa_state_eqb_sound in Heq.
        contradiction.
      }
      simpl.
      rewrite <- IH.
      + reflexivity.
      + intro Hq. apply Hnotin. simpl. auto.
  Qed.

  Lemma enfa_unseen_epsilon_transition_count_cons :
    forall (m : finite_enfa) seen q,
      NoDup (fenfa_states m) ->
      In q (fenfa_states m) ->
      state_inb m q seen = false ->
      enfa_unseen_epsilon_transition_count m seen =
      length (enfa_step (fenfa_base m) q None) +
      enfa_unseen_epsilon_transition_count m (q :: seen).
  Proof.
    intros m seen q Hnodup Hin Hfresh.
    unfold enfa_unseen_epsilon_transition_count.
    induction Hnodup as [| x xs Hnotin Hnodup IH]; simpl in Hin |- *.
    - contradiction.
    - destruct Hin as [Hx | Hin].
      + subst x.
        rewrite Hfresh.
        rewrite (fenfa_state_eqb_complete m q q eq_refl).
        simpl.
        replace
          (sum_nats
             (map
                (fun x =>
                   if state_inb m x seen
                   then 0
                   else length (enfa_step (fenfa_base m) x None)) xs))
          with
          (sum_nats
             (map
                (fun x =>
                   if state_inb m x (q :: seen)
                   then 0
                   else length (enfa_step (fenfa_base m) x None)) xs)).
        * simpl. lia.
        * exact (enfa_unseen_count_on_cons_absent m seen q xs Hnotin).
      + assert (Hxq : x <> q).
        { intro Hxq. subst x. contradiction. }
        destruct (fenfa_state_eqb m x q) eqn:Heq.
        {
          apply fenfa_state_eqb_sound in Heq.
          contradiction.
        }
        simpl.
        specialize (IH Hin).
        rewrite IH.
        destruct (state_inb m x seen); simpl; lia.
  Qed.

  Lemma enfa_epsilon_closure_work_bound_seen_head :
    forall (m : finite_enfa) seen q todo,
      S (enfa_epsilon_closure_work_bound m seen todo) =
      enfa_epsilon_closure_work_bound m seen (q :: todo).
  Proof.
    intros m seen q todo.
    unfold enfa_epsilon_closure_work_bound. simpl. lia.
  Qed.

  Lemma enfa_epsilon_closure_work_bound_unseen_head :
    forall (m : finite_enfa) seen q todo,
      NoDup (fenfa_states m) ->
      In q (fenfa_states m) ->
      state_inb m q seen = false ->
      S
        (enfa_epsilon_closure_work_bound
           m (q :: seen)
           (enfa_step (fenfa_base m) q None ++ todo)) =
      enfa_epsilon_closure_work_bound m seen (q :: todo).
  Proof.
    intros m seen q todo Hnodup Hq Hfresh.
    unfold enfa_epsilon_closure_work_bound.
    simpl.
    rewrite length_app.
    rewrite
      (enfa_unseen_epsilon_transition_count_cons
         m seen q Hnodup Hq Hfresh).
    lia.
  Qed.

  Lemma enfa_unseen_count_plus_seen_step_le_total :
    forall (m : finite_enfa) seen q,
      NoDup (fenfa_states m) ->
      In q (fenfa_states m) ->
      state_inb m q seen = true ->
      length (enfa_step (fenfa_base m) q None) +
      enfa_unseen_epsilon_transition_count m seen <=
      enfa_epsilon_transition_bound m.
  Proof.
    intros m seen q Hnodup Hin Hseen.
    unfold enfa_unseen_epsilon_transition_count,
      enfa_epsilon_transition_bound.
    induction Hnodup as [| x xs Hnotin Hnodup IH]; simpl in Hin |- *.
    - contradiction.
    - destruct Hin as [Hx | Hin].
      + subst x.
        rewrite Hseen.
        pose proof (enfa_unseen_count_on_le_total m seen xs) as Hle.
        lia.
      + assert (Hxq : x <> q).
        { intro Hxq. subst x. contradiction. }
        specialize (IH Hin).
        destruct (state_inb m x seen); simpl; lia.
  Qed.

  Lemma enfa_strict_epsilon_closure_work_bound_le_transition_bound :
    forall (m : finite_enfa) st,
      finite_enfa_wf m ->
      In (started_end st) (fenfa_states m) ->
      enfa_epsilon_closure_work_bound
        m
        (epsilon_suffix_states m [fst st] (snd st))
        (filter
           (fun q' =>
              negb
                (state_inb
                   m q'
                   (epsilon_suffix_states m [fst st] (snd st))))
           (enfa_step (fenfa_base m) (started_end st) None)) <=
      enfa_epsilon_transition_bound m.
  Proof.
    intros m [s t] Hwf Hend.
    simpl in *.
    set (seen := epsilon_suffix_states m [s] t).
    set (q := trace_end s t).
    assert (Hq_seen : state_inb m q seen = true).
    {
      apply state_inb_In_true.
      subst q seen.
      apply trace_end_in_epsilon_suffix_states.
      simpl. auto.
    }
    unfold enfa_epsilon_closure_work_bound.
    pose proof
      (filter_length_le
         (fun q' => negb (state_inb m q' seen))
         (enfa_step (fenfa_base m) q None)) as Hfilter.
    pose proof
      (enfa_unseen_count_plus_seen_step_le_total
         m seen q (fenfa_states_nodup m Hwf) Hend Hq_seen)
      as Htotal.
    eapply Nat.le_trans
      with (m :=
        length (enfa_step (fenfa_base m) q None) +
        enfa_unseen_epsilon_transition_count m seen).
    - apply Nat.add_le_mono_r. exact Hfilter.
    - exact Htotal.
  Qed.

  Inductive enfa_fresh_epsilon_reachable
      (m : finite_enfa)
      (seen todo : list (enfa_state (fenfa_base m)))
      : enfa_state (fenfa_base m) -> Prop :=
  | Fresh_epsilon_todo :
      forall q,
        In q todo ->
        state_inb m q seen = false ->
        enfa_fresh_epsilon_reachable m seen todo q
  | Fresh_epsilon_step :
      forall p q,
        enfa_fresh_epsilon_reachable m seen todo p ->
        In q (enfa_step (fenfa_base m) p None) ->
        state_inb m q seen = false ->
        enfa_fresh_epsilon_reachable m seen todo q.

  Lemma enfa_fresh_epsilon_reachable_todo_nonempty :
    forall (m : finite_enfa) seen todo q,
      enfa_fresh_epsilon_reachable m seen todo q ->
      todo <> [].
  Proof.
    intros m seen todo q Hreach.
    induction Hreach as [q Hin _| p q _ IH _ _].
    - destruct todo as [| x xs]; simpl in Hin; congruence.
    - exact IH.
  Qed.

  Lemma enfa_fresh_epsilon_reachable_skip_seen_head :
    forall (m : finite_enfa) seen r todo q,
      state_inb m r seen = true ->
      enfa_fresh_epsilon_reachable m seen (r :: todo) q ->
      enfa_fresh_epsilon_reachable m seen todo q.
  Proof.
    intros m seen r todo q Hseen Hreach.
    induction Hreach as [q Hin Hfresh| p q Hreach IH Hstep Hfresh].
    - destruct Hin as [Hq | Hin].
      + subst q. rewrite Hseen in Hfresh. discriminate.
      + constructor; auto.
    - apply Fresh_epsilon_step with (p := p); auto.
  Qed.

  Lemma enfa_fresh_epsilon_reachable_after_unseen_head :
    forall (m : finite_enfa) seen r todo q,
      state_inb m r seen = false ->
      q <> r ->
      enfa_fresh_epsilon_reachable m seen (r :: todo) q ->
      enfa_fresh_epsilon_reachable
        m (r :: seen) (enfa_step (fenfa_base m) r None ++ todo) q.
  Proof.
    intros m seen r todo q Hr_fresh Hqr Hreach.
    induction Hreach as [q Hin Hfresh| p q Hreach IH Hstep Hfresh].
    - destruct Hin as [Hq | Hin].
      + subst q. contradiction.
      + constructor.
        * apply in_or_app. right. exact Hin.
        * rewrite state_inb_cons_neq by exact Hqr. exact Hfresh.
    - destruct (fenfa_state_eqb m p r) eqn:Hpr.
      + apply fenfa_state_eqb_sound in Hpr. subst p.
        apply Fresh_epsilon_todo.
        * apply in_or_app. left. exact Hstep.
        * rewrite state_inb_cons_neq by exact Hqr. exact Hfresh.
      + assert (Hpr_neq : p <> r).
        {
          intro Hpr_eq.
          rewrite (fenfa_state_eqb_complete m p r Hpr_eq) in Hpr.
          discriminate.
        }
        apply Fresh_epsilon_step with (p := p).
        * apply IH. exact Hpr_neq.
        * exact Hstep.
        * rewrite state_inb_cons_neq by exact Hqr. exact Hfresh.
  Qed.

  Lemma enfa_epsilon_closure_fuel_complete :
    forall (m : finite_enfa) fuel seen todo q,
      finite_enfa_wf m ->
      (forall r, In r todo -> In r (fenfa_states m)) ->
      enfa_fresh_epsilon_reachable m seen todo q ->
      enfa_epsilon_closure_work_bound m seen todo <= fuel ->
      In q (enfa_epsilon_closure_fuel m fuel seen todo).
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros seen todo q Hwf Htodo Hreach Hfuel.
    - pose proof
        (enfa_fresh_epsilon_reachable_todo_nonempty
           m seen todo q Hreach) as Hnonempty.
      destruct todo as [| r todo']; [contradiction |].
      unfold enfa_epsilon_closure_work_bound in Hfuel.
      simpl in Hfuel. lia.
    - simpl.
      destruct todo as [| r todo'].
      + pose proof
          (enfa_fresh_epsilon_reachable_todo_nonempty
             m seen [] q Hreach) as Hnonempty.
        contradiction.
      + destruct (state_inb m r seen) eqn:Hr_seen.
        * eapply IH.
          -- exact Hwf.
          -- intros x Hx. apply Htodo. simpl. auto.
          -- eapply enfa_fresh_epsilon_reachable_skip_seen_head; eauto.
          -- rewrite <- (enfa_epsilon_closure_work_bound_seen_head
                          m seen r todo') in Hfuel.
             lia.
        * destruct (fenfa_state_eqb m q r) eqn:Hqr.
          -- apply fenfa_state_eqb_sound in Hqr. subst q.
             simpl. auto.
          -- simpl. right.
             assert (Hqr_neq : q <> r).
             {
               intro Hqr_eq.
               rewrite (fenfa_state_eqb_complete m q r Hqr_eq) in Hqr.
               discriminate.
             }
             assert (Hr_state : In r (fenfa_states m)).
             { apply Htodo. simpl. auto. }
             eapply IH.
             ++ exact Hwf.
             ++ intros x Hx.
                apply in_app_or in Hx as [Hx | Hx].
                ** eapply fenfa_steps_in_states; eauto.
                ** apply Htodo. simpl. auto.
             ++ eapply enfa_fresh_epsilon_reachable_after_unseen_head; eauto.
             ++ rewrite <-
                  (enfa_epsilon_closure_work_bound_unseen_head
                     m seen r todo'
                     (fenfa_states_nodup m Hwf) Hr_state Hr_seen)
                  in Hfuel.
                lia.
  Qed.

  Lemma epsilon_simpleb_from_app_true :
    forall (m : finite_enfa) seen t u,
      epsilon_simpleb_from m seen (t ++ u) = true ->
      epsilon_simpleb_from
        m (epsilon_suffix_states m seen t) u = true.
  Proof.
    intros m seen t.
    revert seen.
    induction t as [| [[p l] q] t IH]; intros seen u Hsimple; simpl in *.
    - exact Hsimple.
    - destruct l as [a|].
      + eapply IH. exact Hsimple.
      + apply andb_true_iff in Hsimple as [_ Htail].
        eapply IH. exact Htail.
  Qed.

  Lemma valid_trace_app_inv_prefix :
    forall (m : finite_enfa) p t u r,
      valid_trace m p (t ++ u) r ->
      valid_trace m p t (trace_end p t).
  Proof.
    intros m p t.
    revert p.
    induction t as [| [[p0 l] q0] t IH]; intros p u r Hvalid; simpl.
    - constructor.
    - inversion Hvalid as [| p' l' q' r' t' Hstep Htail]; subst.
      econstructor; eauto.
  Qed.

  Lemma valid_trace_app_inv_suffix :
    forall (m : finite_enfa) p t u r,
      valid_trace m p (t ++ u) r ->
      valid_trace m (trace_end p t) u r.
  Proof.
    intros m p t.
    revert p.
    induction t as [| [[p0 l] q0] t IH]; intros p u r Hvalid; simpl in *.
    - exact Hvalid.
    - inversion Hvalid as [| p' l' q' r' t' Hstep Htail]; subst.
      eapply IH. exact Htail.
  Qed.

  Lemma epsilon_simpleb_from_no_return_to_seen :
    forall (m : finite_enfa) seen p u q,
      In q seen ->
      valid_trace m p u q ->
      trace_word u = [] ->
      epsilon_simpleb_from m seen u = true ->
      u <> [] ->
      False.
  Proof.
    intros m seen p u.
    revert seen p.
    induction u as [| [[p0 l] r] u IH]; intros seen p q Hseen Hvalid
      Hword Hsimple Hnonempty.
    - contradiction Hnonempty. reflexivity.
    - simpl in Hword.
      destruct l as [a|].
      + discriminate.
      + simpl in Hsimple.
        apply andb_true_iff in Hsimple as [Hfresh Hsimple_tail].
        inversion Hvalid as [| p' l' r' q' t' Hstep Htail]; subst.
        destruct u as [| e u'].
        * inversion Htail; subst.
          apply negb_true_iff in Hfresh.
          rewrite (state_inb_In_true m q seen Hseen) in Hfresh.
          discriminate.
        * eapply IH with (seen := r :: seen) (p := r) (q := q).
          -- simpl. auto.
          -- exact Htail.
          -- exact Hword.
          -- exact Hsimple_tail.
          -- discriminate.
  Qed.

  Lemma enfa_epsilon_trace_extends_fresh_reachable :
    forall (m : finite_enfa) seen0 seen todo p u q,
      (forall x, In x seen0 -> In x seen) ->
      enfa_fresh_epsilon_reachable m seen0 todo p ->
      valid_trace m p u q ->
      trace_word u = [] ->
      epsilon_simpleb_from m seen u = true ->
      enfa_fresh_epsilon_reachable m seen0 todo q.
  Proof.
    intros m seen0 seen todo p u q Hincl Hreach Hvalid.
    revert seen Hincl Hreach.
    induction Hvalid as [p| p l r q t Hstep _ IH];
      intros seen Hincl Hreach Hword Hsimple.
    - exact Hreach.
    - simpl in Hword.
      destruct l as [a|].
      + discriminate.
      + simpl in Hsimple.
        apply andb_true_iff in Hsimple as [Hfresh_seen Hsimple].
        apply negb_true_iff in Hfresh_seen.
        assert (Hfresh_seen0 : state_inb m r seen0 = false).
        {
          eapply state_inb_false_of_incl.
          - exact Hincl.
          - exact Hfresh_seen.
        }
        assert (Hreach_r :
          enfa_fresh_epsilon_reachable m seen0 todo r).
        { apply Fresh_epsilon_step with (p := p); auto. }
        eapply (IH (r :: seen)).
        * intros x Hx. simpl. auto.
        * exact Hreach_r.
        * exact Hword.
        * exact Hsimple.
  Qed.

  Lemma enfa_nonempty_epsilon_trace_fresh_reachable :
    forall (m : finite_enfa) seen p u q,
      valid_trace m p u q ->
      trace_word u = [] ->
      epsilon_simpleb_from m seen u = true ->
      u <> [] ->
      enfa_fresh_epsilon_reachable
        m seen
        (filter
           (fun q' => negb (state_inb m q' seen))
           (enfa_step (fenfa_base m) p None))
        q.
  Proof.
    intros m seen p u q Hvalid Hword Hsimple Hnonempty.
    inversion Hvalid as [p_nil| p' l r q' t Hstep Htail]; subst.
    - contradiction Hnonempty. reflexivity.
    - simpl in Hword.
      destruct l as [a|].
      + discriminate.
      + simpl in Hsimple.
        apply andb_true_iff in Hsimple as [Hfresh_negb Hsimple_tail].
        apply negb_true_iff in Hfresh_negb.
        assert (Hin_filter :
          In r
            (filter
               (fun q' => negb (state_inb m q' seen))
               (enfa_step (fenfa_base m) p None))).
        {
          apply filter_In. split; auto.
          now rewrite Hfresh_negb.
        }
        assert (Hreach_r :
          enfa_fresh_epsilon_reachable
            m seen
            (filter
               (fun q' => negb (state_inb m q' seen))
               (enfa_step (fenfa_base m) p None))
            r).
        { apply Fresh_epsilon_todo; auto. }
        eapply
          (enfa_epsilon_trace_extends_fresh_reachable
             m seen (r :: seen)
             (filter
                (fun q' => negb (state_inb m q' seen))
                (enfa_step (fenfa_base m) p None))
             r t q).
        * intros x Hx. simpl. auto.
        * exact Hreach_r.
        * exact Htail.
        * exact Hword.
        * exact Hsimple_tail.
  Qed.

  Lemma enfa_strict_epsilon_closure_states_complete_nonempty :
    forall (m : finite_enfa) s t u,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s (t ++ u) (trace_end s (t ++ u)) ->
      epsilon_simpleb m (s, t ++ u) = true ->
      trace_word u = [] ->
      u <> [] ->
      In (trace_end (trace_end s t) u)
         (enfa_strict_epsilon_closure_states m (s, t)).
  Proof.
    intros m s t u Hwf Hs Hvalid Hsimple Hword Hnonempty.
    assert (Hvalid_t :
      valid_trace m s t (trace_end s t)).
    { eapply valid_trace_app_inv_prefix; eauto. }
    assert (Hend_state : In (trace_end s t) (fenfa_states m)).
    { eapply finite_enfa_wf_valid_trace_end_in_states; eauto. }
    assert (Hvalid_u :
      valid_trace m (trace_end s t) u (trace_end s (t ++ u))).
    { eapply valid_trace_app_inv_suffix; eauto. }
    assert (Hsimple_u :
      epsilon_simpleb_from
        m (epsilon_suffix_states m [s] t) u = true).
    {
      unfold epsilon_simpleb in Hsimple.
      eapply epsilon_simpleb_from_app_true. exact Hsimple.
    }
    assert (Hreach :
      enfa_fresh_epsilon_reachable
        m
        (epsilon_suffix_states m [s] t)
        (filter
           (fun q' =>
              negb
                (state_inb
                   m q'
                   (epsilon_suffix_states m [s] t)))
           (enfa_step (fenfa_base m) (trace_end s t) None))
        (trace_end s (t ++ u))).
    {
      eapply enfa_nonempty_epsilon_trace_fresh_reachable.
      - exact Hvalid_u.
      - exact Hword.
      - exact Hsimple_u.
      - exact Hnonempty.
    }
    replace (trace_end (trace_end s t) u)
      with (trace_end s (t ++ u)) by now rewrite trace_end_app.
    unfold enfa_strict_epsilon_closure_states.
    simpl.
    eapply enfa_epsilon_closure_fuel_complete.
    - exact Hwf.
    - intros r Hr.
      apply filter_In in Hr as [Hr _].
      eapply fenfa_steps_in_states; eauto.
    - exact Hreach.
    - exact
        (enfa_strict_epsilon_closure_work_bound_le_transition_bound
           m (s, t) Hwf Hend_state).
  Qed.

  Lemma enfa_trace_bound_word_length :
    forall (m : finite_enfa) w,
      length w <= enfa_trace_bound m w.
  Proof.
    intros m w.
    unfold enfa_trace_bound.
    lia.
  Qed.

  Lemma enfa_trace_bound_symbol_step_arith :
    forall k n seen_len,
      seen_len <= n ->
      (k + 1) * S n + k + seen_len <=
      (S k + 1) * S n + S k.
  Proof.
    intros k n seen_len Hseen.
    replace (S k + 1) with (S (k + 1)) by lia.
    rewrite Nat.mul_succ_l.
    lia.
  Qed.

  Lemma epsilon_simpleb_from_valid_trace_length_bound :
    forall (m : finite_enfa) seen p t q,
      finite_enfa_wf m ->
      NoDup seen ->
      (forall x, In x seen -> In x (fenfa_states m)) ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      epsilon_simpleb_from m seen t = true ->
      length t + length seen <=
      (length (trace_word t) + 1) * S (length (fenfa_states m)) +
      length (trace_word t).
  Proof.
    intros m seen p t q Hwf Hseen_nodup Hseen_states Hp Htrace.
    revert seen Hseen_nodup Hseen_states Hp.
    induction Htrace as [q| p l q r t Hstep _ IH];
      intros seen Hseen_nodup Hseen_states Hp Hsimple.
    - simpl.
      assert (Hseen_len : length seen <= length (fenfa_states m)).
      {
        eapply NoDup_incl_length.
        - exact Hseen_nodup.
        - intros x Hx. apply Hseen_states. exact Hx.
      }
      lia.
    - simpl in Hsimple |- *.
      assert (Hq : In q (fenfa_states m)).
      { eapply fenfa_steps_in_states; eauto. }
      destruct l as [a|].
      + assert (Hq_seen_nodup : NoDup [q]).
        { constructor; [intros [] | constructor]. }
        assert (Hq_seen_states : forall x,
          In x [q] -> In x (fenfa_states m)).
        { intros x [Hx | []]. now subst x. }
        pose proof
          (IH [q] Hq_seen_nodup Hq_seen_states Hq Hsimple)
          as Hbound.
        assert (Hseen_len : length seen <= length (fenfa_states m)).
        {
          eapply NoDup_incl_length.
          - exact Hseen_nodup.
          - intros x Hx. apply Hseen_states. exact Hx.
        }
        simpl in Hbound.
        replace (S (length t + length seen))
          with ((length t + 1) + length seen) by lia.
        eapply Nat.le_trans
          with (m :=
            ((length (trace_word t) + 1) *
             S (length (fenfa_states m)) +
             length (trace_word t)) + length seen).
        * apply Nat.add_le_mono_r. exact Hbound.
        * apply enfa_trace_bound_symbol_step_arith.
          exact Hseen_len.
      + apply andb_true_iff in Hsimple as [Hfresh Hsimple].
        apply negb_true_iff in Hfresh.
        pose proof (state_inb_false_not_In m q seen Hfresh) as Hnotin.
        assert (Hseen' : forall x,
          In x (q :: seen) -> In x (fenfa_states m)).
        {
          intros x [Hx | Hx].
          - now subst x.
          - now apply Hseen_states.
        }
        assert (Hseen_cons_nodup : NoDup (q :: seen)).
        { constructor; auto. }
        pose proof
          (IH (q :: seen)
             Hseen_cons_nodup Hseen' Hq Hsimple) as Hbound.
        simpl in Hbound.
        replace (S (length t + length seen))
          with (length t + S (length seen)) by lia.
        exact Hbound.
  Qed.

  Lemma epsilon_simple_valid_trace_length_bound :
    forall (m : finite_enfa) s t q,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s t q ->
      epsilon_simpleb m (s, t) = true ->
      length t <= enfa_trace_bound m (trace_word t).
  Proof.
    intros m s t q Hwf Hs Htrace Hsimple.
    unfold epsilon_simpleb in Hsimple.
    pose proof
      (epsilon_simpleb_from_valid_trace_length_bound
         m [s] s t q Hwf
         ltac:(constructor; [intros [] | constructor])
         ltac:(intros x [Hx | []]; now subst x)
         Hs Htrace Hsimple) as Hbound.
    simpl in Hbound.
    unfold enfa_trace_bound.
    lia.
  Qed.

  Lemma two_distinct_in_filter_length :
    forall {B : Type} (p : B -> bool) xs x y,
      In x xs ->
      In y xs ->
      p x = true ->
      p y = true ->
      x <> y ->
      2 <= length (filter p xs).
  Proof.
    intros B p xs.
    induction xs as [| z zs IH]; intros x y Hx Hy Hpx Hpy Hneq.
    - contradiction.
    - simpl in Hx, Hy |- *.
      destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy].
      + subst. contradiction.
      + subst z.
        rewrite Hpx. simpl.
        assert (0 < length (filter p zs)).
        {
          eapply filter_length_pos_of_In; eauto.
        }
        lia.
      + subst z.
        rewrite Hpy. simpl.
        assert (0 < length (filter p zs)).
        {
          eapply filter_length_pos_of_In; eauto.
        }
        lia.
      + destruct (p z); simpl.
        * specialize (IH x y Hx Hy Hpx Hpy Hneq). lia.
        * exact (IH x y Hx Hy Hpx Hpy Hneq).
  Qed.

  Lemma NoDup_filter_ge_two :
    forall {B : Type} (p : B -> bool) xs,
      NoDup xs ->
      2 <= length (filter p xs) ->
      exists x y,
        In x xs /\ In y xs /\ x <> y /\ p x = true /\ p y = true.
  Proof.
    intros B p xs Hnodup.
    induction Hnodup as [| x xs Hnotin Hnodup IH]; simpl; intros Hlen.
    - lia.
    - destruct (p x) eqn:Hpx.
      + destruct (filter p xs) as [| y ys] eqn:Hfilter.
        * simpl in Hlen. lia.
        * assert (Hy_in_filter : In y (filter p xs)).
          { rewrite Hfilter. simpl. auto. }
          apply filter_In in Hy_in_filter as [Hy Hpy].
          exists x, y. repeat split; simpl; auto.
          intro Hxy. subst y. contradiction.
      + destruct (IH Hlen) as [y [z [Hy [Hz [Hneq [Hpy Hpz]]]]]].
        exists y, z. repeat split; simpl; auto.
  Qed.

  Lemma filter_length_le_one_unique :
    forall {B : Type} (p : B -> bool) xs x y,
      length (filter p xs) <= 1 ->
      In x xs ->
      In y xs ->
      p x = true ->
      p y = true ->
      x = y.
  Proof.
    intros B p xs.
    induction xs as [| z zs IH]; intros x y Hlen Hx Hy Hpx Hpy.
    - contradiction.
    - simpl in Hx, Hy.
      destruct (p z) eqn:Hpz.
      + simpl in Hlen. rewrite Hpz in Hlen. simpl in Hlen.
        destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy].
        * congruence.
        * subst z.
          exfalso.
          assert (0 < length (filter p zs)).
          { eapply filter_length_pos_of_In with (x := y); eauto. }
          lia.
        * subst z.
          exfalso.
          assert (0 < length (filter p zs)).
          { eapply filter_length_pos_of_In with (x := x); eauto. }
          lia.
        * assert (0 < length (filter p zs)).
          { eapply filter_length_pos_of_In with (x := x); eauto. }
          lia.
      + simpl in Hlen. rewrite Hpz in Hlen.
        destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy].
        * congruence.
        * subst z. rewrite Hpz in Hpx. discriminate.
        * subst z. rewrite Hpz in Hpy. discriminate.
        * eapply IH; eauto.
  Qed.

  Lemma filter_negb_empty_forallb :
    forall {B : Type} (p : B -> bool) xs,
      filter (fun x => negb (p x)) xs = [] ->
      forallb p xs = true.
  Proof.
    intros B p xs.
    induction xs as [| x xs IH]; simpl; intros Hfilter.
    - reflexivity.
    - destruct (p x) eqn:Hpx; simpl in Hfilter |- *.
      + now apply IH.
      + discriminate.
  Qed.

  Lemma valid_trace_in_traces_from_fuel :
    forall (m : finite_enfa) p t q fuel,
      valid_trace m p t q ->
      length t <= fuel ->
      In t (traces_from_fuel m fuel p (trace_word t)).
  Proof.
    intros m p t q fuel Htrace.
    revert fuel.
    induction Htrace as [q| p l q r t Hstep _ IH]; intros fuel Hlen.
    - destruct fuel; simpl; auto.
    - destruct fuel as [| fuel]; simpl in Hlen; [lia |].
      simpl.
      destruct l as [a|].
      + apply in_or_app. right.
        apply in_or_app. right.
        apply in_concat.
        exists
          (map (fun t0 => ((p, Some a), q) :: t0)
             (traces_from_fuel m fuel q (trace_word t))).
        split.
        * apply in_map_iff. exists q. split; [reflexivity | exact Hstep].
        * apply in_map_iff.
          exists t. split; [reflexivity |].
          apply IH. lia.
      + destruct (trace_word t) as [| a w] eqn:Hword.
        * right. simpl. rewrite app_nil_r. simpl.
          apply in_concat.
          exists
            (map (fun t0 => ((p, None), q) :: t0)
               (traces_from_fuel m fuel q [])).
          split.
          -- apply in_map_iff. exists q. split; [reflexivity | exact Hstep].
          -- apply in_map_iff.
             exists t. split; [reflexivity |].
             apply IH. lia.
        * apply in_or_app. right.
          apply in_or_app. left.
          apply in_concat.
          exists
            (map (fun t0 => ((p, None), q) :: t0)
               (traces_from_fuel m fuel q (a :: w))).
          split.
          -- apply in_map_iff. exists q. split; [reflexivity | exact Hstep].
          -- apply in_map_iff.
             exists t. split; [reflexivity |].
             apply IH. lia.
  Qed.

  Lemma started_traces_start_in :
    forall (m : finite_enfa) w s t,
      In (s, t) (started_traces m w) ->
      In s (enfa_start (fenfa_base m)).
  Proof.
    intros m w s t Hin.
    unfold started_traces in Hin.
    apply in_concat in Hin as [ts [Hts Ht]].
    apply in_map_iff in Hts as [s' [Hts Hs']].
    subst ts.
    apply in_map_iff in Ht as [t' [Hst _]].
    inversion Hst; subst. exact Hs'.
  Qed.

  Lemma started_traces_trace_in :
    forall (m : finite_enfa) w s t,
      In (s, t) (started_traces m w) ->
      In t (traces_from_fuel m (enfa_trace_bound m w) s w).
  Proof.
    intros m w s t Hin.
    unfold started_traces in Hin.
    apply in_concat in Hin as [ts [Hts Ht]].
    apply in_map_iff in Hts as [s' [Hts _]].
    subst ts.
    apply in_map_iff in Ht as [t' [Hst Ht']].
    inversion Hst; subst. exact Ht'.
  Qed.

  Lemma started_traces_valid :
    forall (m : finite_enfa) w s t,
      In (s, t) (started_traces m w) ->
      valid_trace m s t (trace_end s t) /\ trace_word t = w.
  Proof.
    intros m w s t Hin.
    eapply traces_from_fuel_valid.
    now apply started_traces_trace_in.
  Qed.

  Theorem enfa_dra_prime_at_traces_fiber_maximal :
    forall (m : finite_enfa) w q st,
      In st (started_traces m w) ->
      ends_inb m q st = true ->
      epsilon_simpleb m st = true ->
      enfa_reach_fiber_maximal m w q st.
  Proof.
    intros m w q [s t] _ Hend _ st' u Hst' Hin' Hend' Hsimple' Hword_u.
    subst st'.
    destruct u as [| e u'].
    - simpl. now rewrite app_nil_r.
    - exfalso.
      assert (Hq_seen : In q (epsilon_suffix_states m [s] t)).
      {
        unfold ends_inb, started_end in Hend.
        simpl in Hend.
        apply fenfa_state_eqb_sound in Hend.
        subst q.
        apply trace_end_in_epsilon_suffix_states.
        simpl. auto.
      }
      destruct (started_traces_valid m w s (t ++ e :: u') Hin')
        as [Hvalid' _].
      assert (Hend_eq : trace_end s (t ++ e :: u') = q).
      {
        unfold ends_inb, started_end in Hend'.
        simpl in Hend'.
        now apply fenfa_state_eqb_sound in Hend'.
      }
      assert (Hvalid_u :
        valid_trace m (trace_end s t) (e :: u') q).
      {
        pose proof
          (valid_trace_app_inv_suffix
             m s t (e :: u') (trace_end s (t ++ e :: u')) Hvalid')
          as Hsuffix.
        now rewrite Hend_eq in Hsuffix.
      }
      assert (Hsimple_u :
        epsilon_simpleb_from m (epsilon_suffix_states m [s] t) (e :: u') =
        true).
      {
        unfold epsilon_simpleb in Hsimple'.
        eapply epsilon_simpleb_from_app_true. exact Hsimple'.
      }
      eapply epsilon_simpleb_from_no_return_to_seen; eauto.
      discriminate.
  Qed.

  Lemma started_traces_length_bound :
    forall (m : finite_enfa) w s t,
      In (s, t) (started_traces m w) ->
      length t <= enfa_trace_bound m w.
  Proof.
    intros m w s t Hin.
    eapply traces_from_fuel_length_le_fuel with (w := w) (p := s).
    now apply started_traces_trace_in.
  Qed.

  Lemma started_traces_single_start_NoDup :
    forall (m : finite_enfa) s w,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      NoDup (started_traces m w).
  Proof.
    intros m s w Hwf Hstart.
    unfold started_traces.
    rewrite Hstart. simpl. rewrite app_nil_r.
    apply NoDup_map_injective_in.
    - intros t1 t2 _ _ Heq. inversion Heq. reflexivity.
    - apply traces_from_fuel_NoDup; auto.
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
  Qed.

  Definition enfa_started_traces_nodup (m : finite_enfa) : Prop :=
    forall w, NoDup (started_traces m w).

  Theorem section4_enfa_started_traces_nodup_single_start :
    forall (m : finite_enfa) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_started_traces_nodup m.
  Proof.
    intros m s Hwf Hstart w.
    eapply started_traces_single_start_NoDup; eauto.
  Qed.

  Lemma started_epsilon_simple_trace_length_bound :
    forall (m : finite_enfa) w st,
      In st (started_traces m w) ->
      epsilon_simpleb m st = true ->
      length (snd st) <= enfa_trace_bound m w.
  Proof.
    intros m w [s t] Hin _.
    now eapply (started_traces_length_bound m w s t).
  Qed.

  Lemma started_traces_end_in_states :
    forall (m : finite_enfa) w st,
      finite_enfa_wf m ->
      In st (started_traces m w) ->
      In (started_end st) (fenfa_states m).
  Proof.
    intros m w [s t] Hwf Hin.
    unfold started_end; simpl.
    destruct (started_traces_valid m w s t Hin) as [Hvalid _].
    eapply finite_enfa_wf_valid_trace_end_in_states; eauto.
    eapply fenfa_starts_in_states; eauto.
    now apply started_traces_start_in with (w := w) (t := t).
  Qed.

  Lemma valid_started_trace_in_started_traces :
    forall (m : finite_enfa) s t q w,
      In s (enfa_start (fenfa_base m)) ->
      valid_trace m s t q ->
      trace_word t = w ->
      length t <= enfa_trace_bound m w ->
      In (s, t) (started_traces m w).
  Proof.
    intros m s t q w Hstart Hvalid Hword Hlen.
    unfold started_traces.
    apply in_concat.
    exists
      (map (fun t0 => (s, t0))
         (traces_from_fuel m (enfa_trace_bound m w) s w)).
    split.
    - apply in_map_iff. exists s. split; [reflexivity | exact Hstart].
    - apply in_map_iff. exists t. split; [reflexivity |].
      rewrite <- Hword.
      apply valid_trace_in_traces_from_fuel with (q := q).
      + exact Hvalid.
      + rewrite Hword. exact Hlen.
  Qed.

  Definition enfa_prime_trace_enumerated_from
      (m : finite_enfa)
      (s : enfa_state (fenfa_base m)) : Prop :=
    forall w q t,
      valid_trace m s t q ->
      trace_word t = w ->
      epsilon_simpleb m (s, t) = true ->
      In (s, t) (started_traces m w).

  Theorem section4_enfa_prime_trace_enumerated_from_single_start :
    forall (m : finite_enfa) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s.
  Proof.
    intros m s Hwf Hstart w q t Htrace Hword Hsimple.
    assert (Hs : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
    }
    eapply valid_started_trace_in_started_traces with (q := q).
    - rewrite Hstart. simpl. auto.
    - exact Htrace.
    - exact Hword.
    - rewrite <- Hword.
      eapply epsilon_simple_valid_trace_length_bound; eauto.
  Qed.

  Fixpoint enfa_extend_to_maximal_epsilon_fuel
      (m : finite_enfa)
      (fuel : nat)
      (s : enfa_state (fenfa_base m))
      (t : enfa_trace m) : enfa_trace m :=
    match fuel with
    | O => t
    | S fuel' =>
        let seen := epsilon_suffix_states m [s] t in
        let q := trace_end s t in
        match
          filter
            (fun q' => negb (state_inb m q' seen))
            (enfa_step (fenfa_base m) q None)
        with
        | [] => t
        | q' :: _ =>
            enfa_extend_to_maximal_epsilon_fuel
              m fuel' s (t ++ [((q, None), q')])
        end
    end.

  Definition enfa_extend_to_maximal_epsilon_trace
      (m : finite_enfa)
      (s : enfa_state (fenfa_base m))
      (t : enfa_trace m) : enfa_trace m :=
    enfa_extend_to_maximal_epsilon_fuel
      m (S (enfa_trace_bound m (trace_word t))) s t.

  Definition enfa_extend_to_maximal_epsilon_started
      (m : finite_enfa)
      (st : started_trace m) : started_trace m :=
    (fst st,
     enfa_extend_to_maximal_epsilon_trace m (fst st) (snd st)).

  Lemma enfa_extend_to_maximal_epsilon_fuel_correct :
    forall (m : finite_enfa) fuel s t,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s t (trace_end s t) ->
      epsilon_simpleb m (s, t) = true ->
      length t + fuel > enfa_trace_bound m (trace_word t) ->
      let t' := enfa_extend_to_maximal_epsilon_fuel m fuel s t in
      valid_trace m s t' (trace_end s t') /\
      trace_word t' = trace_word t /\
      epsilon_simpleb m (s, t') = true /\
      maximal_epsilon_simpleb m (s, t') = true /\
      exists u,
        t' = t ++ u /\
        trace_word u = [].
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros s t Hwf Hs Hvalid Hsimple Hfuel;
      simpl.
    - exfalso.
      pose proof
        (epsilon_simple_valid_trace_length_bound
           m s t (trace_end s t) Hwf Hs Hvalid Hsimple) as Hbound.
      lia.
    - set (seen := epsilon_suffix_states m [s] t).
      set (q := trace_end s t).
      destruct
        (filter
           (fun q' => negb (state_inb m q' seen))
           (enfa_step (fenfa_base m) q None))
        as [| q' fresh] eqn:Hfreshes.
      + repeat split; auto.
        * unfold maximal_epsilon_simpleb.
          fold seen q.
          now apply filter_negb_empty_forallb.
        * exists []. now rewrite app_nil_r.
      + assert (Hq'_fresh :
          negb (state_inb m q' seen) = true).
        {
          assert (Hin_filter : In q' (q' :: fresh)).
          { simpl; auto. }
          rewrite <- Hfreshes in Hin_filter.
          apply filter_In in Hin_filter as [_ Hfresh].
          exact Hfresh.
        }
        assert (Hq'_step : In q' (enfa_step (fenfa_base m) q None)).
        {
          assert (Hin_filter : In q' (q' :: fresh)).
          { simpl; auto. }
          rewrite <- Hfreshes in Hin_filter.
          apply filter_In in Hin_filter as [Hstep _].
          exact Hstep.
        }
        apply negb_true_iff in Hq'_fresh.
        set (t1 := t ++ [((q, None), q')]).
        assert (Hvalid1 : valid_trace m s t1 (trace_end s t1)).
        {
          unfold t1, q.
          rewrite trace_end_app. simpl.
          apply valid_trace_app_edge; auto.
        }
        assert (Hword1 : trace_word t1 = trace_word t).
        { unfold t1. rewrite trace_word_app. simpl. now rewrite app_nil_r. }
        assert (Hsimple1 : epsilon_simpleb m (s, t1) = true).
        {
          unfold t1, epsilon_simpleb.
          apply epsilon_simpleb_from_app_none.
          - exact Hsimple.
          - exact Hq'_fresh.
        }
        assert (Hfuel1 :
          length t1 + fuel > enfa_trace_bound m (trace_word t1)).
        {
          rewrite Hword1.
          unfold t1. rewrite length_app. simpl. lia.
        }
        destruct
          (IH s t1 Hwf Hs Hvalid1 Hsimple1 Hfuel1)
          as [Hvalid' [Hword' [Hsimple' [Hmax' [u [Hu Huw]]]]]].
        repeat split; auto.
        * rewrite Hword'. exact Hword1.
        * exists (((q, None), q') :: u).
          split.
          -- rewrite Hu. unfold t1.
             change (t ++ (((q, None), q') :: u))
               with (t ++ [((q, None), q')] ++ u).
             now rewrite <- app_assoc.
          -- simpl. exact Huw.
  Qed.

  Lemma enfa_extend_to_maximal_epsilon_started_correct :
    forall (m : finite_enfa) w st,
      finite_enfa_wf m ->
      In st (started_traces m w) ->
      epsilon_simpleb m st = true ->
      let st' := enfa_extend_to_maximal_epsilon_started m st in
      In st' (started_traces m w) /\
      fst st' = fst st /\
      exists u,
        snd st' = snd st ++ u /\
        trace_word u = [] /\
        epsilon_simpleb m st' = true /\
        maximal_epsilon_simpleb m st' = true.
  Proof.
    intros m w [s t] Hwf Hin Hsimple.
    simpl.
    destruct (started_traces_valid m w s t Hin) as [Hvalid Hword].
    assert (Hs_state : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      now eapply started_traces_start_in; eauto.
    }
    pose proof
      (enfa_extend_to_maximal_epsilon_fuel_correct
         m (S (enfa_trace_bound m (trace_word t))) s t
         Hwf Hs_state Hvalid Hsimple) as Hextend.
    assert (Hfuel :
      length t + S (enfa_trace_bound m (trace_word t)) >
      enfa_trace_bound m (trace_word t)) by lia.
    specialize (Hextend Hfuel).
    set (t_ext :=
           enfa_extend_to_maximal_epsilon_fuel
             m (S (enfa_trace_bound m (trace_word t))) s t) in *.
    destruct Hextend as
      [Hvalid' [Hword' [Hsimple' [Hmax' [u [Hu Huw]]]]]].
    refine (conj _ (conj _ _)).
    - eapply valid_started_trace_in_started_traces with
        (q := trace_end s
                (enfa_extend_to_maximal_epsilon_trace m s t)).
      + now eapply started_traces_start_in; eauto.
      + unfold enfa_extend_to_maximal_epsilon_trace.
        change
          (valid_trace m s t_ext (trace_end s t_ext)).
        exact Hvalid'.
      + unfold enfa_extend_to_maximal_epsilon_trace.
        change (trace_word t_ext = w).
        exact (eq_trans Hword' Hword).
      + pose proof
          (epsilon_simple_valid_trace_length_bound
             m s t_ext (trace_end s t_ext)
             Hwf Hs_state Hvalid' Hsimple') as Hlen'.
        unfold enfa_extend_to_maximal_epsilon_trace. simpl.
        change (length t_ext <= enfa_trace_bound m w).
        assert (Hbound_eq :
          enfa_trace_bound m (trace_word t_ext) =
          enfa_trace_bound m w).
        {
          exact
            (eq_trans
               (f_equal (enfa_trace_bound m) Hword')
               (f_equal (enfa_trace_bound m) Hword)).
        }
        eapply Nat.le_trans.
        * exact Hlen'.
        * now apply Nat.eq_le_incl.
    - reflexivity.
    - refine (ex_intro _ u (conj _ (conj Huw (conj _ _)))).
      + unfold enfa_extend_to_maximal_epsilon_trace.
        change (t_ext = t ++ u).
        exact Hu.
      + unfold enfa_extend_to_maximal_epsilon_trace.
        change (epsilon_simpleb m (s, t_ext) = true).
        exact Hsimple'.
      + unfold enfa_extend_to_maximal_epsilon_trace.
        change (maximal_epsilon_simpleb m (s, t_ext) = true).
        exact Hmax'.
  Qed.

  Definition enfa_accepting_maximal_extension_injective
      (m : finite_enfa) : Prop :=
    forall w st1 st2,
      In st1 (started_traces m w) ->
      In st2 (started_traces m w) ->
      accepted_traceb m st1 = true ->
      accepted_traceb m st2 = true ->
      epsilon_simpleb m st1 = true ->
      epsilon_simpleb m st2 = true ->
      enfa_accepting_maximal_epsilon_simpleb m st1 = true ->
      enfa_accepting_maximal_epsilon_simpleb m st2 = true ->
      enfa_extend_to_maximal_epsilon_started m st1 =
      enfa_extend_to_maximal_epsilon_started m st2 ->
      st1 = st2.

  Lemma NoDup_filter_bool :
    forall {B : Type} (p : B -> bool) xs,
      NoDup xs ->
      NoDup (filter p xs).
  Proof.
    intros B p xs Hnodup.
    induction Hnodup as [| x xs Hnotin Hnodup IH]; simpl.
    - constructor.
    - destruct (p x) eqn:Hpx.
      + constructor.
        * intro Hin.
          apply filter_In in Hin as [Hin _].
          contradiction.
        * exact IH.
      + exact IH.
  Qed.

  Lemma enfa_final_states_nodup :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      NoDup (enfa_final_states m).
  Proof.
    intros m Hwf.
    unfold enfa_final_states.
    apply NoDup_filter_bool.
    exact (fenfa_states_nodup m Hwf).
  Qed.

  Lemma accepted_traceb_of_final_endpoint :
    forall (m : finite_enfa) q st,
      In q (enfa_final_states m) ->
      ends_inb m q st = true ->
      accepted_traceb m st = true.
  Proof.
    intros m q st Hq Hend.
    unfold enfa_final_states in Hq.
    apply filter_In in Hq as [_ Hfinal].
    unfold ends_inb in Hend.
    apply fenfa_state_eqb_sound in Hend.
    unfold accepted_traceb.
    now rewrite Hend.
  Qed.

  Definition enfa_accepting_maximal_started_traceb
      (m : finite_enfa)
      (st : started_trace m) : bool :=
    (accepted_traceb m st && epsilon_simpleb m st) &&
    enfa_accepting_maximal_epsilon_simpleb m st.

  Definition enfa_leaf_prime_started_traceb
      (m : finite_enfa)
      (st : started_trace m) : bool :=
    epsilon_simpleb m st && maximal_epsilon_simpleb m st.

  Lemma filter_concat_map_length_sum :
    forall {B C : Type} (p : C -> bool) (f : B -> list C) xs,
      length (filter p (concat (map f xs))) =
      sum_nats (map (fun x => length (filter p (f x))) xs).
  Proof.
    intros B C p f xs.
    induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - rewrite filter_app, length_app, IH. reflexivity.
  Qed.

  Theorem enfa_dra_prime_at_sum_between_starts :
    forall (m : finite_enfa) w q,
      enfa_dra_prime_at m w q =
      sum_nats
        (map
           (fun s => enfa_dra_prime_between m s w q)
           (enfa_start (fenfa_base m))).
  Proof.
    intros m w q.
    unfold enfa_dra_prime_at, enfa_dra_prime_between,
      started_traces, started_traces_from_start.
    rewrite filter_concat_map_length_sum.
    reflexivity.
  Qed.

  Theorem enfa_stUFA_single_start_implies_reachufa :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_stUFA m ->
      enfa_ReachUFA m.
  Proof.
    intros m Hwf Hsingle Hst w q Hq.
    rewrite enfa_dra_prime_at_sum_between_starts.
    destruct (enfa_start (fenfa_base m)) as [| s starts] eqn:Hstarts.
    - simpl. lia.
    - destruct starts as [| s' starts].
      + simpl.
        assert (Hs : In s (fenfa_states m)).
        {
          eapply fenfa_starts_in_states; eauto.
          rewrite Hstarts. simpl. auto.
        }
        pose proof (Hst s q w Hs Hq) as Hbetween.
        lia.
      + exfalso.
        unfold enfa_single_start in Hsingle.
        rewrite Hstarts in Hsingle. simpl in Hsingle. lia.
  Qed.

  Theorem enfa_epsilon_free_single_start_stufa_implies_sufa :
    forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_stUFA m ->
      enfa_SUFA m.
  Proof.
    intros m Heps Hwf Hsingle Hst.
    split.
    - exact Heps.
    - eapply enfa_stUFA_single_start_implies_reachufa; eauto.
  Qed.

  Lemma sum_endpoint_counts_eq_filter_state_inb :
    forall (m : finite_enfa) (p : started_trace m -> bool) qs xs,
      NoDup qs ->
      sum_nats
        (map
           (fun q : enfa_state (fenfa_base m) =>
              length
                (filter
                   (fun st : started_trace m =>
                      ends_inb m q st && p st) xs)) qs) =
      length
        (filter
           (fun st : started_trace m =>
              state_inb m (started_end st) qs && p st) xs).
  Proof.
    intros m p qs xs Hnodup.
    induction Hnodup as [| q qs Hnotin Hnodup IHqs].
    - simpl.
      induction xs as [| st xs IH]; simpl; auto.
    - simpl.
      rewrite IHqs.
      clear IHqs.
      induction xs as [| st xs IH]; simpl.
      + reflexivity.
      + destruct (p st) eqn:Hp.
        * destruct (ends_inb m q st) eqn:Hend.
          -- apply fenfa_state_eqb_sound in Hend.
             subst q.
             assert (Hnotinb :
               state_inb m (started_end st) qs = false).
             { apply state_inb_not_In_false. exact Hnotin. }
             rewrite Hnotinb.
             rewrite (fenfa_state_eqb_complete
                        m (started_end st) (started_end st) eq_refl).
             simpl. rewrite IH. reflexivity.
          -- assert (Hback :
               fenfa_state_eqb m (started_end st) q = false).
             {
               destruct (fenfa_state_eqb m (started_end st) q) eqn:Hback; auto.
               apply fenfa_state_eqb_sound in Hback.
               subst q.
               unfold ends_inb in Hend.
               rewrite (fenfa_state_eqb_complete
                          m (started_end st) (started_end st) eq_refl)
                 in Hend.
               discriminate.
             }
             rewrite Hback. simpl.
             destruct (state_inb m (started_end st) qs); simpl;
               lia.
        * destruct (ends_inb m q st);
            destruct (fenfa_state_eqb m (started_end st) q);
            destruct (state_inb m (started_end st) qs);
            simpl; exact IH.
  Qed.

  Lemma state_inb_final_states :
    forall (m : finite_enfa) q,
      In q (fenfa_states m) ->
      state_inb m q (enfa_final_states m) =
      enfa_final (fenfa_base m) q.
  Proof.
    intros m q Hq.
    unfold enfa_final_states.
    destruct (enfa_final (fenfa_base m) q) eqn:Hfinal.
    - apply state_inb_In_true.
      apply filter_In. split; auto.
    - apply state_inb_not_In_false.
      intro Hin.
      apply filter_In in Hin as [_ Hfin].
      rewrite Hfinal in Hfin. discriminate.
  Qed.

  Lemma enfa_da_prime_word_flat :
    forall (m : finite_enfa) w,
      finite_enfa_wf m ->
      enfa_da_prime_word m w =
      length
        (filter
           (enfa_accepting_maximal_started_traceb m)
           (started_traces m w)).
  Proof.
    intros m w Hwf.
    unfold enfa_da_prime_word, enfa_accepting_maximal_simple_reach_count.
    replace
      (sum_nats
         (map
            (fun q : enfa_state (fenfa_base m) =>
               length
                 (filter
                    (fun st : started_trace m =>
                       (ends_inb m q st && epsilon_simpleb m st) &&
                       enfa_accepting_maximal_epsilon_simpleb m st)
                    (started_traces m w))) (enfa_final_states m)))
      with
      (sum_nats
         (map
            (fun q : enfa_state (fenfa_base m) =>
               length
                 (filter
                    (fun st : started_trace m =>
                       ends_inb m q st &&
                       (epsilon_simpleb m st &&
                        enfa_accepting_maximal_epsilon_simpleb m st))
                    (started_traces m w))) (enfa_final_states m))).
    2:{
      induction (enfa_final_states m) as [| q qs IH]; simpl.
      - reflexivity.
      - f_equal; auto.
        f_equal.
        apply filter_ext.
        intros st.
        now rewrite Bool.andb_assoc.
    }
    rewrite
      (sum_endpoint_counts_eq_filter_state_inb
         m
         (fun st : started_trace m =>
            epsilon_simpleb m st &&
            enfa_accepting_maximal_epsilon_simpleb m st)
         (enfa_final_states m)
         (started_traces m w)
         (enfa_final_states_nodup m Hwf)).
    apply f_equal.
    apply filter_ext_in.
    intros st Hin.
    unfold enfa_accepting_maximal_started_traceb.
    assert (Hend : In (started_end st) (fenfa_states m)).
    { eapply started_traces_end_in_states; eauto. }
    rewrite state_inb_final_states by exact Hend.
    unfold accepted_traceb.
    destruct (enfa_final (fenfa_base m) (started_end st));
      destruct (epsilon_simpleb m st);
      destruct (enfa_accepting_maximal_epsilon_simpleb m st);
      reflexivity.
  Qed.

  Lemma enfa_leaf_prime_word_flat :
    forall (m : finite_enfa) w,
      finite_enfa_wf m ->
      enfa_leaf_prime_word m w =
      length
        (filter
           (enfa_leaf_prime_started_traceb m)
           (started_traces m w)).
  Proof.
    intros m w Hwf.
    unfold enfa_leaf_prime_word, enfa_maximal_simple_reach_count.
    replace
      (sum_nats
         (map
            (fun q : enfa_state (fenfa_base m) =>
               length
                 (filter
                    (fun st : started_trace m =>
                       (ends_inb m q st && epsilon_simpleb m st) &&
                       maximal_epsilon_simpleb m st)
                    (started_traces m w))) (fenfa_states m)))
      with
      (sum_nats
         (map
            (fun q : enfa_state (fenfa_base m) =>
               length
                 (filter
                    (fun st : started_trace m =>
                       ends_inb m q st &&
                       (epsilon_simpleb m st &&
                        maximal_epsilon_simpleb m st))
                    (started_traces m w))) (fenfa_states m))).
    2:{
      induction (fenfa_states m) as [| q qs IH]; simpl.
      - reflexivity.
      - f_equal; auto.
        f_equal.
        apply filter_ext.
        intros st.
        now rewrite Bool.andb_assoc.
    }
    rewrite
      (sum_endpoint_counts_eq_filter_state_inb
         m
         (fun st : started_trace m =>
            epsilon_simpleb m st && maximal_epsilon_simpleb m st)
         (fenfa_states m)
         (started_traces m w)
         (fenfa_states_nodup m Hwf)).
    apply f_equal.
    apply filter_ext_in.
    intros st Hin.
    unfold enfa_leaf_prime_started_traceb.
    assert (Hend : In (started_end st) (fenfa_states m)).
    { eapply started_traces_end_in_states; eauto. }
    rewrite (state_inb_In_true m (started_end st) (fenfa_states m) Hend).
    reflexivity.
  Qed.

  Lemma started_traces_from_start_NoDup :
    forall (m : finite_enfa) s w,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      NoDup (started_traces_from_start m s w).
  Proof.
    intros m s w Hwf Hs.
    unfold started_traces_from_start.
    apply NoDup_map_injective_in.
    - intros t1 t2 _ _ H.
      inversion H. reflexivity.
    - now apply traces_from_fuel_NoDup.
  Qed.

  Lemma started_traces_from_start_in_started_traces :
    forall (m : finite_enfa) s w st,
      In s (enfa_start (fenfa_base m)) ->
      In st (started_traces_from_start m s w) ->
      In st (started_traces m w).
  Proof.
    intros m s w st Hstart Hin.
    unfold started_traces, started_traces_from_start in *.
    apply in_concat.
    exists
      (map (fun t => (s, t))
         (traces_from_fuel m (enfa_trace_bound m w) s w)).
    split.
    - apply in_map_iff. exists s. split; [reflexivity | exact Hstart].
    - exact Hin.
  Qed.

  Lemma valid_started_trace_in_started_traces_from_start :
    forall (m : finite_enfa) s t q w,
      valid_trace m s t q ->
      trace_word t = w ->
      length t <= enfa_trace_bound m w ->
      In (s, t) (started_traces_from_start m s w).
  Proof.
    intros m s t q w Hvalid Hword Hlen.
    unfold started_traces_from_start.
    apply in_map_iff.
    exists t. split; [reflexivity |].
    rewrite <- Hword.
    eapply valid_trace_in_traces_from_fuel; eauto.
    now rewrite Hword.
  Qed.

  Lemma enfa_extend_to_maximal_epsilon_started_in_start_slice :
    forall (m : finite_enfa) s w st,
      finite_enfa_wf m ->
      In s (enfa_start (fenfa_base m)) ->
      In st (started_traces_from_start m s w) ->
      epsilon_simpleb m st = true ->
      In (enfa_extend_to_maximal_epsilon_started m st)
         (started_traces_from_start m s w) /\
      enfa_leaf_prime_started_traceb m
        (enfa_extend_to_maximal_epsilon_started m st) = true.
  Proof.
    intros m s w [s0 t] Hwf Hstart Hin Hsimple.
    unfold started_traces_from_start in Hin.
    apply in_map_iff in Hin as [t0 [Hst Hin_t0]].
    inversion Hst; subst s0 t0; clear Hst.
    assert (Hin_global : In (s, t) (started_traces m w)).
    {
      eapply started_traces_from_start_in_started_traces.
      - exact Hstart.
      - unfold started_traces_from_start.
        apply in_map_iff. exists t. split; [reflexivity | exact Hin_t0].
    }
    destruct
      (enfa_extend_to_maximal_epsilon_started_correct
         m w (s, t) Hwf Hin_global Hsimple)
      as [Hin_ext [_ [u [Hu [Huw [Hsimple_ext Hmax_ext]]]]]].
    split.
    - destruct (enfa_extend_to_maximal_epsilon_started m (s, t))
        as [s_ext t_ext] eqn:Hext.
      simpl in Hext.
      inversion Hext; subst s_ext.
      destruct (started_traces_valid m w s t Hin_global) as [_ Hword].
      destruct (started_traces_valid m w s t_ext Hin_ext) as
        [Hvalid_ext Hword_ext].
      eapply valid_started_trace_in_started_traces_from_start
        with (q := trace_end s t_ext).
      + rewrite H1. exact Hvalid_ext.
      + rewrite H1. exact Hword_ext.
      + rewrite H1. eapply started_traces_length_bound; eauto.
    - unfold enfa_leaf_prime_started_traceb.
      now rewrite Hsimple_ext, Hmax_ext.
  Qed.

  Lemma enfa_accepting_maximal_slice_le_leaf_under_extension_injective :
    forall (m : finite_enfa) s w,
      finite_enfa_wf m ->
      In s (enfa_start (fenfa_base m)) ->
      enfa_accepting_maximal_extension_injective m ->
      length
        (filter
           (enfa_accepting_maximal_started_traceb m)
           (started_traces_from_start m s w)) <=
      length
        (filter
           (enfa_leaf_prime_started_traceb m)
           (started_traces_from_start m s w)).
  Proof.
    intros m s w Hwf Hstart Hinj.
    set (src :=
      filter
        (enfa_accepting_maximal_started_traceb m)
        (started_traces_from_start m s w)).
    set (dst :=
      filter
        (enfa_leaf_prime_started_traceb m)
        (started_traces_from_start m s w)).
    assert (Hs : In s (fenfa_states m)).
    { eapply fenfa_starts_in_states; eauto. }
    assert (Hsrc_nodup : NoDup src).
    {
      unfold src.
      apply NoDup_filter_bool.
      now apply started_traces_from_start_NoDup.
    }
    assert (Hmap_nodup :
      NoDup (map (enfa_extend_to_maximal_epsilon_started m) src)).
    {
      apply NoDup_map_injective_in.
      - intros st1 st2 Hst1 Hst2 Heq.
        unfold src in Hst1, Hst2.
        apply filter_In in Hst1 as [Hin1 Hacc1].
        apply filter_In in Hst2 as [Hin2 Hacc2].
        unfold enfa_accepting_maximal_started_traceb in Hacc1, Hacc2.
        apply andb_true_iff in Hacc1 as [Hacc1 Haccmax1].
        apply andb_true_iff in Hacc2 as [Hacc2 Haccmax2].
        apply andb_true_iff in Hacc1 as [Haccepted1 Heps1].
        apply andb_true_iff in Hacc2 as [Haccepted2 Heps2].
        eapply Hinj with (w := w); eauto.
        + eapply started_traces_from_start_in_started_traces; eauto.
        + eapply started_traces_from_start_in_started_traces; eauto.
      - exact Hsrc_nodup.
    }
    assert (Hincl :
      incl (map (enfa_extend_to_maximal_epsilon_started m) src) dst).
    {
      intros st_ext Hst_ext.
      apply in_map_iff in Hst_ext as [st [Hext Hst]].
      subst st_ext.
      unfold src in Hst.
      apply filter_In in Hst as [Hin Hacc].
      unfold enfa_accepting_maximal_started_traceb in Hacc.
      apply andb_true_iff in Hacc as [Hacc Haccmax].
      apply andb_true_iff in Hacc as [_ Heps].
      destruct
        (enfa_extend_to_maximal_epsilon_started_in_start_slice
           m s w st Hwf Hstart Hin Heps) as [Hin_ext Hleaf_ext].
      unfold dst.
      apply filter_In. split; auto.
    }
    pose proof (NoDup_incl_length Hmap_nodup Hincl) as Hle.
    unfold src, dst in *.
    rewrite length_map in Hle.
    exact Hle.
  Qed.

  Lemma enfa_accepting_maximal_concat_slices_le_leaf_under_extension_injective :
    forall (m : finite_enfa) starts w,
      finite_enfa_wf m ->
      (forall s, In s starts -> In s (enfa_start (fenfa_base m))) ->
      enfa_accepting_maximal_extension_injective m ->
      sum_nats
        (map
           (fun s =>
              length
                (filter
                   (enfa_accepting_maximal_started_traceb m)
                   (started_traces_from_start m s w))) starts) <=
      sum_nats
        (map
           (fun s =>
              length
                (filter
                   (enfa_leaf_prime_started_traceb m)
                   (started_traces_from_start m s w))) starts).
  Proof.
    intros m starts w Hwf Hstarts Hinj.
    induction starts as [| s starts IH]; simpl.
    - lia.
    - assert (Hs_start : In s (enfa_start (fenfa_base m))).
      { apply Hstarts. simpl. auto. }
      pose proof
        (enfa_accepting_maximal_slice_le_leaf_under_extension_injective
           m s w Hwf Hs_start Hinj) as Hhead.
      assert (Htail :
        sum_nats
          (map
             (fun s0 =>
                length
                  (filter
                     (enfa_accepting_maximal_started_traceb m)
                     (started_traces_from_start m s0 w))) starts) <=
        sum_nats
          (map
             (fun s0 =>
                length
                  (filter
                     (enfa_leaf_prime_started_traceb m)
                     (started_traces_from_start m s0 w))) starts)).
      {
        apply IH.
        intros s0 Hs0. apply Hstarts. simpl. auto.
      }
      lia.
  Qed.

  Theorem section4_enfa_accepting_maximal_da_bounded_by_leaf_under_extension_injective :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_accepting_maximal_extension_injective m ->
      enfa_accepting_maximal_da_bounded_by_leaf m.
  Proof.
    intros m Hwf Hinj w.
    rewrite enfa_da_prime_word_flat by exact Hwf.
    rewrite enfa_leaf_prime_word_flat by exact Hwf.
    unfold started_traces.
    change
      (concat
         (map
            (fun s : enfa_state (fenfa_base m) =>
               started_traces_from_start m s w)
            (enfa_start (fenfa_base m))))
      with
      (concat
         (map
            (fun s : enfa_state (fenfa_base m) =>
               map (fun t => (s, t))
                 (traces_from_fuel m (enfa_trace_bound m w) s w))
            (enfa_start (fenfa_base m)))).
    repeat rewrite filter_concat_map_length_sum.
    apply
      enfa_accepting_maximal_concat_slices_le_leaf_under_extension_injective;
      auto.
  Qed.

  Lemma app_eq_prefix_cases :
    forall {B : Type} (xs ys zs ws : list B),
      xs ++ zs = ys ++ ws ->
      (exists v, ys = xs ++ v /\ zs = v ++ ws) \/
      (exists v, xs = ys ++ v /\ ws = v ++ zs).
  Proof.
    intros B xs.
    induction xs as [| x xs IH]; intros ys zs ws H.
    - left. exists ys. simpl in H. split; auto.
    - destruct ys as [| y ys].
      + right. exists (x :: xs). simpl in H.
        split; [reflexivity | symmetry; exact H].
      + simpl in H.
        injection H as Hxy Htail.
        subst y.
        destruct (IH ys zs ws Htail) as
          [[v [Hys Hzs]] | [v [Hxs Hws]]].
        * left. exists v. split; simpl; congruence.
        * right. exists v. split; simpl; congruence.
  Qed.

  Lemma trace_word_suffix_nil_of_same_word :
    forall (m : finite_enfa) (t v : enfa_trace m) w,
      trace_word t = w ->
      trace_word (t ++ v) = w ->
      trace_word v = [].
  Proof.
    intros m t v w Ht Htv.
    rewrite trace_word_app in Htv.
    rewrite Ht in Htv.
    replace w with (w ++ []) in Htv at 2 by apply app_nil_r.
    now apply app_inv_head in Htv.
  Qed.

  Lemma enfa_accepting_maximal_epsilon_simpleb_no_final_in_closure :
    forall (m : finite_enfa) st q,
      enfa_accepting_maximal_epsilon_simpleb m st = true ->
      In q (enfa_strict_epsilon_closure_states m st) ->
      enfa_final (fenfa_base m) q = false.
  Proof.
    intros m st q Hmax Hin.
    unfold enfa_accepting_maximal_epsilon_simpleb in Hmax.
    apply forallb_forall with (x := q) in Hmax; auto.
    now apply negb_true_iff in Hmax.
  Qed.

  Lemma enfa_accepting_maximal_strict_epsilon_prefix_contradiction :
    forall (m : finite_enfa) s t v,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s (t ++ v) (trace_end s (t ++ v)) ->
      epsilon_simpleb m (s, t ++ v) = true ->
      enfa_accepting_maximal_epsilon_simpleb m (s, t) = true ->
      enfa_final (fenfa_base m) (trace_end s (t ++ v)) = true ->
      trace_word v = [] ->
      v <> [] ->
      False.
  Proof.
    intros m s t v Hwf Hs Hvalid Hsimple Hmax Hfinal Hword Hnonempty.
    pose proof
      (enfa_strict_epsilon_closure_states_complete_nonempty
         m s t v Hwf Hs Hvalid Hsimple Hword Hnonempty)
      as Hin_closure.
    pose proof
      (enfa_accepting_maximal_epsilon_simpleb_no_final_in_closure
         m (s, t) (trace_end (trace_end s t) v)
         Hmax Hin_closure) as Hnot_final.
    rewrite trace_end_app in Hfinal.
    rewrite Hfinal in Hnot_final.
    discriminate.
  Qed.

  Theorem section4_enfa_accepting_maximal_extension_injective :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_accepting_maximal_extension_injective m.
  Proof.
    intros m Hwf.
    unfold enfa_accepting_maximal_extension_injective.
    intros w [s1 t1] [s2 t2]
      Hin1 Hin2 Hacc1 Hacc2 Heps1 Heps2 Hmax1 Hmax2 Hext.
    destruct
      (enfa_extend_to_maximal_epsilon_started_correct
         m w (s1, t1) Hwf Hin1 Heps1)
      as [_ [_ [u1 [Hu1 [Huw1 [_ _]]]]]].
    destruct
      (enfa_extend_to_maximal_epsilon_started_correct
         m w (s2, t2) Hwf Hin2 Heps2)
      as [_ [_ [u2 [Hu2 [Huw2 [_ _]]]]]].
    simpl in Hu1, Hu2, Hext.
    injection Hext as Hstart Htrace_ext.
    subst s2.
    rewrite Hu1 in Htrace_ext.
    rewrite Hu2 in Htrace_ext.
    destruct (started_traces_valid m w s1 t1 Hin1)
      as [Hvalid1 Hword1].
    destruct (started_traces_valid m w s1 t2 Hin2)
      as [Hvalid2 Hword2].
    assert (Hs1 : In s1 (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      now eapply started_traces_start_in with (w := w) (t := t1).
    }
    destruct
      (app_eq_prefix_cases t1 t2 u1 u2 Htrace_ext)
      as [[v [Ht2 Hu1_eq]] | [v [Ht1 Hu2_eq]]].
    - destruct v as [| e v].
      + rewrite app_nil_r in Ht2. subst t2. reflexivity.
      + exfalso.
        assert (Hvalid2_prefix :
          valid_trace m s1 (t1 ++ e :: v)
            (trace_end s1 (t1 ++ e :: v))).
        { now rewrite <- Ht2. }
        assert (Heps2_prefix :
          epsilon_simpleb m (s1, t1 ++ e :: v) = true).
        { now rewrite <- Ht2. }
        assert (Hfinal2 :
          enfa_final (fenfa_base m) (trace_end s1 (t1 ++ e :: v)) = true).
        {
          unfold accepted_traceb, started_end in Hacc2.
          simpl in Hacc2.
          now rewrite Ht2 in Hacc2.
        }
        assert (Hword_v : trace_word (e :: v) = []).
        {
          eapply trace_word_suffix_nil_of_same_word.
          - exact Hword1.
          - rewrite <- Ht2. exact Hword2.
        }
        eapply enfa_accepting_maximal_strict_epsilon_prefix_contradiction;
          eauto.
        discriminate.
    - destruct v as [| e v].
      + rewrite app_nil_r in Ht1. subst t1. reflexivity.
      + exfalso.
        assert (Hvalid1_prefix :
          valid_trace m s1 (t2 ++ e :: v)
            (trace_end s1 (t2 ++ e :: v))).
        { now rewrite <- Ht1. }
        assert (Heps1_prefix :
          epsilon_simpleb m (s1, t2 ++ e :: v) = true).
        { now rewrite <- Ht1. }
        assert (Hfinal1 :
          enfa_final (fenfa_base m) (trace_end s1 (t2 ++ e :: v)) = true).
        {
          unfold accepted_traceb, started_end in Hacc1.
          simpl in Hacc1.
          now rewrite Ht1 in Hacc1.
        }
        assert (Hword_v : trace_word (e :: v) = []).
        {
          eapply trace_word_suffix_nil_of_same_word.
          - exact Hword2.
          - rewrite <- Ht1. exact Hword1.
        }
        eapply enfa_accepting_maximal_strict_epsilon_prefix_contradiction
          with (t := t2) (v := e :: v);
          eauto.
        discriminate.
  Qed.

  Theorem section4_enfa_accepting_maximal_da_bounded_by_leaf :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_accepting_maximal_da_bounded_by_leaf m.
  Proof.
    intros m Hwf.
    eapply
      section4_enfa_accepting_maximal_da_bounded_by_leaf_under_extension_injective.
    - exact Hwf.
    - now apply section4_enfa_accepting_maximal_extension_injective.
  Qed.

  Theorem section4_theorem2_leafufa_implies_ufa :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_LeafUFA m ->
      enfa_UFA m.
  Proof.
    intros m Hwf Hleaf.
    eapply
      section4_theorem2_leafufa_implies_ufa_under_accepting_maximal_da_leaf_bound.
    - now apply section4_enfa_accepting_maximal_da_bounded_by_leaf.
    - exact Hleaf.
  Qed.

  Lemma leaf_prime_two_distinct_maximal_started_traces :
    forall (m : finite_enfa) w st1 st2,
      finite_enfa_wf m ->
      In st1 (started_traces m w) ->
      In st2 (started_traces m w) ->
      epsilon_simpleb m st1 = true ->
      maximal_epsilon_simpleb m st1 = true ->
      epsilon_simpleb m st2 = true ->
      maximal_epsilon_simpleb m st2 = true ->
      st1 <> st2 ->
      2 <= enfa_leaf_prime_word m w.
  Proof.
    intros m w st1 st2 Hwf Hin1 Hin2 Heps1 Hmax1 Heps2 Hmax2 Hneq.
    set (q1 := started_end st1).
    set (q2 := started_end st2).
    assert (Hq1 : In q1 (fenfa_states m)).
    { subst q1. eapply started_traces_end_in_states; eauto. }
    assert (Hq2 : In q2 (fenfa_states m)).
    { subst q2. eapply started_traces_end_in_states; eauto. }
    assert (Hfilt1 :
      ((ends_inb m q1 st1 && epsilon_simpleb m st1) &&
       maximal_epsilon_simpleb m st1) = true).
    {
      apply andb_true_iff. split.
      - apply andb_true_iff. split.
        + unfold ends_inb. subst q1.
          apply fenfa_state_eqb_complete. reflexivity.
        + exact Heps1.
      - exact Hmax1.
    }
    assert (Hfilt2 :
      ((ends_inb m q2 st2 && epsilon_simpleb m st2) &&
       maximal_epsilon_simpleb m st2) = true).
    {
      apply andb_true_iff. split.
      - apply andb_true_iff. split.
        + unfold ends_inb. subst q2.
          apply fenfa_state_eqb_complete. reflexivity.
        + exact Heps2.
      - exact Hmax2.
    }
    destruct (fenfa_state_eqb m q1 q2) eqn:Hqeq.
    - apply fenfa_state_eqb_sound in Hqeq. subst q2.
      unfold enfa_leaf_prime_word.
      pose proof
        (sum_map_In_le
           (enfa_maximal_simple_reach_count m w)
           (fenfa_states m) q1 Hq1) as Hle.
      unfold enfa_maximal_simple_reach_count in Hle.
      assert (Hfilt2_q1 :
        ((ends_inb m q1 st2 && epsilon_simpleb m st2) &&
         maximal_epsilon_simpleb m st2) = true).
      {
        apply andb_true_iff. split.
        - apply andb_true_iff. split.
          + unfold ends_inb.
            apply fenfa_state_eqb_complete. symmetry. exact Hqeq.
          + exact Heps2.
        - exact Hmax2.
      }
      assert
        (Htwo :
          2 <=
          length
            (filter
               (fun st =>
                  (ends_inb m q1 st && epsilon_simpleb m st) &&
                  maximal_epsilon_simpleb m st)
               (started_traces m w))).
      {
        eapply
          (two_distinct_in_filter_length
             (fun st =>
                (ends_inb m q1 st && epsilon_simpleb m st) &&
                maximal_epsilon_simpleb m st)
             (started_traces m w) st1 st2).
        - exact Hin1.
        - exact Hin2.
        - exact Hfilt1.
        - exact Hfilt2_q1.
        - exact Hneq.
      }
      eapply Nat.le_trans; [exact Htwo | exact Hle].
    - assert (Hqneq : q1 <> q2).
      {
        intro Heq.
        rewrite (fenfa_state_eqb_complete m q1 q2 Heq) in Hqeq.
        discriminate.
      }
      assert (Hpos1 :
        0 < enfa_maximal_simple_reach_count m w q1).
      {
        unfold enfa_maximal_simple_reach_count.
        eapply filter_length_pos_of_In with (x := st1); eauto.
      }
      assert (Hpos2 :
        0 < enfa_maximal_simple_reach_count m w q2).
      {
        unfold enfa_maximal_simple_reach_count.
        eapply filter_length_pos_of_In with (x := st2); eauto.
      }
      unfold enfa_leaf_prime_word.
      exact
        (sum_map_two_pos_lower
           (enfa_maximal_simple_reach_count m w)
           (fenfa_states m) q1 q2
           (fenfa_states_nodup m Hwf)
           Hq1 Hq2 Hqneq Hpos1 Hpos2).
  Qed.

  Lemma leaf_prime_maximal_started_trace_unique :
    forall (m : finite_enfa) w st1 st2,
      finite_enfa_wf m ->
      enfa_leaf_prime_word m w <= 1 ->
      In st1 (started_traces m w) ->
      In st2 (started_traces m w) ->
      epsilon_simpleb m st1 = true ->
      maximal_epsilon_simpleb m st1 = true ->
      epsilon_simpleb m st2 = true ->
      maximal_epsilon_simpleb m st2 = true ->
      st1 = st2.
  Proof.
    intros m w st1 st2 Hwf Hleaf Hin1 Hin2 Heps1 Hmax1 Heps2 Hmax2.
    set (q1 := started_end st1).
    set (q2 := started_end st2).
    destruct (fenfa_state_eqb m q1 q2) eqn:Hqeq.
    - apply fenfa_state_eqb_sound in Hqeq. subst q2.
      assert (Hq1 : In q1 (fenfa_states m)).
      { subst q1. eapply started_traces_end_in_states; eauto. }
      assert (Hcount :
        enfa_maximal_simple_reach_count m w q1 <= 1).
      {
        unfold enfa_leaf_prime_word in Hleaf.
        pose proof
          (sum_map_In_le
             (enfa_maximal_simple_reach_count m w)
             (fenfa_states m) q1 Hq1) as Hle.
        lia.
      }
      unfold enfa_maximal_simple_reach_count in Hcount.
      eapply filter_length_le_one_unique; eauto.
      + apply andb_true_iff. split.
        * apply andb_true_iff. split.
          -- unfold ends_inb. subst q1.
             apply fenfa_state_eqb_complete. reflexivity.
          -- exact Heps1.
        * exact Hmax1.
      + apply andb_true_iff. split.
        * apply andb_true_iff. split.
          -- unfold ends_inb.
             apply fenfa_state_eqb_complete. symmetry. exact Hqeq.
          -- exact Heps2.
        * exact Hmax2.
    - exfalso.
      assert (Hneq : st1 <> st2).
      {
        intro Hst. subst st2.
        unfold q2 in Hqeq. subst q1.
        rewrite (fenfa_state_eqb_complete m (started_end st1) (started_end st1) eq_refl)
          in Hqeq.
        discriminate.
      }
      pose proof
        (leaf_prime_two_distinct_maximal_started_traces
           m w st1 st2 Hwf Hin1 Hin2 Heps1 Hmax1 Heps2 Hmax2 Hneq)
        as Htwo.
      lia.
  Qed.

  Lemma enfa_leafufa_accepting_maximal_started_trace_unique_under_extension_injective :
    forall (m : finite_enfa) w st1 st2,
      finite_enfa_wf m ->
      enfa_LeafUFA m ->
      enfa_accepting_maximal_extension_injective m ->
      In st1 (started_traces m w) ->
      In st2 (started_traces m w) ->
      accepted_traceb m st1 = true ->
      accepted_traceb m st2 = true ->
      epsilon_simpleb m st1 = true ->
      epsilon_simpleb m st2 = true ->
      enfa_accepting_maximal_epsilon_simpleb m st1 = true ->
      enfa_accepting_maximal_epsilon_simpleb m st2 = true ->
      st1 = st2.
  Proof.
    intros m w st1 st2 Hwf Hleaf Hinj Hin1 Hin2 Hacc1 Hacc2
      Heps1 Heps2 Haccmax1 Haccmax2.
    pose (st1' := enfa_extend_to_maximal_epsilon_started m st1).
    pose (st2' := enfa_extend_to_maximal_epsilon_started m st2).
    destruct
      (enfa_extend_to_maximal_epsilon_started_correct
         m w st1 Hwf Hin1 Heps1)
      as [Hin1' [_ [u1 [Hu1 [Huw1 [Heps1' Hmax1']]]]]].
    destruct
      (enfa_extend_to_maximal_epsilon_started_correct
         m w st2 Hwf Hin2 Heps2)
      as [Hin2' [_ [u2 [Hu2 [Huw2 [Heps2' Hmax2']]]]]].
    fold st1' in Hin1', Heps1', Hmax1'.
    fold st2' in Hin2', Heps2', Hmax2'.
    assert (Hext_eq : st1' = st2').
    {
      eapply leaf_prime_maximal_started_trace_unique.
      - exact Hwf.
      - exact (Hleaf w).
      - exact Hin1'.
      - exact Hin2'.
      - exact Heps1'.
      - exact Hmax1'.
      - exact Heps2'.
      - exact Hmax2'.
    }
    unfold st1', st2' in Hext_eq.
    eapply Hinj; eauto.
  Qed.

  Theorem section4_theorem2_leafufa_implies_ufa_under_started_traces_nodup_and_accepting_maximal_extension_injective :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_started_traces_nodup m ->
      enfa_accepting_maximal_extension_injective m ->
      enfa_LeafUFA m ->
      enfa_UFA m.
  Proof.
    intros m Hwf Hnodup Hinj Hleaf w.
    destruct (le_gt_dec (enfa_da_prime_word m w) 1) as [Hle | Hgt].
    - exact Hle.
    - exfalso.
      assert (Htwo : 2 <= enfa_da_prime_word m w) by lia.
      unfold enfa_da_prime_word in Htwo.
      destruct
        (sum_map_ge_two_cases
           (enfa_accepting_maximal_simple_reach_count m w)
           (enfa_final_states m)
           (enfa_final_states_nodup m Hwf) Htwo)
        as [[q [Hq Hcount2]] |
            [q1 [q2 [Hq1 [Hq2 [Hqneq [Hpos1 Hpos2]]]]]]].
      + unfold enfa_accepting_maximal_simple_reach_count in Hcount2.
        destruct
          (NoDup_filter_ge_two
             (fun st : started_trace m =>
                (ends_inb m q st && epsilon_simpleb m st)
                && enfa_accepting_maximal_epsilon_simpleb m st)
             (started_traces m w)
             (Hnodup w) Hcount2)
          as [st1 [st2 [Hin1 [Hin2 [Hneq [Hfilt1 Hfilt2]]]]]].
        apply andb_true_iff in Hfilt1 as [Hfilt1 Haccmax1].
        apply andb_true_iff in Hfilt2 as [Hfilt2 Haccmax2].
        apply andb_true_iff in Hfilt1 as [Hend1 Heps1].
        apply andb_true_iff in Hfilt2 as [Hend2 Heps2].
        apply Hneq.
        eapply
          enfa_leafufa_accepting_maximal_started_trace_unique_under_extension_injective;
          eauto using accepted_traceb_of_final_endpoint.
      + apply length_filter_pos_In in Hpos1 as [st1 [Hin1 Hfilt1]].
        apply length_filter_pos_In in Hpos2 as [st2 [Hin2 Hfilt2]].
        apply andb_true_iff in Hfilt1 as [Hfilt1 Haccmax1].
        apply andb_true_iff in Hfilt2 as [Hfilt2 Haccmax2].
        apply andb_true_iff in Hfilt1 as [Hend1 Heps1].
        apply andb_true_iff in Hfilt2 as [Hend2 Heps2].
        assert (Hneq_st : st1 <> st2).
        {
          intro Hst. subst st2.
          unfold ends_inb in Hend1, Hend2.
          apply fenfa_state_eqb_sound in Hend1.
          apply fenfa_state_eqb_sound in Hend2.
          apply Hqneq.
          congruence.
        }
        apply Hneq_st.
        eapply
          enfa_leafufa_accepting_maximal_started_trace_unique_under_extension_injective;
          eauto using accepted_traceb_of_final_endpoint.
  Qed.

  Lemma enfa_trace_bound_app_single :
    forall (m : finite_enfa) (w : list A) a,
      enfa_trace_bound m w + 1 <= enfa_trace_bound m (w ++ [a]).
  Proof.
    intros m w a.
    unfold enfa_trace_bound.
    rewrite length_app. simpl. lia.
  Qed.

  Lemma enfa_dra_prime_step_positive_epsilon_free :
    forall (m : finite_enfa) w q a q',
      enfa_epsilon_free m ->
      0 < enfa_dra_prime_at m w q ->
      In q' (enfa_step (fenfa_base m) q (Some a)) ->
      0 < enfa_dra_prime_at m (w ++ [a]) q'.
  Proof.
    intros m w q a q' Heps Hpos Hstep.
    unfold enfa_dra_prime_at in Hpos.
    apply length_filter_pos_In in Hpos as [[s t] [Hin Hfilter]].
    apply andb_true_iff in Hfilter as [Hend Heps_simple].
    unfold ends_inb in Hend.
    apply fenfa_state_eqb_sound in Hend.
    unfold started_end in Hend.
    simpl in Hend.
    destruct (started_traces_valid m w s t Hin) as [Hvalid Hword].
    pose (t' := t ++ [((q, Some a), q')]).
    assert (Ht'_word : trace_word t' = w ++ [a]).
    {
      unfold t'. rewrite trace_word_app. simpl.
      now rewrite Hword.
    }
    assert (Ht'_valid : valid_trace m s t' q').
    {
      unfold t'. subst q.
      apply valid_trace_app_edge; auto.
    }
    assert (Ht'_in : In (s, t') (started_traces m (w ++ [a]))).
    {
      unfold started_traces.
      apply in_concat.
      exists
        (map (fun t0 => (s, t0))
           (traces_from_fuel m (enfa_trace_bound m (w ++ [a])) s (w ++ [a]))).
      split.
      - apply in_map_iff.
        exists s. split; [reflexivity |].
        eapply started_traces_start_in; eauto.
      - apply in_map_iff.
        exists t'. split; [reflexivity |].
        rewrite <- Ht'_word.
        apply valid_trace_in_traces_from_fuel with (q := q').
        + exact Ht'_valid.
        + unfold t'. rewrite length_app. simpl.
          pose proof (started_traces_length_bound m w s t Hin) as Hlen.
          pose proof (enfa_trace_bound_app_single m w a) as Hbound.
          eapply Nat.le_trans.
          -- apply Nat.add_le_mono_r. exact Hlen.
          -- fold t'. rewrite Ht'_word. exact Hbound.
    }
    unfold enfa_dra_prime_at.
    eapply filter_length_pos_of_In with (x := (s, t')).
    - exact Ht'_in.
    - apply andb_true_iff. split.
      + unfold ends_inb, started_end. simpl.
        unfold t'. rewrite trace_end_app. simpl.
        apply fenfa_state_eqb_complete. reflexivity.
      + eapply epsilon_simpleb_epsilon_free; eauto.
  Qed.

  Lemma traces_from_fuel_epsilon_free_deterministic_le_one :
    forall (m : finite_enfa) fuel p w,
      finite_enfa_wf m ->
      enfa_epsilon_free m ->
      enfa_deterministic m ->
      In p (fenfa_states m) ->
      length (traces_from_fuel m fuel p w) <= 1.
  Proof.
    intros m fuel.
    induction fuel as [| fuel IH]; intros p w Hwf Heps Hdet Hp.
    - destruct w; simpl; lia.
    - simpl.
      destruct w as [| a w].
      + rewrite Heps. simpl. lia.
      + rewrite Heps. simpl.
        pose proof (Hdet p a Hp) as Hstep_len.
        destruct (enfa_step (fenfa_base m) p (Some a)) as [| q qs] eqn:Hstep.
        * simpl. lia.
        * destruct qs as [| r rs].
          -- simpl.
             rewrite app_nil_r.
             rewrite length_map.
             apply IH; auto.
             eapply fenfa_steps_in_states; eauto.
             rewrite Hstep. simpl. auto.
          -- simpl in Hstep_len. lia.
  Qed.

  Lemma started_traces_epsilon_free_deterministic_single_start_le_one :
    forall (m : finite_enfa) w,
      finite_enfa_wf m ->
      enfa_epsilon_free m ->
      enfa_single_start m ->
      enfa_deterministic m ->
      length (started_traces m w) <= 1.
  Proof.
    intros m w Hwf Heps Hsingle Hdet.
    unfold started_traces.
    destruct (enfa_start (fenfa_base m)) as [| s ss] eqn:Hstarts.
    - simpl. lia.
    - destruct ss as [| s' ss].
      + simpl. rewrite app_nil_r. rewrite length_map.
        eapply traces_from_fuel_epsilon_free_deterministic_le_one; eauto.
        eapply fenfa_starts_in_states; eauto.
        rewrite Hstarts. simpl. auto.
      + exfalso. unfold enfa_single_start in Hsingle.
        rewrite Hstarts in Hsingle. simpl in Hsingle. lia.
  Qed.

  Lemma leaf_prime_no_started_traces :
    forall (m : finite_enfa) w,
      started_traces m w = [] ->
      enfa_leaf_prime_word m w = 0.
  Proof.
    intros m w Htr.
    unfold enfa_leaf_prime_word, enfa_maximal_simple_reach_count.
    rewrite Htr.
    induction (fenfa_states m) as [| q qs IH]; simpl; auto.
  Qed.

  Lemma sum_single_started_trace_filters_zero :
    forall (m : finite_enfa) st qs,
      (forall q,
        In q qs ->
        ((ends_inb m q st && epsilon_simpleb m st) &&
         maximal_epsilon_simpleb m st) = false) ->
      sum_nats
        (map
           (fun q : enfa_state (fenfa_base m) =>
              length
                (filter
                   (fun st0 : started_trace m =>
                      (ends_inb m q st0 && epsilon_simpleb m st0) &&
                      maximal_epsilon_simpleb m st0) [st])) qs) = 0.
  Proof.
    intros m st qs Hfalse.
    induction qs as [| q qs IH]; simpl; auto.
    rewrite Hfalse by (simpl; auto).
    simpl.
    apply IH.
    intros r Hr. apply Hfalse. simpl. auto.
  Qed.

  Lemma sum_single_started_trace_filters_le_one :
    forall (m : finite_enfa) st qs,
      NoDup qs ->
      sum_nats
        (map
           (fun q : enfa_state (fenfa_base m) =>
              length
                (filter
                   (fun st0 : started_trace m =>
                      (ends_inb m q st0 && epsilon_simpleb m st0) &&
                      maximal_epsilon_simpleb m st0) [st])) qs) <= 1.
  Proof.
    intros m st qs Hnodup.
    induction qs as [| q qs IH]; simpl.
    - lia.
    - inversion Hnodup as [| q' qs' Hnotin Hnodup_tail]; subst.
      destruct (((ends_inb m q st && epsilon_simpleb m st) &&
                 maximal_epsilon_simpleb m st)) eqn:Hq.
      + assert (Htail_zero :
          sum_nats
            (map
               (fun q0 : enfa_state (fenfa_base m) =>
                  length
                    (filter
                       (fun st0 : started_trace m =>
                          (ends_inb m q0 st0 && epsilon_simpleb m st0) &&
                          maximal_epsilon_simpleb m st0) [st])) qs) = 0).
        {
          assert (Htail_false :
            forall r,
              In r qs ->
              ((ends_inb m r st && epsilon_simpleb m st) &&
               maximal_epsilon_simpleb m st) = false).
          {
            intros r Hr_in.
            destruct (((ends_inb m r st && epsilon_simpleb m st) &&
                      maximal_epsilon_simpleb m st)) eqn:Hr; auto.
            apply andb_true_iff in Hq as [Hq_end _].
            apply andb_true_iff in Hq_end as [Hq_end _].
            apply andb_true_iff in Hr as [Hr_end _].
            apply andb_true_iff in Hr_end as [Hr_end _].
            unfold ends_inb in Hq_end, Hr_end.
            apply fenfa_state_eqb_sound in Hq_end.
            apply fenfa_state_eqb_sound in Hr_end.
            subst q r.
            exfalso. exact (Hnotin Hr_in).
          }
          now apply sum_single_started_trace_filters_zero.
        }
        change
          (1 +
           sum_nats
             (map
                (fun q0 : enfa_state (fenfa_base m) =>
                   length
                     (filter
                        (fun st0 : started_trace m =>
                           (ends_inb m q0 st0 && epsilon_simpleb m st0) &&
                           maximal_epsilon_simpleb m st0) [st])) qs) <= 1).
        rewrite Htail_zero. lia.
      + simpl.
        apply IH. exact Hnodup_tail.
  Qed.

  Lemma filter_false_nil :
    forall {B : Type} (p : B -> bool) xs,
      (forall x, In x xs -> p x = false) ->
      filter p xs = [].
  Proof.
    intros B p xs Hall.
    induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - rewrite Hall by (simpl; auto).
      apply IH. intros y Hy. apply Hall. simpl; auto.
  Qed.

  Lemma leaf_prime_single_started_trace :
    forall (m : finite_enfa) w st,
      finite_enfa_wf m ->
      started_traces m w = [st] ->
      enfa_leaf_prime_word m w <= 1.
  Proof.
    intros m w st Hwf Htr.
    unfold enfa_leaf_prime_word, enfa_maximal_simple_reach_count.
    rewrite Htr.
    inversion Hwf as [Hnodup _ _ _ _].
    now apply sum_single_started_trace_filters_le_one.
  Qed.

  Lemma leaf_prime_started_traces_le_one :
    forall (m : finite_enfa) w,
      finite_enfa_wf m ->
      length (started_traces m w) <= 1 ->
      enfa_leaf_prime_word m w <= 1.
  Proof.
    intros m w Hwf Hlen.
    destruct (started_traces m w) as [| st sts] eqn:Htr.
    - rewrite (leaf_prime_no_started_traces m w Htr). lia.
    - destruct sts as [| st' sts].
      + eapply leaf_prime_single_started_trace; eauto.
      + simpl in Hlen. lia.
  Qed.

  (* Theorem 1. I. *)
  Theorem section4_theorem1_epsilon_free_deterministic_leafufa :
    forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_deterministic m ->
      enfa_LeafUFA m.
  Proof.
    intros m Heps Hwf Hsingle Hdet w.
    apply leaf_prime_started_traces_le_one; auto.
    now apply started_traces_epsilon_free_deterministic_single_start_le_one.
  Qed.

  Theorem section4_dfa_conditions_implies_reachufa :
    forall (m : finite_enfa),
      enfa_DFA_conditions m ->
      enfa_ReachUFA m.
  Proof.
    intros m [Heps [Hwf [Hsingle Hdet]]] w q _.
    pose proof (enfa_dra_prime_at_le_started_traces m w q) as Hfilter.
    pose proof
      (started_traces_epsilon_free_deterministic_single_start_le_one
         m w Hwf Heps Hsingle Hdet) as Hstarted.
    lia.
  Qed.

  Theorem section4_dfa_conditions_implies_ufa_reachufa_leafufa :
    forall (m : finite_enfa),
      enfa_DFA_conditions m ->
      enfa_UFA m /\ enfa_ReachUFA m /\ enfa_LeafUFA m.
  Proof.
    intros m [Heps [Hwf [Hsingle Hdet]]].
    assert (Hleaf : enfa_LeafUFA m).
    {
      eapply section4_theorem1_epsilon_free_deterministic_leafufa; eauto.
    }
    assert (Hreach : enfa_ReachUFA m).
    {
      apply section4_dfa_conditions_implies_reachufa.
      exact (conj Heps (conj Hwf (conj Hsingle Hdet))).
    }
    repeat split; auto.
    now eapply section4_theorem2_leafufa_implies_ufa.
  Qed.

  Theorem section4_theorem1_epsilon_free_leafufa_deterministic_trim :
    forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_trim m ->
      enfa_LeafUFA m ->
      enfa_deterministic m.
  Proof.
    intros m Heps Hwf Htrim Hleaf q a Hq.
    destruct (enfa_step (fenfa_base m) q (Some a)) as [| q1 qs] eqn:Hstep.
    - simpl. lia.
    - destruct qs as [| q2 qs].
      + simpl. lia.
      + exfalso.
        destruct (Htrim q Hq) as [[w Hreach] _].
        assert (Hpos1 : 0 < enfa_dra_prime_at m (w ++ [a]) q1).
        {
          eapply enfa_dra_prime_step_positive_epsilon_free; eauto.
          rewrite Hstep. simpl. auto.
        }
        assert (Hpos2 : 0 < enfa_dra_prime_at m (w ++ [a]) q2).
        {
          eapply enfa_dra_prime_step_positive_epsilon_free; eauto.
          rewrite Hstep. simpl. auto.
        }
        assert (Hq1 : In q1 (fenfa_states m)).
        {
          eapply fenfa_steps_in_states.
          - exact Hwf.
          - exact Hq.
          - rewrite Hstep. simpl. auto.
        }
        assert (Hq2 : In q2 (fenfa_states m)).
        {
          eapply fenfa_steps_in_states.
          - exact Hwf.
          - exact Hq.
          - rewrite Hstep. simpl. auto.
        }
        assert (Hneq : q1 <> q2).
        {
          pose proof (fenfa_step_targets_nodup m Hwf q (Some a) Hq) as Hnodup_step.
          rewrite Hstep in Hnodup_step.
          inversion Hnodup_step as [| x xs Hnotin _]; subst.
          intro Heq. subst q2. apply Hnotin. simpl. auto.
        }
        assert (Hmax1 :
          0 < enfa_maximal_simple_reach_count m (w ++ [a]) q1).
        {
          rewrite enfa_maximal_simple_reach_epsilon_free by exact Heps.
          exact Hpos1.
        }
        assert (Hmax2 :
          0 < enfa_maximal_simple_reach_count m (w ++ [a]) q2).
        {
          rewrite enfa_maximal_simple_reach_epsilon_free by exact Heps.
          exact Hpos2.
        }
        pose proof (Hleaf (w ++ [a])) as Hleaf_w.
        unfold enfa_leaf_prime_word in Hleaf_w.
        pose proof
          (sum_map_two_pos_lower
             (enfa_maximal_simple_reach_count m (w ++ [a]))
             (fenfa_states m) q1 q2
             (fenfa_states_nodup m Hwf)
             Hq1 Hq2 Hneq Hmax1 Hmax2) as Htwo.
        lia.
  Qed.

  Theorem section4_theorem1_epsilon_free_leafufa_deterministic_trim_single_start :
    forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_trim m ->
      enfa_single_start m ->
      (enfa_LeafUFA m <-> enfa_deterministic m).
  Proof.
    intros m Heps Hwf Htrim Hsingle. split.
    - now apply section4_theorem1_epsilon_free_leafufa_deterministic_trim.
    - now apply section4_theorem1_epsilon_free_deterministic_leafufa.
  Qed.

  (* Theorem 1. II.
     This is the maximal-trace form of epsilon removal: unlike the classical
     epsilon-closure target list, it counts only maximal epsilon-simple lifted
     computations, matching Leaf'. *)
  Theorem section4_theorem1_leafufa_maximal_epsilon_removal_deterministic :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_LeafUFA m ->
      enfa_maximal_epsilon_removed_deterministic m.
  Proof.
    intros m Hwf _ Hleaf st a st1 st2 _ Hext1 Hext2.
    unfold enfa_maximal_symbol_extension in Hext1, Hext2.
    destruct Hext1 as
      [Hin1 [u1 [_ [_ [_ [_ [Heps1 Hmax1]]]]]]].
    destruct Hext2 as
      [Hin2 [u2 [_ [_ [_ [_ [Heps2 Hmax2]]]]]]].
    eapply leaf_prime_maximal_started_trace_unique
      with (w := started_word st ++ [a]); eauto.
  Qed.

  (* Theorem 1.II/III: epsilon-closure branching for LeafUFA.

     The statement combines the numeric LeafUFA condition with trace-level
     closure branching clauses for maximal epsilon-simple traces. *)
  Theorem section4_theorem1_leafufa_implies_epsilon_closure_branching :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_LeafUFA m ->
      enfa_epsilon_closure_branching_deterministic m.
  Proof.
    intros m Hwf Hsingle Hleaf.
    repeat split.
    - exact Hleaf.
    - unfold enfa_fresh_epsilon_branching_le_one.
      intros st st1 st2 _ Hext1 Hext2.
      unfold enfa_maximal_epsilon_closure_extension,
        enfa_epsilon_closure_extension in *.
      destruct Hext1 as
        [[Hin1 [u1 [_ [_ [_ [_ Heps1]]]]]] Hmax1].
      destruct Hext2 as
        [[Hin2 [u2 [_ [_ [_ [_ Heps2]]]]]] Hmax2].
      eapply leaf_prime_maximal_started_trace_unique
        with (w := started_word st); eauto.
    - unfold enfa_epsilon_closure_symbol_branching_le_one.
      intros st a st1 st2 Hpre Hext1 Hext2.
      eapply section4_theorem1_leafufa_maximal_epsilon_removal_deterministic;
        eauto.
    - unfold enfa_maximal_epsilon_closure_trace_unique.
      intros w st1 st2 Hin1 Hin2 Heps1 Hmax1 Heps2 Hmax2.
      eapply leaf_prime_maximal_started_trace_unique; eauto.
  Qed.

  Theorem section4_theorem1_epsilon_closure_branching_implies_leafufa :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_epsilon_closure_branching_deterministic m ->
      enfa_LeafUFA m.
  Proof.
    intros m _ _ [Hleaf _].
    exact Hleaf.
  Qed.

  Theorem section4_theorem1_epsilon_closure_branching_iff :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_single_start m ->
      (enfa_LeafUFA m <->
       enfa_epsilon_closure_branching_deterministic m).
  Proof.
    intros m Hwf Hsingle. split.
    - now apply section4_theorem1_leafufa_implies_epsilon_closure_branching.
    - now apply section4_theorem1_epsilon_closure_branching_implies_leafufa.
  Qed.

  Lemma started_traces_epsilon_free_single_start_NoDup :
    forall (m : finite_enfa) w,
      finite_enfa_wf m ->
      enfa_epsilon_free m ->
      enfa_single_start m ->
      NoDup (started_traces m w).
  Proof.
    intros m w Hwf Heps Hsingle.
    unfold started_traces.
    destruct (enfa_start (fenfa_base m)) as [| s starts] eqn:Hstarts.
    - simpl. constructor.
    - destruct starts as [| s' starts].
      + simpl. rewrite app_nil_r.
        apply NoDup_map_injective_in.
        * intros t1 t2 _ _ Heq.
          inversion Heq. reflexivity.
        * apply traces_from_fuel_epsilon_free_NoDup; auto.
          eapply fenfa_starts_in_states; eauto.
          rewrite Hstarts. simpl. auto.
      + exfalso.
        unfold enfa_single_start in Hsingle.
        rewrite Hstarts in Hsingle. simpl in Hsingle. lia.
  Qed.

  Lemma started_trace_append_suffix_in :
    forall (m : finite_enfa) w suffix s t q u f,
      enfa_epsilon_free m ->
      In (s, t) (started_traces m w) ->
      trace_end s t = q ->
      In u (traces_from_fuel m (enfa_trace_bound m suffix) q suffix) ->
      f = trace_end q u ->
      In (s, t ++ u) (started_traces m (w ++ suffix)).
  Proof.
    intros m w suffix s t q u f Heps Hst Hend Hu Hf.
    destruct (started_traces_valid m w s t Hst) as [Hvalid_t Hword_t].
    destruct (traces_from_fuel_valid m _ q suffix u Hu) as
      [Hvalid_u Hword_u].
    unfold started_traces.
    apply in_concat.
    exists
      (map (fun t0 => (s, t0))
         (traces_from_fuel m (enfa_trace_bound m (w ++ suffix)) s
            (w ++ suffix))).
    split.
    - apply in_map_iff.
      exists s. split; [reflexivity |].
      eapply started_traces_start_in; eauto.
    - apply in_map_iff.
      exists (t ++ u). split; [reflexivity |].
      replace (w ++ suffix) with (trace_word (t ++ u)) at 2.
      apply valid_trace_in_traces_from_fuel with (q := f).
      + subst f.
        rewrite Hend in Hvalid_t.
        eapply valid_trace_app; eauto.
      + rewrite length_app.
        rewrite
          (traces_from_fuel_epsilon_free_length_word
             m (enfa_trace_bound m w) s w t Heps).
        * rewrite
            (traces_from_fuel_epsilon_free_length_word
               m (enfa_trace_bound m suffix) q suffix u Heps Hu).
          rewrite <- length_app.
          apply enfa_trace_bound_word_length.
        * eapply started_traces_trace_in; eauto.
      + rewrite trace_word_app.
        now rewrite Hword_t, Hword_u.
  Qed.

  (* Theorem 2 *)
  Theorem section4_theorem2_epsilon_free_trim_ufa_implies_reachufa :
    forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_trim m ->
      enfa_UFA m ->
      enfa_ReachUFA m.
  Proof.
    intros m Heps Hwf Hsingle Htrim Hufa w q Hq.
    destruct (le_gt_dec (enfa_dra_prime_at m w q) 1) as [Hle | Hgt].
    - exact Hle.
    - exfalso.
      assert (Htwo : 2 <= enfa_dra_prime_at m w q) by lia.
      unfold enfa_dra_prime_at in Htwo.
      pose proof
        (started_traces_epsilon_free_single_start_NoDup
           m w Hwf Heps Hsingle) as Hnodup_started.
      destruct
        (NoDup_filter_ge_two
           (fun st => ends_inb m q st && epsilon_simpleb m st)
           (started_traces m w)
           Hnodup_started Htwo)
        as [[s1 t1] [[s2 t2] [Hin1 [Hin2 [Hneq [Hfilt1 Hfilt2]]]]]].
      apply andb_true_iff in Hfilt1 as [Hend1 _].
      apply andb_true_iff in Hfilt2 as [Hend2 _].
      unfold ends_inb in Hend1, Hend2.
      apply fenfa_state_eqb_sound in Hend1.
      apply fenfa_state_eqb_sound in Hend2.
      unfold started_end in Hend1, Hend2.
      simpl in Hend1, Hend2.
      destruct (Htrim q Hq) as [_ [suffix [[sq u] [Hsq [Hu_map [Hacc _]]]]]].
      simpl in Hsq. subst sq.
      apply in_map_iff in Hu_map as [u' [Hu_eq Hu]].
      inversion Hu_eq; subst u'; clear Hu_eq.
      set (f := trace_end q u).
      assert (Hfinal_f : enfa_final (fenfa_base m) f = true).
      {
        unfold accepted_traceb in Hacc.
        simpl in Hacc. exact Hacc.
      }
      assert (Hstate_f : In f (fenfa_states m)).
      {
        unfold f.
        destruct (traces_from_fuel_valid m _ q suffix u Hu) as [Hvalid_u _].
        eapply finite_enfa_wf_valid_trace_end_in_states; eauto.
      }
      assert (Hfinals_f : In f (enfa_final_states m)).
      {
        unfold enfa_final_states.
        apply filter_In. split; auto.
      }
      pose (st1' := (s1, t1 ++ u) : started_trace m).
      pose (st2' := (s2, t2 ++ u) : started_trace m).
      assert (Hin1' : In st1' (started_traces m (w ++ suffix))).
      {
        unfold st1'.
        eapply started_trace_append_suffix_in
          with (q := q) (u := u) (f := f); eauto.
      }
      assert (Hin2' : In st2' (started_traces m (w ++ suffix))).
      {
        unfold st2'.
        eapply started_trace_append_suffix_in
          with (q := q) (u := u) (f := f); eauto.
      }
      assert (Hfilt1' :
        ((ends_inb m f st1' && epsilon_simpleb m st1') &&
         enfa_accepting_maximal_epsilon_simpleb m st1') = true).
      {
        apply andb_true_iff. split.
        - apply andb_true_iff. split.
          + unfold st1', ends_inb, started_end, f.
            simpl. rewrite trace_end_app.
            rewrite Hend1.
            apply fenfa_state_eqb_complete. reflexivity.
          + eapply epsilon_simpleb_epsilon_free; eauto.
        - now apply enfa_accepting_maximal_epsilon_simpleb_epsilon_free.
      }
      assert (Hfilt2' :
        ((ends_inb m f st2' && epsilon_simpleb m st2') &&
         enfa_accepting_maximal_epsilon_simpleb m st2') = true).
      {
        apply andb_true_iff. split.
        - apply andb_true_iff. split.
          + unfold st2', ends_inb, started_end, f.
            simpl. rewrite trace_end_app.
            rewrite Hend2.
            apply fenfa_state_eqb_complete. reflexivity.
          + eapply epsilon_simpleb_epsilon_free; eauto.
        - now apply enfa_accepting_maximal_epsilon_simpleb_epsilon_free.
      }
      assert (Hneq' : st1' <> st2').
      {
        unfold st1', st2'. intro Heq.
        inversion Heq as [[Hs Ht]].
        apply app_inv_tail in Ht.
        apply Hneq. now subst.
      }
      assert (Hmax_two :
        2 <= enfa_accepting_maximal_simple_reach_count m (w ++ suffix) f).
      {
        unfold enfa_accepting_maximal_simple_reach_count.
        eapply two_distinct_in_filter_length
          with (x := st1') (y := st2'); eauto.
      }
      pose proof (sum_map_In_le
        (enfa_accepting_maximal_simple_reach_count m (w ++ suffix))
        (enfa_final_states m) f Hfinals_f) as Hmax_le_da.
      pose proof (Hufa (w ++ suffix)) as Hufa_suffix.
      unfold enfa_da_prime_word in Hufa_suffix.
      lia.
  Qed.

  Theorem section4_theorem2_epsilon_free_trim_ufa_implies_stufa :
    forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_trim m ->
      enfa_UFA m ->
      enfa_stUFA m.
  Proof.
    intros m Heps Hwf _ Htrim Hufa p q w Hp Hq.
    destruct (le_gt_dec (enfa_dra_prime_between m p w q) 1) as
      [Hle | Hgt].
    - exact Hle.
    - exfalso.
      assert (Htwo : 2 <= enfa_dra_prime_between m p w q) by lia.
      unfold enfa_dra_prime_between in Htwo.
      pose proof
        (started_traces_from_start_NoDup m p w Hwf Hp) as Hnodup_started.
      destruct
        (NoDup_filter_ge_two
           (fun st => ends_inb m q st && epsilon_simpleb m st)
           (started_traces_from_start m p w)
           Hnodup_started Htwo)
        as [[p1 t1] [[p2 t2]
             [Hin1 [Hin2 [Hneq [Hfilt1 Hfilt2]]]]]].
      unfold started_traces_from_start in Hin1.
      apply in_map_iff in Hin1 as [t1' [Hpair1 Ht1]].
      inversion Hpair1; subst p1 t1'; clear Hpair1.
      unfold started_traces_from_start in Hin2.
      apply in_map_iff in Hin2 as [t2' [Hpair2 Ht2]].
      inversion Hpair2; subst p2 t2'; clear Hpair2.
      assert (Htneq : t1 <> t2).
      {
        intro Ht.
        apply Hneq.
        now subst t2.
      }
      apply andb_true_iff in Hfilt1 as [Hend1 _].
      apply andb_true_iff in Hfilt2 as [Hend2 _].
      unfold ends_inb in Hend1, Hend2.
      apply fenfa_state_eqb_sound in Hend1.
      apply fenfa_state_eqb_sound in Hend2.
      unfold started_end in Hend1, Hend2.
      simpl in Hend1, Hend2.
      destruct (Htrim p Hp) as [[prefix Hreach_p] _].
      unfold enfa_dra_prime_at in Hreach_p.
      destruct
        (length_filter_pos_In
           (fun st => ends_inb m p st && epsilon_simpleb m st)
           (started_traces m prefix)
           Hreach_p)
        as [[s0 t0] [Hprefix_in Hprefix_filt]].
      apply andb_true_iff in Hprefix_filt as [Hprefix_end _].
      unfold ends_inb in Hprefix_end.
      apply fenfa_state_eqb_sound in Hprefix_end.
      unfold started_end in Hprefix_end.
      simpl in Hprefix_end.
      destruct (Htrim q Hq) as [_ [suffix [[sq u] [Hsq [Hu_map [Hacc _]]]]]].
      simpl in Hsq. subst sq.
      apply in_map_iff in Hu_map as [u' [Hu_eq Hu]].
      inversion Hu_eq; subst u'; clear Hu_eq.
      set (f := trace_end q u).
      assert (Hfinal_f : enfa_final (fenfa_base m) f = true).
      {
        unfold accepted_traceb in Hacc.
        simpl in Hacc. exact Hacc.
      }
      assert (Hstate_f : In f (fenfa_states m)).
      {
        unfold f.
        destruct (traces_from_fuel_valid m _ q suffix u Hu) as [Hvalid_u _].
        eapply finite_enfa_wf_valid_trace_end_in_states; eauto.
      }
      assert (Hfinals_f : In f (enfa_final_states m)).
      {
        unfold enfa_final_states.
        apply filter_In. split; auto.
      }
      assert (Hmid1_in :
        In (s0, t0 ++ t1) (started_traces m (prefix ++ w))).
      {
        eapply started_trace_append_suffix_in
          with (q := p) (u := t1) (f := q); eauto.
      }
      assert (Hmid2_in :
        In (s0, t0 ++ t2) (started_traces m (prefix ++ w))).
      {
        eapply started_trace_append_suffix_in
          with (q := p) (u := t2) (f := q); eauto.
      }
      assert (Hmid1_end : trace_end s0 (t0 ++ t1) = q).
      {
        rewrite trace_end_app.
        now rewrite Hprefix_end, Hend1.
      }
      assert (Hmid2_end : trace_end s0 (t0 ++ t2) = q).
      {
        rewrite trace_end_app.
        now rewrite Hprefix_end, Hend2.
      }
      pose (st1' := (s0, (t0 ++ t1) ++ u) : started_trace m).
      pose (st2' := (s0, (t0 ++ t2) ++ u) : started_trace m).
      assert (Hin1' :
        In st1' (started_traces m ((prefix ++ w) ++ suffix))).
      {
        unfold st1'.
        eapply started_trace_append_suffix_in
          with (q := q) (u := u) (f := f); eauto.
      }
      assert (Hin2' :
        In st2' (started_traces m ((prefix ++ w) ++ suffix))).
      {
        unfold st2'.
        eapply started_trace_append_suffix_in
          with (q := q) (u := u) (f := f); eauto.
      }
      assert (Hfilt1' :
        ((ends_inb m f st1' && epsilon_simpleb m st1') &&
         enfa_accepting_maximal_epsilon_simpleb m st1') = true).
      {
        apply andb_true_iff. split.
        - apply andb_true_iff. split.
          + unfold st1', ends_inb, started_end, f.
            simpl. rewrite trace_end_app.
            rewrite Hmid1_end.
            apply fenfa_state_eqb_complete. reflexivity.
          + eapply epsilon_simpleb_epsilon_free; eauto.
        - now apply enfa_accepting_maximal_epsilon_simpleb_epsilon_free.
      }
      assert (Hfilt2' :
        ((ends_inb m f st2' && epsilon_simpleb m st2') &&
         enfa_accepting_maximal_epsilon_simpleb m st2') = true).
      {
        apply andb_true_iff. split.
        - apply andb_true_iff. split.
          + unfold st2', ends_inb, started_end, f.
            simpl. rewrite trace_end_app.
            rewrite Hmid2_end.
            apply fenfa_state_eqb_complete. reflexivity.
          + eapply epsilon_simpleb_epsilon_free; eauto.
        - now apply enfa_accepting_maximal_epsilon_simpleb_epsilon_free.
      }
      assert (Hneq' : st1' <> st2').
      {
        unfold st1', st2'. intro Heq.
        injection Heq as Ht.
        apply app_inv_tail in Ht.
        apply app_inv_head in Ht.
        now apply Htneq.
      }
      assert (Hmax_two :
        2 <=
        enfa_accepting_maximal_simple_reach_count
          m ((prefix ++ w) ++ suffix) f).
      {
        unfold enfa_accepting_maximal_simple_reach_count.
        eapply two_distinct_in_filter_length
          with (x := st1') (y := st2'); eauto.
      }
      pose proof (sum_map_In_le
        (enfa_accepting_maximal_simple_reach_count
           m ((prefix ++ w) ++ suffix))
        (enfa_final_states m) f Hfinals_f) as Hmax_le_da.
      pose proof (Hufa ((prefix ++ w) ++ suffix)) as Hufa_suffix.
      unfold enfa_da_prime_word in Hufa_suffix.
      lia.
  Qed.

  Theorem section4_theorem2_epsilon_free_trim_ufa_implies_sufa :
    forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_trim m ->
      enfa_UFA m ->
      enfa_SUFA m.
  Proof.
    intros m Heps Hwf Hsingle Htrim Hufa.
    split.
    - exact Heps.
    - eapply section4_theorem2_epsilon_free_trim_ufa_implies_reachufa; eauto.
  Qed.

  Lemma filter_unique_singleton :
    forall {B : Type} (p : B -> bool) (x : B) xs,
      NoDup xs ->
      In x xs ->
      p x = true ->
      (forall y, In y xs -> p y = true -> y = x) ->
      filter p xs = [x].
  Proof.
    intros B p x xs Hnodup Hin Hpx Hunique.
    induction xs as [| y ys IH].
    - contradiction.
    - inversion Hnodup as [| ? ? Hnotin Hnodup']; subst.
      simpl in Hin. destruct Hin as [Hy | Hin].
      + subst y. simpl. rewrite Hpx. f_equal.
        apply filter_false_nil. intros z Hz.
        destruct (p z) eqn:Hpz; auto.
        exfalso.
        pose proof (Hunique z (or_intror Hz) Hpz) as Hzx.
        subst z. contradiction.
      + simpl. destruct (p y) eqn:Hpy.
        * pose proof (Hunique y (or_introl eq_refl) Hpy) as Hyx.
          subst y. contradiction.
        * apply IH; auto.
          intros z Hz Hpz. apply Hunique; simpl; auto.
  Qed.

  Lemma enfa_final_states_unique_final :
    forall (m : finite_enfa) f,
      finite_enfa_wf m ->
      In f (fenfa_states m) ->
      enfa_final (fenfa_base m) f = true ->
      (forall q,
        In q (fenfa_states m) ->
        enfa_final (fenfa_base m) q = true ->
        q = f) ->
      enfa_final_states m = [f].
  Proof.
    intros m f Hwf Hfin Hfinal Hunique.
    unfold enfa_final_states.
    apply filter_unique_singleton.
    - exact (fenfa_states_nodup m Hwf).
    - exact Hfin.
    - exact Hfinal.
    - exact Hunique.
  Qed.

  (* Theorem 2 *)
  Theorem section4_theorem2_reachufa_single_final_list_implies_ufa :
    forall (m : finite_enfa),
      enfa_ReachUFA m ->
      forall f,
      In f (fenfa_states m) ->
      enfa_final_states m = [f] ->
      enfa_UFA m.
  Proof.
    intros m Hreach f Hfin Hfinals w.
    unfold enfa_da_prime_word.
    rewrite Hfinals. simpl.
    pose proof (Hreach w f Hfin) as H.
    pose proof (enfa_accepting_maximal_simple_reach_le_dra_prime m w f)
      as Hle.
    lia.
  Qed.

  Theorem section4_theorem2_reachufa_unique_terminating_state_implies_ufa :
    forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_ReachUFA m ->
      enfa_unique_terminating_state m ->
      enfa_UFA m.
  Proof.
    intros m Hwf Hreach [f [Hfin [Hfinal Hunique]]].
    eapply section4_theorem2_reachufa_single_final_list_implies_ufa.
    - exact Hreach.
    - exact Hfin.
    - eapply enfa_final_states_unique_final; eauto.
  Qed.

  Theorem section4_theorem2_unambiguity_and_reach_unambiguity :
    (forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_LeafUFA m -> enfa_UFA m) /\
    (forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_trim m ->
      enfa_prime_extendable m ->
      enfa_UFA m ->
      enfa_ReachUFA m) /\
    (forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_trim m ->
      enfa_UFA m ->
      enfa_ReachUFA m) /\
    (forall (m : finite_enfa),
      enfa_epsilon_free m ->
      finite_enfa_wf m ->
      enfa_single_start m ->
      enfa_trim m ->
      enfa_UFA m ->
      enfa_SUFA m) /\
    (forall (m : finite_enfa),
      enfa_ReachUFA m ->
      forall f,
      In f (fenfa_states m) ->
      enfa_final_states m = [f] ->
      enfa_UFA m) /\
    (forall (m : finite_enfa),
      finite_enfa_wf m ->
      enfa_ReachUFA m ->
      enfa_unique_terminating_state m ->
      enfa_UFA m).
  Proof.
    repeat split; intros; eauto using
      section4_theorem2_leafufa_implies_ufa,
      section4_theorem2_trim_extendable_ufa_implies_reachufa,
      section4_theorem2_epsilon_free_trim_ufa_implies_reachufa,
      section4_theorem2_epsilon_free_trim_ufa_implies_sufa,
      section4_theorem2_reachufa_single_final_list_implies_ufa,
      section4_theorem2_reachufa_unique_terminating_state_implies_ufa.
  Qed.
End EpsilonNFA.

Arguments enfa_state {A} _.
Arguments enfa_start {A} _.
Arguments enfa_final {A} _ _.
Arguments enfa_step {A} _ _ _.
