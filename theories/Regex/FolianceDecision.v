From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Ambiguity Require Import
  FiniteAmbiguity InfiniteAmbiguity.
From PositionAutomata.Automata Require Import EpsilonNFA.
From PositionAutomata.Regex Require Import
  KleeneSemantics RegexSSS FolianceProperties.
From PositionAutomata.Grammar Require Import RightLinearGrammar.
From PositionAutomata.Relations Require Import AmbiguityLR.

(** Paper-facing executable layer for Algorithm 2.

    The paper presents Algorithm 2 as a deterministic exponential-time search
    for k-foliance strings.  This file packages the existing executable solver
    from [FolianceProperties] as that evaluation layer and proves the
    witness-producing and Boolean decision interfaces correct. *)

Section FolianceDecision.
  Context {A : Type}.

  Definition foliance_witness
      (m : @finite_nfa A)
      (k : nat)
      (w : list A) : Prop :=
    word_over (fnfa_alphabet m) w /\ k_foliance m k w.

  Definition foliance_has_foliance
      (m : @finite_nfa A)
      (k : nat) : Prop :=
    exists w, foliance_witness m k w.

  Definition foliance_solve_foliance
      (m : @finite_nfa A)
      (k : nat) : option (list A) :=
    solve_foliance m k.

  Definition foliance_decide_foliance
      (m : @finite_nfa A)
      (k : nat) : bool :=
    match foliance_solve_foliance m k with
    | Some _ => true
    | None => false
    end.

  Definition foliance_solve_regex_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : option (list A) :=
    solve_regex_foliance alphabet label_matches r k.

  Definition foliance_decide_regex_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : bool :=
    match foliance_solve_regex_foliance alphabet label_matches r k with
    | Some _ => true
    | None => false
    end.

  Definition foliance_regex_has_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : Prop :=
    foliance_has_foliance
      (regex_foliance_nfa alphabet label_matches r)
      k.

  Theorem foliance_solve_foliance_sound :
    forall (m : @finite_nfa A) k w,
      foliance_solve_foliance m k = Some w ->
      foliance_witness m k w.
  Proof.
    intros m k w Hsolve.
    unfold foliance_solve_foliance in Hsolve.
    apply solve_foliance_sound in Hsolve as [Hin Hfoliance].
    apply candidate_words_sound in Hin as [_ Hover].
    split; assumption.
  Qed.

  Theorem foliance_solve_foliance_complete :
    forall (m : @finite_nfa A) k,
      foliance_has_foliance m k ->
      exists w,
        foliance_solve_foliance m k = Some w /\
        foliance_witness m k w.
  Proof.
    intros m k [w [Hover Hfoliance]].
    assert (Hlen : length w <= k).
    { exact (proj1 Hfoliance). }
    assert (Hin : In w (candidate_words m k)).
    {
      apply candidate_words_complete; assumption.
    }
    unfold foliance_solve_foliance.
    destruct
      (solve_foliance_complete_over_candidates
         m k (ex_intro _ w (conj Hin Hfoliance)))
      as [w' [Hsolve [Hin' Hfoliance']]].
    exists w'. split.
    - exact Hsolve.
    - apply candidate_words_sound in Hin' as [_ Hover'].
      split; assumption.
  Qed.

  Theorem foliance_solve_foliance_some_iff :
    forall (m : @finite_nfa A) k,
      (exists w, foliance_solve_foliance m k = Some w) <->
      foliance_has_foliance m k.
  Proof.
    intros m k. split.
    - intros [w Hsolve].
      exists w. now apply foliance_solve_foliance_sound in Hsolve.
    - intros Hhas.
      destruct (foliance_solve_foliance_complete m k Hhas)
        as [w [Hsolve _]].
      exists w. exact Hsolve.
  Qed.

  Theorem foliance_decide_foliance_correct :
    forall (m : @finite_nfa A) k,
      foliance_decide_foliance m k = true <->
      foliance_has_foliance m k.
  Proof.
    intros m k.
    unfold foliance_decide_foliance.
    destruct (foliance_solve_foliance m k) as [w |] eqn:Hsolve.
    - split; intros _.
      + exists w. now apply foliance_solve_foliance_sound.
      + reflexivity.
    - split; intros H.
      + discriminate.
      + destruct (foliance_solve_foliance_complete m k H)
          as [w [Hsolve' _]].
        rewrite Hsolve in Hsolve'. discriminate.
  Qed.

  Theorem foliance_solve_regex_foliance_sound :
    forall alphabet label_matches (r : regex A) k w,
      foliance_solve_regex_foliance alphabet label_matches r k = Some w ->
      foliance_witness
        (regex_foliance_nfa alphabet label_matches r)
        k
        w.
  Proof.
    intros alphabet label_matches r k w Hsolve.
    unfold foliance_solve_regex_foliance, solve_regex_foliance in Hsolve.
    change
      (foliance_solve_foliance
         (regex_foliance_nfa alphabet label_matches r) k = Some w)
      in Hsolve.
    now apply foliance_solve_foliance_sound in Hsolve.
  Qed.

  Theorem foliance_solve_regex_foliance_complete :
    forall alphabet label_matches (r : regex A) k,
      foliance_regex_has_foliance alphabet label_matches r k ->
      exists w,
        foliance_solve_regex_foliance alphabet label_matches r k = Some w /\
        foliance_witness
          (regex_foliance_nfa alphabet label_matches r)
          k
          w.
  Proof.
    intros alphabet label_matches r k Hhas.
    unfold foliance_regex_has_foliance in Hhas.
    destruct
      (foliance_solve_foliance_complete
         (regex_foliance_nfa alphabet label_matches r) k Hhas)
      as [w [Hsolve Hw]].
    exists w. split.
    - unfold foliance_solve_regex_foliance, solve_regex_foliance.
      exact Hsolve.
    - exact Hw.
  Qed.

  Theorem foliance_solve_regex_foliance_some_iff :
    forall alphabet label_matches (r : regex A) k,
      (exists w,
        foliance_solve_regex_foliance alphabet label_matches r k = Some w) <->
      foliance_regex_has_foliance alphabet label_matches r k.
  Proof.
    intros alphabet label_matches r k. split.
    - intros [w Hsolve].
      exists w. now apply foliance_solve_regex_foliance_sound in Hsolve.
    - intros Hhas.
      destruct
        (foliance_solve_regex_foliance_complete
           alphabet label_matches r k Hhas)
        as [w [Hsolve _]].
      exists w. exact Hsolve.
  Qed.

  Theorem foliance_decide_regex_foliance_correct :
    forall alphabet label_matches (r : regex A) k,
      foliance_decide_regex_foliance alphabet label_matches r k = true <->
      foliance_regex_has_foliance alphabet label_matches r k.
  Proof.
    intros alphabet label_matches r k.
    unfold foliance_decide_regex_foliance.
    destruct
      (foliance_solve_regex_foliance alphabet label_matches r k)
      as [w |] eqn:Hsolve.
    - split; intros _.
      + exists w. now eapply foliance_solve_regex_foliance_sound.
      + reflexivity.
    - split; intros H.
      + discriminate.
      + destruct
          (foliance_solve_regex_foliance_complete
             alphabet label_matches r k H)
          as [w [Hsolve' _]].
        rewrite Hsolve in Hsolve'. discriminate.
  Qed.
End FolianceDecision.

Section FolianceMachineLayer.
  Context {A : Type}.

  Fixpoint foliance_sigma_regex (alphabet : list A) : regex A :=
    match alphabet with
    | [] => Empty
    | [a] => Atom a
    | a :: alphabet' => Alt (Atom a) (foliance_sigma_regex alphabet')
    end.

  Definition foliance_sigma_star_regex (alphabet : list A) : regex A :=
    Star (foliance_sigma_regex alphabet).

  Definition foliance_pref_regex
      (alphabet : list A) (r : regex A) : regex A :=
    Cat (foliance_sigma_star_regex alphabet) r.

  Definition foliance_msss_machine
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : @finite_enfa A :=
    regex_Msss alphabet label_matches r.

  Definition foliance_msss_start
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      : enfa_state
          (fenfa_base
             (foliance_msss_machine alphabet label_matches r)) :=
    sss_start (sss_compile r).

  Definition foliance_gamma_grammar
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      : right_linear_grammar :=
    gamma_grammar_from
      (foliance_msss_machine alphabet label_matches r)
      (foliance_msss_start alphabet label_matches r).

  Definition foliance_lr_machine
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      : lr1_machine
          (enfa_state
             (fenfa_base
                (foliance_msss_machine alphabet label_matches r))) :=
    lr1_machine_of_enfa
      A_eq_dec
      (foliance_msss_machine alphabet label_matches r).

  Definition foliance_msss_leaf
      (m : @finite_enfa A) (w : list A) : nat :=
    enfa_leaf_prime_word m w.

  Definition foliance_msss_rejected
      (m : @finite_enfa A) (w : list A) : Prop :=
    enfa_da_prime_word m w = 0.

  Definition foliance_msss_rejectedb
      (m : @finite_enfa A) (w : list A) : bool :=
    Nat.eqb (enfa_da_prime_word m w) 0.

  Definition foliance_msss_leaf_prefix_max
      (m : @finite_enfa A) (w : list A) : nat :=
    max_nats (map (foliance_msss_leaf m) (prefixes w)).

  Definition foliance_msss_prefix_rejected
      (m : @finite_enfa A) (w : list A) : Prop :=
    forall u, In u (prefixes w) -> foliance_msss_rejected m u.

  Definition foliance_msss_prefix_rejectedb
      (m : @finite_enfa A) (w : list A) : bool :=
    forallb (foliance_msss_rejectedb m) (prefixes w).

  Definition foliance_msss_foliance_against
      (count_m reject_m : @finite_enfa A)
      (k : nat)
      (w : list A) : Prop :=
    length w <= k /\
    word_over (fenfa_alphabet count_m) w /\
    foliance_msss_rejected reject_m w /\
    k <= foliance_msss_leaf_prefix_max count_m w.

  Definition foliance_msss_foliance
      (m : @finite_enfa A) (k : nat) (w : list A) : Prop :=
    foliance_msss_foliance_against m m k w.

  Definition foliance_msss_foliance_pref_against
      (count_m reject_m : @finite_enfa A)
      (k : nat)
      (w : list A) : Prop :=
    length w <= k /\
    word_over (fenfa_alphabet count_m) w /\
    foliance_msss_prefix_rejected reject_m w /\
    k <= foliance_msss_leaf_prefix_max count_m w.

  Definition foliance_msss_foliance_againstb
      (count_m reject_m : @finite_enfa A)
      (k : nat)
      (w : list A) : bool :=
    (length w <=? k)
    && foliance_msss_rejectedb reject_m w
    && (k <=? foliance_msss_leaf_prefix_max count_m w).

  Definition foliance_msss_folianceb
      (m : @finite_enfa A) (k : nat) (w : list A) : bool :=
    foliance_msss_foliance_againstb m m k w.

  Definition foliance_msss_foliance_pref_againstb
      (count_m reject_m : @finite_enfa A)
      (k : nat)
      (w : list A) : bool :=
    (length w <=? k)
    && foliance_msss_prefix_rejectedb reject_m w
    && (k <=? foliance_msss_leaf_prefix_max count_m w).

  Definition foliance_msss_has_foliance_against
      (count_m reject_m : @finite_enfa A) (k : nat) : Prop :=
    exists w, foliance_msss_foliance_against count_m reject_m k w.

  Definition foliance_msss_has_foliance
      (m : @finite_enfa A) (k : nat) : Prop :=
    foliance_msss_has_foliance_against m m k.

  Definition foliance_msss_has_foliance_pref_against
      (count_m reject_m : @finite_enfa A) (k : nat) : Prop :=
    exists w, foliance_msss_foliance_pref_against count_m reject_m k w.

  Definition foliance_msss_k_co_empty
      (m : @finite_enfa A) (k : nat) : Prop :=
    forall w, length w <= k -> 0 < enfa_da_prime_word m w.

  Definition foliance_contains_match
      (alphabet : list A) (r : regex A) (w : list A) : Prop :=
    matches
      (Cat (foliance_pref_regex alphabet r)
           (foliance_sigma_star_regex alphabet))
      w.

  Theorem foliance_msss_foliance_eta_prefix_witness :
    forall (count_m reject_m : @finite_enfa A) k w,
      foliance_msss_foliance_against count_m reject_m k w ->
      exists u,
        In u (prefixes w) /\
        k <= enfa_leaf_prime_word count_m u.
  Proof.
    intros count_m reject_m [| k] w [_ [_ [_ Hleaf]]].
    - exists []. split.
      + destruct w as [| a w]; simpl; auto.
      + lia.
    - destruct
        (max_nats_positive_witness
           (map (foliance_msss_leaf count_m) (prefixes w)))
        as [n [Hn Hmax]].
      {
        unfold foliance_msss_leaf_prefix_max in Hleaf. lia.
      }
      apply in_map_iff in Hn as [u [Hu Hprefix]].
      subst n.
      exists u. split; auto.
      unfold foliance_msss_leaf_prefix_max in Hleaf.
      unfold foliance_msss_leaf in Hmax |- *.
      rewrite Hmax. exact Hleaf.
  Qed.

  Theorem foliance_msss_foliance_not_k_co_empty :
    forall (m : @finite_enfa A) k w,
      foliance_msss_foliance m k w ->
      ~ foliance_msss_k_co_empty m k.
  Proof.
    intros m k w [Hlen [_ [Hrejected _]]] Hcoempty.
    specialize (Hcoempty w Hlen).
    unfold foliance_msss_rejected in Hrejected.
    lia.
  Qed.

  Theorem foliance_prefix_language_rejection_excludes_factor :
    forall alphabet (r : regex A) w,
      (forall u,
         In u (prefixes w) ->
         ~ matches (foliance_pref_regex alphabet r) u) ->
      ~ foliance_contains_match alphabet r w.
  Proof.
    intros alphabet r w Hprefix Hfactor.
    unfold foliance_contains_match in Hfactor.
    inversion Hfactor; subst.
    match goal with
    | Hleft : matches (foliance_pref_regex alphabet r) ?u,
      Hright : matches (foliance_sigma_star_regex alphabet) ?v |- _ =>
        apply (Hprefix u)
    end.
    - apply prefixes_complete. eexists. reflexivity.
    - assumption.
  Qed.

  Theorem foliance_msss_pref_excludes_factor_under_language_rejection :
    forall alphabet (r : regex A)
      (count_m reject_m : @finite_enfa A) k w,
      (forall u,
         foliance_msss_rejected reject_m u ->
         ~ matches (foliance_pref_regex alphabet r) u) ->
      foliance_msss_foliance_pref_against count_m reject_m k w ->
      ~ foliance_contains_match alphabet r w.
  Proof.
    intros alphabet r count_m reject_m k w Hreject
      [_ [_ [Hprefix _]]].
    apply foliance_prefix_language_rejection_excludes_factor.
    intros u Hu.
    now apply Hreject, Hprefix.
  Qed.

  Lemma foliance_msss_rejectedb_correct :
    forall (m : @finite_enfa A) w,
      foliance_msss_rejectedb m w = true <->
      foliance_msss_rejected m w.
  Proof.
    intros m w.
    unfold foliance_msss_rejectedb, foliance_msss_rejected.
    apply Nat.eqb_eq.
  Qed.

  Lemma foliance_msss_prefix_rejectedb_correct :
    forall (m : @finite_enfa A) w,
      foliance_msss_prefix_rejectedb m w = true <->
      foliance_msss_prefix_rejected m w.
  Proof.
    intros m w.
    unfold foliance_msss_prefix_rejectedb,
      foliance_msss_prefix_rejected.
    split; intros H.
    - intros u Hu.
      apply foliance_msss_rejectedb_correct.
      rewrite forallb_forall in H.
      now apply H.
    - apply forallb_forall.
      intros u Hu.
      apply foliance_msss_rejectedb_correct.
      now apply H.
  Qed.

  Lemma foliance_msss_foliance_againstb_correct :
    forall (count_m reject_m : @finite_enfa A) k w,
      word_over (fenfa_alphabet count_m) w ->
      foliance_msss_foliance_againstb count_m reject_m k w = true <->
      foliance_msss_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w Hover.
    unfold foliance_msss_foliance_againstb,
      foliance_msss_foliance_against.
    split; intros H.
    - apply andb_true_iff in H as [Hleft Hleaf].
      apply andb_true_iff in Hleft as [Hlen Hreject].
      apply Nat.leb_le in Hlen.
      apply foliance_msss_rejectedb_correct in Hreject.
      apply Nat.leb_le in Hleaf.
      repeat split; assumption.
    - destruct H as [Hlen [_ [Hreject Hleaf]]].
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * now apply Nat.leb_le.
        * now apply foliance_msss_rejectedb_correct.
      + now apply Nat.leb_le.
  Qed.

  Lemma foliance_msss_foliance_pref_againstb_correct :
    forall (count_m reject_m : @finite_enfa A) k w,
      word_over (fenfa_alphabet count_m) w ->
      foliance_msss_foliance_pref_againstb count_m reject_m k w = true <->
      foliance_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w Hover.
    unfold foliance_msss_foliance_pref_againstb,
      foliance_msss_foliance_pref_against.
    split; intros H.
    - apply andb_true_iff in H as [Hleft Hleaf].
      apply andb_true_iff in Hleft as [Hlen Hreject].
      apply Nat.leb_le in Hlen.
      apply foliance_msss_prefix_rejectedb_correct in Hreject.
      apply Nat.leb_le in Hleaf.
      repeat split; assumption.
    - destruct H as [Hlen [_ [Hreject Hleaf]]].
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * now apply Nat.leb_le.
        * now apply foliance_msss_prefix_rejectedb_correct.
      + now apply Nat.leb_le.
  Qed.

  Definition foliance_reach_set
      (m : @finite_enfa A)
      (w : list A) : list (enfa_state (fenfa_base m)) :=
    filter
      (fun q => 0 <? enfa_dra_prime_at m w q)
      (fenfa_states m).

  Definition foliance_delta_hat_prime
      (m : @finite_enfa A)
      (w : list A)
      (a : A) : list (enfa_state (fenfa_base m)) :=
    foliance_reach_set m (w ++ [a]).

  (** Exact size of a full finitely branching search tree.  The root counts
      as one node; a node at positive depth has [branching] subtrees. *)
  Fixpoint foliance_full_tree_nodes
      (branching depth : nat) : nat :=
    match depth with
    | O => 1
    | S depth' =>
        1 + branching * foliance_full_tree_nodes branching depth'
    end.

  Fixpoint foliance_search_space
      (alphabet : list A)
      (fuel : nat)
      (w : list A) : list (list A) :=
    w ::
    match fuel with
    | O => []
    | S fuel' =>
        concat
          (map
             (fun a => foliance_search_space alphabet fuel' (w ++ [a]))
             alphabet)
    end.

  (** [foliance_search_space] is a finite tree of exactly the size above.
      In particular, [fuel] bounds every root-to-leaf path. *)
  Theorem foliance_search_space_size :
    forall alphabet fuel w,
      length (foliance_search_space alphabet fuel w) =
      foliance_full_tree_nodes (length alphabet) fuel.
  Proof.
    intros alphabet fuel.
    induction fuel as [| fuel IH]; intros w; simpl.
    - reflexivity.
    - f_equal.
      assert (Hchildren :
        forall choices,
          length
            (concat
               (map
                  (fun a =>
                     foliance_search_space alphabet fuel (w ++ [a]))
                  choices)) =
          length choices *
            foliance_full_tree_nodes (length alphabet) fuel).
      {
        induction choices as [| a choices IHchoices]; simpl.
        - reflexivity.
        - rewrite length_app, IH, IHchoices. lia.
      }
      apply Hchildren.
  Qed.

  Lemma foliance_full_tree_nodes_pow_bound :
    forall branching depth,
      foliance_full_tree_nodes branching depth <=
      Nat.pow (S branching) (S depth).
  Proof.
    intros branching depth.
    induction depth as [| depth IH]; simpl.
    - lia.
    - assert (Hpow_nonzero :
        Nat.pow (S branching) (S depth) <> 0).
      { apply Nat.pow_nonzero. lia. }
      assert (Hpow_positive :
        0 < Nat.pow (S branching) (S depth)) by lia.
      pose proof
        (Nat.mul_le_mono_l _ _ branching IH) as Hmul.
      change
        (1 + branching * foliance_full_tree_nodes branching depth <=
         S branching * Nat.pow (S branching) (S depth)).
      rewrite Nat.mul_succ_l.
      lia.
  Qed.

  Corollary foliance_search_space_pow_bound :
    forall alphabet fuel w,
      length (foliance_search_space alphabet fuel w) <=
      Nat.pow (S (length alphabet)) (S fuel).
  Proof.
    intros alphabet fuel w.
    rewrite foliance_search_space_size.
    apply foliance_full_tree_nodes_pow_bound.
  Qed.

  Definition foliance_search_children_space
      (alphabet : list A)
      (fuel : nat)
      (w : list A) : list (list A) :=
    match fuel with
    | O => []
    | S fuel' =>
        concat
          (map
             (fun a => foliance_search_space alphabet fuel' (w ++ [a]))
             alphabet)
    end.

  Definition foliance_search
      (count_m reject_m : @finite_enfa A)
      (k fuel : nat)
      (_X : list (enfa_state (fenfa_base count_m)))
      (w : list A)
      (_leaf_max : nat) : option (list A) :=
    find
      (foliance_msss_foliance_againstb count_m reject_m k)
      (foliance_search_space (fenfa_alphabet count_m) fuel w).

  Definition foliance_search_children
      (count_m reject_m : @finite_enfa A)
      (k fuel : nat)
      (alphabet : list A)
      (w : list A)
      (_leaf_max : nat) : option (list A) :=
    find
      (foliance_msss_foliance_againstb count_m reject_m k)
      (foliance_search_children_space alphabet fuel w).

  Definition foliance_search_pref
      (count_m reject_m : @finite_enfa A)
      (k fuel : nat)
      (_X : list (enfa_state (fenfa_base count_m)))
      (w : list A)
      (_leaf_max : nat) : option (list A) :=
    find
      (foliance_msss_foliance_pref_againstb count_m reject_m k)
      (foliance_search_space (fenfa_alphabet count_m) fuel w).

  Fixpoint foliance_first_some {B : Type} (xs : list (option B))
      : option B :=
    match xs with
    | [] => None
    | Some x :: _ => Some x
    | None :: xs' => foliance_first_some xs'
    end.

  (** Termination certificate for the paper's depth-first [SearchPref].

      The recursive argument is [fuel].  Every recursive call is made only in
      the [S fuel'] branch and receives [fuel']; the map ranges over the finite
      list [fenfa_alphabet count_m].  The top-level wrapper below supplies
      [fuel := k], which is complete because every admissible witness has
      length at most [k].

      This search fuel is distinct from the trace-enumeration fuel used by
      [traces_from_fuel].  The latter is instantiated with
      [enfa_trace_bound m w]; its sufficiency for epsilon-simple traces is
      proved by [epsilon_simple_valid_trace_length_bound] and
      [reach_ambiguity_enfa_prime_trace_enumerated_from_single_start]. *)
  Fixpoint foliance_search_pref_dfs
      (count_m reject_m : @finite_enfa A)
      (k fuel : nat)
      (_X : list (enfa_state (fenfa_base reject_m)))
      (w : list A)
      (_leaf : nat)
      (leaf_sup : nat) {struct fuel} : option (list A) :=
    if foliance_msss_rejectedb reject_m w then
      if k <=? leaf_sup then Some w
      else
        match fuel with
        | O => None
        | S fuel' =>
            foliance_first_some
              (map
                 (fun a =>
                    let wa := w ++ [a] in
                    let Y := foliance_reach_set reject_m wa in
                    let leaf' := foliance_msss_leaf count_m wa in
                    let leaf_sup' := Nat.max leaf_sup leaf' in
                    if foliance_msss_rejectedb reject_m wa then
                      foliance_search_pref_dfs
                        count_m reject_m k fuel' Y wa leaf' leaf_sup'
                    else None)
                 (fenfa_alphabet count_m))
        end
    else None.

  Definition foliance_search_msss_foliance_against
      (count_m reject_m : @finite_enfa A)
      (k : nat) : option (list A) :=
    foliance_search
      count_m reject_m k k
      (foliance_reach_set count_m [])
      []
      (foliance_msss_leaf count_m []).

  Definition foliance_search_msss_foliance
      (m : @finite_enfa A) (k : nat) : option (list A) :=
    foliance_search_msss_foliance_against m m k.

  Definition foliance_search_msss_foliance_pref_against
      (count_m reject_m : @finite_enfa A)
      (k : nat) : option (list A) :=
    foliance_search_pref
      count_m reject_m k k
      (foliance_reach_set count_m [])
      []
      (foliance_msss_leaf count_m []).

  Definition foliance_search_msss_foliance_pref_against_dfs
      (count_m reject_m : @finite_enfa A)
      (k : nat) : option (list A) :=
    foliance_search_pref_dfs
      count_m reject_m k k
      (foliance_reach_set reject_m [])
      []
      (foliance_msss_leaf count_m [])
      (foliance_msss_leaf count_m []).

  Definition foliance_decide_msss_foliance_against
      (count_m reject_m : @finite_enfa A)
      (k : nat) : bool :=
    match foliance_search_msss_foliance_against count_m reject_m k with
    | Some _ => true
    | None => false
    end.

  Definition foliance_decide_msss_foliance
      (m : @finite_enfa A) (k : nat) : bool :=
    foliance_decide_msss_foliance_against m m k.

  Definition foliance_decide_msss_foliance_pref_against
      (count_m reject_m : @finite_enfa A)
      (k : nat) : bool :=
    match foliance_search_msss_foliance_pref_against count_m reject_m k with
    | Some _ => true
    | None => false
    end.

  Definition foliance_decide_msss_foliance_pref_against_dfs
      (count_m reject_m : @finite_enfa A)
      (k : nat) : bool :=
    match foliance_search_msss_foliance_pref_against_dfs count_m reject_m k with
    | Some _ => true
    | None => false
    end.

  Definition foliance_search_regex_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : option (list A) :=
    foliance_search_msss_foliance
      (foliance_msss_machine alphabet label_matches r)
      k.

  Definition foliance_decide_regex_msss_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : bool :=
    foliance_decide_msss_foliance
      (foliance_msss_machine alphabet label_matches r)
      k.

  Definition foliance_search_regex_foliance_pref
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (count_r reject_r : regex A)
      (k : nat) : option (list A) :=
    foliance_search_msss_foliance_pref_against
      (foliance_msss_machine alphabet label_matches count_r)
      (foliance_msss_machine
         alphabet label_matches (foliance_pref_regex alphabet reject_r))
      k.

  Definition foliance_search_regex_foliance_pref_dfs
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (count_r reject_r : regex A)
      (k : nat) : option (list A) :=
    foliance_search_msss_foliance_pref_against_dfs
      (foliance_msss_machine alphabet label_matches count_r)
      (foliance_msss_machine
         alphabet label_matches (foliance_pref_regex alphabet reject_r))
      k.

  Definition foliance_decide_regex_msss_foliance_pref_dfs
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (count_r reject_r : regex A)
      (k : nat) : bool :=
    foliance_decide_msss_foliance_pref_against_dfs
      (foliance_msss_machine alphabet label_matches count_r)
      (foliance_msss_machine
         alphabet label_matches (foliance_pref_regex alphabet reject_r))
      k.

  Lemma foliance_word_over_app :
    forall alphabet (u v : list A),
      word_over alphabet u ->
      word_over alphabet v ->
      word_over alphabet (u ++ v).
  Proof.
    intros alphabet u v Hu Hv.
    unfold word_over in *.
    now apply Forall_app.
  Qed.

  Lemma foliance_word_over_snoc :
    forall alphabet (w : list A) a,
      word_over alphabet w ->
      In a alphabet ->
      word_over alphabet (w ++ [a]).
  Proof.
    intros alphabet w a Hw Ha.
    apply foliance_word_over_app; auto.
    constructor; auto.
  Qed.

  Lemma foliance_first_some_sound :
    forall (B : Type) (xs : list (option B)) x,
      foliance_first_some xs = Some x ->
      In (Some x) xs.
  Proof.
    intros B xs.
    induction xs as [| [y |] xs IH]; intros x H; simpl in H; try discriminate.
    - inversion H; subst. simpl. auto.
    - simpl. right. now apply IH.
  Qed.

  Lemma foliance_first_some_complete :
    forall (B : Type) (xs : list (option B)) x,
      In (Some x) xs ->
      exists y, foliance_first_some xs = Some y.
  Proof.
    intros B xs.
    induction xs as [| [y |] xs IH]; intros x Hin; simpl in Hin; try contradiction.
    - exists y. reflexivity.
    - destruct Hin as [Hhead | Hin].
      + discriminate.
      + now apply IH with (x := x).
  Qed.

  Lemma foliance_prefixes_snoc :
    forall (w : list A) a,
      prefixes (w ++ [a]) = prefixes w ++ [w ++ [a]].
  Proof.
    induction w as [| b w IH]; intros a; simpl.
    - reflexivity.
    - rewrite IH, map_app. reflexivity.
  Qed.

  Lemma foliance_max_nats_app_single :
    forall xs n,
      max_nats (xs ++ [n]) = Nat.max (max_nats xs) n.
  Proof.
    induction xs as [| x xs IH]; intros n; simpl.
    - apply Nat.max_comm.
    - rewrite IH, Nat.max_assoc. reflexivity.
  Qed.

  Lemma foliance_leaf_prefix_max_snoc :
    forall (count_m : @finite_enfa A) w a,
      foliance_msss_leaf_prefix_max count_m (w ++ [a]) =
      Nat.max
        (foliance_msss_leaf_prefix_max count_m w)
        (foliance_msss_leaf count_m (w ++ [a])).
  Proof.
    intros count_m w a.
    unfold foliance_msss_leaf_prefix_max.
    rewrite foliance_prefixes_snoc, map_app.
    simpl. apply foliance_max_nats_app_single.
  Qed.

  Lemma foliance_msss_prefix_rejected_prefix :
    forall (m : @finite_enfa A) u w,
      prefix_of u w ->
      foliance_msss_prefix_rejected m w ->
      foliance_msss_prefix_rejected m u.
  Proof.
    intros m u w Hprefix Hreject v Hv.
    apply Hreject.
    apply prefixes_complete.
    destruct Hprefix as [suffix Hw].
    pose proof (prefixes_sound u v Hv) as [middle Hu].
    subst u w.
    exists (middle ++ suffix).
    now rewrite app_assoc.
  Qed.

  Lemma foliance_msss_prefix_rejected_snoc :
    forall (m : @finite_enfa A) w a,
      foliance_msss_prefix_rejected m w ->
      foliance_msss_rejected m (w ++ [a]) ->
      foliance_msss_prefix_rejected m (w ++ [a]).
  Proof.
    intros m w a Hprefix Hlast u Hu.
    rewrite foliance_prefixes_snoc in Hu.
    apply in_app_or in Hu as [Hu | Hu].
    - now apply Hprefix.
    - destruct Hu as [Hu | []]. now subst u.
  Qed.

  Lemma foliance_msss_prefix_rejected_nil :
    forall (m : @finite_enfa A),
      foliance_msss_rejected m [] ->
      foliance_msss_prefix_rejected m [].
  Proof.
    intros m Hreject u Hu.
    simpl in Hu. destruct Hu as [Hu | []].
    now subst u.
  Qed.

  Lemma foliance_search_space_sound :
    forall alphabet fuel w v,
      In v (foliance_search_space alphabet fuel w) ->
      exists suffix,
        v = w ++ suffix /\
        length suffix <= fuel /\
        word_over alphabet suffix.
  Proof.
    intros alphabet fuel.
    induction fuel as [| fuel IH]; intros w v Hin; simpl in Hin.
    - destruct Hin as [Hv | []].
      subst v. exists [].
      split; [now rewrite app_nil_r |].
      split; [simpl; lia | constructor].
    - destruct Hin as [Hv | Hin].
      + subst v. exists [].
        split; [now rewrite app_nil_r |].
        split; [simpl; lia | constructor].
      + apply in_concat in Hin as [xs [Hxs Hv]].
        apply in_map_iff in Hxs as [a [Hxs Ha]].
        subst xs.
        destruct (IH (w ++ [a]) v Hv)
          as [suffix [Hsuf [Hlen Hover]]].
        subst v.
        exists (a :: suffix). repeat split.
        * rewrite <- app_assoc. reflexivity.
        * simpl. lia.
        * constructor; assumption.
  Qed.

  Lemma foliance_search_space_complete :
    forall alphabet fuel w suffix,
      length suffix <= fuel ->
      word_over alphabet suffix ->
      In (w ++ suffix) (foliance_search_space alphabet fuel w).
  Proof.
    intros alphabet fuel.
    induction fuel as [| fuel IH]; intros w suffix Hlen Hover; simpl.
    - assert (suffix = []) by (destruct suffix; simpl in Hlen; try lia; auto).
      subst suffix. simpl. left. now rewrite app_nil_r.
    - destruct suffix as [| a suffix].
      + left. now rewrite app_nil_r.
      + right.
        inversion Hover as [| ? ? Ha Hover']; subst.
        apply in_concat.
        exists (foliance_search_space alphabet fuel (w ++ [a])).
        split.
        * apply in_map_iff. exists a. split; auto.
        * replace (w ++ a :: suffix) with ((w ++ [a]) ++ suffix)
            by (rewrite <- app_assoc; reflexivity).
          apply IH.
          -- simpl in Hlen. lia.
          -- exact Hover'.
  Qed.

  Theorem foliance_search_sound :
    forall (count_m reject_m : @finite_enfa A) k fuel X w leaf_max v,
      word_over (fenfa_alphabet count_m) w ->
      foliance_search count_m reject_m k fuel X w leaf_max = Some v ->
      foliance_msss_foliance_against count_m reject_m k v.
  Proof.
    intros count_m reject_m k fuel X w leaf_max v Hover_w Hsearch.
    unfold foliance_search in Hsearch.
    apply find_sound in Hsearch as [Hin Hpred].
    destruct
      (foliance_search_space_sound
         (fenfa_alphabet count_m) fuel w v Hin)
      as [suffix [Hv [_ Hover_suffix]]].
    assert (Hover_v : word_over (fenfa_alphabet count_m) v).
    {
      subst v.
      now apply foliance_word_over_app.
    }
    now apply foliance_msss_foliance_againstb_correct.
  Qed.

  Theorem foliance_search_pref_sound :
    forall (count_m reject_m : @finite_enfa A) k fuel X w leaf_max v,
      word_over (fenfa_alphabet count_m) w ->
      foliance_search_pref count_m reject_m k fuel X w leaf_max = Some v ->
      foliance_msss_foliance_pref_against count_m reject_m k v.
  Proof.
    intros count_m reject_m k fuel X w leaf_max v Hover_w Hsearch.
    unfold foliance_search_pref in Hsearch.
    apply find_sound in Hsearch as [Hin Hpred].
    destruct
      (foliance_search_space_sound
         (fenfa_alphabet count_m) fuel w v Hin)
      as [suffix [Hv [_ Hover_suffix]]].
    assert (Hover_v : word_over (fenfa_alphabet count_m) v).
    {
      subst v.
      now apply foliance_word_over_app.
    }
    now apply foliance_msss_foliance_pref_againstb_correct.
  Qed.

  Theorem foliance_search_msss_foliance_against_sound :
    forall (count_m reject_m : @finite_enfa A) k w,
      foliance_search_msss_foliance_against count_m reject_m k = Some w ->
      foliance_msss_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w H.
    unfold foliance_search_msss_foliance_against in H.
    eapply foliance_search_sound; eauto.
    constructor.
  Qed.

  Theorem foliance_search_msss_foliance_pref_against_sound :
    forall (count_m reject_m : @finite_enfa A) k w,
      foliance_search_msss_foliance_pref_against count_m reject_m k = Some w ->
      foliance_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w H.
    unfold foliance_search_msss_foliance_pref_against in H.
    eapply foliance_search_pref_sound; eauto.
    constructor.
  Qed.

  Theorem foliance_search_msss_foliance_against_complete :
    forall (count_m reject_m : @finite_enfa A) k,
      foliance_msss_has_foliance_against count_m reject_m k ->
      exists w,
        foliance_search_msss_foliance_against count_m reject_m k = Some w /\
        foliance_msss_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k [w Hwit].
    destruct Hwit as [Hlen [Hover [Hreject Hleaf]]].
    unfold foliance_search_msss_foliance_against, foliance_search.
    assert (Hin :
      In w (foliance_search_space (fenfa_alphabet count_m) k [])).
    {
      replace w with ([] ++ w) by reflexivity.
      now apply foliance_search_space_complete.
    }
    assert (Hpred :
      foliance_msss_foliance_againstb count_m reject_m k w = true).
    {
      apply foliance_msss_foliance_againstb_correct; auto.
      repeat split; assumption.
    }
    destruct
      (find_complete
         (foliance_msss_foliance_againstb count_m reject_m k)
         (foliance_search_space (fenfa_alphabet count_m) k [])
         (ex_intro _ w (conj Hin Hpred)))
      as [w' [Hfind [Hin' Hpred']]].
    exists w'. split.
    - exact Hfind.
    - destruct
        (foliance_search_space_sound
           (fenfa_alphabet count_m) k [] w' Hin')
        as [suffix [Hw' [_ Hover_suffix]]].
      assert (Hover_w' : word_over (fenfa_alphabet count_m) w').
      {
        subst w'. simpl.
        exact Hover_suffix.
      }
      now apply foliance_msss_foliance_againstb_correct.
  Qed.

  Theorem foliance_search_msss_foliance_pref_against_complete :
    forall (count_m reject_m : @finite_enfa A) k,
      foliance_msss_has_foliance_pref_against count_m reject_m k ->
      exists w,
        foliance_search_msss_foliance_pref_against count_m reject_m k = Some w /\
        foliance_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k [w Hwit].
    destruct Hwit as [Hlen [Hover [Hreject Hleaf]]].
    unfold foliance_search_msss_foliance_pref_against, foliance_search_pref.
    assert (Hin :
      In w (foliance_search_space (fenfa_alphabet count_m) k [])).
    {
      replace w with ([] ++ w) by reflexivity.
      now apply foliance_search_space_complete.
    }
    assert (Hpred :
      foliance_msss_foliance_pref_againstb count_m reject_m k w = true).
    {
      apply foliance_msss_foliance_pref_againstb_correct; auto.
      repeat split; assumption.
    }
    destruct
      (find_complete
         (foliance_msss_foliance_pref_againstb count_m reject_m k)
         (foliance_search_space (fenfa_alphabet count_m) k [])
         (ex_intro _ w (conj Hin Hpred)))
      as [w' [Hfind [Hin' Hpred']]].
    exists w'. split.
    - exact Hfind.
    - destruct
        (foliance_search_space_sound
           (fenfa_alphabet count_m) k [] w' Hin')
        as [suffix [Hw' [_ Hover_suffix]]].
      assert (Hover_w' : word_over (fenfa_alphabet count_m) w').
      {
        subst w'. simpl.
        exact Hover_suffix.
      }
      now apply foliance_msss_foliance_pref_againstb_correct.
  Qed.

  Theorem foliance_search_pref_dfs_sound :
    forall (count_m reject_m : @finite_enfa A) k fuel X w leaf leaf_sup v,
      word_over (fenfa_alphabet count_m) w ->
      length w + fuel <= k ->
      foliance_msss_prefix_rejected reject_m w ->
      leaf_sup = foliance_msss_leaf_prefix_max count_m w ->
      foliance_search_pref_dfs
        count_m reject_m k fuel X w leaf leaf_sup = Some v ->
      foliance_msss_foliance_pref_against count_m reject_m k v.
  Proof.
    intros count_m reject_m k fuel.
    induction fuel as [| fuel IH];
      intros X w leaf leaf_sup v Hover Hlen Hprefix Hleafsup Hsearch;
      simpl in Hsearch.
    - destruct (foliance_msss_rejectedb reject_m w) eqn:Hreject;
        try discriminate.
      destruct (k <=? leaf_sup) eqn:Hleaf; inversion Hsearch; subst v.
      apply Nat.leb_le in Hleaf.
      repeat split; auto; try lia.
    - destruct (foliance_msss_rejectedb reject_m w) eqn:Hreject;
        try discriminate.
      destruct (k <=? leaf_sup) eqn:Hleaf.
      + inversion Hsearch; subst v.
        apply Nat.leb_le in Hleaf.
        repeat split; auto; try lia.
      + apply foliance_first_some_sound in Hsearch as Hin.
        apply in_map_iff in Hin as [a [Hchild Ha]].
        destruct
          (foliance_msss_rejectedb reject_m (w ++ [a]))
          eqn:Hchild_reject; try discriminate.
        eapply
          (IH
             (foliance_reach_set reject_m (w ++ [a]))
             (w ++ [a])
             (foliance_msss_leaf count_m (w ++ [a]))
             (Nat.max leaf_sup
                (foliance_msss_leaf count_m (w ++ [a])))).
        * eapply foliance_word_over_snoc; eauto.
        * rewrite length_app. simpl. lia.
        * apply foliance_msss_prefix_rejected_snoc; auto.
          now apply foliance_msss_rejectedb_correct.
        * rewrite Hleafsup. symmetry.
          apply foliance_leaf_prefix_max_snoc.
        * exact Hchild.
  Qed.

  Theorem foliance_search_msss_foliance_pref_against_dfs_sound :
    forall (count_m reject_m : @finite_enfa A) k w,
      foliance_search_msss_foliance_pref_against_dfs count_m reject_m k =
        Some w ->
      foliance_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w Hsearch.
    unfold foliance_search_msss_foliance_pref_against_dfs in Hsearch.
    destruct (foliance_msss_rejectedb reject_m []) eqn:Hreject.
    - apply
        (foliance_search_pref_dfs_sound
           count_m reject_m k k
           (foliance_reach_set reject_m [])
           []
           (foliance_msss_leaf count_m [])
           (foliance_msss_leaf count_m [])
           w).
      + constructor.
      + simpl. lia.
      + apply foliance_msss_prefix_rejected_nil.
        now apply foliance_msss_rejectedb_correct.
      + unfold foliance_msss_leaf_prefix_max.
        simpl. now rewrite Nat.max_0_r.
      + exact Hsearch.
    - destruct k as [| k']; simpl in Hsearch;
        rewrite Hreject in Hsearch; discriminate.
  Qed.

  Theorem foliance_search_pref_dfs_complete :
    forall (count_m reject_m : @finite_enfa A) k fuel X w leaf leaf_sup suffix,
      word_over (fenfa_alphabet count_m) w ->
      length w + fuel <= k ->
      foliance_msss_prefix_rejected reject_m w ->
      leaf_sup = foliance_msss_leaf_prefix_max count_m w ->
      length suffix <= fuel ->
      word_over (fenfa_alphabet count_m) suffix ->
      foliance_msss_foliance_pref_against
        count_m reject_m k (w ++ suffix) ->
      exists v,
        foliance_search_pref_dfs
          count_m reject_m k fuel X w leaf leaf_sup = Some v /\
        foliance_msss_foliance_pref_against count_m reject_m k v.
  Proof.
    intros count_m reject_m k fuel.
    induction fuel as [| fuel IH];
      intros X w leaf leaf_sup suffix Hover Hlen Hprefix Hleafsup
        Hsuffix_len Hsuffix_over Hwit.
    - assert (Hreject_w : foliance_msss_rejected reject_m w).
      { apply Hprefix. apply prefixes_refl. }
      assert (Hrejectb_w :
        foliance_msss_rejectedb reject_m w = true).
      { now apply foliance_msss_rejectedb_correct. }
      simpl. rewrite Hrejectb_w.
      destruct (k <=? leaf_sup) eqn:Hleaf.
      + exists w. split; [reflexivity |].
        apply Nat.leb_le in Hleaf.
        repeat split; auto; try lia.
      + apply Nat.leb_gt in Hleaf.
        destruct suffix as [| a suffix]; simpl in Hsuffix_len; try lia.
        simpl in Hwit.
        rewrite app_nil_r in Hwit.
        destruct Hwit as [_ [_ [_ Htarget_leaf]]].
        rewrite <- Hleafsup in Htarget_leaf. lia.
    - assert (Hreject_w : foliance_msss_rejected reject_m w).
      { apply Hprefix. apply prefixes_refl. }
      assert (Hrejectb_w :
        foliance_msss_rejectedb reject_m w = true).
      { now apply foliance_msss_rejectedb_correct. }
      simpl. rewrite Hrejectb_w.
      destruct (k <=? leaf_sup) eqn:Hleaf.
      + exists w. split; [reflexivity |].
        apply Nat.leb_le in Hleaf.
        repeat split; auto; try lia.
      + destruct suffix as [| a suffix].
        * apply Nat.leb_gt in Hleaf.
          simpl in Hwit. rewrite app_nil_r in Hwit.
          destruct Hwit as [_ [_ [_ Htarget_leaf]]].
          rewrite <- Hleafsup in Htarget_leaf. lia.
        * inversion Hsuffix_over as [| a0 suffix0 Ha Hsuffix_over'];
            subst a0 suffix0.
          assert (Hchild_prefix :
            foliance_msss_prefix_rejected reject_m (w ++ [a])).
          {
            eapply foliance_msss_prefix_rejected_prefix.
            - exists suffix. rewrite <- app_assoc. reflexivity.
            - exact (proj1 (proj2 (proj2 Hwit))).
          }
          assert (Hchild_reject :
            foliance_msss_rejectedb reject_m (w ++ [a]) = true).
          {
            apply foliance_msss_rejectedb_correct.
            apply Hchild_prefix. apply prefixes_refl.
          }
          assert (Hchild_leafsup :
            Nat.max leaf_sup (foliance_msss_leaf count_m (w ++ [a])) =
            foliance_msss_leaf_prefix_max count_m (w ++ [a])).
          {
            rewrite Hleafsup. symmetry.
            apply foliance_leaf_prefix_max_snoc.
          }
          assert (Hchild_len :
            length (w ++ [a]) + fuel <= k).
          { rewrite length_app. simpl. lia. }
          assert (Hchild_wit :
            foliance_msss_foliance_pref_against
              count_m reject_m k ((w ++ [a]) ++ suffix)).
          {
            replace ((w ++ [a]) ++ suffix) with (w ++ a :: suffix)
              by (rewrite <- app_assoc; reflexivity).
            exact Hwit.
          }
          destruct
            (IH
               (foliance_reach_set reject_m (w ++ [a]))
               (w ++ [a])
               (foliance_msss_leaf count_m (w ++ [a]))
               (Nat.max leaf_sup
                  (foliance_msss_leaf count_m (w ++ [a])))
               suffix)
            as [v [Hchild_search Hchild_result]].
          -- now apply foliance_word_over_snoc.
          -- exact Hchild_len.
          -- exact Hchild_prefix.
          -- exact Hchild_leafsup.
          -- simpl in Hsuffix_len. lia.
          -- exact Hsuffix_over'.
          -- exact Hchild_wit.
          -- assert (Hin_child :
               In (Some v)
                 (map
                    (fun a0 =>
                       let wa := w ++ [a0] in
                       let Y := foliance_reach_set reject_m wa in
                       let leaf' := foliance_msss_leaf count_m wa in
                       let leaf_sup' := Nat.max leaf_sup leaf' in
                       if foliance_msss_rejectedb reject_m wa then
                         foliance_search_pref_dfs
                           count_m reject_m k fuel Y wa leaf' leaf_sup'
                       else None)
                    (fenfa_alphabet count_m))).
             {
               apply in_map_iff. exists a. split.
               - simpl. rewrite Hchild_reject. exact Hchild_search.
               - exact Ha.
             }
             destruct
               (foliance_first_some_complete
                  _ _ _ Hin_child) as [v' Hfirst].
             exists v'. split.
             ++ exact Hfirst.
             ++ apply
                  (foliance_search_pref_dfs_sound
                     count_m reject_m k (S fuel) X w leaf leaf_sup v');
                  auto.
                simpl. rewrite Hrejectb_w, Hleaf. exact Hfirst.
  Qed.

  Theorem foliance_search_msss_foliance_pref_against_dfs_complete :
    forall (count_m reject_m : @finite_enfa A) k,
      foliance_msss_has_foliance_pref_against count_m reject_m k ->
      exists w,
        foliance_search_msss_foliance_pref_against_dfs count_m reject_m k =
          Some w /\
        foliance_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k [w Hwit].
    destruct Hwit as [Hlen [Hover [Hprefix Hleaf]]].
    assert (Hreject_nil : foliance_msss_rejected reject_m []).
    {
      apply Hprefix.
      apply prefixes_complete.
      exists w. reflexivity.
    }
    unfold foliance_search_msss_foliance_pref_against_dfs.
    eapply foliance_search_pref_dfs_complete with (suffix := w).
    - constructor.
    - simpl. lia.
    - apply foliance_msss_prefix_rejected_nil. exact Hreject_nil.
    - unfold foliance_msss_leaf_prefix_max.
      simpl. now rewrite Nat.max_0_r.
    - exact Hlen.
    - exact Hover.
    - simpl. repeat split; assumption.
  Qed.

  Theorem foliance_search_pref_dfs_some_iff :
    forall (count_m reject_m : @finite_enfa A) k,
      (exists w,
        foliance_search_msss_foliance_pref_against_dfs count_m reject_m k =
          Some w) <->
      foliance_msss_has_foliance_pref_against count_m reject_m k.
  Proof.
    intros count_m reject_m k. split.
    - intros [w H].
      exists w.
      now apply foliance_search_msss_foliance_pref_against_dfs_sound in H.
    - intros Hhas.
      destruct
        (foliance_search_msss_foliance_pref_against_dfs_complete
           count_m reject_m k Hhas)
        as [w [H _]].
      exists w. exact H.
  Qed.

  Theorem foliance_search_some_iff :
    forall (count_m reject_m : @finite_enfa A) k,
      (exists w,
        foliance_search_msss_foliance_against count_m reject_m k = Some w) <->
      foliance_msss_has_foliance_against count_m reject_m k.
  Proof.
    intros count_m reject_m k. split.
    - intros [w H].
      exists w.
      now apply foliance_search_msss_foliance_against_sound in H.
    - intros Hhas.
      destruct
        (foliance_search_msss_foliance_against_complete
           count_m reject_m k Hhas)
        as [w [H _]].
      exists w. exact H.
  Qed.

  Theorem foliance_search_pref_some_iff :
    forall (count_m reject_m : @finite_enfa A) k,
      (exists w,
        foliance_search_msss_foliance_pref_against count_m reject_m k = Some w) <->
      foliance_msss_has_foliance_pref_against count_m reject_m k.
  Proof.
    intros count_m reject_m k. split.
    - intros [w H].
      exists w.
      now apply foliance_search_msss_foliance_pref_against_sound in H.
    - intros Hhas.
      destruct
        (foliance_search_msss_foliance_pref_against_complete
           count_m reject_m k Hhas)
        as [w [H _]].
      exists w. exact H.
  Qed.

  (** Total-correctness interfaces.  Rocq's acceptance of the structurally
      recursive definitions supplies termination; these theorems combine that
      totality with the already proved soundness and completeness properties.
      Thus [None] is a proved negative answer, not fuel exhaustion. *)
  Theorem foliance_search_msss_foliance_against_total_correct :
    forall (count_m reject_m : @finite_enfa A) k,
      match
        foliance_search_msss_foliance_against count_m reject_m k
      with
      | Some w =>
          foliance_msss_foliance_against count_m reject_m k w
      | None =>
          ~ foliance_msss_has_foliance_against count_m reject_m k
      end.
  Proof.
    intros count_m reject_m k.
    destruct
      (foliance_search_msss_foliance_against count_m reject_m k)
      as [w |] eqn:Hsearch.
    - now apply foliance_search_msss_foliance_against_sound in Hsearch.
    - intros Hhas.
      destruct
        (foliance_search_msss_foliance_against_complete
           count_m reject_m k Hhas)
        as [w [Hsome _]].
      rewrite Hsearch in Hsome. discriminate.
  Qed.

  Theorem foliance_search_msss_foliance_pref_against_dfs_total_correct :
    forall (count_m reject_m : @finite_enfa A) k,
      match
        foliance_search_msss_foliance_pref_against_dfs count_m reject_m k
      with
      | Some w =>
          foliance_msss_foliance_pref_against count_m reject_m k w
      | None =>
          ~ foliance_msss_has_foliance_pref_against
              count_m reject_m k
      end.
  Proof.
    intros count_m reject_m k.
    destruct
      (foliance_search_msss_foliance_pref_against_dfs count_m reject_m k)
      as [w |] eqn:Hsearch.
    - now apply
        foliance_search_msss_foliance_pref_against_dfs_sound in Hsearch.
    - intros Hhas.
      destruct
        (foliance_search_msss_foliance_pref_against_dfs_complete
           count_m reject_m k Hhas)
        as [w [Hsome _]].
      rewrite Hsearch in Hsome. discriminate.
  Qed.

  Corollary foliance_search_msss_foliance_against_none_iff :
    forall (count_m reject_m : @finite_enfa A) k,
      foliance_search_msss_foliance_against count_m reject_m k = None <->
      ~ foliance_msss_has_foliance_against count_m reject_m k.
  Proof.
    intros count_m reject_m k. split.
    - intros Hnone.
      pose proof
        (foliance_search_msss_foliance_against_total_correct
           count_m reject_m k) as Htotal.
      now rewrite Hnone in Htotal.
    - intros Hnone.
      destruct
        (foliance_search_msss_foliance_against count_m reject_m k)
        as [w |] eqn:Hsearch; auto.
      exfalso. apply Hnone. exists w.
      now apply foliance_search_msss_foliance_against_sound in Hsearch.
  Qed.

  Corollary foliance_search_msss_foliance_pref_against_dfs_none_iff :
    forall (count_m reject_m : @finite_enfa A) k,
      foliance_search_msss_foliance_pref_against_dfs count_m reject_m k =
        None <->
      ~ foliance_msss_has_foliance_pref_against count_m reject_m k.
  Proof.
    intros count_m reject_m k. split.
    - intros Hnone.
      pose proof
        (foliance_search_msss_foliance_pref_against_dfs_total_correct
           count_m reject_m k) as Htotal.
      now rewrite Hnone in Htotal.
    - intros Hnone.
      destruct
        (foliance_search_msss_foliance_pref_against_dfs
           count_m reject_m k)
        as [w |] eqn:Hsearch; auto.
      exfalso. apply Hnone. exists w.
      now apply
        foliance_search_msss_foliance_pref_against_dfs_sound in Hsearch.
  Qed.

  Theorem foliance_decide_msss_correct :
    forall (m : @finite_enfa A) k,
      foliance_decide_msss_foliance m k = true <->
      foliance_msss_has_foliance m k.
  Proof.
    intros m k.
    unfold foliance_decide_msss_foliance,
      foliance_decide_msss_foliance_against.
    destruct (foliance_search_msss_foliance_against m m k) as [w |] eqn:H.
    - split; intros _.
      + exists w. now apply foliance_search_msss_foliance_against_sound.
      + reflexivity.
    - split; intros Hfalse.
      + discriminate.
      + destruct
          (foliance_search_msss_foliance_against_complete m m k Hfalse)
          as [w [Hsome _]].
        rewrite H in Hsome. discriminate.
  Qed.

  Theorem foliance_decide_msss_pref_correct :
    forall (count_m reject_m : @finite_enfa A) k,
      foliance_decide_msss_foliance_pref_against count_m reject_m k = true <->
      foliance_msss_has_foliance_pref_against count_m reject_m k.
  Proof.
    intros count_m reject_m k.
    unfold foliance_decide_msss_foliance_pref_against.
    destruct
      (foliance_search_msss_foliance_pref_against count_m reject_m k)
      as [w |] eqn:H.
    - split; intros _.
      + exists w. now apply foliance_search_msss_foliance_pref_against_sound.
      + reflexivity.
    - split; intros Hfalse.
      + discriminate.
      + destruct
          (foliance_search_msss_foliance_pref_against_complete
             count_m reject_m k Hfalse)
          as [w [Hsome _]].
        rewrite H in Hsome. discriminate.
  Qed.

  Theorem foliance_decide_msss_pref_dfs_correct :
    forall (count_m reject_m : @finite_enfa A) k,
      foliance_decide_msss_foliance_pref_against_dfs count_m reject_m k =
        true <->
      foliance_msss_has_foliance_pref_against count_m reject_m k.
  Proof.
    intros count_m reject_m k.
    unfold foliance_decide_msss_foliance_pref_against_dfs.
    destruct
      (foliance_search_msss_foliance_pref_against_dfs count_m reject_m k)
      as [w |] eqn:H.
    - split; intros _.
      + exists w. now apply foliance_search_msss_foliance_pref_against_dfs_sound.
      + reflexivity.
    - split; intros Hfalse.
      + discriminate.
      + destruct
          (foliance_search_msss_foliance_pref_against_dfs_complete
             count_m reject_m k Hfalse)
          as [w [Hsome _]].
        rewrite H in Hsome. discriminate.
  Qed.

  Theorem foliance_decide_regex_msss_foliance_pref_correct :
    forall alphabet label_matches (count_r reject_r : regex A) k,
      foliance_decide_regex_msss_foliance_pref_dfs
        alphabet label_matches count_r reject_r k = true <->
      foliance_msss_has_foliance_pref_against
        (foliance_msss_machine alphabet label_matches count_r)
        (foliance_msss_machine
           alphabet label_matches (foliance_pref_regex alphabet reject_r))
        k.
  Proof.
    intros alphabet label_matches count_r reject_r k.
    unfold foliance_decide_regex_msss_foliance_pref_dfs.
    apply foliance_decide_msss_pref_dfs_correct.
  Qed.

  Theorem foliance_msss_positive_da_prime_accepts :
    forall (m : @finite_enfa A) w,
      finite_enfa_wf m ->
      0 < enfa_da_prime_word m w ->
      enfa_accepts_word m w.
  Proof.
    intros m w Hwf Hpos.
    rewrite enfa_da_prime_word_flat in Hpos by exact Hwf.
    destruct
      (filter (enfa_accepting_maximal_started_traceb m)
         (started_traces m w))
      as [| st sts] eqn:Hfilter.
    - simpl in Hpos. lia.
    - assert (Hin_filter :
        In st
          (filter (enfa_accepting_maximal_started_traceb m)
             (started_traces m w))).
      { rewrite Hfilter. simpl. auto. }
      apply filter_In in Hin_filter as [Hin Haccepting].
      destruct st as [s t].
      destruct (started_traces_valid m w s t Hin) as [Hvalid Hword].
      exists s, (trace_end s t), t.
      repeat split.
      + eapply started_traces_start_in; eauto.
      + exact Hvalid.
      + exact Hword.
      + unfold enfa_accepting_maximal_started_traceb in Haccepting.
        apply andb_true_iff in Haccepting as [Hleft _].
        apply andb_true_iff in Hleft as [Haccepted _].
        exact Haccepted.
  Qed.

  Theorem foliance_regex_msss_positive_da_prime_language :
    forall alphabet label_matches (r : regex A) w,
      regex_symbol_closed alphabet label_matches r ->
      0 < enfa_da_prime_word
            (foliance_msss_machine alphabet label_matches r) w ->
      enfa_accepts_word
        (foliance_msss_machine alphabet label_matches r) w.
  Proof.
    intros alphabet label_matches r w Hclosed Hpos.
    eapply foliance_msss_positive_da_prime_accepts.
    - now apply regex_Msss_wf.
    - exact Hpos.
  Qed.

  Theorem foliance_msss_gamma_leaf_bridge :
    forall alphabet label_matches (r : regex A) word_eqb w,
      regex_symbol_closed alphabet label_matches r ->
      NoDup alphabet ->
      word_eqb_reflects_eq word_eqb ->
      foliance_msss_leaf
        (foliance_msss_machine alphabet label_matches r) w =
      rlg_prefix_leaf_prime_count
        (foliance_gamma_grammar alphabet label_matches r)
        (fenfa_state_eqb
           (foliance_msss_machine alphabet label_matches r))
        word_eqb
        (enfa_trace_bound
           (foliance_msss_machine alphabet label_matches r) w)
        w.
  Proof.
    intros alphabet label_matches r word_eqb w Hclosed Halphabet Hwordeq.
    unfold foliance_msss_leaf,
      foliance_gamma_grammar,
      foliance_msss_start.
    eapply reach_ambiguity_gamma_leaf_prime_count_eq_with_alphabet_nodup.
    - now apply regex_Msss_wf.
    - unfold foliance_msss_machine, regex_Msss. reflexivity.
    - exact Halphabet.
    - exact Hwordeq.
  Qed.

  Theorem foliance_lr_projected_leaf_bridge :
    forall A_eq_dec alphabet label_matches (r : regex A) w,
      lr1_projected_leaf_count
        A_eq_dec
        (foliance_msss_machine alphabet label_matches r)
        w =
      foliance_msss_leaf
        (foliance_msss_machine alphabet label_matches r)
        w.
  Proof.
    intros A_eq_dec alphabet label_matches r w.
    unfold foliance_msss_leaf.
    apply reach_ambiguity_lr1_leaf_preservation.
  Qed.
End FolianceMachineLayer.

Section FolianceDecisionExamples.
  Fixpoint foliance_bool_list_eqb (xs ys : list bool) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => Bool.eqb x y && foliance_bool_list_eqb xs' ys'
    | _, _ => false
    end.

  Lemma foliance_bool_list_eqb_sound :
    forall xs ys, foliance_bool_list_eqb xs ys = true -> xs = ys.
  Proof.
    induction xs as [| x xs IH]; intros ys H; destruct ys as [| y ys];
      simpl in H; try discriminate; auto.
    apply andb_true_iff in H as [Hxy Htail].
    destruct x, y; simpl in Hxy; try discriminate.
    - now rewrite (IH ys Htail).
    - now rewrite (IH ys Htail).
  Qed.

  Lemma foliance_bool_list_eqb_complete :
    forall xs ys, xs = ys -> foliance_bool_list_eqb xs ys = true.
  Proof.
    induction xs as [| x xs IH]; intros ys H; subst ys; simpl; auto.
    destruct x; simpl; now apply IH.
  Qed.

  Lemma foliance_bool_list_eqb_reflects_eq :
    word_eqb_reflects_eq foliance_bool_list_eqb.
  Proof.
    split.
    - apply foliance_bool_list_eqb_sound.
    - apply foliance_bool_list_eqb_complete.
  Qed.

  Lemma foliance_bool_foliance_ambiguous_a_closed :
    regex_symbol_closed [true; false] Bool.eqb foliance_ambiguous_a.
  Proof.
    intros b a _ Hmatch.
    destruct b, a; simpl in Hmatch; try discriminate; simpl; auto.
  Qed.

  Lemma foliance_bool_alphabet_nodup :
    NoDup [true; false].
  Proof.
    constructor.
    - simpl. intros [H | []]; discriminate.
    - constructor.
      + simpl. intros [].
      + constructor.
  Qed.

  Example foliance_foliance_ambiguous_a_solver :
    foliance_solve_regex_foliance
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      2 =
    Some [true; true].
  Proof. reflexivity. Qed.

  Example foliance_search_space_fuel_zero :
    foliance_search_space [true; false] 0 [true] = [[true]].
  Proof. reflexivity. Qed.

  Example foliance_full_tree_nodes_binary_depth_two :
    foliance_full_tree_nodes 2 2 = 7.
  Proof. reflexivity. Qed.

  Example foliance_search_foliance_ambiguous_a_solver :
    foliance_search_regex_foliance
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      2 =
    Some [true; true].
  Proof. reflexivity. Qed.

  Example foliance_decide_foliance_ambiguous_a_solver :
    foliance_decide_regex_msss_foliance
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      2 = true.
  Proof. reflexivity. Qed.

  Example foliance_search_foliance_pref_independent_reject_solver :
    foliance_search_regex_foliance_pref
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      foliance_reject_false
      2 =
    Some [true].
  Proof. reflexivity. Qed.

  Example foliance_search_foliance_pref_independent_reject_dfs_solver :
    foliance_search_regex_foliance_pref_dfs
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      foliance_reject_false
      2 =
    Some [true].
  Proof. reflexivity. Qed.

  Example foliance_msss_gamma_leaf_bridge_smoke :
    foliance_msss_leaf
      (foliance_msss_machine [true; false] Bool.eqb foliance_ambiguous_a)
      [true] =
    rlg_prefix_leaf_prime_count
      (foliance_gamma_grammar [true; false] Bool.eqb foliance_ambiguous_a)
      (fenfa_state_eqb
         (foliance_msss_machine [true; false] Bool.eqb foliance_ambiguous_a))
      foliance_bool_list_eqb
      (enfa_trace_bound
         (foliance_msss_machine [true; false] Bool.eqb foliance_ambiguous_a)
         [true])
      [true].
  Proof.
    apply foliance_msss_gamma_leaf_bridge.
    - apply foliance_bool_foliance_ambiguous_a_closed.
    - apply foliance_bool_alphabet_nodup.
    - apply foliance_bool_list_eqb_reflects_eq.
  Qed.

  Example foliance_msss_lr_projected_leaf_bridge_smoke :
    lr1_projected_leaf_count
      Bool.bool_dec
      (foliance_msss_machine [true; false] Bool.eqb foliance_ambiguous_a)
      [true] =
    foliance_msss_leaf
      (foliance_msss_machine [true; false] Bool.eqb foliance_ambiguous_a)
      [true].
  Proof.
    apply foliance_lr_projected_leaf_bridge.
  Qed.
End FolianceDecisionExamples.
