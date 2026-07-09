From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Ambiguity Require Import
  DegreeofAmbiguity DegreeofInfiniteAmbiguity.
From PositionAutomata.Automata Require Import EpsilonNFA.
From PositionAutomata.Regex Require Import
  RegexSSS ReachAmbiguityFoliance.
From PositionAutomata.Grammar Require Import RightLinearGrammar.
From PositionAutomata.Section4 Require Import Section4LR.

(** Paper-facing executable layer for Algorithm 2.

    The paper presents Algorithm 2 as a deterministic exponential-time search
    for k-foliance strings.  This file packages the existing executable solver
    from [ReachAmbiguityFoliance] as that evaluation layer and proves the
    witness-producing and Boolean decision interfaces correct. *)

Section Algorithm2Foliance.
  Context {A : Type}.

  Definition algorithm2_witness
      (m : @finite_nfa A)
      (k : nat)
      (w : list A) : Prop :=
    word_over (fnfa_alphabet m) w /\ k_foliance m k w.

  Definition algorithm2_has_foliance
      (m : @finite_nfa A)
      (k : nat) : Prop :=
    exists w, algorithm2_witness m k w.

  Definition algorithm2_solve_foliance
      (m : @finite_nfa A)
      (k : nat) : option (list A) :=
    solve_foliance m k.

  Definition algorithm2_decide_foliance
      (m : @finite_nfa A)
      (k : nat) : bool :=
    match algorithm2_solve_foliance m k with
    | Some _ => true
    | None => false
    end.

  Definition algorithm2_solve_regex_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : option (list A) :=
    solve_regex_foliance alphabet label_matches r k.

  Definition algorithm2_decide_regex_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : bool :=
    match algorithm2_solve_regex_foliance alphabet label_matches r k with
    | Some _ => true
    | None => false
    end.

  Definition algorithm2_regex_has_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : Prop :=
    algorithm2_has_foliance
      (regex_foliance_nfa alphabet label_matches r)
      k.

  Theorem algorithm2_solve_foliance_sound :
    forall (m : @finite_nfa A) k w,
      algorithm2_solve_foliance m k = Some w ->
      algorithm2_witness m k w.
  Proof.
    intros m k w Hsolve.
    unfold algorithm2_solve_foliance in Hsolve.
    apply solve_foliance_sound in Hsolve as [Hin Hfoliance].
    apply candidate_words_sound in Hin as [_ Hover].
    split; assumption.
  Qed.

  Theorem algorithm2_solve_foliance_complete :
    forall (m : @finite_nfa A) k,
      algorithm2_has_foliance m k ->
      exists w,
        algorithm2_solve_foliance m k = Some w /\
        algorithm2_witness m k w.
  Proof.
    intros m k [w [Hover Hfoliance]].
    assert (Hlen : length w <= k).
    { exact (proj1 Hfoliance). }
    assert (Hin : In w (candidate_words m k)).
    {
      apply candidate_words_complete; assumption.
    }
    unfold algorithm2_solve_foliance.
    destruct
      (solve_foliance_complete_over_candidates
         m k (ex_intro _ w (conj Hin Hfoliance)))
      as [w' [Hsolve [Hin' Hfoliance']]].
    exists w'. split.
    - exact Hsolve.
    - apply candidate_words_sound in Hin' as [_ Hover'].
      split; assumption.
  Qed.

  Theorem algorithm2_solve_foliance_some_iff :
    forall (m : @finite_nfa A) k,
      (exists w, algorithm2_solve_foliance m k = Some w) <->
      algorithm2_has_foliance m k.
  Proof.
    intros m k. split.
    - intros [w Hsolve].
      exists w. now apply algorithm2_solve_foliance_sound in Hsolve.
    - intros Hhas.
      destruct (algorithm2_solve_foliance_complete m k Hhas)
        as [w [Hsolve _]].
      exists w. exact Hsolve.
  Qed.

  Theorem algorithm2_decide_foliance_correct :
    forall (m : @finite_nfa A) k,
      algorithm2_decide_foliance m k = true <->
      algorithm2_has_foliance m k.
  Proof.
    intros m k.
    unfold algorithm2_decide_foliance.
    destruct (algorithm2_solve_foliance m k) as [w |] eqn:Hsolve.
    - split; intros _.
      + exists w. now apply algorithm2_solve_foliance_sound.
      + reflexivity.
    - split; intros H.
      + discriminate.
      + destruct (algorithm2_solve_foliance_complete m k H)
          as [w [Hsolve' _]].
        rewrite Hsolve in Hsolve'. discriminate.
  Qed.

  Theorem algorithm2_solve_regex_foliance_sound :
    forall alphabet label_matches (r : regex A) k w,
      algorithm2_solve_regex_foliance alphabet label_matches r k = Some w ->
      algorithm2_witness
        (regex_foliance_nfa alphabet label_matches r)
        k
        w.
  Proof.
    intros alphabet label_matches r k w Hsolve.
    unfold algorithm2_solve_regex_foliance, solve_regex_foliance in Hsolve.
    change
      (algorithm2_solve_foliance
         (regex_foliance_nfa alphabet label_matches r) k = Some w)
      in Hsolve.
    now apply algorithm2_solve_foliance_sound in Hsolve.
  Qed.

  Theorem algorithm2_solve_regex_foliance_complete :
    forall alphabet label_matches (r : regex A) k,
      algorithm2_regex_has_foliance alphabet label_matches r k ->
      exists w,
        algorithm2_solve_regex_foliance alphabet label_matches r k = Some w /\
        algorithm2_witness
          (regex_foliance_nfa alphabet label_matches r)
          k
          w.
  Proof.
    intros alphabet label_matches r k Hhas.
    unfold algorithm2_regex_has_foliance in Hhas.
    destruct
      (algorithm2_solve_foliance_complete
         (regex_foliance_nfa alphabet label_matches r) k Hhas)
      as [w [Hsolve Hw]].
    exists w. split.
    - unfold algorithm2_solve_regex_foliance, solve_regex_foliance.
      exact Hsolve.
    - exact Hw.
  Qed.

  Theorem algorithm2_solve_regex_foliance_some_iff :
    forall alphabet label_matches (r : regex A) k,
      (exists w,
        algorithm2_solve_regex_foliance alphabet label_matches r k = Some w) <->
      algorithm2_regex_has_foliance alphabet label_matches r k.
  Proof.
    intros alphabet label_matches r k. split.
    - intros [w Hsolve].
      exists w. now apply algorithm2_solve_regex_foliance_sound in Hsolve.
    - intros Hhas.
      destruct
        (algorithm2_solve_regex_foliance_complete
           alphabet label_matches r k Hhas)
        as [w [Hsolve _]].
      exists w. exact Hsolve.
  Qed.

  Theorem algorithm2_decide_regex_foliance_correct :
    forall alphabet label_matches (r : regex A) k,
      algorithm2_decide_regex_foliance alphabet label_matches r k = true <->
      algorithm2_regex_has_foliance alphabet label_matches r k.
  Proof.
    intros alphabet label_matches r k.
    unfold algorithm2_decide_regex_foliance.
    destruct
      (algorithm2_solve_regex_foliance alphabet label_matches r k)
      as [w |] eqn:Hsolve.
    - split; intros _.
      + exists w. now eapply algorithm2_solve_regex_foliance_sound.
      + reflexivity.
    - split; intros H.
      + discriminate.
      + destruct
          (algorithm2_solve_regex_foliance_complete
             alphabet label_matches r k H)
          as [w [Hsolve' _]].
        rewrite Hsolve in Hsolve'. discriminate.
  Qed.
End Algorithm2Foliance.

Section Algorithm2PaperLayer.
  Context {A : Type}.

  Fixpoint algorithm2_sigma_regex (alphabet : list A) : regex A :=
    match alphabet with
    | [] => Empty
    | [a] => Atom a
    | a :: alphabet' => Alt (Atom a) (algorithm2_sigma_regex alphabet')
    end.

  Definition algorithm2_sigma_star_regex (alphabet : list A) : regex A :=
    Star (algorithm2_sigma_regex alphabet).

  Definition algorithm2_pref_regex
      (alphabet : list A) (r : regex A) : regex A :=
    Cat (algorithm2_sigma_star_regex alphabet) r.

  Definition algorithm2_msss_machine
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : @finite_enfa A :=
    regex_Msss alphabet label_matches r.

  Definition algorithm2_msss_start
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      : enfa_state
          (fenfa_base
             (algorithm2_msss_machine alphabet label_matches r)) :=
    sss_start (sss_compile r).

  Definition algorithm2_gamma_grammar
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      : right_linear_grammar :=
    gamma_grammar_from
      (algorithm2_msss_machine alphabet label_matches r)
      (algorithm2_msss_start alphabet label_matches r).

  Definition algorithm2_lr_machine
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      : lr1_machine
          (enfa_state
             (fenfa_base
                (algorithm2_msss_machine alphabet label_matches r))) :=
    lr1_machine_of_enfa
      A_eq_dec
      (algorithm2_msss_machine alphabet label_matches r).

  Definition algorithm2_msss_leaf
      (m : @finite_enfa A) (w : list A) : nat :=
    enfa_leaf_prime_word m w.

  Definition algorithm2_msss_rejected
      (m : @finite_enfa A) (w : list A) : Prop :=
    enfa_da_prime_word m w = 0.

  Definition algorithm2_msss_rejectedb
      (m : @finite_enfa A) (w : list A) : bool :=
    Nat.eqb (enfa_da_prime_word m w) 0.

  Definition algorithm2_msss_leaf_prefix_max
      (m : @finite_enfa A) (w : list A) : nat :=
    max_nats (map (algorithm2_msss_leaf m) (prefixes w)).

  Definition algorithm2_msss_prefix_rejected
      (m : @finite_enfa A) (w : list A) : Prop :=
    forall u, In u (prefixes w) -> algorithm2_msss_rejected m u.

  Definition algorithm2_msss_prefix_rejectedb
      (m : @finite_enfa A) (w : list A) : bool :=
    forallb (algorithm2_msss_rejectedb m) (prefixes w).

  Definition algorithm2_msss_foliance_against
      (count_m reject_m : @finite_enfa A)
      (k : nat)
      (w : list A) : Prop :=
    length w <= k /\
    word_over (fenfa_alphabet count_m) w /\
    algorithm2_msss_rejected reject_m w /\
    k <= algorithm2_msss_leaf_prefix_max count_m w.

  Definition algorithm2_msss_foliance
      (m : @finite_enfa A) (k : nat) (w : list A) : Prop :=
    algorithm2_msss_foliance_against m m k w.

  Definition algorithm2_msss_foliance_pref_against
      (count_m reject_m : @finite_enfa A)
      (k : nat)
      (w : list A) : Prop :=
    length w <= k /\
    word_over (fenfa_alphabet count_m) w /\
    algorithm2_msss_prefix_rejected reject_m w /\
    k <= algorithm2_msss_leaf_prefix_max count_m w.

  Definition algorithm2_msss_foliance_againstb
      (count_m reject_m : @finite_enfa A)
      (k : nat)
      (w : list A) : bool :=
    (length w <=? k)
    && algorithm2_msss_rejectedb reject_m w
    && (k <=? algorithm2_msss_leaf_prefix_max count_m w).

  Definition algorithm2_msss_folianceb
      (m : @finite_enfa A) (k : nat) (w : list A) : bool :=
    algorithm2_msss_foliance_againstb m m k w.

  Definition algorithm2_msss_foliance_pref_againstb
      (count_m reject_m : @finite_enfa A)
      (k : nat)
      (w : list A) : bool :=
    (length w <=? k)
    && algorithm2_msss_prefix_rejectedb reject_m w
    && (k <=? algorithm2_msss_leaf_prefix_max count_m w).

  Definition algorithm2_msss_has_foliance_against
      (count_m reject_m : @finite_enfa A) (k : nat) : Prop :=
    exists w, algorithm2_msss_foliance_against count_m reject_m k w.

  Definition algorithm2_msss_has_foliance
      (m : @finite_enfa A) (k : nat) : Prop :=
    algorithm2_msss_has_foliance_against m m k.

  Definition algorithm2_msss_has_foliance_pref_against
      (count_m reject_m : @finite_enfa A) (k : nat) : Prop :=
    exists w, algorithm2_msss_foliance_pref_against count_m reject_m k w.

  Lemma algorithm2_msss_rejectedb_correct :
    forall (m : @finite_enfa A) w,
      algorithm2_msss_rejectedb m w = true <->
      algorithm2_msss_rejected m w.
  Proof.
    intros m w.
    unfold algorithm2_msss_rejectedb, algorithm2_msss_rejected.
    apply Nat.eqb_eq.
  Qed.

  Lemma algorithm2_msss_prefix_rejectedb_correct :
    forall (m : @finite_enfa A) w,
      algorithm2_msss_prefix_rejectedb m w = true <->
      algorithm2_msss_prefix_rejected m w.
  Proof.
    intros m w.
    unfold algorithm2_msss_prefix_rejectedb,
      algorithm2_msss_prefix_rejected.
    split; intros H.
    - intros u Hu.
      apply algorithm2_msss_rejectedb_correct.
      rewrite forallb_forall in H.
      now apply H.
    - apply forallb_forall.
      intros u Hu.
      apply algorithm2_msss_rejectedb_correct.
      now apply H.
  Qed.

  Lemma algorithm2_msss_foliance_againstb_correct :
    forall (count_m reject_m : @finite_enfa A) k w,
      word_over (fenfa_alphabet count_m) w ->
      algorithm2_msss_foliance_againstb count_m reject_m k w = true <->
      algorithm2_msss_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w Hover.
    unfold algorithm2_msss_foliance_againstb,
      algorithm2_msss_foliance_against.
    split; intros H.
    - apply andb_true_iff in H as [Hleft Hleaf].
      apply andb_true_iff in Hleft as [Hlen Hreject].
      apply Nat.leb_le in Hlen.
      apply algorithm2_msss_rejectedb_correct in Hreject.
      apply Nat.leb_le in Hleaf.
      repeat split; assumption.
    - destruct H as [Hlen [_ [Hreject Hleaf]]].
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * now apply Nat.leb_le.
        * now apply algorithm2_msss_rejectedb_correct.
      + now apply Nat.leb_le.
  Qed.

  Lemma algorithm2_msss_foliance_pref_againstb_correct :
    forall (count_m reject_m : @finite_enfa A) k w,
      word_over (fenfa_alphabet count_m) w ->
      algorithm2_msss_foliance_pref_againstb count_m reject_m k w = true <->
      algorithm2_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w Hover.
    unfold algorithm2_msss_foliance_pref_againstb,
      algorithm2_msss_foliance_pref_against.
    split; intros H.
    - apply andb_true_iff in H as [Hleft Hleaf].
      apply andb_true_iff in Hleft as [Hlen Hreject].
      apply Nat.leb_le in Hlen.
      apply algorithm2_msss_prefix_rejectedb_correct in Hreject.
      apply Nat.leb_le in Hleaf.
      repeat split; assumption.
    - destruct H as [Hlen [_ [Hreject Hleaf]]].
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * now apply Nat.leb_le.
        * now apply algorithm2_msss_prefix_rejectedb_correct.
      + now apply Nat.leb_le.
  Qed.

  Definition algorithm2_reach_set
      (m : @finite_enfa A)
      (w : list A) : list (enfa_state (fenfa_base m)) :=
    filter
      (fun q => 0 <? enfa_dra_prime_at m w q)
      (fenfa_states m).

  Definition algorithm2_delta_hat_prime
      (m : @finite_enfa A)
      (w : list A)
      (a : A) : list (enfa_state (fenfa_base m)) :=
    algorithm2_reach_set m (w ++ [a]).

  Fixpoint algorithm2_search_space
      (alphabet : list A)
      (fuel : nat)
      (w : list A) : list (list A) :=
    w ::
    match fuel with
    | O => []
    | S fuel' =>
        concat
          (map
             (fun a => algorithm2_search_space alphabet fuel' (w ++ [a]))
             alphabet)
    end.

  Definition algorithm2_search_children_space
      (alphabet : list A)
      (fuel : nat)
      (w : list A) : list (list A) :=
    match fuel with
    | O => []
    | S fuel' =>
        concat
          (map
             (fun a => algorithm2_search_space alphabet fuel' (w ++ [a]))
             alphabet)
    end.

  Definition algorithm2_search
      (count_m reject_m : @finite_enfa A)
      (k fuel : nat)
      (_X : list (enfa_state (fenfa_base count_m)))
      (w : list A)
      (_leaf_max : nat) : option (list A) :=
    find
      (algorithm2_msss_foliance_againstb count_m reject_m k)
      (algorithm2_search_space (fenfa_alphabet count_m) fuel w).

  Definition algorithm2_search_children
      (count_m reject_m : @finite_enfa A)
      (k fuel : nat)
      (alphabet : list A)
      (w : list A)
      (_leaf_max : nat) : option (list A) :=
    find
      (algorithm2_msss_foliance_againstb count_m reject_m k)
      (algorithm2_search_children_space alphabet fuel w).

  Definition algorithm2_search_pref
      (count_m reject_m : @finite_enfa A)
      (k fuel : nat)
      (_X : list (enfa_state (fenfa_base count_m)))
      (w : list A)
      (_leaf_max : nat) : option (list A) :=
    find
      (algorithm2_msss_foliance_pref_againstb count_m reject_m k)
      (algorithm2_search_space (fenfa_alphabet count_m) fuel w).

  Fixpoint algorithm2_first_some {B : Type} (xs : list (option B))
      : option B :=
    match xs with
    | [] => None
    | Some x :: _ => Some x
    | None :: xs' => algorithm2_first_some xs'
    end.

  Fixpoint algorithm2_search_pref_dfs
      (count_m reject_m : @finite_enfa A)
      (k fuel : nat)
      (_X : list (enfa_state (fenfa_base reject_m)))
      (w : list A)
      (_leaf : nat)
      (leaf_sup : nat) {struct fuel} : option (list A) :=
    if algorithm2_msss_rejectedb reject_m w then
      if k <=? leaf_sup then Some w
      else
        match fuel with
        | O => None
        | S fuel' =>
            algorithm2_first_some
              (map
                 (fun a =>
                    let wa := w ++ [a] in
                    let Y := algorithm2_reach_set reject_m wa in
                    let leaf' := algorithm2_msss_leaf count_m wa in
                    let leaf_sup' := Nat.max leaf_sup leaf' in
                    if algorithm2_msss_rejectedb reject_m wa then
                      algorithm2_search_pref_dfs
                        count_m reject_m k fuel' Y wa leaf' leaf_sup'
                    else None)
                 (fenfa_alphabet count_m))
        end
    else None.

  Definition algorithm2_search_msss_foliance_against
      (count_m reject_m : @finite_enfa A)
      (k : nat) : option (list A) :=
    algorithm2_search
      count_m reject_m k k
      (algorithm2_reach_set count_m [])
      []
      (algorithm2_msss_leaf count_m []).

  Definition algorithm2_search_msss_foliance
      (m : @finite_enfa A) (k : nat) : option (list A) :=
    algorithm2_search_msss_foliance_against m m k.

  Definition algorithm2_search_msss_foliance_pref_against
      (count_m reject_m : @finite_enfa A)
      (k : nat) : option (list A) :=
    algorithm2_search_pref
      count_m reject_m k k
      (algorithm2_reach_set count_m [])
      []
      (algorithm2_msss_leaf count_m []).

  Definition algorithm2_search_msss_foliance_pref_against_dfs
      (count_m reject_m : @finite_enfa A)
      (k : nat) : option (list A) :=
    algorithm2_search_pref_dfs
      count_m reject_m k k
      (algorithm2_reach_set reject_m [])
      []
      (algorithm2_msss_leaf count_m [])
      (algorithm2_msss_leaf count_m []).

  Definition algorithm2_decide_msss_foliance_against
      (count_m reject_m : @finite_enfa A)
      (k : nat) : bool :=
    match algorithm2_search_msss_foliance_against count_m reject_m k with
    | Some _ => true
    | None => false
    end.

  Definition algorithm2_decide_msss_foliance
      (m : @finite_enfa A) (k : nat) : bool :=
    algorithm2_decide_msss_foliance_against m m k.

  Definition algorithm2_decide_msss_foliance_pref_against
      (count_m reject_m : @finite_enfa A)
      (k : nat) : bool :=
    match algorithm2_search_msss_foliance_pref_against count_m reject_m k with
    | Some _ => true
    | None => false
    end.

  Definition algorithm2_decide_msss_foliance_pref_against_dfs
      (count_m reject_m : @finite_enfa A)
      (k : nat) : bool :=
    match algorithm2_search_msss_foliance_pref_against_dfs count_m reject_m k with
    | Some _ => true
    | None => false
    end.

  Definition algorithm2_search_regex_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : option (list A) :=
    algorithm2_search_msss_foliance
      (algorithm2_msss_machine alphabet label_matches r)
      k.

  Definition algorithm2_decide_regex_msss_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : bool :=
    algorithm2_decide_msss_foliance
      (algorithm2_msss_machine alphabet label_matches r)
      k.

  Definition algorithm2_search_regex_foliance_pref
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (count_r reject_r : regex A)
      (k : nat) : option (list A) :=
    algorithm2_search_msss_foliance_pref_against
      (algorithm2_msss_machine alphabet label_matches count_r)
      (algorithm2_msss_machine
         alphabet label_matches (algorithm2_pref_regex alphabet reject_r))
      k.

  Definition algorithm2_search_regex_foliance_pref_dfs
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (count_r reject_r : regex A)
      (k : nat) : option (list A) :=
    algorithm2_search_msss_foliance_pref_against_dfs
      (algorithm2_msss_machine alphabet label_matches count_r)
      (algorithm2_msss_machine
         alphabet label_matches (algorithm2_pref_regex alphabet reject_r))
      k.

  Definition algorithm2_decide_regex_msss_foliance_pref_dfs
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (count_r reject_r : regex A)
      (k : nat) : bool :=
    algorithm2_decide_msss_foliance_pref_against_dfs
      (algorithm2_msss_machine alphabet label_matches count_r)
      (algorithm2_msss_machine
         alphabet label_matches (algorithm2_pref_regex alphabet reject_r))
      k.

  Lemma algorithm2_word_over_app :
    forall alphabet (u v : list A),
      word_over alphabet u ->
      word_over alphabet v ->
      word_over alphabet (u ++ v).
  Proof.
    intros alphabet u v Hu Hv.
    unfold word_over in *.
    now apply Forall_app.
  Qed.

  Lemma algorithm2_word_over_snoc :
    forall alphabet (w : list A) a,
      word_over alphabet w ->
      In a alphabet ->
      word_over alphabet (w ++ [a]).
  Proof.
    intros alphabet w a Hw Ha.
    apply algorithm2_word_over_app; auto.
    constructor; auto.
  Qed.

  Lemma algorithm2_first_some_sound :
    forall (B : Type) (xs : list (option B)) x,
      algorithm2_first_some xs = Some x ->
      In (Some x) xs.
  Proof.
    intros B xs.
    induction xs as [| [y |] xs IH]; intros x H; simpl in H; try discriminate.
    - inversion H; subst. simpl. auto.
    - simpl. right. now apply IH.
  Qed.

  Lemma algorithm2_first_some_complete :
    forall (B : Type) (xs : list (option B)) x,
      In (Some x) xs ->
      exists y, algorithm2_first_some xs = Some y.
  Proof.
    intros B xs.
    induction xs as [| [y |] xs IH]; intros x Hin; simpl in Hin; try contradiction.
    - exists y. reflexivity.
    - destruct Hin as [Hhead | Hin].
      + discriminate.
      + now apply IH with (x := x).
  Qed.

  Lemma algorithm2_prefixes_snoc :
    forall (w : list A) a,
      prefixes (w ++ [a]) = prefixes w ++ [w ++ [a]].
  Proof.
    induction w as [| b w IH]; intros a; simpl.
    - reflexivity.
    - rewrite IH, map_app. reflexivity.
  Qed.

  Lemma algorithm2_max_nats_app_single :
    forall xs n,
      max_nats (xs ++ [n]) = Nat.max (max_nats xs) n.
  Proof.
    induction xs as [| x xs IH]; intros n; simpl.
    - apply Nat.max_comm.
    - rewrite IH, Nat.max_assoc. reflexivity.
  Qed.

  Lemma algorithm2_leaf_prefix_max_snoc :
    forall (count_m : @finite_enfa A) w a,
      algorithm2_msss_leaf_prefix_max count_m (w ++ [a]) =
      Nat.max
        (algorithm2_msss_leaf_prefix_max count_m w)
        (algorithm2_msss_leaf count_m (w ++ [a])).
  Proof.
    intros count_m w a.
    unfold algorithm2_msss_leaf_prefix_max.
    rewrite algorithm2_prefixes_snoc, map_app.
    simpl. apply algorithm2_max_nats_app_single.
  Qed.

  Lemma algorithm2_msss_prefix_rejected_prefix :
    forall (m : @finite_enfa A) u w,
      prefix_of u w ->
      algorithm2_msss_prefix_rejected m w ->
      algorithm2_msss_prefix_rejected m u.
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

  Lemma algorithm2_msss_prefix_rejected_snoc :
    forall (m : @finite_enfa A) w a,
      algorithm2_msss_prefix_rejected m w ->
      algorithm2_msss_rejected m (w ++ [a]) ->
      algorithm2_msss_prefix_rejected m (w ++ [a]).
  Proof.
    intros m w a Hprefix Hlast u Hu.
    rewrite algorithm2_prefixes_snoc in Hu.
    apply in_app_or in Hu as [Hu | Hu].
    - now apply Hprefix.
    - destruct Hu as [Hu | []]. now subst u.
  Qed.

  Lemma algorithm2_msss_prefix_rejected_nil :
    forall (m : @finite_enfa A),
      algorithm2_msss_rejected m [] ->
      algorithm2_msss_prefix_rejected m [].
  Proof.
    intros m Hreject u Hu.
    simpl in Hu. destruct Hu as [Hu | []].
    now subst u.
  Qed.

  Lemma algorithm2_search_space_sound :
    forall alphabet fuel w v,
      In v (algorithm2_search_space alphabet fuel w) ->
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

  Lemma algorithm2_search_space_complete :
    forall alphabet fuel w suffix,
      length suffix <= fuel ->
      word_over alphabet suffix ->
      In (w ++ suffix) (algorithm2_search_space alphabet fuel w).
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
        exists (algorithm2_search_space alphabet fuel (w ++ [a])).
        split.
        * apply in_map_iff. exists a. split; auto.
        * replace (w ++ a :: suffix) with ((w ++ [a]) ++ suffix)
            by (rewrite <- app_assoc; reflexivity).
          apply IH.
          -- simpl in Hlen. lia.
          -- exact Hover'.
  Qed.

  Theorem algorithm2_search_sound :
    forall (count_m reject_m : @finite_enfa A) k fuel X w leaf_max v,
      word_over (fenfa_alphabet count_m) w ->
      algorithm2_search count_m reject_m k fuel X w leaf_max = Some v ->
      algorithm2_msss_foliance_against count_m reject_m k v.
  Proof.
    intros count_m reject_m k fuel X w leaf_max v Hover_w Hsearch.
    unfold algorithm2_search in Hsearch.
    apply find_sound in Hsearch as [Hin Hpred].
    destruct
      (algorithm2_search_space_sound
         (fenfa_alphabet count_m) fuel w v Hin)
      as [suffix [Hv [_ Hover_suffix]]].
    assert (Hover_v : word_over (fenfa_alphabet count_m) v).
    {
      subst v.
      now apply algorithm2_word_over_app.
    }
    now apply algorithm2_msss_foliance_againstb_correct.
  Qed.

  Theorem algorithm2_search_pref_sound :
    forall (count_m reject_m : @finite_enfa A) k fuel X w leaf_max v,
      word_over (fenfa_alphabet count_m) w ->
      algorithm2_search_pref count_m reject_m k fuel X w leaf_max = Some v ->
      algorithm2_msss_foliance_pref_against count_m reject_m k v.
  Proof.
    intros count_m reject_m k fuel X w leaf_max v Hover_w Hsearch.
    unfold algorithm2_search_pref in Hsearch.
    apply find_sound in Hsearch as [Hin Hpred].
    destruct
      (algorithm2_search_space_sound
         (fenfa_alphabet count_m) fuel w v Hin)
      as [suffix [Hv [_ Hover_suffix]]].
    assert (Hover_v : word_over (fenfa_alphabet count_m) v).
    {
      subst v.
      now apply algorithm2_word_over_app.
    }
    now apply algorithm2_msss_foliance_pref_againstb_correct.
  Qed.

  Theorem algorithm2_search_msss_foliance_against_sound :
    forall (count_m reject_m : @finite_enfa A) k w,
      algorithm2_search_msss_foliance_against count_m reject_m k = Some w ->
      algorithm2_msss_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w H.
    unfold algorithm2_search_msss_foliance_against in H.
    eapply algorithm2_search_sound; eauto.
    constructor.
  Qed.

  Theorem algorithm2_search_msss_foliance_pref_against_sound :
    forall (count_m reject_m : @finite_enfa A) k w,
      algorithm2_search_msss_foliance_pref_against count_m reject_m k = Some w ->
      algorithm2_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w H.
    unfold algorithm2_search_msss_foliance_pref_against in H.
    eapply algorithm2_search_pref_sound; eauto.
    constructor.
  Qed.

  Theorem algorithm2_search_msss_foliance_against_complete :
    forall (count_m reject_m : @finite_enfa A) k,
      algorithm2_msss_has_foliance_against count_m reject_m k ->
      exists w,
        algorithm2_search_msss_foliance_against count_m reject_m k = Some w /\
        algorithm2_msss_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k [w Hwit].
    destruct Hwit as [Hlen [Hover [Hreject Hleaf]]].
    unfold algorithm2_search_msss_foliance_against, algorithm2_search.
    assert (Hin :
      In w (algorithm2_search_space (fenfa_alphabet count_m) k [])).
    {
      replace w with ([] ++ w) by reflexivity.
      now apply algorithm2_search_space_complete.
    }
    assert (Hpred :
      algorithm2_msss_foliance_againstb count_m reject_m k w = true).
    {
      apply algorithm2_msss_foliance_againstb_correct; auto.
      repeat split; assumption.
    }
    destruct
      (find_complete
         (algorithm2_msss_foliance_againstb count_m reject_m k)
         (algorithm2_search_space (fenfa_alphabet count_m) k [])
         (ex_intro _ w (conj Hin Hpred)))
      as [w' [Hfind [Hin' Hpred']]].
    exists w'. split.
    - exact Hfind.
    - destruct
        (algorithm2_search_space_sound
           (fenfa_alphabet count_m) k [] w' Hin')
        as [suffix [Hw' [_ Hover_suffix]]].
      assert (Hover_w' : word_over (fenfa_alphabet count_m) w').
      {
        subst w'. simpl.
        exact Hover_suffix.
      }
      now apply algorithm2_msss_foliance_againstb_correct.
  Qed.

  Theorem algorithm2_search_msss_foliance_pref_against_complete :
    forall (count_m reject_m : @finite_enfa A) k,
      algorithm2_msss_has_foliance_pref_against count_m reject_m k ->
      exists w,
        algorithm2_search_msss_foliance_pref_against count_m reject_m k = Some w /\
        algorithm2_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k [w Hwit].
    destruct Hwit as [Hlen [Hover [Hreject Hleaf]]].
    unfold algorithm2_search_msss_foliance_pref_against, algorithm2_search_pref.
    assert (Hin :
      In w (algorithm2_search_space (fenfa_alphabet count_m) k [])).
    {
      replace w with ([] ++ w) by reflexivity.
      now apply algorithm2_search_space_complete.
    }
    assert (Hpred :
      algorithm2_msss_foliance_pref_againstb count_m reject_m k w = true).
    {
      apply algorithm2_msss_foliance_pref_againstb_correct; auto.
      repeat split; assumption.
    }
    destruct
      (find_complete
         (algorithm2_msss_foliance_pref_againstb count_m reject_m k)
         (algorithm2_search_space (fenfa_alphabet count_m) k [])
         (ex_intro _ w (conj Hin Hpred)))
      as [w' [Hfind [Hin' Hpred']]].
    exists w'. split.
    - exact Hfind.
    - destruct
        (algorithm2_search_space_sound
           (fenfa_alphabet count_m) k [] w' Hin')
        as [suffix [Hw' [_ Hover_suffix]]].
      assert (Hover_w' : word_over (fenfa_alphabet count_m) w').
      {
        subst w'. simpl.
        exact Hover_suffix.
      }
      now apply algorithm2_msss_foliance_pref_againstb_correct.
  Qed.

  Theorem algorithm2_search_pref_dfs_sound :
    forall (count_m reject_m : @finite_enfa A) k fuel X w leaf leaf_sup v,
      word_over (fenfa_alphabet count_m) w ->
      length w + fuel <= k ->
      algorithm2_msss_prefix_rejected reject_m w ->
      leaf_sup = algorithm2_msss_leaf_prefix_max count_m w ->
      algorithm2_search_pref_dfs
        count_m reject_m k fuel X w leaf leaf_sup = Some v ->
      algorithm2_msss_foliance_pref_against count_m reject_m k v.
  Proof.
    intros count_m reject_m k fuel.
    induction fuel as [| fuel IH];
      intros X w leaf leaf_sup v Hover Hlen Hprefix Hleafsup Hsearch;
      simpl in Hsearch.
    - destruct (algorithm2_msss_rejectedb reject_m w) eqn:Hreject;
        try discriminate.
      destruct (k <=? leaf_sup) eqn:Hleaf; inversion Hsearch; subst v.
      apply Nat.leb_le in Hleaf.
      repeat split; auto; try lia.
    - destruct (algorithm2_msss_rejectedb reject_m w) eqn:Hreject;
        try discriminate.
      destruct (k <=? leaf_sup) eqn:Hleaf.
      + inversion Hsearch; subst v.
        apply Nat.leb_le in Hleaf.
        repeat split; auto; try lia.
      + apply algorithm2_first_some_sound in Hsearch as Hin.
        apply in_map_iff in Hin as [a [Hchild Ha]].
        destruct
          (algorithm2_msss_rejectedb reject_m (w ++ [a]))
          eqn:Hchild_reject; try discriminate.
        eapply
          (IH
             (algorithm2_reach_set reject_m (w ++ [a]))
             (w ++ [a])
             (algorithm2_msss_leaf count_m (w ++ [a]))
             (Nat.max leaf_sup
                (algorithm2_msss_leaf count_m (w ++ [a])))).
        * eapply algorithm2_word_over_snoc; eauto.
        * rewrite length_app. simpl. lia.
        * apply algorithm2_msss_prefix_rejected_snoc; auto.
          now apply algorithm2_msss_rejectedb_correct.
        * rewrite Hleafsup. symmetry.
          apply algorithm2_leaf_prefix_max_snoc.
        * exact Hchild.
  Qed.

  Theorem algorithm2_search_msss_foliance_pref_against_dfs_sound :
    forall (count_m reject_m : @finite_enfa A) k w,
      algorithm2_search_msss_foliance_pref_against_dfs count_m reject_m k =
        Some w ->
      algorithm2_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w Hsearch.
    unfold algorithm2_search_msss_foliance_pref_against_dfs in Hsearch.
    destruct (algorithm2_msss_rejectedb reject_m []) eqn:Hreject.
    - apply
        (algorithm2_search_pref_dfs_sound
           count_m reject_m k k
           (algorithm2_reach_set reject_m [])
           []
           (algorithm2_msss_leaf count_m [])
           (algorithm2_msss_leaf count_m [])
           w).
      + constructor.
      + simpl. lia.
      + apply algorithm2_msss_prefix_rejected_nil.
        now apply algorithm2_msss_rejectedb_correct.
      + unfold algorithm2_msss_leaf_prefix_max.
        simpl. now rewrite Nat.max_0_r.
      + exact Hsearch.
    - destruct k as [| k']; simpl in Hsearch;
        rewrite Hreject in Hsearch; discriminate.
  Qed.

  Theorem algorithm2_search_pref_dfs_complete :
    forall (count_m reject_m : @finite_enfa A) k fuel X w leaf leaf_sup suffix,
      word_over (fenfa_alphabet count_m) w ->
      length w + fuel <= k ->
      algorithm2_msss_prefix_rejected reject_m w ->
      leaf_sup = algorithm2_msss_leaf_prefix_max count_m w ->
      length suffix <= fuel ->
      word_over (fenfa_alphabet count_m) suffix ->
      algorithm2_msss_foliance_pref_against
        count_m reject_m k (w ++ suffix) ->
      exists v,
        algorithm2_search_pref_dfs
          count_m reject_m k fuel X w leaf leaf_sup = Some v /\
        algorithm2_msss_foliance_pref_against count_m reject_m k v.
  Proof.
    intros count_m reject_m k fuel.
    induction fuel as [| fuel IH];
      intros X w leaf leaf_sup suffix Hover Hlen Hprefix Hleafsup
        Hsuffix_len Hsuffix_over Hwit.
    - assert (Hreject_w : algorithm2_msss_rejected reject_m w).
      { apply Hprefix. apply prefixes_refl. }
      assert (Hrejectb_w :
        algorithm2_msss_rejectedb reject_m w = true).
      { now apply algorithm2_msss_rejectedb_correct. }
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
    - assert (Hreject_w : algorithm2_msss_rejected reject_m w).
      { apply Hprefix. apply prefixes_refl. }
      assert (Hrejectb_w :
        algorithm2_msss_rejectedb reject_m w = true).
      { now apply algorithm2_msss_rejectedb_correct. }
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
            algorithm2_msss_prefix_rejected reject_m (w ++ [a])).
          {
            eapply algorithm2_msss_prefix_rejected_prefix.
            - exists suffix. rewrite <- app_assoc. reflexivity.
            - exact (proj1 (proj2 (proj2 Hwit))).
          }
          assert (Hchild_reject :
            algorithm2_msss_rejectedb reject_m (w ++ [a]) = true).
          {
            apply algorithm2_msss_rejectedb_correct.
            apply Hchild_prefix. apply prefixes_refl.
          }
          assert (Hchild_leafsup :
            Nat.max leaf_sup (algorithm2_msss_leaf count_m (w ++ [a])) =
            algorithm2_msss_leaf_prefix_max count_m (w ++ [a])).
          {
            rewrite Hleafsup. symmetry.
            apply algorithm2_leaf_prefix_max_snoc.
          }
          assert (Hchild_len :
            length (w ++ [a]) + fuel <= k).
          { rewrite length_app. simpl. lia. }
          assert (Hchild_wit :
            algorithm2_msss_foliance_pref_against
              count_m reject_m k ((w ++ [a]) ++ suffix)).
          {
            replace ((w ++ [a]) ++ suffix) with (w ++ a :: suffix)
              by (rewrite <- app_assoc; reflexivity).
            exact Hwit.
          }
          destruct
            (IH
               (algorithm2_reach_set reject_m (w ++ [a]))
               (w ++ [a])
               (algorithm2_msss_leaf count_m (w ++ [a]))
               (Nat.max leaf_sup
                  (algorithm2_msss_leaf count_m (w ++ [a])))
               suffix)
            as [v [Hchild_search Hchild_result]].
          -- now apply algorithm2_word_over_snoc.
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
                       let Y := algorithm2_reach_set reject_m wa in
                       let leaf' := algorithm2_msss_leaf count_m wa in
                       let leaf_sup' := Nat.max leaf_sup leaf' in
                       if algorithm2_msss_rejectedb reject_m wa then
                         algorithm2_search_pref_dfs
                           count_m reject_m k fuel Y wa leaf' leaf_sup'
                       else None)
                    (fenfa_alphabet count_m))).
             {
               apply in_map_iff. exists a. split.
               - simpl. rewrite Hchild_reject. exact Hchild_search.
               - exact Ha.
             }
             destruct
               (algorithm2_first_some_complete
                  _ _ _ Hin_child) as [v' Hfirst].
             exists v'. split.
             ++ exact Hfirst.
             ++ apply
                  (algorithm2_search_pref_dfs_sound
                     count_m reject_m k (S fuel) X w leaf leaf_sup v');
                  auto.
                simpl. rewrite Hrejectb_w, Hleaf. exact Hfirst.
  Qed.

  Theorem algorithm2_search_msss_foliance_pref_against_dfs_complete :
    forall (count_m reject_m : @finite_enfa A) k,
      algorithm2_msss_has_foliance_pref_against count_m reject_m k ->
      exists w,
        algorithm2_search_msss_foliance_pref_against_dfs count_m reject_m k =
          Some w /\
        algorithm2_msss_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k [w Hwit].
    destruct Hwit as [Hlen [Hover [Hprefix Hleaf]]].
    assert (Hreject_nil : algorithm2_msss_rejected reject_m []).
    {
      apply Hprefix.
      apply prefixes_complete.
      exists w. reflexivity.
    }
    unfold algorithm2_search_msss_foliance_pref_against_dfs.
    eapply algorithm2_search_pref_dfs_complete with (suffix := w).
    - constructor.
    - simpl. lia.
    - apply algorithm2_msss_prefix_rejected_nil. exact Hreject_nil.
    - unfold algorithm2_msss_leaf_prefix_max.
      simpl. now rewrite Nat.max_0_r.
    - exact Hlen.
    - exact Hover.
    - simpl. repeat split; assumption.
  Qed.

  Theorem algorithm2_search_pref_dfs_some_iff :
    forall (count_m reject_m : @finite_enfa A) k,
      (exists w,
        algorithm2_search_msss_foliance_pref_against_dfs count_m reject_m k =
          Some w) <->
      algorithm2_msss_has_foliance_pref_against count_m reject_m k.
  Proof.
    intros count_m reject_m k. split.
    - intros [w H].
      exists w.
      now apply algorithm2_search_msss_foliance_pref_against_dfs_sound in H.
    - intros Hhas.
      destruct
        (algorithm2_search_msss_foliance_pref_against_dfs_complete
           count_m reject_m k Hhas)
        as [w [H _]].
      exists w. exact H.
  Qed.

  Theorem algorithm2_search_some_iff :
    forall (count_m reject_m : @finite_enfa A) k,
      (exists w,
        algorithm2_search_msss_foliance_against count_m reject_m k = Some w) <->
      algorithm2_msss_has_foliance_against count_m reject_m k.
  Proof.
    intros count_m reject_m k. split.
    - intros [w H].
      exists w.
      now apply algorithm2_search_msss_foliance_against_sound in H.
    - intros Hhas.
      destruct
        (algorithm2_search_msss_foliance_against_complete
           count_m reject_m k Hhas)
        as [w [H _]].
      exists w. exact H.
  Qed.

  Theorem algorithm2_search_pref_some_iff :
    forall (count_m reject_m : @finite_enfa A) k,
      (exists w,
        algorithm2_search_msss_foliance_pref_against count_m reject_m k = Some w) <->
      algorithm2_msss_has_foliance_pref_against count_m reject_m k.
  Proof.
    intros count_m reject_m k. split.
    - intros [w H].
      exists w.
      now apply algorithm2_search_msss_foliance_pref_against_sound in H.
    - intros Hhas.
      destruct
        (algorithm2_search_msss_foliance_pref_against_complete
           count_m reject_m k Hhas)
        as [w [H _]].
      exists w. exact H.
  Qed.

  Theorem algorithm2_decide_msss_correct :
    forall (m : @finite_enfa A) k,
      algorithm2_decide_msss_foliance m k = true <->
      algorithm2_msss_has_foliance m k.
  Proof.
    intros m k.
    unfold algorithm2_decide_msss_foliance,
      algorithm2_decide_msss_foliance_against.
    destruct (algorithm2_search_msss_foliance_against m m k) as [w |] eqn:H.
    - split; intros _.
      + exists w. now apply algorithm2_search_msss_foliance_against_sound.
      + reflexivity.
    - split; intros Hfalse.
      + discriminate.
      + destruct
          (algorithm2_search_msss_foliance_against_complete m m k Hfalse)
          as [w [Hsome _]].
        rewrite H in Hsome. discriminate.
  Qed.

  Theorem algorithm2_decide_msss_pref_correct :
    forall (count_m reject_m : @finite_enfa A) k,
      algorithm2_decide_msss_foliance_pref_against count_m reject_m k = true <->
      algorithm2_msss_has_foliance_pref_against count_m reject_m k.
  Proof.
    intros count_m reject_m k.
    unfold algorithm2_decide_msss_foliance_pref_against.
    destruct
      (algorithm2_search_msss_foliance_pref_against count_m reject_m k)
      as [w |] eqn:H.
    - split; intros _.
      + exists w. now apply algorithm2_search_msss_foliance_pref_against_sound.
      + reflexivity.
    - split; intros Hfalse.
      + discriminate.
      + destruct
          (algorithm2_search_msss_foliance_pref_against_complete
             count_m reject_m k Hfalse)
          as [w [Hsome _]].
        rewrite H in Hsome. discriminate.
  Qed.

  Theorem algorithm2_decide_msss_pref_dfs_correct :
    forall (count_m reject_m : @finite_enfa A) k,
      algorithm2_decide_msss_foliance_pref_against_dfs count_m reject_m k =
        true <->
      algorithm2_msss_has_foliance_pref_against count_m reject_m k.
  Proof.
    intros count_m reject_m k.
    unfold algorithm2_decide_msss_foliance_pref_against_dfs.
    destruct
      (algorithm2_search_msss_foliance_pref_against_dfs count_m reject_m k)
      as [w |] eqn:H.
    - split; intros _.
      + exists w. now apply algorithm2_search_msss_foliance_pref_against_dfs_sound.
      + reflexivity.
    - split; intros Hfalse.
      + discriminate.
      + destruct
          (algorithm2_search_msss_foliance_pref_against_dfs_complete
             count_m reject_m k Hfalse)
          as [w [Hsome _]].
        rewrite H in Hsome. discriminate.
  Qed.

  Theorem algorithm2_decide_regex_msss_foliance_pref_correct :
    forall alphabet label_matches (count_r reject_r : regex A) k,
      algorithm2_decide_regex_msss_foliance_pref_dfs
        alphabet label_matches count_r reject_r k = true <->
      algorithm2_msss_has_foliance_pref_against
        (algorithm2_msss_machine alphabet label_matches count_r)
        (algorithm2_msss_machine
           alphabet label_matches (algorithm2_pref_regex alphabet reject_r))
        k.
  Proof.
    intros alphabet label_matches count_r reject_r k.
    unfold algorithm2_decide_regex_msss_foliance_pref_dfs.
    apply algorithm2_decide_msss_pref_dfs_correct.
  Qed.

  Theorem algorithm2_msss_positive_da_prime_accepts :
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

  Theorem algorithm2_regex_msss_positive_da_prime_language :
    forall alphabet label_matches (r : regex A) w,
      regex_symbol_closed alphabet label_matches r ->
      0 < enfa_da_prime_word
            (algorithm2_msss_machine alphabet label_matches r) w ->
      enfa_accepts_word
        (algorithm2_msss_machine alphabet label_matches r) w.
  Proof.
    intros alphabet label_matches r w Hclosed Hpos.
    eapply algorithm2_msss_positive_da_prime_accepts.
    - now apply regex_Msss_wf.
    - exact Hpos.
  Qed.

  Theorem algorithm2_msss_gamma_leaf_bridge :
    forall alphabet label_matches (r : regex A) word_eqb w,
      regex_symbol_closed alphabet label_matches r ->
      NoDup alphabet ->
      word_eqb_reflects_eq word_eqb ->
      algorithm2_msss_leaf
        (algorithm2_msss_machine alphabet label_matches r) w =
      rlg_prefix_leaf_prime_count
        (algorithm2_gamma_grammar alphabet label_matches r)
        (fenfa_state_eqb
           (algorithm2_msss_machine alphabet label_matches r))
        word_eqb
        (enfa_trace_bound
           (algorithm2_msss_machine alphabet label_matches r) w)
        w.
  Proof.
    intros alphabet label_matches r word_eqb w Hclosed Halphabet Hwordeq.
    unfold algorithm2_msss_leaf,
      algorithm2_gamma_grammar,
      algorithm2_msss_start.
    eapply section4_lemma3_gamma_leaf_prime_count_eq_with_alphabet_nodup.
    - now apply regex_Msss_wf.
    - unfold algorithm2_msss_machine, regex_Msss. reflexivity.
    - exact Halphabet.
    - exact Hwordeq.
  Qed.

  Theorem algorithm2_lr_projected_leaf_bridge :
    forall A_eq_dec alphabet label_matches (r : regex A) w,
      lr1_projected_leaf_count
        A_eq_dec
        (algorithm2_msss_machine alphabet label_matches r)
        w =
      algorithm2_msss_leaf
        (algorithm2_msss_machine alphabet label_matches r)
        w.
  Proof.
    intros A_eq_dec alphabet label_matches r w.
    unfold algorithm2_msss_leaf.
    apply section4_lemma4_I_lr1_leaf_preservation.
  Qed.
End Algorithm2PaperLayer.

Section Algorithm2FolianceExamples.
  Fixpoint algorithm2_bool_list_eqb (xs ys : list bool) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => Bool.eqb x y && algorithm2_bool_list_eqb xs' ys'
    | _, _ => false
    end.

  Lemma algorithm2_bool_list_eqb_sound :
    forall xs ys, algorithm2_bool_list_eqb xs ys = true -> xs = ys.
  Proof.
    induction xs as [| x xs IH]; intros ys H; destruct ys as [| y ys];
      simpl in H; try discriminate; auto.
    apply andb_true_iff in H as [Hxy Htail].
    destruct x, y; simpl in Hxy; try discriminate.
    - now rewrite (IH ys Htail).
    - now rewrite (IH ys Htail).
  Qed.

  Lemma algorithm2_bool_list_eqb_complete :
    forall xs ys, xs = ys -> algorithm2_bool_list_eqb xs ys = true.
  Proof.
    induction xs as [| x xs IH]; intros ys H; subst ys; simpl; auto.
    destruct x; simpl; now apply IH.
  Qed.

  Lemma algorithm2_bool_list_eqb_reflects_eq :
    word_eqb_reflects_eq algorithm2_bool_list_eqb.
  Proof.
    split.
    - apply algorithm2_bool_list_eqb_sound.
    - apply algorithm2_bool_list_eqb_complete.
  Qed.

  Lemma algorithm2_bool_foliance_ambiguous_a_closed :
    regex_symbol_closed [true; false] Bool.eqb foliance_ambiguous_a.
  Proof.
    intros b a _ Hmatch.
    destruct b, a; simpl in Hmatch; try discriminate; simpl; auto.
  Qed.

  Lemma algorithm2_bool_alphabet_nodup :
    NoDup [true; false].
  Proof.
    constructor.
    - simpl. intros [H | []]; discriminate.
    - constructor.
      + simpl. intros [].
      + constructor.
  Qed.

  Example algorithm2_foliance_ambiguous_a_solver :
    algorithm2_solve_regex_foliance
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      2 =
    Some [true; true].
  Proof. reflexivity. Qed.

  Example algorithm2_search_foliance_ambiguous_a_solver :
    algorithm2_search_regex_foliance
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      2 =
    Some [true; true].
  Proof. reflexivity. Qed.

  Example algorithm2_decide_foliance_ambiguous_a_solver :
    algorithm2_decide_regex_msss_foliance
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      2 = true.
  Proof. reflexivity. Qed.

  Example algorithm2_search_foliance_pref_independent_reject_solver :
    algorithm2_search_regex_foliance_pref
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      foliance_reject_false
      2 =
    Some [true].
  Proof. reflexivity. Qed.

  Example algorithm2_search_foliance_pref_independent_reject_dfs_solver :
    algorithm2_search_regex_foliance_pref_dfs
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      foliance_reject_false
      2 =
    Some [true].
  Proof. reflexivity. Qed.

  Example algorithm2_msss_gamma_leaf_bridge_smoke :
    algorithm2_msss_leaf
      (algorithm2_msss_machine [true; false] Bool.eqb foliance_ambiguous_a)
      [true] =
    rlg_prefix_leaf_prime_count
      (algorithm2_gamma_grammar [true; false] Bool.eqb foliance_ambiguous_a)
      (fenfa_state_eqb
         (algorithm2_msss_machine [true; false] Bool.eqb foliance_ambiguous_a))
      algorithm2_bool_list_eqb
      (enfa_trace_bound
         (algorithm2_msss_machine [true; false] Bool.eqb foliance_ambiguous_a)
         [true])
      [true].
  Proof.
    apply algorithm2_msss_gamma_leaf_bridge.
    - apply algorithm2_bool_foliance_ambiguous_a_closed.
    - apply algorithm2_bool_alphabet_nodup.
    - apply algorithm2_bool_list_eqb_reflects_eq.
  Qed.

  Example algorithm2_msss_lr_projected_leaf_bridge_smoke :
    lr1_projected_leaf_count
      Bool.bool_dec
      (algorithm2_msss_machine [true; false] Bool.eqb foliance_ambiguous_a)
      [true] =
    algorithm2_msss_leaf
      (algorithm2_msss_machine [true; false] Bool.eqb foliance_ambiguous_a)
      [true].
  Proof.
    apply algorithm2_lr_projected_leaf_bridge.
  Qed.
End Algorithm2FolianceExamples.
