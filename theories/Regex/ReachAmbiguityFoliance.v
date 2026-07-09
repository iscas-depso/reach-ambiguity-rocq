From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Ambiguity Require Import DegreeofAmbiguity DegreeofInfiniteAmbiguity.
From PositionAutomata.Regex Require Import RegexReDoS.

(** Reach-ambiguity and foliance strings over the existing finite-NFA core.

    This file is intentionally a first verified layer over the current project:
    it reuses [finite_nfa], the position-NFA regex construction, and the
    executable word enumeration already used by the ambiguity witnesses.  It
    does not introduce epsilon-NFAs, LR machines, or simulation pruning. *)

Section ReachAmbiguityFoliance.
  Context {A : Type}.

  (** Epsilon-free NFA measures used by the foliance layer.
      [da_between] fixes both endpoints, [da_word] counts accepting runs,
      [dra_at] counts runs from an initial state to one endpoint,
      [dra_word] maximizes over endpoints, and [eta_word] sums them. *)

  (* da_M(p, w, q): runs from [p] to [q] reading [w]. *)
  Definition da_between
      (m : @finite_nfa A)
      (p : nfa_state (fnfa_base m))
      (w : list A)
      (q : nfa_state (fnfa_base m)) : nat :=
    da_from_to m p w q.

  (* da_M(w): accepting runs for [w]. *)
  Definition da_word (m : @finite_nfa A) (w : list A) : nat :=
    ambiguity_of_word (fnfa_base m) w.

  (* dra_M(w, q): runs from an initial state to [q] reading [w]. *)
  Definition dra_at
      (m : @finite_nfa A)
      (w : list A)
      (q : nfa_state (fnfa_base m)) : nat :=
    start_runs_to m w q.
  
  (* dra(M, w): the maximum [dra_at] over all endpoints. *)
  Definition dra_word (m : @finite_nfa A) (w : list A) : nat :=
    max_nats (map (dra_at m w) (fnfa_states m)).

  (* Total run count over all reachable endpoints after reading [w]. *)
  Definition eta_word (m : @finite_nfa A) (w : list A) : nat :=
    sum_nats (map (dra_at m w) (fnfa_states m)).

  (** Paper-facing helpers: final states, acceptance, reach-unambiguity,
      and bounded co-emptiness. *)

  Definition final_states (m : @finite_nfa A)
      : list (nfa_state (fnfa_base m)) :=
    filter (nfa_final (fnfa_base m)) (fnfa_states m).

  Definition accepted (m : @finite_nfa A) (w : list A) : Prop :=
    0 < da_word m w.

  Definition acceptedb (m : @finite_nfa A) (w : list A) : bool :=
    0 <? da_word m w.

  (* Every word-to-state reach-ambiguity is bounded by [k]. *)
  Definition k_reach_ambiguous (m : @finite_nfa A) (k : nat) : Prop :=
    forall w q, dra_at m w q <= k.

  Definition reach_unambiguous (m : @finite_nfa A) : Prop :=
    k_reach_ambiguous m 1.

  (* Every word of length at most [k] is accepted. *)
  Definition k_co_empty (m : @finite_nfa A) (k : nat) : Prop :=
    forall w, length w <= k -> accepted m w.

  (* Bridge positive counts with actual paths. *)

  Lemma dra_at_single_start :
    forall (m : @finite_nfa A) s w q,
      nfa_start (fnfa_base m) = [s] ->
      dra_at m w q = da_between m s w q.
  Proof.
    intros m s w q Hstart.
    unfold dra_at, da_between, start_runs_to, da_from_to.
    rewrite Hstart. simpl. lia.
  Qed.

  Lemma da_between_positive_path :
    forall (m : @finite_nfa A) p w q,
      0 < da_between m p w q ->
      path_from (fnfa_base m) p w q.
  Proof.
    intros m p w q Hpos.
    unfold da_between in Hpos.
    now apply runs_between_positive_path.
  Qed.

  Lemma path_da_between_positive :
    forall (m : @finite_nfa A) p w q,
      path_from (fnfa_base m) p w q ->
      0 < da_between m p w q.
  Proof.
    intros m p w q Hpath.
    unfold da_between.
    now apply path_runs_between_positive.
  Qed.

  Lemma dra_at_positive_path :
    forall (m : @finite_nfa A) w q,
      0 < dra_at m w q ->
      exists s,
        In s (nfa_start (fnfa_base m)) /\
        path_from (fnfa_base m) s w q.
  Proof.
    intros m w q Hpos.
    unfold dra_at in Hpos.
    now apply start_runs_to_positive_path.
  Qed.

  Lemma path_dra_at_positive :
    forall (m : @finite_nfa A) w q s,
      In s (nfa_start (fnfa_base m)) ->
      path_from (fnfa_base m) s w q ->
      0 < dra_at m w q.
  Proof.
    intros m w q s Hstart Hpath.
    unfold dra_at.
    eapply path_start_runs_to_positive; eauto.
  Qed.

  (* Regex entry point: convert [E] to a position NFA, then reuse NFA measures. *)

  Definition regex_foliance_nfa
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : @finite_nfa A :=
    regex_finite_position_nfa alphabet label_matches r.

  Definition regex_dra_at
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (w : list A)
      (q : nfa_state
             (fnfa_base (regex_foliance_nfa alphabet label_matches r))) : nat :=
    dra_at (regex_foliance_nfa alphabet label_matches r) w q.

  Definition regex_eta_word
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (w : list A) : nat :=
    eta_word (regex_foliance_nfa alphabet label_matches r) w.

  Definition regex_da_word
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (w : list A) : nat :=
    da_word (regex_foliance_nfa alphabet label_matches r) w.

  (* Problems 4/5, bounded executable form: enumerate words up to [k],
     then take maxima of da/dra/eta over those candidates. *)

  (* Example for alphabet [a; b] and [k = 2]:
     [[]; [a]; [b]; [a; a]; [a; b]; [b; a]; [b; b]]
     represents epsilon, a, b, aa, ab, ba, bb.
  *)
  Definition candidate_words (m : @finite_nfa A) (k : nat) : list (list A) :=
    words_upto (fnfa_alphabet m) k.

  Definition max_da_upto (m : @finite_nfa A) (k : nat) : nat :=
    max_nats (map (da_word m) (candidate_words m k)).

  Definition max_dra_upto (m : @finite_nfa A) (k : nat) : nat :=
    max_nats (map (dra_word m) (candidate_words m k)).

  Definition max_eta_upto (m : @finite_nfa A) (k : nat) : nat :=
    max_nats (map (eta_word m) (candidate_words m k)).

  (* Problem 4: [k_da] and [k_dra] require length <= [k], acceptance,
     and ambiguity at least [k].  The boolean forms drive enumeration. *)

  Definition k_da (m : @finite_nfa A) (k : nat) (w : list A) : Prop :=
    length w <= k /\
    accepted m w /\
    k <= da_word m w.

  Definition k_dab (m : @finite_nfa A) (k : nat) (w : list A) : bool :=
    (length w <=? k)
    && acceptedb m w
    && (k <=? da_word m w).

  Definition k_dra (m : @finite_nfa A) (k : nat) (w : list A) : Prop :=
    length w <= k /\
    accepted m w /\
    k <= dra_word m w.

  Definition k_drab (m : @finite_nfa A) (k : nat) (w : list A) : bool :=
    (length w <=? k)
    && acceptedb m w
    && (k <=? dra_word m w).

  Definition solve_k_da (m : @finite_nfa A) (k : nat) : option (list A) :=
    find (k_dab m k) (candidate_words m k).
  
  Definition solve_k_dra (m : @finite_nfa A) (k : nat) : option (list A) :=
    find (k_drab m k) (candidate_words m k).

  (* Problem 9: a k-foliance word is rejected, while some prefix reaches eta >= k. *)

  Fixpoint prefixes (w : list A) : list (list A) :=
    match w with
    | [] => [[]]
    | a :: w' => [] :: map (fun u => a :: u) (prefixes w')
    end.

  Definition eta_prefix_max (m : @finite_nfa A) (w : list A) : nat :=
    max_nats (map (eta_word m) (prefixes w)).

  Definition rejected (m : @finite_nfa A) (w : list A) : Prop :=
    da_word m w = 0.

  Definition rejectedb (m : @finite_nfa A) (w : list A) : bool :=
    Nat.eqb (da_word m w) 0.

  Definition k_foliance (m : @finite_nfa A) (k : nat) (w : list A) : Prop :=
    length w <= k /\
    rejected m w /\
    k <= eta_prefix_max m w.

  Definition k_folianceb (m : @finite_nfa A) (k : nat) (w : list A) : bool :=
    (length w <=? k)
    && rejectedb m w
    && (k <=? eta_prefix_max m w).

  Definition has_k_foliance (m : @finite_nfa A) (k : nat) : Prop :=
    exists w, k_foliance m k w.

  (* Problem 10 prefix-free variant.  The [against] forms separate the
     eta-counting automaton from the rejection automaton, matching partial
     matching settings such as Sigma*E. *)

  Definition prefix_rejected (m : @finite_nfa A) (w : list A) : Prop :=
    forall u, In u (prefixes w) -> rejected m u.

  Definition prefix_rejectedb (m : @finite_nfa A) (w : list A) : bool :=
    forallb (rejectedb m) (prefixes w).

  Definition k_foliance_against
      (count_m reject_m : @finite_nfa A)
      (k : nat)
      (w : list A) : Prop :=
    length w <= k /\
    rejected reject_m w /\
    k <= eta_prefix_max count_m w.

  Definition k_foliance_againstb
      (count_m reject_m : @finite_nfa A)
      (k : nat)
      (w : list A) : bool :=
    (length w <=? k)
    && rejectedb reject_m w
    && (k <=? eta_prefix_max count_m w).

  Definition k_foliance_pref_against
      (count_m reject_m : @finite_nfa A)
      (k : nat)
      (w : list A) : Prop :=
    length w <= k /\
    prefix_rejected reject_m w /\
    k <= eta_prefix_max count_m w.

  Definition k_foliance_pref_againstb
      (count_m reject_m : @finite_nfa A)
      (k : nat)
      (w : list A) : bool :=
    (length w <=? k)
    && prefix_rejectedb reject_m w
    && (k <=? eta_prefix_max count_m w).

  Definition solve_foliance (m : @finite_nfa A) (k : nat) : option (list A) :=
    find (k_folianceb m k) (candidate_words m k).

  Definition solve_foliance_against
      (count_m reject_m : @finite_nfa A)
      (k : nat) : option (list A) :=
    find (k_foliance_againstb count_m reject_m k) (candidate_words count_m k).

  Definition solve_foliance_pref_against
      (count_m reject_m : @finite_nfa A)
      (k : nat) : option (list A) :=
    find (k_foliance_pref_againstb count_m reject_m k) (candidate_words count_m k).

  (* Regex-level solvers: ordinary foliance uses one regex; prefix-free or
     partial settings may use separate eta-counting and rejection regexes. *)

  Definition solve_regex_foliance
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (k : nat) : option (list A) :=
    solve_foliance (regex_foliance_nfa alphabet label_matches r) k.

  Definition solve_regex_foliance_pref_against
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (count_r reject_r : regex A)
      (k : nat) : option (list A) :=
    solve_foliance_pref_against
      (regex_foliance_nfa alphabet label_matches count_r)
      (regex_foliance_nfa alphabet label_matches reject_r)
      k.

  (* Mathematical specs for candidates and prefixes:
     [word_over] means w in Sigma*, and [prefix_of] means u in Pref(w). *)

  Definition word_over (alphabet : list A) (w : list A) : Prop :=
    Forall (fun a => In a alphabet) w.

  Definition prefix_of (u w : list A) : Prop :=
    exists v, w = u ++ v.

  (* Enumeration correctness for bounded words over a fixed alphabet. *)
  
  Lemma words_of_length_length :
    forall (alphabet : list A) n (w : list A),
      In w (words_of_length alphabet n) ->
      length w = n.
  Proof.
    intros alphabet n.
    induction n as [| n IH]; intros w Hin; simpl in Hin.
    - destruct Hin as [Hw | []]. subst. reflexivity.
    - apply in_concat in Hin as [ws [Hws Hw]].
      apply in_map_iff in Hws as [a [Hws _]].
      subst ws.
      apply in_map_iff in Hw as [w' [Hw Hw']].
      subst w.
      simpl. now rewrite (IH w' Hw').
  Qed.

  Lemma words_of_length_over :
    forall (alphabet : list A) n (w : list A),
      In w (words_of_length alphabet n) ->
      word_over alphabet w.
  Proof.
    intros alphabet n.
    induction n as [| n IH]; intros w Hin; simpl in Hin.
    - destruct Hin as [Hw | []]. subst. constructor.
    - apply in_concat in Hin as [ws [Hws Hw]].
      apply in_map_iff in Hws as [a [Hws Ha]].
      subst ws.
      apply in_map_iff in Hw as [w' [Hw Hw']].
      subst w.
      constructor; auto.
      now apply IH.
  Qed.

  Lemma words_of_length_complete :
    forall (alphabet : list A) (w : list A),
      word_over alphabet w ->
      In w (words_of_length alphabet (length w)).
  Proof.
    intros alphabet w H.
    induction H as [| a w Ha _ IH]; simpl.
    - left. reflexivity.
    - apply in_concat.
      exists (map (fun w' => a :: w') (words_of_length alphabet (length w))).
      split.
      + apply in_map_iff. exists a. split; auto.
      + now apply in_map.
  Qed.

  Lemma words_upto_length :
    forall (alphabet : list A) k (w : list A),
      In w (words_upto alphabet k) ->
      length w <= k.
  Proof.
    intros alphabet k.
    induction k as [| k IH]; intros w Hin; simpl in Hin.
    - destruct Hin as [Hw | []]. subst. simpl. lia.
    - apply in_app_or in Hin as [Hin | Hin].
      + specialize (IH w Hin). lia.
      + pose proof (words_of_length_length alphabet (S k) w Hin). lia.
  Qed.

  Lemma words_upto_over :
    forall (alphabet : list A) k (w : list A),
      In w (words_upto alphabet k) ->
      word_over alphabet w.
  Proof.
    intros alphabet k.
    induction k as [| k IH]; intros w Hin; simpl in Hin.
    - destruct Hin as [Hw | []]. subst. constructor.
    - apply in_app_or in Hin as [Hin | Hin].
      + now apply IH.
      + now apply words_of_length_over with (n := S k).
  Qed.

  Lemma words_upto_complete :
    forall (alphabet : list A) k (w : list A),
      length w <= k ->
      word_over alphabet w ->
      In w (words_upto alphabet k).
  Proof.
    intros alphabet k.
    induction k as [| k IH]; intros w Hlen Hover; simpl.
    - assert (Hw : w = []) by (destruct w; simpl in Hlen; try lia; reflexivity).
      subst. left. reflexivity.
    - destruct (le_gt_dec (length w) k) as [Hle | Hgt].
      + apply in_or_app. left. now apply IH.
      + apply in_or_app. right.
        assert (Hlen_eq : length w = S k) by lia.
        change (In w (words_of_length alphabet (S k))).
        rewrite <- Hlen_eq.
        now apply words_of_length_complete.
  Qed.

  Theorem candidate_words_sound :
    forall (m : @finite_nfa A) k w,
      In w (candidate_words m k) ->
      length w <= k /\ word_over (fnfa_alphabet m) w.
  Proof.
    intros m k w Hin.
    unfold candidate_words in Hin.
    split.
    - now apply words_upto_length in Hin.
    - now apply words_upto_over with (k := k).
  Qed.

  Theorem candidate_words_complete :
    forall (m : @finite_nfa A) k w,
      length w <= k ->
      word_over (fnfa_alphabet m) w ->
      In w (candidate_words m k).
  Proof.
    intros m k w Hlen Hover.
    unfold candidate_words.
    now apply words_upto_complete.
  Qed.

  (* The executable [prefixes] list agrees with the paper's Pref(w). *)

  Lemma prefixes_sound :
    forall w u,
      In u (prefixes w) ->
      prefix_of u w.
  Proof.
    induction w as [| a w IH]; intros u Hin; simpl in Hin.
    - destruct Hin as [Hu | []]. subst.
      exists []. reflexivity.
    - destruct Hin as [Hu | Hin].
      + subst u. exists (a :: w). reflexivity.
      + apply in_map_iff in Hin as [u' [Hu Hin]].
        subst u.
        destruct (IH u' Hin) as [v Hv].
        subst w.
        exists v. reflexivity.
  Qed.

  Lemma prefixes_complete :
    forall u w,
      prefix_of u w ->
      In u (prefixes w).
  Proof.
    intros u w [v Hw]. subst w.
    induction u as [| a u IH]; simpl.
    - destruct v; simpl; left; reflexivity.
    - right. now apply in_map.
  Qed.

  Lemma prefixes_refl :
    forall w, In w (prefixes w).
  Proof.
    intros w.
    apply prefixes_complete.
    exists []. now rewrite app_nil_r.
  Qed.

  Lemma prefix_of_length :
    forall u w,
      prefix_of u w ->
      length u <= length w.
  Proof.
    intros u w [v Hw]. subst.
    rewrite length_app. lia.
  Qed.

  Lemma prefix_of_word_over :
    forall alphabet u w,
      prefix_of u w ->
      word_over alphabet w ->
      word_over alphabet u.
  Proof.
    intros alphabet u w [v Hw] Hover. subst.
    unfold word_over in *.
    rewrite Forall_app in Hover.
    now destruct Hover.
  Qed.

  Theorem candidate_words_prefix :
    forall (m : @finite_nfa A) k w u,
      In w (candidate_words m k) ->
      In u (prefixes w) ->
      In u (candidate_words m k).
  Proof.
    intros m k w u Hw Hu.
    destruct (candidate_words_sound m k w Hw) as [Hlen Hover].
    pose proof (prefixes_sound w u Hu) as Hprefix.
    apply candidate_words_complete.
    - eapply Nat.le_trans.
      + exact (prefix_of_length u w Hprefix).
      + exact Hlen.
    - eapply prefix_of_word_over; eauto.
  Qed.

  (* Generic nat-list tools: max witnesses, max <= sum, and sum interchange. *)

  Lemma max_nats_in_le :
    forall xs x,
      In x xs -> x <= max_nats xs.
  Proof.
    induction xs as [| y ys IH]; simpl; intros x Hin.
    - contradiction.
    - destruct Hin as [Hx | Hin].
      + subst. apply Nat.le_max_l.
      + eapply Nat.le_trans.
        * apply IH. exact Hin.
        * apply Nat.le_max_r.
  Qed.

  Lemma max_nats_positive_witness :
    forall xs,
      0 < max_nats xs ->
      exists x, In x xs /\ x = max_nats xs.
  Proof.
    induction xs as [| y ys IH]; simpl; intros Hpos.
    - lia.
    - destruct (Nat.leb (max_nats ys) y) eqn:Hle.
      + apply Nat.leb_le in Hle.
        exists y. split; simpl; auto.
        rewrite Nat.max_l by exact Hle. reflexivity.
      + apply Nat.leb_gt in Hle.
        assert (Htail : 0 < max_nats ys) by lia.
        destruct (IH Htail) as [x [Hin Hx]].
        exists x. split; simpl; auto.
        rewrite Nat.max_r by lia. exact Hx.
  Qed.

  Lemma max_nats_le_sum_nats :
    forall xs, max_nats xs <= sum_nats xs.
  Proof.
    induction xs as [| x xs IH]; simpl; lia.
  Qed.

  Lemma sum_nats_map_zero :
    forall {B : Type} (xs : list B),
      sum_nats (map (fun _ => 0) xs) = 0.
  Proof.
    induction xs as [| x xs IH]; simpl; auto.
  Qed.

  Lemma sum_map_swap :
    forall {B C : Type} (f : B -> C -> nat) xs ys,
      sum_nats (map (fun x => sum_nats (map (f x) ys)) xs) =
      sum_nats (map (fun y => sum_nats (map (fun x => f x y) xs)) ys).
  Proof.
    intros B C f xs.
    induction xs as [| x xs IH]; intros ys; simpl.
    - now rewrite sum_nats_map_zero.
    - rewrite IH.
      clear IH.
      induction ys as [| y ys IH]; simpl; auto.
      lia.
  Qed.

  (* Definitions 7/8: endpoint [dra] is bounded by total [eta]. *)

  Theorem dra_at_le_dra_word :
    forall (m : @finite_nfa A) w q,
      In q (fnfa_states m) ->
      dra_at m w q <= dra_word m w.
  Proof.
    intros m w q Hq.
    unfold dra_word.
    apply max_nats_in_le.
    now apply in_map.
  Qed.

  Theorem dra_word_le_eta_word :
    forall (m : @finite_nfa A) w,
      dra_word m w <= eta_word m w.
  Proof.
    intros m w.
    unfold dra_word, eta_word.
    apply max_nats_le_sum_nats.
  Qed.

  Theorem dra_at_le_eta_word :
    forall (m : @finite_nfa A) w q,
      In q (fnfa_states m) ->
      dra_at m w q <= eta_word m w.
  Proof.
    intros m w q Hq.
    eapply Nat.le_trans.
    - now apply dra_at_le_dra_word.
    - apply dra_word_le_eta_word.
  Qed.

  (* Definitions 6/7: in a well-formed finite NFA, accepting runs equal the
     sum of [dra_at] over final states. *)
  Lemma final_states_sound :
    forall (m : @finite_nfa A) q,
      In q (final_states m) ->
      In q (fnfa_states m) /\ nfa_final (fnfa_base m) q = true.
  Proof.
    intros m q H.
    unfold final_states in H.
    now apply filter_In in H.
  Qed.

  Lemma final_states_complete :
    forall (m : @finite_nfa A) q,
      In q (fnfa_states m) ->
      nfa_final (fnfa_base m) q = true ->
      In q (final_states m).
  Proof.
    intros m q Hq Hfinal.
    unfold final_states.
    apply filter_In.
    split; assumption.
  Qed.

  Lemma final_states_NoDup :
    forall (m : @finite_nfa A),
      finite_nfa_wf m ->
      NoDup (final_states m).
  Proof.
    intros m Hwf.
    unfold final_states.
    apply NoDup_filter.
    now destruct Hwf.
  Qed.

  Lemma sum_eqb_zero_notin :
    forall (m : @finite_nfa A) xs q,
      (forall r, In r xs -> q <> r) ->
      sum_nats
        (map
           (fun r => if fnfa_state_eqb m q r then 1 else 0)
           xs) = 0.
  Proof.
    intros m xs.
    induction xs as [| x xs IH]; intros q Hnotin; simpl; auto.
    destruct (fnfa_state_eqb m q x) eqn:Heq.
    - apply fnfa_state_eqb_sound in Heq.
      exfalso. apply (Hnotin x); simpl; auto.
    - apply IH.
      intros r Hr.
      apply Hnotin. simpl. auto.
  Qed.

  Lemma sum_eqb_one_in_NoDup :
    forall (m : @finite_nfa A) xs q,
      NoDup xs ->
      In q xs ->
      sum_nats
        (map
           (fun r => if fnfa_state_eqb m q r then 1 else 0)
           xs) = 1.
  Proof.
    intros m xs.
    induction xs as [| x xs IH]; intros q Hnodup Hin; simpl in *.
    - contradiction.
    - inversion Hnodup as [| x' xs' Hnotin Hnodup']; subst.
      destruct Hin as [Hq | Hin].
      + subst x.
        rewrite (fnfa_state_eqb_complete m q q eq_refl).
        rewrite sum_eqb_zero_notin.
        * reflexivity.
        * intros r Hr Heq. subst r. contradiction.
      + destruct (fnfa_state_eqb m q x) eqn:Heq.
        * apply fnfa_state_eqb_sound in Heq.
          subst x. contradiction.
        * now apply IH.
  Qed.

  Lemma sum_runs_between_nil_final_states :
    forall (m : @finite_nfa A) q,
      finite_nfa_wf m ->
      In q (fnfa_states m) ->
      sum_nats
        (map (fun r => runs_between m q [] r) (final_states m)) =
      if nfa_final (fnfa_base m) q then 1 else 0.
  Proof.
    intros m q Hwf Hq.
    simpl.
    destruct (nfa_final (fnfa_base m) q) eqn:Hfinal.
    - apply sum_eqb_one_in_NoDup.
      + now apply final_states_NoDup.
      + now apply final_states_complete.
    - apply sum_eqb_zero_notin.
      intros r Hr Heq.
      subst r.
      apply final_states_sound in Hr as [_ Hrfinal].
      rewrite Hfinal in Hrfinal. discriminate.
  Qed.

  Lemma accepting_runs_from_final_states :
    forall (m : @finite_nfa A) w q,
      finite_nfa_wf m ->
      In q (fnfa_states m) ->
      accepting_runs_from (fnfa_base m) q w =
      sum_nats
        (map (fun r => runs_between m q w r) (final_states m)).
  Proof.
    intros m w.
    induction w as [| a w IH]; intros q Hwf Hq; simpl.
    - symmetry.
      now apply sum_runs_between_nil_final_states.
    - assert (Hmap :
        map
          (fun q' => accepting_runs_from (fnfa_base m) q' w)
          (nfa_step (fnfa_base m) q a) =
        map
          (fun q' =>
             sum_nats
               (map
                  (fun r => runs_between m q' w r)
                  (final_states m)))
          (nfa_step (fnfa_base m) q a)).
      {
        apply map_ext_in.
        intros q' Hstep.
        apply IH; auto.
        eapply finite_nfa_wf_step_in_states; eauto.
      }
      rewrite Hmap.
      rewrite
        (sum_map_swap
           (fun q' r => runs_between m q' w r)
           (nfa_step (fnfa_base m) q a)
           (final_states m)).
    reflexivity.
  Qed.

  (* [da_word] is the sum of [dra_at] over final states. *)
  Theorem da_word_final_dra_sum :
    forall (m : @finite_nfa A) w,
      finite_nfa_wf m ->
      da_word m w =
      sum_nats (map (dra_at m w) (final_states m)).
  Proof.
    intros m w Hwf.
    unfold da_word, ambiguity_of_word, dra_at, start_runs_to.
    assert (Hmap :
      map
        (fun q => accepting_runs_from (fnfa_base m) q w)
        (nfa_start (fnfa_base m)) =
      map
        (fun q =>
           sum_nats
             (map
                (fun r => runs_between m q w r)
                (final_states m)))
        (nfa_start (fnfa_base m))).
    {
      apply map_ext_in.
      intros q Hstart.
      apply accepting_runs_from_final_states; auto.
      eapply finite_nfa_wf_start_in_states; eauto.
    }
    rewrite Hmap.
    rewrite
      (sum_map_swap
         (fun q r => runs_between m q w r)
         (nfa_start (fnfa_base m))
         (final_states m)).
    reflexivity.
  Qed.

  (** Problem 5 executable spec: a bounded maximum is an upper bound over
      candidates, and every positive maximum has a witnessing candidate. *)

  Lemma max_mapped_upto_upper :
    forall (m : @finite_nfa A) k (f : @finite_nfa A -> list A -> nat) w,
      In w (candidate_words m k) ->
      f m w <= max_nats (map (f m) (candidate_words m k)).
  Proof.
    intros m k f w Hin.
    apply max_nats_in_le.
    now apply in_map.
  Qed.

  Lemma max_mapped_upto_witness :
    forall (m : @finite_nfa A) k (f : @finite_nfa A -> list A -> nat),
      0 < max_nats (map (f m) (candidate_words m k)) ->
      exists w,
        In w (candidate_words m k) /\
        f m w = max_nats (map (f m) (candidate_words m k)).
  Proof.
    intros m k f Hpos.
    destruct (max_nats_positive_witness _ Hpos) as [n [Hin Hn]].
    apply in_map_iff in Hin as [w [Hw Hin]].
    subst n.
    exists w. split; auto.
  Qed.

  Theorem max_da_upto_upper :
    forall (m : @finite_nfa A) k w,
      In w (candidate_words m k) ->
      da_word m w <= max_da_upto m k.
  Proof.
    intros m k w Hin.
    unfold max_da_upto.
    now apply max_mapped_upto_upper.
  Qed.

  Theorem max_dra_upto_upper :
    forall (m : @finite_nfa A) k w,
      In w (candidate_words m k) ->
      dra_word m w <= max_dra_upto m k.
  Proof.
    intros m k w Hin.
    unfold max_dra_upto.
    now apply max_mapped_upto_upper.
  Qed.

  Theorem max_eta_upto_upper :
    forall (m : @finite_nfa A) k w,
      In w (candidate_words m k) ->
      eta_word m w <= max_eta_upto m k.
  Proof.
    intros m k w Hin.
    unfold max_eta_upto.
    now apply max_mapped_upto_upper.
  Qed.

  Theorem max_da_upto_witness :
    forall (m : @finite_nfa A) k,
      0 < max_da_upto m k ->
      exists w,
        In w (candidate_words m k) /\
        da_word m w = max_da_upto m k.
  Proof.
    intros m k Hpos.
    unfold max_da_upto in *.
    now apply max_mapped_upto_witness.
  Qed.

  Theorem max_dra_upto_witness :
    forall (m : @finite_nfa A) k,
      0 < max_dra_upto m k ->
      exists w,
        In w (candidate_words m k) /\
        dra_word m w = max_dra_upto m k.
  Proof.
    intros m k Hpos.
    unfold max_dra_upto in *.
    now apply max_mapped_upto_witness.
  Qed.

  Theorem max_eta_upto_witness :
    forall (m : @finite_nfa A) k,
      0 < max_eta_upto m k ->
      exists w,
        In w (candidate_words m k) /\
        eta_word m w = max_eta_upto m k.
  Proof.
    intros m k Hpos.
    unfold max_eta_upto in *.
    now apply max_mapped_upto_witness.
  Qed.

  (** Boolean/Prop consistency.  Solvers compute with booleans, and their
      soundness theorems return to Prop through these [*_correct] lemmas. *)

  Lemma acceptedb_correct :
    forall (m : @finite_nfa A) w,
      acceptedb m w = true <-> accepted m w.
  Proof.
    intros m w.
    unfold acceptedb, accepted.
    apply Nat.ltb_lt.
  Qed.

  Lemma rejectedb_correct :
    forall (m : @finite_nfa A) w,
      rejectedb m w = true <-> rejected m w.
  Proof.
    intros m w.
    unfold rejectedb, rejected.
    apply Nat.eqb_eq.
  Qed.

  Theorem k_dab_correct :
    forall (m : @finite_nfa A) k w,
      k_dab m k w = true <-> k_da m k w.
  Proof.
    intros m k w.
    unfold k_dab, k_da, acceptedb, accepted.
    split; intros H.
    - apply andb_true_iff in H as [Hleft Hda].
      apply andb_true_iff in Hleft as [Hlen Hacc].
      apply Nat.leb_le in Hlen.
      apply Nat.ltb_lt in Hacc.
      apply Nat.leb_le in Hda.
      repeat split; assumption.
    - destruct H as [Hlen [Hacc Hda]].
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * now apply Nat.leb_le.
        * now apply Nat.ltb_lt.
      + now apply Nat.leb_le.
  Qed.

  Theorem k_drab_correct :
    forall (m : @finite_nfa A) k w,
      k_drab m k w = true <-> k_dra m k w.
  Proof.
    intros m k w.
    unfold k_drab, k_dra, acceptedb, accepted.
    split; intros H.
    - apply andb_true_iff in H as [Hleft Hdra].
      apply andb_true_iff in Hleft as [Hlen Hacc].
      apply Nat.leb_le in Hlen.
      apply Nat.ltb_lt in Hacc.
      apply Nat.leb_le in Hdra.
      repeat split; assumption.
    - destruct H as [Hlen [Hacc Hdra]].
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * now apply Nat.leb_le.
        * now apply Nat.ltb_lt.
      + now apply Nat.leb_le.
  Qed.

  Theorem k_folianceb_correct :
    forall (m : @finite_nfa A) k w,
      k_folianceb m k w = true <-> k_foliance m k w.
  Proof.
    intros m k w.
    unfold k_folianceb, k_foliance, rejectedb, rejected.
    split; intros H.
    - apply andb_true_iff in H as [Hleft Heta].
      apply andb_true_iff in Hleft as [Hlen Hrej].
      apply Nat.leb_le in Hlen.
      apply Nat.eqb_eq in Hrej.
      apply Nat.leb_le in Heta.
      repeat split; assumption.
    - destruct H as [Hlen [Hrej Heta]].
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * now apply Nat.leb_le.
        * now apply Nat.eqb_eq.
      + now apply Nat.leb_le.
  Qed.

  Lemma prefix_rejected_rejected :
    forall (m : @finite_nfa A) w,
      prefix_rejected m w -> rejected m w.
  Proof.
    intros m w Hprefix.
    apply Hprefix.
    apply prefixes_refl.
  Qed.

  Theorem prefix_rejectedb_correct :
    forall (m : @finite_nfa A) w,
      prefix_rejectedb m w = true <-> prefix_rejected m w.
  Proof.
    intros m w.
    unfold prefix_rejectedb, prefix_rejected.
    split; intros H.
    - intros u Hu.
      apply rejectedb_correct.
      rewrite forallb_forall in H.
      now apply H.
    - apply forallb_forall.
      intros u Hu.
      apply rejectedb_correct.
      now apply H.
  Qed.

  Theorem k_foliance_againstb_correct :
    forall (count_m reject_m : @finite_nfa A) k w,
      k_foliance_againstb count_m reject_m k w = true <->
      k_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w.
    unfold k_foliance_againstb, k_foliance_against, rejectedb, rejected.
    split; intros H.
    - apply andb_true_iff in H as [Hleft Heta].
      apply andb_true_iff in Hleft as [Hlen Hrej].
      apply Nat.leb_le in Hlen.
      apply Nat.eqb_eq in Hrej.
      apply Nat.leb_le in Heta.
      repeat split; assumption.
    - destruct H as [Hlen [Hrej Heta]].
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * now apply Nat.leb_le.
        * now apply Nat.eqb_eq.
      + now apply Nat.leb_le.
  Qed.

  Theorem k_foliance_pref_againstb_correct :
    forall (count_m reject_m : @finite_nfa A) k w,
      k_foliance_pref_againstb count_m reject_m k w = true <->
      k_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w.
    unfold k_foliance_pref_againstb, k_foliance_pref_against.
    split; intros H.
    - apply andb_true_iff in H as [Hleft Heta].
      apply andb_true_iff in Hleft as [Hlen Hprefix].
      apply Nat.leb_le in Hlen.
      apply prefix_rejectedb_correct in Hprefix.
      apply Nat.leb_le in Heta.
      repeat split; assumption.
    - destruct H as [Hlen [Hprefix Heta]].
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * now apply Nat.leb_le.
        * now apply prefix_rejectedb_correct.
      + now apply Nat.leb_le.
  Qed.

  Theorem k_foliance_against_same :
    forall (m : @finite_nfa A) k w,
      k_foliance_against m m k w <-> k_foliance m k w.
  Proof.
    intros m k w.
    unfold k_foliance_against, k_foliance.
    tauto.
  Qed.

  (* [k_foliance_pref] is stronger than [k_foliance]: every prefix is rejected. *)

  Theorem k_foliance_pref_against_foliance_against :
    forall (count_m reject_m : @finite_nfa A) k w,
      k_foliance_pref_against count_m reject_m k w ->
      k_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w [Hlen [Hprefix Heta]].
    repeat split; auto.
    now apply prefix_rejected_rejected.
  Qed.

  (* Problem 9 prefix-max witness: a k-foliance word has a prefix with eta >= k. *)

  Theorem k_foliance_eta_prefix_witness :
    forall (m : @finite_nfa A) k w,
      k_foliance m k w ->
      exists u,
        In u (prefixes w) /\
        k <= eta_word m u.
  Proof.
    intros m [| k] w [_ [_ Heta]].
    - exists []. split.
      + destruct w as [| a w]; simpl; auto.
      + lia.
    - destruct
        (max_nats_positive_witness
           (map (eta_word m) (prefixes w)))
        as [n [Hn Hmax]].
      { unfold eta_prefix_max in Heta. lia. }
      apply in_map_iff in Hn as [u [Hu Hprefix]].
      subst n.
      exists u. split; auto.
      unfold eta_prefix_max in Heta.
      lia.
  Qed.

  Theorem k_foliance_against_eta_prefix_witness :
    forall (count_m reject_m : @finite_nfa A) k w,
      k_foliance_against count_m reject_m k w ->
      exists u,
        In u (prefixes w) /\
        k <= eta_word count_m u.
  Proof.
    intros count_m reject_m [| k] w [_ [_ Heta]].
    - exists []. split.
      + destruct w as [| a w]; simpl; auto.
      + lia.
    - destruct
        (max_nats_positive_witness
           (map (eta_word count_m) (prefixes w)))
        as [n [Hn Hmax]].
      { unfold eta_prefix_max in Heta. lia. }
      apply in_map_iff in Hn as [u [Hu Hprefix]].
      subst n.
      exists u. split; auto.
      unfold eta_prefix_max in Heta.
      lia.
  Qed.

  (* Lemma 4 non-co-empty direction: any k-foliance word rules out k-co-emptiness. *)

  Theorem k_foliance_not_k_co_empty :
    forall (m : @finite_nfa A) k w,
      k_foliance m k w ->
      ~ k_co_empty m k.
  Proof.
    intros m k w [Hlen [Hrej _]] Hco.
    specialize (Hco w Hlen).
    unfold rejected, accepted in *.
    lia.
  Qed.

  Theorem has_k_foliance_not_k_co_empty :
    forall (m : @finite_nfa A) k,
      has_k_foliance m k ->
      ~ k_co_empty m k.
  Proof.
    intros m k [w Hw].
    now apply k_foliance_not_k_co_empty with (w := w).
  Qed.

  (* All enumeration solvers use [find]; first prove generic soundness and
     candidate-completeness for [find]. *)

  Lemma find_sound :
    forall {B : Type} (f : B -> bool) xs x,
      find f xs = Some x ->
      In x xs /\ f x = true.
  Proof.
    intros B f xs.
    induction xs as [| y ys IH]; simpl; intros x Hfind.
    - discriminate.
    - destruct (f y) eqn:Hy.
      + inversion Hfind; subst. split; simpl; auto.
      + apply IH in Hfind as [Hin Hx].
        split; simpl; auto.
  Qed.

  Lemma find_complete :
    forall {B : Type} (f : B -> bool) xs,
      (exists x, In x xs /\ f x = true) ->
      exists y, find f xs = Some y /\ In y xs /\ f y = true.
  Proof.
    intros B f xs.
    induction xs as [| y ys IH]; intros [x [Hin Hx]].
    - contradiction.
    - simpl in Hin.
      destruct Hin as [Hx_eq | Hin].
      + subst x. simpl. rewrite Hx.
        exists y. repeat split; simpl; auto.
      + simpl. destruct (f y) eqn:Hy.
        * exists y. repeat split; simpl; auto.
        * destruct (IH (ex_intro _ x (conj Hin Hx)))
            as [z [Hfind [Hzin Hz]]].
          exists z. repeat split; simpl; auto.
  Qed.

  (* Solver correctness:
     sound means the returned word satisfies the target predicate;
     complete_over_candidates means [find] succeeds when a candidate solves it. *)

  Theorem solve_k_da_sound :
    forall (m : @finite_nfa A) k w,
      solve_k_da m k = Some w ->
      In w (candidate_words m k) /\ k_da m k w.
  Proof.
    intros m k w Hsolve.
    unfold solve_k_da in Hsolve.
    apply find_sound in Hsolve as [Hin Hk].
    split; auto.
    now apply k_dab_correct.
  Qed.

  Theorem solve_k_da_complete_over_candidates :
    forall (m : @finite_nfa A) k,
      (exists w, In w (candidate_words m k) /\ k_da m k w) ->
      exists w,
        solve_k_da m k = Some w /\
        In w (candidate_words m k) /\
        k_da m k w.
  Proof.
    intros m k [w [Hin Hk]].
    unfold solve_k_da.
    destruct
      (find_complete
         (k_dab m k)
         (candidate_words m k)
         (ex_intro _ w (conj Hin ((proj2 (k_dab_correct m k w)) Hk))))
      as [w' [Hfind [Hin' Hk']]].
    exists w'. split.
    - exact Hfind.
    - split; auto.
      now apply k_dab_correct.
  Qed.

  Theorem solve_k_dra_sound :
    forall (m : @finite_nfa A) k w,
      solve_k_dra m k = Some w ->
      In w (candidate_words m k) /\ k_dra m k w.
  Proof.
    intros m k w Hsolve.
    unfold solve_k_dra in Hsolve.
    apply find_sound in Hsolve as [Hin Hk].
    split; auto.
    now apply k_drab_correct.
  Qed.

  Theorem solve_k_dra_complete_over_candidates :
    forall (m : @finite_nfa A) k,
      (exists w, In w (candidate_words m k) /\ k_dra m k w) ->
      exists w,
        solve_k_dra m k = Some w /\
        In w (candidate_words m k) /\
        k_dra m k w.
  Proof.
    intros m k [w [Hin Hk]].
    unfold solve_k_dra.
    destruct
      (find_complete
         (k_drab m k)
         (candidate_words m k)
         (ex_intro _ w (conj Hin ((proj2 (k_drab_correct m k w)) Hk))))
      as [w' [Hfind [Hin' Hk']]].
    exists w'. split.
    - exact Hfind.
    - split; auto.
      now apply k_drab_correct.
  Qed.

  Theorem solve_foliance_sound :
    forall (m : @finite_nfa A) k w,
      solve_foliance m k = Some w ->
      In w (candidate_words m k) /\ k_foliance m k w.
  Proof.
    intros m k w Hsolve.
    unfold solve_foliance in Hsolve.
    apply find_sound in Hsolve as [Hin Hk].
    split; auto.
      now apply k_folianceb_correct.
  Qed.

  Theorem solve_foliance_against_sound :
    forall (count_m reject_m : @finite_nfa A) k w,
      solve_foliance_against count_m reject_m k = Some w ->
      In w (candidate_words count_m k) /\
      k_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w Hsolve.
    unfold solve_foliance_against in Hsolve.
    apply find_sound in Hsolve as [Hin Hk].
    split; auto.
    now apply k_foliance_againstb_correct.
  Qed.

  Theorem solve_foliance_pref_against_sound :
    forall (count_m reject_m : @finite_nfa A) k w,
      solve_foliance_pref_against count_m reject_m k = Some w ->
      In w (candidate_words count_m k) /\
      k_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k w Hsolve.
    unfold solve_foliance_pref_against in Hsolve.
    apply find_sound in Hsolve as [Hin Hk].
    split; auto.
    now apply k_foliance_pref_againstb_correct.
  Qed.

  Theorem solve_foliance_complete_over_candidates :
    forall (m : @finite_nfa A) k,
      (exists w, In w (candidate_words m k) /\ k_foliance m k w) ->
      exists w,
        solve_foliance m k = Some w /\
        In w (candidate_words m k) /\
        k_foliance m k w.
  Proof.
    intros m k [w [Hin Hk]].
    unfold solve_foliance.
    destruct
      (find_complete
         (k_folianceb m k)
         (candidate_words m k)
         (ex_intro _ w (conj Hin ((proj2 (k_folianceb_correct m k w)) Hk))))
      as [w' [Hfind [Hin' Hk']]].
    exists w'. split.
    - exact Hfind.
    - split; auto.
      now apply k_folianceb_correct.
  Qed.

  Theorem solve_foliance_against_complete_over_candidates :
    forall (count_m reject_m : @finite_nfa A) k,
      (exists w,
        In w (candidate_words count_m k) /\
        k_foliance_against count_m reject_m k w) ->
      exists w,
        solve_foliance_against count_m reject_m k = Some w /\
        In w (candidate_words count_m k) /\
        k_foliance_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k [w [Hin Hk]].
    unfold solve_foliance_against.
    destruct
      (find_complete
         (k_foliance_againstb count_m reject_m k)
         (candidate_words count_m k)
         (ex_intro _
            w
            (conj
               Hin
               ((proj2
                   (k_foliance_againstb_correct count_m reject_m k w))
                  Hk))))
      as [w' [Hfind [Hin' Hk']]].
    exists w'. split.
    - exact Hfind.
    - split; auto.
      now apply k_foliance_againstb_correct.
  Qed.

  Theorem solve_foliance_pref_against_complete_over_candidates :
    forall (count_m reject_m : @finite_nfa A) k,
      (exists w,
        In w (candidate_words count_m k) /\
        k_foliance_pref_against count_m reject_m k w) ->
      exists w,
        solve_foliance_pref_against count_m reject_m k = Some w /\
        In w (candidate_words count_m k) /\
        k_foliance_pref_against count_m reject_m k w.
  Proof.
    intros count_m reject_m k [w [Hin Hk]].
    unfold solve_foliance_pref_against.
    destruct
      (find_complete
         (k_foliance_pref_againstb count_m reject_m k)
         (candidate_words count_m k)
         (ex_intro _
            w
            (conj
               Hin
               ((proj2
                   (k_foliance_pref_againstb_correct count_m reject_m k w))
                  Hk))))
      as [w' [Hfind [Hin' Hk']]].
    exists w'. split.
    - exact Hfind.
    - split; auto.
      now apply k_foliance_pref_againstb_correct.
  Qed.

  Theorem solve_regex_foliance_pref_against_sound :
    forall alphabet label_matches count_r reject_r k w,
      solve_regex_foliance_pref_against
        alphabet label_matches count_r reject_r k = Some w ->
      In w
        (candidate_words
           (regex_foliance_nfa alphabet label_matches count_r)
           k) /\
      k_foliance_pref_against
        (regex_foliance_nfa alphabet label_matches count_r)
        (regex_foliance_nfa alphabet label_matches reject_r)
        k
        w.
  Proof.
    intros alphabet label_matches count_r reject_r k w Hsolve.
    unfold solve_regex_foliance_pref_against in Hsolve.
    now apply solve_foliance_pref_against_sound in Hsolve.
  Qed.
End ReachAmbiguityFoliance.

Section ReachAmbiguityFolianceExamples.
  (* Example: true + true has two accepting branches; eta can be 2 while
     max-dra need not be 2 when the branches end in different states. *)

  Definition foliance_ambiguous_a : regex bool :=
    Alt (Atom true) (Atom true).

  Definition foliance_ambiguous_a_nfa : @finite_nfa bool :=
    regex_foliance_nfa [true; false] Bool.eqb foliance_ambiguous_a.

  Example foliance_ambiguous_a_da_word :
    regex_da_word [true] Bool.eqb foliance_ambiguous_a [true] = 2.
  Proof. reflexivity. Qed.

  Example foliance_ambiguous_a_eta_word :
    regex_eta_word [true] Bool.eqb foliance_ambiguous_a [true] = 2.
  Proof. reflexivity. Qed.

  Example foliance_ambiguous_a_solver :
    solve_regex_foliance [true; false] Bool.eqb foliance_ambiguous_a 2 =
      Some [true; true].
  Proof. reflexivity. Qed.

  Example foliance_ambiguous_a_solution_check :
    k_folianceb
      (regex_foliance_nfa [true; false] Bool.eqb foliance_ambiguous_a)
      2
      [true; true] = true.
  Proof. reflexivity. Qed.

  Example foliance_ambiguous_a_k_da_solver :
    solve_k_da foliance_ambiguous_a_nfa 2 = Some [true].
  Proof. reflexivity. Qed.

  Example foliance_ambiguous_a_k_dra_solver :
    solve_k_dra foliance_ambiguous_a_nfa 1 = Some [true].
  Proof. reflexivity. Qed.

  Example foliance_ambiguous_a_not_2_co_empty :
    ~ k_co_empty foliance_ambiguous_a_nfa 2.
  Proof.
    eapply k_foliance_not_k_co_empty with (w := [true; true]).
    apply k_folianceb_correct.
    reflexivity.
  Qed.

  Definition foliance_reject_false : regex bool :=
    Atom false.

  Definition foliance_reject_false_nfa : @finite_nfa bool :=
    regex_foliance_nfa [true; false] Bool.eqb foliance_reject_false.

  Example foliance_pref_independent_reject_check :
    k_foliance_pref_againstb
      foliance_ambiguous_a_nfa
      foliance_reject_false_nfa
      2
      [true] = true.
  Proof. reflexivity. Qed.

  Example foliance_pref_independent_reject_solver :
    solve_regex_foliance_pref_against
      [true; false]
      Bool.eqb
      foliance_ambiguous_a
      foliance_reject_false
      2 = Some [true].
  Proof. reflexivity. Qed.

  (** One-state NFA: duplicate edges on the same symbol return to the same
      state, so [dra_word] can actually reach 2. *)

  Definition foliance_unit_eqb (_ _ : unit) : bool := true.

  Lemma foliance_unit_eqb_sound :
    forall x y, foliance_unit_eqb x y = true -> x = y.
  Proof.
    intros [] [] _. reflexivity.
  Qed.

  Lemma foliance_unit_eqb_complete :
    forall x y, x = y -> foliance_unit_eqb x y = true.
  Proof.
    intros [] [] _. reflexivity.
  Qed.

  Definition foliance_duplicated_loop_nfa : @finite_nfa bool :=
    {|
      fnfa_base :=
        {|
          nfa_state := unit;
          nfa_start := [tt];
          nfa_final := fun _ => true;
          nfa_step := fun (_ : unit) (a : bool) =>
            if a then [tt; tt] else []
        |};
      fnfa_states := [tt];
      fnfa_alphabet := [true];
      fnfa_state_eqb := foliance_unit_eqb;
      fnfa_state_eqb_sound := foliance_unit_eqb_sound;
      fnfa_state_eqb_complete := foliance_unit_eqb_complete
    |}.

  Example foliance_duplicated_loop_dra_word :
    dra_word foliance_duplicated_loop_nfa [true] = 2.
  Proof. reflexivity. Qed.
End ReachAmbiguityFolianceExamples.
