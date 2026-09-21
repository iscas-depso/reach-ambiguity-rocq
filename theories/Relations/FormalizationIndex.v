From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Automata Require Import EpsilonNFA AmbiguityCount.
From PositionAutomata.Regex Require Import RegexSSS SigmaBlankIdentity.
From PositionAutomata.Regex Require Import FolianceDecision.
From PositionAutomata.Grammar Require Import RightLinearGrammar.
From PositionAutomata.Relations Require Import AmbiguityLR AmbiguityExamples.

(** Paper-facing index for the reach-ambiguity formalization.

    This file collects paper-facing aliases and thin references to the Rocq
    objects that realize the definitions, lemmas, theorems, examples, and
    decision-problem interfaces used in the paper. *)

Section FormalizationIndex.
  Context {A : Type}.

  (** Definition 4: epsilon-simple computations and derivations. *)

  (* Definition 4 I *)
  Definition formalization_trace_epsilon_simple := @epsilon_simpleb A.

  (* Definition 4 I *)
  Definition formalization_trace_maximal_epsilon_simple :=
    @maximal_epsilon_simpleb A.

  (* Definition 4 II *)
  Definition formalization_derivation_epsilon_simple :=
    @cfg_derivation_epsilon_simple A.

  (* Definition 4 II *)
  Definition formalization_derivation_maximal_epsilon_simple :=
    @cfg_derivation_maximal_epsilon_simple_in A.

  (** Definition 5: (reach-)ambiguities and leaves in NFAs. *)

  (* Definition 5 I.i *)
  Definition formalization_da := @enfa_da_word A.

  (* Definition 5 I.ii *)
  Definition formalization_dra := @enfa_dra_at A.

  (* Definition 5 I.iii *)
  Definition formalization_leaf := @enfa_leaf_word A.

  (* Definition 5 II.i *)
  Definition formalization_da_prime := @enfa_da_prime_word A.

  (* Definition 5 II.ii *)
  Definition formalization_dra_prime := @enfa_dra_prime_at A.

  Definition formalization_maximal_condition_removed :=
    @enfa_dra_prime_at_traces_fiber_maximal A.

  (* Definition 5 II.iii *)
  Definition formalization_leaf_prime := @enfa_leaf_prime_word A.

  Definition formalization_da_prime_degree := @enfa_da_prime_degree A.

  Definition formalization_dra_prime_degree := @enfa_dra_prime_degree A.

  Definition formalization_leaf_prime_degree := @enfa_leaf_prime_degree A.

  Definition formalization_degree_value := enfa_degree_value.

  Definition formalization_da_prime_extended_degree :=
    @enfa_da_prime_extended_degree A.

  Definition formalization_dra_prime_extended_degree :=
    @enfa_dra_prime_extended_degree A.

  Definition formalization_leaf_prime_extended_degree :=
    @enfa_leaf_prime_extended_degree A.

  Definition formalization_da_prime_extended_degree_exists_unique :=
    conj (@enfa_da_prime_extended_degree_exists A)
      (@enfa_da_prime_extended_degree_unique A).

  Definition formalization_dra_prime_extended_degree_exists_unique :=
    conj (@enfa_dra_prime_extended_degree_exists A)
      (@enfa_dra_prime_extended_degree_unique A).

  Definition formalization_leaf_prime_extended_degree_exists_unique :=
    conj (@enfa_leaf_prime_extended_degree_exists A)
      (@enfa_leaf_prime_extended_degree_unique A).

  Definition formalization_ufa_extended_degree_characterization :=
    @enfa_ufa_iff_extended_degree_le_one A.

  Definition formalization_reachufa_extended_degree_characterization :=
    @enfa_reachufa_iff_extended_degree_le_one A.

  Definition formalization_leafufa_extended_degree_characterization :=
    @enfa_leafufa_iff_extended_degree_le_one A.

  Definition formalization_ufa_degree_characterization :=
    @enfa_ufa_iff_da_prime_degree_le_one A.

  Definition formalization_reachufa_degree_characterization :=
    @enfa_reachufa_iff_dra_prime_degree_le_one A.

  Definition formalization_leafufa_degree_characterization :=
    @enfa_leafufa_iff_leaf_prime_degree_le_one A.

  Definition formalization_count := @enfa_count A.

  Definition formalization_count_da_prime_correct :=
    @enfa_count_final_states_eq_da_prime A.

  Definition formalization_count_dra_prime_correct :=
    @enfa_count_singleton_eq_dra_prime A.

  Definition formalization_count_leaf_prime_correct :=
    @enfa_count_all_states_eq_leaf_prime A.

  Definition formalization_count_correct := @enfa_count_correct A.

  Definition formalization_finite_da_prime_degree_attained :=
    @enfa_finite_da_prime_degree_attained_within_a_length_bound A.

  Definition formalization_finite_dra_prime_degree_attained :=
    @enfa_finite_dra_prime_degree_attained_within_a_length_bound A.

  Definition formalization_finite_dra_prime_at_degree_attained :=
    @enfa_finite_dra_prime_at_degree_attained_within_a_length_bound A.

  Definition formalization_finite_leaf_prime_degree_attained :=
    @enfa_finite_leaf_prime_degree_attained_within_a_length_bound A.

  Definition formalization_foliance_prefix_witness :=
    @foliance_msss_foliance_eta_prefix_witness A.

  Definition formalization_foliance_not_k_co_empty :=
    @foliance_msss_foliance_not_k_co_empty A.

  Definition formalization_foliance_pref_excludes_factor :=
    @foliance_prefix_language_rejection_excludes_factor A.

  (** Lemma 1: original vs. prime in epsilon-free NFAs. *)

  (* Lemma 1: da *)
  Definition formalization_da_original_coincides_prime := @reach_ambiguity_da A.

  (* Lemma 1: dra *)
  Definition formalization_dra_original_coincides_prime :=
    @reach_ambiguity_dra A.

  (* Lemma 1: Leaf *)
  Definition formalization_leaf_original_coincides_prime :=
    @reach_ambiguity_leaf A.

  (** Definition 6: UFAs, ReachUFAs, SUFAs, stUFAs, and LeafUFAs. *)

  (* Definition 6 I *)
  Definition formalization_UFA := @enfa_UFA A.

  (* Definition 6 II *)
  Definition formalization_ReachUFA := @enfa_ReachUFA A.

  (* Definition 6 II *)
  Definition formalization_SUFA := @enfa_SUFA A.

  Definition formalization_stUFA := @enfa_stUFA A.

  Definition formalization_stUFA_single_start_implies_reachufa :=
    @enfa_stUFA_single_start_implies_reachufa A.

  Definition formalization_epsilon_free_single_start_stufa_implies_sufa :=
    @enfa_epsilon_free_single_start_stufa_implies_sufa A.

  (* Definition 6 III *)
  Definition formalization_LeafUFA := @enfa_LeafUFA A.

  Definition formalization_biUFA := @enfa_BiUFA A.

  Definition formalization_biUFA_unique_accepting :=
    @enfa_BiUFA_unique_accepting A.

  Definition formalization_biUFA_unique_rejecting :=
    @enfa_BiUFA_unique_rejecting A.

  Definition formalization_leafufa_iff_biufa :=
    @reach_ambiguity_leafufa_iff_biufa A.

  Definition formalization_kleene_h_regex := @h_regex A.

  Definition formalization_kleene_h_regex_idempotence :=
    @h_regex_idempotence A.

  Definition formalization_regex_universal_sigma_blank_step :=
    @regex_universal_sigma_blank_step A.

  Definition formalization_h_regex_universal_sigma_blank_equiv :=
    @h_regex_universal_sigma_blank_equiv A.

  (** Example 2: [(a+b)^* a (a+b)^n].

      These are paper-order aliases for the executable Section 4 example
      family proved in [AmbiguityExamples].  Runtime vulnerability in concrete
      regex engines remains outside the current semantic/cost model. *)

  Definition formalization_suffix_ambiguity_family_regex := suffix_ambiguity_family_regex.

  Definition formalization_suffix_ambiguity_family_m := suffix_ambiguity_family_m.

  Definition formalization_suffix_ambiguity_family_attack_word := suffix_ambiguity_family_attack_word.

  Definition formalization_suffix_ambiguity_family_m_wf := suffix_ambiguity_family_m_wf.

  Definition formalization_suffix_ambiguity_family_m_reachufa :=
    suffix_ambiguity_family_m_reachufa.

  Definition formalization_suffix_ambiguity_family_m_ufa :=
    suffix_ambiguity_family_m_ufa.

  Definition formalization_suffix_ambiguity_family_gamma_terminal_lr1 :=
    suffix_ambiguity_family_gamma_terminal_lr1.

  Definition formalization_suffix_ambiguity_family_da_prime_attack_count :=
    suffix_ambiguity_family_da_prime_attack_count.

  Definition formalization_suffix_ambiguity_family_leaf_prime_attack_count :=
    suffix_ambiguity_family_leaf_prime_attack_count.

  Definition formalization_suffix_ambiguity_family_not_sufa :=
    suffix_ambiguity_family_m_not_sufa.

  Definition formalization_suffix_ambiguity_family_not_leafufa :=
    suffix_ambiguity_family_m_not_leafufa.

  Definition formalization_suffix_ambiguity_family_regex_not_strong_leaf_unambiguous :=
    suffix_ambiguity_family_regex_not_strong_leaf_unambiguous.

  Definition formalization_suffix_ambiguity_family_da_prime_attack_count_0 :=
    suffix_ambiguity_family_da_prime_attack_count_0.

  Definition formalization_suffix_ambiguity_family_da_prime_attack_count_1 :=
    suffix_ambiguity_family_da_prime_attack_count_1.

  Definition formalization_suffix_ambiguity_family_da_prime_attack_count_2 :=
    suffix_ambiguity_family_da_prime_attack_count_2.

  Definition formalization_suffix_ambiguity_family_da_prime_attack_count_3 :=
    suffix_ambiguity_family_da_prime_attack_count_3.

  Definition formalization_suffix_ambiguity_family_leaf_prime_attack_count_0 :=
    suffix_ambiguity_family_leaf_prime_attack_count_0.

  Definition formalization_suffix_ambiguity_family_leaf_prime_attack_count_1 :=
    suffix_ambiguity_family_leaf_prime_attack_count_1.

  Definition formalization_suffix_ambiguity_family_leaf_prime_attack_count_2 :=
    suffix_ambiguity_family_leaf_prime_attack_count_2.

  Definition formalization_suffix_ambiguity_family_leaf_prime_attack_count_3 :=
    suffix_ambiguity_family_leaf_prime_attack_count_3.

  (** Definition 7: weak and strong reach/leaf-unambiguity in regexes. *)

  (* Definition 7 I *)
  Definition formalization_regex_weak_reach_unambiguous :=
    @regex_weak_reach_unambiguous A.

  (* Definition 7 II *)
  Definition formalization_regex_strong_reach_unambiguous :=
    @regex_strong_reach_unambiguous A.

  (* Definition 7 III *)
  Definition formalization_regex_weak_leaf_unambiguous :=
    @regex_weak_leaf_unambiguous A.

  (* Definition 7 IV *)
  Definition formalization_regex_strong_leaf_unambiguous :=
    @regex_strong_leaf_unambiguous A.

  (* Definition 7: definitional characterizations *)
  Definition formalization_regex_characterizations :=
    @reach_ambiguity_regex_characterizations A.

  Definition formalization_regex_weak_leaf_iff_weak_deterministic :=
    @reach_ambiguity_regex_weak_leaf_iff_weak_deterministic A.

  (** Definition 8: (reach-)ambiguities and leaves in CFGs. *)

  (* Definition 8 I.i *)
  Definition formalization_cfg_da :=
    @reach_ambiguity_cfg_da A.

  (* Definition 8 I.ii *)
  Definition formalization_cfg_dra :=
    @reach_ambiguity_cfg_dra A.

  (* Definition 8 I.iii *)
  Definition formalization_cfg_leaf :=
    @reach_ambiguity_cfg_leaf A.

  (* Definition 8 II.i *)
  Definition formalization_cfg_da_prime :=
    @reach_ambiguity_cfg_da_prime A.

  (* Definition 8 II.ii *)
  Definition formalization_cfg_dra_prime :=
    @reach_ambiguity_cfg_dra_prime A.

  (* Definition 8 II.iii *)
  Definition formalization_cfg_leaf_prime :=
    @reach_ambiguity_cfg_leaf_prime A.

  (* Definition 8 I.i: finite-cardinality reading. *)
  Definition formalization_cfg_da_cardinality :=
    @reach_ambiguity_cfg_da_cardinality A.

  (* Definition 8 I.ii: finite-cardinality reading. *)
  Definition formalization_cfg_dra_cardinality :=
    @reach_ambiguity_cfg_dra_cardinality A.

  (* Definition 8 I.iii: finite-cardinality reading. *)
  Definition formalization_cfg_leaf_cardinality :=
    @reach_ambiguity_cfg_leaf_cardinality A.

  (* Definition 8 II.i: finite-cardinality reading. *)
  Definition formalization_cfg_da_prime_cardinality :=
    @reach_ambiguity_cfg_da_prime_cardinality A.

  (* Definition 8 II.ii: finite-cardinality reading. *)
  Definition formalization_cfg_dra_prime_cardinality :=
    @reach_ambiguity_cfg_dra_prime_cardinality A.

  (* Definition 8 II.iii: finite-cardinality reading. *)
  Definition formalization_cfg_leaf_prime_cardinality :=
    @reach_ambiguity_cfg_leaf_prime_cardinality A.

  (* Definition 8 I.i: extended-cardinality reading. *)
  Definition formalization_cfg_da_extended_cardinality :=
    @reach_ambiguity_cfg_da_extended_cardinality A.

  (* Definition 8 I.ii: extended-cardinality reading. *)
  Definition formalization_cfg_dra_extended_cardinality :=
    @reach_ambiguity_cfg_dra_extended_cardinality A.

  (* Definition 8 I.iii: extended-cardinality reading. *)
  Definition formalization_cfg_leaf_extended_cardinality :=
    @reach_ambiguity_cfg_leaf_extended_cardinality A.

  (* Definition 8 II.i: extended-cardinality reading. *)
  Definition formalization_cfg_da_prime_extended_cardinality :=
    @reach_ambiguity_cfg_da_prime_extended_cardinality A.

  (* Definition 8 II.ii: extended-cardinality reading. *)
  Definition formalization_cfg_dra_prime_extended_cardinality :=
    @reach_ambiguity_cfg_dra_prime_extended_cardinality A.

  (* Definition 8 II.iii: extended-cardinality reading. *)
  Definition formalization_cfg_leaf_prime_extended_cardinality :=
    @reach_ambiguity_cfg_leaf_prime_extended_cardinality A.

  (* Definition 8 example: a self-loop CFG gives an infinite reach fiber,
     motivating the extended-cardinality reading used below. *)
  Definition formalization_support_cfg_self_loop_dra_fiber_infinite :=
    @reach_ambiguity_cfg_self_loop_dra_fiber_infinite A.

  Definition formalization_support_cfg_self_loop_dra_fiber_not_finite :=
    @reach_ambiguity_cfg_self_loop_dra_fiber_not_finite A.

  (** Definition 9: reach-, leaf-, and ordinary unambiguous grammars. *)

  (* Definition 9 I *)
  Definition formalization_cfg_unambiguous :=
    @reach_ambiguity_cfg_unambiguous A.

  (* Definition 9 II *)
  Definition formalization_cfg_reach_unambiguous :=
    @reach_ambiguity_cfg_reach_unambiguous A.

  (* Definition 9 III *)
  Definition formalization_cfg_leaf_unambiguous :=
    @reach_ambiguity_cfg_leaf_unambiguous A.

  (* Definition 9 is organized through uniqueness predicates, the
     finite-cardinality numeric layer, finite-supremum predicates, and extended
     cardinality/supremum predicates. *)
  Definition formalization_cfg_da_prime_finite_cardinality :=
    @cfg_da_prime_finite_cardinality A.

  Definition formalization_cfg_dra_prime_finite_cardinality :=
    @cfg_dra_prime_finite_cardinality A.

  Definition formalization_cfg_leaf_prime_finite_cardinality :=
    @cfg_leaf_prime_finite_cardinality A.

  Definition formalization_cfg_da_prime_degree_le :=
    @reach_ambiguity_cfg_da_prime_degree_le A.

  Definition formalization_cfg_dra_prime_degree_le :=
    @reach_ambiguity_cfg_dra_prime_degree_le A.

  Definition formalization_cfg_leaf_prime_degree_le :=
    @reach_ambiguity_cfg_leaf_prime_degree_le A.

  Definition formalization_cfg_da_prime_degree :=
    @reach_ambiguity_cfg_da_prime_degree A.

  Definition formalization_cfg_dra_prime_degree :=
    @reach_ambiguity_cfg_dra_prime_degree A.

  Definition formalization_cfg_leaf_prime_degree :=
    @reach_ambiguity_cfg_leaf_prime_degree A.

  Definition formalization_cfg_da_prime_extended_degree_le :=
    @reach_ambiguity_cfg_da_prime_extended_degree_le A.

  Definition formalization_cfg_dra_prime_extended_degree_le :=
    @reach_ambiguity_cfg_dra_prime_extended_degree_le A.

  Definition formalization_cfg_leaf_prime_extended_degree_le :=
    @reach_ambiguity_cfg_leaf_prime_extended_degree_le A.

  Definition formalization_cfg_da_prime_extended_degree :=
    @reach_ambiguity_cfg_da_prime_extended_degree A.

  Definition formalization_cfg_dra_prime_extended_degree :=
    @reach_ambiguity_cfg_dra_prime_extended_degree A.

  Definition formalization_cfg_leaf_prime_extended_degree :=
    @reach_ambiguity_cfg_leaf_prime_extended_degree A.

  Definition formalization_cfg_unambiguous_iff_da_prime_degree_le_one_under_finite_cardinality :=
    @reach_ambiguity_cfg_unambiguous_iff_da_prime_degree_le_one_under_finite_cardinality A.

  Definition formalization_cfg_reach_unambiguous_iff_dra_prime_degree_le_one_under_finite_cardinality :=
    @reach_ambiguity_cfg_reach_unambiguous_iff_dra_prime_degree_le_one_under_finite_cardinality A.

  Definition formalization_cfg_leaf_unambiguous_iff_leaf_prime_degree_le_one_under_finite_cardinality :=
    @reach_ambiguity_cfg_leaf_unambiguous_iff_leaf_prime_degree_le_one_under_finite_cardinality A.

  (** Theorem 1: leaf-unambiguity and determinism. *)

  (* Theorem 1 I *)
  Definition formalization_deterministic_implies_leafufa :=
    @reach_ambiguity_epsilon_free_deterministic_leafufa A.

  (* Theorem 1 I *)
  Definition formalization_leafufa_implies_deterministic_trim :=
    @reach_ambiguity_epsilon_free_leafufa_deterministic_trim A.

  (* Theorem 1 I *)
  Definition formalization_leafufa_iff_deterministic_trim_single_start :=
    @reach_ambiguity_epsilon_free_leafufa_deterministic_trim_single_start A.

  Definition formalization_leafufa_iff_accessibly_deterministic :=
    @reach_ambiguity_epsilon_free_leafufa_iff_accessibly_deterministic A.

  (* Straightforward DFA implications and non-converses. *)
  Definition formalization_dfa_conditions := @enfa_DFA_conditions A.

  Definition formalization_dfa_implies_ufa_reachufa_leafufa :=
    @reach_ambiguity_dfa_conditions_implies_ufa_reachufa_leafufa A.

  Definition formalization_not_conversely :=
    dfa_class_separation_not_conversely.

  (* Theorem 1 II: refined/decomposed epsilon-closure branching direction. *)
  Definition formalization_leafufa_implies_epsilon_closure_branching :=
    @reach_ambiguity_leafufa_implies_epsilon_closure_branching A.

  (* Theorem 1 III: refined/decomposed epsilon-closure branching iff. *)
  Definition formalization_epsilon_closure_branching_iff :=
    @reach_ambiguity_epsilon_closure_branching_iff A.

  Definition formalization_leafufa_iff_maximal_trace_unique :=
    @reach_ambiguity_leafufa_iff_maximal_trace_unique A.

  (* Theorem 1 II/III: maximal epsilon-simple symbol-extension determinism. *)
  Definition formalization_support_leafufa_maximal_epsilon_removal_deterministic :=
    @reach_ambiguity_leafufa_maximal_epsilon_removal_deterministic A.

  (** Theorem 2: unambiguity and reach-unambiguity. *)

  (* Theorem 2: decomposed wrapper *)
  Definition formalization_unambiguity_and_reach_unambiguity :=
    @reach_ambiguity_unambiguity_and_reach_unambiguity A.

  (* Theorem 2 supporting clauses. *)
  Definition formalization_support_accepting_maximal_da_bounded_by_leaf :=
    @reach_ambiguity_enfa_accepting_maximal_da_bounded_by_leaf A.

  Definition formalization_support_accepting_maximal_extension_injective :=
    @reach_ambiguity_enfa_accepting_maximal_extension_injective A.

  Definition formalization_leafufa_implies_ufa :=
    @reach_ambiguity_leafufa_implies_ufa A.

  Definition formalization_leafufa_implies_reachufa_wf_single_start :=
    @reach_ambiguity_leafufa_implies_reachufa A.

  (* Theorem 2 LeafUFA-to-UFA alias. *)
  Definition formalization_leafufa_implies_ufa_under_accepting_maximal_da_leaf_bound :=
    @reach_ambiguity_leafufa_implies_ufa_under_accepting_maximal_da_leaf_bound A.

  (* Theorem 2 accepting-maximal extension formulation. *)
  Definition formalization_support_leafufa_implies_ufa_under_extension_injective :=
    @reach_ambiguity_leafufa_implies_ufa_under_started_traces_nodup_and_accepting_maximal_extension_injective A.

  Definition formalization_trim_extendable_ufa_implies_reachufa :=
    @reach_ambiguity_trim_extendable_ufa_implies_reachufa A.

  Definition formalization_epsilon_free_trim_extendable_ufa_implies_reachufa :=
    @reach_ambiguity_epsilon_free_trim_extendable_ufa_implies_reachufa A.

  Definition formalization_epsilon_free_trim_ufa_implies_reachufa :=
    @reach_ambiguity_epsilon_free_trim_ufa_implies_reachufa A.

  Definition formalization_epsilon_free_trim_ufa_implies_stufa :=
    @reach_ambiguity_epsilon_free_trim_ufa_implies_stufa A.

  Definition formalization_trim_epsilon_ufa_not_reachufa :=
    trim_epsilon_ufa_does_not_imply_reachufa.

  Definition formalization_epsilon_free_trim_ufa_implies_sufa :=
    @reach_ambiguity_epsilon_free_trim_ufa_implies_sufa A.

  Definition formalization_reachufa_single_final_list_implies_ufa :=
    @reach_ambiguity_reachufa_single_final_list_implies_ufa A.

  Definition formalization_reachufa_unique_terminating_state_implies_ufa :=
    @reach_ambiguity_reachufa_unique_terminating_state_implies_ufa A.

  (** Theorem 3: leaves and the sum of reach-ambiguities. *)

  (* Theorem 3 I *)
  Definition formalization_leaf_sum_dra :=
    @reach_ambiguity_epsilon_free_leaf_sum_dra A.

  (* Theorem 3 II *)
  Definition formalization_prime_leaf_le_sum_dra :=
    @reach_ambiguity_prime_leaf_le_sum_dra A.

  (** Lemma 2: ReachUFAs are at most linearly leaf-ambiguous. *)

  (* Lemma 2 *)
  Definition formalization_reachufa_linear_leaf_bound :=
    @reach_ambiguity_reachufa_leaf_bound A.

  (** Theorem 4: NFA to Grammar. *)

  (* Theorem 4: Gamma construction *)
  Definition formalization_gamma_construction := @gamma_grammar_from A.

  (* Theorem 4: language equivalence. *)
  Definition formalization_gamma_language_equiv :=
    @reach_ambiguity_gamma_support_language_equiv A.

  (* Theorem 4 deterministic construction cost is recorded by the paper
     statement; the Rocq entry above exposes the constructive Gamma map and
     language-equivalence theorem. *)

  (** Lemma 3: Gamma is ambiguity-preserving. *)

  Definition formalization_support_gamma_accepting_maximal_reflects :=
    @reach_ambiguity_gamma_accepting_maximal_reflects A.

  (* Lemma 3: prime accepting trace/derivation bridge *)
  Definition formalization_gamma_prime_accepting_derivation_of_trace :=
    @reach_ambiguity_gamma_support_prime_accepting_derivation_of_trace A.

  Definition formalization_gamma_prime_accepting_trace_of_derivation :=
    @reach_ambiguity_gamma_support_prime_accepting_trace_of_derivation A.

  (* Lemma 3: prime reach trace/derivation bridge *)
  Definition formalization_gamma_prime_reach_derivation_of_trace :=
    @reach_ambiguity_gamma_support_prime_reach_derivation_of_trace A.

  Definition formalization_gamma_prime_reach_trace_of_derivation :=
    @reach_ambiguity_gamma_support_prime_reach_trace_of_derivation A.

  (* Lemma 3: prime leaf trace/derivation bridge *)
  Definition formalization_gamma_prime_leaf_derivation_of_trace :=
    @reach_ambiguity_gamma_support_prime_leaf_derivation_of_trace A.

  Definition formalization_gamma_prime_leaf_trace_of_derivation :=
    @reach_ambiguity_gamma_support_prime_leaf_trace_of_derivation A.

  (* Lemma 3: decomposed unambiguity preservation support *)
  Definition formalization_gamma_ufa_rlg_unambiguous_iff :=
    @reach_ambiguity_gamma_support_ufa_rlg_unambiguous_iff A.

  Definition formalization_gamma_reachufa_rlg_reach_unambiguous_iff :=
    @reach_ambiguity_gamma_support_reachufa_rlg_reach_unambiguous_iff A.

  Definition formalization_gamma_leafufa_rlg_leaf_unambiguous_iff :=
    @reach_ambiguity_gamma_support_leafufa_rlg_leaf_unambiguous_iff A.

  (* Lemma 3: Gamma numeric preservation, specialized to the current
     Gamma/RLG model.  The DA' accepting-maximal branch discharges Gamma
     accepting-maximal reflection internally. *)
  Definition formalization_gamma_da_prime_count_eq_under_accepting_maximal_reflection :=
    @reach_ambiguity_gamma_da_prime_count_eq_with_alphabet_nodup A.

  Definition formalization_gamma_da_prime_count_eq :=
    @reach_ambiguity_gamma_da_prime_count_eq_with_alphabet_nodup A.

  Definition formalization_gamma_dra_prime_count_eq :=
    @reach_ambiguity_gamma_dra_prime_count_eq_with_alphabet_nodup A.

  Definition formalization_gamma_leaf_prime_count_eq :=
    @reach_ambiguity_gamma_leaf_prime_count_eq_with_alphabet_nodup A.

  Definition formalization_gamma_prime_counts_eq_under_accepting_maximal_reflection :=
    @reach_ambiguity_gamma_prime_counts_eq_with_alphabet_nodup A.

  Definition formalization_gamma_prime_counts_eq :=
    @reach_ambiguity_gamma_prime_counts_eq_with_alphabet_nodup A.

  (* Lemma 3 aliases: direct da'/dra'/Leaf' equalities for Gamma's
     right-linear grammar representation, with the ENFA/RLG enumeration
     conditions provided by finite well-formedness, a single start state, and
     NoDup (fenfa_alphabet m).  Gamma accepting-maximal reflection is provided
     by [reach_ambiguity_gamma_accepting_maximal_reflects], and CFG finite and
     extended-cardinality readings are exposed by the Definition 8/9 aliases
     above. *)

  (** Theorem 5: (reach-)unambiguity and LR(1)-ness. *)

  (* Primary paper-order reading: Definition 10's nondeterministic LR machine
     is interpreted with terminal-word reduce-conflict semantics, giving the
     Theorem 5 bridge used by the paper statement. *)
  Definition formalization_terminal_semantic_bridge :=
    @reach_ambiguity_terminal_semantic_bridge A.

  Definition formalization_terminal_lr1_iff_gamma_unambiguous_reach :=
    @reach_ambiguity_terminal_lr1_iff_gamma_unambiguous_reach A.

  (* Theorem 5 I. *)
  Definition formalization_terminal_lr1_iff_ufa_reachufa :=
    @reach_ambiguity_terminal_lr1_iff_ufa_reachufa_wf_single_start A.

  (* Theorem 5 I, shorter paper-facing alias. *)
  Definition formalization_lr1_iff_ufa_reachufa :=
    formalization_terminal_lr1_iff_ufa_reachufa.

  (* Theorem 5 II, LeafUFA sufficient direction. *)
  Definition formalization_leafufa_sufficient_terminal_lr1 :=
    @reach_ambiguity_leafufa_sufficient_terminal_lr1_wf_single_start A.

  (* Theorem 5 II, shorter paper-facing alias. *)
  Definition formalization_leafufa_sufficient_lr1 :=
    formalization_leafufa_sufficient_terminal_lr1.

  (* Canonical item-set formulations for Theorem 5. *)
  Definition formalization_support_canonical_semantic_bridge_under_conflict_reflection :=
    @reach_ambiguity_lr1_support_canonical_semantic_bridge_under_conflict_reflection A.

  Definition formalization_support_final_no_epsilon_successors :=
    @reach_ambiguity_enfa_final_no_epsilon_successors A.

  Definition formalization_support_final_no_epsilon_successors_maximal :=
    @reach_ambiguity_enfa_final_no_epsilon_successors_maximal A.

  Definition formalization_support_prime_final_conflict_reflection :=
    @gamma_prime_final_conflict_reflection A.

  Definition formalization_support_canonical_semantic_bridge_under_prime_final_reflection :=
    @reach_ambiguity_lr1_support_canonical_semantic_bridge_under_prime_final_reflection A.

  Definition formalization_support_canonical_lr1_iff_gamma_unambiguous_reach_under_conflict_reflection :=
    @reach_ambiguity_lr1_support_canonical_lr1_iff_gamma_unambiguous_reach_under_conflict_reflection A.

  Definition formalization_support_canonical_lr1_iff_ufa_reachufa_under_conflict_reflection :=
    @reach_ambiguity_lr1_support_canonical_lr1_iff_ufa_reachufa_under_conflict_reflection A.

  Definition formalization_support_canonical_lr1_iff_ufa_reachufa_under_prime_final_reflection :=
    @reach_ambiguity_lr1_support_canonical_lr1_iff_ufa_reachufa_under_prime_final_reflection A.

  Definition formalization_support_leafufa_sufficient_canonical_lr1_under_conflict_reflection :=
    @reach_ambiguity_lr1_support_leafufa_sufficient_canonical_lr1_under_conflict_reflection A.

  Definition formalization_support_leafufa_sufficient_canonical_lr1_under_prime_final_reflection :=
    @reach_ambiguity_lr1_support_leafufa_sufficient_canonical_lr1_under_prime_final_reflection A.

  Definition formalization_support_canonical_lr1_iff_ufa_reachufa :=
    @reach_ambiguity_lr1_support_canonical_lr1_iff_ufa_reachufa A.

  Definition formalization_support_leafufa_sufficient_canonical_lr1 :=
    @reach_ambiguity_lr1_support_leafufa_sufficient_canonical_lr1 A.

  Definition formalization_support_canonical_lr1_iff_gamma_unambiguous_reach :=
    @reach_ambiguity_lr1_support_canonical_lr1_iff_gamma_unambiguous_reach A.

  (** Definition 10: nondeterministic LR(1) machine. *)

  (* Definition 10 I *)
  Definition formalization_lr1_reduce_items := @lr1_reduce_items A.

  (* Definition 10 I *)
  Definition formalization_lr1_nonreduce_items :=
    @lr1_nonreduce_items A.

  (* Definition 10 I *)
  Definition formalization_lr1_items := @lr1_items A.

  (* Definition 10 II *)
  Definition formalization_lr1_reduce_transitions :=
    @lr1_reduce_transitions A.

  (* Definition 10 II *)
  Definition formalization_lr1_shift_transitions :=
    @lr1_shift_transitions A.

  (* Definition 10 II *)
  Definition formalization_lr1_step := @lr1_step A.

  (* Definition 10 III *)
  Definition formalization_lr1_machine_of_enfa :=
    @lr1_machine_of_enfa A.

  (* Definition 10: structural characterization *)
  Definition formalization_lr1_machine_characterization :=
    @reach_ambiguity_lr1_machine_characterization A.

  (* Definition 10: expanded membership characterization *)
  Definition formalization_lr1_machine_full_characterization :=
    @reach_ambiguity_lr1_machine_full_characterization A.

  (** Theorem 6: leaves and LR(1)-conflicts. *)

  (* Theorem 6 *)
  Definition formalization_conflicts_le_leaves :=
    @reach_ambiguity_conflicts_le_leaves A.

  (* Theorem 6 specialization to Definition 10 machines *)
  Definition formalization_conflicts_le_leaves_of_enfa :=
    @reach_ambiguity_conflicts_le_leaves_of_enfa A.

  (* Theorem 6 corollary. *)
  Definition formalization_leaf_one_conflict_free_of_enfa :=
    @reach_ambiguity_leaf_one_conflict_free_of_enfa A.

  (** Lemma 4: facts about M_LR(u). *)

  (* Lemma 4 I *)
  Definition formalization_lr1_leaf_preservation :=
    @reach_ambiguity_lr1_leaf_preservation A.

  (* Lemma 4 II: deterministic O(|E|) construction-cost clause. *)

  (** Decision problems and complexity results. *)

  (* Problem 1: U, ReachU, and LeafU. *)
  Definition formalization_unambiguity_decision_problem := @unambiguity_decision_problem A.

  Definition formalization_reach_unambiguity_decision_problem := @reach_unambiguity_decision_problem A.

  Definition formalization_leaf_unambiguity_decision_problem := @leaf_unambiguity_decision_problem A.

  (* Theorem 7: NL-hardness of U, ReachU, and epsilon-LeafU. *)

  (* Problem 2: Kiefer GAP problem used in the Theorem 7 proof. *)

  (* Theorem 8: NL-completeness of U, ReachU, and epsilon-LeafU. *)

  (* Problem 3: SUFA- and LeafUFA-Member. *)
  Definition formalization_structural_unambiguity_membership_problem := @structural_unambiguity_membership_problem A.

  Definition formalization_leaf_unambiguity_membership_problem := @leaf_unambiguity_membership_problem A.

  (* Definition 11: directed forest accessibility used by the L-hardness proof. *)

  (* Theorem 9: L-hardness of SUFA-Member. *)

  (* Theorem 10: SUFA-Member DSPACE(log^2 n / log log n) upper bound. *)

  (* Theorem 11: L-completeness of LeafUFA-Member. *)

  (* Theorem 12: CREW P-RAM parallel membership upper bound. *)

End FormalizationIndex.
