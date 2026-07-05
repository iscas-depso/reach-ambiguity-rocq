From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Automata Require Import EpsilonNFA.
From PositionAutomata.Regex Require Import RegexSSS SigmaBlankIdentity.
From PositionAutomata.Grammar Require Import RightLinearGrammar.
From PositionAutomata.Section4 Require Import Section4LR Section4Examples.

(** Paper-order index for Section 4.

    This file collects paper-facing aliases and thin references to the Rocq
    objects that realize the definitions, lemmas, theorems, examples, and
    decision-problem interfaces used in the Section 4 development. *)

Section Section4PaperOrder.
  Context {A : Type}.

  (** Definition 4: epsilon-simple computations and derivations. *)

  (* Definition 4 I *)
  Definition paper_definition4_I_trace_epsilon_simple := @epsilon_simpleb A.

  (* Definition 4 I *)
  Definition paper_definition4_I_trace_maximal_epsilon_simple :=
    @maximal_epsilon_simpleb A.

  (* Definition 4 II *)
  Definition paper_definition4_II_derivation_epsilon_simple :=
    @cfg_derivation_epsilon_simple A.

  (* Definition 4 II *)
  Definition paper_definition4_II_derivation_maximal_epsilon_simple :=
    @cfg_derivation_maximal_epsilon_simple_in A.

  (** Definition 5: (reach-)ambiguities and leaves in NFAs. *)

  (* Definition 5 I.i *)
  Definition paper_definition5_I_i_da := @enfa_da_word A.

  (* Definition 5 I.ii *)
  Definition paper_definition5_I_ii_dra := @enfa_dra_at A.

  (* Definition 5 I.iii *)
  Definition paper_definition5_I_iii_leaf := @enfa_leaf_word A.

  (* Definition 5 II.i *)
  Definition paper_definition5_II_i_da_prime := @enfa_da_prime_word A.

  (* Definition 5 II.ii *)
  Definition paper_definition5_II_ii_dra_prime := @enfa_dra_prime_at A.

  (* Definition 5 II.iii *)
  Definition paper_definition5_II_iii_leaf_prime := @enfa_leaf_prime_word A.

  (** Lemma 1: original vs. prime in epsilon-free NFAs. *)

  (* Lemma 1: da *)
  Definition paper_lemma1_da_original_coincides_prime := @section4_lemma1_da A.

  (* Lemma 1: dra *)
  Definition paper_lemma1_dra_original_coincides_prime :=
    @section4_lemma1_dra A.

  (* Lemma 1: Leaf *)
  Definition paper_lemma1_leaf_original_coincides_prime :=
    @section4_lemma1_leaf A.

  (** Definition 6: UFAs, ReachUFAs, SUFAs, and LeafUFAs. *)

  (* Definition 6 I *)
  Definition paper_definition6_I_UFA := @enfa_UFA A.

  (* Definition 6 II *)
  Definition paper_definition6_II_ReachUFA := @enfa_ReachUFA A.

  (* Definition 6 II *)
  Definition paper_definition6_II_SUFA := @enfa_SUFA A.

  (* Definition 6 III *)
  Definition paper_definition6_III_LeafUFA := @enfa_LeafUFA A.

  Definition paper_definition6_biUFA := @enfa_BiUFA A.

  Definition paper_definition6_biUFA_unique_accepting :=
    @enfa_BiUFA_unique_accepting A.

  Definition paper_definition6_biUFA_unique_rejecting :=
    @enfa_BiUFA_unique_rejecting A.

  Definition paper_definition6_leafufa_iff_biufa :=
    @section4_leafufa_iff_biufa A.

  Definition paper_kleene_h_regex := @h_regex A.

  Definition paper_kleene_h_regex_idempotence :=
    @h_regex_idempotence A.

  Definition paper_kleene_step_assume_universal :=
    @paper_kleene_step_assume_universal A.

  Definition paper_kleene_h_sigma_blank_chain :=
    @paper_kleene_h_sigma_blank_chain A.

  (** Example 2: [(a+b)^* a (a+b)^n].

      These are paper-order aliases for the executable Section 4 example
      family proved in [Section4Examples].  Runtime vulnerability in concrete
      regex engines remains outside the current semantic/cost model. *)

  Definition paper_example2_regex := section4_example2_regex.

  Definition paper_example2_m := section4_example2_m.

  Definition paper_example2_attack_word := section4_example2_attack_word.

  Definition paper_example2_m_wf := section4_example2_m_wf.

  Definition paper_example2_m_reachufa :=
    section4_example2_m_reachufa.

  Definition paper_example2_m_ufa :=
    section4_example2_m_ufa.

  Definition paper_example2_gamma_terminal_lr1 :=
    section4_example2_gamma_terminal_lr1.

  Definition paper_example2_da_prime_attack_count :=
    section4_example2_da_prime_attack_count.

  Definition paper_example2_leaf_prime_attack_count :=
    section4_example2_leaf_prime_attack_count.

  Definition paper_example2_not_sufa_under_definition6 :=
    section4_example2_m_not_sufa_under_definition6.

  Definition paper_example2_not_leafufa :=
    section4_example2_m_not_leafufa.

  Definition paper_example2_regex_not_strong_leaf_unambiguous :=
    section4_example2_regex_not_strong_leaf_unambiguous.

  Definition paper_example2_da_prime_attack_count_0 :=
    section4_example2_da_prime_attack_count_0.

  Definition paper_example2_da_prime_attack_count_1 :=
    section4_example2_da_prime_attack_count_1.

  Definition paper_example2_da_prime_attack_count_2 :=
    section4_example2_da_prime_attack_count_2.

  Definition paper_example2_da_prime_attack_count_3 :=
    section4_example2_da_prime_attack_count_3.

  Definition paper_example2_leaf_prime_attack_count_0 :=
    section4_example2_leaf_prime_attack_count_0.

  Definition paper_example2_leaf_prime_attack_count_1 :=
    section4_example2_leaf_prime_attack_count_1.

  Definition paper_example2_leaf_prime_attack_count_2 :=
    section4_example2_leaf_prime_attack_count_2.

  Definition paper_example2_leaf_prime_attack_count_3 :=
    section4_example2_leaf_prime_attack_count_3.

  (** Definition 7: weak and strong reach/leaf-unambiguity in regexes. *)

  (* Definition 7 I *)
  Definition paper_definition7_I_regex_weak_reach_unambiguous :=
    @regex_weak_reach_unambiguous A.

  (* Definition 7 II *)
  Definition paper_definition7_II_regex_strong_reach_unambiguous :=
    @regex_strong_reach_unambiguous A.

  (* Definition 7 III *)
  Definition paper_definition7_III_regex_weak_leaf_unambiguous :=
    @regex_weak_leaf_unambiguous A.

  (* Definition 7 IV *)
  Definition paper_definition7_IV_regex_strong_leaf_unambiguous :=
    @regex_strong_leaf_unambiguous A.

  (* Definition 7: definitional characterizations *)
  Definition paper_definition7_regex_characterizations :=
    @section4_definition7_regex_characterizations A.

  (** Definition 8: (reach-)ambiguities and leaves in CFGs. *)

  (* Definition 8 I.i *)
  Definition paper_definition8_I_i_cfg_da :=
    @section4_definition8_I_i_cfg_da A.

  (* Definition 8 I.ii *)
  Definition paper_definition8_I_ii_cfg_dra :=
    @section4_definition8_I_ii_cfg_dra A.

  (* Definition 8 I.iii *)
  Definition paper_definition8_I_iii_cfg_leaf :=
    @section4_definition8_I_iii_cfg_leaf A.

  (* Definition 8 II.i *)
  Definition paper_definition8_II_i_cfg_da_prime :=
    @section4_definition8_II_i_cfg_da_prime A.

  (* Definition 8 II.ii *)
  Definition paper_definition8_II_ii_cfg_dra_prime :=
    @section4_definition8_II_ii_cfg_dra_prime A.

  (* Definition 8 II.iii *)
  Definition paper_definition8_II_iii_cfg_leaf_prime :=
    @section4_definition8_II_iii_cfg_leaf_prime A.

  (* Definition 8 I.i: finite-cardinality reading. *)
  Definition paper_definition8_I_i_cfg_da_cardinality :=
    @section4_definition8_I_i_cfg_da_cardinality A.

  (* Definition 8 I.ii: finite-cardinality reading. *)
  Definition paper_definition8_I_ii_cfg_dra_cardinality :=
    @section4_definition8_I_ii_cfg_dra_cardinality A.

  (* Definition 8 I.iii: finite-cardinality reading. *)
  Definition paper_definition8_I_iii_cfg_leaf_cardinality :=
    @section4_definition8_I_iii_cfg_leaf_cardinality A.

  (* Definition 8 II.i: finite-cardinality reading. *)
  Definition paper_definition8_II_i_cfg_da_prime_cardinality :=
    @section4_definition8_II_i_cfg_da_prime_cardinality A.

  (* Definition 8 II.ii: finite-cardinality reading. *)
  Definition paper_definition8_II_ii_cfg_dra_prime_cardinality :=
    @section4_definition8_II_ii_cfg_dra_prime_cardinality A.

  (* Definition 8 II.iii: finite-cardinality reading. *)
  Definition paper_definition8_II_iii_cfg_leaf_prime_cardinality :=
    @section4_definition8_II_iii_cfg_leaf_prime_cardinality A.

  (* Definition 8 I.i: extended-cardinality reading. *)
  Definition paper_definition8_I_i_cfg_da_extended_cardinality :=
    @section4_definition8_I_i_cfg_da_extended_cardinality A.

  (* Definition 8 I.ii: extended-cardinality reading. *)
  Definition paper_definition8_I_ii_cfg_dra_extended_cardinality :=
    @section4_definition8_I_ii_cfg_dra_extended_cardinality A.

  (* Definition 8 I.iii: extended-cardinality reading. *)
  Definition paper_definition8_I_iii_cfg_leaf_extended_cardinality :=
    @section4_definition8_I_iii_cfg_leaf_extended_cardinality A.

  (* Definition 8 II.i: extended-cardinality reading. *)
  Definition paper_definition8_II_i_cfg_da_prime_extended_cardinality :=
    @section4_definition8_II_i_cfg_da_prime_extended_cardinality A.

  (* Definition 8 II.ii: extended-cardinality reading. *)
  Definition paper_definition8_II_ii_cfg_dra_prime_extended_cardinality :=
    @section4_definition8_II_ii_cfg_dra_prime_extended_cardinality A.

  (* Definition 8 II.iii: extended-cardinality reading. *)
  Definition paper_definition8_II_iii_cfg_leaf_prime_extended_cardinality :=
    @section4_definition8_II_iii_cfg_leaf_prime_extended_cardinality A.

  (* Definition 8 example: a self-loop CFG gives an infinite reach fiber,
     motivating the extended-cardinality reading used below. *)
  Definition paper_definition8_support_cfg_self_loop_dra_fiber_infinite :=
    @section4_cfg_self_loop_dra_fiber_infinite A.

  Definition paper_definition8_support_cfg_self_loop_dra_fiber_not_finite :=
    @section4_cfg_self_loop_dra_fiber_not_finite A.

  (** Definition 9: reach-, leaf-, and ordinary unambiguous grammars. *)

  (* Definition 9 I *)
  Definition paper_definition9_I_cfg_unambiguous :=
    @section4_definition9_I_cfg_unambiguous A.

  (* Definition 9 II *)
  Definition paper_definition9_II_cfg_reach_unambiguous :=
    @section4_definition9_II_cfg_reach_unambiguous A.

  (* Definition 9 III *)
  Definition paper_definition9_III_cfg_leaf_unambiguous :=
    @section4_definition9_III_cfg_leaf_unambiguous A.

  (* Definition 9 is organized through uniqueness predicates, the
     finite-cardinality numeric layer, finite-supremum predicates, and extended
     cardinality/supremum predicates. *)
  Definition paper_definition9_I_cfg_da_prime_finite_cardinality :=
    @cfg_da_prime_finite_cardinality A.

  Definition paper_definition9_II_cfg_dra_prime_finite_cardinality :=
    @cfg_dra_prime_finite_cardinality A.

  Definition paper_definition9_III_cfg_leaf_prime_finite_cardinality :=
    @cfg_leaf_prime_finite_cardinality A.

  Definition paper_definition9_I_cfg_da_prime_degree_le :=
    @section4_definition9_I_cfg_da_prime_degree_le A.

  Definition paper_definition9_II_cfg_dra_prime_degree_le :=
    @section4_definition9_II_cfg_dra_prime_degree_le A.

  Definition paper_definition9_III_cfg_leaf_prime_degree_le :=
    @section4_definition9_III_cfg_leaf_prime_degree_le A.

  Definition paper_definition9_I_cfg_da_prime_degree :=
    @section4_definition9_I_cfg_da_prime_degree A.

  Definition paper_definition9_II_cfg_dra_prime_degree :=
    @section4_definition9_II_cfg_dra_prime_degree A.

  Definition paper_definition9_III_cfg_leaf_prime_degree :=
    @section4_definition9_III_cfg_leaf_prime_degree A.

  Definition paper_definition9_I_cfg_da_prime_extended_degree_le :=
    @section4_definition9_I_cfg_da_prime_extended_degree_le A.

  Definition paper_definition9_II_cfg_dra_prime_extended_degree_le :=
    @section4_definition9_II_cfg_dra_prime_extended_degree_le A.

  Definition paper_definition9_III_cfg_leaf_prime_extended_degree_le :=
    @section4_definition9_III_cfg_leaf_prime_extended_degree_le A.

  Definition paper_definition9_I_cfg_da_prime_extended_degree :=
    @section4_definition9_I_cfg_da_prime_extended_degree A.

  Definition paper_definition9_II_cfg_dra_prime_extended_degree :=
    @section4_definition9_II_cfg_dra_prime_extended_degree A.

  Definition paper_definition9_III_cfg_leaf_prime_extended_degree :=
    @section4_definition9_III_cfg_leaf_prime_extended_degree A.

  Definition paper_definition9_I_cfg_unambiguous_iff_da_prime_degree_le_one_under_finite_cardinality :=
    @section4_definition9_I_cfg_unambiguous_iff_da_prime_degree_le_one_under_finite_cardinality A.

  Definition paper_definition9_II_cfg_reach_unambiguous_iff_dra_prime_degree_le_one_under_finite_cardinality :=
    @section4_definition9_II_cfg_reach_unambiguous_iff_dra_prime_degree_le_one_under_finite_cardinality A.

  Definition paper_definition9_III_cfg_leaf_unambiguous_iff_leaf_prime_degree_le_one_under_finite_cardinality :=
    @section4_definition9_III_cfg_leaf_unambiguous_iff_leaf_prime_degree_le_one_under_finite_cardinality A.

  (** Theorem 1: leaf-unambiguity and determinism. *)

  (* Theorem 1 I *)
  Definition paper_theorem1_I_deterministic_implies_leafufa :=
    @section4_theorem1_epsilon_free_deterministic_leafufa A.

  (* Theorem 1 I *)
  Definition paper_theorem1_I_leafufa_implies_deterministic_trim :=
    @section4_theorem1_epsilon_free_leafufa_deterministic_trim A.

  (* Theorem 1 I *)
  Definition paper_theorem1_I_leafufa_iff_deterministic_trim_single_start :=
    @section4_theorem1_epsilon_free_leafufa_deterministic_trim_single_start A.

  (* Theorem 1 II: refined/decomposed epsilon-closure branching direction. *)
  Definition paper_theorem1_II_leafufa_implies_epsilon_closure_branching :=
    @section4_theorem1_leafufa_implies_epsilon_closure_branching A.

  (* Theorem 1 III: refined/decomposed epsilon-closure branching iff. *)
  Definition paper_theorem1_III_epsilon_closure_branching_iff :=
    @section4_theorem1_epsilon_closure_branching_iff A.

  (* Theorem 1 II/III: maximal epsilon-simple symbol-extension determinism. *)
  Definition paper_support_theorem1_leafufa_maximal_epsilon_removal_deterministic :=
    @section4_theorem1_leafufa_maximal_epsilon_removal_deterministic A.

  (** Theorem 2: unambiguity and reach-unambiguity. *)

  (* Theorem 2: decomposed wrapper *)
  Definition paper_theorem2_unambiguity_and_reach_unambiguity :=
    @section4_theorem2_unambiguity_and_reach_unambiguity A.

  (* Theorem 2 supporting clauses. *)
  Definition paper_support_theorem2_accepting_maximal_da_bounded_by_leaf :=
    @section4_enfa_accepting_maximal_da_bounded_by_leaf A.

  Definition paper_support_theorem2_accepting_maximal_extension_injective :=
    @section4_enfa_accepting_maximal_extension_injective A.

  Definition paper_theorem2_leafufa_implies_ufa :=
    @section4_theorem2_leafufa_implies_ufa A.

  (* Theorem 2 LeafUFA-to-UFA alias. *)
  Definition paper_theorem2_leafufa_implies_ufa_under_accepting_maximal_da_leaf_bound :=
    @section4_theorem2_leafufa_implies_ufa_under_accepting_maximal_da_leaf_bound A.

  (* Theorem 2 accepting-maximal extension formulation. *)
  Definition paper_support_theorem2_leafufa_implies_ufa_under_extension_injective :=
    @section4_theorem2_leafufa_implies_ufa_under_started_traces_nodup_and_accepting_maximal_extension_injective A.

  Definition paper_theorem2_trim_extendable_ufa_implies_reachufa :=
    @section4_theorem2_trim_extendable_ufa_implies_reachufa A.

  Definition paper_theorem2_epsilon_free_trim_extendable_ufa_implies_reachufa :=
    @section4_theorem2_epsilon_free_trim_extendable_ufa_implies_reachufa A.

  Definition paper_theorem2_epsilon_free_trim_ufa_implies_reachufa :=
    @section4_theorem2_epsilon_free_trim_ufa_implies_reachufa A.

  Definition paper_theorem2_epsilon_free_trim_ufa_implies_sufa :=
    @section4_theorem2_epsilon_free_trim_ufa_implies_sufa A.

  Definition paper_theorem2_reachufa_single_final_list_implies_ufa :=
    @section4_theorem2_reachufa_single_final_list_implies_ufa A.

  Definition paper_theorem2_reachufa_unique_terminating_state_implies_ufa :=
    @section4_theorem2_reachufa_unique_terminating_state_implies_ufa A.

  (** Theorem 3: leaves and the sum of reach-ambiguities. *)

  (* Theorem 3 I *)
  Definition paper_theorem3_I_leaf_sum_dra :=
    @section4_theorem3_epsilon_free_leaf_sum_dra A.

  (* Theorem 3 II *)
  Definition paper_theorem3_II_prime_leaf_le_sum_dra :=
    @section4_theorem3_prime_leaf_le_sum_dra A.

  (** Lemma 2: ReachUFAs are at most linearly leaf-ambiguous. *)

  (* Lemma 2 *)
  Definition paper_lemma2_reachufa_linear_leaf_bound :=
    @section4_lemma2_reachufa_leaf_bound A.

  (** Theorem 4: NFA to Grammar. *)

  (* Theorem 4: Gamma construction *)
  Definition paper_theorem4_gamma_construction := @gamma_grammar_from A.

  (* Theorem 4: language equivalence. *)
  Definition paper_theorem4_gamma_language_equiv :=
    @section4_gamma_support_language_equiv A.

  (* Theorem 4 deterministic construction cost is recorded by the paper
     statement; the Rocq entry above exposes the constructive Gamma map and
     language-equivalence theorem. *)

  (** Lemma 3: Gamma is ambiguity-preserving. *)

  Definition paper_support_lemma3_gamma_accepting_maximal_reflects :=
    @section4_gamma_accepting_maximal_reflects A.

  (* Lemma 3: prime accepting trace/derivation bridge *)
  Definition paper_lemma3_gamma_prime_accepting_derivation_of_trace :=
    @section4_gamma_support_prime_accepting_derivation_of_trace A.

  Definition paper_lemma3_gamma_prime_accepting_trace_of_derivation :=
    @section4_gamma_support_prime_accepting_trace_of_derivation A.

  (* Lemma 3: prime reach trace/derivation bridge *)
  Definition paper_lemma3_gamma_prime_reach_derivation_of_trace :=
    @section4_gamma_support_prime_reach_derivation_of_trace A.

  Definition paper_lemma3_gamma_prime_reach_trace_of_derivation :=
    @section4_gamma_support_prime_reach_trace_of_derivation A.

  (* Lemma 3: prime leaf trace/derivation bridge *)
  Definition paper_lemma3_gamma_prime_leaf_derivation_of_trace :=
    @section4_gamma_support_prime_leaf_derivation_of_trace A.

  Definition paper_lemma3_gamma_prime_leaf_trace_of_derivation :=
    @section4_gamma_support_prime_leaf_trace_of_derivation A.

  (* Lemma 3: decomposed unambiguity preservation support *)
  Definition paper_lemma3_gamma_ufa_rlg_unambiguous_iff :=
    @section4_gamma_support_ufa_rlg_unambiguous_iff A.

  Definition paper_lemma3_gamma_reachufa_rlg_reach_unambiguous_iff :=
    @section4_gamma_support_reachufa_rlg_reach_unambiguous_iff A.

  Definition paper_lemma3_gamma_leafufa_rlg_leaf_unambiguous_iff :=
    @section4_gamma_support_leafufa_rlg_leaf_unambiguous_iff A.

  (* Lemma 3: Gamma numeric preservation, specialized to the current
     Gamma/RLG model.  The DA' accepting-maximal branch discharges Gamma
     accepting-maximal reflection internally. *)
  Definition paper_lemma3_gamma_da_prime_count_eq_under_accepting_maximal_reflection :=
    @section4_lemma3_gamma_da_prime_count_eq_with_alphabet_nodup A.

  Definition paper_lemma3_gamma_da_prime_count_eq :=
    @section4_lemma3_gamma_da_prime_count_eq_with_alphabet_nodup A.

  Definition paper_lemma3_gamma_dra_prime_count_eq :=
    @section4_lemma3_gamma_dra_prime_count_eq_with_alphabet_nodup A.

  Definition paper_lemma3_gamma_leaf_prime_count_eq :=
    @section4_lemma3_gamma_leaf_prime_count_eq_with_alphabet_nodup A.

  Definition paper_lemma3_gamma_prime_counts_eq_under_accepting_maximal_reflection :=
    @section4_lemma3_gamma_prime_counts_eq_with_alphabet_nodup A.

  Definition paper_lemma3_gamma_prime_counts_eq :=
    @section4_lemma3_gamma_prime_counts_eq_with_alphabet_nodup A.

  (* Lemma 3 aliases: direct da'/dra'/Leaf' equalities for Gamma's
     right-linear grammar representation, with the ENFA/RLG enumeration
     conditions provided by finite well-formedness, a single start state, and
     NoDup (fenfa_alphabet m).  Gamma accepting-maximal reflection is provided
     by [section4_gamma_accepting_maximal_reflects], and CFG finite and
     extended-cardinality readings are exposed by the Definition 8/9 aliases
     above. *)

  (** Theorem 5: (reach-)unambiguity and LR(1)-ness. *)

  (* Primary paper-order reading: Definition 10's nondeterministic LR machine
     is interpreted with terminal-word reduce-conflict semantics, giving the
     Theorem 5 bridge used by the paper statement. *)
  Definition paper_theorem5_terminal_semantic_bridge :=
    @section4_theorem5_terminal_semantic_bridge A.

  Definition paper_theorem5_terminal_lr1_iff_gamma_unambiguous_reach :=
    @section4_theorem5_terminal_lr1_iff_gamma_unambiguous_reach A.

  (* Theorem 5 I. *)
  Definition paper_theorem5_terminal_lr1_iff_ufa_reachufa :=
    @section4_theorem5_terminal_lr1_iff_ufa_reachufa A.

  (* Theorem 5 I, shorter paper-facing alias. *)
  Definition paper_theorem5_lr1_iff_ufa_reachufa :=
    paper_theorem5_terminal_lr1_iff_ufa_reachufa.

  (* Theorem 5 II, LeafUFA sufficient direction. *)
  Definition paper_theorem5_leafufa_sufficient_terminal_lr1 :=
    @section4_theorem5_leafufa_sufficient_terminal_lr1 A.

  (* Theorem 5 II, shorter paper-facing alias. *)
  Definition paper_theorem5_leafufa_sufficient_lr1 :=
    paper_theorem5_leafufa_sufficient_terminal_lr1.

  (* Canonical item-set formulations for Theorem 5. *)
  Definition paper_support_theorem5_canonical_semantic_bridge_under_conflict_reflection :=
    @section4_lr1_support_canonical_semantic_bridge_under_conflict_reflection A.

  Definition paper_support_theorem5_final_no_epsilon_successors :=
    @section4_enfa_final_no_epsilon_successors A.

  Definition paper_support_theorem5_final_no_epsilon_successors_maximal :=
    @section4_enfa_final_no_epsilon_successors_maximal A.

  Definition paper_support_theorem5_prime_final_conflict_reflection :=
    @gamma_prime_final_conflict_reflection A.

  Definition paper_support_theorem5_canonical_semantic_bridge_under_prime_final_reflection :=
    @section4_lr1_support_canonical_semantic_bridge_under_prime_final_reflection A.

  Definition paper_support_theorem5_canonical_lr1_iff_gamma_unambiguous_reach_under_conflict_reflection :=
    @section4_lr1_support_canonical_lr1_iff_gamma_unambiguous_reach_under_conflict_reflection A.

  Definition paper_support_theorem5_canonical_lr1_iff_ufa_reachufa_under_conflict_reflection :=
    @section4_lr1_support_canonical_lr1_iff_ufa_reachufa_under_conflict_reflection A.

  Definition paper_support_theorem5_canonical_lr1_iff_ufa_reachufa_under_prime_final_reflection :=
    @section4_lr1_support_canonical_lr1_iff_ufa_reachufa_under_prime_final_reflection A.

  Definition paper_support_theorem5_leafufa_sufficient_canonical_lr1_under_conflict_reflection :=
    @section4_lr1_support_leafufa_sufficient_canonical_lr1_under_conflict_reflection A.

  Definition paper_support_theorem5_leafufa_sufficient_canonical_lr1_under_prime_final_reflection :=
    @section4_lr1_support_leafufa_sufficient_canonical_lr1_under_prime_final_reflection A.

  Definition paper_support_theorem5_canonical_lr1_iff_ufa_reachufa :=
    @section4_lr1_support_canonical_lr1_iff_ufa_reachufa A.

  Definition paper_support_theorem5_leafufa_sufficient_canonical_lr1 :=
    @section4_lr1_support_leafufa_sufficient_canonical_lr1 A.

  Definition paper_support_theorem5_canonical_lr1_iff_gamma_unambiguous_reach :=
    @section4_lr1_support_canonical_lr1_iff_gamma_unambiguous_reach A.

  (** Definition 10: nondeterministic LR(1) machine. *)

  (* Definition 10 I *)
  Definition paper_definition10_I_lr1_reduce_items := @lr1_reduce_items A.

  (* Definition 10 I *)
  Definition paper_definition10_I_lr1_nonreduce_items :=
    @lr1_nonreduce_items A.

  (* Definition 10 I *)
  Definition paper_definition10_I_lr1_items := @lr1_items A.

  (* Definition 10 II *)
  Definition paper_definition10_II_lr1_reduce_transitions :=
    @lr1_reduce_transitions A.

  (* Definition 10 II *)
  Definition paper_definition10_II_lr1_shift_transitions :=
    @lr1_shift_transitions A.

  (* Definition 10 II *)
  Definition paper_definition10_II_lr1_step := @lr1_step A.

  (* Definition 10 III *)
  Definition paper_definition10_III_lr1_machine_of_enfa :=
    @lr1_machine_of_enfa A.

  (* Definition 10: structural characterization *)
  Definition paper_definition10_lr1_machine_characterization :=
    @section4_definition10_lr1_machine_characterization A.

  (* Definition 10: expanded membership characterization *)
  Definition paper_definition10_lr1_machine_full_characterization :=
    @section4_definition10_lr1_machine_full_characterization A.

  (** Theorem 6: leaves and LR(1)-conflicts. *)

  (* Theorem 6 *)
  Definition paper_theorem6_conflicts_le_leaves :=
    @section4_theorem6_conflicts_le_leaves A.

  (* Theorem 6 specialization to Definition 10 machines *)
  Definition paper_theorem6_conflicts_le_leaves_of_enfa :=
    @section4_theorem6_conflicts_le_leaves_of_enfa A.

  (* Theorem 6 corollary. *)
  Definition paper_theorem6_leaf_one_conflict_free_of_enfa :=
    @section4_theorem6_leaf_one_conflict_free_of_enfa A.

  (** Lemma 4: facts about M_LR(u). *)

  (* Lemma 4 I *)
  Definition paper_lemma4_I_lr1_leaf_preservation :=
    @section4_lemma4_I_lr1_leaf_preservation A.

  (* Lemma 4 II: deterministic O(|E|) construction-cost clause. *)

  (** Decision problems and complexity results. *)

  (* Problem 1: U, ReachU, and LeafU. *)
  Definition paper_problem1_U := @Problem1_U A.

  Definition paper_problem1_ReachU := @Problem1_ReachU A.

  Definition paper_problem1_LeafU := @Problem1_LeafU A.

  (* Theorem 7: NL-hardness of U, ReachU, and epsilon-LeafU. *)

  (* Problem 2: Kiefer GAP problem used in the Theorem 7 proof. *)

  (* Theorem 8: NL-completeness of U, ReachU, and epsilon-LeafU. *)

  (* Problem 3: SUFA- and LeafUFA-Member. *)
  Definition paper_problem3_SUFA_Member := @Problem3_SUFA_Member A.

  Definition paper_problem3_LeafUFA_Member := @Problem3_LeafUFA_Member A.

  (* Definition 11: directed forest accessibility used by the L-hardness proof. *)

  (* Theorem 9: L-hardness of SUFA-Member. *)

  (* Theorem 10: SUFA-Member DSPACE(log^2 n / log log n) upper bound. *)

  (* Theorem 11: L-completeness of LeafUFA-Member. *)

  (* Theorem 12: CREW P-RAM parallel membership upper bound. *)

End Section4PaperOrder.
