From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Regex Require Import KleeneSemantics RegexSSS.
From PositionAutomata.Automata Require Import EpsilonNFA.
From PositionAutomata.Grammar Require Import RightLinearGrammar.
From PositionAutomata.Section4 Require Import Section4LR.

Section Section4Examples.
  (** Examples for the new Section 4 theorems.  They prefer [vm_compute] or
      direct theorem calls, keeping the examples focused on the main
      development. *)

  Fixpoint bool_list_eqb (xs ys : list bool) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => Bool.eqb x y && bool_list_eqb xs' ys'
    | _, _ => false
    end.

  Lemma bool_eqb_reflects_eq :
    label_matches_reflects_eq Bool.eqb.
  Proof.
    split.
    - intros []; reflexivity.
    - intros [] [] H; simpl in H; auto; discriminate.
  Qed.

  (** CFG extended-cardinality example.

      The one-production CFG [S -> S] has infinitely many distinct rightmost
      reach derivations for the same marked reach fiber.  This example
      illustrates the extended-cardinality reading used for Definition 8. *)
  Definition section4_example_cfg_self_loop : @context_free_grammar bool :=
    @section4_cfg_self_loop bool.

  Example section4_example_cfg_self_loop_dra_fiber_infinite :
    section4_infinite_cardinality
      (cfg_dra_derivation section4_example_cfg_self_loop [] tt).
  Proof.
    exact (@section4_cfg_self_loop_dra_fiber_infinite bool).
  Qed.

  Example section4_example_cfg_self_loop_dra_extended_cardinality_infinite :
    section4_definition8_I_ii_cfg_dra_extended_cardinality
      section4_example_cfg_self_loop [] tt Section4Infinite.
  Proof.
    exact (@section4_cfg_self_loop_dra_extended_cardinality_infinite bool).
  Qed.

  Example section4_example_cfg_self_loop_dra_fiber_not_finite :
    ~ exists xs,
        section4_finite_cardinality
          (cfg_dra_derivation section4_example_cfg_self_loop [] tt)
          xs.
  Proof.
    exact (@section4_cfg_self_loop_dra_fiber_not_finite bool).
  Qed.

  (** Minimal ENFA examples for Definitions 5/6.  A one-state bool automaton
      demonstrates da/dra/leaf counts, trim UFA -> ReachUFA, and
      ReachUFA + single final -> UFA. *)
  Definition unit_bool_enfa : @finite_enfa bool :=
    {|
      fenfa_base :=
        {|
          enfa_state := unit;
          enfa_start := [tt];
          enfa_final := fun _ => true;
          enfa_step :=
            fun _ l =>
              match l with
              | Some true => [tt]
              | _ => []
              end
        |};
      fenfa_states := [tt];
      fenfa_alphabet := [true];
      fenfa_state_eqb := fun _ _ => true;
      fenfa_state_eqb_sound := fun x y _ =>
        match x, y with tt, tt => eq_refl end;
      fenfa_state_eqb_complete := fun x y _ =>
        match x, y with tt, tt => eq_refl end
    |}.

  Example unit_bool_enfa_wf :
    finite_enfa_wf unit_bool_enfa.
  Proof.
    constructor; simpl.
    - repeat constructor; intro H; contradiction.
    - intros q Hq. destruct q. simpl. auto.
    - intros q l q' _ Hstep.
      destruct q, l as [[|]|], q'; simpl in *; auto; contradiction.
    - intros q a q' _ Hstep.
      destruct q, a, q'; simpl in *; auto; contradiction.
    - intros q l _.
      destruct q, l as [[|]|]; simpl; repeat constructor; intro H; contradiction.
  Qed.

  Example unit_bool_enfa_epsilon_free :
    enfa_epsilon_free unit_bool_enfa.
  Proof.
    intros []. reflexivity.
  Qed.

  Example unit_bool_enfa_lemma1_da :
    enfa_da_word unit_bool_enfa [true] =
    enfa_da_prime_word unit_bool_enfa [true].
  Proof.
    now apply section4_lemma1_da.
  Qed.

  Example unit_bool_enfa_lemma1_dra :
    enfa_dra_at unit_bool_enfa [true] tt =
    enfa_dra_prime_at unit_bool_enfa [true] tt.
  Proof.
    now apply section4_lemma1_dra.
  Qed.

  Example unit_bool_enfa_trim :
    enfa_trim unit_bool_enfa.
  Proof.
    intros [] _. split.
    - exists (@nil bool). vm_compute. lia.
    - exists [], (tt, []).
      repeat split; simpl; auto.
  Qed.

  Example unit_bool_trim_ufa_direct_to_reachufa :
    enfa_UFA unit_bool_enfa -> enfa_ReachUFA unit_bool_enfa.
  Proof.
    intro Hufa.
    eapply
      (section4_theorem2_epsilon_free_trim_ufa_implies_reachufa
         unit_bool_enfa).
    - apply unit_bool_enfa_epsilon_free.
    - apply unit_bool_enfa_wf.
    - unfold enfa_single_start. simpl. lia.
    - apply unit_bool_enfa_trim.
    - exact Hufa.
  Qed.

  Example unit_bool_enfa_final_singleton :
    enfa_final_states unit_bool_enfa = [tt].
  Proof.
    reflexivity.
  Qed.

  Example unit_bool_reachufa_single_final_to_ufa :
    enfa_ReachUFA unit_bool_enfa -> enfa_UFA unit_bool_enfa.
  Proof.
    intro Hreach.
    eapply section4_theorem2_reachufa_single_final_list_implies_ufa.
    - exact Hreach.
    - simpl. auto.
    - reflexivity.
  Qed.

  Example unit_bool_enfa_accepts_true :
    enfa_accepts_from unit_bool_enfa tt [true].
  Proof.
    exists tt, [((tt, Some true), tt)].
    repeat split; simpl; auto.
    econstructor; simpl; auto.
    constructor.
  Qed.

  Example unit_bool_gamma_accepts_true :
    rlg_accepts (gamma_grammar_from unit_bool_enfa tt) [true].
  Proof.
    eapply section4_gamma_support_language_sound.
    - apply unit_bool_enfa_wf.
    - simpl. auto.
    - apply unit_bool_enfa_accepts_true.
  Qed.

  Example unit_bool_gamma_complete_true :
    rlg_accepts (gamma_grammar_from unit_bool_enfa tt) [true] ->
    enfa_accepts_from unit_bool_enfa tt [true].
  Proof.
    intro H.
    now apply section4_gamma_support_language_complete in H.
  Qed.

  Example unit_bool_leaf_bound_true :
    enfa_leaf_prime_word unit_bool_enfa [true] <=
    length (fenfa_states unit_bool_enfa).
  Proof.
    vm_compute. lia.
  Qed.

  (** Examples with epsilon transitions.  These check the Definition 5/6 prime
      filters: epsilon-simple/maximal trace counts on the empty word and later
      symbol traces. *)
  Definition epsilon_bool_enfa : @finite_enfa bool :=
    {|
      fenfa_base :=
        {|
          enfa_state := bool;
          enfa_start := [false];
          enfa_final := fun q => q;
          enfa_step :=
            fun q l =>
              match q, l with
              | false, None => [true]
              | true, Some true => [true]
              | _, _ => []
              end
        |};
      fenfa_states := [false; true];
      fenfa_alphabet := [true];
      fenfa_state_eqb := Bool.eqb;
      fenfa_state_eqb_sound := fun x y H => proj1 (Bool.eqb_true_iff x y) H;
      fenfa_state_eqb_complete := fun x y H => proj2 (Bool.eqb_true_iff x y) H
    |}.

  Example epsilon_bool_enfa_wf :
    finite_enfa_wf epsilon_bool_enfa.
  Proof.
    constructor; simpl.
    - constructor.
      + intro H. destruct H as [H | []]; discriminate.
      + constructor.
        * intro H. contradiction.
        * constructor.
    - intros q Hq. destruct Hq as [Hq | []]. subst. simpl. auto.
    - intros q l q' Hq Hstep.
      destruct q, l as [[|]|], q'; simpl in *; auto; contradiction.
    - intros q a q' Hq Hstep.
      destruct q, a, q'; simpl in *; auto; contradiction.
    - intros q l Hq.
      destruct q, l as [[|]|]; simpl; repeat constructor; intro H; contradiction.
  Qed.

  Example epsilon_bool_simple_filter_reaches_final :
    enfa_dra_prime_at epsilon_bool_enfa [] true = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example epsilon_bool_leaf_bound_empty :
    enfa_leaf_prime_word epsilon_bool_enfa [] <=
    length (fenfa_states epsilon_bool_enfa).
  Proof.
    vm_compute. lia.
  Qed.

  Definition epsilon_self_loop_bool_enfa : @finite_enfa bool :=
    {|
      fenfa_base :=
        {|
          enfa_state := unit;
          enfa_start := [tt];
          enfa_final := fun _ => true;
          enfa_step :=
            fun _ l =>
              match l with
              | None => [tt]
              | Some _ => []
              end
        |};
      fenfa_states := [tt];
      fenfa_alphabet := [true; false];
      fenfa_state_eqb := fun _ _ => true;
      fenfa_state_eqb_sound := fun x y _ =>
        match x, y with tt, tt => eq_refl end;
      fenfa_state_eqb_complete := fun x y _ =>
        match x, y with tt, tt => eq_refl end
    |}.

  Example epsilon_self_loop_bool_enfa_wf :
    finite_enfa_wf epsilon_self_loop_bool_enfa.
  Proof.
    constructor; simpl.
    - repeat constructor; intro H; contradiction.
    - intros [] Hq. simpl. auto.
    - intros [] [a|] [] _ Hstep; simpl in *; auto; contradiction.
    - intros [] a [] _ Hstep. simpl in Hstep. contradiction.
    - intros [] [a|] _; simpl.
      + constructor.
      + constructor; [intro H; contradiction | constructor].
  Qed.

  Lemma epsilon_self_loop_traces_nonempty :
    forall fuel b w,
      traces_from_fuel
        epsilon_self_loop_bool_enfa fuel tt (b :: w) = [].
  Proof.
    induction fuel as [| fuel IH]; intros b w; simpl.
    - reflexivity.
    - rewrite (IH b w). reflexivity.
  Qed.

  Example epsilon_self_loop_bool_leafufa :
    enfa_LeafUFA epsilon_self_loop_bool_enfa.
  Proof.
    intros [| b w].
    - vm_compute. lia.
    - unfold enfa_leaf_prime_word,
        enfa_maximal_simple_reach_count,
        started_traces.
      simpl.
      rewrite epsilon_self_loop_traces_nonempty.
      simpl. lia.
  Qed.

  Example epsilon_self_loop_bool_not_epsilon_free :
    ~ enfa_epsilon_free epsilon_self_loop_bool_enfa.
  Proof.
    intro Heps.
    specialize (Heps tt).
    simpl in Heps.
    discriminate.
  Qed.

  Example epsilon_self_loop_bool_not_dfa_conditions :
    ~ enfa_DFA_conditions epsilon_self_loop_bool_enfa.
  Proof.
    intros [Heps _].
    exact (epsilon_self_loop_bool_not_epsilon_free Heps).
  Qed.

  (** Example separating reach ambiguity from accepting ambiguity.
      [two_start_join_enfa] reaches one state by two paths for the same prefix,
      without necessarily creating accepting ambiguity. *)
  (* Theorem 1.II is used through the maximal lifted-trace epsilon-removal
     specification, which focuses on maximal epsilon-simple lifted traces and
     their symbol-extension behavior. *)
  Example epsilon_bool_theorem2_II_maximal_removal :
    enfa_LeafUFA epsilon_bool_enfa ->
    enfa_maximal_epsilon_removed_deterministic epsilon_bool_enfa.
  Proof.
    intro Hleaf.
    eapply section4_theorem1_leafufa_maximal_epsilon_removal_deterministic.
    - apply epsilon_bool_enfa_wf.
    - unfold enfa_single_start. simpl. lia.
    - exact Hleaf.
  Qed.

  Definition two_start_join_enfa : @finite_enfa bool :=
    {|
      fenfa_base :=
        {|
          enfa_state := bool;
          enfa_start := [false; true];
          enfa_final := fun _ => false;
          enfa_step :=
            fun _ l =>
              match l with
              | Some true => [true]
              | _ => []
              end
        |};
      fenfa_states := [false; true];
      fenfa_alphabet := [true];
      fenfa_state_eqb := Bool.eqb;
      fenfa_state_eqb_sound := fun x y H => proj1 (Bool.eqb_true_iff x y) H;
      fenfa_state_eqb_complete := fun x y H => proj2 (Bool.eqb_true_iff x y) H
    |}.

  Example two_start_join_enfa_wf :
    finite_enfa_wf two_start_join_enfa.
  Proof.
    constructor; simpl.
    - constructor.
      + intro H. destruct H as [H | []]; discriminate.
      + constructor.
        * intro H. contradiction.
        * constructor.
    - intros q Hq. destruct Hq as [Hq | [Hq | []]]; subst; simpl; auto.
    - intros q l q' Hq Hstep.
      destruct q, l as [[|]|], q'; simpl in *; auto; contradiction.
    - intros q a q' Hq Hstep.
      destruct q, a, q'; simpl in *; auto; contradiction.
    - intros q l Hq.
      destruct q, l as [[|]|]; simpl; repeat constructor; intro H; contradiction.
  Qed.

  Example two_start_join_reach_ambiguous :
    enfa_dra_prime_at two_start_join_enfa [true] true = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example two_start_join_not_accepting :
    enfa_da_prime_word two_start_join_enfa [true] = 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Gamma ambiguity-preservation examples.  [two_accepting_paths_enfa] has
      two distinct accepting paths; the examples show how the Gamma
      derivation/ENFA accepting trace-end correspondence reflects that
      ambiguity. *)
  Definition two_accepting_paths_enfa : @finite_enfa bool :=
    {|
      fenfa_base :=
        {|
          enfa_state := bool;
          enfa_start := [false];
          enfa_final := fun _ => true;
          enfa_step :=
            fun q l =>
              match q, l with
              | false, Some true => [false; true]
              | _, _ => []
              end
        |};
      fenfa_states := [false; true];
      fenfa_alphabet := [true];
      fenfa_state_eqb := Bool.eqb;
      fenfa_state_eqb_sound := fun x y H => proj1 (Bool.eqb_true_iff x y) H;
      fenfa_state_eqb_complete := fun x y H => proj2 (Bool.eqb_true_iff x y) H
    |}.

  Example two_accepting_paths_enfa_wf :
    finite_enfa_wf two_accepting_paths_enfa.
  Proof.
    constructor; simpl.
    - constructor.
      + intro H. destruct H as [H | []]; discriminate.
      + constructor.
        * intro H. contradiction.
        * constructor.
    - intros q Hq. destruct Hq as [Hq | []]. subst. simpl. auto.
    - intros q l q' Hq Hstep.
      destruct q, l as [[|]|], q'; simpl in *; auto; contradiction.
    - intros q a q' Hq Hstep.
      destruct q, a, q'; simpl in *; auto; contradiction.
    - intros q l Hq.
      destruct q, l as [[|]|]; simpl;
        repeat constructor; simpl; intros H; intuition discriminate.
  Qed.

  Example two_accepting_paths_gamma_derivations_reflect_traces :
    let G := gamma_grammar_from two_accepting_paths_enfa false in
    exists q1 q2 t1 t2,
      valid_trace two_accepting_paths_enfa false t1 q1 /\
      valid_trace two_accepting_paths_enfa false t2 q2 /\
      enfa_final (fenfa_base two_accepting_paths_enfa) q1 = true /\
      enfa_final (fenfa_base two_accepting_paths_enfa) q2 = true /\
      ~ (t1 = t2 /\ q1 = q2).
  Proof.
    simpl.
    pose (d1 :=
      [(false, [true], Some false); (false, [], None)]
      : rlg_derivation (gamma_grammar_from two_accepting_paths_enfa false)).
    pose (d2 :=
      [(false, [true], Some true); (true, [], None)]
      : rlg_derivation (gamma_grammar_from two_accepting_paths_enfa false)).
    destruct
      (section4_gamma_support_ambiguity_preservation_complete
         two_accepting_paths_enfa false false d1 d2)
      as [q1 [q2 [t1 [t2 [Ht1 [Ht2 [Hf1 [Hf2 [Hdiff _]]]]]]]]].
    - unfold d1.
      change
        (rlg_derivation_valid
           (gamma_grammar_from two_accepting_paths_enfa false)
           false
           (gamma_derivation_of_trace
              two_accepting_paths_enfa false
              [((false, Some true), false)] false)
           None).
      eapply gamma_derivation_of_trace_valid_from.
      + apply two_accepting_paths_enfa_wf.
      + simpl. auto.
      + econstructor; simpl; auto. constructor.
      + reflexivity.
    - unfold d2.
      change
        (rlg_derivation_valid
           (gamma_grammar_from two_accepting_paths_enfa false)
           false
           (gamma_derivation_of_trace
              two_accepting_paths_enfa false
              [((false, Some true), true)] true)
           None).
      eapply gamma_derivation_of_trace_valid_from.
      + apply two_accepting_paths_enfa_wf.
      + simpl. auto.
      + econstructor; simpl; auto. constructor.
      + reflexivity.
    - unfold d1, d2. discriminate.
    - exists q1, q2, t1, t2. repeat split; auto.
  Qed.

  (** RegexSSS language-equivalence and counting examples.  They show direct
      use of [regex_Msss_language_sound], [regex_Msss_language_equiv_atom],
      and the generic [regex_Msss_language_equiv] on concrete regexes. *)
  Example regex_msss_eps_accepts_empty :
    enfa_da_prime_word (regex_Msss [true] Bool.eqb (@Eps bool)) [] = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example regex_msss_atom_accepts_true :
    enfa_da_prime_word (regex_Msss [true] Bool.eqb (Atom true)) [true] = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example regex_msss_language_sound_atom_true :
    enfa_accepts_word (regex_Msss [true] Bool.eqb (Atom true)) [true].
  Proof.
    eapply regex_Msss_language_sound.
    - split.
      + intros []; reflexivity.
      + intros [] [] H; simpl in H; auto; discriminate.
    - constructor.
  Qed.

  Example regex_msss_language_equiv_atom_true :
    (matches (Atom true) [true] <->
     enfa_accepts_word (regex_Msss [true] Bool.eqb (Atom true)) [true]).
  Proof.
    apply regex_Msss_language_equiv_atom.
    split.
    - intros []; reflexivity.
    - intros [] [] H; simpl in H; auto; discriminate.
  Qed.

  Example regex_msss_language_equiv_star_two_true :
    matches (Star (Atom true)) [true; true] <->
    enfa_accepts_word
      (regex_Msss [true] Bool.eqb (Star (Atom true))) [true; true].
  Proof.
    apply regex_Msss_language_equiv.
    apply bool_eqb_reflects_eq.
  Qed.

  Example regex_msss_alt_has_two_true_traces :
    enfa_da_prime_word
      (regex_Msss [true] Bool.eqb (Alt (Atom true) (Atom true)))
      [true] = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example regex_msss_star_two_symbols :
    enfa_da_prime_word
      (regex_Msss [true] Bool.eqb (Star (Atom true)))
      [true; true] = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Lemma section4_valid_trace_snoc_inv :
    forall (m : @finite_enfa bool) s t q,
      valid_trace m s t q ->
      t <> [] ->
      exists t' p l,
        t = t' ++ [((p, l), q)] /\
        valid_trace m s t' p /\
        In q (enfa_step (fenfa_base m) p l).
  Proof.
    intros m s t q Hvalid.
    induction Hvalid as [q| p l r q t Hstep Htail IH];
      intros Hnonempty.
    - contradiction.
    - destruct t as [| e t'].
      + inversion Htail; subst.
        exists [], p, l. simpl. repeat split; auto.
        constructor.
      + destruct (IH ltac:(discriminate)) as
          [u [p' [l' [Ht [Hu Hlast]]]]].
        exists (((p, l), r) :: u), p', l'.
        rewrite Ht. simpl. repeat split; auto.
        econstructor; eauto.
  Qed.

  (** Paper Example 2.

      We encode the paper alphabet by [true = a] and [false = b].  The
      machine below is the Sippu-Soisalon-Soininen epsilon-NFA [Msss] for
      [(a+b)^* a (a+b)^n].  The paper text says SUFA in one sentence, but
      this generated machine has epsilon transitions; under Definition 6's
      Rocq meaning of SUFA ([epsilon_free /\ ReachUFA]) it is not a SUFA. *)
  Definition section4_example2_ab : regex bool :=
    Alt (Atom true) (Atom false).

  Fixpoint section4_example2_pow_ab (n : nat) : regex bool :=
    match n with
    | O => Eps
    | S n' => Cat section4_example2_ab (section4_example2_pow_ab n')
    end.

  Definition section4_example2_regex (n : nat) : regex bool :=
    Cat
      (Cat (Star section4_example2_ab) (Atom true))
      (section4_example2_pow_ab n).

  Definition section4_example2_m (n : nat) : @finite_enfa bool :=
    regex_Msss [true; false] Bool.eqb (section4_example2_regex n).

  Definition section4_example2_attack_word (n : nat) : list bool :=
    repeat true (S n).

  Definition section4_example2_checkpoint (i : nat) : nat :=
    match i with
    | O => 2
    | S k => 8 + 3 * k
    end.

  Definition section4_example2_suffix_b_entry (i : nat) : nat :=
    9 + 3 * i.

  Definition section4_example2_suffix_b_exit (i : nat) : nat :=
    10 + 3 * i.

  Definition section4_example2_edge
      (p : nat) (l : option bool) (q : nat)
      : nat * option bool * nat :=
    (p, l, q).

  Definition section4_example2_trace_edge
      (p : nat) (l : option bool) (q : nat)
      : ((nat * option bool) * nat) :=
    ((p, l), q).

  Definition section4_example2_fixed_edges
      : list (nat * option bool * nat) :=
    [ section4_example2_edge 0 None 4;
      section4_example2_edge 4 None 3;
      section4_example2_edge 5 None 4;
      section4_example2_edge 4 (Some true) 5;
      section4_example2_edge 4 None 6;
      section4_example2_edge 7 None 5;
      section4_example2_edge 6 (Some false) 7;
      section4_example2_edge 3 (Some true) 2 ].

  Fixpoint section4_example2_suffix_edges_from
      (i blocks : nat) : list (nat * option bool * nat) :=
    match blocks with
    | O =>
        [ section4_example2_edge
            (section4_example2_checkpoint i) None 1 ]
    | S blocks' =>
        [ section4_example2_edge
            (section4_example2_checkpoint i) (Some true)
            (section4_example2_checkpoint (S i));
          section4_example2_edge
            (section4_example2_checkpoint i) None
            (section4_example2_suffix_b_entry i);
          section4_example2_edge
            (section4_example2_suffix_b_exit i) None
            (section4_example2_checkpoint (S i));
          section4_example2_edge
            (section4_example2_suffix_b_entry i) (Some false)
            (section4_example2_suffix_b_exit i) ] ++
        section4_example2_suffix_edges_from (S i) blocks'
    end.

  Definition section4_example2_edges (n : nat)
      : list (nat * option bool * nat) :=
    section4_example2_fixed_edges ++
    section4_example2_suffix_edges_from 0 n.

  Inductive section4_example2_edge_shape
      (n : nat) : nat -> option bool -> nat -> Prop :=
  | Example2EdgeStart :
      section4_example2_edge_shape n 0 None 4
  | Example2EdgeStarExit :
      section4_example2_edge_shape n 4 None 3
  | Example2EdgeStarLoopBack :
      section4_example2_edge_shape n 5 None 4
  | Example2EdgeStarTrue :
      section4_example2_edge_shape n 4 (Some true) 5
  | Example2EdgeStarBEntry :
      section4_example2_edge_shape n 4 None 6
  | Example2EdgeStarBJoin :
      section4_example2_edge_shape n 7 None 5
  | Example2EdgeStarFalse :
      section4_example2_edge_shape n 6 (Some false) 7
  | Example2EdgeMandatoryA :
      section4_example2_edge_shape n 3 (Some true) 2
  | Example2EdgeSuffixTrue :
      forall i,
        i < n ->
        section4_example2_edge_shape n
          (section4_example2_checkpoint i) (Some true)
          (section4_example2_checkpoint (S i))
  | Example2EdgeSuffixBEntry :
      forall i,
        i < n ->
        section4_example2_edge_shape n
          (section4_example2_checkpoint i) None
          (section4_example2_suffix_b_entry i)
  | Example2EdgeSuffixBJoin :
      forall i,
        i < n ->
        section4_example2_edge_shape n
          (section4_example2_suffix_b_exit i) None
          (section4_example2_checkpoint (S i))
  | Example2EdgeSuffixFalse :
      forall i,
        i < n ->
        section4_example2_edge_shape n
          (section4_example2_suffix_b_entry i) (Some false)
          (section4_example2_suffix_b_exit i)
  | Example2EdgeFinal :
      section4_example2_edge_shape n
        (section4_example2_checkpoint n) None 1.

  Lemma section4_example2_suffix_edge_in_shape :
    forall n base p l q,
      In (p, l, q) (section4_example2_suffix_edges_from base n) ->
      (exists i,
          base <= i < base + n /\
          ((p, l, q) =
            (section4_example2_checkpoint i, Some true,
             section4_example2_checkpoint (S i)) \/
           (p, l, q) =
            (section4_example2_checkpoint i, None,
             section4_example2_suffix_b_entry i) \/
           (p, l, q) =
            (section4_example2_suffix_b_exit i, None,
             section4_example2_checkpoint (S i)) \/
           (p, l, q) =
            (section4_example2_suffix_b_entry i, Some false,
             section4_example2_suffix_b_exit i))) \/
      (p, l, q) =
        (section4_example2_checkpoint (base + n), None, 1).
  Proof.
    induction n as [| n IH]; intros base p l q Hin; simpl in Hin.
    - destruct Hin as [Hin | []]. right.
      inversion Hin; subst. now rewrite Nat.add_0_r.
    - repeat
        (destruct Hin as [Hin | Hin];
         [left; exists base; split; [lia |];
          inversion Hin; subst; simpl; auto |]).
      specialize (IH (S base) p l q Hin) as
        [[i [[Hi0 Hi1] Hcase]] | Hfinal].
      + left. exists i. split; [lia | exact Hcase].
      + right.
        replace (base + S n) with (S base + n) by lia.
        exact Hfinal.
  Qed.

  Lemma section4_example2_edge_in_shape :
    forall n p l q,
      In (p, l, q) (section4_example2_edges n) ->
      section4_example2_edge_shape n p l q.
  Proof.
    intros n p l q Hin.
    unfold section4_example2_edges, section4_example2_fixed_edges in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    - simpl in Hin.
      repeat
        (destruct Hin as [Hin | Hin];
         [inversion Hin; subst; constructor |]).
      contradiction.
    - apply section4_example2_suffix_edge_in_shape in Hin as
        [[i [[Hi0 Hi1] Hcase]] | Hfinal].
      + assert (Hi : i < n) by lia.
        destruct Hcase as
          [Hcase | [Hcase | [Hcase | Hcase]]];
          inversion Hcase; subst; constructor; exact Hi.
      + inversion Hfinal; subst.
        replace (0 + n) with n by lia.
        constructor.
  Qed.

  Lemma section4_example2_suffix_true_edge_in_from :
    forall blocks base i,
      base <= i < base + blocks ->
      In
        (section4_example2_checkpoint i, Some true,
         section4_example2_checkpoint (S i))
        (section4_example2_suffix_edges_from base blocks).
  Proof.
    induction blocks as [| blocks IH]; intros base i Hi; [lia |].
    simpl.
    destruct (Nat.eq_dec i base) as [-> | Hneq].
    - simpl. auto.
    - right. right. right. right.
      apply IH. lia.
  Qed.

  Lemma section4_example2_suffix_true_edge_in :
    forall n i,
      i < n ->
      In
        (section4_example2_checkpoint i, Some true,
         section4_example2_checkpoint (S i))
        (section4_example2_edges n).
  Proof.
    intros n i Hi.
    unfold section4_example2_edges.
    apply in_or_app. right.
    apply section4_example2_suffix_true_edge_in_from.
    lia.
  Qed.

  Lemma section4_example2_suffix_b_entry_edge_in_from :
    forall blocks base i,
      base <= i < base + blocks ->
      In
        (section4_example2_checkpoint i, None,
         section4_example2_suffix_b_entry i)
        (section4_example2_suffix_edges_from base blocks).
  Proof.
    induction blocks as [| blocks IH]; intros base i Hi; [lia |].
    simpl.
    destruct (Nat.eq_dec i base) as [-> | Hneq].
    - simpl. auto.
    - right. right. right. right.
      apply IH. lia.
  Qed.

  Lemma section4_example2_suffix_b_entry_edge_in :
    forall n i,
      i < n ->
      In
        (section4_example2_checkpoint i, None,
         section4_example2_suffix_b_entry i)
        (section4_example2_edges n).
  Proof.
    intros n i Hi.
    unfold section4_example2_edges.
    apply in_or_app. right.
    apply section4_example2_suffix_b_entry_edge_in_from.
    lia.
  Qed.

  Lemma section4_example2_suffix_b_exit_edge_in_from :
    forall blocks base i,
      base <= i < base + blocks ->
      In
        (section4_example2_suffix_b_exit i, None,
         section4_example2_checkpoint (S i))
        (section4_example2_suffix_edges_from base blocks).
  Proof.
    induction blocks as [| blocks IH]; intros base i Hi; [lia |].
    simpl.
    destruct (Nat.eq_dec i base) as [-> | Hneq].
    - simpl. auto.
    - right. right. right. right.
      apply IH. lia.
  Qed.

  Lemma section4_example2_suffix_b_exit_edge_in :
    forall n i,
      i < n ->
      In
        (section4_example2_suffix_b_exit i, None,
         section4_example2_checkpoint (S i))
        (section4_example2_edges n).
  Proof.
    intros n i Hi.
    unfold section4_example2_edges.
    apply in_or_app. right.
    apply section4_example2_suffix_b_exit_edge_in_from.
    lia.
  Qed.

  Lemma section4_example2_suffix_false_edge_in_from :
    forall blocks base i,
      base <= i < base + blocks ->
      In
        (section4_example2_suffix_b_entry i, Some false,
         section4_example2_suffix_b_exit i)
        (section4_example2_suffix_edges_from base blocks).
  Proof.
    induction blocks as [| blocks IH]; intros base i Hi; [lia |].
    simpl.
    destruct (Nat.eq_dec i base) as [-> | Hneq].
    - simpl. auto.
    - right. right. right. right.
      apply IH. lia.
  Qed.

  Lemma section4_example2_suffix_false_edge_in :
    forall n i,
      i < n ->
      In
        (section4_example2_suffix_b_entry i, Some false,
         section4_example2_suffix_b_exit i)
        (section4_example2_edges n).
  Proof.
    intros n i Hi.
    unfold section4_example2_edges.
    apply in_or_app. right.
    apply section4_example2_suffix_false_edge_in_from.
    lia.
  Qed.

  Lemma section4_example2_suffix_final_edge_in_from :
    forall blocks base,
      In
        (section4_example2_checkpoint (base + blocks), None, 1)
        (section4_example2_suffix_edges_from base blocks).
  Proof.
    induction blocks as [| blocks IH]; intro base; simpl.
    - now rewrite Nat.add_0_r; auto.
    - right. right. right. right.
      replace (base + S blocks) with (S base + blocks) by lia.
      apply IH.
  Qed.

  Lemma section4_example2_suffix_final_edge_in :
    forall n,
      In
        (section4_example2_checkpoint n, None, 1)
        (section4_example2_edges n).
  Proof.
    intro n.
    unfold section4_example2_edges.
    apply in_or_app. right.
    replace n with (0 + n) at 1 by lia.
    apply section4_example2_suffix_final_edge_in_from.
  Qed.

  Lemma section4_example2_pow_ab_compile_edges_from :
    forall n i,
      sss_edges
        (sss_compile_between
           (section4_example2_checkpoint (S i))
           (section4_example2_checkpoint i) 1
           (section4_example2_pow_ab n)) =
      section4_example2_suffix_edges_from i n.
  Proof.
    induction n as [| n IH]; intro i; simpl.
    - reflexivity.
    - destruct i as [| i].
      + simpl.
        change 11 with (section4_example2_checkpoint 2).
        change 8 with (section4_example2_checkpoint 1).
        rewrite (IH 1). reflexivity.
      + simpl.
        match goal with
        | |- context
            [sss_compile_between ?fresh ?start 1
               (section4_example2_pow_ab n)] =>
            replace fresh
              with (section4_example2_checkpoint (S (S (S i))))
              by (simpl; lia);
            replace start
              with (section4_example2_checkpoint (S (S i)))
              by (simpl; lia)
        end.
        rewrite (IH (S (S i))). reflexivity.
  Qed.

  Lemma section4_example2_compile_edges :
    forall n,
      sss_edges (sss_compile (section4_example2_regex n)) =
      section4_example2_edges n.
  Proof.
    intro n.
    unfold section4_example2_regex, section4_example2_edges,
      section4_example2_fixed_edges.
    simpl.
    change 8 with (section4_example2_checkpoint 1).
    change 2 with (section4_example2_checkpoint 0).
    rewrite (section4_example2_pow_ab_compile_edges_from n 0).
    reflexivity.
  Qed.

  Lemma section4_example2_step_shape :
    forall n p l q,
      In q (enfa_step (fenfa_base (section4_example2_m n)) p l) ->
      section4_example2_edge_shape n p l q.
  Proof.
    intros n p l q Hstep.
    unfold section4_example2_m, regex_Msss in Hstep.
    change
      (In q
         (sss_step Bool.eqb
            (sss_edges (sss_compile (section4_example2_regex n))) p l))
      in Hstep.
    apply sss_step_edge_witness in Hstep as
      [[[src edge_l] dst] [Hedge [Hsrc [Hmatch Hdst]]]].
    simpl in Hsrc, Hdst. subst src dst.
    destruct edge_l as [b|], l as [a|]; simpl in Hmatch;
      try discriminate.
    - destruct b, a; simpl in Hmatch; try discriminate;
        rewrite section4_example2_compile_edges in Hedge;
        now apply section4_example2_edge_in_shape.
    - rewrite section4_example2_compile_edges in Hedge.
      now apply section4_example2_edge_in_shape.
  Qed.

  Ltac section4_example2_invert_step H :=
    apply section4_example2_step_shape in H;
    inversion H; subst; clear H.

  Ltac section4_example2_solve_step :=
    match goal with
    | |- In ?q
          (enfa_step (fenfa_base (section4_example2_m ?n)) ?p ?l) =>
        unfold section4_example2_m, regex_Msss;
        change
          (In q
             (sss_step Bool.eqb
                (sss_edges (sss_compile (section4_example2_regex n))) p l));
        apply sss_step_contains_edge;
        [ rewrite section4_example2_compile_edges;
          unfold section4_example2_edges, section4_example2_fixed_edges;
          simpl; auto 20
        | reflexivity ]
    end.

  Fixpoint section4_example2_star_word_loop (n : nat) (w : list bool)
      : enfa_trace (section4_example2_m n) :=
    match w with
    | [] => []
    | true :: w' =>
        section4_example2_trace_edge 4 (Some true) 5 ::
        section4_example2_trace_edge 5 None 4 ::
        section4_example2_star_word_loop n w'
    | false :: w' =>
        section4_example2_trace_edge 4 None 6 ::
        section4_example2_trace_edge 6 (Some false) 7 ::
        section4_example2_trace_edge 7 None 5 ::
        section4_example2_trace_edge 5 None 4 ::
        section4_example2_star_word_loop n w'
    end.

  Definition section4_example2_star_word_trace (n : nat) (w : list bool)
      : enfa_trace (section4_example2_m n) :=
    section4_example2_trace_edge 0 None 4 ::
    section4_example2_star_word_loop n w.

  Lemma section4_example2_star_word_loop_word :
    forall n w,
      trace_word (section4_example2_star_word_loop n w) = w.
  Proof.
    intros n w. induction w as [| [] w IH]; simpl; auto.
    - now rewrite IH.
    - now rewrite IH.
  Qed.

  Lemma section4_example2_star_word_trace_word :
    forall n w,
      trace_word (section4_example2_star_word_trace n w) = w.
  Proof.
    intros n w.
    unfold section4_example2_star_word_trace. simpl.
    apply section4_example2_star_word_loop_word.
  Qed.

  Lemma section4_example2_star_word_loop_valid :
    forall n w,
      valid_trace
        (section4_example2_m n) 4
        (section4_example2_star_word_loop n w) 4.
  Proof.
    intros n w. induction w as [| [] w IH]; simpl.
    - constructor.
    - econstructor.
      + section4_example2_solve_step.
      + econstructor.
        * section4_example2_solve_step.
        * exact IH.
    - econstructor.
      + section4_example2_solve_step.
      + econstructor.
        * section4_example2_solve_step.
        * econstructor.
          -- section4_example2_solve_step.
          -- econstructor.
             ++ section4_example2_solve_step.
             ++ exact IH.
  Qed.

  Lemma section4_example2_star_word_trace_valid :
    forall n w,
      valid_trace
        (section4_example2_m n) 0
        (section4_example2_star_word_trace n w) 4.
  Proof.
    intros n w.
    unfold section4_example2_star_word_trace. simpl.
    econstructor.
    - section4_example2_solve_step.
    - apply section4_example2_star_word_loop_valid.
  Qed.

  Lemma section4_example2_star_word_loop_end :
    forall n w,
      @trace_end bool (section4_example2_m n) 4
        (section4_example2_star_word_loop n w) = 4.
  Proof.
    intros n w. induction w as [| [] w IH]; simpl; auto.
  Qed.

  Lemma section4_example2_star_word_trace_end :
    forall n w,
      @trace_end bool (section4_example2_m n) 0
        (section4_example2_star_word_trace n w) = 4.
  Proof.
    intros n w.
    unfold section4_example2_star_word_trace. simpl.
    apply section4_example2_star_word_loop_end.
  Qed.

  Fixpoint section4_example2_star_true_loop (n k : nat)
      : enfa_trace (section4_example2_m n) :=
    match k with
    | O => []
    | S k' =>
        section4_example2_trace_edge 4 (Some true) 5 ::
        section4_example2_trace_edge 5 None 4 ::
        section4_example2_star_true_loop n k'
    end.

  Definition section4_example2_star_exit_trace (n k : nat)
      : enfa_trace (section4_example2_m n) :=
    section4_example2_trace_edge 0 None 4 ::
    section4_example2_star_true_loop n k ++
    [section4_example2_trace_edge 4 None 3].

  Definition section4_example2_star_b_trace (n k : nat)
      : enfa_trace (section4_example2_m n) :=
    section4_example2_trace_edge 0 None 4 ::
    section4_example2_star_true_loop n k ++
    [section4_example2_trace_edge 4 None 6].

  Lemma section4_example2_star_true_loop_word :
    forall n k,
      trace_word (section4_example2_star_true_loop n k) = repeat true k.
  Proof.
    intros n k. induction k as [| k IH]; simpl; auto.
    now rewrite IH.
  Qed.

  Lemma section4_example2_star_exit_trace_word :
    forall n k,
      trace_word (section4_example2_star_exit_trace n k) = repeat true k.
  Proof.
    intros n k.
    unfold section4_example2_star_exit_trace. simpl.
    rewrite trace_word_app.
    rewrite section4_example2_star_true_loop_word. simpl.
    now rewrite app_nil_r.
  Qed.

  Lemma section4_example2_star_b_trace_word :
    forall n k,
      trace_word (section4_example2_star_b_trace n k) = repeat true k.
  Proof.
    intros n k.
    unfold section4_example2_star_b_trace. simpl.
    rewrite trace_word_app.
    rewrite section4_example2_star_true_loop_word. simpl.
    now rewrite app_nil_r.
  Qed.

  Lemma section4_example2_star_true_loop_valid :
    forall n k,
      valid_trace
        (section4_example2_m n) 4
        (section4_example2_star_true_loop n k) 4.
  Proof.
    intros n k. induction k as [| k IH]; simpl.
    - constructor.
    - econstructor.
      + section4_example2_solve_step.
      + econstructor.
        * section4_example2_solve_step.
        * exact IH.
  Qed.

  Lemma section4_example2_star_exit_trace_valid :
    forall n k,
      valid_trace
        (section4_example2_m n) 0
        (section4_example2_star_exit_trace n k) 3.
  Proof.
    intros n k.
    unfold section4_example2_star_exit_trace. simpl.
    econstructor.
    - section4_example2_solve_step.
    - eapply valid_trace_app.
      + apply section4_example2_star_true_loop_valid.
      + econstructor.
        * section4_example2_solve_step.
        * constructor.
  Qed.

  Lemma section4_example2_star_b_trace_valid :
    forall n k,
      valid_trace
        (section4_example2_m n) 0
        (section4_example2_star_b_trace n k) 6.
  Proof.
    intros n k.
    unfold section4_example2_star_b_trace. simpl.
    econstructor.
    - section4_example2_solve_step.
    - eapply valid_trace_app.
      + apply section4_example2_star_true_loop_valid.
      + econstructor.
        * section4_example2_solve_step.
        * constructor.
  Qed.

  Lemma section4_example2_star_true_loop_simple_from :
    forall n k seen,
      epsilon_simpleb_from
        (section4_example2_m n) seen
        (section4_example2_star_true_loop n k) = true.
  Proof.
    intros n k.
    induction k as [| k IH]; intro seen; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma section4_example2_star_true_loop_eps3_simple_from :
    forall n k seen,
      seen = [4; 0] \/ seen = [4; 5] ->
      epsilon_simpleb_from
        (section4_example2_m n) seen
        (section4_example2_star_true_loop n k ++
         [section4_example2_trace_edge 4 None 3]) = true.
  Proof.
    intros n k.
    induction k as [| k IH]; intros seen Hseen; simpl.
    - destruct Hseen as [-> | ->]; reflexivity.
    - apply IH. right. reflexivity.
  Qed.

  Lemma section4_example2_star_true_loop_eps6_simple_from :
    forall n k seen,
      seen = [4; 0] \/ seen = [4; 5] ->
      epsilon_simpleb_from
        (section4_example2_m n) seen
        (section4_example2_star_true_loop n k ++
         [section4_example2_trace_edge 4 None 6]) = true.
  Proof.
    intros n k.
    induction k as [| k IH]; intros seen Hseen; simpl.
    - destruct Hseen as [-> | ->]; reflexivity.
    - apply IH. right. reflexivity.
  Qed.

  Lemma section4_example2_star_exit_trace_simple :
    forall n k,
      epsilon_simpleb
        (section4_example2_m n)
        (0, section4_example2_star_exit_trace n k) = true.
  Proof.
    intros n k.
    unfold epsilon_simpleb, section4_example2_star_exit_trace.
    simpl.
    apply section4_example2_star_true_loop_eps3_simple_from.
    left. reflexivity.
  Qed.

  Lemma section4_example2_star_b_trace_simple :
    forall n k,
      epsilon_simpleb
        (section4_example2_m n)
        (0, section4_example2_star_b_trace n k) = true.
  Proof.
    intros n k.
    unfold epsilon_simpleb, section4_example2_star_b_trace.
    simpl.
    apply section4_example2_star_true_loop_eps6_simple_from.
    left. reflexivity.
  Qed.

  Lemma section4_example2_star_true_loop_end :
    forall n k,
      @trace_end bool (section4_example2_m n) 4
        (section4_example2_star_true_loop n k) = 4.
  Proof.
    intros n k. induction k as [| k IH]; simpl; auto.
  Qed.

  Fixpoint section4_example2_suffix_word_path
      (n i : nat) (w : list bool) : enfa_trace (section4_example2_m n) :=
    match w with
    | [] => []
    | true :: w' =>
        section4_example2_trace_edge
          (section4_example2_checkpoint i) (Some true)
          (section4_example2_checkpoint (S i)) ::
        section4_example2_suffix_word_path n (S i) w'
    | false :: w' =>
        section4_example2_trace_edge
          (section4_example2_checkpoint i) None
          (section4_example2_suffix_b_entry i) ::
        section4_example2_trace_edge
          (section4_example2_suffix_b_entry i) (Some false)
          (section4_example2_suffix_b_exit i) ::
        section4_example2_trace_edge
          (section4_example2_suffix_b_exit i) None
          (section4_example2_checkpoint (S i)) ::
        section4_example2_suffix_word_path n (S i) w'
    end.

  Inductive section4_example2_suffix_nf (n : nat)
      : nat -> list bool -> nat -> enfa_trace (section4_example2_m n) ->
        Prop :=
  | Example2SuffixAtCheckpoint :
      forall i w,
        i + length w <= n ->
        section4_example2_suffix_nf n i w
          (section4_example2_checkpoint (i + length w))
          (section4_example2_suffix_word_path n i w)
  | Example2SuffixAtBEntry :
      forall i w,
        i + length w < n ->
        section4_example2_suffix_nf n i w
          (section4_example2_suffix_b_entry (i + length w))
          (section4_example2_suffix_word_path n i w ++
           [section4_example2_trace_edge
              (section4_example2_checkpoint (i + length w)) None
              (section4_example2_suffix_b_entry (i + length w))])
  | Example2SuffixAtBExit :
      forall i w,
        i + length w < n ->
        section4_example2_suffix_nf n i (w ++ [false])
          (section4_example2_suffix_b_exit (i + length w))
          (section4_example2_suffix_word_path n i w ++
           [ section4_example2_trace_edge
               (section4_example2_checkpoint (i + length w)) None
               (section4_example2_suffix_b_entry (i + length w));
             section4_example2_trace_edge
               (section4_example2_suffix_b_entry (i + length w)) (Some false)
               (section4_example2_suffix_b_exit (i + length w)) ])
  | Example2SuffixAtFinal :
      forall i w,
        i + length w = n ->
        section4_example2_suffix_nf n i w 1
          (section4_example2_suffix_word_path n i w ++
           [section4_example2_trace_edge
              (section4_example2_checkpoint n) None 1]).

  Inductive section4_example2_from4_nf (n : nat)
      : list bool -> nat -> enfa_trace (section4_example2_m n) -> Prop :=
  | Example2From4At4 :
      forall w,
        section4_example2_from4_nf n w 4
          (section4_example2_star_word_loop n w)
  | Example2From4At3 :
      forall w,
        section4_example2_from4_nf n w 3
          (section4_example2_star_word_loop n w ++
           [section4_example2_trace_edge 4 None 3])
  | Example2From4At6 :
      forall w,
        section4_example2_from4_nf n w 6
          (section4_example2_star_word_loop n w ++
           [section4_example2_trace_edge 4 None 6])
  | Example2From4At5True :
      forall prefix,
        section4_example2_from4_nf n (prefix ++ [true]) 5
          (section4_example2_star_word_loop n prefix ++
           [section4_example2_trace_edge 4 (Some true) 5])
  | Example2From4At7False :
      forall prefix,
        section4_example2_from4_nf n (prefix ++ [false]) 7
          (section4_example2_star_word_loop n prefix ++
           [ section4_example2_trace_edge 4 None 6;
             section4_example2_trace_edge 6 (Some false) 7 ])
  | Example2From4At5False :
      forall prefix,
        section4_example2_from4_nf n (prefix ++ [false]) 5
          (section4_example2_star_word_loop n prefix ++
           [ section4_example2_trace_edge 4 None 6;
             section4_example2_trace_edge 6 (Some false) 7;
             section4_example2_trace_edge 7 None 5 ])
  | Example2From4Suffix :
      forall prefix suffix q t,
        section4_example2_suffix_nf n 0 suffix q t ->
        section4_example2_from4_nf n (prefix ++ true :: suffix) q
          (section4_example2_star_word_loop n prefix ++
           [ section4_example2_trace_edge 4 None 3;
             section4_example2_trace_edge 3 (Some true)
               (section4_example2_checkpoint 0) ] ++ t).

  Inductive section4_example2_started_nf (n : nat)
      : list bool -> nat -> enfa_trace (section4_example2_m n) -> Prop :=
  | Example2StartedAtInitial :
      section4_example2_started_nf n [] 0 []
  | Example2StartedFrom4 :
      forall w q t,
        section4_example2_from4_nf n w q t ->
        section4_example2_started_nf n w q
          (section4_example2_trace_edge 0 None 4 :: t).

  Lemma section4_example2_suffix_word_path_word :
    forall n i w,
      trace_word (section4_example2_suffix_word_path n i w) = w.
  Proof.
    intros n i w. revert i.
    induction w as [| [] w IH]; intro i; simpl; auto.
    - now rewrite IH.
    - now rewrite IH.
  Qed.

  Lemma section4_example2_suffix_word_path_end :
    forall n i w,
      @trace_end bool (section4_example2_m n)
        (section4_example2_checkpoint i)
        (section4_example2_suffix_word_path n i w) =
      section4_example2_checkpoint (i + length w).
  Proof.
    intros n i w. revert i.
    induction w as [| [] w IH]; intro i; simpl.
    - now rewrite Nat.add_0_r.
    - change
        (@trace_end bool (section4_example2_m n)
           (section4_example2_checkpoint (S i))
           (section4_example2_suffix_word_path n (S i) w) =
         section4_example2_checkpoint (i + S (length w))).
      rewrite (IH (S i)).
      replace (S i + length w) with (i + S (length w)) by lia.
      reflexivity.
    - change
        (@trace_end bool (section4_example2_m n)
           (section4_example2_checkpoint (S i))
           (section4_example2_suffix_word_path n (S i) w) =
         section4_example2_checkpoint (i + S (length w))).
      rewrite (IH (S i)).
      replace (S i + length w) with (i + S (length w)) by lia.
      reflexivity.
  Qed.

  Lemma section4_example2_suffix_word_path_valid :
    forall n i w,
      i + length w <= n ->
      valid_trace
        (section4_example2_m n)
        (section4_example2_checkpoint i)
        (section4_example2_suffix_word_path n i w)
        (section4_example2_checkpoint (i + length w)).
  Proof.
    intros n i w. revert i.
    induction w as [| [] w IH]; intros i Hle; simpl.
    - rewrite Nat.add_0_r. constructor.
    - econstructor.
      + unfold section4_example2_m, regex_Msss.
        change
          (In (section4_example2_checkpoint (S i))
             (sss_step Bool.eqb
                (sss_edges (sss_compile (section4_example2_regex n)))
                (section4_example2_checkpoint i) (Some true))).
        apply sss_step_contains_edge.
        * rewrite section4_example2_compile_edges.
          assert (Hi : i < n) by (simpl in Hle; lia).
          exact (section4_example2_suffix_true_edge_in n i Hi).
        * reflexivity.
      + change
          (valid_trace
             (section4_example2_m n)
             (section4_example2_checkpoint (S i))
             (section4_example2_suffix_word_path n (S i) w)
             (section4_example2_checkpoint (i + S (length w)))).
        replace (i + S (length w)) with (S i + length w) by lia.
        apply IH. simpl in Hle; lia.
    - econstructor.
      + unfold section4_example2_m, regex_Msss.
        change
          (In (section4_example2_suffix_b_entry i)
             (sss_step Bool.eqb
                (sss_edges (sss_compile (section4_example2_regex n)))
                (section4_example2_checkpoint i) None)).
        apply sss_step_contains_edge.
        * rewrite section4_example2_compile_edges.
          assert (Hi : i < n) by (simpl in Hle; lia).
          exact (section4_example2_suffix_b_entry_edge_in n i Hi).
        * reflexivity.
      + econstructor.
        * unfold section4_example2_m, regex_Msss.
          change
            (In (section4_example2_suffix_b_exit i)
               (sss_step Bool.eqb
                  (sss_edges (sss_compile (section4_example2_regex n)))
                  (section4_example2_suffix_b_entry i) (Some false))).
          apply sss_step_contains_edge.
          -- rewrite section4_example2_compile_edges.
             assert (Hi : i < n) by (simpl in Hle; lia).
             exact (section4_example2_suffix_false_edge_in n i Hi).
          -- reflexivity.
        * econstructor.
          -- unfold section4_example2_m, regex_Msss.
             change
               (In (section4_example2_checkpoint (S i))
                  (sss_step Bool.eqb
                     (sss_edges (sss_compile (section4_example2_regex n)))
                     (section4_example2_suffix_b_exit i) None)).
             apply sss_step_contains_edge.
             ++ rewrite section4_example2_compile_edges.
                assert (Hi : i < n) by (simpl in Hle; lia).
                exact (section4_example2_suffix_b_exit_edge_in n i Hi).
             ++ reflexivity.
          -- change
               (valid_trace
                  (section4_example2_m n)
                  (section4_example2_checkpoint (S i))
                  (section4_example2_suffix_word_path n (S i) w)
                  (section4_example2_checkpoint (i + S (length w)))).
             replace (i + S (length w)) with (S i + length w) by lia.
             apply IH. simpl in Hle; lia.
  Qed.

  Lemma section4_example2_suffix_nf_transport :
    forall n i w q q' t t',
      q = q' ->
      t = t' ->
      section4_example2_suffix_nf n i w q t ->
      section4_example2_suffix_nf n i w q' t'.
  Proof.
    intros n i w q q' t t' -> -> Hnf. exact Hnf.
  Qed.

  Lemma section4_example2_suffix_nf_cons_true :
    forall n i w q t,
      section4_example2_suffix_nf n (S i) w q t ->
      section4_example2_suffix_nf n i (true :: w) q
        (section4_example2_trace_edge
           (section4_example2_checkpoint i) (Some true)
           (section4_example2_checkpoint (S i)) :: t).
  Proof.
    intros blocks i w q t Hnf.
    inversion Hnf; subst.
    - change
        (section4_example2_suffix_nf blocks i (true :: w)
           (section4_example2_checkpoint (S i + length w))
           (section4_example2_suffix_word_path blocks i (true :: w))).
      replace (S i + length w) with (i + length (true :: w))
        by (simpl; lia).
      constructor. simpl. lia.
    - change
        (section4_example2_suffix_nf blocks i (true :: w)
           (section4_example2_suffix_b_entry (S i + length w))
           (section4_example2_suffix_word_path blocks i (true :: w) ++
            [section4_example2_trace_edge
               (section4_example2_checkpoint (S i + length w)) None
               (section4_example2_suffix_b_entry (S i + length w))])).
      replace (S i + length w) with (i + length (true :: w))
        by (simpl; lia).
      constructor 2. simpl. lia.
    - replace (true :: w0 ++ [false]) with ((true :: w0) ++ [false])
        by reflexivity.
      change
        (section4_example2_suffix_nf blocks i ((true :: w0) ++ [false])
           (section4_example2_suffix_b_exit (S i + length w0))
           (section4_example2_suffix_word_path blocks i (true :: w0) ++
            [ section4_example2_trace_edge
                (section4_example2_checkpoint (S i + length w0)) None
                (section4_example2_suffix_b_entry (S i + length w0));
              section4_example2_trace_edge
                (section4_example2_suffix_b_entry (S i + length w0))
                (Some false)
                (section4_example2_suffix_b_exit (S i + length w0)) ])).
      replace (S i + length w0) with (i + length (true :: w0))
        by (simpl; lia).
      constructor 3. simpl. lia.
    - change
        (section4_example2_suffix_nf (S i + length w) i (true :: w) 1
           (section4_example2_suffix_word_path
              (S i + length w) i (true :: w) ++
            [section4_example2_trace_edge
               (section4_example2_checkpoint (S i + length w)) None 1])).
      constructor 4. simpl. lia.
  Qed.

  Lemma section4_example2_suffix_nf_cons_false :
    forall n i w q t,
      section4_example2_suffix_nf n (S i) w q t ->
      section4_example2_suffix_nf n i (false :: w) q
        (section4_example2_trace_edge
           (section4_example2_checkpoint i) None
           (section4_example2_suffix_b_entry i) ::
         section4_example2_trace_edge
           (section4_example2_suffix_b_entry i) (Some false)
           (section4_example2_suffix_b_exit i) ::
         section4_example2_trace_edge
           (section4_example2_suffix_b_exit i) None
           (section4_example2_checkpoint (S i)) :: t).
  Proof.
    intros blocks i w q t Hnf.
    inversion Hnf; subst.
    - change
        (section4_example2_suffix_nf blocks i (false :: w)
           (section4_example2_checkpoint (S i + length w))
           (section4_example2_suffix_word_path blocks i (false :: w))).
      replace (S i + length w) with (i + length (false :: w))
        by (simpl; lia).
      constructor. simpl. lia.
    - change
        (section4_example2_suffix_nf blocks i (false :: w)
           (section4_example2_suffix_b_entry (S i + length w))
           (section4_example2_suffix_word_path blocks i (false :: w) ++
            [section4_example2_trace_edge
               (section4_example2_checkpoint (S i + length w)) None
               (section4_example2_suffix_b_entry (S i + length w))])).
      replace (S i + length w) with (i + length (false :: w))
        by (simpl; lia).
      constructor 2. simpl. lia.
    - replace (false :: w0 ++ [false]) with ((false :: w0) ++ [false])
        by reflexivity.
      change
        (section4_example2_suffix_nf blocks i ((false :: w0) ++ [false])
           (section4_example2_suffix_b_exit (S i + length w0))
           (section4_example2_suffix_word_path blocks i (false :: w0) ++
            [ section4_example2_trace_edge
                (section4_example2_checkpoint (S i + length w0)) None
                (section4_example2_suffix_b_entry (S i + length w0));
              section4_example2_trace_edge
                (section4_example2_suffix_b_entry (S i + length w0))
                (Some false)
                (section4_example2_suffix_b_exit (S i + length w0)) ])).
      replace (S i + length w0) with (i + length (false :: w0))
        by (simpl; lia).
      constructor 3. simpl. lia.
    - change
        (section4_example2_suffix_nf (S i + length w) i (false :: w) 1
           (section4_example2_suffix_word_path
              (S i + length w) i (false :: w) ++
            [section4_example2_trace_edge
               (section4_example2_checkpoint (S i + length w)) None 1])).
      constructor 4. simpl. lia.
  Qed.

  Lemma section4_example2_from4_nf_cons_true_loop :
    forall n w q t,
      section4_example2_from4_nf n w q t ->
      section4_example2_from4_nf n (true :: w) q
        (section4_example2_trace_edge 4 (Some true) 5 ::
         section4_example2_trace_edge 5 None 4 :: t).
  Proof.
    intros n w q t Hnf.
    inversion Hnf; subst; simpl.
    - constructor.
    - constructor.
    - constructor.
    - replace (true :: prefix ++ [true])
        with ((true :: prefix) ++ [true]) by reflexivity.
      constructor 4.
    - replace (true :: prefix ++ [false])
        with ((true :: prefix) ++ [false]) by reflexivity.
      constructor 5.
    - replace (true :: prefix ++ [false])
        with ((true :: prefix) ++ [false]) by reflexivity.
      constructor 6.
    - replace (true :: prefix ++ true :: suffix)
        with ((true :: prefix) ++ true :: suffix) by reflexivity.
      match goal with
      | Hsuffix : section4_example2_suffix_nf n 0 suffix q ?tail |- _ =>
          change
            (section4_example2_from4_nf n
               ((true :: prefix) ++ true :: suffix) q
               (section4_example2_star_word_loop n (true :: prefix) ++
                [ section4_example2_trace_edge 4 None 3;
                  section4_example2_trace_edge 3 (Some true)
                    (section4_example2_checkpoint 0) ] ++ tail));
          econstructor 7; exact Hsuffix
      end.
  Qed.

  Lemma section4_example2_from4_nf_cons_false_loop :
    forall n w q t,
      section4_example2_from4_nf n w q t ->
      section4_example2_from4_nf n (false :: w) q
        (section4_example2_trace_edge 4 None 6 ::
         section4_example2_trace_edge 6 (Some false) 7 ::
         section4_example2_trace_edge 7 None 5 ::
         section4_example2_trace_edge 5 None 4 :: t).
  Proof.
    intros n w q t Hnf.
    inversion Hnf; subst; simpl.
    - constructor.
    - constructor.
    - constructor.
    - replace (false :: prefix ++ [true])
        with ((false :: prefix) ++ [true]) by reflexivity.
      constructor 4.
    - replace (false :: prefix ++ [false])
        with ((false :: prefix) ++ [false]) by reflexivity.
      constructor 5.
    - replace (false :: prefix ++ [false])
        with ((false :: prefix) ++ [false]) by reflexivity.
      constructor 6.
    - replace (false :: prefix ++ true :: suffix)
        with ((false :: prefix) ++ true :: suffix) by reflexivity.
      match goal with
      | Hsuffix : section4_example2_suffix_nf n 0 suffix q ?tail |- _ =>
          change
            (section4_example2_from4_nf n
               ((false :: prefix) ++ true :: suffix) q
               (section4_example2_star_word_loop n (false :: prefix) ++
                [ section4_example2_trace_edge 4 None 3;
                  section4_example2_trace_edge 3 (Some true)
                    (section4_example2_checkpoint 0) ] ++ tail));
          econstructor 7; exact Hsuffix
      end.
  Qed.

  Fixpoint section4_example2_suffix_true_path
      (n i k : nat) : enfa_trace (section4_example2_m n) :=
    match k with
    | O => []
    | S k' =>
        section4_example2_trace_edge
          (section4_example2_checkpoint i) (Some true)
          (section4_example2_checkpoint (S i)) ::
        section4_example2_suffix_true_path n (S i) k'
    end.

  Definition section4_example2_accept_attack_trace (n : nat)
      : enfa_trace (section4_example2_m n) :=
    [ section4_example2_trace_edge 0 None 4;
      section4_example2_trace_edge 4 None 3;
      section4_example2_trace_edge 3 (Some true) 2 ] ++
    section4_example2_suffix_true_path n 0 n ++
    [ section4_example2_trace_edge
        (section4_example2_checkpoint n) None 1 ].

  Definition section4_example2_suffix_b_attack_trace (n i : nat)
      : enfa_trace (section4_example2_m n) :=
    section4_example2_trace_edge 0 None 4 ::
    section4_example2_star_true_loop n (n - i) ++
    [ section4_example2_trace_edge 4 None 3;
      section4_example2_trace_edge 3 (Some true) 2 ] ++
    section4_example2_suffix_true_path n 0 i ++
    [ section4_example2_trace_edge
        (section4_example2_checkpoint i) None
        (section4_example2_suffix_b_entry i) ].

  Lemma section4_example2_suffix_true_path_word :
    forall n i k,
      trace_word (section4_example2_suffix_true_path n i k) =
      repeat true k.
  Proof.
    intros n i k.
    revert i.
    induction k as [| k IH]; intro i; simpl.
    - reflexivity.
    - now rewrite IH.
  Qed.

  Lemma section4_example2_suffix_true_path_end :
    forall n i k,
      @trace_end bool (section4_example2_m n)
        (section4_example2_checkpoint i)
        (section4_example2_suffix_true_path n i k) =
      section4_example2_checkpoint (i + k).
  Proof.
    intros n i k.
    revert i.
    induction k as [| k IH]; intro i; simpl.
    - now rewrite Nat.add_0_r.
    - change
        (S (S (S (S (S (S (S (S (i + (i + (i + 0)))))))))))
        with (section4_example2_checkpoint (S i)).
      rewrite (IH (S i)).
      replace (S i + k) with (i + S k) by lia.
      reflexivity.
  Qed.

  Lemma section4_example2_suffix_true_path_valid :
    forall n i k,
      i + k <= n ->
      valid_trace
        (section4_example2_m n)
        (section4_example2_checkpoint i)
        (section4_example2_suffix_true_path n i k)
        (section4_example2_checkpoint (i + k)).
  Proof.
    intros n i k.
    revert i.
    induction k as [| k IH]; intros i Hle; simpl.
    - rewrite Nat.add_0_r. constructor.
    - econstructor.
      + unfold section4_example2_m, regex_Msss.
        change
          (In (section4_example2_checkpoint (S i))
             (sss_step Bool.eqb
                (sss_edges (sss_compile (section4_example2_regex n)))
                (section4_example2_checkpoint i) (Some true))).
        apply sss_step_contains_edge.
        * rewrite section4_example2_compile_edges.
          apply section4_example2_suffix_true_edge_in.
          lia.
        * reflexivity.
      + change
          (valid_trace
             (section4_example2_m n)
             (section4_example2_checkpoint (S i))
             (section4_example2_suffix_true_path n (S i) k)
             (section4_example2_checkpoint (i + S k))).
        replace (i + S k) with (S i + k) by lia.
        apply IH. lia.
  Qed.

  Lemma section4_example2_suffix_true_path_simple_from :
    forall n i k seen,
      epsilon_simpleb_from
        (section4_example2_m n) seen
        (section4_example2_suffix_true_path n i k) = true.
  Proof.
    intros n i k.
    revert i.
    induction k as [| k IH]; intros i seen; simpl.
    - reflexivity.
    - apply IH.
  Qed.

  Lemma section4_example2_suffix_true_path_suffix_states :
    forall n i k seen,
      epsilon_suffix_states
        (section4_example2_m n) seen
        (section4_example2_suffix_true_path n i k) =
      match k with
      | O => seen
      | S _ => [section4_example2_checkpoint (i + k)]
      end.
  Proof.
    intros n i k.
    revert i.
    induction k as [| k IH]; intros i seen; simpl.
    - reflexivity.
    - destruct k as [| k].
      + replace (i + 1) with (S i) by lia.
        reflexivity.
      + rewrite IH.
        replace (S i + S k) with (i + S (S k)) by lia.
        reflexivity.
  Qed.

  Lemma section4_example2_state_inb_singleton_false :
    forall n dst q,
      dst <> q ->
      state_inb (section4_example2_m n) dst [q] = false.
  Proof.
    intros n dst q Hneq.
    unfold state_inb. simpl.
    destruct (Nat.eqb dst q) eqn:Heq; simpl; auto.
    apply Nat.eqb_eq in Heq. contradiction.
  Qed.

  Lemma section4_example2_suffix_true_path_eps_simple_from :
    forall n i k dst seen,
      dst <> section4_example2_checkpoint (i + k) ->
      (k = 0 ->
       state_inb (section4_example2_m n) dst seen = false) ->
      epsilon_simpleb_from
        (section4_example2_m n) seen
        (section4_example2_suffix_true_path n i k ++
         [section4_example2_trace_edge
            (section4_example2_checkpoint (i + k)) None dst]) = true.
  Proof.
    intros n i k dst seen Hdst Hseen.
    apply epsilon_simpleb_from_app_none.
    - apply section4_example2_suffix_true_path_simple_from.
    - rewrite section4_example2_suffix_true_path_suffix_states.
      destruct k as [| k].
      + apply Hseen. reflexivity.
      + apply section4_example2_state_inb_singleton_false.
        exact Hdst.
  Qed.

  Lemma section4_example2_suffix_true_path_to_1_simple_from :
    forall n,
      epsilon_simpleb_from
        (section4_example2_m n) [section4_example2_checkpoint 0]
        (section4_example2_suffix_true_path n 0 n ++
         [section4_example2_trace_edge
            (section4_example2_checkpoint n) None 1]) = true.
  Proof.
    intro n.
    replace n with (0 + n) at 2 by lia.
    apply section4_example2_suffix_true_path_eps_simple_from.
    - destruct n; simpl; lia.
    - intro Hn. subst n. reflexivity.
  Qed.

  Lemma section4_example2_suffix_true_path_to_b_entry_simple_from :
    forall n i,
      epsilon_simpleb_from
        (section4_example2_m n) [section4_example2_checkpoint 0]
        (section4_example2_suffix_true_path n 0 i ++
         [section4_example2_trace_edge
            (section4_example2_checkpoint i) None
            (section4_example2_suffix_b_entry i)]) = true.
  Proof.
    intros n i.
    replace i with (0 + i) at 2 by lia.
    apply section4_example2_suffix_true_path_eps_simple_from.
    - replace (0 + i) with i by lia.
      unfold section4_example2_suffix_b_entry,
        section4_example2_checkpoint.
      destruct i; simpl; lia.
    - intro Hi. subst i. reflexivity.
  Qed.

  Lemma section4_example2_star_true_loop_eps3_then_simple_from :
    forall n k seen rest,
      seen = [4; 0] \/ seen = [4; 5] ->
      epsilon_simpleb_from
        (section4_example2_m n) [section4_example2_checkpoint 0] rest = true ->
      epsilon_simpleb_from
        (section4_example2_m n) seen
        (section4_example2_star_true_loop n k ++
         [ section4_example2_trace_edge 4 None 3;
           section4_example2_trace_edge 3 (Some true)
             (section4_example2_checkpoint 0) ] ++ rest) = true.
  Proof.
    intros n k.
    induction k as [| k IH]; intros seen rest Hseen Hrest; simpl.
    - destruct Hseen as [-> | ->]; exact Hrest.
    - apply IH.
      + right. reflexivity.
      + exact Hrest.
  Qed.

  Lemma section4_example2_accept_attack_trace_word :
    forall n,
      trace_word (section4_example2_accept_attack_trace n) =
      section4_example2_attack_word n.
  Proof.
    intro n.
    unfold section4_example2_accept_attack_trace,
      section4_example2_attack_word.
    simpl.
    rewrite trace_word_app.
    rewrite section4_example2_suffix_true_path_word. simpl.
    now rewrite app_nil_r.
  Qed.

  Lemma section4_example2_suffix_b_attack_trace_word :
    forall n i,
      i <= n ->
      trace_word (section4_example2_suffix_b_attack_trace n i) =
      section4_example2_attack_word n.
  Proof.
    intros n i Hi.
    unfold section4_example2_suffix_b_attack_trace,
      section4_example2_attack_word.
    simpl.
    repeat rewrite trace_word_app.
    rewrite section4_example2_star_true_loop_word.
    assert (Hsuffix :
      @trace_word bool (section4_example2_m n)
        (section4_example2_trace_edge 4 None 3 ::
         section4_example2_trace_edge 3 (Some true) 2 ::
         section4_example2_suffix_true_path n 0 i ++
         [section4_example2_trace_edge
            (section4_example2_checkpoint i) None
            (section4_example2_suffix_b_entry i)]) =
      true :: repeat true i).
    {
      simpl.
      rewrite trace_word_app.
      rewrite section4_example2_suffix_true_path_word.
      simpl. now rewrite app_nil_r.
    }
    rewrite Hsuffix.
    simpl.
    repeat rewrite app_nil_r.
    replace (repeat true (n - i) ++ true :: repeat true i)
      with (repeat true (n - i + S i)).
    2:{ symmetry. rewrite repeat_app. reflexivity. }
    replace (n - i + S i) with (S n) by lia.
    reflexivity.
  Qed.

  Lemma section4_example2_accept_attack_trace_valid :
    forall n,
      valid_trace
        (section4_example2_m n) 0
        (section4_example2_accept_attack_trace n) 1.
  Proof.
    intro n.
    unfold section4_example2_accept_attack_trace. simpl.
    econstructor.
    - section4_example2_solve_step.
    - econstructor.
      + section4_example2_solve_step.
      + econstructor.
        * section4_example2_solve_step.
        * eapply valid_trace_app.
          -- change 2 with (section4_example2_checkpoint 0).
             replace n with (0 + n) at 2 by lia.
             apply section4_example2_suffix_true_path_valid.
             lia.
          -- econstructor.
             ++ unfold section4_example2_m, regex_Msss.
                change
                  (In 1
                     (sss_step Bool.eqb
                        (sss_edges
                           (sss_compile (section4_example2_regex n)))
                        (section4_example2_checkpoint n) None)).
                apply sss_step_contains_edge.
                ** rewrite section4_example2_compile_edges.
                   apply section4_example2_suffix_final_edge_in.
                ** reflexivity.
             ++ constructor.
  Qed.

  Lemma section4_example2_suffix_b_attack_trace_valid :
    forall n i,
      i < n ->
      valid_trace
        (section4_example2_m n) 0
        (section4_example2_suffix_b_attack_trace n i)
        (section4_example2_suffix_b_entry i).
  Proof.
    intros n i Hi.
    unfold section4_example2_suffix_b_attack_trace. simpl.
    econstructor.
    - section4_example2_solve_step.
    - eapply valid_trace_app.
      + apply section4_example2_star_true_loop_valid.
      + simpl.
        econstructor.
        * section4_example2_solve_step.
        * econstructor.
          -- section4_example2_solve_step.
          -- eapply valid_trace_app.
             ++ change 2 with (section4_example2_checkpoint 0).
                replace i with (0 + i) at 2 by lia.
                apply section4_example2_suffix_true_path_valid.
                lia.
             ++ econstructor.
                ** unfold section4_example2_m, regex_Msss.
                   change
                     (In (section4_example2_suffix_b_entry i)
                        (sss_step Bool.eqb
                           (sss_edges
                              (sss_compile (section4_example2_regex n)))
                           (section4_example2_checkpoint i) None)).
                   apply sss_step_contains_edge.
                   --- rewrite section4_example2_compile_edges.
                       apply section4_example2_suffix_b_entry_edge_in.
                       exact Hi.
                   --- reflexivity.
                ** constructor.
  Qed.

  Lemma section4_example2_accept_attack_trace_end :
    forall n,
      @trace_end bool (section4_example2_m n) 0
        (section4_example2_accept_attack_trace n) = 1.
  Proof.
    intro n.
    unfold section4_example2_accept_attack_trace. simpl.
    rewrite trace_end_app.
    change 2 with (section4_example2_checkpoint 0).
    rewrite section4_example2_suffix_true_path_end.
    rewrite Nat.add_0_l. reflexivity.
  Qed.

  Lemma section4_example2_suffix_b_attack_trace_end :
    forall n i,
      @trace_end bool (section4_example2_m n) 0
        (section4_example2_suffix_b_attack_trace n i) =
      section4_example2_suffix_b_entry i.
  Proof.
    intros n i.
    unfold section4_example2_suffix_b_attack_trace. simpl.
    repeat rewrite trace_end_app.
    rewrite section4_example2_star_true_loop_end.
    simpl.
    change 2 with (section4_example2_checkpoint 0).
    rewrite trace_end_app.
    rewrite section4_example2_suffix_true_path_end.
    rewrite Nat.add_0_l. reflexivity.
  Qed.

  Lemma section4_example2_accept_attack_trace_simple :
    forall n,
      epsilon_simpleb
        (section4_example2_m n)
        (0, section4_example2_accept_attack_trace n) = true.
  Proof.
    intro n.
    unfold epsilon_simpleb, section4_example2_accept_attack_trace.
    simpl.
    apply section4_example2_suffix_true_path_to_1_simple_from.
  Qed.

  Lemma section4_example2_suffix_b_attack_trace_simple :
    forall n i,
      epsilon_simpleb
        (section4_example2_m n)
        (0, section4_example2_suffix_b_attack_trace n i) = true.
  Proof.
    intros n i.
    unfold epsilon_simpleb, section4_example2_suffix_b_attack_trace.
    simpl.
    apply section4_example2_star_true_loop_eps3_then_simple_from.
    - left. reflexivity.
    - apply section4_example2_suffix_true_path_to_b_entry_simple_from.
  Qed.

  Lemma section4_example2_star_exit_trace_end :
    forall n k,
      @trace_end bool (section4_example2_m n) 0
        (section4_example2_star_exit_trace n k) = 3.
  Proof.
    intros n k.
    unfold section4_example2_star_exit_trace. simpl.
    rewrite trace_end_app.
    rewrite section4_example2_star_true_loop_end.
    reflexivity.
  Qed.

  Lemma section4_example2_star_b_trace_end :
    forall n k,
      @trace_end bool (section4_example2_m n) 0
        (section4_example2_star_b_trace n k) = 6.
  Proof.
    intros n k.
    unfold section4_example2_star_b_trace. simpl.
    rewrite trace_end_app.
    rewrite section4_example2_star_true_loop_end.
    reflexivity.
  Qed.

  Lemma section4_example2_no_epsilon_from_3 :
    forall n,
      enfa_step (fenfa_base (section4_example2_m n)) 3 None = [].
  Proof.
    intros n.
    destruct (enfa_step (fenfa_base (section4_example2_m n)) 3 None)
      as [| q qs] eqn:Hstep; [reflexivity |].
    exfalso.
    assert (Hin : In q (q :: qs)).
    { simpl; auto. }
    rewrite <- Hstep in Hin.
    apply section4_example2_step_shape in Hin.
    inversion Hin; subst; simpl in *; try discriminate; try lia;
      match goal with
      | H : 3 = section4_example2_checkpoint ?i |- _ =>
          destruct i; simpl in H; lia
      | H : section4_example2_checkpoint ?i = 3 |- _ =>
          destruct i; simpl in H; lia
      | H : 3 = section4_example2_suffix_b_entry ?i |- _ =>
          simpl in H; lia
      | H : section4_example2_suffix_b_entry ?i = 3 |- _ =>
          simpl in H; lia
      | H : 3 = section4_example2_suffix_b_exit ?i |- _ =>
          simpl in H; lia
      | H : section4_example2_suffix_b_exit ?i = 3 |- _ =>
          simpl in H; lia
      | H : context [section4_example2_checkpoint ?i] |- _ =>
          destruct i; simpl in H; lia
      | H : context [section4_example2_suffix_b_entry ?i] |- _ =>
          simpl in H; lia
      | H : context [section4_example2_suffix_b_exit ?i] |- _ =>
          simpl in H; lia
      end.
  Qed.

  Lemma section4_example2_no_epsilon_from_by_shape :
    forall n p,
      (forall q, ~ section4_example2_edge_shape n p None q) ->
      enfa_step (fenfa_base (section4_example2_m n)) p None = [].
  Proof.
    intros n p Hnone.
    destruct (enfa_step (fenfa_base (section4_example2_m n)) p None)
      as [| q qs] eqn:Hstep; [reflexivity |].
    exfalso.
    assert (Hin : In q (q :: qs)).
    { simpl; auto. }
    rewrite <- Hstep in Hin.
    apply section4_example2_step_shape in Hin.
    exact (Hnone q Hin).
  Qed.

  Lemma section4_example2_checkpoint_inj :
    forall i j,
      section4_example2_checkpoint i = section4_example2_checkpoint j ->
      i = j.
  Proof.
    intros [| i] [| j] H; simpl in H; try lia.
  Qed.

  Lemma section4_example2_suffix_b_entry_inj :
    forall i j,
      section4_example2_suffix_b_entry i =
      section4_example2_suffix_b_entry j ->
      i = j.
  Proof.
    intros i j H.
    unfold section4_example2_suffix_b_entry in H. lia.
  Qed.

  Lemma section4_example2_suffix_b_exit_inj :
    forall i j,
      section4_example2_suffix_b_exit i =
      section4_example2_suffix_b_exit j ->
      i = j.
  Proof.
    intros i j H.
    unfold section4_example2_suffix_b_exit in H. lia.
  Qed.

  Lemma section4_example2_checkpoint_neq_b_entry :
    forall i j,
      section4_example2_checkpoint i <>
      section4_example2_suffix_b_entry j.
  Proof.
    intros [| i] j H; unfold section4_example2_suffix_b_entry in H;
      simpl in H; lia.
  Qed.

  Lemma section4_example2_checkpoint_neq_b_exit :
    forall i j,
      section4_example2_checkpoint i <>
      section4_example2_suffix_b_exit j.
  Proof.
    intros [| i] j H; unfold section4_example2_suffix_b_exit in H;
      simpl in H; lia.
  Qed.

  Lemma section4_example2_suffix_b_entry_neq_b_exit :
    forall i j,
      section4_example2_suffix_b_entry i <>
      section4_example2_suffix_b_exit j.
  Proof.
    intros i j H.
    unfold section4_example2_suffix_b_entry,
      section4_example2_suffix_b_exit in H. lia.
  Qed.

  Ltac section4_example2_discharge_state_neq :=
    simpl in *; try discriminate; try lia;
    repeat match goal with
    | H : ?x = ?x |- _ => clear H
    | H : 0 = section4_example2_checkpoint ?i |- _ =>
        destruct i; simpl in H; lia
    | H : section4_example2_checkpoint ?i = 0 |- _ =>
        destruct i; simpl in H; lia
    | H : 3 = section4_example2_checkpoint ?i |- _ =>
        destruct i; simpl in H; lia
    | H : section4_example2_checkpoint ?i = 3 |- _ =>
        destruct i; simpl in H; lia
    | H : 4 = section4_example2_checkpoint ?i |- _ =>
        destruct i; simpl in H; lia
    | H : section4_example2_checkpoint ?i = 4 |- _ =>
        destruct i; simpl in H; lia
    | H : 5 = section4_example2_checkpoint ?i |- _ =>
        destruct i; simpl in H; lia
    | H : section4_example2_checkpoint ?i = 5 |- _ =>
        destruct i; simpl in H; lia
    | H : 6 = section4_example2_checkpoint ?i |- _ =>
        destruct i; simpl in H; lia
    | H : section4_example2_checkpoint ?i = 6 |- _ =>
        destruct i; simpl in H; lia
    | H : 7 = section4_example2_checkpoint ?i |- _ =>
        destruct i; simpl in H; lia
    | H : section4_example2_checkpoint ?i = 7 |- _ =>
        destruct i; simpl in H; lia
    | H : 0 = section4_example2_suffix_b_entry ?i |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : section4_example2_suffix_b_entry ?i = 0 |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : 3 = section4_example2_suffix_b_entry ?i |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : section4_example2_suffix_b_entry ?i = 3 |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : 4 = section4_example2_suffix_b_entry ?i |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : section4_example2_suffix_b_entry ?i = 4 |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : 5 = section4_example2_suffix_b_entry ?i |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : section4_example2_suffix_b_entry ?i = 5 |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : 6 = section4_example2_suffix_b_entry ?i |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : section4_example2_suffix_b_entry ?i = 6 |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : 7 = section4_example2_suffix_b_entry ?i |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : section4_example2_suffix_b_entry ?i = 7 |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : 0 = section4_example2_suffix_b_exit ?i |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_suffix_b_exit ?i = 0 |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : 3 = section4_example2_suffix_b_exit ?i |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_suffix_b_exit ?i = 3 |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : 4 = section4_example2_suffix_b_exit ?i |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_suffix_b_exit ?i = 4 |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : 5 = section4_example2_suffix_b_exit ?i |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_suffix_b_exit ?i = 5 |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : 6 = section4_example2_suffix_b_exit ?i |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_suffix_b_exit ?i = 6 |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : 7 = section4_example2_suffix_b_exit ?i |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_suffix_b_exit ?i = 7 |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_checkpoint ?i =
          section4_example2_checkpoint ?j |- _ =>
        apply section4_example2_checkpoint_inj in H; subst
    | H : section4_example2_suffix_b_entry ?i =
          section4_example2_suffix_b_entry ?j |- _ =>
        apply section4_example2_suffix_b_entry_inj in H; subst
    | H : section4_example2_suffix_b_exit ?i =
          section4_example2_suffix_b_exit ?j |- _ =>
        apply section4_example2_suffix_b_exit_inj in H; subst
    | H : 1 = section4_example2_checkpoint ?i |- _ =>
        destruct i; simpl in H; lia
    | H : section4_example2_checkpoint ?i = 1 |- _ =>
        destruct i; simpl in H; lia
    | H : 1 = section4_example2_suffix_b_entry ?i |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : section4_example2_suffix_b_entry ?i = 1 |- _ =>
        unfold section4_example2_suffix_b_entry in H; lia
    | H : 1 = section4_example2_suffix_b_exit ?i |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_suffix_b_exit ?i = 1 |- _ =>
        unfold section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_suffix_b_entry ?i =
          section4_example2_checkpoint ?j |- _ =>
        unfold section4_example2_suffix_b_entry,
          section4_example2_checkpoint in H;
        destruct j; simpl in H; lia
    | H : section4_example2_checkpoint ?j =
          section4_example2_suffix_b_entry ?i |- _ =>
        unfold section4_example2_suffix_b_entry,
          section4_example2_checkpoint in H;
        destruct j; simpl in H; lia
    | H : section4_example2_suffix_b_exit ?i =
          section4_example2_checkpoint ?j |- _ =>
        exfalso;
        apply (section4_example2_checkpoint_neq_b_exit j i);
        symmetry; exact H
    | H : section4_example2_checkpoint ?j =
          section4_example2_suffix_b_exit ?i |- _ =>
        exfalso;
        apply (section4_example2_checkpoint_neq_b_exit j i);
        exact H
    | H : section4_example2_suffix_b_entry ?i =
          section4_example2_suffix_b_exit ?j |- _ =>
        unfold section4_example2_suffix_b_entry,
          section4_example2_suffix_b_exit in H; lia
    | H : section4_example2_suffix_b_exit ?j =
          section4_example2_suffix_b_entry ?i |- _ =>
        unfold section4_example2_suffix_b_entry,
          section4_example2_suffix_b_exit in H; lia
    end.

  Lemma section4_example2_no_epsilon_from_1 :
    forall n,
      enfa_step (fenfa_base (section4_example2_m n)) 1 None = [].
  Proof.
    intro n.
    apply section4_example2_no_epsilon_from_by_shape.
    intros q Hshape.
    inversion Hshape; subst; section4_example2_discharge_state_neq.
  Qed.

  Lemma section4_example2_no_epsilon_from_suffix_b_entry :
    forall n i,
      enfa_step
        (fenfa_base (section4_example2_m n))
        (section4_example2_suffix_b_entry i) None = [].
  Proof.
    intros n i.
    apply section4_example2_no_epsilon_from_by_shape.
    intros q Hshape.
    inversion Hshape; subst; section4_example2_discharge_state_neq.
  Qed.

  Lemma section4_example2_no_epsilon_from_6 :
    forall n,
      enfa_step (fenfa_base (section4_example2_m n)) 6 None = [].
  Proof.
    intros n.
    destruct (enfa_step (fenfa_base (section4_example2_m n)) 6 None)
      as [| q qs] eqn:Hstep; [reflexivity |].
    exfalso.
    assert (Hin : In q (q :: qs)).
    { simpl; auto. }
    rewrite <- Hstep in Hin.
    apply section4_example2_step_shape in Hin.
    inversion Hin; subst; simpl in *; try discriminate; try lia;
      match goal with
      | H : 6 = section4_example2_checkpoint ?i |- _ =>
          destruct i; simpl in H; lia
      | H : section4_example2_checkpoint ?i = 6 |- _ =>
          destruct i; simpl in H; lia
      | H : 6 = section4_example2_suffix_b_entry ?i |- _ =>
          simpl in H; lia
      | H : section4_example2_suffix_b_entry ?i = 6 |- _ =>
          simpl in H; lia
      | H : 6 = section4_example2_suffix_b_exit ?i |- _ =>
          simpl in H; lia
      | H : section4_example2_suffix_b_exit ?i = 6 |- _ =>
          simpl in H; lia
      | H : context [section4_example2_checkpoint ?i] |- _ =>
          destruct i; simpl in H; lia
      | H : context [section4_example2_suffix_b_entry ?i] |- _ =>
          simpl in H; lia
      | H : context [section4_example2_suffix_b_exit ?i] |- _ =>
          simpl in H; lia
      end.
  Qed.

  Lemma section4_example2_valid_from_1_nil :
    forall n t q,
      valid_trace (section4_example2_m n) 1 t q ->
      t = [] /\ q = 1.
  Proof.
    intros n t q Hvalid.
    inversion Hvalid; subst; auto.
    exfalso.
    apply section4_example2_step_shape in H.
    inversion H; subst; section4_example2_discharge_state_neq.
  Qed.

  Lemma section4_example2_valid_from_b_entry_inv :
    forall n i t q,
      valid_trace
        (section4_example2_m n)
        (section4_example2_suffix_b_entry i) t q ->
      (t = [] /\ q = section4_example2_suffix_b_entry i) \/
      (i < n /\
       exists u,
         t =
           section4_example2_trace_edge
             (section4_example2_suffix_b_entry i) (Some false)
             (section4_example2_suffix_b_exit i) :: u /\
         valid_trace
           (section4_example2_m n)
           (section4_example2_suffix_b_exit i) u q).
  Proof.
    intros n i t q Hvalid.
    inversion Hvalid; subst; auto.
    right.
    apply section4_example2_step_shape in H.
    inversion H; subst; section4_example2_discharge_state_neq.
    repeat match goal with
    | Hneq : section4_example2_suffix_b_entry ?x =
             section4_example2_suffix_b_entry ?y |- _ =>
        apply section4_example2_suffix_b_entry_inj in Hneq; subst
    end.
    assert (i0 = i) by lia. subst i0.
    split; [lia |].
    exists t0. split; [reflexivity | assumption].
  Qed.

  Lemma section4_example2_valid_from_b_exit_inv :
    forall n i t q,
      valid_trace
        (section4_example2_m n)
        (section4_example2_suffix_b_exit i) t q ->
      (t = [] /\ q = section4_example2_suffix_b_exit i) \/
      (i < n /\
       exists u,
         t =
           section4_example2_trace_edge
             (section4_example2_suffix_b_exit i) None
             (section4_example2_checkpoint (S i)) :: u /\
         valid_trace
           (section4_example2_m n)
           (section4_example2_checkpoint (S i)) u q).
  Proof.
    intros n i t q Hvalid.
    inversion Hvalid; subst; auto.
    right.
    apply section4_example2_step_shape in H.
    inversion H; subst; section4_example2_discharge_state_neq.
    repeat match goal with
    | Hneq : section4_example2_suffix_b_exit ?x =
             section4_example2_suffix_b_exit ?y |- _ =>
        apply section4_example2_suffix_b_exit_inj in Hneq; subst
    end.
    assert (i0 = i) by lia. subst i0.
    split; [lia |].
    exists t0. split; [reflexivity | assumption].
  Qed.

  Lemma section4_example2_valid_from_3_inv :
    forall n t q,
      valid_trace (section4_example2_m n) 3 t q ->
      (t = [] /\ q = 3) \/
      exists u,
        t =
          section4_example2_trace_edge 3 (Some true)
            (section4_example2_checkpoint 0) :: u /\
        valid_trace
          (section4_example2_m n) (section4_example2_checkpoint 0) u q.
  Proof.
    intros n t q Hvalid.
    inversion Hvalid; subst; auto.
    right.
    apply section4_example2_step_shape in H.
    inversion H; subst; section4_example2_discharge_state_neq.
    exists t0. split; [reflexivity | assumption].
  Qed.

  Lemma section4_example2_valid_from_5_inv :
    forall n t q,
      valid_trace (section4_example2_m n) 5 t q ->
      (t = [] /\ q = 5) \/
      exists u,
        t =
          section4_example2_trace_edge 5 None 4 :: u /\
        valid_trace (section4_example2_m n) 4 u q.
  Proof.
    intros n t q Hvalid.
    inversion Hvalid; subst; auto.
    right.
    apply section4_example2_step_shape in H.
    inversion H; subst; section4_example2_discharge_state_neq.
    exists t0. split; [reflexivity | assumption].
  Qed.

  Lemma section4_example2_valid_from_6_inv :
    forall n t q,
      valid_trace (section4_example2_m n) 6 t q ->
      (t = [] /\ q = 6) \/
      exists u,
        t =
          section4_example2_trace_edge 6 (Some false) 7 :: u /\
        valid_trace (section4_example2_m n) 7 u q.
  Proof.
    intros n t q Hvalid.
    inversion Hvalid; subst; auto.
    right.
    apply section4_example2_step_shape in H.
    inversion H; subst; section4_example2_discharge_state_neq.
    exists t0. split; [reflexivity | assumption].
  Qed.

  Lemma section4_example2_valid_from_7_inv :
    forall n t q,
      valid_trace (section4_example2_m n) 7 t q ->
      (t = [] /\ q = 7) \/
      exists u,
        t =
          section4_example2_trace_edge 7 None 5 :: u /\
        valid_trace (section4_example2_m n) 5 u q.
  Proof.
    intros n t q Hvalid.
    inversion Hvalid; subst; auto.
    right.
    apply section4_example2_step_shape in H.
    inversion H; subst; section4_example2_discharge_state_neq.
    exists t0. split; [reflexivity | assumption].
  Qed.

  Lemma section4_example2_suffix_nf_complete_fuel :
    forall fuel n i t q,
      length t <= fuel ->
      i <= n ->
      valid_trace
        (section4_example2_m n) (section4_example2_checkpoint i) t q ->
      section4_example2_suffix_nf n i (trace_word t) q t.
  Proof.
    induction fuel as [| fuel IH];
      intros n i t q Hlen Hi Hvalid.
    - destruct t as [| e t']; simpl in Hlen; [| lia].
      inversion Hvalid; subst.
      simpl.
      replace (section4_example2_checkpoint i)
        with (section4_example2_checkpoint (i + length ([] : list bool)))
        by (simpl; rewrite Nat.add_0_r; reflexivity).
      replace ([] : enfa_trace (section4_example2_m n))
        with (section4_example2_suffix_word_path n i ([] : list bool))
        by reflexivity.
      apply Example2SuffixAtCheckpoint. simpl. lia.
    - inversion Hvalid; subst.
      + simpl.
        replace (section4_example2_checkpoint i)
          with (section4_example2_checkpoint (i + length ([] : list bool)))
          by (simpl; rewrite Nat.add_0_r; reflexivity).
        replace ([] : enfa_trace (section4_example2_m n))
          with (section4_example2_suffix_word_path n i ([] : list bool))
          by reflexivity.
        apply Example2SuffixAtCheckpoint. simpl. lia.
      + apply section4_example2_step_shape in H.
        inversion H; subst; section4_example2_discharge_state_neq.
        * apply section4_example2_suffix_nf_cons_true.
          eapply IH; eauto; simpl in Hlen; lia.
        * match goal with
          | Htail : valid_trace
                (section4_example2_m n)
                (section4_example2_suffix_b_entry i) ?tail q |- _ =>
              destruct
                (section4_example2_valid_from_b_entry_inv n i tail q Htail)
                as [[Ht Hq] | [Hi_lt [u [Ht Hu]]]]
          end.
          -- subst. simpl.
             change
               (section4_example2_suffix_nf n i ([] : list bool)
                  (section4_example2_suffix_b_entry i)
                  (section4_example2_suffix_word_path n i ([] : list bool) ++
                   [section4_example2_trace_edge
                      (section4_example2_checkpoint i) None
                      (section4_example2_suffix_b_entry i)])).
             replace (section4_example2_suffix_b_entry i)
               with
                 (section4_example2_suffix_b_entry
                    (i + length ([] : list bool)))
               by (simpl; rewrite Nat.add_0_r; reflexivity).
             replace (section4_example2_checkpoint i)
               with
                 (section4_example2_checkpoint
                    (i + length ([] : list bool)))
               by (simpl; rewrite Nat.add_0_r; reflexivity).
             apply Example2SuffixAtBEntry. simpl. lia.
          -- subst.
             destruct
               (section4_example2_valid_from_b_exit_inv n i u q Hu)
               as [[Hu_nil Hq] | [_ [v [Hu_eq Hv]]]].
             ++ subst. simpl.
                change
                  (section4_example2_suffix_nf n i
                     (([] : list bool) ++ [false])
                     (section4_example2_suffix_b_exit i)
                     (section4_example2_suffix_word_path
                        n i ([] : list bool) ++
                      [ section4_example2_trace_edge
                          (section4_example2_checkpoint i) None
                          (section4_example2_suffix_b_entry i);
                        section4_example2_trace_edge
                          (section4_example2_suffix_b_entry i) (Some false)
                          (section4_example2_suffix_b_exit i) ])).
                replace (section4_example2_suffix_b_exit i)
                  with
                    (section4_example2_suffix_b_exit
                       (i + length ([] : list bool)))
                  by (simpl; rewrite Nat.add_0_r; reflexivity).
                replace (section4_example2_checkpoint i)
                  with
                    (section4_example2_checkpoint
                       (i + length ([] : list bool)))
                  by (simpl; rewrite Nat.add_0_r; reflexivity).
                replace (section4_example2_suffix_b_entry i)
                  with
                    (section4_example2_suffix_b_entry
                       (i + length ([] : list bool)))
                  by (simpl; rewrite Nat.add_0_r; reflexivity).
                constructor 3. simpl. lia.
             ++ subst u. simpl.
                apply section4_example2_suffix_nf_cons_false.
                eapply IH; eauto; simpl in Hlen; lia.
        * match goal with
          | Htail : valid_trace (section4_example2_m ?blocks) 1 ?tail q |- _ =>
              apply section4_example2_valid_from_1_nil in Htail as [Ht Hq]
          end.
          subst. simpl.
          constructor 4. simpl. lia.
  Qed.

  Lemma section4_example2_suffix_nf_complete :
    forall n i t q,
      i <= n ->
      valid_trace
        (section4_example2_m n) (section4_example2_checkpoint i) t q ->
      section4_example2_suffix_nf n i (trace_word t) q t.
  Proof.
    intros n i t q Hi Hvalid.
    eapply section4_example2_suffix_nf_complete_fuel; eauto.
  Qed.

  Lemma section4_example2_from4_nf_complete_fuel :
    forall fuel n t q,
      length t <= fuel ->
      valid_trace (section4_example2_m n) 4 t q ->
      section4_example2_from4_nf n (trace_word t) q t.
  Proof.
    induction fuel as [| fuel IH]; intros n t q Hlen Hvalid.
    - destruct t as [| e t']; simpl in Hlen; [| lia].
      inversion Hvalid; subst. constructor.
    - inversion Hvalid; subst.
      + constructor.
      + apply section4_example2_step_shape in H.
        inversion H; subst; section4_example2_discharge_state_neq.
        * match goal with
          | Htail : valid_trace (section4_example2_m n) 3 ?tail q |- _ =>
              destruct (section4_example2_valid_from_3_inv n tail q Htail)
                as [[Ht Hq] | [u [Ht Hu]]]
          end.
          -- subst. simpl. constructor 2.
          -- subst. simpl.
             change
               (section4_example2_from4_nf n
                  (([] : list bool) ++
                   true :: trace_word (u : enfa_trace (section4_example2_m n))) q
                  (section4_example2_star_word_loop n ([] : list bool) ++
                   [ section4_example2_trace_edge 4 None 3;
                     section4_example2_trace_edge 3 (Some true)
                       (section4_example2_checkpoint 0) ] ++
                   (u : enfa_trace (section4_example2_m n)))).
             econstructor 7.
             eapply section4_example2_suffix_nf_complete; eauto.
             lia.
        * match goal with
          | Htail : valid_trace (section4_example2_m n) 5 ?tail q |- _ =>
              destruct (section4_example2_valid_from_5_inv n tail q Htail)
                as [[Ht Hq] | [u [Ht Hu]]]
          end.
          -- subst. simpl.
             replace [true] with ([] ++ [true]) by reflexivity.
             constructor 4.
          -- subst. simpl.
             apply section4_example2_from4_nf_cons_true_loop.
             eapply IH; eauto; simpl in Hlen; lia.
        * match goal with
          | Htail : valid_trace (section4_example2_m n) 6 ?tail q |- _ =>
              destruct (section4_example2_valid_from_6_inv n tail q Htail)
                as [[Ht Hq] | [u [Ht Hu]]]
          end.
          -- subst. simpl. constructor 3.
          -- subst.
             destruct (section4_example2_valid_from_7_inv n u q Hu)
               as [[Hu_nil Hq] | [v [Hu_eq Hv]]].
             ++ subst. simpl.
                replace [false] with ([] ++ [false]) by reflexivity.
                constructor 5.
             ++ subst u.
                destruct (section4_example2_valid_from_5_inv n v q Hv)
                  as [[Hv_nil Hq] | [r [Hv_eq Hr]]].
                ** subst. simpl.
                   replace [false] with ([] ++ [false]) by reflexivity.
                   constructor 6.
                ** subst v. simpl.
                   apply section4_example2_from4_nf_cons_false_loop.
                   eapply IH; eauto; simpl in Hlen; lia.
  Qed.

  Lemma section4_example2_from4_nf_complete :
    forall n t q,
      valid_trace (section4_example2_m n) 4 t q ->
      section4_example2_from4_nf n (trace_word t) q t.
  Proof.
    intros n t q Hvalid.
    eapply section4_example2_from4_nf_complete_fuel; eauto.
  Qed.

  Lemma section4_example2_started_nf_complete :
    forall n t q,
      valid_trace (section4_example2_m n) 0 t q ->
      section4_example2_started_nf n (trace_word t) q t.
  Proof.
    intros n t q Hvalid.
    inversion Hvalid; subst.
    - constructor.
    - apply section4_example2_step_shape in H.
      inversion H; subst; section4_example2_discharge_state_neq.
      simpl. constructor.
      now apply section4_example2_from4_nf_complete.
  Qed.

  Lemma section4_app_cons_eq_of_tail_length :
    forall {B : Type} (xs ys : list B) a zs ws,
      length zs = length ws ->
      xs ++ a :: zs = ys ++ a :: ws ->
      xs = ys /\ zs = ws.
  Proof.
    intros B xs.
    induction xs as [| x xs IH]; intros [| y ys] a zs ws Hlen Heq;
      simpl in Heq.
    - inversion Heq; subst. auto.
    - exfalso.
      inversion Heq; subst.
      rewrite length_app in Hlen. simpl in Hlen. lia.
    - exfalso.
      inversion Heq; subst.
      rewrite length_app in Hlen. simpl in Hlen. lia.
    - inversion Heq; subst.
      match goal with
      | Htail : xs ++ a :: zs = ys ++ a :: ws |- _ =>
          destruct (IH ys a zs ws Hlen Htail) as [Hxs Hzs]
      end.
      subst. auto.
  Qed.

  Lemma section4_last_app_singleton :
    forall {B : Type} (xs : list B) a d,
      last (xs ++ [a]) d = a.
  Proof.
    intros B xs a d.
    induction xs as [| x xs IH]; simpl; auto.
    destruct xs; simpl in *; auto.
  Qed.

  Lemma section4_app_true_false_absurd :
    forall xs ys,
      xs ++ [true] = ys ++ [false] -> False.
  Proof.
    intros xs ys Heq.
    pose proof (f_equal (@rev bool) Heq) as Hrev.
    repeat rewrite rev_app_distr in Hrev.
    simpl in Hrev.
    discriminate Hrev.
  Qed.

  Ltac section4_example2_tail_eqs :=
    repeat match goal with
    | H : ?xs ++ [?a] = ?ys ++ [?a] |- _ =>
        apply app_inv_tail in H; subst
    | H : ?xs ++ [true] = ?ys ++ [false] |- _ =>
        exfalso; exact (section4_app_true_false_absurd xs ys H)
    | H : ?xs ++ [false] = ?ys ++ [true] |- _ =>
        symmetry in H;
        exfalso; exact (section4_app_true_false_absurd ys xs H)
    end.

  Lemma section4_example2_suffix_nf_endpoint_length :
    forall n i w1 w2 q t1 t2,
      section4_example2_suffix_nf n i w1 q t1 ->
      section4_example2_suffix_nf n i w2 q t2 ->
      length w1 = length w2.
  Proof.
    intros n i w1 w2 q t1 t2 H1 H2.
    inversion H1; subst; inversion H2; subst;
      section4_example2_discharge_state_neq;
      repeat rewrite length_app; simpl; lia.
  Qed.

  Lemma section4_example2_suffix_nf_functional :
    forall n i w q t1 t2,
      section4_example2_suffix_nf n i w q t1 ->
      section4_example2_suffix_nf n i w q t2 ->
      t1 = t2.
  Proof.
    intros n i w q t1 t2 H1 H2.
    inversion H1; subst; inversion H2; subst;
      try solve [section4_example2_discharge_state_neq].
    - reflexivity.
    - reflexivity.
    - section4_example2_tail_eqs. reflexivity.
    - reflexivity.
  Qed.

  Lemma section4_example2_suffix_split_unique :
    forall n prefix1 suffix1 prefix2 suffix2 q t1 t2,
      prefix1 ++ true :: suffix1 = prefix2 ++ true :: suffix2 ->
      section4_example2_suffix_nf n 0 suffix1 q t1 ->
      section4_example2_suffix_nf n 0 suffix2 q t2 ->
      prefix1 = prefix2 /\ suffix1 = suffix2 /\ t1 = t2.
  Proof.
    intros n prefix1 suffix1 prefix2 suffix2 q t1 t2
      Hword Hnf1 Hnf2.
    pose proof
      (section4_example2_suffix_nf_endpoint_length
         n 0 suffix1 suffix2 q t1 t2 Hnf1 Hnf2) as Hlen.
    destruct
      (section4_app_cons_eq_of_tail_length
         prefix1 prefix2 true suffix1 suffix2 Hlen Hword)
      as [Hprefix Hsuffix].
    subst.
    repeat split.
    now eapply section4_example2_suffix_nf_functional; eauto.
  Qed.

  Lemma section4_example2_from4_nf_functional :
    forall n w q t1 t2,
      section4_example2_from4_nf n w q t1 ->
      section4_example2_from4_nf n w q t2 ->
      t1 = t2.
  Proof.
    intros n w q t1 t2 H1 H2.
    inversion H1; subst; inversion H2; subst;
      try solve [section4_example2_discharge_state_neq];
      try solve
        [match goal with
         | Hnf : section4_example2_suffix_nf _ _ _ 3 _ |- _ =>
             inversion Hnf; subst; section4_example2_discharge_state_neq
         | Hnf : section4_example2_suffix_nf _ _ _ 4 _ |- _ =>
             inversion Hnf; subst; section4_example2_discharge_state_neq
         | Hnf : section4_example2_suffix_nf _ _ _ 5 _ |- _ =>
             inversion Hnf; subst; section4_example2_discharge_state_neq
         | Hnf : section4_example2_suffix_nf _ _ _ 6 _ |- _ =>
             inversion Hnf; subst; section4_example2_discharge_state_neq
         | Hnf : section4_example2_suffix_nf _ _ _ 7 _ |- _ =>
             inversion Hnf; subst; section4_example2_discharge_state_neq
         end];
      try solve
        [match goal with
         | Hword : ?p1 ++ true :: ?s1 = ?p2 ++ true :: ?s2,
           Hnf1 : section4_example2_suffix_nf n 0 ?s1 q ?u1,
           Hnf2 : section4_example2_suffix_nf n 0 ?s2 q ?u2 |- _ =>
             destruct
               (section4_example2_suffix_split_unique
                  n p1 s1 p2 s2 q u1 u2 Hword Hnf1 Hnf2)
               as [-> [-> ->]];
              reflexivity
         end];
      try solve [section4_example2_tail_eqs; reflexivity].
  Qed.

  Lemma section4_example2_started_nf_functional :
    forall n w q t1 t2,
      section4_example2_started_nf n w q t1 ->
      section4_example2_started_nf n w q t2 ->
      t1 = t2.
  Proof.
    intros n w q t1 t2 H1 H2.
    inversion H1; subst; inversion H2; subst;
      try solve [section4_example2_discharge_state_neq];
      try solve
        [match goal with
         | Hnf : section4_example2_from4_nf _ _ 0 _ |- _ =>
             inversion Hnf; subst; section4_example2_discharge_state_neq;
             match goal with
             | Hsuffix : section4_example2_suffix_nf _ _ _ 0 _ |- _ =>
                 inversion Hsuffix; subst; section4_example2_discharge_state_neq
             end
         end].
    - reflexivity.
    - f_equal.
      eapply section4_example2_from4_nf_functional; eauto.
  Qed.

  Lemma section4_example2_star_exit_trace_maximal :
    forall n k,
      maximal_epsilon_simpleb
        (section4_example2_m n)
        (0, section4_example2_star_exit_trace n k) = true.
  Proof.
    intros n k.
    unfold maximal_epsilon_simpleb, started_end,
      section4_example2_star_exit_trace.
    cbn [fst snd trace_end].
    rewrite trace_end_app.
    rewrite section4_example2_star_true_loop_end.
    rewrite section4_example2_no_epsilon_from_3.
    reflexivity.
  Qed.

  Lemma section4_example2_star_b_trace_maximal :
    forall n k,
      maximal_epsilon_simpleb
        (section4_example2_m n)
        (0, section4_example2_star_b_trace n k) = true.
  Proof.
    intros n k.
    unfold maximal_epsilon_simpleb, started_end,
      section4_example2_star_b_trace.
    cbn [fst snd trace_end].
    rewrite trace_end_app.
    rewrite section4_example2_star_true_loop_end.
    rewrite section4_example2_no_epsilon_from_6.
    reflexivity.
  Qed.

  Lemma section4_example2_accept_attack_trace_accepting_maximal :
    forall n,
      enfa_accepting_maximal_epsilon_simpleb
        (section4_example2_m n)
        (0, section4_example2_accept_attack_trace n) = true.
  Proof.
    intro n.
    unfold enfa_accepting_maximal_epsilon_simpleb,
      enfa_strict_epsilon_closure_states, started_end.
    rewrite section4_example2_accept_attack_trace_end.
    rewrite section4_example2_no_epsilon_from_1.
    simpl.
    rewrite enfa_epsilon_closure_fuel_empty_todo.
    reflexivity.
  Qed.

  Lemma section4_example2_suffix_b_attack_trace_maximal :
    forall n i,
      maximal_epsilon_simpleb
        (section4_example2_m n)
        (0, section4_example2_suffix_b_attack_trace n i) = true.
  Proof.
    intros n i.
    unfold maximal_epsilon_simpleb, started_end.
    cbn [fst snd].
    rewrite section4_example2_suffix_b_attack_trace_end.
    rewrite section4_example2_no_epsilon_from_suffix_b_entry.
    reflexivity.
  Qed.

  Lemma section4_example2_accept_attack_trace_maximal :
    forall n,
      maximal_epsilon_simpleb
        (section4_example2_m n)
        (0, section4_example2_accept_attack_trace n) = true.
  Proof.
    intro n.
    unfold maximal_epsilon_simpleb, started_end.
    cbn [fst snd].
    rewrite section4_example2_accept_attack_trace_end.
    rewrite section4_example2_no_epsilon_from_1.
    reflexivity.
  Qed.

  Lemma section4_example2_maximal_false_of_fresh_epsilon :
    forall n (st : started_trace (section4_example2_m n)) q',
      In q'
        (enfa_step
           (fenfa_base (section4_example2_m n)) (started_end st) None) ->
      state_inb
        (section4_example2_m n) q'
        (epsilon_suffix_states
           (section4_example2_m n) [fst st] (snd st)) = false ->
      maximal_epsilon_simpleb (section4_example2_m n) st = false.
  Proof.
    intros n st q' Hstep Hfresh.
    unfold maximal_epsilon_simpleb.
    destruct
      (forallb
         (fun q0 : enfa_state (fenfa_base (section4_example2_m n)) =>
            state_inb
              (section4_example2_m n) q0
              (epsilon_suffix_states
                 (section4_example2_m n) [fst st] (snd st)))
         (enfa_step
            (fenfa_base (section4_example2_m n)) (started_end st) None))
      eqn:Hforall; auto.
    apply forallb_forall with (x := q') in Hforall; auto.
    rewrite Hfresh in Hforall. discriminate.
  Qed.

  Lemma section4_example2_star_word_loop_all_true :
    forall n k,
      section4_example2_star_word_loop n (repeat true k) =
      section4_example2_star_true_loop n k.
  Proof.
    intros n k.
    induction k as [| k IH]; simpl; now rewrite ?IH.
  Qed.

  Lemma section4_example2_star_true_loop_suffix_states :
    forall n k seen,
      epsilon_suffix_states
        (section4_example2_m n) seen
        (section4_example2_star_true_loop n k) =
      match k with
      | O => seen
      | S _ => [4; 5]
      end.
  Proof.
    intros n k.
    induction k as [| k IH]; intro seen; simpl; auto.
    destruct k as [| k]; simpl in *; auto.
  Qed.

  Lemma section4_example2_star_word_loop_then_true_suffix_states :
    forall n prefix seen,
      epsilon_suffix_states
        (section4_example2_m n) seen
        (section4_example2_star_word_loop n prefix ++
         [section4_example2_trace_edge 4 (Some true) 5]) = [5].
  Proof.
    intros n prefix.
    induction prefix as [| [] prefix IH]; intro seen; simpl; auto.
  Qed.

  Lemma section4_example2_suffix_word_path_extra_seen_false :
    forall n i w dst extra,
      dst <> extra ->
      state_inb
        (section4_example2_m n) dst
        (epsilon_suffix_states
           (section4_example2_m n)
           [section4_example2_checkpoint i]
           (section4_example2_suffix_word_path n i w)) = false ->
      state_inb
        (section4_example2_m n) dst
        (epsilon_suffix_states
           (section4_example2_m n)
           [section4_example2_checkpoint i; extra]
           (section4_example2_suffix_word_path n i w)) = false.
  Proof.
    intros n i w dst extra Hneq Hbase.
    destruct w as [| [] w]; simpl in *; auto.
    change
      (state_inb
         (section4_example2_m n) dst
         [section4_example2_checkpoint i] = false) in Hbase.
    change
      (state_inb
         (section4_example2_m n) dst
         [section4_example2_checkpoint i; extra] = false).
    apply state_inb_not_In_false.
    apply state_inb_false_not_In in Hbase.
    intros [Hin | [Hin | []]].
    - apply Hbase. simpl. auto.
    - symmetry in Hin. contradiction.
  Qed.

  Lemma section4_example2_suffix_word_path_no_b_entry_seen :
    forall n i w,
      state_inb
        (section4_example2_m n)
        (section4_example2_suffix_b_entry (i + length w))
        (epsilon_suffix_states
           (section4_example2_m n)
           [section4_example2_checkpoint i]
           (section4_example2_suffix_word_path n i w)) = false.
  Proof.
    intros n i w.
    revert i.
    induction w as [| [] w IH]; intro i; simpl.
    - replace (i + 0) with i by lia.
      change
        (state_inb
           (section4_example2_m n)
           (section4_example2_suffix_b_entry i)
           [section4_example2_checkpoint i] = false).
      apply section4_example2_state_inb_singleton_false.
      intro H.
      now apply (section4_example2_checkpoint_neq_b_entry i i).
    - replace (i + S (length w)) with (S i + length w) by lia.
      apply IH.
    - replace (i + S (length w)) with (S i + length w) by lia.
      change
        (state_inb
           (section4_example2_m n)
           (section4_example2_suffix_b_entry (S i + length w))
           (epsilon_suffix_states
              (section4_example2_m n)
              [section4_example2_checkpoint (S i);
               section4_example2_suffix_b_exit i]
              (section4_example2_suffix_word_path n (S i) w)) =
         false).
      apply section4_example2_suffix_word_path_extra_seen_false.
      + unfold section4_example2_suffix_b_entry,
          section4_example2_suffix_b_exit. lia.
      + apply IH.
  Qed.

  Lemma section4_example2_suffix_word_path_no_final_seen :
    forall n i w,
      state_inb
        (section4_example2_m n) 1
        (epsilon_suffix_states
           (section4_example2_m n)
           [section4_example2_checkpoint i]
           (section4_example2_suffix_word_path n i w)) = false.
  Proof.
    intros n i w.
    revert i.
    induction w as [| [] w IH]; intro i; simpl.
    - change
        (state_inb
           (section4_example2_m n) 1
           [section4_example2_checkpoint i] = false).
      apply section4_example2_state_inb_singleton_false.
      intro H.
      destruct i; simpl in H; lia.
    - change
        (state_inb
           (section4_example2_m n) 1
           (epsilon_suffix_states
              (section4_example2_m n)
              [section4_example2_checkpoint (S i)]
              (section4_example2_suffix_word_path n (S i) w)) =
         false).
      apply IH.
    - change
        (state_inb
           (section4_example2_m n) 1
           (epsilon_suffix_states
              (section4_example2_m n)
              [section4_example2_checkpoint (S i);
               section4_example2_suffix_b_exit i]
              (section4_example2_suffix_word_path n (S i) w)) =
         false).
      apply section4_example2_suffix_word_path_extra_seen_false.
      + unfold section4_example2_suffix_b_exit. lia.
      + apply IH.
  Qed.

  Lemma section4_example2_from4_suffix_word_path_suffix_states :
    forall n prefix suffix,
      epsilon_suffix_states
        (section4_example2_m n) [0]
        (section4_example2_trace_edge 0 None 4 ::
         (section4_example2_star_word_loop n prefix ++
          [ section4_example2_trace_edge 4 None 3;
            section4_example2_trace_edge 3 (Some true)
              (section4_example2_checkpoint 0) ] ++
          section4_example2_suffix_word_path n 0 suffix)) =
      epsilon_suffix_states
        (section4_example2_m n)
        [section4_example2_checkpoint 0]
        (section4_example2_suffix_word_path n 0 suffix).
  Proof.
    intros n prefix suffix.
    assert
      (Hgen :
         forall seen,
           epsilon_suffix_states
             (section4_example2_m n) seen
             (section4_example2_star_word_loop n prefix ++
              [ section4_example2_trace_edge 4 None 3;
                section4_example2_trace_edge 3 (Some true)
                  (section4_example2_checkpoint 0) ] ++
              section4_example2_suffix_word_path n 0 suffix) =
           epsilon_suffix_states
             (section4_example2_m n)
             [section4_example2_checkpoint 0]
             (section4_example2_suffix_word_path n 0 suffix)).
    { induction prefix as [| [] prefix IH]; intro seen; simpl; auto. }
    simpl.
    apply Hgen.
  Qed.

  Lemma section4_example2_m_start :
    forall n, enfa_start (fenfa_base (section4_example2_m n)) = [0].
  Proof.
    reflexivity.
  Qed.

  Lemma section4_example2_m_final :
    forall n q,
      enfa_final (fenfa_base (section4_example2_m n)) q = Nat.eqb q 1.
  Proof.
    intros n q.
    unfold section4_example2_m, regex_Msss, sss_compile.
    simpl. rewrite sss_compile_between_final_eq. reflexivity.
  Qed.

  Lemma section4_example2_unique_terminating_state :
    forall n, enfa_unique_terminating_state (section4_example2_m n).
  Proof.
    intro n.
    exists 1.
    repeat split.
    - replace 1 with (sss_final (sss_compile (section4_example2_regex n))).
      + unfold section4_example2_m, regex_Msss.
        apply sss_final_in_states.
      + unfold sss_compile. rewrite sss_compile_final_eq. reflexivity.
    - apply section4_example2_m_final.
    - intros q Hq Hfinal.
      rewrite section4_example2_m_final in Hfinal.
      now apply Nat.eqb_eq in Hfinal.
  Qed.

  Lemma section4_example2_symbol_closed :
    forall n,
      regex_symbol_closed
        [true; false] Bool.eqb (section4_example2_regex n).
  Proof.
    intros n b a _ Hmatch.
    destruct b, a; simpl in Hmatch; try discriminate; simpl; auto.
  Qed.

  Example section4_example2_m_wf :
    forall n, finite_enfa_wf (section4_example2_m n).
  Proof.
    intro n. apply regex_Msss_wf.
    apply section4_example2_symbol_closed.
  Qed.

  Lemma filter_length_le_one_of_NoDup_unique :
    forall {B : Type} (p : B -> bool) xs,
      NoDup xs ->
      (forall x y, In x xs -> In y xs -> p x = true -> p y = true ->
        x = y) ->
      length (filter p xs) <= 1.
  Proof.
    intros B p xs Hnodup Hunique.
    induction Hnodup as [| x xs Hnotin Hnodup IH]; simpl.
    - lia.
    - destruct (p x) eqn:Hpx.
      + rewrite
          (filter_false_nil p xs
             (fun y Hy =>
                match p y as b return p y = b -> p y = false with
                | true =>
                    fun Hpy =>
                      False_rect _
                        (Hnotin
                           (eq_ind y (fun z => In z xs) Hy x
                              (eq_sym
                                 (Hunique x y
                                    (or_introl eq_refl) (or_intror Hy)
                                    Hpx Hpy))))
                | false => fun Hpy => Hpy
                end eq_refl)).
        simpl. lia.
      + apply IH.
        intros y z Hy Hz Hpy Hpz.
        apply Hunique; simpl; auto.
  Qed.

  Lemma section4_example2_started_trace_start_eq :
    forall n w s t,
      In (s, t) (started_traces (section4_example2_m n) w) ->
      s = 0.
  Proof.
    intros n w s t Hin.
    pose proof (started_traces_start_in
                  (section4_example2_m n) w s t Hin) as Hstart.
    rewrite section4_example2_m_start in Hstart.
    simpl in Hstart. destruct Hstart as [Hstart | []].
    symmetry. exact Hstart.
  Qed.

  Lemma section4_example2_dra_prime_unique_trace :
    forall n w q st1 st2,
      In st1 (started_traces (section4_example2_m n) w) ->
      In st2 (started_traces (section4_example2_m n) w) ->
      (ends_inb (section4_example2_m n) q st1 &&
       epsilon_simpleb (section4_example2_m n) st1) = true ->
      (ends_inb (section4_example2_m n) q st2 &&
       epsilon_simpleb (section4_example2_m n) st2) = true ->
      st1 = st2.
  Proof.
    intros n w q [s1 t1] [s2 t2] Hin1 Hin2 Hf1 Hf2.
    apply andb_true_iff in Hf1 as [Hend1 _].
    apply andb_true_iff in Hf2 as [Hend2 _].
    unfold ends_inb, started_end in Hend1, Hend2; simpl in Hend1, Hend2.
    apply Nat.eqb_eq in Hend1.
    apply Nat.eqb_eq in Hend2.
    subst q.
    destruct (started_traces_valid
                (section4_example2_m n) w s1 t1 Hin1)
      as [Hvalid1 Hword1].
    destruct (started_traces_valid
                (section4_example2_m n) w s2 t2 Hin2)
      as [Hvalid2 Hword2].
    pose proof (section4_example2_started_trace_start_eq n w s1 t1 Hin1)
      as Hs1.
    pose proof (section4_example2_started_trace_start_eq n w s2 t2 Hin2)
      as Hs2.
    subst s1 s2.
    assert (Hnf1 :
      section4_example2_started_nf n w
        (@trace_end bool (section4_example2_m n) 0 t1) t1).
    {
      rewrite <- Hword1.
      apply section4_example2_started_nf_complete.
      exact Hvalid1.
    }
    assert (Hnf2_raw :
      section4_example2_started_nf n w
        (@trace_end bool (section4_example2_m n) 0 t2) t2).
    {
      rewrite <- Hword2.
      apply section4_example2_started_nf_complete.
      exact Hvalid2.
    }
    rewrite Hend2 in Hnf2_raw.
    pose proof Hnf2_raw as Hnf2.
    f_equal.
    eapply section4_example2_started_nf_functional; eauto.
  Qed.

  Theorem section4_example2_m_reachufa :
    forall n, enfa_ReachUFA (section4_example2_m n).
  Proof.
    intros n w q _.
    unfold enfa_dra_prime_at.
    apply filter_length_le_one_of_NoDup_unique.
    - eapply started_traces_single_start_NoDup.
      + apply section4_example2_m_wf.
      + apply section4_example2_m_start.
    - intros st1 st2 Hin1 Hin2 Hf1 Hf2.
      eapply section4_example2_dra_prime_unique_trace; eauto.
  Qed.

  Theorem section4_example2_m_ufa :
    forall n, enfa_UFA (section4_example2_m n).
  Proof.
    intro n.
    eapply section4_theorem2_reachufa_unique_terminating_state_implies_ufa.
    - apply section4_example2_m_wf.
    - apply section4_example2_m_reachufa.
    - apply section4_example2_unique_terminating_state.
  Qed.

  Theorem section4_example2_gamma_terminal_lr1 :
    forall n,
      gamma_terminal_lr1 Bool.bool_dec (section4_example2_m n) 0.
  Proof.
    intro n.
    pose proof
      (section4_theorem5_terminal_lr1_iff_ufa_reachufa
         Bool.bool_dec (section4_example2_m n) 0) as Hiff.
    specialize
      (Hiff
         (section4_example2_m_wf n)
         (section4_example2_m_start n)).
    assert (Henum :
      enfa_prime_trace_enumerated_from (section4_example2_m n) 0).
    {
      eapply section4_enfa_prime_trace_enumerated_from_single_start.
      - apply section4_example2_m_wf.
      - apply section4_example2_m_start.
    }
    assert (Hnodup :
      enfa_started_traces_nodup (section4_example2_m n)).
    {
      eapply section4_enfa_started_traces_nodup_single_start.
      - apply section4_example2_m_wf.
      - apply section4_example2_m_start.
    }
    specialize (Hiff Henum Hnodup).
    apply (proj2 Hiff).
    split.
    - apply section4_example2_m_ufa.
    - apply section4_example2_m_reachufa.
  Qed.

  Lemma section4_example2_star_exit_attack_started :
    forall n,
      In
        (0, section4_example2_star_exit_trace n (S n))
        (started_traces
           (section4_example2_m n)
           (section4_example2_attack_word n)).
  Proof.
    intro n.
    eapply
      (section4_enfa_prime_trace_enumerated_from_single_start
         (section4_example2_m n) 0).
    - apply section4_example2_m_wf.
    - apply section4_example2_m_start.
    - apply section4_example2_star_exit_trace_valid.
    - unfold section4_example2_attack_word.
      apply section4_example2_star_exit_trace_word.
    - apply section4_example2_star_exit_trace_simple.
  Qed.

  Lemma section4_example2_star_b_attack_started :
    forall n,
      In
        (0, section4_example2_star_b_trace n (S n))
        (started_traces
           (section4_example2_m n)
           (section4_example2_attack_word n)).
  Proof.
    intro n.
    eapply
      (section4_enfa_prime_trace_enumerated_from_single_start
         (section4_example2_m n) 0).
    - apply section4_example2_m_wf.
    - apply section4_example2_m_start.
    - apply section4_example2_star_b_trace_valid.
    - unfold section4_example2_attack_word.
      apply section4_example2_star_b_trace_word.
    - apply section4_example2_star_b_trace_simple.
  Qed.

  Lemma section4_example2_accept_attack_started :
    forall n,
      In
        (0, section4_example2_accept_attack_trace n)
        (started_traces
           (section4_example2_m n)
           (section4_example2_attack_word n)).
  Proof.
    intro n.
    eapply
      (section4_enfa_prime_trace_enumerated_from_single_start
         (section4_example2_m n) 0).
    - apply section4_example2_m_wf.
    - apply section4_example2_m_start.
    - apply section4_example2_accept_attack_trace_valid.
    - apply section4_example2_accept_attack_trace_word.
    - apply section4_example2_accept_attack_trace_simple.
  Qed.

  Lemma section4_example2_suffix_b_attack_started :
    forall n i,
      i < n ->
      In
        (0, section4_example2_suffix_b_attack_trace n i)
        (started_traces
           (section4_example2_m n)
           (section4_example2_attack_word n)).
  Proof.
    intros n i Hi.
    eapply
      (section4_enfa_prime_trace_enumerated_from_single_start
         (section4_example2_m n) 0).
    - apply section4_example2_m_wf.
    - apply section4_example2_m_start.
    - now apply section4_example2_suffix_b_attack_trace_valid.
    - apply section4_example2_suffix_b_attack_trace_word. lia.
    - apply section4_example2_suffix_b_attack_trace_simple.
  Qed.

  Lemma section4_example2_accept_attack_da_primeb :
    forall n,
      enfa_accepting_maximal_started_traceb
        (section4_example2_m n)
        (0, section4_example2_accept_attack_trace n) = true.
  Proof.
    intro n.
    unfold enfa_accepting_maximal_started_traceb,
      accepted_traceb, started_end.
    cbn [fst snd].
    rewrite section4_example2_accept_attack_trace_end.
    rewrite section4_example2_m_final.
    rewrite section4_example2_accept_attack_trace_simple.
    rewrite section4_example2_accept_attack_trace_accepting_maximal.
    reflexivity.
  Qed.

  Lemma section4_example2_star_exit_attack_leafb :
    forall n,
      enfa_leaf_prime_started_traceb
        (section4_example2_m n)
        (0, section4_example2_star_exit_trace n (S n)) = true.
  Proof.
    intro n.
    unfold enfa_leaf_prime_started_traceb.
    rewrite section4_example2_star_exit_trace_simple.
    rewrite section4_example2_star_exit_trace_maximal.
    reflexivity.
  Qed.

  Lemma section4_example2_star_b_attack_leafb :
    forall n,
      enfa_leaf_prime_started_traceb
        (section4_example2_m n)
        (0, section4_example2_star_b_trace n (S n)) = true.
  Proof.
    intro n.
    unfold enfa_leaf_prime_started_traceb.
    rewrite section4_example2_star_b_trace_simple.
    rewrite section4_example2_star_b_trace_maximal.
    reflexivity.
  Qed.

  Lemma section4_example2_suffix_b_attack_leafb :
    forall n i,
      enfa_leaf_prime_started_traceb
        (section4_example2_m n)
        (0, section4_example2_suffix_b_attack_trace n i) = true.
  Proof.
    intros n i.
    unfold enfa_leaf_prime_started_traceb.
    rewrite section4_example2_suffix_b_attack_trace_simple.
    rewrite section4_example2_suffix_b_attack_trace_maximal.
    reflexivity.
  Qed.

  Lemma section4_example2_accept_attack_leafb :
    forall n,
      enfa_leaf_prime_started_traceb
        (section4_example2_m n)
        (0, section4_example2_accept_attack_trace n) = true.
  Proof.
    intro n.
    unfold enfa_leaf_prime_started_traceb.
    rewrite section4_example2_accept_attack_trace_simple.
    rewrite section4_example2_accept_attack_trace_maximal.
    reflexivity.
  Qed.

  Definition section4_example2_attack_leaf_endpoints (n : nat) : list nat :=
    [1; 3; 6] ++
    map section4_example2_suffix_b_entry (seq 0 n).

  Definition section4_example2_attack_leaf_traces
      (n : nat) : list (started_trace (section4_example2_m n)) :=
    [ (0, section4_example2_accept_attack_trace n);
      (0, section4_example2_star_exit_trace n (S n));
      (0, section4_example2_star_b_trace n (S n)) ] ++
    map
      (fun i => (0, section4_example2_suffix_b_attack_trace n i))
      (seq 0 n).

  Lemma section4_example2_attack_leaf_endpoints_length :
    forall n,
      length (section4_example2_attack_leaf_endpoints n) = n + 3.
  Proof.
    intro n.
    unfold section4_example2_attack_leaf_endpoints.
    simpl. rewrite map_length, seq_length. lia.
  Qed.

  Lemma section4_NoDup_of_NoDup_map :
    forall {B C : Type} (f : B -> C) xs,
      NoDup (map f xs) -> NoDup xs.
  Proof.
    intros B C f xs Hnodup.
    induction xs as [| x xs IH]; simpl in *.
    - constructor.
    - inversion Hnodup; subst.
      constructor.
      + intro Hin. apply H1. now apply in_map.
      + now apply IH.
  Qed.

  Lemma section4_example2_attack_leaf_endpoints_nodup :
    forall n, NoDup (section4_example2_attack_leaf_endpoints n).
  Proof.
    intro n.
    unfold section4_example2_attack_leaf_endpoints.
    simpl.
    repeat constructor.
    - intros [H | [H | Hin]]; try discriminate.
      apply in_map_iff in Hin as [i [Hi _]].
      subst. unfold section4_example2_suffix_b_entry in Hi. lia.
    - intros [H | Hin]; try discriminate.
      apply in_map_iff in Hin as [i [Hi _]].
      subst. unfold section4_example2_suffix_b_entry in Hi. lia.
    - intro Hin.
      apply in_map_iff in Hin as [i [Hi _]].
      subst. unfold section4_example2_suffix_b_entry in Hi. lia.
    - apply NoDup_map_injective_in.
      + intros i j _ _ Hij.
        now apply section4_example2_suffix_b_entry_inj.
      + apply seq_NoDup.
  Qed.

  Lemma section4_example2_attack_leaf_trace_endpoints :
    forall n,
      map (@started_end bool (section4_example2_m n))
        (section4_example2_attack_leaf_traces n) =
      section4_example2_attack_leaf_endpoints n.
  Proof.
    intro n.
    unfold section4_example2_attack_leaf_traces,
      section4_example2_attack_leaf_endpoints.
    rewrite map_app.
    rewrite map_map.
    change
      ([@trace_end bool (section4_example2_m n) 0
          (section4_example2_accept_attack_trace n);
        @trace_end bool (section4_example2_m n) 0
          (section4_example2_star_exit_trace n (S n));
        @trace_end bool (section4_example2_m n) 0
          (section4_example2_star_b_trace n (S n))] ++
       map
         (fun i =>
            @trace_end bool (section4_example2_m n) 0
              (section4_example2_suffix_b_attack_trace n i))
         (seq 0 n) =
       [1; 3; 6] ++
       map section4_example2_suffix_b_entry (seq 0 n)).
    rewrite section4_example2_accept_attack_trace_end.
    rewrite section4_example2_star_exit_trace_end.
    rewrite section4_example2_star_b_trace_end.
    f_equal.
    apply map_ext. intro i.
    apply section4_example2_suffix_b_attack_trace_end.
  Qed.

  Lemma section4_example2_attack_leaf_traces_nodup :
    forall n, NoDup (section4_example2_attack_leaf_traces n).
  Proof.
    intro n.
    apply
      (section4_NoDup_of_NoDup_map
         (@started_end bool (section4_example2_m n))).
    rewrite section4_example2_attack_leaf_trace_endpoints.
    apply section4_example2_attack_leaf_endpoints_nodup.
  Qed.

  Lemma section4_false_not_in_repeat_true :
    forall k, ~ In false (repeat true k).
  Proof.
    induction k as [| k IH]; simpl; intros H.
    - exact H.
    - destruct H as [H | H]; [discriminate | now apply IH].
  Qed.

  Ltac section4_example2_contradict_repeat_true_false :=
    match goal with
    | H : ?xs ++ [false] = repeat true ?k |- _ =>
        let Hin := fresh "Hin_false" in
        assert (Hin : In false (xs ++ [false]))
          by (apply in_or_app; right; simpl; auto);
        rewrite H in Hin;
        exact (section4_false_not_in_repeat_true k Hin)
    | H : repeat true ?k = ?xs ++ [false] |- _ =>
        symmetry in H; section4_example2_contradict_repeat_true_false
    | H : ?xs ++ [false] = true :: repeat true ?k |- _ =>
        let Hin := fresh "Hin_false" in
        assert (Hin : In false (xs ++ [false]))
          by (apply in_or_app; right; simpl; auto);
        rewrite H in Hin;
        change (In false (repeat true (S k))) in Hin;
        exact (section4_false_not_in_repeat_true (S k) Hin)
    | H : true :: repeat true ?k = ?xs ++ [false] |- _ =>
        symmetry in H; section4_example2_contradict_repeat_true_false
    | H : ?xs ++ false :: ?ys = repeat true ?k |- _ =>
        let Hin := fresh "Hin_false" in
        assert (Hin : In false (xs ++ false :: ys))
          by (apply in_or_app; right; simpl; auto);
        rewrite H in Hin;
        exact (section4_false_not_in_repeat_true k Hin)
    | H : repeat true ?k = ?xs ++ false :: ?ys |- _ =>
        symmetry in H; section4_example2_contradict_repeat_true_false
    | H : ?xs ++ false :: ?ys = true :: repeat true ?k |- _ =>
        let Hin := fresh "Hin_false" in
        assert (Hin : In false (xs ++ false :: ys))
          by (apply in_or_app; right; simpl; auto);
        rewrite H in Hin;
        change (In false (repeat true (S k))) in Hin;
        exact (section4_false_not_in_repeat_true (S k) Hin)
    | H : true :: repeat true ?k = ?xs ++ false :: ?ys |- _ =>
        symmetry in H; section4_example2_contradict_repeat_true_false
    | H : ?xs ++ true :: ?ys ++ [false] = true :: repeat true ?k |- _ =>
        let Hin := fresh "Hin_false" in
        assert (Hin : In false (xs ++ true :: ys ++ [false]))
          by (apply in_or_app; right; simpl;
              right; apply in_or_app; right; simpl; auto);
        rewrite H in Hin;
        change (In false (repeat true (S k))) in Hin;
        exact (section4_false_not_in_repeat_true (S k) Hin)
    | H : true :: repeat true ?k = ?xs ++ true :: ?ys ++ [false] |- _ =>
        symmetry in H; section4_example2_contradict_repeat_true_false
    end.

  Lemma section4_example2_attack_leaf_traces_in_filter :
    forall n st,
      In st (section4_example2_attack_leaf_traces n) ->
      In st
        (filter
           (enfa_leaf_prime_started_traceb (section4_example2_m n))
           (started_traces
              (section4_example2_m n)
              (section4_example2_attack_word n))).
  Proof.
    intros n st Hin.
    apply filter_In.
    unfold section4_example2_attack_leaf_traces in Hin.
    simpl in Hin.
    destruct Hin as [Hin | [Hin | [Hin | Hin]]].
    - subst st.
      split.
      + apply section4_example2_accept_attack_started.
      + apply section4_example2_accept_attack_leafb.
    - subst st.
      split.
      + apply section4_example2_star_exit_attack_started.
      + apply section4_example2_star_exit_attack_leafb.
    - subst st.
      split.
      + apply section4_example2_star_b_attack_started.
      + apply section4_example2_star_b_attack_leafb.
    - apply in_map_iff in Hin as [i [Hst Hi]].
      subst st.
      apply in_seq in Hi as [Hi0 Hi1].
      split.
      + apply section4_example2_suffix_b_attack_started. lia.
      + apply section4_example2_suffix_b_attack_leafb.
  Qed.

  Lemma section4_example2_leaf_prime_attack_at_least_n_plus_3 :
    forall n,
      n + 3 <=
      enfa_leaf_prime_word
        (section4_example2_m n) (section4_example2_attack_word n).
  Proof.
    intro n.
    rewrite enfa_leaf_prime_word_flat by apply section4_example2_m_wf.
    pose proof
      (NoDup_incl_length
         (section4_example2_attack_leaf_traces_nodup n)
         (fun st Hst =>
             section4_example2_attack_leaf_traces_in_filter n st Hst))
      as Hle.
    pose proof
      (f_equal (@length nat)
         (section4_example2_attack_leaf_trace_endpoints n)) as Hlen.
    rewrite map_length in Hlen.
    rewrite section4_example2_attack_leaf_endpoints_length in Hlen.
    rewrite <- Hlen.
    exact Hle.
  Qed.

  Lemma section4_example2_attack_leaf_endpoint_allowed :
    forall n st,
      In st
        (started_traces
           (section4_example2_m n) (section4_example2_attack_word n)) ->
      enfa_leaf_prime_started_traceb (section4_example2_m n) st = true ->
      In (started_end st) (section4_example2_attack_leaf_endpoints n).
  Proof.
    intros n [s t] Hin Hleaf.
    apply andb_true_iff in Hleaf as [_ Hmax].
    destruct (started_traces_valid
                (section4_example2_m n)
                (section4_example2_attack_word n) s t Hin)
      as [Hvalid Hword].
    pose proof (section4_example2_started_trace_start_eq
                  n (section4_example2_attack_word n) s t Hin) as Hs.
    subst s.
    pose proof
      (section4_example2_started_nf_complete n t
         (@trace_end bool (section4_example2_m n) 0 t) Hvalid) as Hnf.
    rewrite Hword in Hnf.
    unfold section4_example2_attack_word in Hnf.
    inversion Hnf; subst; clear Hnf.
    inversion H; subst; clear H.
      + exfalso.
        assert (Hnot :
          maximal_epsilon_simpleb
            (section4_example2_m n)
            (0,
             section4_example2_trace_edge 0 None 4 ::
             section4_example2_star_word_loop n (repeat true (S n))) =
          false).
        {
          eapply section4_example2_maximal_false_of_fresh_epsilon
            with (q' := 3).
          - unfold started_end. cbn [fst snd]. simpl.
            rewrite section4_example2_star_word_loop_all_true.
            rewrite section4_example2_star_true_loop_end.
            apply sss_step_contains_edge; simpl; auto.
          - cbn [fst snd]. simpl.
            rewrite section4_example2_star_word_loop_all_true.
            rewrite section4_example2_star_true_loop_suffix_states.
            destruct n; reflexivity.
        }
        change
          (maximal_epsilon_simpleb
             (section4_example2_m n)
             (0,
              section4_example2_trace_edge 0 None 4 ::
              section4_example2_star_word_loop n (repeat true (S n))) =
           true) in Hmax.
        rewrite Hnot in Hmax. discriminate.
      + unfold started_end. cbn [fst snd]. simpl.
        rewrite trace_end_app.
        rewrite section4_example2_star_word_loop_end.
        simpl.
        unfold section4_example2_attack_leaf_endpoints.
        simpl. auto.
      + unfold started_end. cbn [fst snd]. simpl.
        rewrite trace_end_app.
        rewrite section4_example2_star_word_loop_end.
        simpl.
        unfold section4_example2_attack_leaf_endpoints.
        simpl. auto.
      + exfalso.
        assert (Hnot :
          maximal_epsilon_simpleb
            (section4_example2_m n)
            (0,
             section4_example2_trace_edge 0 None 4 ::
             (section4_example2_star_word_loop n prefix ++
              [section4_example2_trace_edge 4 (Some true) 5])) =
          false).
        {
          eapply section4_example2_maximal_false_of_fresh_epsilon
            with (q' := 4).
          - unfold started_end. cbn [fst snd]. simpl.
            rewrite trace_end_app.
            rewrite section4_example2_star_word_loop_end.
            simpl. apply sss_step_contains_edge; simpl; auto.
          - cbn [fst snd]. simpl.
            rewrite section4_example2_star_word_loop_then_true_suffix_states.
            apply section4_example2_state_inb_singleton_false.
            lia.
        }
        change
          (maximal_epsilon_simpleb
             (section4_example2_m n)
             (0,
              section4_example2_trace_edge 0 None 4 ::
              (section4_example2_star_word_loop n prefix ++
               [section4_example2_trace_edge 4 (Some true) 5])) =
           true) in Hmax.
        rewrite Hnot in Hmax. discriminate.
      + exfalso. section4_example2_contradict_repeat_true_false.
      + exfalso. section4_example2_contradict_repeat_true_false.
      + inversion H1; subst; clear H1.
        * exfalso.
          destruct (Nat.lt_ge_cases (length suffix) n) as [Hlt | Hge].
          -- assert (Hnot :
               maximal_epsilon_simpleb
                 (section4_example2_m n)
                 (0,
                  section4_example2_trace_edge 0 None 4 ::
                  (section4_example2_star_word_loop n prefix ++
                   [ section4_example2_trace_edge 4 None 3;
                     section4_example2_trace_edge 3 (Some true)
                       (section4_example2_checkpoint 0) ] ++
                   section4_example2_suffix_word_path n 0 suffix)) =
               false).
             {
               eapply section4_example2_maximal_false_of_fresh_epsilon
                 with
                   (q' := section4_example2_suffix_b_entry (length suffix)).
               - unfold started_end. cbn [fst snd]. simpl.
                  repeat rewrite trace_end_app.
                  rewrite section4_example2_star_word_loop_end.
                  simpl.
                  change 2 with (section4_example2_checkpoint 0).
                  rewrite section4_example2_suffix_word_path_end.
                 rewrite Nat.add_0_l.
                 unfold section4_example2_m, regex_Msss.
                 change
                   (In (section4_example2_suffix_b_entry (length suffix))
                      (sss_step Bool.eqb
                         (sss_edges
                            (sss_compile (section4_example2_regex n)))
                         (section4_example2_checkpoint (length suffix))
                         None)).
                 apply sss_step_contains_edge.
                 + rewrite section4_example2_compile_edges.
                   apply section4_example2_suffix_b_entry_edge_in.
                   exact Hlt.
                 + reflexivity.
                - cbn [fst snd].
                  rewrite
                    section4_example2_from4_suffix_word_path_suffix_states.
                  replace (length suffix) with (0 + length suffix) by lia.
                  apply section4_example2_suffix_word_path_no_b_entry_seen.
              }
              change
                (maximal_epsilon_simpleb
                   (section4_example2_m n)
                   (0,
                    section4_example2_trace_edge 0 None 4 ::
                    section4_example2_star_word_loop n prefix ++
                    [ section4_example2_trace_edge 4 None 3;
                      section4_example2_trace_edge 3 (Some true)
                        (section4_example2_checkpoint 0) ] ++
                    section4_example2_suffix_word_path n 0 suffix) =
                 true) in Hmax.
              rewrite Hnot in Hmax. discriminate.
          -- assert (length suffix = n) by lia. subst n.
             assert (Hnot :
               maximal_epsilon_simpleb
                 (section4_example2_m (length suffix))
                 (0,
                  section4_example2_trace_edge 0 None 4 ::
                  (section4_example2_star_word_loop (length suffix) prefix ++
                   [ section4_example2_trace_edge 4 None 3;
                     section4_example2_trace_edge 3 (Some true)
                       (section4_example2_checkpoint 0) ] ++
                   section4_example2_suffix_word_path
                     (length suffix) 0 suffix)) =
               false).
             {
               eapply section4_example2_maximal_false_of_fresh_epsilon
                 with (q' := 1).
               - unfold started_end. cbn [fst snd]. simpl.
                  repeat rewrite trace_end_app.
                  rewrite section4_example2_star_word_loop_end.
                  simpl.
                  change 2 with (section4_example2_checkpoint 0).
                  rewrite section4_example2_suffix_word_path_end.
                 rewrite Nat.add_0_l.
                 unfold section4_example2_m, regex_Msss.
                 change
                   (In 1
                      (sss_step Bool.eqb
                         (sss_edges
                            (sss_compile
                               (section4_example2_regex (length suffix))))
                         (section4_example2_checkpoint (length suffix))
                         None)).
                 apply sss_step_contains_edge.
                 + rewrite section4_example2_compile_edges.
                   apply section4_example2_suffix_final_edge_in.
                 + reflexivity.
               - cbn [fst snd].
                 rewrite
                   section4_example2_from4_suffix_word_path_suffix_states.
                  apply section4_example2_suffix_word_path_no_final_seen.
              }
              change
                (maximal_epsilon_simpleb
                   (section4_example2_m (length suffix))
                   (0,
                    section4_example2_trace_edge 0 None 4 ::
                    section4_example2_star_word_loop
                      (length suffix) prefix ++
                    [ section4_example2_trace_edge 4 None 3;
                      section4_example2_trace_edge 3 (Some true)
                        (section4_example2_checkpoint 0) ] ++
                    section4_example2_suffix_word_path
                      (length suffix) 0 suffix) =
                 true) in Hmax.
              rewrite Hnot in Hmax. discriminate.
        * unfold started_end. cbn [fst snd]. simpl.
          repeat rewrite trace_end_app.
          rewrite section4_example2_star_word_loop_end.
          simpl.
          rewrite trace_end_app.
          change 2 with (section4_example2_checkpoint 0).
          rewrite section4_example2_suffix_word_path_end.
          rewrite Nat.add_0_l.
          simpl.
          unfold section4_example2_attack_leaf_endpoints.
          simpl. right. right. right.
          apply in_map.
          apply in_seq. lia.
        * exfalso. section4_example2_contradict_repeat_true_false.
        * unfold started_end. cbn [fst snd]. simpl.
          repeat rewrite trace_end_app.
          rewrite section4_example2_star_word_loop_end.
          simpl.
          rewrite trace_end_app.
          change 2 with (section4_example2_checkpoint 0).
          rewrite section4_example2_suffix_word_path_end.
          rewrite Nat.add_0_l.
          simpl.
          unfold section4_example2_attack_leaf_endpoints.
          simpl. auto.
  Qed.

  Lemma section4_example2_leaf_prime_attack_at_most_n_plus_3 :
    forall n,
      enfa_leaf_prime_word
        (section4_example2_m n) (section4_example2_attack_word n) <= n + 3.
  Proof.
    intro n.
    rewrite enfa_leaf_prime_word_flat by apply section4_example2_m_wf.
    set (filtered :=
           filter
             (enfa_leaf_prime_started_traceb (section4_example2_m n))
             (started_traces
                (section4_example2_m n)
                (section4_example2_attack_word n))).
    assert (Hnodup_endpoints :
      NoDup (map (@started_end bool (section4_example2_m n)) filtered)).
    {
      apply NoDup_map_injective_in.
      - intros st1 st2 Hst1 Hst2 Hend.
        subst filtered.
        apply filter_In in Hst1 as [Hin1 Hleaf1].
        apply filter_In in Hst2 as [Hin2 Hleaf2].
        unfold enfa_leaf_prime_started_traceb in Hleaf1, Hleaf2.
        apply andb_true_iff in Hleaf1 as [Hsimple1 _].
        apply andb_true_iff in Hleaf2 as [Hsimple2 _].
        eapply section4_example2_dra_prime_unique_trace
          with (q := started_end st1); eauto.
        + apply andb_true_iff. split.
          * unfold ends_inb. apply Nat.eqb_eq. reflexivity.
          * exact Hsimple1.
        + apply andb_true_iff. split.
          * unfold ends_inb. apply Nat.eqb_eq. symmetry. exact Hend.
          * exact Hsimple2.
      - subst filtered.
        apply NoDup_filter_bool.
        eapply started_traces_single_start_NoDup.
        + apply section4_example2_m_wf.
        + apply section4_example2_m_start.
    }
    assert (Hincl :
      incl
        (map (@started_end bool (section4_example2_m n)) filtered)
        (section4_example2_attack_leaf_endpoints n)).
    {
      intros q Hq.
      apply in_map_iff in Hq as [st [Hq Hst]].
      subst q filtered.
      apply filter_In in Hst as [Hin Hleaf].
      now apply section4_example2_attack_leaf_endpoint_allowed.
    }
    pose proof (NoDup_incl_length Hnodup_endpoints Hincl) as Hle.
    rewrite map_length in Hle.
    rewrite section4_example2_attack_leaf_endpoints_length in Hle.
    exact Hle.
  Qed.

  Theorem section4_example2_leaf_prime_attack_count :
    forall n,
      enfa_leaf_prime_word
        (section4_example2_m n) (section4_example2_attack_word n) = n + 3.
  Proof.
    intro n.
    pose proof
      (section4_example2_leaf_prime_attack_at_least_n_plus_3 n) as Hlower.
    pose proof
      (section4_example2_leaf_prime_attack_at_most_n_plus_3 n) as Hupper.
    lia.
  Qed.

  Lemma section4_example2_da_prime_attack_at_least_one :
    forall n,
      1 <=
      enfa_da_prime_word
        (section4_example2_m n) (section4_example2_attack_word n).
  Proof.
    intro n.
    rewrite enfa_da_prime_word_flat by apply section4_example2_m_wf.
    eapply filter_length_pos_of_In.
    - apply section4_example2_accept_attack_started.
    - apply section4_example2_accept_attack_da_primeb.
  Qed.

  Theorem section4_example2_da_prime_attack_count :
    forall n,
      enfa_da_prime_word
        (section4_example2_m n) (section4_example2_attack_word n) = 1.
  Proof.
    intro n.
    pose proof (section4_example2_da_prime_attack_at_least_one n) as Hlower.
    pose proof
      (section4_example2_m_ufa n (section4_example2_attack_word n))
      as Hupper.
    lia.
  Qed.

  Lemma section4_example2_leaf_prime_attack_at_least_two :
    forall n,
      2 <=
      enfa_leaf_prime_word
        (section4_example2_m n) (section4_example2_attack_word n).
  Proof.
    intro n.
    rewrite enfa_leaf_prime_word_flat by apply section4_example2_m_wf.
    eapply two_distinct_in_filter_length
      with
        (x := (0, section4_example2_star_exit_trace n (S n)))
        (y := (0, section4_example2_star_b_trace n (S n))).
    - apply section4_example2_star_exit_attack_started.
    - apply section4_example2_star_b_attack_started.
    - apply section4_example2_star_exit_attack_leafb.
    - apply section4_example2_star_b_attack_leafb.
    - intro Heq.
      inversion Heq as [Htrace].
      unfold section4_example2_star_exit_trace,
        section4_example2_star_b_trace in Htrace.
      apply app_inv_head in Htrace.
      discriminate.
  Qed.

  Example section4_example2_m_not_leafufa :
    forall n, ~ enfa_LeafUFA (section4_example2_m n).
  Proof.
    intros n Hleaf.
    specialize (Hleaf (section4_example2_attack_word n)).
    pose proof (section4_example2_leaf_prime_attack_at_least_two n).
    lia.
  Qed.

  Example section4_example2_regex_not_strong_leaf_unambiguous :
    forall n,
      ~ regex_strong_leaf_unambiguous
          [true; false] Bool.eqb (section4_example2_regex n).
  Proof.
    intro n.
    unfold regex_strong_leaf_unambiguous, regex_leaf_unambiguous,
      section4_example2_m.
    apply section4_example2_m_not_leafufa.
  Qed.

  Lemma section4_example2_initial_epsilon_step :
    forall n,
      In 4 (enfa_step (fenfa_base (section4_example2_m n)) 0 None).
  Proof.
    intro n.
    unfold section4_example2_m, regex_Msss, sss_step.
    apply nodup_In.
    apply in_map_iff.
    exists (0, None, 4).
    split; [reflexivity |].
    apply filter_In.
    split.
    - cbn. auto.
    - cbn. reflexivity.
  Qed.

  Example section4_example2_m_not_sufa_under_definition6 :
    forall n, ~ enfa_SUFA (section4_example2_m n).
  Proof.
    intros n [Heps _].
    pose proof (section4_example2_initial_epsilon_step n) as Hstep.
    rewrite (Heps 0) in Hstep.
    contradiction.
  Qed.

  Example section4_example2_m0_ufa_reachufa_not_leafufa_not_dfa :
    finite_enfa_wf (section4_example2_m 0) /\
    enfa_UFA (section4_example2_m 0) /\
    enfa_ReachUFA (section4_example2_m 0) /\
    ~ enfa_LeafUFA (section4_example2_m 0) /\
    ~ enfa_DFA_conditions (section4_example2_m 0).
  Proof.
    split.
    - apply section4_example2_m_wf.
    - split.
      + apply section4_example2_m_ufa.
      + split.
        * apply section4_example2_m_reachufa.
        * split.
          -- apply section4_example2_m_not_leafufa.
          -- intro Hdfa.
             pose proof
               (section4_dfa_conditions_implies_ufa_reachufa_leafufa
                  (section4_example2_m 0) Hdfa) as [_ [_ Hleaf]].
             exact (section4_example2_m_not_leafufa 0 Hleaf).
  Qed.

  Theorem section4_straightforward_not_conversely :
    (exists m : @finite_enfa bool,
      finite_enfa_wf m /\
      enfa_UFA m /\
      enfa_ReachUFA m /\
      ~ enfa_LeafUFA m /\
      ~ enfa_DFA_conditions m) /\
    (exists m : @finite_enfa bool,
      finite_enfa_wf m /\
      enfa_LeafUFA m /\
      ~ enfa_DFA_conditions m).
  Proof.
    split.
    - exists (section4_example2_m 0).
      exact section4_example2_m0_ufa_reachufa_not_leafufa_not_dfa.
    - exists epsilon_self_loop_bool_enfa.
      split.
      + apply epsilon_self_loop_bool_enfa_wf.
      + split.
        * apply epsilon_self_loop_bool_leafufa.
        * apply epsilon_self_loop_bool_not_dfa_conditions.
  Qed.

  Example section4_example2_da_prime_attack_count_0 :
    enfa_da_prime_word
      (section4_example2_m 0) (section4_example2_attack_word 0) = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example section4_example2_da_prime_attack_count_1 :
    enfa_da_prime_word
      (section4_example2_m 1) (section4_example2_attack_word 1) = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example section4_example2_da_prime_attack_count_2 :
    enfa_da_prime_word
      (section4_example2_m 2) (section4_example2_attack_word 2) = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example section4_example2_da_prime_attack_count_3 :
    enfa_da_prime_word
      (section4_example2_m 3) (section4_example2_attack_word 3) = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example section4_example2_leaf_prime_attack_count_0 :
    enfa_leaf_prime_word
      (section4_example2_m 0) (section4_example2_attack_word 0) = 0 + 3.
  Proof. vm_compute. reflexivity. Qed.

  Example section4_example2_leaf_prime_attack_count_1 :
    enfa_leaf_prime_word
      (section4_example2_m 1) (section4_example2_attack_word 1) = 1 + 3.
  Proof. vm_compute. reflexivity. Qed.

  Example section4_example2_leaf_prime_attack_count_2 :
    enfa_leaf_prime_word
      (section4_example2_m 2) (section4_example2_attack_word 2) = 2 + 3.
  Proof. vm_compute. reflexivity. Qed.

  Example section4_example2_leaf_prime_attack_count_3 :
    enfa_leaf_prime_word
      (section4_example2_m 3) (section4_example2_attack_word 3) = 3 + 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Gamma trace/derivation and Definitions 8/9 bridge examples.  This block
      includes roundtrip and epsilon-simple equalities, plus theorem calls from
      ReachUFA/LeafUFA to Gamma RLG unambiguity. *)
  Example unit_bool_gamma_trace_roundtrip :
    gamma_trace_of_derivation unit_bool_enfa tt
      (gamma_derivation_of_trace
         unit_bool_enfa tt [((tt, Some true), tt)] tt) =
    Some [((tt, Some true), tt)].
  Proof.
    reflexivity.
  Qed.

  Example unit_bool_gamma_rlg_dra_prime_count_true :
    let G := gamma_grammar_from unit_bool_enfa tt in
    rlg_dra_prime_count
      G
      (fenfa_state_eqb unit_bool_enfa)
      bool_list_eqb
      1
      [true]
      tt = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example unit_bool_gamma_epsilon_simple_roundtrip :
    rlg_epsilon_simpleb
      (gamma_grammar_from unit_bool_enfa tt)
      (fenfa_state_eqb unit_bool_enfa)
      tt
      (gamma_derivation_of_trace
         unit_bool_enfa tt [((tt, Some true), tt)] tt) =
    epsilon_simpleb unit_bool_enfa (tt, [((tt, Some true), tt)]).
  Proof.
    apply section4_gamma_support_trace_derivation_epsilon_simple.
  Qed.

  Example unit_bool_gamma_prime_accepting_derivation :
    rlg_derivation_accepting_prime
      (gamma_grammar_from unit_bool_enfa tt)
      (fenfa_state_eqb unit_bool_enfa)
      [true]
      (gamma_derivation_of_trace
         unit_bool_enfa tt [((tt, Some true), tt)] tt).
  Proof.
    unfold rlg_derivation_accepting_prime, rlg_derivation_accepting.
    split.
    - split.
      + eapply RLGDerivation_step.
        * vm_compute. auto.
        * apply RLGDerivation_stop. vm_compute. auto.
      + reflexivity.
    - split; vm_compute; reflexivity.
  Qed.

  Example unit_bool_gamma_reach_bridge :
    enfa_prime_trace_enumerated_from unit_bool_enfa tt ->
    enfa_ReachUFA unit_bool_enfa ->
    gamma_rlg_reach_unambiguous unit_bool_enfa tt.
  Proof.
    intros Henumerated Hreach.
    eapply section4_gamma_support_reachufa_to_rlg_reach_unambiguous.
    - apply unit_bool_enfa_wf.
    - reflexivity.
    - exact Henumerated.
    - exact Hreach.
  Qed.

  Example unit_bool_gamma_leaf_bridge :
    enfa_prime_trace_enumerated_from unit_bool_enfa tt ->
    enfa_LeafUFA unit_bool_enfa ->
    gamma_rlg_leaf_unambiguous unit_bool_enfa tt.
  Proof.
    intros Henumerated Hleaf.
    eapply section4_gamma_support_leafufa_to_rlg_leaf_unambiguous.
    - apply unit_bool_enfa_wf.
    - reflexivity.
    - exact Henumerated.
    - exact Hleaf.
  Qed.

  Example unit_bool_gamma_reach_bridge_iff :
    enfa_prime_trace_enumerated_from unit_bool_enfa tt ->
    enfa_started_traces_nodup unit_bool_enfa ->
    (enfa_ReachUFA unit_bool_enfa <->
     gamma_rlg_reach_unambiguous unit_bool_enfa tt).
  Proof.
    intros Henumerated Hnodup.
    eapply section4_gamma_support_reachufa_rlg_reach_unambiguous_iff.
    - apply unit_bool_enfa_wf.
    - reflexivity.
    - exact Henumerated.
    - exact Hnodup.
  Qed.

  Example two_accepting_paths_gamma_pair_injective :
    gamma_derivation_of_trace
      two_accepting_paths_enfa false
      [((false, Some true), false)]
      false <>
    gamma_derivation_of_trace
      two_accepting_paths_enfa false
      [((false, Some true), true)]
      true.
  Proof.
    intro Heq.
    apply section4_gamma_support_trace_derivation_pair_injective
      in Heq as [_ Hq].
    discriminate.
  Qed.

  (** LR(1) examples.  The first examples check the Theorem 6/7 machine
      structure and [conflicts <= leaves] counting interface; later examples
      separate Gamma semantic conflicts from the canonical item-set predicate
      and include a directly computed [gamma_canonical_lr1] positive case. *)
  Example unit_bool_lr1_machine_characterization :
    fenfa_states
      (lr1_enfa _ (lr1_machine_of_enfa Bool.bool_dec unit_bool_enfa)) =
    lr1_reduce_items unit_bool_enfa ++ lr1_nonreduce_items unit_bool_enfa.
  Proof.
    reflexivity.
  Qed.

  Example unit_bool_lr1_conflicts_le_leaves_empty :
    let M := lr1_machine_of_enfa Bool.bool_dec unit_bool_enfa in
    lr1_conflict_count M [] <= lr1_leaf_count M [].
  Proof.
    simpl. apply section4_theorem6_conflicts_le_leaves.
  Qed.

  Example unit_bool_lr1_conflicts_le_leaves_of_enfa_empty :
    lr1_conflict_count
      (lr1_machine_of_enfa Bool.bool_dec unit_bool_enfa) [] <=
    lr1_leaf_count
      (lr1_machine_of_enfa Bool.bool_dec unit_bool_enfa) [].
  Proof.
    apply section4_theorem6_conflicts_le_leaves_of_enfa.
  Qed.

  Example unit_bool_lr1_full_spec_from_leaf_bound :
    gamma_lr1 unit_bool_enfa ->
    (forall w,
      lr1_leaf_count (lr1_machine_of_enfa Bool.bool_dec unit_bool_enfa) w <= 1) ->
    gamma_lr1_full_spec Bool.bool_dec unit_bool_enfa.
  Proof.
    intros Hlr Hleaf.
    eapply section4_lr1_support_full_spec_if_lr1_leaf_bounded; eauto.
  Qed.

  Example unit_bool_lr1_full_spec_iff :
    gamma_lr1_full_spec Bool.bool_dec unit_bool_enfa <->
    enfa_UFA unit_bool_enfa /\
    enfa_ReachUFA unit_bool_enfa /\
    lr1_conflict_free (lr1_machine_of_enfa Bool.bool_dec unit_bool_enfa).
  Proof.
    apply section4_lr1_support_full_spec_iff_ufa_reachufa_conflict_free.
  Qed.

  Example unit_bool_lr1_start_state_spec :
    lr1_start_item_spec unit_bool_enfa (@LRState bool unit tt LAEpsilon).
  Proof.
    exists tt. simpl. auto.
  Qed.

  Example unit_bool_lr1_projected_leaf_preservation_true :
    lr1_projected_leaf_count Bool.bool_dec unit_bool_enfa [true] =
    enfa_leaf_prime_word unit_bool_enfa [true].
  Proof.
    apply section4_lemma4_I_lr1_leaf_preservation.
  Qed.

  (** Diamond-shaped ENFA: after reading [true], two paths reach state [3].
      The corresponding Gamma grammar gives a reach reduce conflict. *)
  Definition diamond_join_enfa : @finite_enfa bool :=
    {|
      fenfa_base :=
        {|
          enfa_state := nat;
          enfa_start := [0];
          enfa_final := fun _ => false;
          enfa_step :=
            fun q l =>
              match q, l with
              | 0, Some true => [1; 2]
              | 1, None => [3]
              | 2, None => [3]
              | _, _ => []
              end
        |};
      fenfa_states := [0; 1; 2; 3];
      fenfa_alphabet := [true];
      fenfa_state_eqb := Nat.eqb;
      fenfa_state_eqb_sound := fun x y H => proj1 (Nat.eqb_eq x y) H;
      fenfa_state_eqb_complete := fun x y H => proj2 (Nat.eqb_eq x y) H
    |}.

  Example diamond_join_enfa_wf :
    finite_enfa_wf diamond_join_enfa.
  Proof.
    constructor; simpl.
    - repeat constructor; simpl; intros H; lia.
    - intros q Hq. destruct Hq as [Hq | []]; subst q; simpl; auto.
    - intros q l q' Hq Hstep.
      destruct Hq as [Hq | [Hq | [Hq | [Hq | []]]]]; subst q;
        destruct l as [[|]|]; simpl in Hstep;
        repeat (destruct Hstep as [Hstep | Hstep];
          [subst q'; simpl; auto |]); contradiction.
    - intros q a q' Hq Hstep.
      destruct Hq as [Hq | [Hq | [Hq | [Hq | []]]]]; subst q;
        destruct a; simpl in Hstep;
        repeat (destruct Hstep as [Hstep | Hstep];
          [subst q'; simpl; auto |]); contradiction.
    - intros q l Hq.
      destruct Hq as [Hq | [Hq | [Hq | [Hq | []]]]]; subst q;
        destruct l as [[|]|]; simpl; repeat constructor; simpl; intros H; lia.
  Qed.

  Example diamond_join_lr1_projected_leaf_preservation_empty :
    lr1_projected_leaf_count Bool.bool_dec diamond_join_enfa [] =
    enfa_leaf_prime_word diamond_join_enfa [].
  Proof.
    apply section4_lemma4_I_lr1_leaf_preservation.
  Qed.

  Example diamond_join_lr1_projected_leaf_preservation_true :
    lr1_projected_leaf_count Bool.bool_dec diamond_join_enfa [true] =
    enfa_leaf_prime_word diamond_join_enfa [true].
  Proof.
    apply section4_lemma4_I_lr1_leaf_preservation.
  Qed.

  Example diamond_join_lr1_raw_leaf_empty_not_lemma3 :
    lr1_leaf_count (lr1_machine_of_enfa Bool.bool_dec diamond_join_enfa) [] <>
    enfa_leaf_prime_word diamond_join_enfa [].
  Proof.
    vm_compute. discriminate.
  Qed.

  Example diamond_join_gamma_reach_reduce_conflict :
    gamma_semantic_reach_reduce_conflict
      diamond_join_enfa 0.
  Proof.
    exists [true], 3,
      ([(0, [true], Some 1); (1, [], Some 3)]
        : rlg_derivation (gamma_grammar_from diamond_join_enfa 0)),
      ([(0, [true], Some 2); (2, [], Some 3)]
        : rlg_derivation (gamma_grammar_from diamond_join_enfa 0)).
    split.
    - split.
      + econstructor.
        * vm_compute. auto.
        * econstructor.
          -- vm_compute. auto.
          -- constructor.
      + split; [reflexivity | vm_compute; reflexivity].
    - split.
      + split.
        * econstructor.
          -- vm_compute. auto.
          -- econstructor.
             ++ vm_compute. auto.
             ++ constructor.
        * split; [reflexivity | vm_compute; reflexivity].
      + discriminate.
  Qed.

  (** Crossing-epsilon reach-conflict example.

      The two prime prefix derivations below both read [true] and reach state
      [2].  One path consumes [true] directly, while the other first takes an
      epsilon edge and then consumes [true].  The canonical LR item-set
      construction distinguishes the viable-prefix states, while the Gamma
      semantic interface records the reach reduce conflict. *)
  Definition crossing_epsilon_enfa : @finite_enfa bool :=
    {|
      fenfa_base :=
        {|
          enfa_state := nat;
          enfa_start := [0];
          enfa_final := fun _ => false;
          enfa_step :=
            fun q l =>
              match q, l with
              | 0, Some true => [2]
              | 0, None => [1]
              | 1, Some true => [2]
              | _, _ => []
              end
        |};
      fenfa_states := [0; 1; 2];
      fenfa_alphabet := [true];
      fenfa_state_eqb := Nat.eqb;
      fenfa_state_eqb_sound := fun x y H => proj1 (Nat.eqb_eq x y) H;
      fenfa_state_eqb_complete := fun x y H => proj2 (Nat.eqb_eq x y) H
    |}.

  Example crossing_epsilon_enfa_wf :
    finite_enfa_wf crossing_epsilon_enfa.
  Proof.
    constructor; simpl.
    - repeat constructor; simpl; intros H; lia.
    - intros q Hq. destruct Hq as [Hq | []]; subst q; simpl; auto.
    - intros q l q' Hq Hstep.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        destruct l as [[|]|]; simpl in Hstep;
        repeat (destruct Hstep as [Hstep | Hstep];
          [subst q'; simpl; auto |]); contradiction.
    - intros q a q' Hq Hstep.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        destruct a; simpl in Hstep;
        repeat (destruct Hstep as [Hstep | Hstep];
          [subst q'; simpl; auto |]); contradiction.
    - intros q l Hq.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        destruct l as [[|]|]; simpl; repeat constructor; simpl; intros H; lia.
  Qed.

  Definition crossing_epsilon_reach_derivation_left
      : rlg_derivation (gamma_grammar_from crossing_epsilon_enfa 0) :=
    [(0, [true], Some 2)].

  Definition crossing_epsilon_reach_derivation_right
      : rlg_derivation (gamma_grammar_from crossing_epsilon_enfa 0) :=
    [(0, [], Some 1); (1, [true], Some 2)].

  Example crossing_epsilon_gamma_left_prime_reaches :
    rlg_prefix_derivation_prime_reaches
      (gamma_grammar_from crossing_epsilon_enfa 0)
      Nat.eqb
      [true]
      2
      crossing_epsilon_reach_derivation_left.
  Proof.
    unfold crossing_epsilon_reach_derivation_left.
    split.
    - econstructor.
      + vm_compute. auto.
      + constructor.
    - split.
      + reflexivity.
      + vm_compute. reflexivity.
  Qed.

  Example crossing_epsilon_gamma_right_prime_reaches :
    rlg_prefix_derivation_prime_reaches
      (gamma_grammar_from crossing_epsilon_enfa 0)
      Nat.eqb
      [true]
      2
      crossing_epsilon_reach_derivation_right.
  Proof.
    unfold crossing_epsilon_reach_derivation_right.
    split.
    - econstructor.
      + vm_compute. auto.
      + econstructor.
        * vm_compute. auto.
        * constructor.
    - split.
      + reflexivity.
      + vm_compute. reflexivity.
  Qed.

  Example crossing_epsilon_gamma_reach_reduce_conflict :
    gamma_semantic_reach_reduce_conflict crossing_epsilon_enfa 0.
  Proof.
    exists [true], 2,
      crossing_epsilon_reach_derivation_left,
      crossing_epsilon_reach_derivation_right.
    repeat split.
    - apply crossing_epsilon_gamma_left_prime_reaches.
    - apply crossing_epsilon_gamma_right_prime_reaches.
    - discriminate.
  Qed.

  Example crossing_epsilon_gamma_lr_terminal_reach_reduce_conflict :
    gamma_lr_terminal_reach_reduce_conflict
      Bool.bool_dec crossing_epsilon_enfa 0.
  Proof.
    exact crossing_epsilon_gamma_reach_reduce_conflict.
  Qed.

  Example crossing_epsilon_not_gamma_terminal_lr1 :
    ~ gamma_terminal_lr1 Bool.bool_dec crossing_epsilon_enfa 0.
  Proof.
    unfold gamma_terminal_lr1,
      gamma_lr_terminal_reduce_conflict_free,
      gamma_lr_terminal_reach_reduce_conflict_free,
      gamma_semantic_reach_reduce_conflict_free.
    intros [_ Hreach].
    specialize
      (Hreach [true] 2
         crossing_epsilon_reach_derivation_left
         crossing_epsilon_reach_derivation_right
         crossing_epsilon_gamma_left_prime_reaches
         crossing_epsilon_gamma_right_prime_reaches).
    discriminate.
  Qed.

  (** The corresponding canonical item-set calculation has no
      reduce/reduce conflict: the direct edge [0 -true-> 2] and the crossed
      path [0 -epsilon-> 1 -true-> 2] reach distinct LR viable-prefix states
      before reducing the final nonterminal [2].  The examples above use the
      semantic Gamma conflict interface that matches the paper theorem. *)

  (** Two distinct accepting traces appear as an accepting reduce conflict in Gamma. *)
  Example two_accepting_paths_gamma_accept_reduce_conflict :
    gamma_semantic_accept_reduce_conflict
      two_accepting_paths_enfa false.
  Proof.
    exists [true],
      (gamma_derivation_of_trace
         two_accepting_paths_enfa false
         [((false, Some true), false)] false),
      (gamma_derivation_of_trace
         two_accepting_paths_enfa false
         [((false, Some true), true)] true).
    split.
    - unfold rlg_derivation_accepting_prime, rlg_derivation_accepting.
      split.
      + split.
        * eapply RLGDerivation_step.
          -- vm_compute. auto.
          -- apply RLGDerivation_stop. vm_compute. auto.
        * reflexivity.
      + split; vm_compute; reflexivity.
    - split.
      + unfold rlg_derivation_accepting_prime, rlg_derivation_accepting.
        split.
        * split.
          -- eapply RLGDerivation_step.
             ++ vm_compute. auto.
             ++ apply RLGDerivation_stop. vm_compute. auto.
          -- reflexivity.
        * split; vm_compute; reflexivity.
      + intro Heq.
        apply section4_gamma_support_trace_derivation_pair_injective
          in Heq as [_ Hq].
        discriminate.
  Qed.

  Example unit_bool_canonical_lr1_direct :
    gamma_canonical_lr1 Bool.bool_dec unit_bool_enfa tt.
  Proof.
    unfold gamma_canonical_lr1, lr1_canonical_collection_conflict_free,
      lr1_item_set_reduce_conflict_free.
    intros xs Hxs it1 it2 la Hin1 Hin2 Hred1 Hred2 Hla1 Hla2.
    vm_compute in Hxs.
    repeat
      match goal with
      | H : _ \/ _ |- _ => destruct H as [H | H]
      | H : False |- _ => contradiction
      | H : _ = _ |- _ => subst
      end.
    all:
      repeat
        match goal with
        | H : _ \/ _ |- _ => destruct H as [H | H]
        | H : In _ (_ :: _) |- _ =>
            simpl in H; destruct H as [H | H]
        | H : In _ [] |- _ => contradiction
        | H : False |- _ => contradiction
        | H : _ = _ |- _ => subst
        end;
      vm_compute in Hred1;
      vm_compute in Hred2;
      try discriminate;
      vm_compute in Hla1;
      vm_compute in Hla2;
      try discriminate;
      reflexivity.
  Qed.

  Example unit_bool_canonical_lr1_from_ufa_reachufa :
    enfa_prime_trace_enumerated_from unit_bool_enfa tt ->
    enfa_started_traces_nodup unit_bool_enfa ->
    enfa_UFA unit_bool_enfa ->
    enfa_ReachUFA unit_bool_enfa ->
    gamma_canonical_lr1 Bool.bool_dec unit_bool_enfa tt.
  Proof.
    intros _ _ _ _. apply unit_bool_canonical_lr1_direct.
  Qed.

  Example unit_bool_leafufa_sufficient_canonical_lr1 :
    enfa_prime_trace_enumerated_from unit_bool_enfa tt ->
    enfa_started_traces_nodup unit_bool_enfa ->
    enfa_prime_extendable unit_bool_enfa ->
    enfa_LeafUFA unit_bool_enfa ->
    gamma_canonical_lr1 Bool.bool_dec unit_bool_enfa tt.
  Proof.
    intros _ _ _ _. apply unit_bool_canonical_lr1_direct.
  Qed.

  (** Theorem 5 bridge alignment example.

      Canonical LR final items are generated from final states directly, while
      Leaf' uses globally maximal reach endpoints.  In this finite ENFA the
      states [1] and [2] are final and have fresh non-final epsilon successors:
      DA' still counts them as accepting-maximal, while global maximal reach
      counts at those final states are zero. *)
  Definition section4_example_theorem5_final_not_max_enfa : @finite_enfa bool :=
    {|
      fenfa_base :=
        {|
          enfa_state := nat;
          enfa_start := [0];
          enfa_final :=
            fun q =>
              match q with
              | 1 => true
              | 2 => true
              | _ => false
              end;
          enfa_step :=
            fun q l =>
              match q, l with
              | 0, None => [1; 2]
              | 1, None => [3]
              | 2, None => [4]
              | _, _ => []
              end
        |};
      fenfa_states := [0; 1; 2; 3; 4];
      fenfa_alphabet := [];
      fenfa_state_eqb := Nat.eqb;
      fenfa_state_eqb_sound := fun x y H => proj1 (Nat.eqb_eq x y) H;
      fenfa_state_eqb_complete := fun x y H => proj2 (Nat.eqb_eq x y) H
    |}.

  Ltac section4_example_solve_in :=
    repeat
      match goal with
      | H : _ \/ _ |- _ => destruct H as [H | H]
      | H : False |- _ => contradiction
      | H : _ = _ |- _ => subst
      end;
    simpl; auto; try contradiction; try discriminate.

  Example section4_example_theorem5_final_not_max_enfa_wf :
    finite_enfa_wf section4_example_theorem5_final_not_max_enfa.
  Proof.
    constructor; simpl.
    - repeat constructor; simpl; intuition congruence.
    - intros q Hq. simpl in Hq |- *. intuition congruence.
    - intros q l q' _ Hstep.
      destruct q as [| [| [| [| [| q]]]]];
        destruct l as [[|] |];
        simpl in Hstep |- *; intuition congruence.
    - intros q a q' _ Hstep.
      destruct q as [| [| [| [| [| q]]]]];
        destruct a;
        simpl in Hstep; contradiction.
    - intros q l _.
      destruct q as [| [| [| [| [| q]]]]];
        destruct l as [[|] |];
        simpl;
        repeat constructor; simpl; intuition congruence.
  Qed.

  Definition section4_example_theorem5_final_not_max_initial :=
    lr1_initial_item_set Bool.bool_dec
      section4_example_theorem5_final_not_max_enfa 0.

  Definition section4_example_theorem5_final_not_max_after_eps :=
    lr1_goto Bool.bool_dec
      section4_example_theorem5_final_not_max_enfa
      section4_example_theorem5_final_not_max_initial
      (@LREpsilon bool nat).

  Ltac section4_example_solve_local_item :=
    repeat (first [left; reflexivity | right]);
    try reflexivity; try discriminate.

  Example section4_example_theorem5_final_not_max_canonical_reduce_conflict :
    lr1_same_lookahead_reduce_conflict Bool.bool_dec
      section4_example_theorem5_final_not_max_enfa
      section4_example_theorem5_final_not_max_after_eps.
  Proof.
    unfold lr1_same_lookahead_reduce_conflict.
    exists (LRFinal nat 1 LAEpsilon), (LRFinal nat 2 LAEpsilon), LAEpsilon.
    vm_compute. repeat split; section4_example_solve_local_item.
  Qed.

  Example section4_example_theorem5_final_not_max_da_prime_empty :
    enfa_da_prime_word
      section4_example_theorem5_final_not_max_enfa [] = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example section4_example_theorem5_final_not_max_accepting_counts_empty :
    map
      (enfa_accepting_maximal_simple_reach_count
         section4_example_theorem5_final_not_max_enfa [])
      [1; 2] =
    [1; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example section4_example_theorem5_final_not_max_dra_prime_empty :
    map
      (enfa_dra_prime_at
         section4_example_theorem5_final_not_max_enfa [])
      [0; 1; 2; 3; 4] =
    [1; 1; 1; 1; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example section4_example_theorem5_final_not_max_maximal_counts_empty :
    map
      (enfa_maximal_simple_reach_count
         section4_example_theorem5_final_not_max_enfa [])
      [0; 1; 2; 3; 4] =
    [0; 0; 0; 1; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example section4_example_theorem5_final_not_max_violates_final_no_epsilon :
    ~ section4_enfa_final_no_epsilon_successors
        section4_example_theorem5_final_not_max_enfa.
  Proof.
    intro Hno.
    specialize (Hno 1).
    simpl in Hno.
    specialize (Hno (or_intror (or_introl eq_refl)) eq_refl).
    discriminate.
  Qed.

  (** Gamma accepting-maximal reflection fuel regression.

      The ε-worklist below has more transition-processing steps than states:
      with state-count fuel, the strict closure from [0] missed [4].  The
      executable ε-transition bound makes the ENFA and Gamma/RLG strict
      closures agree, and both see the later final state [4]. *)
  Definition section4_example_gamma_fuel_enfa : @finite_enfa bool :=
    {|
      fenfa_base :=
        {|
          enfa_state := nat;
          enfa_start := [0];
          enfa_final :=
            fun q =>
              match q with
              | 0 => true
              | 4 => true
              | _ => false
              end;
          enfa_step :=
            fun q l =>
              match q, l with
              | 0, None => [1; 2; 3; 4]
              | 1, None => [0]
              | 2, None => [0]
              | 3, None => [0]
              | _, _ => []
              end
        |};
      fenfa_states := [0; 1; 2; 3; 4];
      fenfa_alphabet := [];
      fenfa_state_eqb := Nat.eqb;
      fenfa_state_eqb_sound := fun x y H => proj1 (Nat.eqb_eq x y) H;
      fenfa_state_eqb_complete := fun x y H => proj2 (Nat.eqb_eq x y) H
    |}.

  Definition section4_example_gamma_fuel_derivation :=
    gamma_derivation_of_trace section4_example_gamma_fuel_enfa 0 [] 0.

  Example section4_example_gamma_fuel_enfa_strict_closure :
    enfa_strict_epsilon_closure_states
      section4_example_gamma_fuel_enfa (0, []) =
    [1; 2; 3; 4].
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example section4_example_gamma_fuel_rlg_strict_closure :
    rlg_strict_epsilon_closure_nonterminals
      (gamma_grammar_from section4_example_gamma_fuel_enfa 0)
      Nat.eqb
      0
      section4_example_gamma_fuel_derivation =
    [1; 2; 3; 4].
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example section4_example_gamma_fuel_accepting_maximal_false :
    enfa_accepting_maximal_epsilon_simpleb
      section4_example_gamma_fuel_enfa (0, []) = false /\
    rlg_accepting_maximal_epsilon_simpleb
      (gamma_grammar_from section4_example_gamma_fuel_enfa 0)
      Nat.eqb
      0
      section4_example_gamma_fuel_derivation = false.
  Proof.
    vm_compute. auto.
  Qed.

  Example section4_example_gamma_fuel_accepting_maximal_agree :
    enfa_accepting_maximal_epsilon_simpleb
      section4_example_gamma_fuel_enfa (0, []) =
    rlg_accepting_maximal_epsilon_simpleb
      (gamma_grammar_from section4_example_gamma_fuel_enfa 0)
      Nat.eqb
      0
      section4_example_gamma_fuel_derivation.
  Proof.
    vm_compute. reflexivity.
  Qed.
End Section4Examples.
