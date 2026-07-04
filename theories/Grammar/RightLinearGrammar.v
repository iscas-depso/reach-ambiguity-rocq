From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Ambiguity Require Import DegreeofAmbiguity.
From PositionAutomata.Automata Require Import EpsilonNFA.

(** Section 4, Definitions 8--9 and Gamma bridge support for right-linear
    grammars.  Productions have the form [A -> u B] or [A -> u]. *)

Section RightLinearGrammar.
  Context {A : Type}.

  Record right_linear_grammar : Type := {
    rlg_nonterminal : Type;
    rlg_start : rlg_nonterminal;
    rlg_productions :
      list (rlg_nonterminal * list A * option rlg_nonterminal)
  }.

  (* Left nonterminal, generated terminal word, and optional right nonterminal. *)
  Definition rlg_production (G : right_linear_grammar) : Type :=
    (rlg_nonterminal G * list A * option (rlg_nonterminal G))%type.

  (** CFG-level statements for paper Definitions 8 and 9.

      The paper states these definitions for CFGs, while the Gamma bridge
      later specializes them to right-linear grammars.  This layer records the
      general rightmost-derivation objects that Definition 8 counts, including
      the left/right boundary terminals used by the augmented grammar notation.
      Ordinary ambiguity uses the unmarked start form [S]; reach ambiguity and
      leaves use the marked start form [left S], so the displayed
      [left alpha A beta] and [left alpha beta] forms are reachable without
      requiring an ad hoc production for the marker.  The prime clauses take
      the epsilon-simple/maximal predicates as parameters; the executable
      right-linear instance below supplies concrete Boolean filters. *)
  Inductive cfg_symbol (N : Type) : Type :=
  | CfgTerminal : A -> cfg_symbol N
  | CfgNonterminal : N -> cfg_symbol N
  | CfgLeftMarker : cfg_symbol N
  | CfgRightMarker : cfg_symbol N.

  Arguments CfgTerminal {N} _.
  Arguments CfgNonterminal {N} _.
  Arguments CfgLeftMarker {N}.
  Arguments CfgRightMarker {N}.

  Definition cfg_sentential_form (N : Type) : Type := list (cfg_symbol N).

  Record context_free_grammar : Type := {
    cfg_nonterminal : Type;
    cfg_start : cfg_nonterminal;
    cfg_productions :
      list (cfg_nonterminal * cfg_sentential_form cfg_nonterminal)
  }.

  Definition cfg_production (G : context_free_grammar) : Type :=
    (cfg_nonterminal G * cfg_sentential_form (cfg_nonterminal G))%type.

  Definition cfg_terminal_word
      (G : context_free_grammar)
      (w : list A) : cfg_sentential_form (cfg_nonterminal G) :=
    map (@CfgTerminal (cfg_nonterminal G)) w.

  Definition cfg_start_form
      (G : context_free_grammar) : cfg_sentential_form (cfg_nonterminal G) :=
    [CfgNonterminal (cfg_start G)].

  Definition cfg_marked_start_form
      (G : context_free_grammar) : cfg_sentential_form (cfg_nonterminal G) :=
    [CfgLeftMarker; CfgNonterminal (cfg_start G)].

  Fixpoint cfg_all_terminals
      {N : Type} (sf : cfg_sentential_form N) : Prop :=
    match sf with
    | [] => True
    | CfgTerminal _ :: sf' => cfg_all_terminals sf'
    | CfgLeftMarker :: sf' => cfg_all_terminals sf'
    | CfgRightMarker :: sf' => cfg_all_terminals sf'
    | CfgNonterminal _ :: _ => False
    end.

  Fixpoint cfg_no_boundary_markers
      {N : Type} (sf : cfg_sentential_form N) : Prop :=
    match sf with
    | [] => True
    | CfgTerminal _ :: sf' => cfg_no_boundary_markers sf'
    | CfgNonterminal _ :: sf' => cfg_no_boundary_markers sf'
    | CfgLeftMarker :: _ => False
    | CfgRightMarker :: _ => False
    end.

  Inductive cfg_rightmost_step_by_production
      (G : context_free_grammar)
      : cfg_sentential_form (cfg_nonterminal G) ->
        cfg_production G ->
        cfg_sentential_form (cfg_nonterminal G) -> Prop :=
  | CFGRightmost_step :
      forall left suffix X rhs,
        In (X, rhs) (cfg_productions G) ->
        cfg_all_terminals suffix ->
        cfg_rightmost_step_by_production G
          (left ++ (CfgNonterminal X :: suffix))
          (X, rhs)
          (left ++ rhs ++ suffix).

  Definition cfg_derivation (G : context_free_grammar) : Type :=
    list (cfg_production G).

  Inductive cfg_rightmost_derivation_valid
      (G : context_free_grammar)
      : cfg_sentential_form (cfg_nonterminal G) ->
        cfg_derivation G ->
        cfg_sentential_form (cfg_nonterminal G) -> Prop :=
  | CFGDerivation_nil :
      forall alpha,
        cfg_rightmost_derivation_valid G alpha [] alpha
  | CFGDerivation_step :
      forall alpha beta gamma p d,
        cfg_rightmost_step_by_production G alpha p beta ->
        cfg_rightmost_derivation_valid G beta d gamma ->
        cfg_rightmost_derivation_valid G alpha (p :: d) gamma.

  Definition cfg_marked_rightmost_derivation_valid
      (G : context_free_grammar)
      (d : cfg_derivation G)
      (gamma : cfg_sentential_form (cfg_nonterminal G)) : Prop :=
    cfg_rightmost_derivation_valid G (cfg_marked_start_form G) d gamma.

  (* Definition 8 I.i *)
  Definition cfg_da_derivation
      (G : context_free_grammar)
      (w : list A)
      (d : cfg_derivation G) : Prop :=
    cfg_rightmost_derivation_valid G
      (cfg_start_form G) d (cfg_terminal_word G w).

  (* Definition 8 I.ii *)
  Definition cfg_dra_derivation
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (X : cfg_nonterminal G)
      (d : cfg_derivation G) : Prop :=
    cfg_no_boundary_markers alpha /\
    exists beta,
      cfg_no_boundary_markers beta /\
      cfg_marked_rightmost_derivation_valid G d
        ([CfgLeftMarker] ++ alpha ++ (CfgNonterminal X :: beta)).

  (* Definition 8 I.iii *)
  Definition cfg_leaf_derivation
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (d : cfg_derivation G) : Prop :=
    cfg_no_boundary_markers alpha /\
    exists beta,
      cfg_no_boundary_markers beta /\
      cfg_marked_rightmost_derivation_valid G d
        ([CfgLeftMarker] ++ alpha ++ beta).

  Definition cfg_derivation_factor
      (G : context_free_grammar)
      (factor d : cfg_derivation G) : Prop :=
    exists prefix suffix, d = prefix ++ factor ++ suffix.

  Definition cfg_left_epsilon_cycle_derivation
      (G : context_free_grammar)
      (X : cfg_nonterminal G)
      (d : cfg_derivation G) : Prop :=
    d <> [] /\
    cfg_rightmost_derivation_valid G
      [CfgNonterminal X] d [CfgLeftMarker; CfgNonterminal X].

  (* Definition 4 II, CFG specification part:
     no factor of the derivation witnesses [A =>+ left A]. *)
  Definition cfg_derivation_epsilon_simple
      (G : context_free_grammar)
      (d : cfg_derivation G) : Prop :=
    forall X factor,
      cfg_derivation_factor G factor d ->
      ~ cfg_left_epsilon_cycle_derivation G X factor.

  (* Definition 4 II: maximal epsilon-simple derivations.
     Maximality is taken with respect to the factor order on derivations,
     restricted to epsilon-simplederivations in the ambient set S.
     Thus [cfg_derivation_maximal_epsilon_simple_in G S d] means that
     [d] is an epsilon-simple maximal element of [S], i.e. 
     an element of the paper's ceiling construction ⌈S⌉.
  *)
  Definition cfg_derivation_maximal_epsilon_simple_in
      (G : context_free_grammar)
      (S : cfg_derivation G -> Prop)
      (d : cfg_derivation G) : Prop :=
    S d /\
    cfg_derivation_epsilon_simple G d /\
    forall d',
      S d' ->
      cfg_derivation_epsilon_simple G d' ->
      cfg_derivation_factor G d d' ->
      d' = d.

  Definition cfg_da_derivation_set
      (G : context_free_grammar)
      (w : list A) : cfg_derivation G -> Prop :=
    cfg_da_derivation G w.

  Definition cfg_dra_derivation_set
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (X : cfg_nonterminal G) : cfg_derivation G -> Prop :=
    cfg_dra_derivation G alpha X.

  Definition cfg_leaf_derivation_set
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      : cfg_derivation G -> Prop :=
    cfg_leaf_derivation G alpha.

  (* Definition 8 II.i *)
  Definition cfg_da_prime_derivation
      (G : context_free_grammar)
      (w : list A)
      (d : cfg_derivation G) : Prop :=
    cfg_derivation_maximal_epsilon_simple_in
      G (cfg_da_derivation_set G w) d.

  (* Definition 8 II.ii *)
  Definition cfg_dra_prime_derivation
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (X : cfg_nonterminal G)
      (d : cfg_derivation G) : Prop :=
    cfg_dra_derivation G alpha X d /\
    cfg_derivation_epsilon_simple G d.

  (* Definition 8 II.iii *)
  Definition cfg_leaf_prime_derivation
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (d : cfg_derivation G) : Prop :=
    cfg_derivation_maximal_epsilon_simple_in
      G (cfg_leaf_derivation_set G alpha) d.

  (* Definition 9 I *)
  Definition cfg_prime_unambiguous
      (G : context_free_grammar) : Prop :=
    forall w d1 d2,
      cfg_da_prime_derivation G w d1 ->
      cfg_da_prime_derivation G w d2 ->
      d1 = d2.

  (* Definition 9 II *)
  Definition cfg_prime_reach_unambiguous
      (G : context_free_grammar) : Prop :=
    forall alpha X d1 d2,
      cfg_dra_prime_derivation G alpha X d1 ->
      cfg_dra_prime_derivation G alpha X d2 ->
      d1 = d2.

  (* Definition 9 III *)
  Definition cfg_prime_leaf_unambiguous
      (G : context_free_grammar) : Prop :=
    forall alpha d1 d2,
      cfg_leaf_prime_derivation G alpha d1 ->
      cfg_leaf_prime_derivation G alpha d2 ->
      d1 = d2.

  Definition section4_finite_cardinality {B : Type}
      (P : B -> Prop)
      (xs : list B) : Prop :=
    NoDup xs /\ forall x, In x xs <-> P x.

  Definition section4_cardinality {B : Type}
      (P : B -> Prop)
      (n : nat) : Prop :=
    exists xs, section4_finite_cardinality P xs /\ length xs = n.

  Lemma section4_finite_cardinality_length_unique :
    forall {B : Type} (P : B -> Prop) xs ys,
      section4_finite_cardinality P xs ->
      section4_finite_cardinality P ys ->
      length xs = length ys.
  Proof.
    intros B P xs ys [Hnodup_xs Hxs] [Hnodup_ys Hys].
    apply Nat.le_antisymm.
    - eapply NoDup_incl_length; eauto.
      intros x Hx.
      apply Hys.
      now apply Hxs.
    - eapply NoDup_incl_length; eauto.
      intros y Hy.
      apply Hxs.
      now apply Hys.
  Qed.

  Lemma section4_cardinality_functional :
    forall {B : Type} (P : B -> Prop) n m,
      section4_cardinality P n ->
      section4_cardinality P m ->
      n = m.
  Proof.
    intros B P n m [xs [Hxs Hlen_xs]] [ys [Hys Hlen_ys]].
    subst.
    now apply section4_finite_cardinality_length_unique with (P := P).
  Qed.

  Lemma section4_NoDup_length_le_one_unique :
    forall {B : Type} (xs : list B) x y,
      NoDup xs ->
      length xs <= 1 ->
      In x xs ->
      In y xs ->
      x = y.
  Proof.
    intros B xs x y _ Hle Hx Hy.
    destruct xs as [| a xs].
    - contradiction.
    - destruct xs as [| b xs].
      + simpl in Hx, Hy.
        destruct Hx as [-> | []].
        destruct Hy as [-> | []].
        reflexivity.
      + simpl in Hle. lia.
  Qed.

  Lemma section4_NoDup_unique_length_le_one :
    forall {B : Type} (xs : list B),
      NoDup xs ->
      (forall x y, In x xs -> In y xs -> x = y) ->
      length xs <= 1.
  Proof.
    intros B xs Hnodup Hunique.
    destruct xs as [| x xs].
    - simpl. lia.
    - destruct xs as [| y ys].
      + simpl. lia.
      + inversion Hnodup as [| ? ? Hnotin _]; subst.
        exfalso.
        assert (x = y) as Heq.
        { apply Hunique; simpl; auto. }
        subst.
        apply Hnotin. simpl. auto.
  Qed.

  Lemma section4_finite_cardinality_le_one_unique :
    forall {B : Type} (P : B -> Prop) xs,
      section4_finite_cardinality P xs ->
      length xs <= 1 ->
      forall x y, P x -> P y -> x = y.
  Proof.
    intros B P xs [Hnodup Hxs] Hle x y HPx HPy.
    eapply section4_NoDup_length_le_one_unique; eauto.
    - now apply Hxs.
    - now apply Hxs.
  Qed.

  Lemma section4_finite_cardinality_unique_le_one :
    forall {B : Type} (P : B -> Prop) xs,
      section4_finite_cardinality P xs ->
      (forall x y, P x -> P y -> x = y) ->
      length xs <= 1.
  Proof.
    intros B P xs [Hnodup Hxs] Hunique.
    eapply section4_NoDup_unique_length_le_one; eauto.
    intros x y Hinx Hiny.
    apply Hunique; now apply Hxs.
  Qed.

  Lemma section4_finite_cardinality_le_one_iff_unique :
    forall {B : Type} (P : B -> Prop) xs,
      section4_finite_cardinality P xs ->
      length xs <= 1 <-> forall x y, P x -> P y -> x = y.
  Proof.
    intros B P xs Hcard.
    split.
    - now apply section4_finite_cardinality_le_one_unique.
    - now apply section4_finite_cardinality_unique_le_one.
  Qed.

  Inductive section4_enat : Type :=
  | Section4Finite : nat -> section4_enat
  | Section4Infinite : section4_enat.

  Definition section4_enat_le
      (x y : section4_enat) : Prop :=
    match x, y with
    | Section4Finite n, Section4Finite m => n <= m
    | Section4Finite _, Section4Infinite => True
    | Section4Infinite, Section4Infinite => True
    | Section4Infinite, Section4Finite _ => False
    end.

  Definition section4_enat_upper_bound {I : Type}
      (measure : I -> section4_enat -> Prop)
      (bound : section4_enat) : Prop :=
    forall i c, measure i c -> section4_enat_le c bound.

  Definition section4_enat_supremum {I : Type}
      (measure : I -> section4_enat -> Prop)
      (sup : section4_enat) : Prop :=
    section4_enat_upper_bound measure sup /\
    forall bound, section4_enat_upper_bound measure bound ->
      section4_enat_le sup bound.

  Definition section4_enat_supremum_le {I : Type}
      (measure : I -> section4_enat -> Prop)
      (bound : section4_enat) : Prop :=
    exists sup, section4_enat_supremum measure sup /\
      section4_enat_le sup bound.

  Definition section4_infinite_cardinality {B : Type}
      (P : B -> Prop) : Prop :=
    exists f : nat -> B,
      (forall n, P (f n)) /\
      forall i j, f i = f j -> i = j.

  Definition section4_extended_cardinality {B : Type}
      (P : B -> Prop)
      (c : section4_enat) : Prop :=
    match c with
    | Section4Finite n => section4_cardinality P n
    | Section4Infinite => section4_infinite_cardinality P
    end.

  Lemma section4_finite_cardinality_not_infinite :
    forall {B : Type} (P : B -> Prop) xs,
      section4_finite_cardinality P xs ->
      section4_infinite_cardinality P ->
      False.
  Proof.
    intros B P xs [Hnodup Hxs] [f [Hf Hinj]].
    pose (ns := seq 0 (S (length xs))).
    assert (Hmap_nodup : NoDup (map f ns)).
    { apply NoDup_map_injective_in.
      - intros i j _ _ Heq. now apply Hinj.
      - apply seq_NoDup.
    }
    assert (Hincl : incl (map f ns) xs).
    { intros y Hy.
      apply in_map_iff in Hy as [n [<- _]].
      apply Hxs. apply Hf.
    }
    pose proof (NoDup_incl_length Hmap_nodup Hincl) as Hle.
    unfold ns in Hle. rewrite length_map, length_seq in Hle. lia.
  Qed.

  Lemma section4_cardinality_not_infinite :
    forall {B : Type} (P : B -> Prop) n,
      section4_cardinality P n ->
      section4_infinite_cardinality P ->
      False.
  Proof.
    intros B P n [xs [Hfinite _]] Hinf.
    eapply section4_finite_cardinality_not_infinite; eauto.
  Qed.

  Lemma section4_extended_cardinality_functional :
    forall {B : Type} (P : B -> Prop) c1 c2,
      section4_extended_cardinality P c1 ->
      section4_extended_cardinality P c2 ->
      c1 = c2.
  Proof.
    intros B P [n1 |] [n2 |] H1 H2; simpl in *.
    - f_equal. eapply section4_cardinality_functional; eauto.
    - exfalso. eapply section4_cardinality_not_infinite; eauto.
    - exfalso. eapply section4_cardinality_not_infinite; eauto.
    - reflexivity.
  Qed.

  Lemma section4_enat_infinite_supremum_of_infinite_measure :
    forall {I : Type} (measure : I -> section4_enat -> Prop) i,
      measure i Section4Infinite ->
      section4_enat_supremum measure Section4Infinite.
  Proof.
    intros I measure i Hinf.
    split.
    - intros j [n |] _; simpl; auto.
    - intros [bound |] Hupper; simpl; auto.
      specialize (Hupper i Section4Infinite Hinf).
      simpl in Hupper. contradiction.
  Qed.

  Definition section4_definition8_I_i_cfg_da_cardinality
      (G : context_free_grammar)
      (w : list A)
      (n : nat) : Prop :=
    section4_cardinality (cfg_da_derivation G w) n.

  Definition section4_definition8_I_ii_cfg_dra_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (X : cfg_nonterminal G)
      (n : nat) : Prop :=
    section4_cardinality (cfg_dra_derivation G alpha X) n.

  Definition section4_definition8_I_iii_cfg_leaf_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (n : nat) : Prop :=
    section4_cardinality (cfg_leaf_derivation G alpha) n.

  Definition section4_definition8_II_i_cfg_da_prime_cardinality
      (G : context_free_grammar)
      (w : list A)
      (n : nat) : Prop :=
    section4_cardinality (cfg_da_prime_derivation G w) n.

  Definition section4_definition8_II_ii_cfg_dra_prime_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (X : cfg_nonterminal G)
      (n : nat) : Prop :=
    section4_cardinality (cfg_dra_prime_derivation G alpha X) n.

  Definition section4_definition8_II_iii_cfg_leaf_prime_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (n : nat) : Prop :=
    section4_cardinality (cfg_leaf_prime_derivation G alpha) n.

  Definition section4_definition8_I_i_cfg_da_extended_cardinality
      (G : context_free_grammar)
      (w : list A)
      (c : section4_enat) : Prop :=
    section4_extended_cardinality (cfg_da_derivation G w) c.

  Definition section4_definition8_I_ii_cfg_dra_extended_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (X : cfg_nonterminal G)
      (c : section4_enat) : Prop :=
    section4_extended_cardinality (cfg_dra_derivation G alpha X) c.

  Definition section4_definition8_I_iii_cfg_leaf_extended_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (c : section4_enat) : Prop :=
    section4_extended_cardinality (cfg_leaf_derivation G alpha) c.

  Definition section4_definition8_II_i_cfg_da_prime_extended_cardinality
      (G : context_free_grammar)
      (w : list A)
      (c : section4_enat) : Prop :=
    section4_extended_cardinality (cfg_da_prime_derivation G w) c.

  Definition section4_definition8_II_ii_cfg_dra_prime_extended_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (X : cfg_nonterminal G)
      (c : section4_enat) : Prop :=
    section4_extended_cardinality (cfg_dra_prime_derivation G alpha X) c.

  Definition section4_definition8_II_iii_cfg_leaf_prime_extended_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (c : section4_enat) : Prop :=
    section4_extended_cardinality (cfg_leaf_prime_derivation G alpha) c.

  Definition section4_nat_upper_bound {I : Type}
      (measure : I -> nat -> Prop)
      (bound : nat) : Prop :=
    forall i n, measure i n -> n <= bound.

  Definition section4_nat_supremum {I : Type}
      (measure : I -> nat -> Prop)
      (sup : nat) : Prop :=
    section4_nat_upper_bound measure sup /\
    forall bound, section4_nat_upper_bound measure bound -> sup <= bound.

  Definition section4_nat_supremum_le {I : Type}
      (measure : I -> nat -> Prop)
      (bound : nat) : Prop :=
    exists sup, section4_nat_supremum measure sup /\ sup <= bound.

  Lemma section4_nat_supremum_le_upper_bound :
    forall {I : Type} (measure : I -> nat -> Prop) bound,
      section4_nat_supremum_le measure bound ->
      section4_nat_upper_bound measure bound.
  Proof.
    intros I measure bound [sup [[Hupper _] Hle]] i n Hmeasure.
    specialize (Hupper i n Hmeasure).
    lia.
  Qed.

  Definition cfg_da_prime_finite_cardinality
      (G : context_free_grammar)
      (w : list A)
      (n : nat) : Prop :=
    section4_definition8_II_i_cfg_da_prime_cardinality G w n.

  Definition cfg_dra_prime_finite_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (X : cfg_nonterminal G)
      (n : nat) : Prop :=
    section4_definition8_II_ii_cfg_dra_prime_cardinality G alpha X n.

  Definition cfg_leaf_prime_finite_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (n : nat) : Prop :=
    section4_definition8_II_iii_cfg_leaf_prime_cardinality G alpha n.

  Definition cfg_da_prime_extended_cardinality
      (G : context_free_grammar)
      (w : list A)
      (c : section4_enat) : Prop :=
    section4_definition8_II_i_cfg_da_prime_extended_cardinality G w c.

  Definition cfg_dra_prime_extended_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (X : cfg_nonterminal G)
      (c : section4_enat) : Prop :=
    section4_definition8_II_ii_cfg_dra_prime_extended_cardinality G alpha X c.

  Definition cfg_leaf_prime_extended_cardinality
      (G : context_free_grammar)
      (alpha : cfg_sentential_form (cfg_nonterminal G))
      (c : section4_enat) : Prop :=
    section4_definition8_II_iii_cfg_leaf_prime_extended_cardinality G alpha c.

  Definition cfg_reach_index (G : context_free_grammar) : Type :=
    (cfg_sentential_form (cfg_nonterminal G) * cfg_nonterminal G)%type.

  Definition section4_definition9_I_cfg_da_prime_degree_le
      (G : context_free_grammar)
      (bound : nat) : Prop :=
    section4_nat_upper_bound
      (fun w n => cfg_da_prime_finite_cardinality G w n)
      bound.

  Definition section4_definition9_II_cfg_dra_prime_degree_le
      (G : context_free_grammar)
      (bound : nat) : Prop :=
    section4_nat_upper_bound
      (fun ix n =>
         cfg_dra_prime_finite_cardinality G (fst ix) (snd ix) n)
      bound.

  Definition section4_definition9_III_cfg_leaf_prime_degree_le
      (G : context_free_grammar)
      (bound : nat) : Prop :=
    section4_nat_upper_bound
      (fun alpha n => cfg_leaf_prime_finite_cardinality G alpha n)
      bound.

  (* Exact finite-supremum predicates over finite-cardinality witnesses.
     Infinite and extended-natural readings are provided by the extended
     cardinality layer below. *)
  Definition section4_definition9_I_cfg_da_prime_degree
      (G : context_free_grammar)
      (degree : nat) : Prop :=
    section4_nat_supremum
      (fun w n => cfg_da_prime_finite_cardinality G w n)
      degree.

  Definition section4_definition9_II_cfg_dra_prime_degree
      (G : context_free_grammar)
      (degree : nat) : Prop :=
    section4_nat_supremum
      (fun ix n =>
         cfg_dra_prime_finite_cardinality G (fst ix) (snd ix) n)
      degree.

  Definition section4_definition9_III_cfg_leaf_prime_degree
      (G : context_free_grammar)
      (degree : nat) : Prop :=
    section4_nat_supremum
      (fun alpha n => cfg_leaf_prime_finite_cardinality G alpha n)
      degree.

  Definition section4_definition9_I_cfg_da_prime_extended_degree_le
      (G : context_free_grammar)
      (bound : section4_enat) : Prop :=
    section4_enat_upper_bound
      (fun w c => cfg_da_prime_extended_cardinality G w c)
      bound.

  Definition section4_definition9_II_cfg_dra_prime_extended_degree_le
      (G : context_free_grammar)
      (bound : section4_enat) : Prop :=
    section4_enat_upper_bound
      (fun ix c =>
         cfg_dra_prime_extended_cardinality G (fst ix) (snd ix) c)
      bound.

  Definition section4_definition9_III_cfg_leaf_prime_extended_degree_le
      (G : context_free_grammar)
      (bound : section4_enat) : Prop :=
    section4_enat_upper_bound
      (fun alpha c => cfg_leaf_prime_extended_cardinality G alpha c)
      bound.

  Definition section4_definition9_I_cfg_da_prime_extended_degree
      (G : context_free_grammar)
      (degree : section4_enat) : Prop :=
    section4_enat_supremum
      (fun w c => cfg_da_prime_extended_cardinality G w c)
      degree.

  Definition section4_definition9_II_cfg_dra_prime_extended_degree
      (G : context_free_grammar)
      (degree : section4_enat) : Prop :=
    section4_enat_supremum
      (fun ix c =>
         cfg_dra_prime_extended_cardinality G (fst ix) (snd ix) c)
      degree.

  Definition section4_definition9_III_cfg_leaf_prime_extended_degree
      (G : context_free_grammar)
      (degree : section4_enat) : Prop :=
    section4_enat_supremum
      (fun alpha c => cfg_leaf_prime_extended_cardinality G alpha c)
      degree.

  Theorem section4_definition9_I_cfg_unambiguous_iff_da_prime_degree_le_one_under_finite_cardinality :
    forall (G : context_free_grammar),
      (forall w, exists n, cfg_da_prime_finite_cardinality G w n) ->
      cfg_prime_unambiguous G <->
      section4_definition9_I_cfg_da_prime_degree_le G 1.
  Proof.
    intros G Hfinite.
    split.
    - intros Huniq w n [xs [Hcard Hlen]].
      rewrite <- Hlen.
      apply (section4_finite_cardinality_unique_le_one
               (cfg_da_prime_derivation G w) xs Hcard).
      intros d1 d2 Hd1 Hd2.
      eapply Huniq; eauto.
    - intros Hdegree w d1 d2 Hd1 Hd2.
      destruct (Hfinite w) as [n [xs [Hcard Hlen]]].
      eapply section4_finite_cardinality_le_one_unique; eauto.
      rewrite Hlen.
      eapply Hdegree.
      exists xs. split; eauto.
  Qed.

  Theorem section4_definition9_II_cfg_reach_unambiguous_iff_dra_prime_degree_le_one_under_finite_cardinality :
    forall (G : context_free_grammar),
      (forall alpha X,
          exists n, cfg_dra_prime_finite_cardinality G alpha X n) ->
      cfg_prime_reach_unambiguous G <->
      section4_definition9_II_cfg_dra_prime_degree_le G 1.
  Proof.
    intros G Hfinite.
    split.
    - intros Huniq [alpha X] n [xs [Hcard Hlen]].
      rewrite <- Hlen.
      apply (section4_finite_cardinality_unique_le_one
               (cfg_dra_prime_derivation G alpha X) xs Hcard).
      intros d1 d2 Hd1 Hd2.
      eapply Huniq; eauto.
    - intros Hdegree alpha X d1 d2 Hd1 Hd2.
      destruct (Hfinite alpha X) as [n [xs [Hcard Hlen]]].
      eapply section4_finite_cardinality_le_one_unique; eauto.
      rewrite Hlen.
      eapply (Hdegree (alpha, X) n).
      exists xs. split; eauto.
  Qed.

  Theorem section4_definition9_III_cfg_leaf_unambiguous_iff_leaf_prime_degree_le_one_under_finite_cardinality :
    forall (G : context_free_grammar),
      (forall alpha, exists n, cfg_leaf_prime_finite_cardinality G alpha n) ->
      cfg_prime_leaf_unambiguous G <->
      section4_definition9_III_cfg_leaf_prime_degree_le G 1.
  Proof.
    intros G Hfinite.
    split.
    - intros Huniq alpha n [xs [Hcard Hlen]].
      rewrite <- Hlen.
      apply (section4_finite_cardinality_unique_le_one
               (cfg_leaf_prime_derivation G alpha) xs Hcard).
      intros d1 d2 Hd1 Hd2.
      eapply Huniq; eauto.
    - intros Hdegree alpha d1 d2 Hd1 Hd2.
      destruct (Hfinite alpha) as [n [xs [Hcard Hlen]]].
      eapply section4_finite_cardinality_le_one_unique; eauto.
      rewrite Hlen.
      eapply Hdegree.
      exists xs. split; eauto.
  Qed.

  Definition section4_definition8_I_i_cfg_da := cfg_da_derivation.
  Definition section4_definition8_I_ii_cfg_dra := cfg_dra_derivation.
  Definition section4_definition8_I_iii_cfg_leaf := cfg_leaf_derivation.
  Definition section4_definition8_II_i_cfg_da_prime :=
    cfg_da_prime_derivation.
  Definition section4_definition8_II_ii_cfg_dra_prime :=
    cfg_dra_prime_derivation.
  Definition section4_definition8_II_iii_cfg_leaf_prime :=
    cfg_leaf_prime_derivation.
  Definition section4_definition9_I_cfg_unambiguous :=
    cfg_prime_unambiguous.
  Definition section4_definition9_II_cfg_reach_unambiguous :=
    cfg_prime_reach_unambiguous.
  Definition section4_definition9_III_cfg_leaf_unambiguous :=
    cfg_prime_leaf_unambiguous.

  (** Definitions 8/9 base semantics: a right-linear grammar derives a
      terminal word from a nonterminal.  The explicit derivation layer below
      keeps production sequences so ambiguity can distinguish derivations. *)
  Definition section4_cfg_self_loop : context_free_grammar :=
    {|
      cfg_nonterminal := unit;
      cfg_start := tt;
      cfg_productions := [(tt, [CfgNonterminal tt])]
    |}.

  Definition section4_cfg_self_loop_production
      : cfg_production section4_cfg_self_loop :=
    (tt, [CfgNonterminal tt]).

  Definition section4_cfg_self_loop_derivation (n : nat)
      : cfg_derivation section4_cfg_self_loop :=
    repeat section4_cfg_self_loop_production n.

  Lemma section4_cfg_self_loop_marked_derivation_repeat :
    forall n,
      cfg_marked_rightmost_derivation_valid
        section4_cfg_self_loop
        (section4_cfg_self_loop_derivation n)
        [CfgLeftMarker; CfgNonterminal tt].
  Proof.
    unfold cfg_marked_rightmost_derivation_valid.
    induction n as [| n IH]; simpl.
    - constructor.
    - eapply CFGDerivation_step
        with (beta := [CfgLeftMarker; CfgNonterminal tt]).
      + change
          (cfg_rightmost_step_by_production
             section4_cfg_self_loop
             ([CfgLeftMarker] ++ CfgNonterminal tt :: [])
             (tt, [CfgNonterminal tt])
             ([CfgLeftMarker] ++ [CfgNonterminal tt] ++ [])).
        constructor; simpl; auto.
      + exact IH.
  Qed.

  Lemma section4_cfg_self_loop_dra_repeat :
    forall n,
      cfg_dra_derivation
        section4_cfg_self_loop
        []
        tt
        (section4_cfg_self_loop_derivation n).
  Proof.
    intro n.
    split; simpl; auto.
    exists []. split; simpl; auto.
    apply section4_cfg_self_loop_marked_derivation_repeat.
  Qed.

  Lemma section4_cfg_self_loop_derivation_injective :
    forall i j,
      section4_cfg_self_loop_derivation i =
      section4_cfg_self_loop_derivation j ->
      i = j.
  Proof.
    intros i j Heq.
    apply (f_equal (@length _)) in Heq.
    unfold section4_cfg_self_loop_derivation in Heq.
    repeat rewrite repeat_length in Heq.
    exact Heq.
  Qed.

  Theorem section4_cfg_self_loop_dra_fiber_infinite :
    section4_infinite_cardinality
      (cfg_dra_derivation section4_cfg_self_loop [] tt).
  Proof.
    exists section4_cfg_self_loop_derivation.
    split.
    - apply section4_cfg_self_loop_dra_repeat.
    - apply section4_cfg_self_loop_derivation_injective.
  Qed.

  Theorem section4_cfg_self_loop_dra_extended_cardinality_infinite :
    section4_definition8_I_ii_cfg_dra_extended_cardinality
      section4_cfg_self_loop [] tt Section4Infinite.
  Proof.
    exact section4_cfg_self_loop_dra_fiber_infinite.
  Qed.

  Theorem section4_cfg_self_loop_dra_fiber_not_finite :
    ~ exists xs,
        section4_finite_cardinality
          (cfg_dra_derivation section4_cfg_self_loop [] tt)
          xs.
  Proof.
    intros [xs Hfinite].
    eapply section4_finite_cardinality_not_infinite; eauto.
    exact section4_cfg_self_loop_dra_fiber_infinite.
  Qed.

  Inductive rlg_derives_from (G : right_linear_grammar)
      : rlg_nonterminal G -> list A -> Prop :=
  | RLG_stop :
      forall X u,
        In (X, u, None) (rlg_productions G) ->
        rlg_derives_from G X u
  | RLG_step :
      forall X u Y v,
        In (X, u, Some Y) (rlg_productions G) ->
        rlg_derives_from G Y v ->
        rlg_derives_from G X (u ++ v).

  (** Definitions 8/9 explicit derivations.  Unlike [rlg_derives_from],
      [rlg_derivation] stores the production sequence, so equality of
      accepting derivations can be stated directly. *)
  Definition rlg_derivation (G : right_linear_grammar) : Type :=
    list (rlg_production G).

  Fixpoint rlg_derivation_word
      (G : right_linear_grammar)
      (d : rlg_derivation G) : list A :=
    match d with
    | [] => []
    | (_, u, _) :: d' => u ++ rlg_derivation_word G d'
    end.

  Inductive rlg_derivation_valid (G : right_linear_grammar)
      : rlg_nonterminal G -> rlg_derivation G ->
        option (rlg_nonterminal G) -> Prop :=
  | RLGDerivation_stop :
      forall X u,
        In (X, u, None) (rlg_productions G) ->
        rlg_derivation_valid G X [(X, u, None)] None
  | RLGDerivation_step :
      forall X u Y d tail,
        In (X, u, Some Y) (rlg_productions G) ->
        rlg_derivation_valid G Y d tail ->
        rlg_derivation_valid G X ((X, u, Some Y) :: d) tail.

  Definition rlg_derivation_accepting
      (G : right_linear_grammar)
      (w : list A)
      (d : rlg_derivation G) : Prop :=
    rlg_derivation_valid G (rlg_start G) d None /\
    rlg_derivation_word G d = w.

  (** Bounded enumeration interface connecting the Definitions 8/9 counting
      specs to executable finite lists. *)
  Fixpoint rlg_derivations_from_fuel
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (fuel : nat)
      (X : rlg_nonterminal G) : list (rlg_derivation G) :=
    match fuel with
    | O => []
    | S fuel' =>
        concat
          (map
             (fun prod =>
                match prod with
                | (Y, _u, None) =>
                    if nt_eqb X Y then [[prod]] else []
                | (Y, _u, Some Z) =>
                    if nt_eqb X Y
                    then
                      map (fun d => prod :: d)
                        (rlg_derivations_from_fuel G nt_eqb fuel' Z)
                    else []
                end)
             (rlg_productions G))
    end.

  (** Prefix derivations model reach ambiguity: a derivation may stop at a
      nonterminal [X], meaning it has read a prefix and reached [X]. *)
  Inductive rlg_prefix_derivation_valid (G : right_linear_grammar)
      : rlg_nonterminal G -> rlg_derivation G ->
        rlg_nonterminal G -> Prop :=
  | RLGPrefix_nil :
      forall X, rlg_prefix_derivation_valid G X [] X
  | RLGPrefix_step :
      forall X u Y d Z,
        In (X, u, Some Y) (rlg_productions G) ->
        rlg_prefix_derivation_valid G Y d Z ->
        rlg_prefix_derivation_valid G X ((X, u, Some Y) :: d) Z.

  Definition rlg_prefix_derivation_word
      (G : right_linear_grammar)
      (d : rlg_derivation G) : list A :=
    rlg_derivation_word G d.

  Fixpoint rlg_prefix_derivations_from_fuel
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (fuel : nat)
      (X : rlg_nonterminal G) : list (rlg_derivation G) :=
    match fuel with
    | O => [[]]
    | S fuel' =>
        [[]] ++
        concat
          (map
             (fun prod =>
                match prod with
                | (Y, _u, None) => []
                | (Y, _u, Some Z) =>
                    if nt_eqb X Y
                    then
                      map (fun d => prod :: d)
                        (rlg_prefix_derivations_from_fuel G nt_eqb fuel' Z)
                    else []
                end)
             (rlg_productions G))
    end.

  (** Epsilon-simple/maximal filters for prime counts.  These correspond to
      the primed [da'], [dra'], and [Leaf'] measures: only epsilon-simple
      traces/derivations, maximal at the epsilon suffix where required, count. *)
  Fixpoint rlg_derivation_end
      (G : right_linear_grammar)
      (X : rlg_nonterminal G)
      (d : rlg_derivation G) : rlg_nonterminal G :=
    match d with
    | [] => X
    | (Y, _, None) :: _ => Y
    | (_, _, Some Y) :: d' => rlg_derivation_end G Y d'
    end.

  Definition rlg_nt_inb
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (X : rlg_nonterminal G)
      (xs : list (rlg_nonterminal G)) : bool :=
    existsb (nt_eqb X) xs.

  Definition rlg_epsilon_successors
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (X : rlg_nonterminal G) : list (rlg_nonterminal G) :=
    concat
      (map
         (fun prod =>
            match prod with
            | (Y, [], Some Z) =>
                if nt_eqb X Y then [Z] else []
            | _ => []
            end)
         (rlg_productions G)).

  Fixpoint rlg_epsilon_closure_fuel
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (fuel : nat)
      (seen todo : list (rlg_nonterminal G))
      : list (rlg_nonterminal G) :=
    match fuel with
    | O => []
    | S fuel' =>
        match todo with
        | [] => []
        | X :: todo' =>
            if rlg_nt_inb G nt_eqb X seen then
              rlg_epsilon_closure_fuel G nt_eqb fuel' seen todo'
            else
              X ::
              rlg_epsilon_closure_fuel
                G nt_eqb fuel' (X :: seen)
                (rlg_epsilon_successors G nt_eqb X ++ todo')
        end
    end.

  Lemma rlg_epsilon_closure_fuel_empty_todo :
    forall (G : right_linear_grammar) nt_eqb fuel seen,
      rlg_epsilon_closure_fuel G nt_eqb fuel seen [] = [].
  Proof.
    intros G nt_eqb fuel.
    destruct fuel; reflexivity.
  Qed.

  Definition rlg_epsilon_step_prodb
      (G : right_linear_grammar)
      (prod : rlg_production G) : bool :=
    match prod with
    | (_, [], Some _) => true
    | _ => false
    end.

  Definition rlg_epsilon_transition_bound
      (G : right_linear_grammar) : nat :=
    length
      (filter (rlg_epsilon_step_prodb G) (rlg_productions G)).

  (* Definition 4 II *)
  Fixpoint rlg_epsilon_simpleb_from
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (seen : list (rlg_nonterminal G))
      (d : rlg_derivation G) : bool :=
    match d with
    | [] => true
    | (_, _, None) :: d' =>
        match d' with
        | [] => true
        | _ :: _ => false
        end
    | (_, u, Some Y) :: d' =>
        match u with
        | [] =>
            negb (rlg_nt_inb G nt_eqb Y seen)
            && rlg_epsilon_simpleb_from G nt_eqb (Y :: seen) d'
        | _ :: _ =>
            rlg_epsilon_simpleb_from G nt_eqb [Y] d'
        end
    end.

  Definition rlg_epsilon_simpleb
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (X : rlg_nonterminal G)
      (d : rlg_derivation G) : bool :=
    rlg_epsilon_simpleb_from G nt_eqb [X] d.

  (* Definition 4 II *)
  Fixpoint rlg_epsilon_suffix_nonterminals
      (G : right_linear_grammar)
      (seen : list (rlg_nonterminal G))
      (d : rlg_derivation G) : list (rlg_nonterminal G) :=
    match d with
    | [] => seen
    | (_, _, None) :: _ => seen
    | (_, u, Some Y) :: d' =>
        match u with
        | [] => rlg_epsilon_suffix_nonterminals G (Y :: seen) d'
        | _ :: _ => rlg_epsilon_suffix_nonterminals G [Y] d'
        end
    end.

  Definition rlg_maximal_epsilon_simpleb_from
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (seen : list (rlg_nonterminal G))
      (current : rlg_nonterminal G) : bool :=
    forallb
      (fun prod =>
         match prod with
         | (X, [], Some Y) =>
             if nt_eqb current X then rlg_nt_inb G nt_eqb Y seen else true
         | _ => true
         end)
      (rlg_productions G).

  Definition rlg_maximal_epsilon_simpleb
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (X : rlg_nonterminal G)
      (d : rlg_derivation G) : bool :=
    rlg_maximal_epsilon_simpleb_from
      G nt_eqb
      (rlg_epsilon_suffix_nonterminals G [X] d)
      (rlg_derivation_end G X d).

  Definition rlg_final_nonterminalb
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (X : rlg_nonterminal G) : bool :=
    existsb
      (fun prod =>
         match prod with
         | (Y, [], None) => nt_eqb X Y
         | _ => false
         end)
      (rlg_productions G).

  Definition rlg_strict_epsilon_closure_nonterminals
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (X : rlg_nonterminal G)
      (d : rlg_derivation G)
      : list (rlg_nonterminal G) :=
    let seen := rlg_epsilon_suffix_nonterminals G [X] d in
    let current := rlg_derivation_end G X d in
    rlg_epsilon_closure_fuel
      G nt_eqb
      (rlg_epsilon_transition_bound G)
      seen
      (filter
         (fun Y => negb (rlg_nt_inb G nt_eqb Y seen))
         (rlg_epsilon_successors G nt_eqb current)).

  Definition rlg_accepting_maximal_epsilon_simpleb
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (X : rlg_nonterminal G)
      (d : rlg_derivation G) : bool :=
    forallb
      (fun Y => negb (rlg_final_nonterminalb G nt_eqb Y))
      (rlg_strict_epsilon_closure_nonterminals G nt_eqb X d).

  Fixpoint rlg_derivation_reachesb
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (word_eqb : list A -> list A -> bool)
      (prefix : list A)
      (X : rlg_nonterminal G)
      (seen : list A)
      (d : rlg_derivation G) : bool :=
    match d with
    | [] => false
    | (Y, u, _) :: d' =>
        (word_eqb seen prefix && nt_eqb Y X) ||
        rlg_derivation_reachesb G nt_eqb word_eqb prefix X (seen ++ u) d'
    end.

  Definition rlg_derivation_leafb
      (G : right_linear_grammar)
      (word_eqb : list A -> list A -> bool)
      (prefix : list A)
      (d : rlg_derivation G) : bool :=
    word_eqb prefix (firstn (length prefix) (rlg_derivation_word G d)).

  (** Definitions 8/9 bounded counts: [rlg_da_count] counts accepting
      derivations, [rlg_dra_count] counts prefix derivations reaching a given
      nonterminal, and [rlg_leaf_count] counts accepting derivations with the
      given prefix. *)
  Definition rlg_da_count
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (word_eqb : list A -> list A -> bool)
      (fuel : nat)
      (w : list A) : nat :=
    length
      (filter
         (fun d => word_eqb (rlg_derivation_word G d) w)
         (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G))).

  Definition rlg_dra_count
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (word_eqb : list A -> list A -> bool)
      (fuel : nat)
      (prefix : list A)
      (X : rlg_nonterminal G) : nat :=
    length
      (filter
         (rlg_derivation_reachesb G nt_eqb word_eqb prefix X [])
         (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G))).

  Definition rlg_leaf_count
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (word_eqb : list A -> list A -> bool)
      (fuel : nat)
      (prefix : list A) : nat :=
    length
      (filter
         (rlg_derivation_leafb G word_eqb prefix)
         (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G))).

  (** Definitions 8/9 prime counts: add epsilon-simple and maximal filters to
      the unprimed counts, matching the paper's [da'], [dra'], and [Leaf']. *)
  Definition rlg_da_prime_count
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (word_eqb : list A -> list A -> bool)
      (fuel : nat)
      (w : list A) : nat :=
    length
      (filter
         (fun d =>
            (word_eqb (rlg_derivation_word G d) w
             && rlg_epsilon_simpleb G nt_eqb (rlg_start G) d)
            && rlg_accepting_maximal_epsilon_simpleb
                 G nt_eqb (rlg_start G) d)
         (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G))).

  Definition rlg_dra_prime_count
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (word_eqb : list A -> list A -> bool)
      (fuel : nat)
      (prefix : list A)
      (X : rlg_nonterminal G) : nat :=
    length
      (filter
         (fun d =>
            (word_eqb (rlg_prefix_derivation_word G d) prefix
             && nt_eqb (rlg_derivation_end G (rlg_start G) d) X)
            && rlg_epsilon_simpleb G nt_eqb (rlg_start G) d)
         (rlg_prefix_derivations_from_fuel
            G nt_eqb fuel (rlg_start G))).

  Definition rlg_leaf_prime_count
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (word_eqb : list A -> list A -> bool)
      (fuel : nat)
      (prefix : list A) : nat :=
    length
      (filter
         (fun d =>
            (rlg_derivation_leafb G word_eqb prefix d
             && rlg_epsilon_simpleb G nt_eqb (rlg_start G) d)
            && rlg_maximal_epsilon_simpleb G nt_eqb (rlg_start G) d)
         (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G))).

  Definition rlg_prefix_leaf_prime_count
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (word_eqb : list A -> list A -> bool)
      (fuel : nat)
      (prefix : list A) : nat :=
    length
      (filter
         (fun d =>
            (word_eqb (rlg_prefix_derivation_word G d) prefix
             && rlg_epsilon_simpleb G nt_eqb (rlg_start G) d)
            && rlg_maximal_epsilon_simpleb G nt_eqb (rlg_start G) d)
         (rlg_prefix_derivations_from_fuel
            G nt_eqb fuel (rlg_start G))).

  Lemma filter_length_le :
    forall {B : Type} (p : B -> bool) xs,
      length (filter p xs) <= length xs.
  Proof.
    intros B p xs.
    induction xs as [| x xs IH]; simpl.
    - lia.
    - destruct (p x); simpl; lia.
  Qed.

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

  Lemma filter_length_pos_exists :
    forall {B : Type} (p : B -> bool) xs,
      0 < length (filter p xs) ->
      exists x, In x xs /\ p x = true.
  Proof.
    intros B p xs.
    induction xs as [| x xs IH]; simpl; intros Hpos.
    - lia.
    - destruct (p x) eqn:Hpx.
      + exists x. simpl. auto.
      + destruct (IH Hpos) as [y [Hy Hpy]].
        exists y. simpl. auto.
  Qed.

  Definition word_eqb_reflects_eq
      (word_eqb : list A -> list A -> bool) : Prop :=
    (forall x y, word_eqb x y = true -> x = y) /\
    (forall x y, x = y -> word_eqb x y = true).

  Lemma length_concat_map_sum_nats :
    forall {B C : Type} (f : B -> list C) xs,
      length (concat (map f xs)) =
      sum_nats (map (fun x => length (f x)) xs).
  Proof.
    intros B C f xs.
    induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - rewrite app_length, IH. reflexivity.
  Qed.

  Lemma concat_map_nil :
    forall {B C : Type} (xs : list B),
      concat (map (fun _ : B => @nil C) xs) = [].
  Proof.
    intros B C xs.
    induction xs as [| x xs IH]; simpl; auto.
  Qed.

  Lemma concat_map_singleton :
    forall {B : Type} (xs : list B),
      concat (map (fun x => [x]) xs) = xs.
  Proof.
    intros B xs.
    induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - now rewrite IH.
  Qed.

  Lemma forallb_ext_in :
    forall {B : Type} (p q : B -> bool) xs,
      (forall x, In x xs -> p x = q x) ->
      forallb p xs = forallb q xs.
  Proof.
    intros B p q xs H.
    induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - rewrite H by (simpl; auto).
      rewrite IH; auto.
      intros y Hy. apply H. simpl. auto.
  Qed.

  Lemma filter_count_eq_of_bijection :
    forall (B C : Type) (f : B -> C) (p : C -> bool) xs ys,
      NoDup xs ->
      NoDup ys ->
      (forall x, In x xs -> In (f x) ys /\ p (f x) = true) ->
      (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
      (forall y, In y ys -> p y = true ->
        exists x, In x xs /\ f x = y) ->
      length xs = length (filter p ys).
  Proof.
    intros B C f p xs ys Hxs Hys Hto Hinj Hfrom.
    assert (Hmap_nodup : NoDup (map f xs)).
    {
      apply NoDup_map_injective_in; auto.
    }
    assert (Hmap_incl : incl (map f xs) (filter p ys)).
    {
      intros z Hz.
      apply in_map_iff in Hz as [x [Hz Hx]].
      subst z.
      destruct (Hto x Hx) as [Hy Hp].
      apply filter_In. split; auto.
    }
    assert (Hfilter_incl : incl (filter p ys) (map f xs)).
    {
      intros y Hy.
      apply filter_In in Hy as [Hy Hp].
      destruct (Hfrom y Hy Hp) as [x [Hx Hfx]].
      subst y. apply in_map. exact Hx.
    }
    assert (Hle1 : length (map f xs) <= length (filter p ys)).
    {
      eapply NoDup_incl_length; eauto.
    }
    assert (Hle2 : length (filter p ys) <= length (map f xs)).
    {
      eapply NoDup_incl_length.
      - apply NoDup_filter_bool. exact Hys.
      - exact Hfilter_incl.
    }
    rewrite length_map in Hle1, Hle2.
    lia.
  Qed.

  Theorem rlg_da_count_bounded_by_enumeration :
    forall G nt_eqb word_eqb fuel w,
      rlg_da_count G nt_eqb word_eqb fuel w <=
      length (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G)).
  Proof.
    intros. unfold rlg_da_count. apply filter_length_le.
  Qed.

  Theorem rlg_dra_count_bounded_by_enumeration :
    forall G nt_eqb word_eqb fuel prefix X,
      rlg_dra_count G nt_eqb word_eqb fuel prefix X <=
      length (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G)).
  Proof.
    intros. unfold rlg_dra_count. apply filter_length_le.
  Qed.

  Theorem rlg_leaf_count_bounded_by_enumeration :
    forall G nt_eqb word_eqb fuel prefix,
      rlg_leaf_count G nt_eqb word_eqb fuel prefix <=
      length (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G)).
  Proof.
    intros. unfold rlg_leaf_count. apply filter_length_le.
  Qed.

  Theorem rlg_da_prime_count_bounded_by_enumeration :
    forall G nt_eqb word_eqb fuel w,
      rlg_da_prime_count G nt_eqb word_eqb fuel w <=
      length (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G)).
  Proof.
    intros. unfold rlg_da_prime_count. apply filter_length_le.
  Qed.

  Theorem rlg_dra_prime_count_bounded_by_enumeration :
    forall G nt_eqb word_eqb fuel prefix X,
      rlg_dra_prime_count G nt_eqb word_eqb fuel prefix X <=
      length
        (rlg_prefix_derivations_from_fuel
           G nt_eqb fuel (rlg_start G)).
  Proof.
    intros. unfold rlg_dra_prime_count. apply filter_length_le.
  Qed.

  Theorem rlg_leaf_prime_count_bounded_by_enumeration :
    forall G nt_eqb word_eqb fuel prefix,
      rlg_leaf_prime_count G nt_eqb word_eqb fuel prefix <=
      length (rlg_derivations_from_fuel G nt_eqb fuel (rlg_start G)).
  Proof.
    intros. unfold rlg_leaf_prime_count. apply filter_length_le.
  Qed.

  Theorem rlg_prefix_leaf_prime_count_bounded_by_enumeration :
    forall G nt_eqb word_eqb fuel prefix,
      rlg_prefix_leaf_prime_count G nt_eqb word_eqb fuel prefix <=
      length
        (rlg_prefix_derivations_from_fuel
           G nt_eqb fuel (rlg_start G)).
  Proof.
    intros. unfold rlg_prefix_leaf_prime_count. apply filter_length_le.
  Qed.

  Lemma rlg_derivations_from_fuel_valid :
    forall G nt_eqb,
      (forall x y, nt_eqb x y = true -> x = y) ->
      forall fuel X d,
      In d (rlg_derivations_from_fuel G nt_eqb fuel X) ->
      rlg_derivation_valid G X d None.
  Proof.
    intros G nt_eqb Hsound fuel.
    induction fuel as [| fuel IH]; intros X d Hin.
    - contradiction.
    - simpl in Hin.
      apply in_concat in Hin as [ds [Hds Hd]].
      apply in_map_iff in Hds as [[[Y u] [Z|]] [Hds Hprod]];
        subst ds.
      + destruct (nt_eqb X Y) eqn:Heq; simpl in Hd; try contradiction.
        apply Hsound in Heq. subst Y.
        apply in_map_iff in Hd as [d' [Hd Hd']]. subst d.
        eapply RLGDerivation_step; eauto.
      + destruct (nt_eqb X Y) eqn:Heq; simpl in Hd; try contradiction.
        destruct Hd as [Hd | []]. subst d.
        apply Hsound in Heq. subst Y.
        apply RLGDerivation_stop. exact Hprod.
  Qed.

  Lemma rlg_prefix_derivations_from_fuel_valid :
    forall G nt_eqb,
      (forall x y, nt_eqb x y = true -> x = y) ->
      forall fuel X d,
      In d (rlg_prefix_derivations_from_fuel G nt_eqb fuel X) ->
      exists Y, rlg_prefix_derivation_valid G X d Y.
  Proof.
    intros G nt_eqb Hsound fuel.
    induction fuel as [| fuel IH]; intros X d Hin.
    - simpl in Hin. destruct Hin as [Hin | []]. subst d.
      exists X. constructor.
    - simpl in Hin. destruct Hin as [Hin | Hin].
      + subst d. exists X. constructor.
      + apply in_concat in Hin as [ds [Hds Hd]].
        apply in_map_iff in Hds as [[[Y u] [Z|]] [Hds Hprod]];
          subst ds; simpl in Hd; try contradiction.
        destruct (nt_eqb X Y) eqn:Heq; simpl in Hd; try contradiction.
        apply Hsound in Heq. subst Y.
        apply in_map_iff in Hd as [d' [Hd Hd']]. subst d.
        destruct (IH Z d' Hd') as [T Hvalid].
        exists T. eapply RLGPrefix_step; eauto.
  Qed.

  Lemma rlg_derivations_from_fuel_complete :
    forall G nt_eqb,
      (forall x y, x = y -> nt_eqb x y = true) ->
      forall X d,
      rlg_derivation_valid G X d None ->
      forall fuel,
      length d <= fuel ->
      In d (rlg_derivations_from_fuel G nt_eqb fuel X).
  Proof.
    intros G nt_eqb Hcomplete X d Hvalid.
    induction Hvalid as [X u Hprod| X u Y d tail Hprod _ IH];
      intros fuel Hlen.
    - destruct fuel as [| fuel]; simpl in Hlen; [lia|].
      simpl.
      apply in_concat.
      exists [[(X, u, None)]]. split.
      + apply in_map_iff.
        exists (X, u, None). split; [now rewrite Hcomplete | exact Hprod].
      + simpl. auto.
    - destruct fuel as [| fuel]; simpl in Hlen; [lia|].
      simpl.
      apply in_concat.
      exists
        (map (fun d0 => (X, u, Some Y) :: d0)
           (rlg_derivations_from_fuel G nt_eqb fuel Y)).
      split.
      + apply in_map_iff.
        exists (X, u, Some Y). split; [now rewrite Hcomplete | exact Hprod].
      + apply in_map_iff.
        exists d. split; [reflexivity |].
        apply IH. simpl in Hlen. lia.
  Qed.

  Lemma rlg_prefix_derivations_from_fuel_complete :
    forall G nt_eqb,
      (forall x y, x = y -> nt_eqb x y = true) ->
      forall X d Y,
      rlg_prefix_derivation_valid G X d Y ->
      forall fuel,
      length d <= fuel ->
      In d (rlg_prefix_derivations_from_fuel G nt_eqb fuel X).
  Proof.
    intros G nt_eqb Hcomplete X d Y Hvalid.
    induction Hvalid as [X| X u Y d Z Hprod _ IH]; intros fuel Hlen.
    - destruct fuel as [| fuel]; simpl; auto.
    - destruct fuel as [| fuel]; simpl in Hlen; [lia|].
      simpl. right.
      apply in_concat.
      exists
        (map (fun d0 => (X, u, Some Y) :: d0)
           (rlg_prefix_derivations_from_fuel G nt_eqb fuel Y)).
      split.
      + apply in_map_iff.
        exists (X, u, Some Y). split; [now rewrite Hcomplete | exact Hprod].
      + apply in_map_iff.
        exists d. split; [reflexivity |].
        apply IH. simpl in Hlen. lia.
  Qed.

  Lemma rlg_prefix_derivation_valid_end :
    forall G X d Y,
      rlg_prefix_derivation_valid G X d Y ->
      rlg_derivation_end G X d = Y.
  Proof.
    intros G X d Y Hvalid.
    induction Hvalid as [X| X u Y d Z _ _ IH]; simpl.
    - reflexivity.
    - exact IH.
  Qed.

  Lemma rlg_derivations_from_fuel_NoDup :
    forall G nt_eqb,
      NoDup (rlg_productions G) ->
      forall fuel X,
      NoDup (rlg_derivations_from_fuel G nt_eqb fuel X).
  Proof.
    intros G nt_eqb Hprod_nodup fuel.
    induction fuel as [| fuel IH]; intros X.
    - constructor.
    - simpl.
      set (chunk := fun prod : rlg_production G =>
        match prod with
        | (Y, _u, None) =>
            if nt_eqb X Y then [[prod]] else []
        | (Y, _u, Some Z) =>
            if nt_eqb X Y
            then
              map (fun d => prod :: d)
                (rlg_derivations_from_fuel G nt_eqb fuel Z)
            else []
        end).
      change (NoDup (concat (map chunk (rlg_productions G)))).
      assert (Hhead : forall prod d,
        In d (chunk prod) -> exists tail, d = prod :: tail).
      {
        intros [[Y u] [Z|]] d Hin; unfold chunk in Hin; simpl in Hin.
        - destruct (nt_eqb X Y); simpl in Hin; try contradiction.
          apply in_map_iff in Hin as [d' [Hd _]].
          subst d. exists d'. reflexivity.
        - destruct (nt_eqb X Y); simpl in Hin; try contradiction.
          destruct Hin as [Hin | []]. subst d.
          exists []. reflexivity.
      }
      apply NoDup_concat_map.
      + exact Hprod_nodup.
      + intros [[Y u] [Z|]] Hprod; unfold chunk; simpl.
        * destruct (nt_eqb X Y); simpl.
          -- apply NoDup_map_injective_in.
             ++ intros d1 d2 _ _ Heq. now inversion Heq.
             ++ apply IH.
          -- constructor.
        * destruct (nt_eqb X Y); simpl.
          -- repeat constructor; intro H; contradiction.
          -- constructor.
      + intros prod1 prod2 d Hprod1 Hprod2 Hneq Hd1 Hd2.
        destruct (Hhead prod1 d Hd1) as [tail1 Htail1].
        destruct (Hhead prod2 d Hd2) as [tail2 Htail2].
        subst d. inversion Htail2; subst.
        contradiction.
  Qed.

  Lemma rlg_prefix_derivations_from_fuel_NoDup :
    forall G nt_eqb,
      NoDup (rlg_productions G) ->
      forall fuel X,
      NoDup (rlg_prefix_derivations_from_fuel G nt_eqb fuel X).
  Proof.
    intros G nt_eqb Hprod_nodup fuel.
    induction fuel as [| fuel IH]; intros X.
    - simpl. repeat constructor; intro H; contradiction.
    - simpl.
      set (chunk := fun prod : rlg_production G =>
        match prod with
        | (Y, _u, Some Z) =>
            if nt_eqb X Y
            then
              map (fun d => prod :: d)
                (rlg_prefix_derivations_from_fuel G nt_eqb fuel Z)
            else []
        | (_, _, None) => []
        end).
      change (NoDup ([] :: concat (map chunk (rlg_productions G)))).
      constructor.
      + intro Hin.
        apply in_concat in Hin as [ds [Hds Hd]].
        apply in_map_iff in Hds as [prod [Hds Hprod]].
        subst ds.
        destruct prod as [[Y u] [Z|]]; unfold chunk in Hd; simpl in Hd;
          try contradiction.
        destruct (nt_eqb X Y); simpl in Hd; try contradiction.
        apply in_map_iff in Hd as [d [Hd _]].
        discriminate.
      + assert (Hhead : forall prod d,
          In d (chunk prod) -> exists tail, d = prod :: tail).
        {
          intros [[Y u] [Z|]] d Hin; unfold chunk in Hin; simpl in Hin;
            try contradiction.
          destruct (nt_eqb X Y); simpl in Hin; try contradiction.
          apply in_map_iff in Hin as [d' [Hd _]].
          subst d. exists d'. reflexivity.
        }
        apply NoDup_concat_map.
        * exact Hprod_nodup.
        * intros [[Y u] [Z|]] Hprod; unfold chunk; simpl; try constructor.
          destruct (nt_eqb X Y); simpl.
          -- apply NoDup_map_injective_in.
             ++ intros d1 d2 _ _ Heq. now inversion Heq.
             ++ apply IH.
          -- constructor.
        * intros prod1 prod2 d Hprod1 Hprod2 Hneq Hd1 Hd2.
          destruct (Hhead prod1 d Hd1) as [tail1 Htail1].
          destruct (Hhead prod2 d Hd2) as [tail2 Htail2].
          subst d. inversion Htail2; subst.
          contradiction.
  Qed.

  Definition rlg_accepts (G : right_linear_grammar) (w : list A) : Prop :=
    rlg_derives_from G (rlg_start G) w.

  Definition rlg_da_word (G : right_linear_grammar) (w : list A) : Prop :=
    rlg_accepts G w.

  Definition rlg_dra_reaches
      (G : right_linear_grammar)
      (prefix : list A)
      (X : rlg_nonterminal G) : Prop :=
    exists suffix, rlg_derives_from G (rlg_start G) (prefix ++ suffix) /\
      rlg_derives_from G X suffix.

  Definition rlg_leaf_reaches
      (G : right_linear_grammar)
      (prefix : list A) : Prop :=
    exists suffix, rlg_derives_from G (rlg_start G) (prefix ++ suffix).

  (** Definitions 8/9 Prop-level specs.  These fuel-independent predicates
      express ordinary, reach, and leaf unambiguity directly over explicit
      derivations. *)
  Definition rlg_derivation_reaches
      (G : right_linear_grammar)
      (prefix : list A)
      (X : rlg_nonterminal G)
      (d : rlg_derivation G) : Prop :=
    exists d_prefix d_suffix tail,
      d = d_prefix ++ d_suffix /\
      rlg_derivation_valid G (rlg_start G) d tail /\
      rlg_derivation_word G d_prefix = prefix /\
      rlg_derivation_valid G X d_suffix tail.

  Definition rlg_derivation_leaf
      (G : right_linear_grammar)
      (prefix : list A)
      (d : rlg_derivation G) : Prop :=
    exists suffix,
      rlg_derivation_valid G (rlg_start G) d None /\
      rlg_derivation_word G d = prefix ++ suffix.

  Definition rlg_unambiguous (G : right_linear_grammar) : Prop :=
    forall w d1 d2,
      rlg_derivation_accepting G w d1 ->
      rlg_derivation_accepting G w d2 ->
      d1 = d2.

  Definition rlg_reach_unambiguous (G : right_linear_grammar) : Prop :=
    forall prefix X d1 d2,
      rlg_derivation_reaches G prefix X d1 ->
      rlg_derivation_reaches G prefix X d2 ->
      d1 = d2.

  Definition rlg_leaf_unambiguous (G : right_linear_grammar) : Prop :=
    forall prefix d1 d2,
      rlg_derivation_leaf G prefix d1 ->
      rlg_derivation_leaf G prefix d2 ->
      d1 = d2.

  (** Definitions 8/9 prime/refined specs.  These predicates compare only
      epsilon-simple/maximal derivations and are the versions bridged to
      [enfa_UFA], [enfa_ReachUFA], and [enfa_LeafUFA]. *)
  Definition rlg_derivation_accepting_prime
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (w : list A)
      (d : rlg_derivation G) : Prop :=
    rlg_derivation_accepting G w d /\
    rlg_epsilon_simpleb G nt_eqb (rlg_start G) d = true /\
    rlg_accepting_maximal_epsilon_simpleb
      G nt_eqb (rlg_start G) d = true.

  Definition rlg_prefix_derivation_prime_reaches
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (prefix : list A)
      (X : rlg_nonterminal G)
      (d : rlg_derivation G) : Prop :=
    rlg_prefix_derivation_valid G (rlg_start G) d X /\
    rlg_prefix_derivation_word G d = prefix /\
    rlg_epsilon_simpleb G nt_eqb (rlg_start G) d = true.

  Definition rlg_prefix_derivation_prime_leaf
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool)
      (prefix : list A)
      (d : rlg_derivation G) : Prop :=
    exists X,
      rlg_prefix_derivation_prime_reaches G nt_eqb prefix X d /\
      rlg_maximal_epsilon_simpleb G nt_eqb (rlg_start G) d = true.

  Definition rlg_prime_unambiguous
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool) : Prop :=
    forall w d1 d2,
      rlg_derivation_accepting_prime G nt_eqb w d1 ->
      rlg_derivation_accepting_prime G nt_eqb w d2 ->
      d1 = d2.

  Definition rlg_prime_reach_unambiguous
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool) : Prop :=
    forall prefix X d1 d2,
      rlg_prefix_derivation_prime_reaches G nt_eqb prefix X d1 ->
      rlg_prefix_derivation_prime_reaches G nt_eqb prefix X d2 ->
      d1 = d2.

  Definition rlg_prime_leaf_unambiguous
      (G : right_linear_grammar)
      (nt_eqb : rlg_nonterminal G -> rlg_nonterminal G -> bool) : Prop :=
    forall prefix d1 d2,
      rlg_prefix_derivation_prime_leaf G nt_eqb prefix d1 ->
      rlg_prefix_derivation_prime_leaf G nt_eqb prefix d2 ->
      d1 = d2.

  Definition option_label_word (l : option A) : list A :=
    match l with
    | None => []
    | Some a => [a]
    end.

  Lemma option_label_word_injective :
    forall l1 l2,
      option_label_word l1 = option_label_word l2 ->
      l1 = l2.
  Proof.
    intros [a|] [b|] H; simpl in H; try discriminate; congruence.
  Qed.

  (** Gamma bridge support: the [Gamma(M)] construction.  Final ENFA states
      give [q -> epsilon], epsilon edges give [p -> epsilon q], and labeled
      edges give [p -> a q]. *)
  Definition gamma_final_productions (m : @finite_enfa A)
      : list (enfa_state (fenfa_base m) * list A *
              option (enfa_state (fenfa_base m))) :=
    map (fun q => (q, [], None)) (enfa_final_states m).

  Definition gamma_epsilon_productions (m : @finite_enfa A)
      : list (enfa_state (fenfa_base m) * list A *
              option (enfa_state (fenfa_base m))) :=
    concat
      (map
         (fun p =>
            map (fun q => (p, [], Some q))
              (enfa_step (fenfa_base m) p None))
         (fenfa_states m)).

  Definition gamma_symbol_productions (m : @finite_enfa A)
      : list (enfa_state (fenfa_base m) * list A *
              option (enfa_state (fenfa_base m))) :=
    concat
      (map
         (fun p =>
            concat
              (map
                 (fun a =>
                    map (fun q => (p, [a], Some q))
                      (enfa_step (fenfa_base m) p (Some a)))
                 (fenfa_alphabet m)))
         (fenfa_states m)).

  Definition gamma_productions (m : @finite_enfa A)
      : list (enfa_state (fenfa_base m) * list A *
              option (enfa_state (fenfa_base m))) :=
    gamma_final_productions m ++
    gamma_epsilon_productions m ++
    gamma_symbol_productions m.

  Lemma gamma_final_productions_NoDup :
    forall (m : @finite_enfa A),
      finite_enfa_wf m ->
      NoDup (gamma_final_productions m).
  Proof.
    intros m Hwf.
    unfold gamma_final_productions.
    apply NoDup_map_injective_in.
    - intros q r _ _ Heq. now inversion Heq.
    - unfold enfa_final_states.
      apply NoDup_filter_bool.
      apply fenfa_states_nodup. exact Hwf.
  Qed.

  Lemma gamma_epsilon_productions_NoDup :
    forall (m : @finite_enfa A),
      finite_enfa_wf m ->
      NoDup (gamma_epsilon_productions m).
  Proof.
    intros m Hwf.
    unfold gamma_epsilon_productions.
    apply NoDup_concat_map.
    - apply fenfa_states_nodup. exact Hwf.
    - intros p Hp.
      apply NoDup_map_injective_in.
      + intros q r _ _ Heq. now inversion Heq.
      + eapply fenfa_step_targets_nodup; eauto.
    - intros p r z Hp Hr Hneq Hzp Hzr.
      apply in_map_iff in Hzp as [q [Hzp _]].
      apply in_map_iff in Hzr as [q' [Hzr _]].
      subst z. inversion Hzr; subst.
      contradiction.
  Qed.

  Lemma gamma_symbol_productions_NoDup_with_alphabet_nodup :
    forall (m : @finite_enfa A),
      finite_enfa_wf m ->
      NoDup (fenfa_alphabet m) ->
      NoDup (gamma_symbol_productions m).
  Proof.
    intros m Hwf Halphabet.
    unfold gamma_symbol_productions.
    apply NoDup_concat_map.
    - apply fenfa_states_nodup. exact Hwf.
    - intros p Hp.
      apply NoDup_concat_map.
      + exact Halphabet.
      + intros a Ha.
        apply NoDup_map_injective_in.
        * intros q r _ _ Heq. now inversion Heq.
        * eapply fenfa_step_targets_nodup; eauto.
      + intros a b z Ha Hb Hneq Hza Hzb.
        apply in_map_iff in Hza as [q [Hza _]].
        apply in_map_iff in Hzb as [r [Hzb _]].
        subst z. inversion Hzb; subst.
        contradiction.
    - intros p r z Hp Hr Hneq Hzp Hzr.
      apply in_concat in Hzp as [ap [Hap Hzp]].
      apply in_map_iff in Hap as [a [Hap _]].
      subst ap.
      apply in_map_iff in Hzp as [q [Hzp _]].
      apply in_concat in Hzr as [ar [Har Hzr]].
      apply in_map_iff in Har as [b [Har _]].
      subst ar.
      apply in_map_iff in Hzr as [q' [Hzr _]].
      subst z. inversion Hzr; subst.
      contradiction.
  Qed.

  Lemma gamma_productions_NoDup_with_alphabet_nodup :
    forall (m : @finite_enfa A),
      finite_enfa_wf m ->
      NoDup (fenfa_alphabet m) ->
      NoDup (gamma_productions m).
  Proof.
    intros m Hwf Halphabet.
    unfold gamma_productions.
    apply NoDup_app. repeat split.
    - apply gamma_final_productions_NoDup. exact Hwf.
    - apply NoDup_app. repeat split.
      + apply gamma_epsilon_productions_NoDup. exact Hwf.
      + apply gamma_symbol_productions_NoDup_with_alphabet_nodup; auto.
      + intros z Hz_eps Hz_sym.
        unfold gamma_epsilon_productions in Hz_eps.
        apply in_concat in Hz_eps as [eps [Heps Hz_eps]].
        apply in_map_iff in Heps as [p [Heps _]].
        subst eps.
        apply in_map_iff in Hz_eps as [q [Hz_eps _]].
        unfold gamma_symbol_productions in Hz_sym.
        apply in_concat in Hz_sym as [syms [Hsyms Hz_sym]].
        apply in_map_iff in Hsyms as [p' [Hsyms _]].
        subst syms.
        apply in_concat in Hz_sym as [sym [Hsym Hz_sym]].
        apply in_map_iff in Hsym as [a [Hsym _]].
        subst sym.
        apply in_map_iff in Hz_sym as [q' [Hz_sym _]].
        subst z. discriminate.
    - intros z Hz_final Hz_rest.
      unfold gamma_final_productions in Hz_final.
      apply in_map_iff in Hz_final as [q [Hz_final _]].
      subst z.
      apply in_app_or in Hz_rest as [Hz_eps | Hz_sym].
      + unfold gamma_epsilon_productions in Hz_eps.
        apply in_concat in Hz_eps as [eps [Heps Hz_eps]].
        apply in_map_iff in Heps as [p [Heps _]].
        subst eps.
        apply in_map_iff in Hz_eps as [q' [Hz_eps _]].
        discriminate.
      + unfold gamma_symbol_productions in Hz_sym.
        apply in_concat in Hz_sym as [syms [Hsyms Hz_sym]].
        apply in_map_iff in Hsyms as [p [Hsyms _]].
        subst syms.
        apply in_concat in Hz_sym as [sym [Hsym Hz_sym]].
        apply in_map_iff in Hsym as [a [Hsym _]].
        subst sym.
        apply in_map_iff in Hz_sym as [q' [Hz_sym _]].
        discriminate.
  Qed.

  Definition gamma_grammar_from
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : right_linear_grammar :=
    {|
      rlg_nonterminal := enfa_state (fenfa_base m);
      rlg_start := s;
      rlg_productions := gamma_productions m
    |}.

  (** Definition 8/9 aliases on the Gamma side.  They name prime RLG
      unambiguity, reach-unambiguity, and leaf-unambiguity for [Gamma(M)] so
      the bridge theorems can state preservation directly. *)
  Definition gamma_rlg_unambiguous
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    rlg_prime_unambiguous (gamma_grammar_from m s) (fenfa_state_eqb m).

  Definition gamma_rlg_reach_unambiguous
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    rlg_prime_reach_unambiguous (gamma_grammar_from m s) (fenfa_state_eqb m).

  Definition gamma_rlg_leaf_unambiguous
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    rlg_prime_leaf_unambiguous (gamma_grammar_from m s) (fenfa_state_eqb m).

  Definition enfa_prime_maximal_witnesses
      (m : @finite_enfa A)
      (qs : list (enfa_state (fenfa_base m)))
      (w : list A)
      : list (enfa_state (fenfa_base m) * started_trace m) :=
    concat
      (map
         (fun q =>
            map (fun st => (q, st))
              (filter
                 (fun st =>
                    (ends_inb m q st && epsilon_simpleb m st)
                    && maximal_epsilon_simpleb m st)
                 (started_traces m w)))
         qs).

  Definition enfa_accepting_prime_witnesses
      (m : @finite_enfa A)
      (qs : list (enfa_state (fenfa_base m)))
      (w : list A)
      : list (enfa_state (fenfa_base m) * started_trace m) :=
    concat
      (map
         (fun q =>
            map (fun st => (q, st))
              (filter
                 (fun st =>
                    (ends_inb m q st && epsilon_simpleb m st)
                    && enfa_accepting_maximal_epsilon_simpleb m st)
                 (started_traces m w)))
         qs).

  Definition enfa_da_prime_witnesses
      (m : @finite_enfa A)
      (w : list A)
      : list (enfa_state (fenfa_base m) * started_trace m) :=
    enfa_accepting_prime_witnesses m (enfa_final_states m) w.

  Definition enfa_leaf_prime_witnesses
      (m : @finite_enfa A)
      (w : list A)
      : list (enfa_state (fenfa_base m) * started_trace m) :=
    enfa_prime_maximal_witnesses m (fenfa_states m) w.

  Lemma enfa_prime_maximal_witnesses_length :
    forall (m : @finite_enfa A) qs w,
      length (enfa_prime_maximal_witnesses m qs w) =
      sum_nats
        (map (fun q => enfa_maximal_simple_reach_count m w q) qs).
  Proof.
    intros m qs w.
    unfold enfa_prime_maximal_witnesses.
    rewrite length_concat_map_sum_nats.
    induction qs as [| q qs IH]; simpl.
    - reflexivity.
    - unfold enfa_maximal_simple_reach_count at 1.
      rewrite length_map. f_equal. exact IH.
  Qed.

  Lemma enfa_accepting_prime_witnesses_length :
    forall (m : @finite_enfa A) qs w,
      length (enfa_accepting_prime_witnesses m qs w) =
      sum_nats
        (map
           (fun q => enfa_accepting_maximal_simple_reach_count m w q)
           qs).
  Proof.
    intros m qs w.
    unfold enfa_accepting_prime_witnesses.
    rewrite length_concat_map_sum_nats.
    induction qs as [| q qs IH]; simpl.
    - reflexivity.
    - unfold enfa_accepting_maximal_simple_reach_count at 1.
      rewrite length_map. f_equal. exact IH.
  Qed.

  Lemma enfa_da_prime_witnesses_length :
    forall (m : @finite_enfa A) w,
      length (enfa_da_prime_witnesses m w) = enfa_da_prime_word m w.
  Proof.
    intros m w.
    unfold enfa_da_prime_witnesses, enfa_da_prime_word.
    apply enfa_accepting_prime_witnesses_length.
  Qed.

  Lemma enfa_leaf_prime_witnesses_length :
    forall (m : @finite_enfa A) w,
      length (enfa_leaf_prime_witnesses m w) = enfa_leaf_prime_word m w.
  Proof.
    intros m w.
    unfold enfa_leaf_prime_witnesses, enfa_leaf_prime_word.
    apply enfa_prime_maximal_witnesses_length.
  Qed.

  Lemma enfa_prime_maximal_witnesses_In :
    forall (m : @finite_enfa A) qs w q st,
      In (q, st) (enfa_prime_maximal_witnesses m qs w) <->
      In q qs /\
      In st (started_traces m w) /\
      ((ends_inb m q st && epsilon_simpleb m st) &&
       maximal_epsilon_simpleb m st) = true.
  Proof.
    intros m qs w q st.
    unfold enfa_prime_maximal_witnesses.
    split.
    - intros Hin.
      apply in_concat in Hin as [chunk [Hchunk Hin]].
      apply in_map_iff in Hchunk as [q' [Hchunk Hq']].
      subst chunk.
      apply in_map_iff in Hin as [st' [Hp Hst']].
      inversion Hp; subst q' st'.
      apply filter_In in Hst' as [Hst Hf].
      repeat split; auto.
    - intros [Hq [Hst Hf]].
      apply in_concat.
      exists
        (map (fun st0 => (q, st0))
           (filter
              (fun st0 =>
                 (ends_inb m q st0 && epsilon_simpleb m st0)
                 && maximal_epsilon_simpleb m st0)
              (started_traces m w))).
      split.
      + apply in_map_iff.
        exists q. split; [reflexivity | exact Hq].
      + apply in_map.
        apply filter_In. split; auto.
  Qed.

  Lemma enfa_accepting_prime_witnesses_In :
    forall (m : @finite_enfa A) qs w q st,
      In (q, st) (enfa_accepting_prime_witnesses m qs w) <->
      In q qs /\
      In st (started_traces m w) /\
      ((ends_inb m q st && epsilon_simpleb m st) &&
       enfa_accepting_maximal_epsilon_simpleb m st) = true.
  Proof.
    intros m qs w q st.
    unfold enfa_accepting_prime_witnesses.
    split.
    - intros Hin.
      apply in_concat in Hin as [chunk [Hchunk Hin]].
      apply in_map_iff in Hchunk as [q' [Hchunk Hq']].
      subst chunk.
      apply in_map_iff in Hin as [st' [Hp Hst']].
      inversion Hp; subst q' st'.
      apply filter_In in Hst' as [Hst Hf].
      repeat split; auto.
    - intros [Hq [Hst Hf]].
      apply in_concat.
      exists
        (map (fun st0 => (q, st0))
           (filter
              (fun st0 =>
                 (ends_inb m q st0 && epsilon_simpleb m st0)
                 && enfa_accepting_maximal_epsilon_simpleb m st0)
              (started_traces m w))).
      split.
      + apply in_map_iff.
        exists q. split; [reflexivity | exact Hq].
      + apply in_map.
        apply filter_In. split; auto.
  Qed.

  Lemma enfa_prime_maximal_witnesses_NoDup :
    forall (m : @finite_enfa A) qs w,
      NoDup qs ->
      NoDup (started_traces m w) ->
      NoDup (enfa_prime_maximal_witnesses m qs w).
  Proof.
    intros m qs w Hqs Htr.
    unfold enfa_prime_maximal_witnesses.
    apply NoDup_concat_map.
    - exact Hqs.
    - intros q Hq.
      apply NoDup_map_injective_in.
      + intros st1 st2 _ _ Hp. now inversion Hp.
      + apply NoDup_filter_bool. exact Htr.
    - intros q1 q2 z Hq1 Hq2 Hneq Hz1 Hz2.
      apply in_map_iff in Hz1 as [st1 [Hz1 _]].
      apply in_map_iff in Hz2 as [st2 [Hz2 _]].
      subst z. inversion Hz2; subst.
      apply Hneq. reflexivity.
  Qed.

  Lemma enfa_accepting_prime_witnesses_NoDup :
    forall (m : @finite_enfa A) qs w,
      NoDup qs ->
      NoDup (started_traces m w) ->
      NoDup (enfa_accepting_prime_witnesses m qs w).
  Proof.
    intros m qs w Hqs Htr.
    unfold enfa_accepting_prime_witnesses.
    apply NoDup_concat_map.
    - exact Hqs.
    - intros q Hq.
      apply NoDup_map_injective_in.
      + intros st1 st2 _ _ Hp. now inversion Hp.
      + apply NoDup_filter_bool. exact Htr.
    - intros q1 q2 z Hq1 Hq2 Hneq Hz1 Hz2.
      apply in_map_iff in Hz1 as [st1 [Hz1 _]].
      apply in_map_iff in Hz2 as [st2 [Hz2 _]].
      subst z. inversion Hz2; subst.
      apply Hneq. reflexivity.
  Qed.

  (** Core data conversions for the Gamma bridge.  [gamma_derivation_of_trace]
      maps ENFA traces to Gamma derivations, while [gamma_trace_of_derivation]
      reconstructs ENFA traces from valid Gamma derivations.  Prefix variants
      serve reach and leaf ambiguity. *)
  Fixpoint gamma_derivation_of_trace
      (m : @finite_enfa A)
      (root : enfa_state (fenfa_base m))
      (t : enfa_trace m)
      (q : enfa_state (fenfa_base m))
      : rlg_derivation (gamma_grammar_from m root) :=
    match t with
    | [] => [(q, [], None)]
    | ((p, l), q') :: t' =>
        (p, option_label_word l, Some q') ::
        gamma_derivation_of_trace m root t' q
    end.

  Fixpoint gamma_prefix_derivation_of_trace
      (m : @finite_enfa A)
      (root : enfa_state (fenfa_base m))
      (t : enfa_trace m)
      : rlg_derivation (gamma_grammar_from m root) :=
    match t with
    | [] => []
    | ((p, l), q') :: t' =>
        (p, option_label_word l, Some q') ::
        gamma_prefix_derivation_of_trace m root t'
    end.

  Definition gamma_accepting_maximal_reflects
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    forall q t w,
      valid_trace m s t q ->
      trace_word t = w ->
      enfa_final (fenfa_base m) q = true ->
      epsilon_simpleb m (s, t) = true ->
      (enfa_accepting_maximal_epsilon_simpleb m (s, t) = true <->
       rlg_accepting_maximal_epsilon_simpleb
         (gamma_grammar_from m s)
         (fenfa_state_eqb m)
         s
         (gamma_derivation_of_trace m s t q) = true).

  Definition gamma_label_of_word (u : list A) : option (option A) :=
    match u with
    | [] => Some None
    | [a] => Some (Some a)
    | _ :: _ :: _ => None
    end.

  Fixpoint gamma_trace_of_derivation
      (m : @finite_enfa A)
      (root : enfa_state (fenfa_base m))
      (d : rlg_derivation (gamma_grammar_from m root))
      : option (enfa_trace m) :=
    match d with
    | [] => None
    | (_, _, None) :: [] => Some []
    | (X, u, Some Y) :: d' =>
        match gamma_label_of_word u, gamma_trace_of_derivation m root d' with
        | Some l, Some t => Some (((X, l), Y) :: t)
        | _, _ => None
        end
    | (_, _, None) :: _ :: _ => None
    end.

  Fixpoint gamma_trace_of_prefix_derivation
      (m : @finite_enfa A)
      (root : enfa_state (fenfa_base m))
      (d : rlg_derivation (gamma_grammar_from m root))
      : option (enfa_trace m) :=
    match d with
    | [] => Some []
    | (X, u, Some Y) :: d' =>
        match gamma_label_of_word u, gamma_trace_of_prefix_derivation m root d' with
        | Some l, Some t => Some (((X, l), Y) :: t)
        | _, _ => None
        end
    | (_, _, None) :: _ => None
    end.

  Definition enfa_accepts_from
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m))
      (w : list A) : Prop :=
    exists q t,
      valid_trace m s t q /\
      trace_word t = w /\
      enfa_final (fenfa_base m) q = true.

  Lemma gamma_final_prod_in :
    forall (m : @finite_enfa A) q,
      In q (enfa_final_states m) ->
      In (q, [], None) (gamma_productions m).
  Proof.
    intros m q Hq.
    unfold gamma_productions, gamma_final_productions.
    apply in_or_app. left.
    apply in_map_iff.
    exists q. split; [reflexivity | exact Hq].
  Qed.

  Lemma gamma_epsilon_prod_in :
    forall (m : @finite_enfa A) p q,
      In p (fenfa_states m) ->
      In q (enfa_step (fenfa_base m) p None) ->
      In (p, [], Some q) (gamma_productions m).
  Proof.
    intros m p q Hp Hq.
    unfold gamma_productions.
    apply in_or_app. right.
    apply in_or_app. left.
    unfold gamma_epsilon_productions.
    apply in_concat.
    exists (map (fun q0 => (p, [], Some q0))
              (enfa_step (fenfa_base m) p None)).
    split.
    - apply in_map_iff.
      exists p. split; [reflexivity | exact Hp].
    - apply in_map_iff.
      exists q. split; [reflexivity | exact Hq].
  Qed.

  Lemma gamma_symbol_prod_in :
    forall (m : @finite_enfa A) p a q,
      In p (fenfa_states m) ->
      In a (fenfa_alphabet m) ->
      In q (enfa_step (fenfa_base m) p (Some a)) ->
      In (p, [a], Some q) (gamma_productions m).
  Proof.
    intros m p a q Hp Ha Hq.
    unfold gamma_productions.
    apply in_or_app. right.
    apply in_or_app. right.
    unfold gamma_symbol_productions.
    apply in_concat.
    exists
      (concat
         (map
            (fun a0 =>
               map (fun q0 => (p, [a0], Some q0))
                 (enfa_step (fenfa_base m) p (Some a0)))
            (fenfa_alphabet m))).
    split.
    - apply in_map_iff.
      exists p. split; [reflexivity | exact Hp].
    - apply in_concat.
      exists
        (map (fun q0 => (p, [a], Some q0))
           (enfa_step (fenfa_base m) p (Some a))).
      split.
      + apply in_map_iff.
        exists a. split; [reflexivity | exact Ha].
      + apply in_map_iff.
        exists q. split; [reflexivity | exact Hq].
  Qed.

  (** Gamma production introduction and inversion.  These lemmas show that
      Gamma productions correspond exactly to ENFA final states, epsilon
      transitions, or symbol transitions. *)
  Lemma gamma_transition_prod_in :
    forall (m : @finite_enfa A) p l q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      In q (enfa_step (fenfa_base m) p l) ->
      In (p, option_label_word l, Some q) (gamma_productions m).
  Proof.
    intros m p [a|] q Hwf Hp Hstep; simpl.
    - apply gamma_symbol_prod_in; auto.
      eapply fenfa_steps_in_alphabet; eauto.
    - now apply gamma_epsilon_prod_in.
  Qed.

  Lemma gamma_final_state_prod :
    forall (m : @finite_enfa A) q,
      In q (fenfa_states m) ->
      enfa_final (fenfa_base m) q = true ->
      In (q, [], None) (gamma_productions m).
  Proof.
    intros m q Hq Hfinal.
    apply gamma_final_prod_in.
    unfold enfa_final_states.
    apply filter_In. split; auto.
  Qed.

  Lemma gamma_none_prod_inv :
    forall (m : @finite_enfa A) X u,
      In (X, u, None) (gamma_productions m) ->
      u = [] /\ In X (enfa_final_states m).
  Proof.
    intros m X u H.
    unfold gamma_productions in H.
    apply in_app_or in H as [H | H].
    - unfold gamma_final_productions in H.
      apply in_map_iff in H as [q [Hq Hqin]].
      inversion Hq; subst. split; auto.
    - apply in_app_or in H as [H | H].
      + unfold gamma_epsilon_productions in H.
        apply in_concat in H as [xs [Hxs Hin]].
        apply in_map_iff in Hxs as [p [Hxs _]].
        subst xs.
        apply in_map_iff in Hin as [q [Hq _]].
        discriminate.
      + unfold gamma_symbol_productions in H.
        apply in_concat in H as [xs [Hxs Hin]].
        apply in_map_iff in Hxs as [p [Hxs _]].
        subst xs.
        apply in_concat in Hin as [ys [Hys Hin]].
        apply in_map_iff in Hys as [a [Hys _]].
        subst ys.
        apply in_map_iff in Hin as [q [Hq _]].
        discriminate.
  Qed.

  Lemma gamma_some_prod_inv :
    forall (m : @finite_enfa A) X u Y,
      In (X, u, Some Y) (gamma_productions m) ->
      (u = [] /\ In X (fenfa_states m) /\
       In Y (enfa_step (fenfa_base m) X None)) \/
      (exists a,
        u = [a] /\ In X (fenfa_states m) /\ In a (fenfa_alphabet m) /\
        In Y (enfa_step (fenfa_base m) X (Some a))).
  Proof.
    intros m X u Y H.
    unfold gamma_productions in H.
    apply in_app_or in H as [H | H].
    - unfold gamma_final_productions in H.
      apply in_map_iff in H as [q [Hq _]].
      discriminate.
    - apply in_app_or in H as [H | H].
      + left.
        unfold gamma_epsilon_productions in H.
        apply in_concat in H as [xs [Hxs Hin]].
        apply in_map_iff in Hxs as [p [Hxs Hp]].
        subst xs.
        apply in_map_iff in Hin as [q [Hq Hqstep]].
        inversion Hq; subst.
        repeat split; auto.
      + right.
        unfold gamma_symbol_productions in H.
        apply in_concat in H as [xs [Hxs Hin]].
        apply in_map_iff in Hxs as [p [Hxs Hp]].
        subst xs.
        apply in_concat in Hin as [ys [Hys Hin]].
        apply in_map_iff in Hys as [a [Hys Ha]].
        subst ys.
        apply in_map_iff in Hin as [q [Hq Hqstep]].
        inversion Hq; subst.
        exists a. repeat split; auto.
  Qed.

  Lemma gamma_epsilon_productions_length :
    forall (m : @finite_enfa A),
      length (gamma_epsilon_productions m) =
      enfa_epsilon_transition_bound m.
  Proof.
    intros m.
    unfold gamma_epsilon_productions, enfa_epsilon_transition_bound.
    rewrite length_concat_map_sum_nats.
    induction (fenfa_states m) as [| p ps IH]; simpl.
    - reflexivity.
    - rewrite length_map. now rewrite IH.
  Qed.

  Lemma gamma_filter_final_epsilon_step :
    forall (m : @finite_enfa A),
      filter
        (fun prod =>
           match prod with
           | (_, [], Some _) => true
           | _ => false
           end)
        (gamma_final_productions m) = [].
  Proof.
    intros m.
    unfold gamma_final_productions.
    induction (enfa_final_states m) as [| q qs IH]; simpl; auto.
  Qed.

  Lemma gamma_filter_epsilon_epsilon_step :
    forall (m : @finite_enfa A),
      filter
        (fun prod =>
           match prod with
           | (_, [], Some _) => true
           | _ => false
           end)
        (gamma_epsilon_productions m) =
      gamma_epsilon_productions m.
  Proof.
    intros m.
    unfold gamma_epsilon_productions.
    induction (fenfa_states m) as [| p ps IH]; simpl.
    - reflexivity.
    - rewrite filter_app. f_equal.
      + induction (enfa_step (fenfa_base m) p None) as [| q qs IHq];
          simpl; auto.
        now rewrite IHq.
      + exact IH.
  Qed.

  Lemma gamma_filter_symbol_epsilon_step :
    forall (m : @finite_enfa A),
      filter
        (fun prod =>
           match prod with
           | (_, [], Some _) => true
           | _ => false
           end)
        (gamma_symbol_productions m) = [].
  Proof.
    intros m.
    unfold gamma_symbol_productions.
    generalize (fenfa_alphabet m) as alph.
    induction (fenfa_states m) as [| p ps IHps]; intros alph; simpl.
    - reflexivity.
    - rewrite filter_app, IHps, app_nil_r.
      induction alph as [| a alph IHa]; simpl.
      + reflexivity.
      + rewrite filter_app, IHa, app_nil_r.
        induction (enfa_step (fenfa_base m) p (Some a)) as [| q qs IHq];
          simpl.
        * reflexivity.
        * exact IHq.
  Qed.

  Lemma gamma_rlg_epsilon_transition_bound :
    forall (m : @finite_enfa A) root,
      rlg_epsilon_transition_bound (gamma_grammar_from m root) =
      enfa_epsilon_transition_bound m.
  Proof.
    intros m root.
    unfold rlg_epsilon_transition_bound, gamma_grammar_from.
    simpl.
    unfold gamma_productions.
    rewrite filter_app.
    rewrite gamma_filter_final_epsilon_step.
    rewrite filter_app.
    rewrite gamma_filter_epsilon_epsilon_step.
    rewrite gamma_filter_symbol_epsilon_step.
    simpl.
    rewrite app_nil_r.
    apply gamma_epsilon_productions_length.
  Qed.

  Definition gamma_epsilon_successor_chunk
      (m : @finite_enfa A)
      (q : enfa_state (fenfa_base m))
      (prod : enfa_state (fenfa_base m) * list A *
              option (enfa_state (fenfa_base m)))
      : list (enfa_state (fenfa_base m)) :=
    match prod with
    | (p, [], Some r) =>
        if fenfa_state_eqb m q p then [r] else []
    | _ => []
    end.

  Lemma gamma_epsilon_successor_chunk_epsilon_targets :
    forall (m : @finite_enfa A) q p,
      concat
        (map (gamma_epsilon_successor_chunk m q)
           (map (fun r => (p, [], Some r))
              (enfa_step (fenfa_base m) p None))) =
      if fenfa_state_eqb m q p
      then enfa_step (fenfa_base m) p None
      else [].
  Proof.
    intros m q p.
    destruct (fenfa_state_eqb m q p) eqn:Heq.
    - induction (enfa_step (fenfa_base m) p None) as [| r rs IH];
        simpl.
      + reflexivity.
      + rewrite Heq. simpl. now rewrite IH.
    - induction (enfa_step (fenfa_base m) p None) as [| r rs IH];
        simpl.
      + reflexivity.
      + rewrite Heq. exact IH.
  Qed.

  Lemma gamma_epsilon_successors_from_states_notin :
    forall (m : @finite_enfa A) q ps,
      ~ In q ps ->
      concat
        (map (gamma_epsilon_successor_chunk m q)
           (concat
              (map
                 (fun p =>
                    map (fun r => (p, [], Some r))
                      (enfa_step (fenfa_base m) p None))
                 ps))) = [].
  Proof.
    intros m q ps.
    induction ps as [| p ps IH]; intros Hnotin.
    - lazy. reflexivity.
    - cbn. rewrite map_app, concat_app.
      replace
        (concat
           (map (gamma_epsilon_successor_chunk m q)
              (map (fun r => (p, [], Some r))
                 (enfa_step (fenfa_base m) p None))))
        with
          (if fenfa_state_eqb m q p
           then enfa_step (fenfa_base m) p None
           else [])
        by (symmetry; apply gamma_epsilon_successor_chunk_epsilon_targets).
      destruct (fenfa_state_eqb m q p) eqn:Heq.
      + apply fenfa_state_eqb_sound in Heq. subst p.
        exfalso. apply Hnotin. simpl. left. reflexivity.
      + rewrite IH.
        * reflexivity.
        * intro Hin. apply Hnotin. simpl. auto.
  Qed.

  Lemma gamma_epsilon_successors_from_states :
    forall (m : @finite_enfa A) q ps,
      NoDup ps ->
      In q ps ->
      concat
        (map (gamma_epsilon_successor_chunk m q)
           (concat
              (map
                 (fun p =>
                    map (fun r => (p, [], Some r))
                      (enfa_step (fenfa_base m) p None))
                 ps))) =
      enfa_step (fenfa_base m) q None.
  Proof.
    intros m q ps Hnodup Hq.
    induction ps as [| p ps IH]; simpl in Hq.
    - contradiction.
    - inversion Hnodup as [| p' ps' Hnotin Hnodup']; subst.
      simpl.
      rewrite map_app, concat_app.
      replace
        (concat
           (map (gamma_epsilon_successor_chunk m q)
              (map (fun r => (p, [], Some r))
                 (enfa_step (fenfa_base m) p None))))
        with
          (if fenfa_state_eqb m q p
           then enfa_step (fenfa_base m) p None
           else [])
        by (symmetry; apply gamma_epsilon_successor_chunk_epsilon_targets).
      destruct (fenfa_state_eqb m q p) eqn:Heq.
      + apply fenfa_state_eqb_sound in Heq. subst p.
        rewrite gamma_epsilon_successors_from_states_notin.
        * rewrite app_nil_r. reflexivity.
        * exact Hnotin.
      + destruct Hq as [Hq | Hq].
        * subst p.
          rewrite (fenfa_state_eqb_complete m q q eq_refl) in Heq.
          discriminate.
        * rewrite (IH Hnodup' Hq). reflexivity.
  Qed.

  Lemma gamma_epsilon_successors_final_nil :
    forall (m : @finite_enfa A) q,
      concat
        (map (gamma_epsilon_successor_chunk m q)
           (gamma_final_productions m)) = [].
  Proof.
    intros m q.
    unfold gamma_final_productions.
    induction (enfa_final_states m) as [| r rs IH]; simpl; auto.
  Qed.

  Lemma gamma_epsilon_successors_symbol_nil :
    forall (m : @finite_enfa A) q,
      concat
        (map (gamma_epsilon_successor_chunk m q)
           (gamma_symbol_productions m)) = [].
  Proof.
    intros m q.
    unfold gamma_symbol_productions.
    generalize (fenfa_alphabet m) as alph.
    induction (fenfa_states m) as [| p ps IHps]; intros alph; simpl.
    - reflexivity.
    - rewrite map_app, concat_app, IHps, app_nil_r.
      induction alph as [| a alph IHa]; simpl.
      + reflexivity.
      + rewrite map_app, concat_app, IHa, app_nil_r.
        induction (enfa_step (fenfa_base m) p (Some a)) as [| r rs IHr];
          simpl.
        * reflexivity.
        * exact IHr.
  Qed.

  Lemma gamma_epsilon_successors_eq :
    forall (m : @finite_enfa A) root q,
      finite_enfa_wf m ->
      In q (fenfa_states m) ->
      rlg_epsilon_successors
        (gamma_grammar_from m root) (fenfa_state_eqb m) q =
      enfa_step (fenfa_base m) q None.
  Proof.
    intros m root q Hwf Hq.
    unfold rlg_epsilon_successors, gamma_grammar_from. simpl.
    unfold gamma_productions.
    change
      (concat
         (map (gamma_epsilon_successor_chunk m q)
            (gamma_final_productions m ++
             gamma_epsilon_productions m ++
             gamma_symbol_productions m)) =
       enfa_step (fenfa_base m) q None).
    rewrite !map_app, !concat_app.
    rewrite gamma_epsilon_successors_final_nil.
    rewrite gamma_epsilon_successors_symbol_nil.
    simpl.
    rewrite app_nil_r.
    unfold gamma_epsilon_productions.
    apply gamma_epsilon_successors_from_states.
    - apply fenfa_states_nodup. exact Hwf.
    - exact Hq.
  Qed.

  Lemma trace_word_cons :
    forall (m : @finite_enfa A) p l q t,
      @trace_word A m (((p, l), q) :: t) =
      option_label_word l ++ @trace_word A m t.
  Proof.
    intros m p [a|] q t; reflexivity.
  Qed.

  Lemma gamma_derivation_of_trace_word :
    forall (m : @finite_enfa A) root t q,
      rlg_derivation_word
        (gamma_grammar_from m root)
        (gamma_derivation_of_trace m root t q) =
      trace_word t.
  Proof.
    intros m root t.
    induction t as [| [[p l] q'] t IH]; intros q; simpl.
    - reflexivity.
    - rewrite IH. destruct l; reflexivity.
  Qed.

  Lemma gamma_prefix_derivation_of_trace_word :
    forall (m : @finite_enfa A) root t,
      rlg_derivation_word
        (gamma_grammar_from m root)
        (gamma_prefix_derivation_of_trace m root t) =
      trace_word t.
  Proof.
    intros m root t.
    induction t as [| [[p l] q] t IH]; simpl.
    - reflexivity.
    - rewrite IH. destruct l; reflexivity.
  Qed.

  (** Trace/derivation roundtrip properties for the Gamma bridge.  Gamma
      derivations preserve both language and ENFA trace structure; injectivity
      turns distinct trace/end pairs into distinct grammar derivations. *)
  Lemma gamma_derivation_of_trace_length :
    forall (m : @finite_enfa A) root t q,
      length (gamma_derivation_of_trace m root t q) = S (length t).
  Proof.
    intros m root t.
    induction t as [| [[p l] q'] t IH]; intros q; simpl.
    - reflexivity.
    - now rewrite IH.
  Qed.

  Lemma gamma_prefix_derivation_of_trace_length :
    forall (m : @finite_enfa A) root t,
      length (gamma_prefix_derivation_of_trace m root t) = length t.
  Proof.
    intros m root t.
    induction t as [| [[p l] q] t IH]; simpl.
    - reflexivity.
    - now rewrite IH.
  Qed.

  Lemma gamma_trace_of_derivation_of_trace :
    forall (m : @finite_enfa A) root t q,
      gamma_trace_of_derivation m root
        (gamma_derivation_of_trace m root t q) = Some t.
  Proof.
    intros m root t.
    induction t as [| [[p l] q'] t IH]; intros q; simpl.
    - reflexivity.
    - rewrite IH. destruct l; reflexivity.
  Qed.

  Lemma gamma_trace_of_prefix_derivation_of_trace :
    forall (m : @finite_enfa A) root t,
      gamma_trace_of_prefix_derivation m root
        (gamma_prefix_derivation_of_trace m root t) = Some t.
  Proof.
    intros m root t.
    induction t as [| [[p l] q] t IH]; simpl.
    - reflexivity.
    - rewrite IH. destruct l; reflexivity.
  Qed.

  Lemma gamma_prefix_derivation_of_trace_injective :
    forall (m : @finite_enfa A) root t1 t2,
      gamma_prefix_derivation_of_trace m root t1 =
      gamma_prefix_derivation_of_trace m root t2 ->
      t1 = t2.
  Proof.
    intros m root t1 t2 Heq.
    pose proof
      (f_equal (gamma_trace_of_prefix_derivation m root) Heq) as Htrace.
    rewrite !gamma_trace_of_prefix_derivation_of_trace in Htrace.
    inversion Htrace. reflexivity.
  Qed.

  Lemma gamma_derivation_of_trace_injective :
    forall (m : @finite_enfa A) root t1 q1 t2 q2,
      gamma_derivation_of_trace m root t1 q1 =
      gamma_derivation_of_trace m root t2 q2 ->
      t1 = t2 /\ q1 = q2.
  Proof.
    intros m root t1.
    induction t1 as [| e1 t1 IH]; intros q1 t2 q2 Heq.
    - destruct t2 as [| e2 t2].
      + simpl in Heq. inversion Heq. split; reflexivity.
      + destruct e2 as [[p2 l2] r2].
        simpl in Heq. inversion Heq; subst.
    - destruct t2 as [| e2 t2].
      + destruct e1 as [[p1 l1] r1].
        simpl in Heq. inversion Heq; subst.
      + simpl in Heq.
        destruct e1 as [[p1 l1] r1].
        destruct e2 as [[p2 l2] r2].
        inversion Heq; subst.
        match goal with
        | Htail :
            gamma_derivation_of_trace m root t1 q1 =
            gamma_derivation_of_trace m root t2 q2 |- _ =>
            destruct (IH q1 t2 q2 Htail) as [Ht Hq]
        end.
        match goal with
        | Hword : option_label_word l1 = option_label_word l2 |- _ =>
            apply option_label_word_injective in Hword; subst l2
        end.
        split; congruence.
  Qed.

  Theorem section4_gamma_support_trace_derivation_pair_injective :
    forall (m : @finite_enfa A) root t1 q1 t2 q2,
      gamma_derivation_of_trace m root t1 q1 =
      gamma_derivation_of_trace m root t2 q2 ->
      t1 = t2 /\ q1 = q2.
  Proof.
    intros. now apply gamma_derivation_of_trace_injective in H.
  Qed.

  (** Epsilon-simple preservation: [rlg_epsilon_simpleb] on Gamma derivations
      corresponds to [epsilon_simpleb] on ENFA traces, forming the first part
      of the prime ambiguity bridge. *)
  Lemma gamma_derivation_of_trace_epsilon_simple_from :
    forall (m : @finite_enfa A) root seen t q,
      rlg_epsilon_simpleb_from
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        seen
        (gamma_derivation_of_trace m root t q) =
      epsilon_simpleb_from m seen t.
  Proof.
    intros m root seen t.
    revert seen.
    induction t as [| [[p l] q'] t IH]; intros seen q; simpl.
    - reflexivity.
    - destruct l; simpl; now rewrite IH.
  Qed.

  Theorem section4_gamma_support_trace_derivation_epsilon_simple :
    forall (m : @finite_enfa A) root p t q,
      rlg_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        p
        (gamma_derivation_of_trace m root t q) =
      epsilon_simpleb m (p, t).
  Proof.
    intros m root p t q.
    unfold rlg_epsilon_simpleb, epsilon_simpleb.
    apply gamma_derivation_of_trace_epsilon_simple_from.
  Qed.

  Lemma gamma_prefix_derivation_of_trace_epsilon_simple_from :
    forall (m : @finite_enfa A) root seen t,
      rlg_epsilon_simpleb_from
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        seen
        (gamma_prefix_derivation_of_trace m root t) =
      epsilon_simpleb_from m seen t.
  Proof.
    intros m root seen t.
    revert seen.
    induction t as [| [[p l] q] t IH]; intros seen; simpl.
    - reflexivity.
    - destruct l; simpl; now rewrite IH.
  Qed.

  Theorem section4_gamma_support_prefix_trace_derivation_epsilon_simple :
    forall (m : @finite_enfa A) root p t,
      rlg_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        p
        (gamma_prefix_derivation_of_trace m root t) =
      epsilon_simpleb m (p, t).
  Proof.
    intros m root p t.
    unfold rlg_epsilon_simpleb, epsilon_simpleb.
    apply gamma_prefix_derivation_of_trace_epsilon_simple_from.
  Qed.

  Lemma gamma_derivation_of_trace_epsilon_suffix :
    forall (m : @finite_enfa A) root seen t q,
      rlg_epsilon_suffix_nonterminals
        (gamma_grammar_from m root)
        seen
        (gamma_derivation_of_trace m root t q) =
      epsilon_suffix_states m seen t.
  Proof.
    intros m root seen t.
    revert seen.
    induction t as [| [[p l] q'] t IH]; intros seen q; simpl.
    - reflexivity.
    - destruct l; simpl; now rewrite IH.
  Qed.

  Lemma gamma_prefix_derivation_of_trace_epsilon_suffix :
    forall (m : @finite_enfa A) root seen t,
      rlg_epsilon_suffix_nonterminals
        (gamma_grammar_from m root)
        seen
        (gamma_prefix_derivation_of_trace m root t) =
      epsilon_suffix_states m seen t.
  Proof.
    intros m root seen t.
    revert seen.
    induction t as [| [[p l] q] t IH]; intros seen; simpl.
    - reflexivity.
    - destruct l; simpl; now rewrite IH.
  Qed.

  Lemma finite_enfa_wf_valid_trace_end_in_states :
    forall (m : @finite_enfa A) p t q,
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

  Lemma valid_trace_trace_end :
    forall (m : @finite_enfa A) p t q,
      valid_trace m p t q ->
      trace_end p t = q.
  Proof.
    intros m p t q Htrace.
    induction Htrace as [q| p l q r t _ _ IH]; simpl.
    - reflexivity.
    - exact IH.
  Qed.

  Lemma gamma_derivation_of_trace_end_valid :
    forall (m : @finite_enfa A) root p t q,
      valid_trace m p t q ->
      rlg_derivation_end
        (gamma_grammar_from m root)
        p
        (gamma_derivation_of_trace m root t q) = q.
  Proof.
    intros m root p t q Htrace.
    induction Htrace as [q| p l q r t _ _ IH]; simpl.
    - reflexivity.
    - exact IH.
  Qed.

  Lemma gamma_prefix_derivation_of_trace_end_valid :
    forall (m : @finite_enfa A) root p t q,
      valid_trace m p t q ->
      rlg_derivation_end
        (gamma_grammar_from m root)
        p
        (gamma_prefix_derivation_of_trace m root t) = q.
  Proof.
    intros m root p t q Htrace.
    induction Htrace as [q| p l q r t _ _ IH]; simpl.
    - reflexivity.
    - exact IH.
  Qed.

  (** Maximal epsilon-simple preservation.  These theorems relate the Gamma
      maximal filter to ENFA [maximal_epsilon_simpleb]; together with
      epsilon-simple preservation, this supports the paper's prime measures. *)
  Lemma gamma_final_nonterminalb_eq :
    forall (m : @finite_enfa A) root q,
      finite_enfa_wf m ->
      In q (fenfa_states m) ->
      rlg_final_nonterminalb
        (gamma_grammar_from m root) (fenfa_state_eqb m) q =
      enfa_final (fenfa_base m) q.
  Proof.
    intros m root q _ Hq.
    destruct (enfa_final (fenfa_base m) q) eqn:Hfinal.
    - unfold rlg_final_nonterminalb.
      apply existsb_exists.
      exists (q, [], None). split.
      + apply gamma_final_state_prod; auto.
      + simpl. apply fenfa_state_eqb_complete. reflexivity.
    - apply Bool.not_true_iff_false.
      intro Htrue.
      unfold rlg_final_nonterminalb in Htrue.
      apply existsb_exists in Htrue as [[[Y u] opt] [Hprod Hmatch]].
      destruct opt as [Z|].
      + destruct u as [| a u]; simpl in Hmatch; discriminate.
      + destruct u as [| a u].
        * simpl in Hmatch.
          apply fenfa_state_eqb_sound in Hmatch. subst Y.
          apply gamma_none_prod_inv in Hprod as [_ Hfinals].
          unfold enfa_final_states in Hfinals.
          apply filter_In in Hfinals as [_ Hfinal_q].
          congruence.
        * simpl in Hmatch. discriminate.
  Qed.

  Lemma gamma_epsilon_closure_fuel :
    forall (m : @finite_enfa A) root fuel seen todo,
      finite_enfa_wf m ->
      (forall q, In q todo -> In q (fenfa_states m)) ->
      rlg_epsilon_closure_fuel
        (gamma_grammar_from m root) (fenfa_state_eqb m)
        fuel seen todo =
      enfa_epsilon_closure_fuel m fuel seen todo.
  Proof.
    intros m root fuel.
    induction fuel as [| fuel IH]; intros seen todo Hwf Htodo.
    - reflexivity.
    - destruct todo as [| q todo']; simpl.
      + reflexivity.
      + assert (Hinb_eq :
          rlg_nt_inb
            (gamma_grammar_from m root) (fenfa_state_eqb m) q seen =
          state_inb m q seen).
        { unfold rlg_nt_inb, state_inb. reflexivity. }
        rewrite Hinb_eq.
        destruct (state_inb m q seen) eqn:Hs.
        * apply IH; auto.
          intros x Hx. apply Htodo. simpl. auto.
        * rewrite gamma_epsilon_successors_eq by
            (auto; apply Htodo; simpl; auto).
          f_equal.
          apply IH; auto.
          intros x Hx.
          apply in_app_or in Hx as [Hx | Hx].
          -- eapply fenfa_steps_in_states; eauto.
             apply Htodo. simpl. auto.
          -- apply Htodo. simpl. auto.
  Qed.

  Theorem section4_gamma_support_trace_derivation_strict_epsilon_closure :
    forall (m : @finite_enfa A) root p t q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      rlg_strict_epsilon_closure_nonterminals
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        p
        (gamma_derivation_of_trace m root t q) =
      enfa_strict_epsilon_closure_states m (p, t).
  Proof.
    intros m root p t q Hwf Hp Htrace.
    pose proof
      (finite_enfa_wf_valid_trace_end_in_states m p t q Hwf Hp Htrace)
      as Hqstates.
    pose proof (valid_trace_trace_end m p t q Htrace) as Hend.
    unfold rlg_strict_epsilon_closure_nonterminals,
      enfa_strict_epsilon_closure_states.
    unfold started_end. simpl. rewrite Hend.
    rewrite gamma_derivation_of_trace_epsilon_suffix.
    rewrite (gamma_derivation_of_trace_end_valid m root p t q Htrace).
    rewrite gamma_rlg_epsilon_transition_bound.
    rewrite gamma_epsilon_successors_eq by auto.
    change
      (filter
         (fun Y =>
            negb
              (rlg_nt_inb
                 (gamma_grammar_from m root) (fenfa_state_eqb m) Y
                 (epsilon_suffix_states m [p] t)))
         (enfa_step (fenfa_base m) q None))
      with
      (filter
         (fun q' => negb (state_inb m q' (epsilon_suffix_states m [p] t)))
         (enfa_step (fenfa_base m) q None)).
    apply gamma_epsilon_closure_fuel; auto.
    intros x Hx.
    apply filter_In in Hx as [Hstep _].
    eapply fenfa_steps_in_states; eauto.
  Qed.

  Theorem section4_gamma_support_trace_derivation_accepting_maximal_epsilon_simple :
    forall (m : @finite_enfa A) root p t q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      enfa_accepting_maximal_epsilon_simpleb m (p, t) =
      rlg_accepting_maximal_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        p
        (gamma_derivation_of_trace m root t q).
  Proof.
    intros m root p t q Hwf Hp Htrace.
    pose proof (valid_trace_trace_end m p t q Htrace) as Hend.
    pose proof
      (finite_enfa_wf_valid_trace_end_in_states m p t q Hwf Hp Htrace) as Hq.
    unfold enfa_accepting_maximal_epsilon_simpleb,
      rlg_accepting_maximal_epsilon_simpleb.
    rewrite section4_gamma_support_trace_derivation_strict_epsilon_closure
      by auto.
    apply forallb_ext_in.
    intros x Hx.
    rewrite gamma_final_nonterminalb_eq by
      (auto;
       eapply enfa_strict_epsilon_closure_states_in_states; eauto;
       unfold started_end; simpl; rewrite Hend; exact Hq).
    reflexivity.
  Qed.

  Theorem section4_gamma_accepting_maximal_reflects :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      gamma_accepting_maximal_reflects m s.
  Proof.
    intros m s Hwf Hs q t w Htrace _ _ _.
    pose proof
      (section4_gamma_support_trace_derivation_accepting_maximal_epsilon_simple
         m s s t q Hwf Hs Htrace) as Heq.
    split; intro H.
    - rewrite <- Heq. exact H.
    - rewrite Heq. exact H.
  Qed.

  Theorem section4_gamma_support_trace_derivation_maximal_epsilon_simple :
    forall (m : @finite_enfa A) root p t q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      maximal_epsilon_simpleb m (p, t) = true ->
      rlg_maximal_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        p
        (gamma_derivation_of_trace m root t q) = true.
  Proof.
    intros m root p t q _ _ Htrace Hmax.
    unfold rlg_maximal_epsilon_simpleb.
    rewrite gamma_derivation_of_trace_epsilon_suffix.
    rewrite (gamma_derivation_of_trace_end_valid m root p t q Htrace).
    unfold rlg_maximal_epsilon_simpleb_from.
    apply forallb_forall.
    intros [[X u] [Y|]] Hprod; simpl.
    - destruct u as [| a u]; simpl.
      + destruct (fenfa_state_eqb m q X) eqn:Heq.
        * apply fenfa_state_eqb_sound in Heq.
          subst X.
          apply gamma_some_prod_inv in Hprod as
            [[_ [_ Hstep]] | [a [Hu _]]].
          -- unfold maximal_epsilon_simpleb in Hmax.
             simpl in Hmax.
             pose proof (valid_trace_trace_end m p t q Htrace) as Hend.
             rewrite <- Hend in Hstep.
             rewrite forallb_forall in Hmax.
             unfold rlg_nt_inb, state_inb.
             now apply Hmax.
          -- discriminate.
        * reflexivity.
      + reflexivity.
    - destruct u; reflexivity.
  Qed.

  Theorem section4_gamma_support_trace_derivation_maximal_epsilon_simple_complete :
    forall (m : @finite_enfa A) root p t q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      rlg_maximal_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        p
        (gamma_derivation_of_trace m root t q) = true ->
      maximal_epsilon_simpleb m (p, t) = true.
  Proof.
    intros m root p t q Hwf Hp Htrace Hmax.
    unfold maximal_epsilon_simpleb.
    simpl.
    unfold rlg_maximal_epsilon_simpleb in Hmax.
    rewrite gamma_derivation_of_trace_epsilon_suffix in Hmax.
    rewrite (gamma_derivation_of_trace_end_valid m root p t q Htrace) in Hmax.
    unfold rlg_maximal_epsilon_simpleb_from in Hmax.
    apply forallb_forall.
    intros q' Hstep.
    pose proof (valid_trace_trace_end m p t q Htrace) as Hend.
    unfold started_end in Hstep. simpl in Hstep.
    rewrite Hend in Hstep.
    rewrite forallb_forall in Hmax.
    specialize
      (Hmax (q, [], Some q')
         (gamma_epsilon_prod_in m q q'
            (finite_enfa_wf_valid_trace_end_in_states m p t q Hwf Hp Htrace)
            Hstep)).
    simpl in Hmax.
    rewrite (fenfa_state_eqb_complete m q q eq_refl) in Hmax.
    exact Hmax.
  Qed.

  Theorem section4_gamma_support_prefix_trace_derivation_maximal_epsilon_simple :
    forall (m : @finite_enfa A) root p t q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      maximal_epsilon_simpleb m (p, t) = true ->
      rlg_maximal_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        p
        (gamma_prefix_derivation_of_trace m root t) = true.
  Proof.
    intros m root p t q _ _ Htrace Hmax.
    unfold rlg_maximal_epsilon_simpleb.
    rewrite gamma_prefix_derivation_of_trace_epsilon_suffix.
    rewrite (gamma_prefix_derivation_of_trace_end_valid m root p t q Htrace).
    unfold rlg_maximal_epsilon_simpleb_from.
    apply forallb_forall.
    intros [[X u] [Y|]] Hprod; simpl.
    - destruct u as [| a u]; simpl.
      + destruct (fenfa_state_eqb m q X) eqn:Heq.
        * apply fenfa_state_eqb_sound in Heq.
          subst X.
          apply gamma_some_prod_inv in Hprod as
            [[_ [_ Hstep]] | [a [Hu _]]].
          -- unfold maximal_epsilon_simpleb in Hmax.
             simpl in Hmax.
             pose proof (valid_trace_trace_end m p t q Htrace) as Hend.
             rewrite <- Hend in Hstep.
             rewrite forallb_forall in Hmax.
             unfold rlg_nt_inb, state_inb.
             now apply Hmax.
          -- discriminate.
        * reflexivity.
      + reflexivity.
    - destruct u; reflexivity.
  Qed.

  Theorem section4_gamma_support_prefix_trace_derivation_maximal_epsilon_simple_complete :
    forall (m : @finite_enfa A) root p t q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      rlg_maximal_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        p
        (gamma_prefix_derivation_of_trace m root t) = true ->
      maximal_epsilon_simpleb m (p, t) = true.
  Proof.
    intros m root p t q Hwf Hp Htrace Hmax.
    unfold maximal_epsilon_simpleb.
    simpl.
    unfold rlg_maximal_epsilon_simpleb in Hmax.
    rewrite gamma_prefix_derivation_of_trace_epsilon_suffix in Hmax.
    rewrite (gamma_prefix_derivation_of_trace_end_valid m root p t q Htrace) in Hmax.
    unfold rlg_maximal_epsilon_simpleb_from in Hmax.
    apply forallb_forall.
    intros q' Hstep.
    pose proof (valid_trace_trace_end m p t q Htrace) as Hend.
    unfold started_end in Hstep. simpl in Hstep.
    rewrite Hend in Hstep.
    rewrite forallb_forall in Hmax.
    specialize
      (Hmax (q, [], Some q')
         (gamma_epsilon_prod_in m q q'
            (finite_enfa_wf_valid_trace_end_in_states m p t q Hwf Hp Htrace)
            Hstep)).
    simpl in Hmax.
    rewrite (fenfa_state_eqb_complete m q q eq_refl) in Hmax.
    exact Hmax.
  Qed.

  Lemma gamma_derivation_of_trace_valid_from :
    forall (m : @finite_enfa A) root p q t,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      enfa_final (fenfa_base m) q = true ->
      rlg_derivation_valid
        (gamma_grammar_from m root)
        p
        (gamma_derivation_of_trace m root t q)
        None.
  Proof.
    intros m root p q t Hwf Hp Htrace Hfinal.
    induction Htrace as [q| p l q r t Hstep Htail IH].
    - simpl. apply RLGDerivation_stop.
      apply gamma_final_state_prod; auto.
    - simpl. eapply RLGDerivation_step.
      + eapply gamma_transition_prod_in; eauto.
      + apply IH; auto.
        eapply fenfa_steps_in_states; eauto.
  Qed.

  Lemma gamma_prefix_derivation_of_trace_valid_from :
    forall (m : @finite_enfa A) root p q t,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      rlg_prefix_derivation_valid
        (gamma_grammar_from m root)
        p
        (gamma_prefix_derivation_of_trace m root t)
        q.
  Proof.
    intros m root p q t Hwf Hp Htrace.
    induction Htrace as [q| p l q r t Hstep Htail IH].
    - simpl. constructor.
    - simpl. eapply RLGPrefix_step.
      + eapply gamma_transition_prod_in; eauto.
      + apply IH; auto.
        eapply fenfa_steps_in_states; eauto.
  Qed.

  Lemma gamma_derivation_of_trace_valid :
    forall (m : @finite_enfa A) s q t,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s t q ->
      enfa_final (fenfa_base m) q = true ->
      rlg_derivation_valid
        (gamma_grammar_from m s)
        s
        (gamma_derivation_of_trace m s t q)
        None.
  Proof.
    intros m s q t Hwf Hs Htrace Hfinal.
    eapply gamma_derivation_of_trace_valid_from; eauto.
  Qed.

  Lemma gamma_derives_of_trace_from :
    forall (m : @finite_enfa A) root p q t,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      enfa_final (fenfa_base m) q = true ->
      rlg_derives_from (gamma_grammar_from m root) p (trace_word t).
  Proof.
    intros m root p q t Hwf Hp Htrace Hfinal.
    induction Htrace as [q| p l q r t Hstep Htail IH].
    - simpl.
      apply RLG_stop.
      apply gamma_final_state_prod; auto.
    - rewrite trace_word_cons.
      eapply RLG_step.
      + simpl.
        eapply gamma_transition_prod_in; eauto.
      + apply IH; auto.
        eapply fenfa_steps_in_states; eauto.
  Qed.

  Lemma gamma_derives_of_trace :
    forall (m : @finite_enfa A) s q t,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s t q ->
      enfa_final (fenfa_base m) q = true ->
      rlg_derives_from (gamma_grammar_from m s) s (trace_word t).
  Proof.
    intros m s q t Hwf Hs Htrace Hfinal.
    eapply gamma_derives_of_trace_from; eauto.
  Qed.

  (** Gamma bridge soundness: if the ENFA accepts [w] from [s], then
      [Gamma(M)] derives [w] from the same start. *)
  Theorem section4_gamma_support_language_sound :
    forall (m : @finite_enfa A) s w,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      enfa_accepts_from m s w ->
      rlg_accepts (gamma_grammar_from m s) w.
  Proof.
    intros m s w Hwf Hs [q [t [Htrace [Hword Hfinal]]]].
    unfold rlg_accepts.
    rewrite <- Hword.
    eapply gamma_derives_of_trace; eauto.
  Qed.

  Lemma gamma_trace_of_derivation_from :
    forall (m : @finite_enfa A) root X w,
      rlg_derives_from (gamma_grammar_from m root) X w ->
      enfa_accepts_from m X w.
  Proof.
    intros m root X w Hder.
    induction Hder as [X u Hprod| X u Y v Hprod _ IH].
    - simpl in Hprod.
      apply gamma_none_prod_inv in Hprod as [Hu Hfinal].
      subst u.
      unfold enfa_accepts_from.
      exists X, []. split.
      + constructor.
      + split.
        * reflexivity.
        * apply filter_In in Hfinal as [_ Hfinal]. exact Hfinal.
    - simpl in Hprod.
      apply gamma_some_prod_inv in Hprod as
        [[Hu [_ Hstep]] | [a [Hu [_ [_ Hstep]]]]].
      + subst u.
        unfold enfa_accepts_from in *.
        destruct IH as [q [t [Htrace [Hword Hfinal]]]].
        exists q, (((X, None), Y) :: t).
        split.
        * econstructor; eauto.
        * split.
          -- simpl. exact Hword.
          -- exact Hfinal.
      + subst u.
        unfold enfa_accepts_from in *.
        destruct IH as [q [t [Htrace [Hword Hfinal]]]].
        exists q, (((X, Some a), Y) :: t).
        split.
        * econstructor; eauto.
        * split.
          -- simpl. now rewrite Hword.
          -- exact Hfinal.
  Qed.

  Lemma gamma_trace_of_derivation_valid :
    forall (m : @finite_enfa A) root X d t,
      rlg_derivation_valid (gamma_grammar_from m root) X d None ->
      gamma_trace_of_derivation m root d = Some t ->
      exists q,
        valid_trace m X t q /\
        trace_word t = rlg_derivation_word (gamma_grammar_from m root) d /\
        enfa_final (fenfa_base m) q = true.
  Proof.
    intros m root X d t Hvalid.
    revert t.
    induction Hvalid as [X u Hprod| X u Y d tail Hprod _ IH];
      intros t Htrace.
    - simpl in Htrace.
      apply gamma_none_prod_inv in Hprod as [Hu Hfinal].
      subst u.
      inversion Htrace; subst.
      exists X. split.
      + constructor.
      + split.
        * reflexivity.
        * apply filter_In in Hfinal as [_ Hfinal]. exact Hfinal.
    - simpl in Htrace.
      destruct (gamma_label_of_word u) as [l|] eqn:Hlabel; try discriminate.
      destruct (gamma_trace_of_derivation m root d) as [t'|] eqn:Ht';
        try discriminate.
      inversion Htrace; subst.
      specialize (IH t' eq_refl) as [q [Hvalid_t [Hword Hfinal]]].
      apply gamma_some_prod_inv in Hprod as
        [[Hu [_ Hstep]] | [a [Hu [_ [_ Hstep]]]]].
      + subst u. simpl in Hlabel. inversion Hlabel; subst l.
        exists q. repeat split.
        * econstructor; eauto.
        * simpl. exact Hword.
        * exact Hfinal.
      + subst u. simpl in Hlabel. inversion Hlabel; subst l.
        exists q. repeat split.
        * econstructor; eauto.
        * simpl. now rewrite Hword.
        * exact Hfinal.
  Qed.

  Lemma gamma_trace_of_valid_derivation_some :
    forall (m : @finite_enfa A) root X d,
      rlg_derivation_valid (gamma_grammar_from m root) X d None ->
      exists t, gamma_trace_of_derivation m root d = Some t.
  Proof.
    intros m root X d Hvalid.
    induction Hvalid as [X u Hprod| X u Y d tail Hprod _ IH].
    - apply gamma_none_prod_inv in Hprod as [Hu _].
      subst u. exists []. reflexivity.
    - destruct IH as [t Ht].
      apply gamma_some_prod_inv in Hprod as
        [[Hu [_ _]] | [a [Hu [_ [_ _]]]]].
      + subst u. exists (((X, None), Y) :: t).
        simpl. rewrite Ht. reflexivity.
      + subst u. exists (((X, Some a), Y) :: t).
        simpl. rewrite Ht. reflexivity.
  Qed.

  Lemma gamma_trace_of_valid_prefix_derivation_some :
    forall (m : @finite_enfa A) root X d Y,
      rlg_prefix_derivation_valid (gamma_grammar_from m root) X d Y ->
      exists t, gamma_trace_of_prefix_derivation m root d = Some t.
  Proof.
    intros m root X d Y Hvalid.
    induction Hvalid as [X| X u Y d Z Hprod _ IH].
    - exists []. reflexivity.
    - destruct IH as [t Ht].
      apply gamma_some_prod_inv in Hprod as
        [[Hu [_ _]] | [a [Hu [_ [_ _]]]]].
      + subst u. exists (((X, None), Y) :: t).
        simpl. rewrite Ht. reflexivity.
      + subst u. exists (((X, Some a), Y) :: t).
        simpl. rewrite Ht. reflexivity.
  Qed.

  Lemma gamma_trace_of_prefix_derivation_valid :
    forall (m : @finite_enfa A) root X d Y t,
      rlg_prefix_derivation_valid (gamma_grammar_from m root) X d Y ->
      gamma_trace_of_prefix_derivation m root d = Some t ->
      valid_trace m X t Y /\
      trace_word t = rlg_prefix_derivation_word (gamma_grammar_from m root) d.
  Proof.
    intros m root X d Y t Hvalid.
    revert t.
    induction Hvalid as [X| X u Y d Z Hprod _ IH]; intros t Ht.
    - simpl in Ht. inversion Ht; subst. split; constructor.
    - simpl in Ht.
      destruct (gamma_label_of_word u) as [l|] eqn:Hlabel; try discriminate.
      destruct (gamma_trace_of_prefix_derivation m root d) as [t'|] eqn:Ht';
        try discriminate.
      inversion Ht; subst.
      specialize (IH t' eq_refl) as [Hvalid_t Hword].
      apply gamma_some_prod_inv in Hprod as
        [[Hu [_ Hstep]] | [a [Hu [_ [_ Hstep]]]]].
      + subst u. simpl in Hlabel. inversion Hlabel; subst l.
        split.
        * econstructor; eauto.
        * simpl. exact Hword.
      + subst u. simpl in Hlabel. inversion Hlabel; subst l.
        split.
        * econstructor; eauto.
        * simpl. now rewrite Hword.
  Qed.

  Lemma gamma_prefix_derivation_of_trace_of_valid_prefix_derivation :
    forall (m : @finite_enfa A) root X d Y t,
      rlg_prefix_derivation_valid (gamma_grammar_from m root) X d Y ->
      gamma_trace_of_prefix_derivation m root d = Some t ->
      gamma_prefix_derivation_of_trace m root t = d /\
      valid_trace m X t Y /\
      trace_word t =
        rlg_prefix_derivation_word (gamma_grammar_from m root) d.
  Proof.
    intros m root X d Y t Hvalid.
    revert t.
    induction Hvalid as [X| X u Y d Z Hprod _ IH]; intros t Ht.
    - simpl in Ht. inversion Ht; subst. repeat split; constructor.
    - simpl in Ht.
      destruct (gamma_label_of_word u) as [l|] eqn:Hlabel; try discriminate.
      destruct (gamma_trace_of_prefix_derivation m root d) as [t'|] eqn:Ht';
        try discriminate.
      inversion Ht; subst.
      apply gamma_some_prod_inv in Hprod as
        [[Hu [_ Hstep]] | [a [Hu [_ [_ Hstep]]]]].
      + subst u. simpl in Hlabel. inversion Hlabel; subst l.
        destruct (IH t' eq_refl) as [Hround [Hvalid_t Hword]].
        repeat split.
        * simpl. now rewrite Hround.
        * econstructor; eauto.
        * simpl. exact Hword.
      + subst u. simpl in Hlabel. inversion Hlabel; subst l.
        destruct (IH t' eq_refl) as [Hround [Hvalid_t Hword]].
        repeat split.
        * simpl. now rewrite Hround.
        * econstructor; eauto.
        * simpl. now rewrite Hword.
  Qed.

  Theorem section4_gamma_support_valid_derivation_to_trace :
    forall (m : @finite_enfa A) root X d,
      rlg_derivation_valid (gamma_grammar_from m root) X d None ->
      exists q t,
        gamma_trace_of_derivation m root d = Some t /\
        valid_trace m X t q /\
        trace_word t =
          rlg_derivation_word (gamma_grammar_from m root) d /\
        enfa_final (fenfa_base m) q = true.
  Proof.
    intros m root X d Hvalid.
    destruct (gamma_trace_of_valid_derivation_some m root X d Hvalid)
      as [t Ht].
    destruct (gamma_trace_of_derivation_valid m root X d t Hvalid Ht)
      as [q [Htrace [Hword Hfinal]]].
    exists q, t. repeat split; auto.
  Qed.

  Lemma gamma_derivation_of_trace_of_valid_derivation :
    forall (m : @finite_enfa A) root X d t,
      rlg_derivation_valid (gamma_grammar_from m root) X d None ->
      gamma_trace_of_derivation m root d = Some t ->
      exists q,
        gamma_derivation_of_trace m root t q = d /\
        valid_trace m X t q /\
        trace_word t =
          rlg_derivation_word (gamma_grammar_from m root) d /\
        enfa_final (fenfa_base m) q = true.
  Proof.
    intros m root X d t Hvalid.
    revert t.
    induction Hvalid as [X u Hprod| X u Y d tail Hprod _ IH];
      intros t Htrace.
    - simpl in Htrace.
      apply gamma_none_prod_inv in Hprod as [Hu Hfinal].
      subst u.
      inversion Htrace; subst.
      exists X. split.
      + reflexivity.
      + split.
        * constructor.
        * split.
          -- reflexivity.
          -- apply filter_In in Hfinal as [_ Hfinal]. exact Hfinal.
    - simpl in Htrace.
      destruct (gamma_label_of_word u) as [l|] eqn:Hlabel; try discriminate.
      destruct (gamma_trace_of_derivation m root d) as [t'|] eqn:Ht';
        try discriminate.
      inversion Htrace; subst.
      apply gamma_some_prod_inv in Hprod as
        [[Hu [_ Hstep]] | [a [Hu [_ [_ Hstep]]]]].
      + subst u. simpl in Hlabel. inversion Hlabel; subst l.
        destruct (IH t' eq_refl) as
          [q [Hround [Hvalid_t [Hword Hfinal]]]].
        exists q. split.
        * simpl. now rewrite Hround.
        * split.
          -- econstructor; eauto.
          -- split.
             ++ simpl. exact Hword.
             ++ exact Hfinal.
      + subst u. simpl in Hlabel. inversion Hlabel; subst l.
        destruct (IH t' eq_refl) as
          [q [Hround [Hvalid_t [Hword Hfinal]]]].
        exists q. split.
        * simpl. now rewrite Hround.
        * split.
          -- econstructor; eauto.
          -- split.
             ++ simpl. now rewrite Hword.
             ++ exact Hfinal.
  Qed.

  Theorem section4_gamma_support_valid_derivation_epsilon_simple :
    forall (m : @finite_enfa A) root X d t,
      rlg_derivation_valid (gamma_grammar_from m root) X d None ->
      gamma_trace_of_derivation m root d = Some t ->
      rlg_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        X d =
      epsilon_simpleb m (X, t).
  Proof.
    intros m root X d t Hvalid Ht.
    destruct
      (gamma_derivation_of_trace_of_valid_derivation
         m root X d t Hvalid Ht)
      as [q [Hround _]].
    rewrite <- Hround.
    apply section4_gamma_support_trace_derivation_epsilon_simple.
  Qed.

  Theorem section4_gamma_support_valid_derivation_maximal_epsilon_simple :
    forall (m : @finite_enfa A) root X d t,
      finite_enfa_wf m ->
      In X (fenfa_states m) ->
      rlg_derivation_valid (gamma_grammar_from m root) X d None ->
      gamma_trace_of_derivation m root d = Some t ->
      rlg_maximal_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        X d = true ->
      maximal_epsilon_simpleb m (X, t) = true.
  Proof.
    intros m root X d t Hwf HX Hvalid Ht Hmax.
    destruct
      (gamma_derivation_of_trace_of_valid_derivation
         m root X d t Hvalid Ht)
      as [q [Hround [Htrace _]]].
    rewrite <- Hround in Hmax.
    eapply section4_gamma_support_trace_derivation_maximal_epsilon_simple_complete;
      eauto.
  Qed.

  Theorem section4_gamma_support_valid_prefix_derivation_epsilon_simple :
    forall (m : @finite_enfa A) root X d Y t,
      rlg_prefix_derivation_valid (gamma_grammar_from m root) X d Y ->
      gamma_trace_of_prefix_derivation m root d = Some t ->
      rlg_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        X d =
      epsilon_simpleb m (X, t).
  Proof.
    intros m root X d Y t Hvalid Ht.
    destruct
      (gamma_prefix_derivation_of_trace_of_valid_prefix_derivation
         m root X d Y t Hvalid Ht)
      as [Hround _].
    rewrite <- Hround.
    apply section4_gamma_support_prefix_trace_derivation_epsilon_simple.
  Qed.

  Theorem section4_gamma_support_valid_prefix_derivation_maximal_epsilon_simple :
    forall (m : @finite_enfa A) root X d Y t,
      finite_enfa_wf m ->
      In X (fenfa_states m) ->
      rlg_prefix_derivation_valid (gamma_grammar_from m root) X d Y ->
      gamma_trace_of_prefix_derivation m root d = Some t ->
      rlg_maximal_epsilon_simpleb
        (gamma_grammar_from m root)
        (fenfa_state_eqb m)
        X d = true ->
      maximal_epsilon_simpleb m (X, t) = true.
  Proof.
    intros m root X d Y t Hwf HX Hvalid Ht Hmax.
    destruct
      (gamma_prefix_derivation_of_trace_of_valid_prefix_derivation
         m root X d Y t Hvalid Ht)
      as [Hround [Htrace _]].
    rewrite <- Hround in Hmax.
    eapply section4_gamma_support_prefix_trace_derivation_maximal_epsilon_simple_complete;
      eauto.
  Qed.

  Theorem section4_gamma_support_trace_derivation_roundtrip :
    forall (m : @finite_enfa A) root p q t,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      valid_trace m p t q ->
      enfa_final (fenfa_base m) q = true ->
      gamma_trace_of_derivation m root
        (gamma_derivation_of_trace m root t q) = Some t /\
      rlg_derivation_valid
        (gamma_grammar_from m root)
        p
        (gamma_derivation_of_trace m root t q)
        None.
  Proof.
    intros m root p q t Hwf Hp Htrace Hfinal.
    split.
    - apply gamma_trace_of_derivation_of_trace.
    - eapply gamma_derivation_of_trace_valid_from; eauto.
  Qed.

  (** Language-equivalence part of the Gamma bridge.  The sound and complete
      directions show that ENFA acceptance of [w] from [s] is equivalent to
      acceptance by [Gamma(M)]. *)
  Theorem section4_gamma_support_language_complete :
    forall (m : @finite_enfa A) s w,
      rlg_accepts (gamma_grammar_from m s) w ->
      enfa_accepts_from m s w.
  Proof.
    intros m s w H.
    unfold rlg_accepts in H.
    now apply gamma_trace_of_derivation_from in H.
  Qed.

  Theorem section4_gamma_support_language_equiv :
    forall (m : @finite_enfa A) s w,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      enfa_accepts_from m s w <->
      rlg_accepts (gamma_grammar_from m s) w.
  Proof.
    intros m s w Hwf Hs. split.
    - now apply section4_gamma_support_language_sound.
    - intros H. now apply section4_gamma_support_language_complete.
  Qed.

  (** Prime trace/derivation bridge for Gamma.  These theorems connect ENFA
      prime accepting, reach, and leaf traces with Gamma RLG prime derivations;
      later ambiguity-preservation and UFA/ReachUFA/LeafUFA bridges use them as
      their core interface. *)
  Theorem section4_gamma_support_prime_accepting_derivation_of_trace :
    forall (m : @finite_enfa A) s q t w,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s t q ->
      trace_word t = w ->
      enfa_final (fenfa_base m) q = true ->
      epsilon_simpleb m (s, t) = true ->
      enfa_accepting_maximal_epsilon_simpleb m (s, t) = true ->
      rlg_derivation_accepting_prime
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        w
        (gamma_derivation_of_trace m s t q).
  Proof.
    intros m s q t w Hwf Hs Htrace Hword Hfinal Hsimple Hmax.
    pose proof
      (section4_gamma_accepting_maximal_reflects m s Hwf Hs) as Hreflect.
    repeat split.
    - eapply gamma_derivation_of_trace_valid; eauto.
    - now rewrite gamma_derivation_of_trace_word.
    - rewrite section4_gamma_support_trace_derivation_epsilon_simple.
      exact Hsimple.
    - apply (proj1 (Hreflect q t w Htrace Hword Hfinal Hsimple)).
      exact Hmax.
  Qed.

  Theorem section4_gamma_support_prime_accepting_trace_of_derivation :
    forall (m : @finite_enfa A) s w d,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      rlg_derivation_accepting_prime
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        w d ->
      exists q t,
        gamma_trace_of_derivation m s d = Some t /\
        valid_trace m s t q /\
        trace_word t = w /\
        enfa_final (fenfa_base m) q = true /\
        epsilon_simpleb m (s, t) = true /\
        enfa_accepting_maximal_epsilon_simpleb m (s, t) = true.
  Proof.
    intros m s w d Hwf Hs [[Hvalid Hword] [Hsimple Hmax]].
    pose proof
      (section4_gamma_accepting_maximal_reflects m s Hwf Hs) as Hreflect.
    destruct (section4_gamma_support_valid_derivation_to_trace
                m s s d Hvalid)
      as [q [t [Ht [Htrace [Htrace_word Hfinal]]]]].
    exists q, t.
    split; [exact Ht |].
    split; [exact Htrace |].
    split.
    - now rewrite Htrace_word.
    - split; [exact Hfinal |].
      split.
      + replace (epsilon_simpleb m (s, t)) with
          (rlg_epsilon_simpleb
             (gamma_grammar_from m s) (fenfa_state_eqb m) s d).
        exact Hsimple.
        pose proof
          (section4_gamma_support_valid_derivation_epsilon_simple
             m s s d t Hvalid Ht) as Heq.
        exact Heq.
      + destruct
          (gamma_derivation_of_trace_of_valid_derivation
             m s s d t Hvalid Ht)
          as [q' [Hround [Htrace' _]]].
        assert (q' = q).
        {
          pose proof (valid_trace_trace_end m s t q' Htrace') as Hq'.
          pose proof (valid_trace_trace_end m s t q Htrace) as Hq.
          congruence.
        }
        subst q'.
        rewrite <- Hround in Hmax.
        assert (Hword_t : trace_word t = w).
        { now rewrite Htrace_word. }
        assert (Hsimple_t : epsilon_simpleb m (s, t) = true).
        {
          replace (epsilon_simpleb m (s, t)) with
            (rlg_epsilon_simpleb
               (gamma_grammar_from m s) (fenfa_state_eqb m) s d).
          - exact Hsimple.
          - pose proof
              (section4_gamma_support_valid_derivation_epsilon_simple
                 m s s d t Hvalid Ht) as Heq.
            exact Heq.
        }
        apply (proj2 (Hreflect q t w Htrace Hword_t Hfinal Hsimple_t)).
        exact Hmax.
  Qed.

  Theorem section4_gamma_support_prime_reach_derivation_of_trace :
    forall (m : @finite_enfa A) s q t w,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s t q ->
      trace_word t = w ->
      epsilon_simpleb m (s, t) = true ->
      rlg_prefix_derivation_prime_reaches
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        w
        q
        (gamma_prefix_derivation_of_trace m s t).
  Proof.
    intros m s q t w Hwf Hs Htrace Hword Hsimple.
    repeat split.
    - eapply gamma_prefix_derivation_of_trace_valid_from; eauto.
    - now rewrite gamma_prefix_derivation_of_trace_word.
    - rewrite section4_gamma_support_prefix_trace_derivation_epsilon_simple.
      exact Hsimple.
  Qed.

  Theorem section4_gamma_support_prime_reach_trace_of_derivation :
    forall (m : @finite_enfa A) s w q d,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      rlg_prefix_derivation_prime_reaches
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        w q d ->
      exists t,
        gamma_trace_of_prefix_derivation m s d = Some t /\
        valid_trace m s t q /\
        trace_word t = w /\
        epsilon_simpleb m (s, t) = true.
  Proof.
    intros m s w q d Hwf Hs [Hvalid [Hword Hsimple]].
    destruct
      (gamma_trace_of_valid_prefix_derivation_some
         m s s d q Hvalid) as [t Ht].
    destruct
      (gamma_trace_of_prefix_derivation_valid
         m s s d q t Hvalid Ht) as [Htrace Htrace_word].
    exists t. repeat split; auto.
    - now rewrite Htrace_word.
    - replace (epsilon_simpleb m (s, t)) with
        (rlg_epsilon_simpleb
           (gamma_grammar_from m s) (fenfa_state_eqb m) s d).
      exact Hsimple.
      pose proof
        (section4_gamma_support_valid_prefix_derivation_epsilon_simple
           m s s d q t Hvalid Ht) as Heq.
      exact Heq.
  Qed.

  Theorem section4_gamma_support_prime_leaf_derivation_of_trace :
    forall (m : @finite_enfa A) s q t prefix,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s t q ->
      trace_word t = prefix ->
      epsilon_simpleb m (s, t) = true ->
      maximal_epsilon_simpleb m (s, t) = true ->
      rlg_prefix_derivation_prime_leaf
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        prefix
        (gamma_prefix_derivation_of_trace m s t).
  Proof.
    intros m s q t prefix Hwf Hs Htrace Hword Hsimple Hmax.
    exists q. split.
    - eapply section4_gamma_support_prime_reach_derivation_of_trace; eauto.
    - eapply section4_gamma_support_prefix_trace_derivation_maximal_epsilon_simple;
        eauto.
  Qed.

  Theorem section4_gamma_support_prime_leaf_trace_of_derivation :
    forall (m : @finite_enfa A) s prefix d,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      rlg_prefix_derivation_prime_leaf
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        prefix d ->
      exists q t,
        gamma_trace_of_prefix_derivation m s d = Some t /\
        valid_trace m s t q /\
        trace_word t = prefix /\
        epsilon_simpleb m (s, t) = true /\
        maximal_epsilon_simpleb m (s, t) = true.
  Proof.
    intros m s prefix d Hwf Hs [q [Hreach Hmax]].
    destruct
      (section4_gamma_support_prime_reach_trace_of_derivation
         m s prefix q d Hwf Hs Hreach)
      as [t [Ht [Htrace [Hword Hsimple]]]].
    exists q, t. repeat split; auto.
    eapply section4_gamma_support_valid_prefix_derivation_maximal_epsilon_simple;
      eauto.
    exact (proj1 Hreach).
  Qed.

  Lemma gamma_final_states_nodup :
    forall (m : @finite_enfa A),
      finite_enfa_wf m ->
      NoDup (enfa_final_states m).
  Proof.
    intros m Hwf.
    unfold enfa_final_states.
    apply NoDup_filter_bool.
    exact (fenfa_states_nodup m Hwf).
  Qed.

  Lemma gamma_started_filter_true :
    forall (m : @finite_enfa A) s w q t,
      valid_trace m s t q ->
      trace_word t = w ->
      epsilon_simpleb m (s, t) = true ->
      maximal_epsilon_simpleb m (s, t) = true ->
      ends_inb m q (s, t) && epsilon_simpleb m (s, t) = true /\
      ((ends_inb m q (s, t) && epsilon_simpleb m (s, t)) &&
       maximal_epsilon_simpleb m (s, t)) = true.
  Proof.
    intros m s w q t Htrace _ Hsimple Hmax.
    pose proof (valid_trace_trace_end m s t q Htrace) as Hend.
    unfold ends_inb, started_end. simpl.
    rewrite Hend.
    rewrite (fenfa_state_eqb_complete m q q eq_refl).
    rewrite Hsimple, Hmax. simpl. auto.
  Qed.

  Lemma gamma_started_accepting_filter_true :
    forall (m : @finite_enfa A) s w q t,
      valid_trace m s t q ->
      trace_word t = w ->
      epsilon_simpleb m (s, t) = true ->
      enfa_accepting_maximal_epsilon_simpleb m (s, t) = true ->
      ends_inb m q (s, t) && epsilon_simpleb m (s, t) = true /\
      ((ends_inb m q (s, t) && epsilon_simpleb m (s, t)) &&
       enfa_accepting_maximal_epsilon_simpleb m (s, t)) = true.
  Proof.
    intros m s w q t Htrace _ Hsimple Hmax.
    pose proof (valid_trace_trace_end m s t q Htrace) as Hend.
    unfold ends_inb, started_end. simpl.
    rewrite Hend.
    rewrite (fenfa_state_eqb_complete m q q eq_refl).
    rewrite Hsimple, Hmax. simpl. auto.
  Qed.

  (** Gamma bridge between Definition 6 and Definitions 8/9.  The six
      directions relate ENFA [UFA], [ReachUFA], and [LeafUFA] to prime
      unambiguity, reach-unambiguity, and leaf-unambiguity of [Gamma(M)].
      The finite-enumeration hypotheses are listed in the statements:
      [finite_enfa_wf m], single start [enfa_start = [s]],
      [enfa_prime_trace_enumerated_from], and [enfa_started_traces_nodup]. *)
  Lemma gamma_accepting_prime_filter_to_trace :
    forall (m : @finite_enfa A) s word_eqb w
      (d : rlg_derivation (gamma_grammar_from m s)),
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      word_eqb_reflects_eq word_eqb ->
      rlg_derivation_valid (gamma_grammar_from m s) s d None ->
      word_eqb (rlg_derivation_word (gamma_grammar_from m s) d) w = true ->
      rlg_epsilon_simpleb
        (gamma_grammar_from m s) (fenfa_state_eqb m) s d = true ->
      rlg_accepting_maximal_epsilon_simpleb
        (gamma_grammar_from m s) (fenfa_state_eqb m) s d = true ->
      exists q t,
        gamma_derivation_of_trace m s t q = d /\
        valid_trace m s t q /\
        trace_word t = w /\
        enfa_final (fenfa_base m) q = true /\
        epsilon_simpleb m (s, t) = true /\
        enfa_accepting_maximal_epsilon_simpleb m (s, t) = true.
  Proof.
    intros m s word_eqb w d Hwf Hs [Hword_sound _]
      Hvalid Hword Hsimple Hmax.
    pose proof
      (section4_gamma_accepting_maximal_reflects m s Hwf Hs) as Hreflect.
    destruct
      (gamma_trace_of_valid_derivation_some m s s d Hvalid)
      as [t Ht].
    destruct
      (gamma_derivation_of_trace_of_valid_derivation
         m s s d t Hvalid Ht)
      as [q [Hround [Htrace [Htrace_word Hfinal]]]].
    exists q, t.
    split; [exact Hround |].
    split; [exact Htrace |].
    split.
    - rewrite Htrace_word. now apply Hword_sound.
    - split; [exact Hfinal |].
      split.
      + replace (epsilon_simpleb m (s, t)) with
          (rlg_epsilon_simpleb
             (gamma_grammar_from m s) (fenfa_state_eqb m) s d).
        * exact Hsimple.
        * pose proof
            (section4_gamma_support_valid_derivation_epsilon_simple
               m s s d t Hvalid Ht) as Heq.
          exact Heq.
      + rewrite <- Hround in Hmax.
        assert (Hword_t : trace_word t = w).
        { rewrite Htrace_word. now apply Hword_sound. }
        assert (Hsimple_t : epsilon_simpleb m (s, t) = true).
        {
          replace (epsilon_simpleb m (s, t)) with
            (rlg_epsilon_simpleb
               (gamma_grammar_from m s) (fenfa_state_eqb m) s d).
          - exact Hsimple.
          - pose proof
              (section4_gamma_support_valid_derivation_epsilon_simple
                 m s s d t Hvalid Ht) as Heq.
            exact Heq.
        }
        apply (proj2 (Hreflect q t w Htrace Hword_t Hfinal Hsimple_t)).
        exact Hmax.
  Qed.

  Theorem section4_lemma3_gamma_da_prime_count_eq_with_enumeration :
    forall (m : @finite_enfa A) s word_eqb w,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      word_eqb_reflects_eq word_eqb ->
      NoDup
        (rlg_derivations_from_fuel
           (gamma_grammar_from m s)
           (fenfa_state_eqb m)
           (S (enfa_trace_bound m w))
           s) ->
      enfa_da_prime_word m w =
      rlg_da_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (S (enfa_trace_bound m w))
        w.
  Proof.
    intros m s word_eqb w Hwf Hstart Henum Hnodup Hwordeq
      Hrlg_nodup.
    destruct Hwordeq as [Hword_sound Hword_complete].
    assert (Hs : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
    }
    pose proof
      (section4_gamma_accepting_maximal_reflects m s Hwf Hs) as Hreflect.
    rewrite <- enfa_da_prime_witnesses_length.
    unfold rlg_da_prime_count.
    set (xs := enfa_da_prime_witnesses m w).
    set (enum :=
      rlg_derivations_from_fuel
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        (S (enfa_trace_bound m w))
        s).
    set (p := fun d =>
      (word_eqb
         (rlg_derivation_word (gamma_grammar_from m s) d) w
       && rlg_epsilon_simpleb
            (gamma_grammar_from m s) (fenfa_state_eqb m) s d)
      && rlg_accepting_maximal_epsilon_simpleb
           (gamma_grammar_from m s) (fenfa_state_eqb m) s d).
    set (f := fun qst : (enfa_state (fenfa_base m) * started_trace m)%type =>
      match qst with
      | (q, (_, t)) => gamma_derivation_of_trace m s t q
      end).
    change (length xs = length (filter p enum)).
    assert (Hxs_nodup : NoDup xs).
    {
      unfold xs, enfa_da_prime_witnesses.
      apply enfa_accepting_prime_witnesses_NoDup.
      - apply gamma_final_states_nodup. exact Hwf.
      - apply Hnodup.
    }
    assert (Hmap_nodup : NoDup (map f xs)).
    {
      apply NoDup_map_injective_in; auto.
      intros [q1 [s1 t1]] [q2 [s2 t2]] Hx1 Hx2 Heq.
      unfold f in Heq. simpl in Heq.
      unfold xs, enfa_da_prime_witnesses in Hx1, Hx2.
      apply enfa_accepting_prime_witnesses_In in Hx1 as
        [_ [Hin1 _]].
      apply enfa_accepting_prime_witnesses_In in Hx2 as
        [_ [Hin2 _]].
      apply gamma_derivation_of_trace_injective in Heq as [Ht Hq].
      pose proof (started_traces_start_in m w s1 t1 Hin1) as Hs1.
      pose proof (started_traces_start_in m w s2 t2 Hin2) as Hs2.
      rewrite Hstart in Hs1, Hs2. simpl in Hs1, Hs2.
      destruct Hs1 as [Hs1 | []].
      destruct Hs2 as [Hs2 | []].
      subst. reflexivity.
    }
    assert (Hrlg_filter_nodup : NoDup (filter p enum)).
    {
      apply NoDup_filter_bool.
      unfold enum. exact Hrlg_nodup.
    }
    assert (Hto : incl (map f xs) (filter p enum)).
    {
      intros z Hz.
      apply in_map_iff in Hz as [[q [s0 t]] [Hz Hx]].
      subst z.
      apply filter_In.
      unfold xs, enfa_da_prime_witnesses in Hx.
      apply enfa_accepting_prime_witnesses_In in Hx as
        [Hqfinal [Hin Hfilter]].
      apply andb_true_iff in Hfilter as [Hfilter Haccmax].
      apply andb_true_iff in Hfilter as [Hend Hsimple].
      unfold ends_inb, started_end in Hend. simpl in Hend.
      apply fenfa_state_eqb_sound in Hend.
      destruct (started_traces_valid m w s0 t Hin) as [Htrace Htrace_word].
      pose proof (started_traces_start_in m w s0 t Hin) as Hs0.
      rewrite Hstart in Hs0. simpl in Hs0.
      destruct Hs0 as [Hs0 | []]. subst s0.
      rewrite Hend in Htrace.
      apply filter_In in Hqfinal as [_ Hfinal].
      split.
      - unfold f. simpl.
        unfold enum.
        eapply rlg_derivations_from_fuel_complete.
        + intros x y Hxy. apply fenfa_state_eqb_complete. exact Hxy.
        + eapply gamma_derivation_of_trace_valid; eauto.
        + rewrite gamma_derivation_of_trace_length.
          pose proof (started_traces_length_bound m w s t Hin) as Hlen.
          lia.
      - unfold p, f. simpl.
        apply andb_true_iff. split.
        + apply andb_true_iff. split.
          * apply Hword_complete.
            now rewrite gamma_derivation_of_trace_word.
          * rewrite section4_gamma_support_trace_derivation_epsilon_simple.
            exact Hsimple.
        + apply (proj1 (Hreflect q t w Htrace Htrace_word Hfinal Hsimple)).
          exact Haccmax.
    }
    assert (Hfrom : incl (filter p enum) (map f xs)).
    {
      intros d Hd_filter.
      apply filter_In in Hd_filter as [Hd Hp].
      unfold p in Hp.
      apply andb_true_iff in Hp as [Hp Haccmax].
      apply andb_true_iff in Hp as [Hword Hsimple].
      pose proof
        (rlg_derivations_from_fuel_valid
           (gamma_grammar_from m s) (fenfa_state_eqb m)
           (fun x y Hxy => fenfa_state_eqb_sound m x y Hxy)
           (S (enfa_trace_bound m w)) s d Hd)
        as Hvalid_derivation.
      destruct
        (section4_gamma_support_valid_derivation_to_trace
           m s s d Hvalid_derivation)
        as [q [t [Ht [Htrace [Htrace_word Hfinal]]]]].
      destruct
        (gamma_derivation_of_trace_of_valid_derivation
           m s s d t Hvalid_derivation Ht)
        as [q' [Hround [Htrace' _]]].
      assert (q' = q).
      {
        pose proof (valid_trace_trace_end m s t q' Htrace') as Hq'.
        pose proof (valid_trace_trace_end m s t q Htrace) as Hq.
        congruence.
      }
      subst q'.
      assert (Htrace_word_w : trace_word t = w).
      { rewrite Htrace_word. now apply Hword_sound. }
      assert (HsimpleE : epsilon_simpleb m (s, t) = true).
      {
        replace (epsilon_simpleb m (s, t)) with
          (rlg_epsilon_simpleb
             (gamma_grammar_from m s) (fenfa_state_eqb m) s d).
        - exact Hsimple.
        - pose proof
            (section4_gamma_support_valid_derivation_epsilon_simple
               m s s d t Hvalid_derivation Ht) as Heq.
          exact Heq.
      }
      assert (HmaxE : enfa_accepting_maximal_epsilon_simpleb m (s, t) = true).
      {
        rewrite <- Hround in Haccmax.
        apply (proj2 (Hreflect q t w Htrace Htrace_word_w Hfinal HsimpleE)).
        exact Haccmax.
      }
      assert (Hin : In (s, t) (started_traces m w)).
      { eapply Henum; eauto. }
      assert (Hqstate : In q (fenfa_states m)).
      { eapply finite_enfa_wf_valid_trace_end_in_states; eauto. }
      assert (Hqfinal : In q (enfa_final_states m)).
      { unfold enfa_final_states. apply filter_In. split; auto. }
      apply in_map_iff.
      exists (q, (s, t)). split.
      - unfold f. simpl. exact Hround.
      - unfold xs, enfa_da_prime_witnesses.
        apply enfa_accepting_prime_witnesses_In.
        repeat split; auto.
        destruct
          (gamma_started_accepting_filter_true
             m s w q t Htrace Htrace_word_w HsimpleE HmaxE)
          as [_ Hf].
        exact Hf.
    }
    assert (Hle1 : length (map f xs) <= length (filter p enum)).
    { eapply NoDup_incl_length; eauto. }
    assert (Hle2 : length (filter p enum) <= length (map f xs)).
    { eapply NoDup_incl_length; eauto. }
    rewrite length_map in Hle1, Hle2.
    lia.
  Qed.

  Theorem section4_lemma3_gamma_dra_prime_count_eq_with_enumeration :
    forall (m : @finite_enfa A) s word_eqb w q,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      word_eqb_reflects_eq word_eqb ->
      NoDup
        (rlg_prefix_derivations_from_fuel
           (gamma_grammar_from m s)
           (fenfa_state_eqb m)
           (enfa_trace_bound m w)
           s) ->
      enfa_dra_prime_at m w q =
      rlg_dra_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (enfa_trace_bound m w)
        w
        q.
  Proof.
    intros m s word_eqb w q Hwf Hstart Henum Hnodup
      Hwordeq Hrlg_nodup.
    destruct Hwordeq as [Hword_sound Hword_complete].
    assert (Hs : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
    }
    unfold enfa_dra_prime_at, rlg_dra_prime_count.
    set (xs :=
      filter
        (fun st => ends_inb m q st && epsilon_simpleb m st)
        (started_traces m w)).
    set (enum :=
      rlg_prefix_derivations_from_fuel
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        (enfa_trace_bound m w)
        s).
    set (p := fun d =>
      (word_eqb (rlg_prefix_derivation_word (gamma_grammar_from m s) d) w
       && fenfa_state_eqb m
            (rlg_derivation_end (gamma_grammar_from m s) s d) q)
      && rlg_epsilon_simpleb
           (gamma_grammar_from m s) (fenfa_state_eqb m) s d).
    set (f := fun st : started_trace m =>
      match st with
      | (_, t) => gamma_prefix_derivation_of_trace m s t
      end).
    change (length xs = length (filter p enum)).
    assert (Hxs_nodup : NoDup xs).
    {
      unfold xs.
      apply NoDup_filter_bool.
      apply Hnodup.
    }
    assert (Hmap_nodup : NoDup (map f xs)).
    {
      apply NoDup_map_injective_in; auto.
      intros [s1 t1] [s2 t2] Hx1 Hx2 Heq.
      unfold f in Heq. simpl in Heq.
      apply gamma_prefix_derivation_of_trace_injective in Heq.
      unfold xs in Hx1, Hx2.
      apply filter_In in Hx1 as [Hin1 _].
      apply filter_In in Hx2 as [Hin2 _].
      pose proof (started_traces_start_in m w s1 t1 Hin1) as Hs1.
      pose proof (started_traces_start_in m w s2 t2 Hin2) as Hs2.
      rewrite Hstart in Hs1, Hs2. simpl in Hs1, Hs2.
      destruct Hs1 as [Hs1 | []].
      destruct Hs2 as [Hs2 | []].
      subst. reflexivity.
    }
    assert (Hrlg_filter_nodup : NoDup (filter p enum)).
    {
      apply NoDup_filter_bool.
      unfold enum. exact Hrlg_nodup.
    }
    assert (Hto : incl (map f xs) (filter p enum)).
    {
      intros z Hz.
      apply in_map_iff in Hz as [[s0 t] [Hz Hx]].
      subst z.
      apply filter_In.
      unfold xs in Hx.
      apply filter_In in Hx as [Hin Hfilter].
      apply andb_true_iff in Hfilter as [Hend Hsimple].
      unfold ends_inb, started_end in Hend. simpl in Hend.
      apply fenfa_state_eqb_sound in Hend.
      destruct (started_traces_valid m w s0 t Hin) as [Htrace Htrace_word].
      pose proof (started_traces_start_in m w s0 t Hin) as Hs0.
      rewrite Hstart in Hs0. simpl in Hs0.
      destruct Hs0 as [Hs0 | []]. subst s0.
      rewrite Hend in Htrace.
      split.
      - unfold f. simpl.
        unfold enum.
        eapply rlg_prefix_derivations_from_fuel_complete.
        + intros x y Hxy. apply fenfa_state_eqb_complete. exact Hxy.
        + eapply gamma_prefix_derivation_of_trace_valid_from; eauto.
        + rewrite gamma_prefix_derivation_of_trace_length.
          pose proof (started_traces_length_bound m w s t Hin) as Hlen.
          exact Hlen.
      - unfold p, f. simpl.
        apply andb_true_iff. split.
        + apply andb_true_iff. split.
          * apply Hword_complete.
            now rewrite gamma_prefix_derivation_of_trace_word.
          * rewrite (gamma_prefix_derivation_of_trace_end_valid
                       m s s t q Htrace).
            apply fenfa_state_eqb_complete. reflexivity.
        + rewrite section4_gamma_support_prefix_trace_derivation_epsilon_simple.
          exact Hsimple.
    }
    assert (Hfrom : incl (filter p enum) (map f xs)).
    {
      intros d Hd_filter.
      apply filter_In in Hd_filter as [Hd Hp].
      unfold p in Hp.
      apply andb_true_iff in Hp as [Hp Hsimple].
      apply andb_true_iff in Hp as [Hword Hend].
      apply fenfa_state_eqb_sound in Hend.
      destruct
        (rlg_prefix_derivations_from_fuel_valid
           (gamma_grammar_from m s) (fenfa_state_eqb m)
           (fun x y Hxy => fenfa_state_eqb_sound m x y Hxy)
           (enfa_trace_bound m w) s d Hd)
        as [Y Hvalid_prefix].
      pose proof
        (rlg_prefix_derivation_valid_end
           (gamma_grammar_from m s) s d Y Hvalid_prefix)
        as HY.
      rewrite HY in Hend. subst Y.
      assert (Hprime :
        rlg_prefix_derivation_prime_reaches
          (gamma_grammar_from m s)
          (fenfa_state_eqb m)
          w q d).
      {
        repeat split.
        - exact Hvalid_prefix.
        - now apply Hword_sound.
        - exact Hsimple.
      }
      destruct
        (section4_gamma_support_prime_reach_trace_of_derivation
           m s w q d Hwf Hs Hprime)
        as [t [Ht [Htrace [Htrace_word_w HsimpleE]]]].
      destruct
        (gamma_prefix_derivation_of_trace_of_valid_prefix_derivation
           m s s d q t Hvalid_prefix Ht)
        as [Hround _].
      assert (Hin : In (s, t) (started_traces m w)).
      { eapply Henum; eauto. }
      apply in_map_iff.
      exists (s, t). split.
      - unfold f. simpl. exact Hround.
      - unfold xs.
        apply filter_In. split; [exact Hin |].
        apply andb_true_iff. split.
        + pose proof (valid_trace_trace_end m s t q Htrace) as Htrace_end.
          unfold ends_inb, started_end. simpl.
          rewrite Htrace_end.
          apply fenfa_state_eqb_complete. reflexivity.
        + exact HsimpleE.
    }
    assert (Hle1 : length (map f xs) <= length (filter p enum)).
    { eapply NoDup_incl_length; eauto. }
    assert (Hle2 : length (filter p enum) <= length (map f xs)).
    { eapply NoDup_incl_length; eauto. }
    rewrite length_map in Hle1, Hle2.
    lia.
  Qed.

  Theorem section4_lemma3_gamma_leaf_prime_count_eq_with_enumeration :
    forall (m : @finite_enfa A) s word_eqb w,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      word_eqb_reflects_eq word_eqb ->
      NoDup
        (rlg_prefix_derivations_from_fuel
           (gamma_grammar_from m s)
           (fenfa_state_eqb m)
           (enfa_trace_bound m w)
           s) ->
      enfa_leaf_prime_word m w =
      rlg_prefix_leaf_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (enfa_trace_bound m w)
        w.
  Proof.
    intros m s word_eqb w Hwf Hstart Henum Hnodup
      Hwordeq Hrlg_nodup.
    destruct Hwordeq as [Hword_sound Hword_complete].
    assert (Hs : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
    }
    rewrite <- enfa_leaf_prime_witnesses_length.
    unfold rlg_prefix_leaf_prime_count.
    set (xs := enfa_leaf_prime_witnesses m w).
    set (enum :=
      rlg_prefix_derivations_from_fuel
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        (enfa_trace_bound m w)
        s).
    set (p := fun d =>
      (word_eqb (rlg_prefix_derivation_word (gamma_grammar_from m s) d) w
       && rlg_epsilon_simpleb
            (gamma_grammar_from m s) (fenfa_state_eqb m) s d)
      && rlg_maximal_epsilon_simpleb
           (gamma_grammar_from m s) (fenfa_state_eqb m) s d).
    set (f := fun qst : (enfa_state (fenfa_base m) * started_trace m)%type =>
      match qst with
      | (_, (_, t)) => gamma_prefix_derivation_of_trace m s t
      end).
    change (length xs = length (filter p enum)).
    assert (Hxs_nodup : NoDup xs).
    {
      unfold xs, enfa_leaf_prime_witnesses.
      apply enfa_prime_maximal_witnesses_NoDup.
      - apply fenfa_states_nodup. exact Hwf.
      - apply Hnodup.
    }
    assert (Hmap_nodup : NoDup (map f xs)).
    {
      apply NoDup_map_injective_in; auto.
      intros [q1 [s1 t1]] [q2 [s2 t2]] Hx1 Hx2 Heq.
      unfold f in Heq. simpl in Heq.
      apply gamma_prefix_derivation_of_trace_injective in Heq.
      unfold xs, enfa_leaf_prime_witnesses in Hx1, Hx2.
      apply enfa_prime_maximal_witnesses_In in Hx1 as
        [_ [Hin1 Hfilter1]].
      apply enfa_prime_maximal_witnesses_In in Hx2 as
        [_ [Hin2 Hfilter2]].
      apply andb_true_iff in Hfilter1 as [Hfilter1 _].
      apply andb_true_iff in Hfilter1 as [Hend1 _].
      apply andb_true_iff in Hfilter2 as [Hfilter2 _].
      apply andb_true_iff in Hfilter2 as [Hend2 _].
      unfold ends_inb, started_end in Hend1, Hend2.
      simpl in Hend1, Hend2.
      apply fenfa_state_eqb_sound in Hend1.
      apply fenfa_state_eqb_sound in Hend2.
      pose proof (started_traces_start_in m w s1 t1 Hin1) as Hs1.
      pose proof (started_traces_start_in m w s2 t2 Hin2) as Hs2.
      rewrite Hstart in Hs1, Hs2. simpl in Hs1, Hs2.
      destruct Hs1 as [Hs1 | []].
      destruct Hs2 as [Hs2 | []].
      subst s1 s2.
      subst t2.
      congruence.
    }
    assert (Hrlg_filter_nodup : NoDup (filter p enum)).
    {
      apply NoDup_filter_bool.
      unfold enum. exact Hrlg_nodup.
    }
    assert (Hto : incl (map f xs) (filter p enum)).
    {
      intros z Hz.
      apply in_map_iff in Hz as [[q [s0 t]] [Hz Hx]].
      subst z.
      apply filter_In.
      unfold xs, enfa_leaf_prime_witnesses in Hx.
      apply enfa_prime_maximal_witnesses_In in Hx as
        [Hqstate [Hin Hfilter]].
      apply andb_true_iff in Hfilter as [Hfilter Hmax].
      apply andb_true_iff in Hfilter as [Hend Hsimple].
      unfold ends_inb, started_end in Hend. simpl in Hend.
      apply fenfa_state_eqb_sound in Hend.
      destruct (started_traces_valid m w s0 t Hin) as [Htrace Htrace_word].
      pose proof (started_traces_start_in m w s0 t Hin) as Hs0.
      rewrite Hstart in Hs0. simpl in Hs0.
      destruct Hs0 as [Hs0 | []]. subst s0.
      rewrite Hend in Htrace.
      split.
      - unfold f. simpl.
        unfold enum.
        eapply rlg_prefix_derivations_from_fuel_complete.
        + intros x y Hxy. apply fenfa_state_eqb_complete. exact Hxy.
        + eapply gamma_prefix_derivation_of_trace_valid_from; eauto.
        + rewrite gamma_prefix_derivation_of_trace_length.
          pose proof (started_traces_length_bound m w s t Hin) as Hlen.
          exact Hlen.
      - unfold p, f. simpl.
        apply andb_true_iff. split.
        + apply andb_true_iff. split.
          * apply Hword_complete.
            now rewrite gamma_prefix_derivation_of_trace_word.
          * rewrite section4_gamma_support_prefix_trace_derivation_epsilon_simple.
            exact Hsimple.
        + eapply section4_gamma_support_prefix_trace_derivation_maximal_epsilon_simple;
            eauto.
    }
    assert (Hfrom : incl (filter p enum) (map f xs)).
    {
      intros d Hd_filter.
      apply filter_In in Hd_filter as [Hd Hp].
      unfold p in Hp.
      apply andb_true_iff in Hp as [Hp Hmax].
      apply andb_true_iff in Hp as [Hword Hsimple].
      destruct
        (rlg_prefix_derivations_from_fuel_valid
           (gamma_grammar_from m s) (fenfa_state_eqb m)
           (fun x y Hxy => fenfa_state_eqb_sound m x y Hxy)
           (enfa_trace_bound m w) s d Hd)
        as [Y Hvalid_prefix].
      assert (Hleaf :
        rlg_prefix_derivation_prime_leaf
          (gamma_grammar_from m s)
          (fenfa_state_eqb m)
          w d).
      {
        exists Y. split.
        - repeat split.
          + exact Hvalid_prefix.
          + now apply Hword_sound.
          + exact Hsimple.
        - exact Hmax.
      }
      destruct
        (section4_gamma_support_prime_leaf_trace_of_derivation
           m s w d Hwf Hs Hleaf)
        as [q [t [Ht [Htrace [Htrace_word_w [HsimpleE HmaxE]]]]]].
      destruct
        (gamma_prefix_derivation_of_trace_of_valid_prefix_derivation
           m s s d Y t Hvalid_prefix Ht)
        as [Hround [HtraceY _]].
      assert (Y = q).
      {
        pose proof (valid_trace_trace_end m s t Y HtraceY) as HY.
        pose proof (valid_trace_trace_end m s t q Htrace) as Hq.
        congruence.
      }
      subst Y.
      assert (Hin : In (s, t) (started_traces m w)).
      { eapply Henum; eauto. }
      assert (Hqstate : In q (fenfa_states m)).
      { eapply finite_enfa_wf_valid_trace_end_in_states; eauto. }
      apply in_map_iff.
      exists (q, (s, t)). split.
      - unfold f. simpl. exact Hround.
      - unfold xs, enfa_leaf_prime_witnesses.
        apply enfa_prime_maximal_witnesses_In.
        repeat split; auto.
        destruct
          (gamma_started_filter_true
             m s w q t Htrace Htrace_word_w HsimpleE HmaxE)
          as [_ Hf].
        exact Hf.
    }
    assert (Hle1 : length (map f xs) <= length (filter p enum)).
    { eapply NoDup_incl_length; eauto. }
    assert (Hle2 : length (filter p enum) <= length (map f xs)).
    { eapply NoDup_incl_length; eauto. }
    rewrite length_map in Hle1, Hle2.
    lia.
  Qed.

  Theorem section4_lemma3_gamma_prime_counts_eq_with_enumeration :
    forall (m : @finite_enfa A) s word_eqb w q,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      word_eqb_reflects_eq word_eqb ->
      NoDup
        (rlg_derivations_from_fuel
           (gamma_grammar_from m s)
           (fenfa_state_eqb m)
           (S (enfa_trace_bound m w))
           s) ->
      NoDup
        (rlg_prefix_derivations_from_fuel
           (gamma_grammar_from m s)
           (fenfa_state_eqb m)
           (enfa_trace_bound m w)
           s) ->
      enfa_da_prime_word m w =
      rlg_da_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (S (enfa_trace_bound m w))
        w /\
      enfa_dra_prime_at m w q =
      rlg_dra_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (enfa_trace_bound m w)
        w
        q /\
      enfa_leaf_prime_word m w =
      rlg_prefix_leaf_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (enfa_trace_bound m w)
        w.
  Proof.
    intros m s word_eqb w q Hwf Hstart Henum Hnodup Hwordeq
      Hda_nodup Hprefix_nodup.
    split.
    - eapply section4_lemma3_gamma_da_prime_count_eq_with_enumeration;
        eauto.
    - split.
      + eapply section4_lemma3_gamma_dra_prime_count_eq_with_enumeration;
          eauto.
      + eapply section4_lemma3_gamma_leaf_prime_count_eq_with_enumeration;
          eauto.
  Qed.

  Lemma gamma_rlg_derivations_from_fuel_NoDup_with_alphabet_nodup :
    forall (m : @finite_enfa A) s fuel,
      finite_enfa_wf m ->
      NoDup (fenfa_alphabet m) ->
      NoDup
        (rlg_derivations_from_fuel
           (gamma_grammar_from m s)
           (fenfa_state_eqb m)
           fuel
           s).
  Proof.
    intros m s fuel Hwf Halphabet.
    apply rlg_derivations_from_fuel_NoDup.
    simpl.
    apply gamma_productions_NoDup_with_alphabet_nodup; auto.
  Qed.

  Lemma gamma_rlg_prefix_derivations_from_fuel_NoDup_with_alphabet_nodup :
    forall (m : @finite_enfa A) s fuel,
      finite_enfa_wf m ->
      NoDup (fenfa_alphabet m) ->
      NoDup
        (rlg_prefix_derivations_from_fuel
           (gamma_grammar_from m s)
           (fenfa_state_eqb m)
           fuel
           s).
  Proof.
    intros m s fuel Hwf Halphabet.
    apply rlg_prefix_derivations_from_fuel_NoDup.
    simpl.
    apply gamma_productions_NoDup_with_alphabet_nodup; auto.
  Qed.

  Theorem section4_lemma3_gamma_da_prime_count_eq_with_alphabet_nodup :
    forall (m : @finite_enfa A) s word_eqb w,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      NoDup (fenfa_alphabet m) ->
      word_eqb_reflects_eq word_eqb ->
      enfa_da_prime_word m w =
      rlg_da_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (S (enfa_trace_bound m w))
        w.
  Proof.
    intros m s word_eqb w Hwf Hstart Halphabet Hwordeq.
    eapply section4_lemma3_gamma_da_prime_count_eq_with_enumeration.
    - exact Hwf.
    - exact Hstart.
    - eapply section4_enfa_prime_trace_enumerated_from_single_start; eauto.
    - eapply section4_enfa_started_traces_nodup_single_start; eauto.
    - exact Hwordeq.
    - eapply gamma_rlg_derivations_from_fuel_NoDup_with_alphabet_nodup;
        eauto.
  Qed.

  Theorem section4_lemma3_gamma_dra_prime_count_eq_with_alphabet_nodup :
    forall (m : @finite_enfa A) s word_eqb w q,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      NoDup (fenfa_alphabet m) ->
      word_eqb_reflects_eq word_eqb ->
      enfa_dra_prime_at m w q =
      rlg_dra_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (enfa_trace_bound m w)
        w
        q.
  Proof.
    intros m s word_eqb w q Hwf Hstart Halphabet Hwordeq.
    eapply section4_lemma3_gamma_dra_prime_count_eq_with_enumeration.
    - exact Hwf.
    - exact Hstart.
    - eapply section4_enfa_prime_trace_enumerated_from_single_start; eauto.
    - eapply section4_enfa_started_traces_nodup_single_start; eauto.
    - exact Hwordeq.
    - eapply gamma_rlg_prefix_derivations_from_fuel_NoDup_with_alphabet_nodup;
        eauto.
  Qed.

  Theorem section4_lemma3_gamma_leaf_prime_count_eq_with_alphabet_nodup :
    forall (m : @finite_enfa A) s word_eqb w,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      NoDup (fenfa_alphabet m) ->
      word_eqb_reflects_eq word_eqb ->
      enfa_leaf_prime_word m w =
      rlg_prefix_leaf_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (enfa_trace_bound m w)
        w.
  Proof.
    intros m s word_eqb w Hwf Hstart Halphabet Hwordeq.
    eapply section4_lemma3_gamma_leaf_prime_count_eq_with_enumeration.
    - exact Hwf.
    - exact Hstart.
    - eapply section4_enfa_prime_trace_enumerated_from_single_start; eauto.
    - eapply section4_enfa_started_traces_nodup_single_start; eauto.
    - exact Hwordeq.
    - eapply gamma_rlg_prefix_derivations_from_fuel_NoDup_with_alphabet_nodup;
        eauto.
  Qed.

  Theorem section4_lemma3_gamma_prime_counts_eq_with_alphabet_nodup :
    forall (m : @finite_enfa A) s word_eqb w q,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      NoDup (fenfa_alphabet m) ->
      word_eqb_reflects_eq word_eqb ->
      enfa_da_prime_word m w =
      rlg_da_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (S (enfa_trace_bound m w))
        w /\
      enfa_dra_prime_at m w q =
      rlg_dra_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (enfa_trace_bound m w)
        w
        q /\
      enfa_leaf_prime_word m w =
      rlg_prefix_leaf_prime_count
        (gamma_grammar_from m s)
        (fenfa_state_eqb m)
        word_eqb
        (enfa_trace_bound m w)
        w.
  Proof.
    intros m s word_eqb w q Hwf Hstart Halphabet Hwordeq.
    split.
    - eapply section4_lemma3_gamma_da_prime_count_eq_with_alphabet_nodup;
        eauto.
    - split.
      + eapply section4_lemma3_gamma_dra_prime_count_eq_with_alphabet_nodup;
          eauto.
      + eapply section4_lemma3_gamma_leaf_prime_count_eq_with_alphabet_nodup;
          eauto.
  Qed.

  (* Aliases for the accepting-maximal reflection formulations. *)
  Definition section4_lemma3_gamma_da_prime_count_eq_with_enumeration_under_accepting_maximal_reflection :=
    section4_lemma3_gamma_da_prime_count_eq_with_enumeration.

  Definition section4_lemma3_gamma_prime_counts_eq_with_enumeration_under_accepting_maximal_reflection :=
    section4_lemma3_gamma_prime_counts_eq_with_enumeration.

  Definition section4_lemma3_gamma_da_prime_count_eq_with_alphabet_nodup_under_accepting_maximal_reflection :=
    section4_lemma3_gamma_da_prime_count_eq_with_alphabet_nodup.

  Definition section4_lemma3_gamma_prime_counts_eq_with_alphabet_nodup_under_accepting_maximal_reflection :=
    section4_lemma3_gamma_prime_counts_eq_with_alphabet_nodup.

  Theorem section4_gamma_support_reachufa_to_rlg_reach_unambiguous :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_ReachUFA m ->
      gamma_rlg_reach_unambiguous m s.
  Proof.
    intros m s Hwf Hstart Henum Hreach prefix q d1 d2 Hd1 Hd2.
    assert (Hs : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
    }
    destruct
      (section4_gamma_support_prime_reach_trace_of_derivation
         m s prefix q d1 Hwf Hs Hd1)
      as [t1 [Ht1 [Htrace1 [Hword1 Hsimple1]]]].
    destruct
      (section4_gamma_support_prime_reach_trace_of_derivation
         m s prefix q d2 Hwf Hs Hd2)
      as [t2 [Ht2 [Htrace2 [Hword2 Hsimple2]]]].
    assert (Hq : In q (fenfa_states m)).
    { eapply finite_enfa_wf_valid_trace_end_in_states; eauto. }
    pose proof (Hreach prefix q Hq) as Hcount.
    unfold enfa_dra_prime_at in Hcount.
    assert (Hin1 : In (s, t1) (started_traces m prefix)).
    { eapply Henum; eauto. }
    assert (Hin2 : In (s, t2) (started_traces m prefix)).
    { eapply Henum; eauto. }
    assert (Hfilt1 : ends_inb m q (s, t1) && epsilon_simpleb m (s, t1) = true).
    {
      pose proof (valid_trace_trace_end m s t1 q Htrace1) as Hend.
      unfold ends_inb, started_end. simpl.
      rewrite Hend.
      rewrite (fenfa_state_eqb_complete m q q eq_refl).
      exact Hsimple1.
    }
    assert (Hfilt2 : ends_inb m q (s, t2) && epsilon_simpleb m (s, t2) = true).
    {
      pose proof (valid_trace_trace_end m s t2 q Htrace2) as Hend.
      unfold ends_inb, started_end. simpl.
      rewrite Hend.
      rewrite (fenfa_state_eqb_complete m q q eq_refl).
      exact Hsimple2.
    }
    assert ((s, t1) = (s, t2)) as Hst.
    {
      eapply filter_length_le_one_unique
        with (p := fun st => ends_inb m q st && epsilon_simpleb m st)
             (xs := started_traces m prefix); eauto.
    }
    inversion Hst; subst t2.
    destruct Hd1 as [Hvalid1 _].
    destruct Hd2 as [Hvalid2 _].
    destruct
      (gamma_prefix_derivation_of_trace_of_valid_prefix_derivation
         m s s d1 q t1 Hvalid1 Ht1)
      as [Hround1 _].
    destruct
      (gamma_prefix_derivation_of_trace_of_valid_prefix_derivation
         m s s d2 q t1 Hvalid2 Ht2)
      as [Hround2 _].
    rewrite <- Hround1, <- Hround2. reflexivity.
  Qed.

  Theorem section4_gamma_support_rlg_reach_unambiguous_to_reachufa :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_started_traces_nodup m ->
      gamma_rlg_reach_unambiguous m s ->
      enfa_ReachUFA m.
  Proof.
    intros m s Hwf Hstart Hnodup Hrlg w q Hq.
    unfold enfa_dra_prime_at.
    destruct
      (le_gt_dec
         (length
            (filter
               (fun st : started_trace m =>
                  ends_inb m q st && epsilon_simpleb m st)
               (started_traces m w))) 1)
      as [Hle | Hgt].
    - exact Hle.
    - exfalso.
      assert (Htwo :
        2 <= length
          (filter
             (fun st : started_trace m =>
                ends_inb m q st && epsilon_simpleb m st)
             (started_traces m w))) by lia.
      destruct
        (NoDup_filter_ge_two
           (fun st : started_trace m =>
              ends_inb m q st && epsilon_simpleb m st)
           (started_traces m w)
           (Hnodup w) Htwo)
        as [[s1 t1] [[s2 t2] [Hin1 [Hin2 [Hneq [Hfilt1 Hfilt2]]]]]].
      destruct (started_traces_valid m w s1 t1 Hin1) as [Htrace1 Hword1].
      destruct (started_traces_valid m w s2 t2 Hin2) as [Htrace2 Hword2].
      apply andb_true_iff in Hfilt1 as [Hend1 Hsimple1].
      apply andb_true_iff in Hfilt2 as [Hend2 Hsimple2].
      unfold ends_inb in Hend1, Hend2.
      apply fenfa_state_eqb_sound in Hend1.
      apply fenfa_state_eqb_sound in Hend2.
      unfold started_end in Hend1, Hend2. simpl in Hend1, Hend2.
      subst q.
      assert (Hs1 : s1 = s).
      {
        pose proof (started_traces_start_in m w s1 t1 Hin1) as Hs1.
        rewrite Hstart in Hs1. simpl in Hs1. destruct Hs1 as [Hs1 | []].
        symmetry. exact Hs1.
      }
      assert (Hs2 : s2 = s).
      {
        pose proof (started_traces_start_in m w s2 t2 Hin2) as Hs2.
        rewrite Hstart in Hs2. simpl in Hs2. destruct Hs2 as [Hs2 | []].
        symmetry. exact Hs2.
      }
      subst s1 s2.
      pose (d1 := gamma_prefix_derivation_of_trace m s t1).
      pose (d2 := gamma_prefix_derivation_of_trace m s t2).
      assert (Hd1 :
        rlg_prefix_derivation_prime_reaches
          (gamma_grammar_from m s) (fenfa_state_eqb m) w
          (trace_end s t1) d1).
      {
        unfold d1.
        eapply section4_gamma_support_prime_reach_derivation_of_trace.
        - exact Hwf.
        - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
        - exact Htrace1.
        - exact Hword1.
        - exact Hsimple1.
      }
      assert (Hd2 :
        rlg_prefix_derivation_prime_reaches
          (gamma_grammar_from m s) (fenfa_state_eqb m) w
          (trace_end s t1) d2).
      {
        unfold d2.
        rewrite Hend2 in Htrace2.
        eapply section4_gamma_support_prime_reach_derivation_of_trace.
        - exact Hwf.
        - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
        - exact Htrace2.
        - exact Hword2.
        - exact Hsimple2.
      }
      specialize (Hrlg w (trace_end s t1) d1 d2 Hd1 Hd2).
      unfold d1, d2 in Hrlg.
      apply Hneq.
      assert (Some t1 = Some t2) as Hteq.
      {
        rewrite <- (gamma_trace_of_prefix_derivation_of_trace m s t1).
        rewrite <- (gamma_trace_of_prefix_derivation_of_trace m s t2).
        now rewrite Hrlg.
      }
      inversion Hteq. reflexivity.
  Qed.

  Theorem section4_gamma_support_ufa_to_rlg_unambiguous :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_UFA m ->
      gamma_rlg_unambiguous m s.
  Proof.
    intros m s Hwf Hstart Henum Hufa w d1 d2 Hd1 Hd2.
    assert (Hs : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
    }
    destruct
      (section4_gamma_support_prime_accepting_trace_of_derivation
         m s w d1 Hwf Hs Hd1)
      as [q1 [t1 [Ht1 [Htrace1 [Hword1 [Hfinal1 [Hsimple1 Hmax1]]]]]]].
    destruct
      (section4_gamma_support_prime_accepting_trace_of_derivation
         m s w d2 Hwf Hs Hd2)
      as [q2 [t2 [Ht2 [Htrace2 [Hword2 [Hfinal2 [Hsimple2 Hmax2]]]]]]].
    assert (Hq1 : In q1 (fenfa_states m)).
    {
      eapply finite_enfa_wf_valid_trace_end_in_states.
      - exact Hwf.
      - exact Hs.
      - exact Htrace1.
    }
    assert (Hq2 : In q2 (fenfa_states m)).
    {
      eapply finite_enfa_wf_valid_trace_end_in_states.
      - exact Hwf.
      - exact Hs.
      - exact Htrace2.
    }
    assert (Hfinals1 : In q1 (enfa_final_states m)).
    { unfold enfa_final_states. apply filter_In. auto. }
    assert (Hfinals2 : In q2 (enfa_final_states m)).
    { unfold enfa_final_states. apply filter_In. auto. }
    assert (Hin1 : In (s, t1) (started_traces m w)).
    { eapply Henum; eauto. }
    assert (Hin2 : In (s, t2) (started_traces m w)).
    { eapply Henum; eauto. }
    destruct (gamma_started_accepting_filter_true
                m s w q1 t1 Htrace1 Hword1 Hsimple1 Hmax1)
      as [_ Hfilt1].
    destruct (gamma_started_accepting_filter_true
                m s w q2 t2 Htrace2 Hword2 Hsimple2 Hmax2)
      as [_ Hfilt2].
    destruct (fenfa_state_eqb m q1 q2) eqn:Hqeq.
    - apply fenfa_state_eqb_sound in Hqeq. subst q2.
      pose proof (Hufa w) as Hda.
      unfold enfa_da_prime_word in Hda.
      pose proof
        (sum_map_In_le
           (enfa_accepting_maximal_simple_reach_count m w)
           (enfa_final_states m) q1 Hfinals1) as Hcount_le.
      assert (Hcount : enfa_accepting_maximal_simple_reach_count m w q1 <= 1)
        by lia.
      unfold enfa_accepting_maximal_simple_reach_count in Hcount.
      assert ((s, t1) = (s, t2)) as Hst.
      {
        eapply filter_length_le_one_unique
          with
            (p := fun st =>
                    (ends_inb m q1 st && epsilon_simpleb m st)
                    && enfa_accepting_maximal_epsilon_simpleb m st)
            (xs := started_traces m w); eauto.
      }
      inversion Hst; subst t2.
      destruct Hd1 as [[Hvalid1 _] _].
      destruct Hd2 as [[Hvalid2 _] _].
      destruct
        (gamma_derivation_of_trace_of_valid_derivation
           m s s d1 t1 Hvalid1 Ht1)
        as [q1' [Hround1 [Htrace1' _]]].
      destruct
        (gamma_derivation_of_trace_of_valid_derivation
           m s s d2 t1 Hvalid2 Ht2)
        as [q2' [Hround2 [Htrace2' _]]].
      assert (q1' = q1).
      {
        pose proof (valid_trace_trace_end m s t1 q1' Htrace1').
        pose proof (valid_trace_trace_end m s t1 q1 Htrace1).
        congruence.
      }
      assert (q2' = q1).
      {
        pose proof (valid_trace_trace_end m s t1 q2' Htrace2').
        pose proof (valid_trace_trace_end m s t1 q1 Htrace1).
        congruence.
      }
      subst q1' q2'.
      rewrite <- Hround1, <- Hround2.
      reflexivity.
    - exfalso.
      assert (Hneq : q1 <> q2).
      {
        intro Heq. subst q2.
        rewrite (fenfa_state_eqb_complete m q1 q1 eq_refl) in Hqeq.
        discriminate.
      }
      assert (Hpos1 : 0 < enfa_accepting_maximal_simple_reach_count m w q1).
      {
        unfold enfa_accepting_maximal_simple_reach_count.
        eapply filter_length_pos_of_In with (x := (s, t1)); eauto.
      }
      assert (Hpos2 : 0 < enfa_accepting_maximal_simple_reach_count m w q2).
      {
        unfold enfa_accepting_maximal_simple_reach_count.
        eapply filter_length_pos_of_In with (x := (s, t2)); eauto.
      }
      pose proof
        (sum_map_two_pos_lower
           (enfa_accepting_maximal_simple_reach_count m w)
           (enfa_final_states m) q1 q2
           (gamma_final_states_nodup m Hwf)
           Hfinals1 Hfinals2 Hneq Hpos1 Hpos2) as Htwo.
      pose proof (Hufa w) as Hda.
      unfold enfa_da_prime_word in Hda. lia.
  Qed.

  Theorem section4_gamma_support_rlg_unambiguous_to_ufa :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_started_traces_nodup m ->
      gamma_rlg_unambiguous m s ->
      enfa_UFA m.
  Proof.
    intros m s Hwf Hstart Hnodup Hrlg w.
    unfold enfa_da_prime_word.
    destruct
      (le_gt_dec
         (sum_nats
            (map (enfa_accepting_maximal_simple_reach_count m w)
               (enfa_final_states m))) 1)
      as [Hle | Hgt].
    - exact Hle.
    - exfalso.
      assert (Htwo :
        2 <= sum_nats
          (map (enfa_accepting_maximal_simple_reach_count m w)
             (enfa_final_states m))) by lia.
      destruct
        (sum_map_ge_two_cases
           (enfa_accepting_maximal_simple_reach_count m w)
           (enfa_final_states m)
           (gamma_final_states_nodup m Hwf) Htwo)
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
          as [[s1 t1] [[s2 t2] [Hin1 [Hin2 [Hneq [Hfilt1 Hfilt2]]]]]].
        destruct (started_traces_valid m w s1 t1 Hin1) as [Htrace1 Hword1].
        destruct (started_traces_valid m w s2 t2 Hin2) as [Htrace2 Hword2].
        apply andb_true_iff in Hfilt1 as [Hfilt1 Hmax1].
        apply andb_true_iff in Hfilt2 as [Hfilt2 Hmax2].
        apply andb_true_iff in Hfilt1 as [Hend1 Hsimple1].
        apply andb_true_iff in Hfilt2 as [Hend2 Hsimple2].
        unfold ends_inb in Hend1, Hend2.
        apply fenfa_state_eqb_sound in Hend1.
        apply fenfa_state_eqb_sound in Hend2.
        unfold started_end in Hend1, Hend2. simpl in Hend1, Hend2.
        assert (Hs1 : s1 = s).
        {
          pose proof (started_traces_start_in m w s1 t1 Hin1) as Hs1.
          rewrite Hstart in Hs1. simpl in Hs1. destruct Hs1 as [Hs1 | []].
          symmetry. exact Hs1.
        }
        assert (Hs2 : s2 = s).
        {
          pose proof (started_traces_start_in m w s2 t2 Hin2) as Hs2.
          rewrite Hstart in Hs2. simpl in Hs2. destruct Hs2 as [Hs2 | []].
          symmetry. exact Hs2.
        }
        subst s1 s2.
        rewrite Hend1 in Htrace1.
        rewrite Hend2 in Htrace2.
        pose (d1 := gamma_derivation_of_trace m s t1 q).
        pose (d2 := gamma_derivation_of_trace m s t2 q).
        assert (Hprime1 :
          rlg_derivation_accepting_prime
            (gamma_grammar_from m s) (fenfa_state_eqb m) w d1).
        {
          unfold d1.
          eapply section4_gamma_support_prime_accepting_derivation_of_trace.
          - exact Hwf.
          - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
          - exact Htrace1.
          - exact Hword1.
          - apply filter_In in Hq as [_ Hfinal]. exact Hfinal.
          - exact Hsimple1.
          - exact Hmax1.
        }
        assert (Hprime2 :
          rlg_derivation_accepting_prime
            (gamma_grammar_from m s) (fenfa_state_eqb m) w d2).
        {
          unfold d2.
          eapply section4_gamma_support_prime_accepting_derivation_of_trace.
          - exact Hwf.
          - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
          - exact Htrace2.
          - exact Hword2.
          - apply filter_In in Hq as [_ Hfinal]. exact Hfinal.
          - exact Hsimple2.
          - exact Hmax2.
        }
        specialize (Hrlg w d1 d2 Hprime1 Hprime2).
        apply Hneq.
        unfold d1, d2 in Hrlg.
        apply gamma_derivation_of_trace_injective in Hrlg as [Ht _].
        subst t2. reflexivity.
      + destruct
          (filter_length_pos_exists
             (fun st : started_trace m =>
                (ends_inb m q1 st && epsilon_simpleb m st)
                && enfa_accepting_maximal_epsilon_simpleb m st)
             (started_traces m w) Hpos1)
          as [[s1 t1] [Hin1 Hfilt1]].
        destruct
          (filter_length_pos_exists
             (fun st : started_trace m =>
                (ends_inb m q2 st && epsilon_simpleb m st)
                && enfa_accepting_maximal_epsilon_simpleb m st)
             (started_traces m w) Hpos2)
          as [[s2 t2] [Hin2 Hfilt2]].
        destruct (started_traces_valid m w s1 t1 Hin1) as [Htrace1 Hword1].
        destruct (started_traces_valid m w s2 t2 Hin2) as [Htrace2 Hword2].
        apply andb_true_iff in Hfilt1 as [Hfilt1 Hmax1].
        apply andb_true_iff in Hfilt2 as [Hfilt2 Hmax2].
        apply andb_true_iff in Hfilt1 as [Hend1 Hsimple1].
        apply andb_true_iff in Hfilt2 as [Hend2 Hsimple2].
        unfold ends_inb in Hend1, Hend2.
        apply fenfa_state_eqb_sound in Hend1.
        apply fenfa_state_eqb_sound in Hend2.
        unfold started_end in Hend1, Hend2. simpl in Hend1, Hend2.
        assert (Hs1 : s1 = s).
        {
          pose proof (started_traces_start_in m w s1 t1 Hin1) as Hs1.
          rewrite Hstart in Hs1. simpl in Hs1. destruct Hs1 as [Hs1 | []].
          symmetry. exact Hs1.
        }
        assert (Hs2 : s2 = s).
        {
          pose proof (started_traces_start_in m w s2 t2 Hin2) as Hs2.
          rewrite Hstart in Hs2. simpl in Hs2. destruct Hs2 as [Hs2 | []].
          symmetry. exact Hs2.
        }
        subst s1 s2.
        rewrite Hend1 in Htrace1.
        rewrite Hend2 in Htrace2.
        pose (d1 := gamma_derivation_of_trace m s t1 q1).
        pose (d2 := gamma_derivation_of_trace m s t2 q2).
        assert (Hprime1 :
          rlg_derivation_accepting_prime
            (gamma_grammar_from m s) (fenfa_state_eqb m) w d1).
        {
          unfold d1.
          eapply section4_gamma_support_prime_accepting_derivation_of_trace.
          - exact Hwf.
          - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
          - exact Htrace1.
          - exact Hword1.
          - apply filter_In in Hq1 as [_ Hfinal]. exact Hfinal.
          - exact Hsimple1.
          - exact Hmax1.
        }
        assert (Hprime2 :
          rlg_derivation_accepting_prime
            (gamma_grammar_from m s) (fenfa_state_eqb m) w d2).
        {
          unfold d2.
          eapply section4_gamma_support_prime_accepting_derivation_of_trace.
          - exact Hwf.
          - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
          - exact Htrace2.
          - exact Hword2.
          - apply filter_In in Hq2 as [_ Hfinal]. exact Hfinal.
          - exact Hsimple2.
          - exact Hmax2.
        }
        specialize (Hrlg w d1 d2 Hprime1 Hprime2).
        unfold d1, d2 in Hrlg.
        apply gamma_derivation_of_trace_injective in Hrlg as [_ Hq].
        contradiction.
  Qed.

  Theorem section4_gamma_support_leafufa_to_rlg_leaf_unambiguous :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_LeafUFA m ->
      gamma_rlg_leaf_unambiguous m s.
  Proof.
    intros m s Hwf Hstart Henum Hleaf prefix d1 d2 Hd1 Hd2.
    assert (Hs : In s (fenfa_states m)).
    {
      eapply fenfa_starts_in_states; eauto.
      rewrite Hstart. simpl. auto.
    }
    destruct
      (section4_gamma_support_prime_leaf_trace_of_derivation
         m s prefix d1 Hwf Hs Hd1)
      as [q1 [t1 [Ht1 [Htrace1 [Hword1 [Hsimple1 Hmax1]]]]]].
    destruct
      (section4_gamma_support_prime_leaf_trace_of_derivation
         m s prefix d2 Hwf Hs Hd2)
      as [q2 [t2 [Ht2 [Htrace2 [Hword2 [Hsimple2 Hmax2]]]]]].
    assert (Hq1 : In q1 (fenfa_states m)).
    {
      eapply finite_enfa_wf_valid_trace_end_in_states.
      - exact Hwf.
      - exact Hs.
      - exact Htrace1.
    }
    assert (Hq2 : In q2 (fenfa_states m)).
    {
      eapply finite_enfa_wf_valid_trace_end_in_states.
      - exact Hwf.
      - exact Hs.
      - exact Htrace2.
    }
    assert (Hin1 : In (s, t1) (started_traces m prefix)).
    { eapply Henum; eauto. }
    assert (Hin2 : In (s, t2) (started_traces m prefix)).
    { eapply Henum; eauto. }
    destruct (gamma_started_filter_true m s prefix q1 t1 Htrace1 Hword1 Hsimple1 Hmax1)
      as [_ Hfilt1].
    destruct (gamma_started_filter_true m s prefix q2 t2 Htrace2 Hword2 Hsimple2 Hmax2)
      as [_ Hfilt2].
    destruct (fenfa_state_eqb m q1 q2) eqn:Hqeq.
    - apply fenfa_state_eqb_sound in Hqeq. subst q2.
      pose proof (Hleaf prefix) as Hleaf_count.
      unfold enfa_leaf_prime_word in Hleaf_count.
      pose proof
        (sum_map_In_le
           (enfa_maximal_simple_reach_count m prefix)
           (fenfa_states m) q1 Hq1) as Hcount_le.
      assert (Hcount : enfa_maximal_simple_reach_count m prefix q1 <= 1) by lia.
      unfold enfa_maximal_simple_reach_count in Hcount.
      assert ((s, t1) = (s, t2)) as Hst.
      {
        eapply filter_length_le_one_unique
          with
            (p := fun st =>
                    (ends_inb m q1 st && epsilon_simpleb m st)
                    && maximal_epsilon_simpleb m st)
            (xs := started_traces m prefix); eauto.
      }
      inversion Hst; subst t2.
      destruct Hd1 as [X1 [Hreach1 _]].
      destruct Hd2 as [X2 [Hreach2 _]].
      destruct Hreach1 as [Hvalid1 _].
      destruct Hreach2 as [Hvalid2 _].
      destruct
        (gamma_prefix_derivation_of_trace_of_valid_prefix_derivation
           m s s d1 X1 t1 Hvalid1 Ht1)
        as [Hround1 _].
      destruct
        (gamma_prefix_derivation_of_trace_of_valid_prefix_derivation
           m s s d2 X2 t1 Hvalid2 Ht2)
        as [Hround2 _].
      rewrite <- Hround1, <- Hround2.
      reflexivity.
    - exfalso.
      assert (Hneq : q1 <> q2).
      {
        intro Heq. subst q2.
        rewrite (fenfa_state_eqb_complete m q1 q1 eq_refl) in Hqeq.
        discriminate.
      }
      assert (Hpos1 : 0 < enfa_maximal_simple_reach_count m prefix q1).
      {
        unfold enfa_maximal_simple_reach_count.
        eapply filter_length_pos_of_In with (x := (s, t1)); eauto.
      }
      assert (Hpos2 : 0 < enfa_maximal_simple_reach_count m prefix q2).
      {
        unfold enfa_maximal_simple_reach_count.
        eapply filter_length_pos_of_In with (x := (s, t2)); eauto.
      }
      pose proof
        (sum_map_two_pos_lower
           (enfa_maximal_simple_reach_count m prefix)
           (fenfa_states m) q1 q2
           (fenfa_states_nodup m Hwf)
           Hq1 Hq2 Hneq Hpos1 Hpos2) as Htwo.
      pose proof (Hleaf prefix) as Hleaf_count.
      unfold enfa_leaf_prime_word in Hleaf_count. lia.
  Qed.

  Theorem section4_gamma_support_rlg_leaf_unambiguous_to_leafufa :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_started_traces_nodup m ->
      gamma_rlg_leaf_unambiguous m s ->
      enfa_LeafUFA m.
  Proof.
    intros m s Hwf Hstart Hnodup Hrlg w.
    unfold enfa_leaf_prime_word.
    destruct
      (le_gt_dec
         (sum_nats
            (map (enfa_maximal_simple_reach_count m w)
               (fenfa_states m))) 1)
      as [Hle | Hgt].
    - exact Hle.
    - exfalso.
      assert (Htwo :
        2 <= sum_nats
          (map (enfa_maximal_simple_reach_count m w)
             (fenfa_states m))) by lia.
      destruct
        (sum_map_ge_two_cases
           (enfa_maximal_simple_reach_count m w)
           (fenfa_states m)
           (fenfa_states_nodup m Hwf) Htwo)
        as [[q [Hq Hcount2]] |
            [q1 [q2 [Hq1 [Hq2 [Hqneq [Hpos1 Hpos2]]]]]]].
      + unfold enfa_maximal_simple_reach_count in Hcount2.
        destruct
          (NoDup_filter_ge_two
             (fun st : started_trace m =>
                (ends_inb m q st && epsilon_simpleb m st)
                && maximal_epsilon_simpleb m st)
             (started_traces m w)
             (Hnodup w) Hcount2)
          as [[s1 t1] [[s2 t2] [Hin1 [Hin2 [Hneq [Hfilt1 Hfilt2]]]]]].
        destruct (started_traces_valid m w s1 t1 Hin1) as [Htrace1 Hword1].
        destruct (started_traces_valid m w s2 t2 Hin2) as [Htrace2 Hword2].
        apply andb_true_iff in Hfilt1 as [Hfilt1 Hmax1].
        apply andb_true_iff in Hfilt2 as [Hfilt2 Hmax2].
        apply andb_true_iff in Hfilt1 as [Hend1 Hsimple1].
        apply andb_true_iff in Hfilt2 as [Hend2 Hsimple2].
        unfold ends_inb in Hend1, Hend2.
        apply fenfa_state_eqb_sound in Hend1.
        apply fenfa_state_eqb_sound in Hend2.
        unfold started_end in Hend1, Hend2. simpl in Hend1, Hend2.
        assert (Hs1 : s1 = s).
        {
          pose proof (started_traces_start_in m w s1 t1 Hin1) as Hs1.
          rewrite Hstart in Hs1. simpl in Hs1. destruct Hs1 as [Hs1 | []].
          symmetry. exact Hs1.
        }
        assert (Hs2 : s2 = s).
        {
          pose proof (started_traces_start_in m w s2 t2 Hin2) as Hs2.
          rewrite Hstart in Hs2. simpl in Hs2. destruct Hs2 as [Hs2 | []].
          symmetry. exact Hs2.
        }
        subst s1 s2.
        rewrite Hend1 in Htrace1.
        rewrite Hend2 in Htrace2.
        pose (d1 := gamma_prefix_derivation_of_trace m s t1).
        pose (d2 := gamma_prefix_derivation_of_trace m s t2).
        assert (Hleaf1 :
          rlg_prefix_derivation_prime_leaf
            (gamma_grammar_from m s) (fenfa_state_eqb m) w d1).
        {
          unfold d1.
          eapply section4_gamma_support_prime_leaf_derivation_of_trace.
          - exact Hwf.
          - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
          - exact Htrace1.
          - exact Hword1.
          - exact Hsimple1.
          - exact Hmax1.
        }
        assert (Hleaf2 :
          rlg_prefix_derivation_prime_leaf
            (gamma_grammar_from m s) (fenfa_state_eqb m) w d2).
        {
          unfold d2.
          eapply section4_gamma_support_prime_leaf_derivation_of_trace.
          - exact Hwf.
          - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
          - exact Htrace2.
          - exact Hword2.
          - exact Hsimple2.
          - exact Hmax2.
        }
        specialize (Hrlg w d1 d2 Hleaf1 Hleaf2).
        apply Hneq.
        unfold d1, d2 in Hrlg.
        assert (Some t1 = Some t2) as Hteq.
        {
          rewrite <- (gamma_trace_of_prefix_derivation_of_trace m s t1).
          rewrite <- (gamma_trace_of_prefix_derivation_of_trace m s t2).
          now rewrite Hrlg.
        }
        inversion Hteq. reflexivity.
      + destruct
          (filter_length_pos_exists
             (fun st : started_trace m =>
                (ends_inb m q1 st && epsilon_simpleb m st)
                && maximal_epsilon_simpleb m st)
             (started_traces m w) Hpos1)
          as [[s1 t1] [Hin1 Hfilt1]].
        destruct
          (filter_length_pos_exists
             (fun st : started_trace m =>
                (ends_inb m q2 st && epsilon_simpleb m st)
                && maximal_epsilon_simpleb m st)
             (started_traces m w) Hpos2)
          as [[s2 t2] [Hin2 Hfilt2]].
        destruct (started_traces_valid m w s1 t1 Hin1) as [Htrace1 Hword1].
        destruct (started_traces_valid m w s2 t2 Hin2) as [Htrace2 Hword2].
        apply andb_true_iff in Hfilt1 as [Hfilt1 Hmax1].
        apply andb_true_iff in Hfilt2 as [Hfilt2 Hmax2].
        apply andb_true_iff in Hfilt1 as [Hend1 Hsimple1].
        apply andb_true_iff in Hfilt2 as [Hend2 Hsimple2].
        unfold ends_inb in Hend1, Hend2.
        apply fenfa_state_eqb_sound in Hend1.
        apply fenfa_state_eqb_sound in Hend2.
        unfold started_end in Hend1, Hend2. simpl in Hend1, Hend2.
        assert (Hs1 : s1 = s).
        {
          pose proof (started_traces_start_in m w s1 t1 Hin1) as Hs1.
          rewrite Hstart in Hs1. simpl in Hs1. destruct Hs1 as [Hs1 | []].
          symmetry. exact Hs1.
        }
        assert (Hs2 : s2 = s).
        {
          pose proof (started_traces_start_in m w s2 t2 Hin2) as Hs2.
          rewrite Hstart in Hs2. simpl in Hs2. destruct Hs2 as [Hs2 | []].
          symmetry. exact Hs2.
        }
        subst s1 s2.
        rewrite Hend1 in Htrace1.
        rewrite Hend2 in Htrace2.
        pose (d1 := gamma_prefix_derivation_of_trace m s t1).
        pose (d2 := gamma_prefix_derivation_of_trace m s t2).
        assert (Hleaf1 :
          rlg_prefix_derivation_prime_leaf
            (gamma_grammar_from m s) (fenfa_state_eqb m) w d1).
        {
          unfold d1.
          eapply section4_gamma_support_prime_leaf_derivation_of_trace.
          - exact Hwf.
          - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
          - exact Htrace1.
          - exact Hword1.
          - exact Hsimple1.
          - exact Hmax1.
        }
        assert (Hleaf2 :
          rlg_prefix_derivation_prime_leaf
            (gamma_grammar_from m s) (fenfa_state_eqb m) w d2).
        {
          unfold d2.
          eapply section4_gamma_support_prime_leaf_derivation_of_trace.
          - exact Hwf.
          - eapply fenfa_starts_in_states; eauto. rewrite Hstart. simpl. auto.
          - exact Htrace2.
          - exact Hword2.
          - exact Hsimple2.
          - exact Hmax2.
        }
        specialize (Hrlg w d1 d2 Hleaf1 Hleaf2).
        unfold d1, d2 in Hrlg.
        assert (Some t1 = Some t2) as Hteq.
        {
          rewrite <- (gamma_trace_of_prefix_derivation_of_trace m s t1).
          rewrite <- (gamma_trace_of_prefix_derivation_of_trace m s t2).
          now rewrite Hrlg.
        }
        inversion Hteq; subst t2.
        pose proof (valid_trace_trace_end m s t1 q1 Htrace1) as Hendq1.
         pose proof (valid_trace_trace_end m s t1 q2 Htrace2) as Hendq2.
         congruence.
  Qed.

  (** Bidirectional Gamma bridge wrappers.  These iff theorems package the six
      directions above with well-formedness, single-start, enumeration
      completeness, and nodup hypotheses. *)
  Theorem section4_gamma_support_ufa_rlg_unambiguous_iff :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      enfa_UFA m <-> gamma_rlg_unambiguous m s.
  Proof.
    intros m s Hwf Hstart Henum Hnodup.
    split.
    - eapply section4_gamma_support_ufa_to_rlg_unambiguous; eauto.
    - eapply section4_gamma_support_rlg_unambiguous_to_ufa; eauto.
  Qed.

  Theorem section4_gamma_support_reachufa_rlg_reach_unambiguous_iff :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      enfa_ReachUFA m <-> gamma_rlg_reach_unambiguous m s.
  Proof.
    intros m s Hwf Hstart Henum Hnodup.
    split.
    - eapply section4_gamma_support_reachufa_to_rlg_reach_unambiguous; eauto.
    - eapply section4_gamma_support_rlg_reach_unambiguous_to_reachufa; eauto.
  Qed.

  Theorem section4_gamma_support_leafufa_rlg_leaf_unambiguous_iff :
    forall (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      enfa_LeafUFA m <-> gamma_rlg_leaf_unambiguous m s.
  Proof.
    intros m s Hwf Hstart Henum Hnodup.
    split.
    - eapply section4_gamma_support_leafufa_to_rlg_leaf_unambiguous; eauto.
    - eapply section4_gamma_support_rlg_leaf_unambiguous_to_leafufa; eauto.
  Qed.

  (** Structured "M ambiguous iff Gamma(M) ambiguous" support.  The sound
      direction maps distinct ENFA accepting trace/end pairs to distinct RLG
      derivations; the complete direction reconstructs ENFA trace/end pairs
      from distinct accepting RLG derivations. *)
  Theorem section4_gamma_support_ambiguity_preservation_sound :
    forall (m : @finite_enfa A) root s q1 q2 t1 t2,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s t1 q1 ->
      valid_trace m s t2 q2 ->
      enfa_final (fenfa_base m) q1 = true ->
      enfa_final (fenfa_base m) q2 = true ->
      t1 <> t2 \/ q1 <> q2 ->
      exists d1 d2,
        rlg_derivation_valid (gamma_grammar_from m root) s d1 None /\
        rlg_derivation_valid (gamma_grammar_from m root) s d2 None /\
        d1 <> d2 /\
        rlg_derivation_word (gamma_grammar_from m root) d1 = trace_word t1 /\
        rlg_derivation_word (gamma_grammar_from m root) d2 = trace_word t2.
  Proof.
    intros m root s q1 q2 t1 t2 Hwf Hs Ht1 Ht2 Hf1 Hf2 Hdiff.
    exists (gamma_derivation_of_trace m root t1 q1),
      (gamma_derivation_of_trace m root t2 q2).
    repeat split.
    - eapply gamma_derivation_of_trace_valid_from; eauto.
    - eapply gamma_derivation_of_trace_valid_from; eauto.
    - intro Heq.
      apply gamma_derivation_of_trace_injective in Heq as [Ht Hq].
      destruct Hdiff as [Hdiff | Hdiff]; auto.
    - apply gamma_derivation_of_trace_word.
    - apply gamma_derivation_of_trace_word.
  Qed.

  Theorem section4_gamma_support_ambiguity_preservation_complete :
    forall (m : @finite_enfa A) root s d1 d2,
      rlg_derivation_valid (gamma_grammar_from m root) s d1 None ->
      rlg_derivation_valid (gamma_grammar_from m root) s d2 None ->
      d1 <> d2 ->
      exists q1 q2 t1 t2,
        valid_trace m s t1 q1 /\
        valid_trace m s t2 q2 /\
        enfa_final (fenfa_base m) q1 = true /\
        enfa_final (fenfa_base m) q2 = true /\
        ~ (t1 = t2 /\ q1 = q2) /\
        trace_word t1 =
          rlg_derivation_word (gamma_grammar_from m root) d1 /\
        trace_word t2 =
          rlg_derivation_word (gamma_grammar_from m root) d2.
  Proof.
    intros m root s d1 d2 Hvalid1 Hvalid2 Hdiff.
    destruct (gamma_trace_of_valid_derivation_some m root s d1 Hvalid1)
      as [t1 Ht1].
    destruct (gamma_trace_of_valid_derivation_some m root s d2 Hvalid2)
      as [t2 Ht2].
    destruct
      (gamma_derivation_of_trace_of_valid_derivation
         m root s d1 t1 Hvalid1 Ht1)
      as [q1 [Hround1 [Htrace1 [Hword1 Hfinal1]]]].
    destruct
      (gamma_derivation_of_trace_of_valid_derivation
         m root s d2 t2 Hvalid2 Ht2)
      as [q2 [Hround2 [Htrace2 [Hword2 Hfinal2]]]].
    exists q1, q2, t1, t2.
    repeat split; auto.
    intros [Ht Hq].
      apply Hdiff.
      rewrite <- Hround1, <- Hround2, Ht, Hq.
      reflexivity.
  Qed.
End RightLinearGrammar.
