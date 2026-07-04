From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Ambiguity Require Import DegreeofAmbiguity.
From PositionAutomata.Regex Require Import RegexReDoS RegexSSS.
From PositionAutomata.Automata Require Import EpsilonNFA.
From PositionAutomata.Grammar Require Import RightLinearGrammar.

(** Section 4 LR(1)-oriented specifications and Gamma-specific machinery.

    Section 4.2 decision-problem predicates are included alongside the LR
    machine and Gamma bridge interfaces. *)

Section Section4LR.
  Context {A : Type}.

  Definition finite_nfa_to_enfa (m : @finite_nfa A) : @finite_enfa A :=
    {|
      fenfa_base :=
        {|
          enfa_state := nfa_state (fnfa_base m);
          enfa_start := nfa_start (fnfa_base m);
          enfa_final := nfa_final (fnfa_base m);
          enfa_step :=
            fun q l =>
              match l with
              | None => []
              | Some a => nfa_step (fnfa_base m) q a
              end
        |};
      fenfa_states := fnfa_states m;
      fenfa_alphabet := fnfa_alphabet m;
      fenfa_state_eqb := fnfa_state_eqb m;
      fenfa_state_eqb_sound := fnfa_state_eqb_sound m;
      fenfa_state_eqb_complete := fnfa_state_eqb_complete m
    |}.

  Theorem finite_nfa_to_enfa_epsilon_free :
    forall (m : @finite_nfa A),
      enfa_epsilon_free (finite_nfa_to_enfa m).
  Proof.
    intros m q. reflexivity.
  Qed.

  (** Definition 7 regex-level specs.  [Mpos(E)] and [Msss(E)] carry the weak
      and strong reach-unambiguous notions, plus the weak deterministic and
      leaf-unambiguous characterizations. *)
  Definition regex_Mpos
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : @finite_enfa A :=
    finite_nfa_to_enfa (regex_finite_position_nfa alphabet label_matches r).

  Definition regex_weak_reach_unambiguous
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    enfa_ReachUFA (regex_Mpos alphabet label_matches r).

  Definition regex_strong_reach_unambiguous
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    enfa_ReachUFA (regex_Msss alphabet label_matches r).

  Definition regex_weak_deterministic
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    enfa_LeafUFA (regex_Mpos alphabet label_matches r).

  Definition regex_weak_leaf_unambiguous
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    regex_weak_deterministic alphabet label_matches r.

  Definition regex_leaf_unambiguous
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    enfa_LeafUFA (regex_Msss alphabet label_matches r).

  Definition regex_strong_leaf_unambiguous
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    regex_leaf_unambiguous alphabet label_matches r.

  Theorem section4_definition7_regex_characterizations :
    forall alphabet label_matches (r : regex A),
      regex_weak_reach_unambiguous alphabet label_matches r =
        enfa_ReachUFA (regex_Mpos alphabet label_matches r) /\
      regex_strong_reach_unambiguous alphabet label_matches r =
        enfa_ReachUFA (@regex_Msss A alphabet label_matches r) /\
      regex_weak_leaf_unambiguous alphabet label_matches r =
        enfa_LeafUFA (regex_Mpos alphabet label_matches r) /\
      regex_strong_leaf_unambiguous alphabet label_matches r =
        enfa_LeafUFA (@regex_Msss A alphabet label_matches r).
  Proof.
    intros. repeat split; reflexivity.
  Qed.

  Inductive lr_lookahead : Type :=
  | LATerm : A -> lr_lookahead
  | LAEpsilon : lr_lookahead
  | LAEndLeft : lr_lookahead
  | LAEndRight : lr_lookahead.

  Inductive lr_symbol (Q : Type) : Type :=
  | LRTerm : A -> lr_symbol Q
  | LRNonterm : Q -> lr_symbol Q
  | LREpsilon : lr_symbol Q
  | LREndLeft : lr_symbol Q
  | LREndRight : lr_symbol Q.

  Arguments LRTerm {Q} _.
  Arguments LRNonterm {Q} _.
  Arguments LREpsilon {Q}.
  Arguments LREndLeft {Q}.
  Arguments LREndRight {Q}.

  (** LR(1) item shapes used for Theorem 6.  This formalizes the normalized
      LR(1) machine skeleton for the right-linear grammar [Gamma(M)]: state
      items, shift-before/after items, complete items, and final reduce items. *)
  Inductive lr1_item (Q : Type) : Type :=
  | LRState : Q -> lr_lookahead -> lr1_item Q
  | LRBefore : Q -> lr_symbol Q -> Q -> lr_lookahead -> lr1_item Q
  | LRAfterSymbol : Q -> lr_symbol Q -> Q -> lr_lookahead -> lr1_item Q
  | LRComplete : Q -> lr_symbol Q -> Q -> lr_lookahead -> lr1_item Q
  | LRFinal : Q -> lr_lookahead -> lr1_item Q.

  Arguments LRState {Q} _ _.
  Arguments LRBefore {Q} _ _ _ _.
  Arguments LRAfterSymbol {Q} _ _ _ _.
  Arguments LRComplete {Q} _ _ _ _.
  Arguments LRFinal {Q} _ _.

  Definition eqb_of_dec {B : Type}
      (dec : forall x y : B, {x = y} + {x <> y}) (x y : B) : bool :=
    if dec x y then true else false.

  Lemma eqb_of_dec_sound :
    forall {B : Type} (dec : forall x y : B, {x = y} + {x <> y}) x y,
      eqb_of_dec dec x y = true -> x = y.
  Proof.
    intros B dec x y H.
    unfold eqb_of_dec in H.
    destruct (dec x y); auto; discriminate.
  Qed.

  Lemma eqb_of_dec_complete :
    forall {B : Type} (dec : forall x y : B, {x = y} + {x <> y}) x y,
      x = y -> eqb_of_dec dec x y = true.
  Proof.
    intros B dec x y H.
    subst y. unfold eqb_of_dec.
    destruct (dec x x); auto; contradiction.
  Qed.

  Definition enfa_state_eq_dec (m : @finite_enfa A)
      : forall x y : enfa_state (fenfa_base m), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct (fenfa_state_eqb m x y) eqn:Heq.
    - left. now apply fenfa_state_eqb_sound.
    - right. intro Hxy.
      apply fenfa_state_eqb_complete in Hxy.
      rewrite Hxy in Heq. discriminate.
  Defined.

  Definition lr_lookahead_eq_dec
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      : forall x y : lr_lookahead, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Defined.

  Definition lr_symbol_eq_dec
      {Q : Type}
      (Q_eq_dec : forall x y : Q, {x = y} + {x <> y})
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      : forall x y : lr_symbol Q, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Defined.

  Definition lr1_item_eq_dec
      {Q : Type}
      (Q_eq_dec : forall x y : Q, {x = y} + {x <> y})
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      : forall x y : lr1_item Q, {x = y} + {x <> y}.
  Proof.
    decide equality;
      try apply Q_eq_dec;
      try apply lr_lookahead_eq_dec; try exact A_eq_dec;
      try apply lr_symbol_eq_dec; try assumption.
  Defined.

  Definition lr_symbol_of_label {Q : Type} (l : option A) : lr_symbol Q :=
    match l with
    | None => LREpsilon
    | Some a => LRTerm a
    end.

  Definition enfa_transition_edges (m : @finite_enfa A)
      : list (enfa_state (fenfa_base m) * option A *
              enfa_state (fenfa_base m)) :=
    concat
      (map
         (fun p =>
            map (fun q => (p, None, q))
              (enfa_step (fenfa_base m) p None) ++
            concat
              (map
                 (fun a =>
                    map (fun q => (p, Some a, q))
                      (enfa_step (fenfa_base m) p (Some a)))
                 (fenfa_alphabet m)))
         (fenfa_states m)).

  Definition lr1_lookaheads (m : @finite_enfa A) : list lr_lookahead :=
    [LAEpsilon; LAEndLeft; LAEndRight] ++ map LATerm (fenfa_alphabet m).

  (** Theorem 6 state-set decomposition.  Reduce items include completed
      transition items and final items; nonreduce items include automaton state
      items and intermediate transition-gadget items. *)
  Definition lr1_reduce_items (m : @finite_enfa A)
      : list (lr1_item (enfa_state (fenfa_base m))) :=
    concat
      (map
         (fun la =>
            map
              (fun e =>
                 match e with
                 | (p, l, q) => LRComplete p (lr_symbol_of_label l) q la
                 end)
              (enfa_transition_edges m) ++
            map (fun q => LRFinal q la) (enfa_final_states m))
         (lr1_lookaheads m)).

  Definition lr1_nonreduce_items (m : @finite_enfa A)
      : list (lr1_item (enfa_state (fenfa_base m))) :=
    concat
      (map
         (fun la =>
            map (fun p => LRState p la) (fenfa_states m) ++
            concat
              (map
                 (fun e =>
                    match e with
                    | (p, l, q) =>
                        [ LRBefore p (lr_symbol_of_label l) q la;
                          LRAfterSymbol p (lr_symbol_of_label l) q la ]
                    end)
                 (enfa_transition_edges m)))
         (lr1_lookaheads m)).

  Definition lr1_items (m : @finite_enfa A)
      : list (lr1_item (enfa_state (fenfa_base m))) :=
    lr1_reduce_items m ++ lr1_nonreduce_items m.

  Definition lr1_start_item_spec
      (m : @finite_enfa A)
      (it : lr1_item (enfa_state (fenfa_base m))) : Prop :=
    exists s,
      In s (enfa_start (fenfa_base m)) /\
      it = LRState s LAEpsilon.

  Definition lr1_final_item_spec
      (m : @finite_enfa A)
      (it : lr1_item (enfa_state (fenfa_base m))) : Prop :=
    In it (lr1_reduce_items m).

  Definition lr1_alphabet_symbol_spec
      (m : @finite_enfa A)
      (x : lr_symbol (enfa_state (fenfa_base m))) : Prop :=
    x = LREpsilon \/
    x = LREndLeft \/
    x = LREndRight \/
    (exists a, In a (fenfa_alphabet m) /\ x = LRTerm a) \/
    (exists q, In q (fenfa_states m) /\ x = LRNonterm q).

  (** Theorem 6 membership specs.  These predicates unfold the list
      constructions into the paper-level descriptions of reduce/nonreduce
      items, start/final items, and alphabet symbols. *)
  Definition lr1_reduce_item_spec
      (m : @finite_enfa A)
      (it : lr1_item (enfa_state (fenfa_base m))) : Prop :=
    exists la,
      In la (lr1_lookaheads m) /\
      ((exists p l q,
          In (p, l, q) (enfa_transition_edges m) /\
          it = LRComplete p (lr_symbol_of_label l) q la) \/
       (exists q,
          In q (enfa_final_states m) /\
          it = LRFinal q la)).

  Definition lr1_nonreduce_item_spec
      (m : @finite_enfa A)
      (it : lr1_item (enfa_state (fenfa_base m))) : Prop :=
    exists la,
      In la (lr1_lookaheads m) /\
      ((exists p,
          In p (fenfa_states m) /\
          it = LRState p la) \/
       (exists p l q,
          In (p, l, q) (enfa_transition_edges m) /\
          (it = LRBefore p (lr_symbol_of_label l) q la \/
           it = LRAfterSymbol p (lr_symbol_of_label l) q la))).

  (** Theorem 6 transition specs.  Reduce transitions are epsilon control
      edges; shift transitions read terminal or nonterminal symbols. *)
  Definition lr1_reduce_transitions (m : @finite_enfa A)
      : list (lr1_item (enfa_state (fenfa_base m)) *
              option (lr_symbol (enfa_state (fenfa_base m))) *
              lr1_item (enfa_state (fenfa_base m))) :=
    concat
      (map
         (fun la =>
            concat
              (map
                 (fun e =>
                    match e with
                    | (p, l, q) =>
                        [ (LRState p la, None,
                           LRBefore p (lr_symbol_of_label l) q la);
                          (LRAfterSymbol p (lr_symbol_of_label l) q la,
                           None, LRState q la) ]
                    end)
                 (enfa_transition_edges m)))
         (lr1_lookaheads m)).

  Definition lr1_shift_transitions (m : @finite_enfa A)
      : list (lr1_item (enfa_state (fenfa_base m)) *
              option (lr_symbol (enfa_state (fenfa_base m))) *
              lr1_item (enfa_state (fenfa_base m))) :=
    concat
      (map
         (fun la =>
            concat
              (map
                 (fun e =>
                    match e with
                    | (p, l, q) =>
                        let x := lr_symbol_of_label l in
                        [ (LRBefore p x q la, Some x,
                           LRAfterSymbol p x q la);
                          (LRAfterSymbol p x q la, Some (LRNonterm q),
                           LRComplete p x q la) ]
                    end)
                 (enfa_transition_edges m)))
         (lr1_lookaheads m)).

  Definition lr1_transitions (m : @finite_enfa A) :=
    lr1_reduce_transitions m ++ lr1_shift_transitions m.

  Definition lr1_reduce_transition_spec
      (m : @finite_enfa A)
      (tr : lr1_item (enfa_state (fenfa_base m)) *
            option (lr_symbol (enfa_state (fenfa_base m))) *
            lr1_item (enfa_state (fenfa_base m))) : Prop :=
    exists la p l q,
      In la (lr1_lookaheads m) /\
      In (p, l, q) (enfa_transition_edges m) /\
      (tr =
         (LRState p la, None, LRBefore p (lr_symbol_of_label l) q la) \/
       tr =
         (LRAfterSymbol p (lr_symbol_of_label l) q la,
          None, LRState q la)).

  Definition lr1_shift_transition_spec
      (m : @finite_enfa A)
      (tr : lr1_item (enfa_state (fenfa_base m)) *
            option (lr_symbol (enfa_state (fenfa_base m))) *
            lr1_item (enfa_state (fenfa_base m))) : Prop :=
    exists la p l q,
      In la (lr1_lookaheads m) /\
      In (p, l, q) (enfa_transition_edges m) /\
      (tr =
         (LRBefore p (lr_symbol_of_label l) q la,
          Some (lr_symbol_of_label l),
          LRAfterSymbol p (lr_symbol_of_label l) q la) \/
       tr =
         (LRAfterSymbol p (lr_symbol_of_label l) q la,
          Some (LRNonterm q),
          LRComplete p (lr_symbol_of_label l) q la)).

  Definition lr1_step
      (m : @finite_enfa A)
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (p : lr1_item (enfa_state (fenfa_base m)))
      (l : option (lr_symbol (enfa_state (fenfa_base m))))
      : list (lr1_item (enfa_state (fenfa_base m))) :=
    let item_dec := lr1_item_eq_dec (enfa_state_eq_dec m) A_eq_dec in
    let symbol_dec := lr_symbol_eq_dec (enfa_state_eq_dec m) A_eq_dec in
    nodup item_dec
      (map
         (fun t => match t with (_, _, q) => q end)
         (filter
            (fun t =>
               match t with
               | (p0, l0, _) =>
                   eqb_of_dec item_dec p p0 &&
                   match l, l0 with
                   | None, None => true
                   | Some x, Some y => eqb_of_dec symbol_dec x y
                   | _, _ => false
                   end
               end)
            (lr1_transitions m))).

  Record lr1_machine (Q : Type) : Type := {
    lr1_enfa : @finite_enfa (lr_symbol Q);
    lr1_reduce_states : list (enfa_state (fenfa_base lr1_enfa));
    lr1_nonreduce_states : list (enfa_state (fenfa_base lr1_enfa));
    lr1_reduce_states_spec :
      fenfa_states lr1_enfa = lr1_reduce_states ++ lr1_nonreduce_states
  }.

  (** Normalized LR(1) machine for Theorem 6.  The states, alphabet,
      transitions, and reduce set are generated explicitly from the source
      ENFA for the counting relation.  The later [lr1_closure]/[lr1_goto]/
      [lr1_canonical_collection] definitions provide the Gamma-specific
      canonical item-set generator. *)
  Definition lr1_machine_of_enfa
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      : lr1_machine (enfa_state (fenfa_base m)) :=
    {|
      lr1_enfa :=
        {|
          fenfa_base :=
            {|
              enfa_state := lr1_item (enfa_state (fenfa_base m));
              enfa_start :=
                concat
                  (map
                     (fun s => map (fun la => LRState s la) [LAEpsilon])
                     (enfa_start (fenfa_base m)));
              enfa_final :=
                fun q =>
                  existsb
                    (eqb_of_dec
                       (lr1_item_eq_dec (enfa_state_eq_dec m) A_eq_dec) q)
                    (lr1_reduce_items m);
              enfa_step := lr1_step m A_eq_dec
            |};
          fenfa_states := lr1_items m;
          fenfa_alphabet :=
            [LREpsilon; LREndLeft; LREndRight] ++
            map LRTerm (fenfa_alphabet m) ++
            map LRNonterm (fenfa_states m);
          fenfa_state_eqb :=
            eqb_of_dec (lr1_item_eq_dec (enfa_state_eq_dec m) A_eq_dec);
          fenfa_state_eqb_sound :=
            eqb_of_dec_sound (lr1_item_eq_dec (enfa_state_eq_dec m) A_eq_dec);
          fenfa_state_eqb_complete :=
            eqb_of_dec_complete (lr1_item_eq_dec (enfa_state_eq_dec m) A_eq_dec)
        |};
      lr1_reduce_states := lr1_reduce_items m;
      lr1_nonreduce_states := lr1_nonreduce_items m;
      lr1_reduce_states_spec := eq_refl
    |}.

  (** Gamma-specific canonical LR(1) item-set construction.  Closure expands
      state items into available production items and adds final reduce items
      [q -> epsilon]; goto advances over terminal symbols and nonterminal
      states.  The canonical collection closes the item-set graph with finite
      fuel as the interface for the Gamma LR(1) bridge. *)
  Definition lr1_item_set (m : @finite_enfa A) : Type :=
    list (lr1_item (enfa_state (fenfa_base m))).

  Definition lr1_item_memberb
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (it : lr1_item (enfa_state (fenfa_base m)))
      (xs : lr1_item_set m) : bool :=
    existsb
      (eqb_of_dec (lr1_item_eq_dec (enfa_state_eq_dec m) A_eq_dec) it)
      xs.

  Definition lr1_normalize_item_set
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m) : lr1_item_set m :=
    nodup (lr1_item_eq_dec (enfa_state_eq_dec m) A_eq_dec) xs.

  Definition lr1_item_set_subsetb
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs ys : lr1_item_set m) : bool :=
    forallb (fun it => lr1_item_memberb A_eq_dec m it ys) xs.

  Definition lr1_item_set_eqb
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs ys : lr1_item_set m) : bool :=
    lr1_item_set_subsetb A_eq_dec m xs ys &&
    lr1_item_set_subsetb A_eq_dec m ys xs.

  Definition lr1_nonempty_item_set {m : @finite_enfa A}
      (xs : lr1_item_set m) : bool :=
    match xs with
    | [] => false
    | _ :: _ => true
    end.

  Definition lr1_closure_additions
      (m : @finite_enfa A)
      (it : lr1_item (enfa_state (fenfa_base m)))
      : lr1_item_set m :=
    match it with
    | LRState p la =>
        concat
          (map
             (fun e =>
                match e with
                | (p0, l, q) =>
                    if fenfa_state_eqb m p p0
                    then [LRBefore p (lr_symbol_of_label l) q la]
                    else []
                end)
             (enfa_transition_edges m)) ++
        if enfa_final (fenfa_base m) p
        then [LRFinal p la]
        else []
    | LRAfterSymbol _ _ q la => [LRState q la]
    | _ => []
    end.

  Definition lr1_closure_step
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m) : lr1_item_set m :=
    lr1_normalize_item_set A_eq_dec m
      (xs ++ concat (map (lr1_closure_additions m) xs)).

  Fixpoint lr1_closure_fuel
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (fuel : nat)
      (xs : lr1_item_set m) : lr1_item_set m :=
    match fuel with
    | O => lr1_normalize_item_set A_eq_dec m xs
    | S fuel' =>
        let xs' := lr1_closure_step A_eq_dec m xs in
        if lr1_item_set_eqb A_eq_dec m xs xs'
        then xs'
        else lr1_closure_fuel A_eq_dec m fuel' xs'
    end.

  Definition lr1_closure
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m) : lr1_item_set m :=
    lr1_closure_fuel A_eq_dec m (length (lr1_items m)) xs.

  Definition lr1_shift_targets
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (x : lr_symbol (enfa_state (fenfa_base m)))
      (it : lr1_item (enfa_state (fenfa_base m)))
      : lr1_item_set m :=
    match it with
    | LRBefore p y q la =>
        if eqb_of_dec (lr_symbol_eq_dec (enfa_state_eq_dec m) A_eq_dec) x y
        then [LRAfterSymbol p y q la]
        else []
    | LRAfterSymbol p y q la =>
        match x with
        | LRNonterm q' =>
            if fenfa_state_eqb m q q'
            then [LRComplete p y q la]
            else []
        | _ => []
        end
    | _ => []
    end.

  Definition lr1_successor_symbols (m : @finite_enfa A)
      : list (lr_symbol (enfa_state (fenfa_base m))) :=
    [LREpsilon; LREndLeft; LREndRight] ++
    map LRTerm (fenfa_alphabet m) ++
    map LRNonterm (fenfa_states m).

  Definition lr1_goto
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m)
      (x : lr_symbol (enfa_state (fenfa_base m))) : lr1_item_set m :=
    lr1_closure A_eq_dec m
      (concat (map (lr1_shift_targets A_eq_dec m x) xs)).

  Definition lr1_initial_item_set
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : lr1_item_set m :=
    lr1_closure A_eq_dec m [LRState s LAEpsilon].

  Definition lr1_item_set_memberb
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m)
      (xss : list (lr1_item_set m)) : bool :=
    existsb (lr1_item_set_eqb A_eq_dec m xs) xss.

  Definition lr1_add_item_set
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m)
      (xss : list (lr1_item_set m)) : list (lr1_item_set m) :=
    if lr1_item_set_memberb A_eq_dec m xs xss then xss else xs :: xss.

  Definition lr1_successor_item_sets
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m) : list (lr1_item_set m) :=
    filter lr1_nonempty_item_set
      (map (lr1_goto A_eq_dec m xs) (lr1_successor_symbols m)).

  Fixpoint pow2 (n : nat) : nat :=
    match n with
    | O => 1
    | S n' => 2 * pow2 n'
    end.

  Fixpoint lr1_canonical_collection_fuel
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (fuel : nat)
      (xss : list (lr1_item_set m)) : list (lr1_item_set m) :=
    match fuel with
    | O => xss
    | S fuel' =>
        let next := concat (map (lr1_successor_item_sets A_eq_dec m) xss) in
        let xss' :=
          fold_right (lr1_add_item_set A_eq_dec m) xss next in
        if forallb
             (fun xs => lr1_item_set_memberb A_eq_dec m xs xss)
             xss'
        then xss'
        else lr1_canonical_collection_fuel A_eq_dec m fuel' xss'
    end.

  Definition lr1_canonical_collection
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : list (lr1_item_set m) :=
    lr1_canonical_collection_fuel A_eq_dec m (pow2 (length (lr1_items m)))
      [lr1_initial_item_set A_eq_dec m s].

  Definition lr_symbol_terminal_word
      {Q : Type} (x : lr_symbol Q) : list A :=
    match x with
    | LRTerm a => [a]
    | _ => []
    end.

  Inductive lr1_reachable_item_set
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m))
      : list A -> lr1_item_set m -> Prop :=
  | LR1Reach_initial :
      lr1_reachable_item_set A_eq_dec m s []
        (lr1_initial_item_set A_eq_dec m s)
  | LR1Reach_goto :
      forall w xs x,
        lr1_reachable_item_set A_eq_dec m s w xs ->
        In x (lr1_successor_symbols m) ->
        lr1_nonempty_item_set (lr1_goto A_eq_dec m xs x) = true ->
        lr1_reachable_item_set A_eq_dec m s
          (w ++ lr_symbol_terminal_word x)
          (lr1_goto A_eq_dec m xs x).

  Definition lr1_reduce_item_memberb
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (it : lr1_item (enfa_state (fenfa_base m))) : bool :=
    lr1_item_memberb A_eq_dec m it (lr1_reduce_items m).

  Definition lr1_reduce_items_in_set
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m) : lr1_item_set m :=
    filter (lr1_reduce_item_memberb A_eq_dec m) xs.

  Definition lr1_reduce_lookahead
      {Q : Type} (it : lr1_item Q) : option lr_lookahead :=
    match it with
    | LRComplete _ _ _ la => Some la
    | LRFinal _ la => Some la
    | _ => None
    end.

  Definition lr1_same_lookahead_reduce_conflict
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m) : Prop :=
    exists it1 it2 la,
      In it1 xs /\
      In it2 xs /\
      lr1_reduce_item_memberb A_eq_dec m it1 = true /\
      lr1_reduce_item_memberb A_eq_dec m it2 = true /\
      lr1_reduce_lookahead it1 = Some la /\
      lr1_reduce_lookahead it2 = Some la /\
      it1 <> it2.

  Definition lr1_item_set_reduce_conflict_free
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (xs : lr1_item_set m) : Prop :=
    forall it1 it2 la,
      In it1 xs ->
      In it2 xs ->
      lr1_reduce_item_memberb A_eq_dec m it1 = true ->
      lr1_reduce_item_memberb A_eq_dec m it2 = true ->
      lr1_reduce_lookahead it1 = Some la ->
      lr1_reduce_lookahead it2 = Some la ->
      it1 = it2.

  Definition lr1_canonical_collection_conflict_free
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    forall xs,
      In xs (lr1_canonical_collection A_eq_dec m s) ->
      lr1_item_set_reduce_conflict_free A_eq_dec m xs.

  Theorem lr1_item_memberb_iff :
    forall A_eq_dec (m : @finite_enfa A) it xs,
      lr1_item_memberb A_eq_dec m it xs = true <-> In it xs.
  Proof.
    intros A_eq_dec m it xs.
    unfold lr1_item_memberb.
    split; intros H.
    - apply existsb_exists in H as [it' [Hin Heq]].
      apply eqb_of_dec_sound in Heq. subst it'. exact Hin.
    - apply existsb_exists.
      exists it. split; [exact H |].
      apply eqb_of_dec_complete. reflexivity.
  Qed.

  Theorem lr1_item_set_subsetb_iff :
    forall A_eq_dec (m : @finite_enfa A) xs ys,
      lr1_item_set_subsetb A_eq_dec m xs ys = true <->
      incl xs ys.
  Proof.
    intros A_eq_dec m xs ys.
    unfold lr1_item_set_subsetb.
    split; intros H.
    - rewrite forallb_forall in H.
      intros it Hin.
      apply (proj1 (lr1_item_memberb_iff A_eq_dec m it ys)).
      now apply H.
    - rewrite forallb_forall.
      intros it Hin.
      apply (proj2 (lr1_item_memberb_iff A_eq_dec m it ys)).
      now apply H.
  Qed.

  Theorem lr1_item_set_eqb_iff :
    forall A_eq_dec (m : @finite_enfa A) xs ys,
      lr1_item_set_eqb A_eq_dec m xs ys = true <->
      (forall it, In it xs <-> In it ys).
  Proof.
    intros A_eq_dec m xs ys.
    unfold lr1_item_set_eqb.
    rewrite andb_true_iff.
    rewrite !lr1_item_set_subsetb_iff.
    split.
    - intros [Hxy Hyx] it. split; [apply Hxy | apply Hyx].
    - intro H.
      split.
      + intros it Hin. now apply (proj1 (H it)).
      + intros it Hin. now apply (proj2 (H it)).
  Qed.

  Theorem lr1_item_set_memberb_iff :
    forall A_eq_dec (m : @finite_enfa A) xs xss,
      lr1_item_set_memberb A_eq_dec m xs xss = true <->
      exists ys, In ys xss /\ forall it, In it xs <-> In it ys.
  Proof.
    intros A_eq_dec m xs xss.
    unfold lr1_item_set_memberb.
    split; intros H.
    - apply existsb_exists in H as [ys [Hin Heq]].
      pose proof
        (proj1 (lr1_item_set_eqb_iff A_eq_dec m xs ys) Heq)
        as Hequiv.
      exists ys. auto.
    - destruct H as [ys [Hin Heq]].
      apply existsb_exists.
      exists ys. split; [exact Hin |].
      apply (proj2 (lr1_item_set_eqb_iff A_eq_dec m xs ys)).
      exact Heq.
  Qed.

  Theorem lr1_normalize_item_set_In :
    forall A_eq_dec (m : @finite_enfa A) it xs,
      In it (lr1_normalize_item_set A_eq_dec m xs) <-> In it xs.
  Proof.
    intros A_eq_dec m it xs.
    unfold lr1_normalize_item_set.
    rewrite nodup_In. reflexivity.
  Qed.

  Theorem lr1_closure_fuel_contains_seed :
    forall A_eq_dec (m : @finite_enfa A) fuel xs it,
      In it xs ->
      In it (lr1_closure_fuel A_eq_dec m fuel xs).
  Proof.
    intros A_eq_dec m fuel.
    induction fuel as [| fuel IH]; intros xs it Hin; simpl.
    - apply lr1_normalize_item_set_In. exact Hin.
    - set (xs' := lr1_closure_step A_eq_dec m xs).
      assert (Hin' : In it xs').
      {
        unfold xs', lr1_closure_step.
        apply lr1_normalize_item_set_In.
        apply in_or_app. left. exact Hin.
      }
      destruct (lr1_item_set_eqb A_eq_dec m xs xs'); auto.
  Qed.

  Theorem lr1_closure_contains_seed :
    forall A_eq_dec (m : @finite_enfa A) xs it,
      In it xs ->
      In it (lr1_closure A_eq_dec m xs).
  Proof.
    intros A_eq_dec m xs it Hin.
    unfold lr1_closure.
    now apply lr1_closure_fuel_contains_seed.
  Qed.

  Theorem lr1_initial_item_set_contains_start :
    forall A_eq_dec (m : @finite_enfa A) s,
      In (LRState s LAEpsilon) (lr1_initial_item_set A_eq_dec m s).
  Proof.
    intros A_eq_dec m s.
    unfold lr1_initial_item_set.
    apply lr1_closure_contains_seed. simpl. auto.
  Qed.

  Theorem lr1_goto_contains_shift_target :
    forall A_eq_dec (m : @finite_enfa A) xs x it it',
      In it xs ->
      In it' (lr1_shift_targets A_eq_dec m x it) ->
      In it' (lr1_goto A_eq_dec m xs x).
  Proof.
    intros A_eq_dec m xs x it it' Hit Htarget.
    unfold lr1_goto.
    apply lr1_closure_contains_seed.
    apply in_concat.
    exists (lr1_shift_targets A_eq_dec m x it).
    split.
    - apply in_map_iff. exists it. auto.
    - exact Htarget.
  Qed.

  Theorem lr1_item_set_reduce_conflict_free_iff_no_conflict :
    forall A_eq_dec (m : @finite_enfa A) xs,
      lr1_item_set_reduce_conflict_free A_eq_dec m xs <->
      ~ lr1_same_lookahead_reduce_conflict A_eq_dec m xs.
  Proof.
    intros A_eq_dec m xs.
    unfold lr1_item_set_reduce_conflict_free,
      lr1_same_lookahead_reduce_conflict.
    split.
    - intros Hfree [it1 [it2 [la
        [Hin1 [Hin2 [Hred1 [Hred2 [Hla1 [Hla2 Hneq]]]]]]]]].
      apply Hneq.
      eapply Hfree; eauto.
    - intros Hno it1 it2 la Hin1 Hin2 Hred1 Hred2 Hla1 Hla2.
      destruct (lr1_item_eq_dec (enfa_state_eq_dec m) A_eq_dec it1 it2)
        as [Heq | Hneq]; [exact Heq |].
      exfalso. apply Hno.
      exists it1, it2, la.
      repeat split; auto.
  Qed.

  Lemma sum_nats_app :
    forall xs ys, sum_nats (xs ++ ys) = sum_nats xs + sum_nats ys.
  Proof.
    induction xs as [| x xs IH]; intros ys; simpl.
    - reflexivity.
    - rewrite IH. lia.
  Qed.

  (** Theorem 7 counting interface.  [lr1_conflict_count] sums prime reach
      counts over reduce states; [lr1_leaf_count] uses the underlying ENFA
      prime leaf count. *)
  Definition lr1_conflict_count
      {Q : Type} (M : lr1_machine Q)
      (w : list (lr_symbol Q)) : nat :=
    sum_nats
      (map
         (enfa_maximal_simple_reach_count (lr1_enfa Q M) w)
         (lr1_reduce_states Q M)).

  Definition lr1_leaf_count
      {Q : Type} (M : lr1_machine Q)
      (w : list (lr_symbol Q)) : nat :=
    enfa_leaf_prime_word (lr1_enfa Q M) w.

  Definition lr1_conflict_free {Q : Type} (M : lr1_machine Q) : Prop :=
    forall w, lr1_conflict_count M w <= 1.

  Definition gamma_lr1_conflict_count_spec
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A) : Prop :=
    lr1_conflict_free (lr1_machine_of_enfa A_eq_dec m).

  (** Definition 10 basic machine characterization: the reduce/nonreduce
      states and full state list of [lr1_machine_of_enfa] are exactly the item
      sets generated from the ENFA above. *)
  Theorem section4_definition10_lr1_machine_characterization :
    forall A_eq_dec (m : @finite_enfa A),
      lr1_reduce_states _ (lr1_machine_of_enfa A_eq_dec m) =
        lr1_reduce_items m /\
      lr1_nonreduce_states _ (lr1_machine_of_enfa A_eq_dec m) =
        lr1_nonreduce_items m /\
      fenfa_states (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m)) =
        lr1_reduce_items m ++ lr1_nonreduce_items m.
  Proof.
    intros. repeat split; reflexivity.
  Qed.

  (** Definition 10 unfolded specs.  The following membership theorems
      characterize start/final/alphabet entries, reduce/nonreduce items,
      reduce/shift transitions, and the step function. *)
  Theorem section4_definition10_start_state_membership :
    forall A_eq_dec (m : @finite_enfa A) it,
      In it
        (enfa_start
           (fenfa_base
              (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m)))) <->
      lr1_start_item_spec m it.
  Proof.
    intros A_eq_dec m it. unfold lr1_start_item_spec.
    simpl.
    split; intros H.
    - apply in_concat in H as [xs [Hxs Hit]].
      apply in_map_iff in Hxs as [s [Hxs Hs]]. subst xs.
      simpl in Hit. destruct Hit as [Hit | []].
      exists s. split; auto.
    - destruct H as [s [Hs Hit]]. subst it.
      apply in_concat.
      exists [LRState s LAEpsilon]. split.
      + apply in_map_iff. exists s. split; [reflexivity | exact Hs].
      + simpl. auto.
  Qed.

  Theorem section4_definition10_final_state_membership :
    forall A_eq_dec (m : @finite_enfa A) it,
      enfa_final
        (fenfa_base (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m))) it =
        true <->
      lr1_final_item_spec m it.
  Proof.
    intros A_eq_dec m it.
    unfold lr1_final_item_spec. simpl.
    split; intros H.
    - apply existsb_exists in H as [q [Hq Heq]].
      apply eqb_of_dec_sound in Heq. subst q. exact Hq.
    - apply existsb_exists.
      exists it. split; [exact H |].
      apply eqb_of_dec_complete. reflexivity.
  Qed.

  Theorem section4_definition10_alphabet_membership :
    forall A_eq_dec (m : @finite_enfa A) x,
      In x (fenfa_alphabet
        (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m))) <->
      lr1_alphabet_symbol_spec m x.
  Proof.
    intros A_eq_dec m x. unfold lr1_alphabet_symbol_spec. simpl.
    split; intros H.
    - destruct H as [H | [H | [H | Htail]]]; subst; auto.
      apply in_app_or in Htail as [Hterm | Hnonterm].
      + apply in_map_iff in Hterm as [a [Hx Ha]]. subst x.
        right; right; right; left. exists a. auto.
      + apply in_map_iff in Hnonterm as [q [Hx Hq]]. subst x.
        right; right; right; right. exists q. auto.
    - destruct H as [H | [H | [H | H]]].
      + subst x. auto.
      + subst x. auto.
      + subst x. auto.
      + destruct H as [[a [Ha H]] | [q [Hq H]]]; subst.
        * right; right; right. apply in_or_app. left.
          apply in_map_iff. exists a. auto.
        * right; right; right. apply in_or_app. right.
          apply in_map_iff. exists q. auto.
  Qed.

  Theorem section4_definition10_reduce_item_membership :
    forall (m : @finite_enfa A) it,
      In it (lr1_reduce_items m) <-> lr1_reduce_item_spec m it.
  Proof.
    intros m it. unfold lr1_reduce_items, lr1_reduce_item_spec.
    split; intros H.
    - apply in_concat in H as [xs [Hxs Hit]].
      apply in_map_iff in Hxs as [la [Hxs Hla]]. subst xs.
      exists la. split; [exact Hla |].
      apply in_app_or in Hit as [Hit | Hit].
      + left.
        apply in_map_iff in Hit as [[[p l] q] [Hit Hedge]].
        inversion Hit; subst.
        exists p, l, q. split; auto.
      + right.
        apply in_map_iff in Hit as [q [Hit Hq]].
        inversion Hit; subst.
        exists q. split; auto.
    - destruct H as [la [Hla [[p [l [q [Hedge Hit]]]] | [q [Hq Hit]]]]];
        subst it.
      + apply in_concat.
        exists
          (map
             (fun e =>
                match e with
                | (p, l, q) => LRComplete p (lr_symbol_of_label l) q la
                end)
             (enfa_transition_edges m) ++
           map (fun q => LRFinal q la) (enfa_final_states m)).
        split.
        * apply in_map_iff. exists la. split; reflexivity || exact Hla.
        * apply in_or_app. left.
          apply in_map_iff. exists (p, l, q). split; auto.
      + apply in_concat.
        exists
          (map
             (fun e =>
                match e with
                | (p, l, q) => LRComplete p (lr_symbol_of_label l) q la
                end)
             (enfa_transition_edges m) ++
           map (fun q => LRFinal q la) (enfa_final_states m)).
        split.
        * apply in_map_iff. exists la. split; reflexivity || exact Hla.
        * apply in_or_app. right.
          apply in_map_iff. exists q. split; auto.
  Qed.

  Theorem section4_definition10_nonreduce_item_membership :
    forall (m : @finite_enfa A) it,
      In it (lr1_nonreduce_items m) <-> lr1_nonreduce_item_spec m it.
  Proof.
    intros m it. unfold lr1_nonreduce_items, lr1_nonreduce_item_spec.
    split; intros H.
    - apply in_concat in H as [xs [Hxs Hit]].
      apply in_map_iff in Hxs as [la [Hxs Hla]]. subst xs.
      exists la. split; [exact Hla |].
      apply in_app_or in Hit as [Hit | Hit].
      + left.
        apply in_map_iff in Hit as [p [Hit Hp]].
        inversion Hit; subst.
        exists p. split; auto.
      + right.
        apply in_concat in Hit as [ys [Hys Hit]].
        apply in_map_iff in Hys as [[[p l] q] [Hys Hedge]].
        subst ys.
        simpl in Hit.
        destruct Hit as [Hit | [Hit | []]];
          inversion Hit; subst;
          exists p, l, q; split; auto.
    - destruct H as [la [Hla [[p [Hp Hit]] |
        [p [l [q [Hedge [Hit | Hit]]]]]]]]; subst it.
      + apply in_concat.
        exists
          (map (fun p => LRState p la) (fenfa_states m) ++
           concat
             (map
                (fun e =>
                   match e with
                   | (p, l, q) =>
                       [LRBefore p (lr_symbol_of_label l) q la;
                        LRAfterSymbol p (lr_symbol_of_label l) q la]
                   end)
                (enfa_transition_edges m))).
        split.
        * apply in_map_iff. exists la. split; reflexivity || exact Hla.
        * apply in_or_app. left.
          apply in_map_iff. exists p. split; auto.
      + apply in_concat.
        exists
          (map (fun p => LRState p la) (fenfa_states m) ++
           concat
             (map
                (fun e =>
                   match e with
                   | (p, l, q) =>
                       [LRBefore p (lr_symbol_of_label l) q la;
                        LRAfterSymbol p (lr_symbol_of_label l) q la]
                   end)
                (enfa_transition_edges m))).
        split.
        * apply in_map_iff. exists la. split; reflexivity || exact Hla.
        * apply in_or_app. right.
          apply in_concat.
          exists
            [LRBefore p (lr_symbol_of_label l) q la;
             LRAfterSymbol p (lr_symbol_of_label l) q la].
          split.
          -- apply in_map_iff. exists (p, l, q). split; auto.
          -- simpl. auto.
      + apply in_concat.
        exists
          (map (fun p => LRState p la) (fenfa_states m) ++
           concat
             (map
                (fun e =>
                   match e with
                   | (p, l, q) =>
                       [LRBefore p (lr_symbol_of_label l) q la;
                        LRAfterSymbol p (lr_symbol_of_label l) q la]
                   end)
                (enfa_transition_edges m))).
        split.
        * apply in_map_iff. exists la. split; reflexivity || exact Hla.
        * apply in_or_app. right.
          apply in_concat.
          exists
            [LRBefore p (lr_symbol_of_label l) q la;
             LRAfterSymbol p (lr_symbol_of_label l) q la].
          split.
          -- apply in_map_iff. exists (p, l, q). split; auto.
          -- simpl. auto.
  Qed.

  Theorem section4_definition10_reduce_transition_membership :
    forall (m : @finite_enfa A) tr,
      In tr (lr1_reduce_transitions m) <->
      lr1_reduce_transition_spec m tr.
  Proof.
    intros m tr. unfold lr1_reduce_transitions, lr1_reduce_transition_spec.
    split; intros H.
    - apply in_concat in H as [xs [Hxs Htr]].
      apply in_map_iff in Hxs as [la [Hxs Hla]]. subst xs.
      apply in_concat in Htr as [ys [Hys Htr]].
      apply in_map_iff in Hys as [[[p l] q] [Hys Hedge]].
      subst ys.
      simpl in Htr.
      destruct Htr as [Htr | [Htr | []]];
        inversion Htr; subst;
        exists la, p, l, q; repeat split; auto.
    - destruct H as [la [p [l [q [Hla [Hedge [Htr | Htr]]]]]]]; subst tr.
      + apply in_concat.
        exists
          (concat
             (map
                (fun e =>
                   match e with
                   | (p, l, q) =>
                       [(LRState p la, None,
                         LRBefore p (lr_symbol_of_label l) q la);
                        (LRAfterSymbol p (lr_symbol_of_label l) q la,
                         None, LRState q la)]
                   end)
                (enfa_transition_edges m))).
        split.
        * apply in_map_iff. exists la. split; reflexivity || exact Hla.
        * apply in_concat.
          exists
            [(LRState p la, None,
              LRBefore p (lr_symbol_of_label l) q la);
             (LRAfterSymbol p (lr_symbol_of_label l) q la,
              None, LRState q la)].
          split.
          -- apply in_map_iff. exists (p, l, q). split; auto.
          -- simpl. auto.
      + apply in_concat.
        exists
          (concat
             (map
                (fun e =>
                   match e with
                   | (p, l, q) =>
                       [(LRState p la, None,
                         LRBefore p (lr_symbol_of_label l) q la);
                        (LRAfterSymbol p (lr_symbol_of_label l) q la,
                         None, LRState q la)]
                   end)
                (enfa_transition_edges m))).
        split.
        * apply in_map_iff. exists la. split; reflexivity || exact Hla.
        * apply in_concat.
          exists
            [(LRState p la, None,
              LRBefore p (lr_symbol_of_label l) q la);
             (LRAfterSymbol p (lr_symbol_of_label l) q la,
              None, LRState q la)].
          split.
          -- apply in_map_iff. exists (p, l, q). split; auto.
          -- simpl. auto.
  Qed.

  Theorem section4_definition10_shift_transition_membership :
    forall (m : @finite_enfa A) tr,
      In tr (lr1_shift_transitions m) <->
      lr1_shift_transition_spec m tr.
  Proof.
    intros m tr. unfold lr1_shift_transitions, lr1_shift_transition_spec.
    split; intros H.
    - apply in_concat in H as [xs [Hxs Htr]].
      apply in_map_iff in Hxs as [la [Hxs Hla]]. subst xs.
      apply in_concat in Htr as [ys [Hys Htr]].
      apply in_map_iff in Hys as [[[p l] q] [Hys Hedge]].
      subst ys.
      simpl in Htr.
      destruct Htr as [Htr | [Htr | []]];
        inversion Htr; subst;
        exists la, p, l, q; repeat split; auto.
    - destruct H as [la [p [l [q [Hla [Hedge [Htr | Htr]]]]]]]; subst tr.
      + apply in_concat.
        exists
          (concat
             (map
                (fun e =>
                   match e with
                   | (p, l, q) =>
                       let x := lr_symbol_of_label l in
                       [(LRBefore p x q la, Some x, LRAfterSymbol p x q la);
                        (LRAfterSymbol p x q la, Some (LRNonterm q),
                         LRComplete p x q la)]
                   end)
                (enfa_transition_edges m))).
        split.
        * apply in_map_iff. exists la. split; reflexivity || exact Hla.
        * apply in_concat.
          exists
            (let x := lr_symbol_of_label l in
             [(LRBefore p x q la, Some x, LRAfterSymbol p x q la);
              (LRAfterSymbol p x q la, Some (LRNonterm q),
               LRComplete p x q la)]).
          split.
          -- apply in_map_iff. exists (p, l, q). split; auto.
          -- simpl. auto.
      + apply in_concat.
        exists
          (concat
             (map
                (fun e =>
                   match e with
                   | (p, l, q) =>
                       let x := lr_symbol_of_label l in
                       [(LRBefore p x q la, Some x, LRAfterSymbol p x q la);
                        (LRAfterSymbol p x q la, Some (LRNonterm q),
                         LRComplete p x q la)]
                   end)
                (enfa_transition_edges m))).
        split.
        * apply in_map_iff. exists la. split; reflexivity || exact Hla.
        * apply in_concat.
          exists
            (let x := lr_symbol_of_label l in
             [(LRBefore p x q la, Some x, LRAfterSymbol p x q la);
              (LRAfterSymbol p x q la, Some (LRNonterm q),
               LRComplete p x q la)]).
          split.
          -- apply in_map_iff. exists (p, l, q). split; auto.
          -- simpl. auto.
  Qed.

  Theorem section4_definition10_step_membership :
    forall A_eq_dec (m : @finite_enfa A) p l q,
      In q (lr1_step m A_eq_dec p l) <->
      In (p, l, q) (lr1_transitions m).
  Proof.
    intros A_eq_dec m p l q.
    unfold lr1_step.
    set (item_dec := lr1_item_eq_dec (enfa_state_eq_dec m) A_eq_dec).
    set (symbol_dec := lr_symbol_eq_dec (enfa_state_eq_dec m) A_eq_dec).
    split; intros H.
    - apply nodup_In in H.
      apply in_map_iff in H as [[[p0 l0] q0] [Hq Htr]].
      simpl in Hq. subst q0.
      apply filter_In in Htr as [Htr Hmatch].
      simpl in Hmatch.
      apply andb_true_iff in Hmatch as [Hp Hl].
      apply eqb_of_dec_sound in Hp. subst p0.
      destruct l as [x|], l0 as [y|]; try discriminate; simpl in Hl.
      + apply eqb_of_dec_sound in Hl. subst y. exact Htr.
      + exact Htr.
    - apply nodup_In.
      apply in_map_iff.
      exists (p, l, q). split; [reflexivity |].
      apply filter_In. split; [exact H |].
      simpl.
      rewrite (eqb_of_dec_complete item_dec p p eq_refl). simpl.
      destruct l as [x|].
      + rewrite (eqb_of_dec_complete symbol_dec x x eq_refl).
        reflexivity.
      + reflexivity.
  Qed.

  Theorem section4_definition10_lr1_machine_full_characterization :
    forall A_eq_dec (m : @finite_enfa A),
      (forall it,
        In it
          (enfa_start
             (fenfa_base
                (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m)))) <->
        lr1_start_item_spec m it) /\
      (forall it,
        enfa_final
          (fenfa_base (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m))) it =
          true <->
        lr1_final_item_spec m it) /\
      (forall x,
        In x
          (fenfa_alphabet
             (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m))) <->
        lr1_alphabet_symbol_spec m x) /\
      (forall it,
        In it (lr1_reduce_items m) <-> lr1_reduce_item_spec m it) /\
      (forall it,
        In it (lr1_nonreduce_items m) <-> lr1_nonreduce_item_spec m it) /\
      (forall tr,
        In tr (lr1_reduce_transitions m) <->
        lr1_reduce_transition_spec m tr) /\
      (forall tr,
        In tr (lr1_shift_transitions m) <->
        lr1_shift_transition_spec m tr) /\
      (forall p l q,
        In q (lr1_step m A_eq_dec p l) <->
        In (p, l, q) (lr1_transitions m)).
  Proof.
    intros A_eq_dec m.
    split.
    - intro it0.
      apply (section4_definition10_start_state_membership A_eq_dec m it0).
    - split.
      + intro it1.
        apply (section4_definition10_final_state_membership A_eq_dec m it1).
      + split.
        * intro x0.
          apply (section4_definition10_alphabet_membership A_eq_dec m x0).
        * split.
          -- intro it2.
             apply (section4_definition10_reduce_item_membership m it2).
          -- split.
             ++ intro it3.
                apply (section4_definition10_nonreduce_item_membership m it3).
             ++ split.
                ** intro tr0.
                   apply (section4_definition10_reduce_transition_membership m tr0).
                ** split.
                   --- intro tr1.
                       apply (section4_definition10_shift_transition_membership m tr1).
                   --- intros p l q.
                       apply (section4_definition10_step_membership A_eq_dec m p l q).
  Qed.

  (** Lemma 3 I projection interface.

      The raw LR ENFA has administrative states and symbols. The paper's
      leaf-preservation claim is therefore stated over the observable
      projection that keeps only terminal [LRTerm] labels and maps each
      original ENFA edge to the LR gadget that simulates it. *)
  Definition lr1_observable_symbol_word {Q : Type} (x : lr_symbol Q)
      : list A :=
    match x with
    | LRTerm a => [a]
    | _ => []
    end.

  Definition lr1_observable_label_word {Q : Type}
      (l : option (lr_symbol Q)) : list A :=
    match l with
    | None => []
    | Some x => lr1_observable_symbol_word x
    end.

  Fixpoint lr1_observable_trace_word {Q : Type}
      (t : list ((lr1_item Q * option (lr_symbol Q)) * lr1_item Q))
      : list A :=
    match t with
    | [] => []
    | ((_, l), _) :: t' =>
        lr1_observable_label_word l ++
        lr1_observable_trace_word t'
    end.

  Definition lr1_project_edge
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (e : enfa_edge m)
      : enfa_trace (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m)) :=
    match e with
    | ((p, l), q) =>
        let x := lr_symbol_of_label l in
        [ ((LRState p LAEpsilon, None), LRBefore p x q LAEpsilon);
          ((LRBefore p x q LAEpsilon, Some x),
             LRAfterSymbol p x q LAEpsilon);
          ((LRAfterSymbol p x q LAEpsilon, None), LRState q LAEpsilon) ]
    end.

  Fixpoint lr1_project_trace
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (t : enfa_trace m)
      : enfa_trace (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m)) :=
    match t with
    | [] => []
    | e :: t' =>
        lr1_project_edge A_eq_dec m e ++
        lr1_project_trace A_eq_dec m t'
    end.

  Lemma lr1_original_edge_membership :
    forall (m : @finite_enfa A) p l q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      In q (enfa_step (fenfa_base m) p l) ->
      In (p, l, q) (enfa_transition_edges m).
  Proof.
    intros m p [a |] q Hwf Hp Hstep; unfold enfa_transition_edges.
    - apply in_concat.
      exists
        (map (fun q0 => (p, None, q0))
           (enfa_step (fenfa_base m) p None) ++
         concat
           (map
              (fun a0 =>
                 map (fun q0 => (p, Some a0, q0))
                   (enfa_step (fenfa_base m) p (Some a0)))
              (fenfa_alphabet m))).
      split.
      + apply in_map_iff. exists p. split; [reflexivity | exact Hp].
      + apply in_or_app. right.
        apply in_concat.
        exists
          (map (fun q0 => (p, Some a, q0))
             (enfa_step (fenfa_base m) p (Some a))).
        split.
        * apply in_map_iff. exists a. split; [reflexivity |].
          eapply fenfa_steps_in_alphabet; eauto.
        * apply in_map_iff. exists q. split; [reflexivity | exact Hstep].
    - apply in_concat.
      exists
        (map (fun q0 => (p, None, q0))
           (enfa_step (fenfa_base m) p None) ++
         concat
           (map
              (fun a =>
                 map (fun q0 => (p, Some a, q0))
                   (enfa_step (fenfa_base m) p (Some a)))
              (fenfa_alphabet m))).
      split.
      + apply in_map_iff. exists p. split; [reflexivity | exact Hp].
      + apply in_or_app. left.
        apply in_map_iff. exists q. split; [reflexivity | exact Hstep].
  Qed.

  Lemma lr1_project_edge_valid :
    forall A_eq_dec (m : @finite_enfa A) p l q,
      finite_enfa_wf m ->
      In p (fenfa_states m) ->
      In q (enfa_step (fenfa_base m) p l) ->
      valid_trace
        (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m))
        (LRState p LAEpsilon)
        (lr1_project_edge A_eq_dec m ((p, l), q))
        (LRState q LAEpsilon).
  Proof.
    intros A_eq_dec m p l q Hwf Hp Hstep.
    pose proof
      (lr1_original_edge_membership m p l q Hwf Hp Hstep) as Hedge.
    simpl.
    econstructor.
    - apply (proj2
        (section4_definition10_step_membership
           A_eq_dec m (LRState p LAEpsilon) None
           (LRBefore p (lr_symbol_of_label l) q LAEpsilon))).
      apply in_or_app. left.
      apply (proj2 (section4_definition10_reduce_transition_membership m _)).
      exists LAEpsilon, p, l, q.
      repeat split; simpl; auto.
    - econstructor.
      + apply (proj2
          (section4_definition10_step_membership
             A_eq_dec m (LRBefore p (lr_symbol_of_label l) q LAEpsilon)
             (Some (lr_symbol_of_label l))
             (LRAfterSymbol p (lr_symbol_of_label l) q LAEpsilon))).
        apply in_or_app. right.
        apply (proj2 (section4_definition10_shift_transition_membership m _)).
        exists LAEpsilon, p, l, q.
        repeat split; simpl; auto.
      + econstructor.
        * apply (proj2
            (section4_definition10_step_membership
               A_eq_dec m
               (LRAfterSymbol p (lr_symbol_of_label l) q LAEpsilon)
               None (LRState q LAEpsilon))).
          apply in_or_app. left.
          apply (proj2 (section4_definition10_reduce_transition_membership m _)).
          exists LAEpsilon, p, l, q.
          repeat split; simpl; auto.
        * constructor.
  Qed.

  Theorem lr1_project_trace_valid :
    forall A_eq_dec (m : @finite_enfa A) s t q,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      valid_trace m s t q ->
      valid_trace
        (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m))
        (LRState s LAEpsilon)
        (lr1_project_trace A_eq_dec m t)
        (LRState q LAEpsilon).
  Proof.
    intros A_eq_dec m s t q Hwf Hs Htrace.
    induction Htrace as [q0 | p l q0 r t0 Hstep Htail IH].
    - constructor.
    - change
        (valid_trace
           (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m))
           (LRState p LAEpsilon)
           (lr1_project_edge A_eq_dec m ((p, l), q0) ++
            lr1_project_trace A_eq_dec m t0)
           (LRState r LAEpsilon)).
      eapply valid_trace_app.
      + eapply lr1_project_edge_valid; eauto.
      + apply IH.
        eapply fenfa_steps_in_states; eauto.
  Qed.

  Theorem lr1_project_trace_observable_word :
    forall A_eq_dec (m : @finite_enfa A) (t : enfa_trace m),
      lr1_observable_trace_word (lr1_project_trace A_eq_dec m t) =
      trace_word t.
  Proof.
    intros A_eq_dec m t.
    induction t as [| [[p l] q] t IH]; simpl.
    - reflexivity.
    - destruct l; simpl; now rewrite IH.
  Qed.

  Definition lr1_projected_leaf_witnesses_at
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (w : list A)
      (q : enfa_state (fenfa_base m))
      : list
          (started_trace
             (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m))) :=
    map
      (fun st =>
         (LRState (fst st) LAEpsilon,
          lr1_project_trace A_eq_dec m (snd st)))
      (filter
         (fun st =>
            (ends_inb m q st && epsilon_simpleb m st)
            && maximal_epsilon_simpleb m st)
         (started_traces m w)).

  Definition lr1_projected_leaf_count
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (w : list A) : nat :=
    sum_nats
      (map
         (fun q => length (lr1_projected_leaf_witnesses_at A_eq_dec m w q))
         (fenfa_states m)).

  Theorem lr1_projected_leaf_witnesses_at_length :
    forall A_eq_dec (m : @finite_enfa A) w q,
      length (lr1_projected_leaf_witnesses_at A_eq_dec m w q) =
      enfa_maximal_simple_reach_count m w q.
  Proof.
    intros A_eq_dec m w q.
    unfold lr1_projected_leaf_witnesses_at,
      enfa_maximal_simple_reach_count.
    now rewrite length_map.
  Qed.

  Theorem lr1_projected_started_trace_valid :
    forall A_eq_dec (m : @finite_enfa A) w s t,
      finite_enfa_wf m ->
      In (s, t) (started_traces m w) ->
      valid_trace
        (lr1_enfa _ (lr1_machine_of_enfa A_eq_dec m))
        (LRState s LAEpsilon)
        (lr1_project_trace A_eq_dec m t)
        (LRState (trace_end s t) LAEpsilon) /\
      lr1_observable_trace_word (lr1_project_trace A_eq_dec m t) = w.
  Proof.
    intros A_eq_dec m w s t Hwf Hin.
    destruct (started_traces_valid m w s t Hin) as [Htrace Hword].
    split.
    - eapply lr1_project_trace_valid; eauto.
      eapply fenfa_starts_in_states; eauto.
      eapply started_traces_start_in; eauto.
    - rewrite lr1_project_trace_observable_word. exact Hword.
  Qed.

  Theorem section4_lemma4_I_lr1_leaf_preservation :
    forall A_eq_dec (m : @finite_enfa A) w,
      lr1_projected_leaf_count A_eq_dec m w =
      enfa_leaf_prime_word m w.
  Proof.
    intros A_eq_dec m w.
    unfold lr1_projected_leaf_count, enfa_leaf_prime_word.
    apply f_equal.
    apply map_ext.
    intro q.
    apply lr1_projected_leaf_witnesses_at_length.
  Qed.

  (** Theorem 6: LR(1) conflicts are bounded by leaves.  For any normalized
      LR(1) machine, reduce states form a sublist of all states, so the prime
      reach total over reduce states is bounded by the prime leaf total over
      all states. *)
  Theorem section4_theorem6_conflicts_le_leaves :
    forall {Q : Type} (M : lr1_machine Q) w,
      lr1_conflict_count M w <= lr1_leaf_count M w.
  Proof.
    intros Q M w.
    unfold lr1_conflict_count, lr1_leaf_count, enfa_leaf_prime_word.
    rewrite (lr1_reduce_states_spec Q M).
    rewrite map_app, sum_nats_app.
    lia.
  Qed.

  (** Direct Theorem 6 specialization to [lr1_machine_of_enfa] from
      Definition 10. *)
  Theorem section4_theorem6_conflicts_le_leaves_of_enfa :
    forall A_eq_dec (m : @finite_enfa A) w,
      lr1_conflict_count (lr1_machine_of_enfa A_eq_dec m) w <=
      lr1_leaf_count (lr1_machine_of_enfa A_eq_dec m) w.
  Proof.
    intros. apply section4_theorem6_conflicts_le_leaves.
  Qed.

  Theorem lr1_leaf_count_le_one_conflict_free :
    forall {Q : Type} (M : lr1_machine Q),
      (forall w, lr1_leaf_count M w <= 1) ->
      lr1_conflict_free M.
  Proof.
    intros Q M Hleaf w.
    pose proof (section4_theorem6_conflicts_le_leaves M w).
    specialize (Hleaf w).
    lia.
  Qed.

  (** Gamma-specific LR(1)-ness interface.

      The paper's Definition 10 describes a nondeterministic LR machine and
      counts conflicts over terminal words.  The terminal-word LR predicates
      below therefore use the Gamma/RLG prime accepting and prime reach
      derivations as the semantic reduce witnesses of that machine.

      [gamma_canonical_lr1] later in this block is the executable deterministic
      canonical item-set predicate, connected to the terminal-word semantics by
      the bridge conditions below. *)
  Definition gamma_semantic_accept_reduce_conflict_free
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    forall w d1 d2,
      rlg_derivation_accepting_prime
        (gamma_grammar_from m s) (fenfa_state_eqb m) w d1 ->
      rlg_derivation_accepting_prime
        (gamma_grammar_from m s) (fenfa_state_eqb m) w d2 ->
      d1 = d2.

  Definition gamma_semantic_reach_reduce_conflict_free
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    forall prefix q d1 d2,
      rlg_prefix_derivation_prime_reaches
        (gamma_grammar_from m s) (fenfa_state_eqb m) prefix q d1 ->
      rlg_prefix_derivation_prime_reaches
        (gamma_grammar_from m s) (fenfa_state_eqb m) prefix q d2 ->
      d1 = d2.

  Definition gamma_semantic_accept_reduce_conflict
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    exists w d1 d2,
      rlg_derivation_accepting_prime
        (gamma_grammar_from m s) (fenfa_state_eqb m) w d1 /\
      rlg_derivation_accepting_prime
        (gamma_grammar_from m s) (fenfa_state_eqb m) w d2 /\
      d1 <> d2.

  Definition gamma_semantic_reach_reduce_conflict
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    exists prefix q d1 d2,
      rlg_prefix_derivation_prime_reaches
        (gamma_grammar_from m s) (fenfa_state_eqb m) prefix q d1 /\
      rlg_prefix_derivation_prime_reaches
        (gamma_grammar_from m s) (fenfa_state_eqb m) prefix q d2 /\
      d1 <> d2.

  Definition gamma_semantic_reduce_conflict_free
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_semantic_accept_reduce_conflict_free m s /\
    gamma_semantic_reach_reduce_conflict_free m s.

  Definition gamma_lr_terminal_accept_reduce_conflict_free
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_semantic_accept_reduce_conflict_free m s.

  Definition gamma_lr_terminal_reach_reduce_conflict_free
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_semantic_reach_reduce_conflict_free m s.

  Definition gamma_lr_terminal_accept_reduce_conflict
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_semantic_accept_reduce_conflict m s.

  Definition gamma_lr_terminal_reach_reduce_conflict
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_semantic_reach_reduce_conflict m s.

  Definition gamma_lr_terminal_reduce_conflict_free
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_lr_terminal_accept_reduce_conflict_free A_eq_dec m s /\
    gamma_lr_terminal_reach_reduce_conflict_free A_eq_dec m s.

  Definition gamma_terminal_lr1
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_lr_terminal_reduce_conflict_free A_eq_dec m s.

  Definition gamma_canonical_lr1
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    lr1_canonical_collection_conflict_free A_eq_dec m s.

  Theorem gamma_canonical_lr1_no_item_set_conflict :
    forall A_eq_dec (m : @finite_enfa A) s,
      gamma_canonical_lr1 A_eq_dec m s <->
      forall xs,
        In xs (lr1_canonical_collection A_eq_dec m s) ->
        ~ lr1_same_lookahead_reduce_conflict A_eq_dec m xs.
  Proof.
    intros A_eq_dec m s.
    unfold gamma_canonical_lr1,
      lr1_canonical_collection_conflict_free.
    split; intros H xs Hxs.
    - apply lr1_item_set_reduce_conflict_free_iff_no_conflict.
      now apply H.
    - apply lr1_item_set_reduce_conflict_free_iff_no_conflict.
      now apply H.
  Qed.

  Theorem gamma_semantic_lr1_iff_gamma_unambiguous_reach :
    forall (m : @finite_enfa A) s,
      gamma_semantic_reduce_conflict_free m s <->
      gamma_rlg_unambiguous m s /\ gamma_rlg_reach_unambiguous m s.
  Proof.
    intros m s.
    unfold gamma_semantic_reduce_conflict_free,
      gamma_semantic_accept_reduce_conflict_free,
      gamma_semantic_reach_reduce_conflict_free,
      gamma_rlg_unambiguous, gamma_rlg_reach_unambiguous.
    tauto.
  Qed.

  Theorem section4_theorem5_terminal_semantic_bridge :
    forall A_eq_dec (m : @finite_enfa A) s,
      gamma_terminal_lr1 A_eq_dec m s <->
      gamma_semantic_reduce_conflict_free m s.
  Proof.
    intros A_eq_dec m s.
    unfold gamma_terminal_lr1,
      gamma_lr_terminal_reduce_conflict_free,
      gamma_lr_terminal_accept_reduce_conflict_free,
      gamma_lr_terminal_reach_reduce_conflict_free,
      gamma_semantic_reduce_conflict_free.
    tauto.
  Qed.

  Theorem section4_theorem5_terminal_lr1_iff_gamma_unambiguous_reach :
    forall A_eq_dec (m : @finite_enfa A) s,
      gamma_terminal_lr1 A_eq_dec m s <->
      gamma_rlg_unambiguous m s /\ gamma_rlg_reach_unambiguous m s.
  Proof.
    intros A_eq_dec m s.
    rewrite section4_theorem5_terminal_semantic_bridge.
    apply gamma_semantic_lr1_iff_gamma_unambiguous_reach.
  Qed.

  Definition gamma_canonical_semantic_bridge
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_canonical_lr1 A_eq_dec m s <->
    gamma_semantic_reduce_conflict_free m s.

  Definition gamma_canonical_conflict_soundness
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_canonical_lr1 A_eq_dec m s ->
    gamma_semantic_reduce_conflict_free m s.

  Definition gamma_canonical_conflict_completeness
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_semantic_reduce_conflict_free m s ->
    gamma_canonical_lr1 A_eq_dec m s.

  Definition gamma_canonical_conflict_reflection
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    gamma_canonical_conflict_soundness A_eq_dec m s /\
    gamma_canonical_conflict_completeness A_eq_dec m s.

  Definition section4_enfa_final_no_epsilon_successors
      (m : @finite_enfa A) : Prop :=
    forall q,
      In q (fenfa_states m) ->
      enfa_final (fenfa_base m) q = true ->
      enfa_step (fenfa_base m) q None = [].

  Theorem section4_enfa_final_no_epsilon_successors_maximal :
    forall (m : @finite_enfa A) st,
      section4_enfa_final_no_epsilon_successors m ->
      In (started_end st) (fenfa_states m) ->
      accepted_traceb m st = true ->
      maximal_epsilon_simpleb m st = true.
  Proof.
    intros m st Hfinal Hstate Haccept.
    unfold maximal_epsilon_simpleb.
    unfold accepted_traceb in Haccept.
    rewrite (Hfinal (started_end st) Hstate Haccept).
    reflexivity.
  Qed.

  Definition gamma_prime_final_conflict_reflection
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A)
      (s : enfa_state (fenfa_base m)) : Prop :=
    section4_enfa_final_no_epsilon_successors m /\
    gamma_canonical_conflict_reflection A_eq_dec m s.

  (** Canonical bridge.

      The executable canonical item-set predicate and the Gamma/RLG semantic
      uniqueness predicates are related through the named reflection condition
      below.  The examples include the terminal semantic conflict interface
      used by the paper theorem. *)
  Theorem section4_lr1_support_canonical_semantic_bridge_under_conflict_reflection :
    forall A_eq_dec (m : @finite_enfa A) s,
      gamma_canonical_conflict_reflection A_eq_dec m s ->
      gamma_canonical_semantic_bridge A_eq_dec m s.
  Proof.
    intros A_eq_dec m s [Hsound Hcomplete].
    unfold gamma_canonical_semantic_bridge,
      gamma_canonical_conflict_soundness,
      gamma_canonical_conflict_completeness in *.
    split; assumption.
  Qed.

  (** Prime-final canonical bridge.

      [section4_enfa_final_no_epsilon_successors] aligns final LR items with
      prime/maximal accepting semantics: final states have no epsilon
      successors.  The combined reflection condition is named
      [gamma_prime_final_conflict_reflection]. *)
  Theorem section4_lr1_support_canonical_semantic_bridge_under_prime_final_reflection :
    forall A_eq_dec (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      In s (fenfa_states m) ->
      gamma_prime_final_conflict_reflection A_eq_dec m s ->
      gamma_canonical_semantic_bridge A_eq_dec m s.
  Proof.
    intros A_eq_dec m s _ _ [_ Hreflection].
    now apply
      section4_lr1_support_canonical_semantic_bridge_under_conflict_reflection.
  Qed.

  (** Canonical LR(1) is related to Gamma unambiguity through
      [gamma_canonical_semantic_bridge], the item-set soundness/completeness
      bridge used by the canonical formulation. *)
  Theorem section4_lr1_support_canonical_lr1_iff_gamma_unambiguous_reach :
    forall A_eq_dec (m : @finite_enfa A) s,
      gamma_canonical_semantic_bridge A_eq_dec m s ->
      gamma_canonical_lr1 A_eq_dec m s <->
      gamma_rlg_unambiguous m s /\ gamma_rlg_reach_unambiguous m s.
  Proof.
    intros A_eq_dec m s Hbridge.
    split.
    - intro Hcanon.
      apply (proj1 (gamma_semantic_lr1_iff_gamma_unambiguous_reach m s)).
      now apply (proj1 Hbridge).
    - intro Hgamma.
      apply (proj2 Hbridge).
      now apply (proj2 (gamma_semantic_lr1_iff_gamma_unambiguous_reach m s)).
  Qed.

  Theorem section4_lr1_support_canonical_lr1_iff_gamma_unambiguous_reach_under_conflict_reflection :
    forall A_eq_dec (m : @finite_enfa A) s,
      gamma_canonical_conflict_reflection A_eq_dec m s ->
      gamma_canonical_lr1 A_eq_dec m s <->
      gamma_rlg_unambiguous m s /\ gamma_rlg_reach_unambiguous m s.
  Proof.
    intros A_eq_dec m s Hreflection.
    apply section4_lr1_support_canonical_lr1_iff_gamma_unambiguous_reach.
    now apply
      section4_lr1_support_canonical_semantic_bridge_under_conflict_reflection.
  Qed.

  Definition gamma_lr1 (m : @finite_enfa A) : Prop :=
    enfa_UFA m /\ enfa_ReachUFA m.

  Definition gamma_lr1_full_spec
      (A_eq_dec : forall x y : A, {x = y} + {x <> y})
      (m : @finite_enfa A) : Prop :=
    gamma_lr1 m /\ gamma_lr1_conflict_count_spec A_eq_dec m.

  (** LR(1) bridge specification.  [gamma_lr1] unfolds directly to UFA plus
      ReachUFA, and the canonical item-set version below is stated with
      [gamma_canonical_semantic_bridge]. *)
  Theorem section4_lr1_support_lr1_iff_ufa_reachufa :
    forall (m : @finite_enfa A),
      gamma_lr1 m <-> enfa_UFA m /\ enfa_ReachUFA m.
  Proof.
    intros. unfold gamma_lr1. tauto.
  Qed.

  Theorem section4_lr1_support_leafufa_sufficient_lr1 :
    forall (m : @finite_enfa A),
      enfa_UFA m ->
      enfa_ReachUFA m ->
      enfa_LeafUFA m ->
      gamma_lr1 m.
  Proof.
    intros m Hu Hr _. split; assumption.
  Qed.

  (** Theorem 5 I, read through Definition 10's nondeterministic LR machine
      over terminal words.  Unlike the deterministic canonical item-set
      canonical item-set formulation below, this statement follows directly
      from the terminal-word LR semantics. *)
  Theorem section4_theorem5_terminal_lr1_iff_ufa_reachufa :
    forall A_eq_dec (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      gamma_terminal_lr1 A_eq_dec m s <->
      enfa_UFA m /\ enfa_ReachUFA m.
  Proof.
    intros A_eq_dec m s Hwf Hstart Henum Hnodup.
    split.
    - intro Hterminal.
      apply
        (proj1
           (section4_theorem5_terminal_lr1_iff_gamma_unambiguous_reach
              A_eq_dec m s)) in Hterminal as [Hrlg_ufa Hrlg_reach].
      split.
      + eapply section4_gamma_support_rlg_unambiguous_to_ufa; eauto.
      + eapply section4_gamma_support_rlg_reach_unambiguous_to_reachufa;
          eauto.
    - intros [Hufa Hreach].
      apply
        (proj2
           (section4_theorem5_terminal_lr1_iff_gamma_unambiguous_reach
              A_eq_dec m s)).
      split.
      + eapply section4_gamma_support_ufa_to_rlg_unambiguous; eauto.
      + eapply section4_gamma_support_reachufa_to_rlg_reach_unambiguous;
          eauto.
  Qed.

  (** Theorem 5 II, LeafUFA sufficient direction for the terminal-word
      nondeterministic LR semantics. *)
  Theorem section4_theorem5_leafufa_sufficient_terminal_lr1 :
    forall A_eq_dec (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      enfa_trim m ->
      enfa_prime_extendable m ->
      enfa_LeafUFA m ->
      gamma_terminal_lr1 A_eq_dec m s.
  Proof.
    intros A_eq_dec m s Hwf Hstart Henum Hnodup Htrim Hextend Hleaf.
    apply
      (proj2
         (section4_theorem5_terminal_lr1_iff_ufa_reachufa
            A_eq_dec m s Hwf Hstart Henum Hnodup)).
    assert (Hufa : enfa_UFA m).
    {
      now apply section4_theorem2_leafufa_implies_ufa.
    }
    split.
    - exact Hufa.
    - eapply section4_theorem2_trim_extendable_ufa_implies_reachufa; eauto.
  Qed.

  (** LR(1) bridge canonical formulation.  Under well-formed, single-start,
      trace-enumeration, nodup, and [gamma_canonical_semantic_bridge]
      conditions, canonical LR(1) is equivalent to
      [enfa_UFA m /\ enfa_ReachUFA m]. *)
  Theorem section4_lr1_support_canonical_lr1_iff_ufa_reachufa :
    forall A_eq_dec (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      gamma_canonical_semantic_bridge A_eq_dec m s ->
      gamma_canonical_lr1 A_eq_dec m s <->
      enfa_UFA m /\ enfa_ReachUFA m.
  Proof.
    intros A_eq_dec m s Hwf Hstart Henum Hnodup Hbridge.
    split.
    - intro Hcanon.
      apply (proj1 (section4_lr1_support_canonical_lr1_iff_gamma_unambiguous_reach
                      A_eq_dec m s Hbridge)) in Hcanon
        as [Hrlg_ufa Hrlg_reach].
      split.
      + eapply section4_gamma_support_rlg_unambiguous_to_ufa; eauto.
      + eapply section4_gamma_support_rlg_reach_unambiguous_to_reachufa; eauto.
    - intros [Hufa Hreach].
      apply (proj2 (section4_lr1_support_canonical_lr1_iff_gamma_unambiguous_reach
                      A_eq_dec m s Hbridge)).
      split.
      + eapply section4_gamma_support_ufa_to_rlg_unambiguous; eauto.
      + eapply section4_gamma_support_reachufa_to_rlg_reach_unambiguous; eauto.
  Qed.

  (* Alias for the accepting-maximal reflection formulation. *)
  Definition section4_lr1_support_canonical_lr1_iff_ufa_reachufa_under_semantic_bridge_and_accepting_maximal_reflection :=
    section4_lr1_support_canonical_lr1_iff_ufa_reachufa.

  (** Theorem 5 I under the LR item-set/semantic conflict-reflection bridge. *)
  Theorem section4_lr1_support_canonical_lr1_iff_ufa_reachufa_under_conflict_reflection :
    forall A_eq_dec (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      gamma_canonical_conflict_reflection A_eq_dec m s ->
      gamma_canonical_lr1 A_eq_dec m s <->
      enfa_UFA m /\ enfa_ReachUFA m.
  Proof.
    intros A_eq_dec m s Hwf Hstart Henum Hnodup Hreflection.
    apply
      (section4_lr1_support_canonical_lr1_iff_ufa_reachufa
         A_eq_dec m s Hwf Hstart Henum Hnodup).
    now apply
      section4_lr1_support_canonical_semantic_bridge_under_conflict_reflection.
  Qed.

  Definition section4_lr1_support_canonical_lr1_iff_ufa_reachufa_under_conflict_and_accepting_maximal_reflection :=
    section4_lr1_support_canonical_lr1_iff_ufa_reachufa_under_conflict_reflection.

  Theorem section4_lr1_support_canonical_lr1_iff_ufa_reachufa_under_prime_final_reflection :
    forall A_eq_dec (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      In s (fenfa_states m) ->
      gamma_prime_final_conflict_reflection A_eq_dec m s ->
      gamma_canonical_lr1 A_eq_dec m s <->
      enfa_UFA m /\ enfa_ReachUFA m.
  Proof.
    intros A_eq_dec m s Hwf Hstart Henum Hnodup Hs Hreflection.
    apply
      (section4_lr1_support_canonical_lr1_iff_ufa_reachufa
         A_eq_dec m s Hwf Hstart Henum Hnodup).
    eapply
      section4_lr1_support_canonical_semantic_bridge_under_prime_final_reflection;
      eauto.
  Qed.

  Definition section4_lr1_support_canonical_lr1_iff_ufa_reachufa_under_prime_final_and_accepting_maximal_reflection :=
    section4_lr1_support_canonical_lr1_iff_ufa_reachufa_under_prime_final_reflection.

  (** LR(1) bridge canonical version for the LeafUFA sufficient branch.
      LeafUFA first gives UFA; the explicit trim/extendable conditions provide
      ReachUFA, and [gamma_canonical_semantic_bridge] then gives canonical
      LR(1). *)
  Theorem section4_lr1_support_leafufa_sufficient_canonical_lr1 :
    forall A_eq_dec (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      enfa_trim m ->
      enfa_prime_extendable m ->
      gamma_canonical_semantic_bridge A_eq_dec m s ->
      enfa_LeafUFA m ->
      gamma_canonical_lr1 A_eq_dec m s.
  Proof.
    intros A_eq_dec m s Hwf Hstart Henum Hnodup Htrim Hextend
      Hbridge Hleaf.
    apply
      (proj2
         (section4_lr1_support_canonical_lr1_iff_ufa_reachufa
            A_eq_dec m s Hwf Hstart Henum Hnodup Hbridge)).
    assert (Hufa : enfa_UFA m).
    {
      now apply section4_theorem2_leafufa_implies_ufa.
    }
    split.
    - exact Hufa.
    - eapply section4_theorem2_trim_extendable_ufa_implies_reachufa; eauto.
  Qed.

  (* Alias for the semantic-bridge accepting-maximal formulation. *)
  Definition section4_lr1_support_leafufa_sufficient_canonical_lr1_under_semantic_bridge_accepting_maximal_reflection_and_da_leaf_bound :=
    section4_lr1_support_leafufa_sufficient_canonical_lr1.

  (** Theorem 5 II, the LeafUFA sufficient direction under the LR
      item-set/semantic conflict-reflection bridge. *)
  Theorem section4_lr1_support_leafufa_sufficient_canonical_lr1_under_conflict_reflection :
    forall A_eq_dec (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      enfa_trim m ->
      enfa_prime_extendable m ->
      gamma_canonical_conflict_reflection A_eq_dec m s ->
      enfa_LeafUFA m ->
      gamma_canonical_lr1 A_eq_dec m s.
  Proof.
    intros A_eq_dec m s Hwf Hstart Henum Hnodup Htrim Hextend
      Hreflection Hleaf.
    apply
      (section4_lr1_support_leafufa_sufficient_canonical_lr1
         A_eq_dec m s Hwf Hstart Henum Hnodup Htrim Hextend).
    now apply
      section4_lr1_support_canonical_semantic_bridge_under_conflict_reflection.
    exact Hleaf.
  Qed.

  Definition section4_lr1_support_leafufa_sufficient_canonical_lr1_under_conflict_accepting_maximal_reflection_and_da_leaf_bound :=
    section4_lr1_support_leafufa_sufficient_canonical_lr1_under_conflict_reflection.

  Theorem section4_lr1_support_leafufa_sufficient_canonical_lr1_under_prime_final_reflection :
    forall A_eq_dec (m : @finite_enfa A) s,
      finite_enfa_wf m ->
      enfa_start (fenfa_base m) = [s] ->
      enfa_prime_trace_enumerated_from m s ->
      enfa_started_traces_nodup m ->
      enfa_trim m ->
      enfa_prime_extendable m ->
      In s (fenfa_states m) ->
      gamma_prime_final_conflict_reflection A_eq_dec m s ->
      enfa_LeafUFA m ->
      gamma_canonical_lr1 A_eq_dec m s.
  Proof.
    intros A_eq_dec m s Hwf Hstart Henum Hnodup Htrim Hextend
      Hs Hreflection Hleaf.
    apply
      (section4_lr1_support_leafufa_sufficient_canonical_lr1
         A_eq_dec m s Hwf Hstart Henum Hnodup Htrim Hextend).
    eapply
      section4_lr1_support_canonical_semantic_bridge_under_prime_final_reflection;
      eauto.
    exact Hleaf.
  Qed.

  Definition section4_lr1_support_leafufa_sufficient_canonical_lr1_under_prime_final_accepting_maximal_reflection_and_da_leaf_bound :=
    section4_lr1_support_leafufa_sufficient_canonical_lr1_under_prime_final_reflection.

  Theorem section4_theorem6_leaf_one_conflict_free_of_enfa :
    forall A_eq_dec (m : @finite_enfa A),
      (forall w,
        lr1_leaf_count (lr1_machine_of_enfa A_eq_dec m) w <= 1) ->
      gamma_lr1_conflict_count_spec A_eq_dec m.
  Proof.
    intros A_eq_dec m Hleaf.
    apply lr1_leaf_count_le_one_conflict_free.
    exact Hleaf.
  Qed.

  Theorem section4_lr1_support_full_spec_if_lr1_leaf_bounded :
    forall A_eq_dec (m : @finite_enfa A),
      gamma_lr1 m ->
      (forall w,
        lr1_leaf_count (lr1_machine_of_enfa A_eq_dec m) w <= 1) ->
      gamma_lr1_full_spec A_eq_dec m.
  Proof.
    intros A_eq_dec m Hlr Hleaf.
    split; [exact Hlr |].
    now apply section4_theorem6_leaf_one_conflict_free_of_enfa.
  Qed.

  Theorem section4_lr1_support_full_spec_iff_ufa_reachufa_conflict_free :
    forall A_eq_dec (m : @finite_enfa A),
      gamma_lr1_full_spec A_eq_dec m <->
      enfa_UFA m /\
      enfa_ReachUFA m /\
      lr1_conflict_free (lr1_machine_of_enfa A_eq_dec m).
  Proof.
    intros A_eq_dec m.
    unfold gamma_lr1_full_spec, gamma_lr1,
      gamma_lr1_conflict_count_spec.
    tauto.
  Qed.

  (** Section 4.2 decision-problem interface: Problem 1/2 input objects and
      their reach/leaf/SUFA membership predicates. *)
  Inductive regular_descriptor : Type :=
  | DescriptorRegex : regex A -> regular_descriptor
  | DescriptorENFA : @finite_enfa A -> regular_descriptor
  | DescriptorRLG : @right_linear_grammar A -> regular_descriptor.

  Definition descriptor_unambiguous
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (D : regular_descriptor) : Prop :=
    match D with
    | DescriptorRegex r => enfa_UFA (regex_Msss alphabet label_matches r)
    | DescriptorENFA m => enfa_UFA m
    | DescriptorRLG G => rlg_unambiguous G
    end.

  Definition descriptor_reach_unambiguous
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (D : regular_descriptor) : Prop :=
    match D with
    | DescriptorRegex r =>
        regex_strong_reach_unambiguous alphabet label_matches r
    | DescriptorENFA m => enfa_ReachUFA m
    | DescriptorRLG G => rlg_reach_unambiguous G
    end.

  Definition descriptor_leaf_unambiguous
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (D : regular_descriptor) : Prop :=
    match D with
    | DescriptorRegex r => regex_strong_leaf_unambiguous alphabet label_matches r
    | DescriptorENFA m => enfa_LeafUFA m
    | DescriptorRLG G => rlg_leaf_unambiguous G
    end.

  Definition Problem1_U
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (D : regular_descriptor) : Prop :=
    descriptor_unambiguous alphabet label_matches D.

  Definition Problem1_ReachU
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (D : regular_descriptor) : Prop :=
    descriptor_reach_unambiguous alphabet label_matches D.

  Definition Problem1_LeafU
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (D : regular_descriptor) : Prop :=
    descriptor_leaf_unambiguous alphabet label_matches D.

  Definition Problem3_SUFA_Member
      (m : @finite_enfa A)
      (w : list A) : Prop :=
    enfa_SUFA m /\ 0 < enfa_da_prime_word m w.

  Definition Problem3_LeafUFA_Member
      (m : @finite_enfa A)
      (w : list A) : Prop :=
    enfa_LeafUFA m /\ 0 < enfa_da_prime_word m w.

  Definition Problem2_SUFA_Member := Problem3_SUFA_Member.

  Definition Problem2_LeafUFA_Member := Problem3_LeafUFA_Member.
End Section4LR.
