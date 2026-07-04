From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Regex Require Import KleeneSemantics.
From PositionAutomata.Automata Require Import EpsilonNFA.

(** A Thompson/Sippu-Soisalon-Soininen style epsilon-NFA compiler for
    regular expressions.  The construction deliberately uses [nat] states so
    that the generated machine has a simple executable equality test. *)

Section RegexSSS.
  Context {A : Type}.

  (** Fragment used by the Section 4 Definition 7 [Msss(E)] construction.
      A fragment stores an entry, an exit, the next fresh state, and edges. *)
  Record sss_fragment : Type := {
    sss_start : nat;
    sss_final : nat;
    sss_next : nat;
    sss_edges : list (nat * option A * nat)
  }.

  Definition sss_edge_src (e : nat * option A * nat) : nat :=
    match e with (p, _, _) => p end.

  Definition sss_edge_label (e : nat * option A * nat) : option A :=
    match e with (_, l, _) => l end.

  Definition sss_edge_dst (e : nat * option A * nat) : nat :=
    match e with (_, _, q) => q end.

  Fixpoint regex_symbols (r : regex A) : list A :=
    match r with
    | Empty | Eps => []
    | Atom a => [a]
    | Alt r1 r2 | Cat r1 r2 => regex_symbols r1 ++ regex_symbols r2
    | Star r' => regex_symbols r'
    end.

  Definition regex_symbol_closed
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    forall b a,
      In b (regex_symbols r) ->
      label_matches b a = true ->
      In a alphabet.

  Definition sss_edge (p : nat) (l : option A) (q : nat)
      : nat * option A * nat := (p, l, q).

  (** Structure-recursive SSS compiler.  This version follows the paper
      diagram: concatenation shares the middle state, and star loops through
      the body entry state. *)
  Fixpoint sss_compile_between
      (fresh start final : nat) (r : regex A) : sss_fragment :=
    match r with
    | Empty =>
        {|
          sss_start := start;
          sss_final := final;
          sss_next := fresh;
          sss_edges := []
        |}
    | Eps =>
        {|
          sss_start := start;
          sss_final := final;
          sss_next := fresh;
          sss_edges := [sss_edge start None final]
        |}
    | Atom a =>
        {|
          sss_start := start;
          sss_final := final;
          sss_next := fresh;
          sss_edges := [sss_edge start (Some a) final]
        |}
    | Alt r1 r2 =>
        let f1 := sss_compile_between fresh start final r1 in
        let r2_start := sss_next f1 in
        let r2_final := S r2_start in
        let f2 := sss_compile_between (S (S r2_start)) r2_start r2_final r2 in
        {|
          sss_start := start;
          sss_final := final;
          sss_next := sss_next f2;
          sss_edges :=
            sss_edges f1 ++
            [ sss_edge start None r2_start;
              sss_edge r2_final None final ] ++
            sss_edges f2
        |}
    | Cat r1 r2 =>
        let mid := fresh in
        let f1 := sss_compile_between (S fresh) start mid r1 in
        let f2 := sss_compile_between (sss_next f1) mid final r2 in
        {|
          sss_start := sss_start f1;
          sss_final := sss_final f2;
          sss_next := sss_next f2;
          sss_edges :=
            sss_edges f1 ++ sss_edges f2
        |}
    | Star r' =>
        let body_start := fresh in
        let body_final := S fresh in
        let body := sss_compile_between (S (S fresh)) body_start body_final r' in
        {|
          sss_start := start;
          sss_final := final;
          sss_next := sss_next body;
          sss_edges :=
            [ sss_edge start None body_start;
              sss_edge body_start None final;
              sss_edge body_final None body_start ] ++
            sss_edges body
        |}
    end.

  Definition sss_compile_from (fresh : nat) (r : regex A) : sss_fragment :=
    sss_compile_between (S (S fresh)) fresh (S fresh) r.

  Definition sss_compile (r : regex A) : sss_fragment :=
    sss_compile_from 0 r.

  Definition sss_fragment_states (f : sss_fragment) : list nat :=
    nodup Nat.eq_dec
      (sss_start f :: sss_final f ::
       concat (map (fun e => [sss_edge_src e; sss_edge_dst e]) (sss_edges f))).

  Definition sss_edge_matches
      (label_matches : A -> A -> bool)
      (asked : option A)
      (e : nat * option A * nat) : bool :=
    match sss_edge_label e, asked with
    | None, None => true
    | Some b, Some a => label_matches b a
    | _, _ => false
    end.

  Definition sss_step
      (label_matches : A -> A -> bool)
      (edges : list (nat * option A * nat))
      (p : nat)
      (l : option A) : list nat :=
    nodup Nat.eq_dec
      (map sss_edge_dst
         (filter
            (fun e => Nat.eqb (sss_edge_src e) p && sss_edge_matches label_matches l e)
            edges)).

  (** Package an SSS fragment as the finite epsilon-NFA used by [Msss(E)]. *)
  Definition regex_Msss
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : @finite_enfa A :=
    let f := sss_compile r in
    {|
      fenfa_base :=
        {|
          enfa_state := nat;
          enfa_start := [sss_start f];
          enfa_final := fun q => Nat.eqb q (sss_final f);
          enfa_step := sss_step label_matches (sss_edges f)
        |};
      fenfa_states := sss_fragment_states f;
      fenfa_alphabet := alphabet;
      fenfa_state_eqb := Nat.eqb;
      fenfa_state_eqb_sound := fun x y H => proj1 (Nat.eqb_eq x y) H;
      fenfa_state_eqb_complete := fun x y H => proj2 (Nat.eqb_eq x y) H
    |}.

  (** Well-formedness support for the generated finite epsilon-NFA. *)
  Lemma sss_compile_has_next :
    forall fresh r, exists n, sss_next (sss_compile_from fresh r) = n.
  Proof.
    intros fresh r. eauto.
  Qed.

  Lemma sss_compile_between_start_eq :
    forall fresh start final r,
      sss_start (sss_compile_between fresh start final r) = start.
  Proof.
    intros fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final; simpl; auto.
  Qed.

  Lemma sss_compile_between_final_eq :
    forall fresh start final r,
      sss_final (sss_compile_between fresh start final r) = final.
  Proof.
    intros fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final; simpl; auto.
  Qed.

  Lemma sss_compile_start_eq :
    forall fresh r,
      sss_start (sss_compile_from fresh r) = fresh.
  Proof.
    intros fresh r. unfold sss_compile_from.
    apply sss_compile_between_start_eq.
  Qed.

  Lemma sss_compile_final_eq :
    forall fresh r,
      sss_final (sss_compile_from fresh r) = S fresh.
  Proof.
    intros fresh r. unfold sss_compile_from.
    apply sss_compile_between_final_eq.
  Qed.

  Lemma sss_compile_between_next_ge :
    forall fresh start final r,
      fresh <= sss_next (sss_compile_between fresh start final r).
  Proof.
    intros fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final; simpl; try lia.
    - set (f1 := sss_compile_between fresh start final r1).
      specialize (IH1 fresh start final).
      fold f1 in IH1.
      specialize (IH2 (S (S (sss_next f1))) (sss_next f1) (S (sss_next f1))).
      lia.
    - set (f1 := sss_compile_between (S fresh) start fresh r1).
      specialize (IH1 (S fresh) start fresh).
      fold f1 in IH1.
      specialize (IH2 (sss_next f1) fresh final).
      lia.
    - specialize (IH (S (S fresh)) fresh (S fresh)).
      lia.
  Qed.

  Lemma sss_compile_next_gt :
    forall fresh r,
      fresh < sss_next (sss_compile_from fresh r).
  Proof.
    intros fresh r. unfold sss_compile_from.
    pose proof (sss_compile_between_next_ge (S (S fresh)) fresh (S fresh) r).
    lia.
  Qed.

  Lemma sss_compile_final_range :
    forall fresh r,
      fresh <= sss_final (sss_compile_from fresh r) /\
      sss_final (sss_compile_from fresh r) <
        sss_next (sss_compile_from fresh r).
  Proof.
    intros fresh r.
    unfold sss_compile_from.
    rewrite sss_compile_between_final_eq.
    pose proof (sss_compile_between_next_ge (S (S fresh)) fresh (S fresh) r).
    split; lia.
  Qed.

  Lemma sss_compile_between_edges_lower :
    forall fresh start final r base p l q,
      base <= fresh ->
      base <= start ->
      base <= final ->
      In (p, l, q) (sss_edges (sss_compile_between fresh start final r)) ->
      base <= p /\ base <= q.
  Proof.
    intros fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final base p l q Hfresh Hstart Hfinal Hin; simpl in *.
    - contradiction.
    - destruct Hin as [Hin | []]. inversion Hin; subst; lia.
    - destruct Hin as [Hin | []]. inversion Hin; subst; lia.
    - set (f1 := sss_compile_between fresh start final r1) in *.
      set (r2_start := sss_next f1) in *.
      set (r2_final := S r2_start) in *.
      set (f2 := sss_compile_between (S (S r2_start)) r2_start r2_final r2) in *.
      pose proof (sss_compile_between_next_ge fresh start final r1) as Hn1.
      fold f1 in Hn1.
      fold r2_start in Hn1.
      assert (Hr2_start_ge : base <= r2_start) by lia.
      assert (Hr2_final_ge : base <= r2_final) by lia.
      apply in_app_or in Hin as [Hin | Hin].
      + exact (IH1 fresh start final base p l q Hfresh Hstart Hfinal Hin).
      + destruct Hin as [H | [H | Hin]].
        * inversion H; subst; split; lia.
        * inversion H; subst; split; lia.
        * assert (Hfresh2 : base <= S (S r2_start)) by lia.
          exact
            (IH2 (S (S r2_start)) r2_start r2_final base p l q
               Hfresh2 Hr2_start_ge Hr2_final_ge Hin).
    - set (f1 := sss_compile_between (S fresh) start fresh r1) in *.
      set (f2 := sss_compile_between (sss_next f1) fresh final r2) in *.
      pose proof (sss_compile_between_next_ge (S fresh) start fresh r1) as Hn1.
      fold f1 in Hn1.
      apply in_app_or in Hin as [Hin | Hin].
      + assert (Hfresh1 : base <= S fresh) by lia.
        exact (IH1 (S fresh) start fresh base p l q
                 Hfresh1 Hstart Hfresh Hin).
      + assert (Hfresh2 : base <= sss_next f1) by lia.
        exact (IH2 (sss_next f1) fresh final base p l q
                 Hfresh2 Hfresh Hfinal Hin).
    - set (body := sss_compile_between (S (S fresh)) fresh (S fresh) r) in *.
      destruct Hin as [H | [H | [H | Hin]]].
      + inversion H; subst; split; lia.
      + inversion H; subst; split; lia.
      + inversion H; subst; split; lia.
      + assert (Hfresh_body : base <= S (S fresh)) by lia.
        assert (Hstart_body : base <= fresh) by lia.
        assert (Hfinal_body : base <= S fresh) by lia.
        exact (IH (S (S fresh)) fresh (S fresh) base p l q
                 Hfresh_body Hstart_body Hfinal_body Hin).
  Qed.

  Lemma sss_compile_between_edges_upper :
    forall fresh start final r p l q,
      start < fresh ->
      final < fresh ->
      In (p, l, q) (sss_edges (sss_compile_between fresh start final r)) ->
      p < sss_next (sss_compile_between fresh start final r) /\
      q < sss_next (sss_compile_between fresh start final r).
  Proof.
    intros fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final p l q Hstart Hfinal Hin; simpl in *.
    - contradiction.
    - destruct Hin as [Hin | []]. inversion Hin; subst; lia.
    - destruct Hin as [Hin | []]. inversion Hin; subst; lia.
    - set (f1 := sss_compile_between fresh start final r1) in *.
      set (r2_start := sss_next f1) in *.
      set (r2_final := S r2_start) in *.
      set (f2 := sss_compile_between (S (S r2_start)) r2_start r2_final r2) in *.
      change (p < sss_next f2 /\ q < sss_next f2).
      pose proof (sss_compile_between_next_ge fresh start final r1) as Hn1.
      fold f1 in Hn1. fold r2_start in Hn1.
      pose proof
        (sss_compile_between_next_ge
           (S (S r2_start)) r2_start r2_final r2) as Hn2.
      fold f2 in Hn2.
      assert (Hr2_start_next : r2_start < sss_next f2) by lia.
      apply in_app_or in Hin as [Hin | Hin].
      + destruct (IH1 fresh start final p l q Hstart Hfinal Hin)
          as [Hp Hq].
        fold f1 in Hp, Hq. split; lia.
      + destruct Hin as [H | [H | Hin]].
        * inversion H; subst; split; lia.
        * inversion H; subst; split; lia.
        * assert (Hr2s : r2_start < S (S r2_start)) by lia.
          assert (Hr2f : r2_final < S (S r2_start)) by lia.
          destruct
            (IH2 (S (S r2_start)) r2_start r2_final p l q
               Hr2s Hr2f Hin)
            as [Hp Hq].
          fold f2 in Hp, Hq. split; lia.
    - set (f1 := sss_compile_between (S fresh) start fresh r1) in *.
      set (f2 := sss_compile_between (sss_next f1) fresh final r2) in *.
      change (p < sss_next f2 /\ q < sss_next f2).
      pose proof (sss_compile_between_next_ge (S fresh) start fresh r1) as Hn1.
      fold f1 in Hn1.
      pose proof
        (sss_compile_between_next_ge (sss_next f1) fresh final r2) as Hn2.
      fold f2 in Hn2.
      assert (Hf1_next_f2 : sss_next f1 <= sss_next f2) by lia.
      apply in_app_or in Hin as [Hin | Hin].
      + assert (Hstart1 : start < S fresh) by lia.
        assert (Hfinal1 : fresh < S fresh) by lia.
        destruct (IH1 (S fresh) start fresh p l q Hstart1 Hfinal1 Hin)
          as [Hp Hq].
        fold f1 in Hp, Hq. split; lia.
      + assert (Hfresh2 : fresh < sss_next f1) by lia.
        assert (Hfinal2 : final < sss_next f1) by lia.
        destruct
          (IH2 (sss_next f1) fresh final p l q Hfresh2 Hfinal2 Hin)
          as [Hp Hq].
        fold f2 in Hp, Hq. split; lia.
    - set (body := sss_compile_between (S (S fresh)) fresh (S fresh) r) in *.
      change (p < sss_next body /\ q < sss_next body).
      pose proof
        (sss_compile_between_next_ge (S (S fresh)) fresh (S fresh) r)
        as Hnbody.
      fold body in Hnbody.
      destruct Hin as [H | [H | [H | Hin]]].
      + inversion H; subst; split; lia.
      + inversion H; subst; split; lia.
      + inversion H; subst; split; lia.
      + assert (Hbs : fresh < S (S fresh)) by lia.
        assert (Hbf : S fresh < S (S fresh)) by lia.
        destruct (IH (S (S fresh)) fresh (S fresh) p l q Hbs Hbf Hin)
          as [Hp Hq].
        fold body in Hp, Hq. split; lia.
  Qed.

  Definition sss_owned_state
      (fresh start final next x : nat) : Prop :=
    x = start \/ x = final \/ (fresh <= x /\ x < next).

  Lemma sss_compile_between_edge_owned :
    forall fresh start final r p l q,
      start < fresh ->
      final < fresh ->
      In (p, l, q) (sss_edges (sss_compile_between fresh start final r)) ->
      sss_owned_state fresh start final
        (sss_next (sss_compile_between fresh start final r)) p /\
      sss_owned_state fresh start final
        (sss_next (sss_compile_between fresh start final r)) q.
  Proof.
    intros fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final p l q Hstart Hfinal Hin; simpl in *.
    - contradiction.
    - destruct Hin as [Hin | []].
      inversion Hin; subst; unfold sss_owned_state; auto.
    - destruct Hin as [Hin | []].
      inversion Hin; subst; unfold sss_owned_state; auto.
    - set (f1 := sss_compile_between fresh start final r1) in *.
      set (r2_start := sss_next f1) in *.
      set (r2_final := S r2_start) in *.
      set (f2 := sss_compile_between (S (S r2_start)) r2_start r2_final r2) in *.
      change
        (sss_owned_state fresh start final (sss_next f2) p /\
         sss_owned_state fresh start final (sss_next f2) q).
      pose proof (sss_compile_between_next_ge fresh start final r1) as Hn1.
      fold f1 in Hn1. fold r2_start in Hn1.
      pose proof
        (sss_compile_between_next_ge
           (S (S r2_start)) r2_start r2_final r2) as Hn2.
      fold f2 in Hn2.
      apply in_app_or in Hin as [Hin | Hin].
      + destruct (IH1 fresh start final p l q Hstart Hfinal Hin)
          as [Hp Hq].
        fold f1 in Hp, Hq. unfold sss_owned_state in *.
        destruct Hp as [-> | [-> | Hp]];
          destruct Hq as [-> | [-> | Hq]]; repeat (first [left; reflexivity | right]); lia.
      + destruct Hin as [H | [H | Hin]].
        * inversion H; subst. unfold sss_owned_state. split; auto.
          right; right; lia.
        * inversion H; subst. unfold sss_owned_state. split; auto.
          right; right; lia.
        * assert (Hr2s : r2_start < S (S r2_start)) by lia.
          assert (Hr2f : r2_final < S (S r2_start)) by lia.
          destruct
            (IH2 (S (S r2_start)) r2_start r2_final p l q
               Hr2s Hr2f Hin)
            as [Hp Hq].
          fold f2 in Hp, Hq. unfold sss_owned_state in *.
          destruct Hp as [-> | [-> | Hp]];
            destruct Hq as [-> | [-> | Hq]];
            repeat (first [left; reflexivity | right]); lia.
    - set (f1 := sss_compile_between (S fresh) start fresh r1) in *.
      set (f2 := sss_compile_between (sss_next f1) fresh final r2) in *.
      change
        (sss_owned_state fresh start final (sss_next f2) p /\
         sss_owned_state fresh start final (sss_next f2) q).
      pose proof (sss_compile_between_next_ge (S fresh) start fresh r1) as Hn1.
      fold f1 in Hn1.
      pose proof
        (sss_compile_between_next_ge (sss_next f1) fresh final r2) as Hn2.
      fold f2 in Hn2.
      apply in_app_or in Hin as [Hin | Hin].
      + assert (Hstart1 : start < S fresh) by lia.
        assert (Hfinal1 : fresh < S fresh) by lia.
        destruct (IH1 (S fresh) start fresh p l q Hstart1 Hfinal1 Hin)
          as [Hp Hq].
        fold f1 in Hp, Hq. unfold sss_owned_state in *.
        destruct Hp as [-> | [-> | Hp]];
          destruct Hq as [-> | [-> | Hq]];
          repeat (first [left; reflexivity | right]); lia.
      + assert (Hfresh2 : fresh < sss_next f1) by lia.
        assert (Hfinal2 : final < sss_next f1) by lia.
        destruct
          (IH2 (sss_next f1) fresh final p l q Hfresh2 Hfinal2 Hin)
          as [Hp Hq].
        fold f2 in Hp, Hq. unfold sss_owned_state in *.
        destruct Hp as [-> | [-> | Hp]];
          destruct Hq as [-> | [-> | Hq]];
          repeat (first [left; reflexivity | right]); lia.
    - set (body := sss_compile_between (S (S fresh)) fresh (S fresh) r) in *.
      change
        (sss_owned_state fresh start final (sss_next body) p /\
         sss_owned_state fresh start final (sss_next body) q).
      pose proof
        (sss_compile_between_next_ge (S (S fresh)) fresh (S fresh) r)
        as Hnbody.
      fold body in Hnbody.
      destruct Hin as [H | [H | [H | Hin]]].
      + inversion H; subst. unfold sss_owned_state. split; auto.
        right; right; lia.
      + inversion H; subst. unfold sss_owned_state. split; auto.
        right; right; lia.
      + inversion H; subst. unfold sss_owned_state. split; right; right; lia.
      + assert (Hbs : fresh < S (S fresh)) by lia.
        assert (Hbf : S fresh < S (S fresh)) by lia.
        destruct (IH (S (S fresh)) fresh (S fresh) p l q Hbs Hbf Hin)
          as [Hp Hq].
        fold body in Hp, Hq. unfold sss_owned_state in *.
        destruct Hp as [-> | [-> | Hp]];
          destruct Hq as [-> | [-> | Hq]];
          repeat (first [left; reflexivity | right]); lia.
  Qed.

  Lemma sss_compile_between_no_edge_to_start :
    forall fresh start final r p l,
      start < fresh ->
      final < fresh ->
      start <> final ->
      ~ In (p, l, start)
          (sss_edges (sss_compile_between fresh start final r)).
  Proof.
    intros fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final p l Hstart Hfinal Hneq Hin; simpl in *.
    - contradiction.
    - destruct Hin as [H | []]. inversion H; subst; contradiction.
    - destruct Hin as [H | []]. inversion H; subst; contradiction.
    - set (f1 := sss_compile_between fresh start final r1) in *.
      set (r2_start := sss_next f1) in *.
      set (r2_final := S r2_start) in *.
      set (f2 := sss_compile_between (S (S r2_start)) r2_start r2_final r2) in *.
      pose proof (sss_compile_between_next_ge fresh start final r1) as Hn1.
      fold f1 in Hn1. fold r2_start in Hn1.
      apply in_app_or in Hin as [Hin | Hin].
      + exact (IH1 fresh start final p l Hstart Hfinal Hneq Hin).
      + destruct Hin as [H | [H | Hin]].
        * pose proof (f_equal sss_edge_dst H) as Hdst.
          simpl in Hdst. lia.
        * pose proof (f_equal sss_edge_dst H) as Hdst.
          simpl in Hdst. congruence.
        * assert (Hr2s : r2_start < S (S r2_start)) by lia.
          assert (Hr2f : r2_final < S (S r2_start)) by lia.
          destruct
            (sss_compile_between_edge_owned
               (S (S r2_start)) r2_start r2_final r2 p l start
               Hr2s Hr2f Hin)
            as [_ Hdst].
          unfold sss_owned_state in Hdst. lia.
    - set (f1 := sss_compile_between (S fresh) start fresh r1) in *.
      set (f2 := sss_compile_between (sss_next f1) fresh final r2) in *.
      pose proof (sss_compile_between_next_ge (S fresh) start fresh r1) as Hn1.
      fold f1 in Hn1.
      apply in_app_or in Hin as [Hin | Hin].
      + assert (Hstart1 : start < S fresh) by lia.
        assert (Hfinal1 : fresh < S fresh) by lia.
        assert (Hneq1 : start <> fresh) by lia.
        exact (IH1 (S fresh) start fresh p l Hstart1 Hfinal1 Hneq1 Hin).
      + assert (Hfresh2 : fresh < sss_next f1) by lia.
        assert (Hfinal2 : final < sss_next f1) by lia.
        destruct
          (sss_compile_between_edge_owned
             (sss_next f1) fresh final r2 p l start
             Hfresh2 Hfinal2 Hin)
          as [_ Hdst].
        unfold sss_owned_state in Hdst. lia.
    - set (body := sss_compile_between (S (S fresh)) fresh (S fresh) r) in *.
      destruct Hin as [H | [H | [H | Hin]]].
      + inversion H; subst; lia.
      + inversion H; subst; contradiction.
      + inversion H; subst; lia.
      + assert (Hbs : fresh < S (S fresh)) by lia.
        assert (Hbf : S fresh < S (S fresh)) by lia.
        destruct
          (sss_compile_between_edge_owned
             (S (S fresh)) fresh (S fresh) r p l start Hbs Hbf Hin)
          as [_ Hdst].
        unfold sss_owned_state in Hdst. lia.
  Qed.

  Lemma sss_compile_between_no_edge_from_final :
    forall fresh start final r l q,
      start < fresh ->
      final < fresh ->
      start <> final ->
      ~ In (final, l, q)
          (sss_edges (sss_compile_between fresh start final r)).
  Proof.
    intros fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final l q Hstart Hfinal Hneq Hin; simpl in *.
    - contradiction.
    - destruct Hin as [H | []]. inversion H; subst; contradiction.
    - destruct Hin as [H | []]. inversion H; subst; contradiction.
    - set (f1 := sss_compile_between fresh start final r1) in *.
      set (r2_start := sss_next f1) in *.
      set (r2_final := S r2_start) in *.
      set (f2 := sss_compile_between (S (S r2_start)) r2_start r2_final r2) in *.
      pose proof (sss_compile_between_next_ge fresh start final r1) as Hn1.
      fold f1 in Hn1. fold r2_start in Hn1.
      apply in_app_or in Hin as [Hin | Hin].
      + exact (IH1 fresh start final l q Hstart Hfinal Hneq Hin).
      + destruct Hin as [H | [H | Hin]].
        * pose proof (f_equal sss_edge_src H) as Hsrc.
          simpl in Hsrc. congruence.
        * pose proof (f_equal sss_edge_src H) as Hsrc.
          simpl in Hsrc. lia.
        * assert (Hr2s : r2_start < S (S r2_start)) by lia.
          assert (Hr2f : r2_final < S (S r2_start)) by lia.
          destruct
            (sss_compile_between_edge_owned
               (S (S r2_start)) r2_start r2_final r2 final l q
               Hr2s Hr2f Hin)
            as [Hsrc _].
          unfold sss_owned_state in Hsrc. lia.
    - set (f1 := sss_compile_between (S fresh) start fresh r1) in *.
      set (f2 := sss_compile_between (sss_next f1) fresh final r2) in *.
      pose proof (sss_compile_between_next_ge (S fresh) start fresh r1) as Hn1.
      fold f1 in Hn1.
      apply in_app_or in Hin as [Hin | Hin].
      + assert (Hstart1 : start < S fresh) by lia.
        assert (Hfinal1 : fresh < S fresh) by lia.
        destruct
          (sss_compile_between_edge_owned
             (S fresh) start fresh r1 final l q Hstart1 Hfinal1 Hin)
          as [Hsrc _].
        unfold sss_owned_state in Hsrc. lia.
      + assert (Hfresh2 : fresh < sss_next f1) by lia.
        assert (Hfinal2 : final < sss_next f1) by lia.
        assert (Hneq2 : fresh <> final) by lia.
        exact (IH2 (sss_next f1) fresh final l q Hfresh2 Hfinal2 Hneq2 Hin).
    - set (body := sss_compile_between (S (S fresh)) fresh (S fresh) r) in *.
      destruct Hin as [H | [H | [H | Hin]]].
      + inversion H; subst; contradiction.
      + inversion H; subst; lia.
      + inversion H; subst; lia.
      + assert (Hbs : fresh < S (S fresh)) by lia.
        assert (Hbf : S fresh < S (S fresh)) by lia.
        destruct
          (sss_compile_between_edge_owned
             (S (S fresh)) fresh (S fresh) r final l q Hbs Hbf Hin)
          as [Hsrc _].
        unfold sss_owned_state in Hsrc. lia.
  Qed.

  Lemma sss_compile_edges_range :
    forall fresh r p l q,
      In (p, l, q) (sss_edges (sss_compile_from fresh r)) ->
      fresh <= p /\ p < sss_next (sss_compile_from fresh r) /\
      fresh <= q /\ q < sss_next (sss_compile_from fresh r).
  Proof.
    intros fresh r p l q Hin.
    unfold sss_compile_from in *.
    pose proof
      (sss_compile_between_edges_lower
         (S (S fresh)) fresh (S fresh) r fresh p l q)
      as Hlower.
    pose proof
      (sss_compile_between_edges_upper
         (S (S fresh)) fresh (S fresh) r p l q)
      as Hupper.
    destruct Hlower as [Hpl Hql]; try lia; auto.
    destruct Hupper as [Hpu Hqu]; try lia; auto.
  Qed.

  Lemma sss_compile_edge_src_range :
    forall fresh r p l q,
      In (p, l, q) (sss_edges (sss_compile_from fresh r)) ->
      fresh <= p /\ p < sss_next (sss_compile_from fresh r).
  Proof.
    intros fresh r p l q Hin.
    destruct (sss_compile_edges_range fresh r p l q Hin)
      as [Hp0 [Hp1 _]].
    auto.
  Qed.

  Lemma sss_compile_edge_dst_range :
    forall fresh r p l q,
      In (p, l, q) (sss_edges (sss_compile_from fresh r)) ->
      fresh <= q /\ q < sss_next (sss_compile_from fresh r).
  Proof.
    intros fresh r p l q Hin.
    destruct (sss_compile_edges_range fresh r p l q Hin)
      as [_ [_ [Hq0 Hq1]]].
    auto.
  Qed.

  Lemma sss_compile_no_edge_from_next :
    forall fresh r l q,
      ~ In
          (sss_next (sss_compile_from fresh r), l, q)
          (sss_edges (sss_compile_from fresh r)).
  Proof.
    intros fresh r l q Hin.
    pose proof
      (sss_compile_edges_range
         fresh r (sss_next (sss_compile_from fresh r)) l q Hin)
      as [_ [Hlt _]].
    lia.
  Qed.

  Lemma sss_start_in_states :
    forall f, In (sss_start f) (sss_fragment_states f).
  Proof.
    intros f.
    unfold sss_fragment_states.
    apply nodup_In.
    simpl. auto.
  Qed.

  Lemma sss_final_in_states :
    forall f, In (sss_final f) (sss_fragment_states f).
  Proof.
    intros f.
    unfold sss_fragment_states.
    apply nodup_In.
    simpl. auto.
  Qed.

  Lemma sss_edge_src_in_states :
    forall f e,
      In e (sss_edges f) ->
      In (sss_edge_src e) (sss_fragment_states f).
  Proof.
    intros f e He.
    unfold sss_fragment_states.
    apply nodup_In.
    simpl. right. right.
    apply in_concat.
    exists [sss_edge_src e; sss_edge_dst e].
    split.
    - apply in_map_iff. exists e. split; [reflexivity | exact He].
    - simpl; auto.
  Qed.

  Lemma sss_edge_dst_in_states :
    forall f e,
      In e (sss_edges f) ->
      In (sss_edge_dst e) (sss_fragment_states f).
  Proof.
    intros f e He.
    unfold sss_fragment_states.
    apply nodup_In.
    simpl. right. right.
    apply in_concat.
    exists [sss_edge_src e; sss_edge_dst e].
    split.
    - apply in_map_iff. exists e. split; [reflexivity | exact He].
    - simpl; auto.
  Qed.

  Lemma sss_step_edge_witness :
    forall label_matches edges p l q,
      In q (sss_step label_matches edges p l) ->
      exists e,
        In e edges /\
        sss_edge_src e = p /\
        sss_edge_matches label_matches l e = true /\
        sss_edge_dst e = q.
  Proof.
    intros label_matches edges p l q Hq.
    unfold sss_step in Hq.
    apply nodup_In in Hq.
    apply in_map_iff in Hq as [e [Hq He]].
    apply filter_In in He as [He Hmatch].
    apply andb_true_iff in Hmatch as [Hsrc Hlabel].
    apply Nat.eqb_eq in Hsrc.
    exists e. repeat split; auto.
  Qed.

  Lemma sss_compile_edge_symbol :
    forall fresh r p b q,
      In (p, Some b, q) (sss_edges (sss_compile_from fresh r)) ->
      In b (regex_symbols r).
  Proof.
    intros fresh r p b q Hin.
    unfold sss_compile_from in Hin.
    assert
      (Hbetween :
        forall fresh0 start final r0 p0 b0 q0,
          In (p0, Some b0, q0)
            (sss_edges (sss_compile_between fresh0 start final r0)) ->
          In b0 (regex_symbols r0)).
    {
      clear fresh r p b q Hin.
      intros fresh0 start final r0.
      revert fresh0 start final.
      induction r0 as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
        intros fresh0 start final p b q Hin; simpl in *.
      - contradiction.
      - destruct Hin as [Hin | []]. inversion Hin.
      - destruct Hin as [Hin | []].
        inversion Hin; subst. simpl. auto.
      - set (f1 := sss_compile_between fresh0 start final r1) in *.
        set (r2_start := sss_next f1) in *.
        set (r2_final := S r2_start) in *.
        apply in_app_or in Hin as [Hin | Hin].
        + apply in_or_app. left. eapply IH1; eauto.
        + destruct Hin as [H | [H | Hin]].
          * inversion H.
          * inversion H.
          * apply in_or_app. right. eapply IH2; eauto.
      - set (f1 := sss_compile_between (S fresh0) start fresh0 r1) in *.
        apply in_app_or in Hin as [Hin | Hin].
        + apply in_or_app. left. eapply IH1; eauto.
        + apply in_or_app. right. eapply IH2; eauto.
      - destruct Hin as [H | [H | [H | Hin]]]; try inversion H.
        eapply IH; eauto.
    }
    eapply Hbetween; eauto.
  Qed.

  (** Bridge from the compiler to [finite_enfa_wf]. *)
  Theorem regex_Msss_wf :
    forall alphabet label_matches r,
      regex_symbol_closed alphabet label_matches r ->
      finite_enfa_wf (regex_Msss alphabet label_matches r).
  Proof.
    intros alphabet label_matches r Hclosed.
    unfold regex_Msss.
    set (f := sss_compile r).
    constructor; simpl.
    - unfold f, sss_compile. apply NoDup_nodup.
    - intros q Hq.
      simpl in Hq. destruct Hq as [Hq | []]. subst q.
      apply sss_start_in_states.
    - intros q l q' _ Hstep.
      apply sss_step_edge_witness in Hstep as [e [He [_ [_ Hdst]]]].
      subst q'.
      now apply sss_edge_dst_in_states.
    - intros q a q' _ Hstep.
      apply sss_step_edge_witness in Hstep as [e [He [_ [Hmatch Hdst]]]].
      destruct e as [[p [b|]] dst]; simpl in Hmatch; try discriminate.
      subst q'.
      eapply Hclosed.
      + unfold f, sss_compile in He.
        eapply sss_compile_edge_symbol; eauto.
      + exact Hmatch.
    - intros q l _.
      unfold sss_step.
      apply NoDup_nodup.
  Qed.

  Definition enfa_accepts_word (m : @finite_enfa A) (w : list A) : Prop :=
    exists s q t,
      In s (enfa_start (fenfa_base m)) /\
      valid_trace m s t q /\
      trace_word t = w /\
      enfa_final (fenfa_base m) q = true.

  Definition sss_trace : Type := list ((nat * option A) * nat).

  Fixpoint sss_trace_word (t : sss_trace) : list A :=
    match t with
    | [] => []
    | ((_, None), _) :: t' => sss_trace_word t'
    | ((_, Some a), _) :: t' => a :: sss_trace_word t'
    end.

  Inductive sss_valid_trace
      (label_matches : A -> A -> bool)
      (edges : list (nat * option A * nat))
      : nat -> sss_trace -> nat -> Prop :=
  | SSSValid_nil :
      forall q,
        sss_valid_trace label_matches edges q [] q
  | SSSValid_cons :
      forall p l q r t,
        In (p, l, q) edges ->
        sss_edge_matches label_matches l (p, l, q) = true ->
        sss_valid_trace label_matches edges q t r ->
        sss_valid_trace label_matches edges p (((p, l), q) :: t) r.

  Lemma sss_valid_trace_no_edges_from :
    forall label_matches edges p t q,
      (forall l q', ~ In (p, l, q') edges) ->
      sss_valid_trace label_matches edges p t q ->
      t = [] /\ q = p.
  Proof.
    intros label_matches edges p t q Hnone Htrace.
    inversion Htrace as [q'| p' l q' r t' Hedge Hmatch Htail]; subst.
    - split; reflexivity.
    - exfalso. eapply Hnone; eauto.
  Qed.

  Lemma sss_valid_trace_edges_mono :
    forall label_matches edges1 edges2 p t q,
      (forall e, In e edges1 -> In e edges2) ->
      sss_valid_trace label_matches edges1 p t q ->
      sss_valid_trace label_matches edges2 p t q.
  Proof.
    intros label_matches edges1 edges2 p t q Hincl Htrace.
    induction Htrace as [q| p l q r t Hedge Hmatch _ IH].
    - constructor.
    - econstructor; eauto.
  Qed.

  Lemma sss_valid_trace_app :
    forall label_matches edges p t q u r,
      sss_valid_trace label_matches edges p t q ->
      sss_valid_trace label_matches edges q u r ->
      sss_valid_trace label_matches edges p (t ++ u) r.
  Proof.
    intros label_matches edges p t q u r Ht Hu.
    induction Ht as [q| p l q r' t Hedge Hmatch _ IH]; simpl.
    - exact Hu.
    - econstructor; eauto.
  Qed.

  Lemma sss_trace_word_app :
    forall t u,
      sss_trace_word (t ++ u) = sss_trace_word t ++ sss_trace_word u.
  Proof.
    induction t as [| [[p [a|]] q] t IH]; intros u; simpl; auto.
    now rewrite IH.
  Qed.

  Lemma sss_valid_trace_inside :
    forall label_matches full_edges inner_edges
      (inside : nat -> Prop) p t q,
      (forall x l y,
        inside x ->
        In (x, l, y) full_edges ->
        In (x, l, y) inner_edges) ->
      (forall x l y,
        In (x, l, y) inner_edges -> inside y) ->
      inside p ->
      sss_valid_trace label_matches full_edges p t q ->
      sss_valid_trace label_matches inner_edges p t q.
  Proof.
    intros label_matches full_edges inner_edges inside p t q
      Hclass Hdst Hp Htrace.
    revert Hp.
    induction Htrace as [q| p l q r t Hedge Hmatch _ IH];
      intros Hp.
    - constructor.
    - econstructor.
      + eapply Hclass; eauto.
      + exact Hmatch.
      + apply IH. eapply Hdst. eapply Hclass; eauto.
  Qed.

  Lemma sss_valid_trace_exit_decompose :
    forall label_matches full_edges inner_edges
      (inside : nat -> Prop) exit_src exit_label exit_dst p t,
      (forall x l y,
        inside x ->
        In (x, l, y) full_edges ->
        In (x, l, y) inner_edges \/
        (x = exit_src /\ l = exit_label /\ y = exit_dst)) ->
      (forall x l y,
        In (x, l, y) inner_edges -> inside y) ->
      (forall l y, ~ In (exit_dst, l, y) full_edges) ->
      ~ inside exit_dst ->
      inside p ->
      sss_valid_trace label_matches full_edges p t exit_dst ->
      exists t_inner,
        t = t_inner ++ [((exit_src, exit_label), exit_dst)] /\
        sss_valid_trace label_matches inner_edges p t_inner exit_src.
  Proof.
    intros label_matches full_edges inner_edges inside
      exit_src exit_label exit_dst p t Hclass Hdst Hexit_none
      Hexit_not_inside Hp Htrace.
    revert Hp.
    induction Htrace as [q| p l q r t Hedge Hmatch Htail IH];
      intros Hp.
    - exfalso. now apply Hexit_not_inside.
    - destruct (Hclass p l q Hp Hedge) as [Hinner | [Hp_src [Hl Hq]]].
      + destruct (IH Hclass Hexit_none Hexit_not_inside
          (Hdst p l q Hinner)) as
          [t_inner [Ht Hvalid]].
        exists (((p, l), q) :: t_inner). split.
        * simpl. now rewrite Ht.
        * econstructor; eauto.
      + subst p l q.
        destruct
          (sss_valid_trace_no_edges_from
             label_matches full_edges r t r Hexit_none Htail)
          as [Ht Hend].
        subst t.
        exists []. split; simpl; [reflexivity | constructor].
  Qed.

  Lemma sss_valid_trace_exit_prefix_decompose :
    forall label_matches full_edges inner_edges
      (inside : nat -> Prop) exit_src exit_label exit_dst
      p t target,
      (forall x l y,
        inside x ->
        In (x, l, y) full_edges ->
        In (x, l, y) inner_edges \/
        (x = exit_src /\ l = exit_label /\ y = exit_dst)) ->
      (forall x l y,
        In (x, l, y) inner_edges -> inside y) ->
      ~ inside target ->
      inside p ->
      sss_valid_trace label_matches full_edges p t target ->
      exists t_inner t_rest,
        t = t_inner ++ [((exit_src, exit_label), exit_dst)] ++ t_rest /\
        sss_valid_trace label_matches inner_edges p t_inner exit_src /\
        sss_valid_trace label_matches full_edges exit_dst t_rest target.
  Proof.
    intros label_matches full_edges inner_edges inside
      exit_src exit_label exit_dst p t target Hclass Hdst
      Htarget_not_inside Hp Htrace.
    revert Hp.
    induction Htrace as [q| p l q r t Hedge Hmatch Htail IH];
      intros Hp.
    - exfalso. now apply Htarget_not_inside.
    - destruct (Hclass p l q Hp Hedge) as [Hinner | [Hp_src [Hl Hq]]].
      + destruct (IH Htarget_not_inside (Hdst p l q Hinner)) as
          [t_inner [t_rest [Ht [Hvalid Hrest]]]].
        exists (((p, l), q) :: t_inner), t_rest.
        split.
        * simpl. now rewrite Ht.
        * split; [| exact Hrest].
          econstructor; eauto.
      + subst p l q.
        exists [], t.
        split; simpl; [reflexivity |].
        split; [constructor | exact Htail].
  Qed.

  Lemma sss_valid_trace_shared_decompose :
    forall label_matches full_edges left_edges right_edges
      (left right : nat -> Prop) cut p t q,
      (forall x l y,
        left x ->
        x <> cut ->
        In (x, l, y) full_edges ->
        In (x, l, y) left_edges) ->
      (forall x l y,
        In (x, l, y) left_edges -> left y) ->
      (forall x l y,
        right x ->
        In (x, l, y) full_edges ->
        In (x, l, y) right_edges) ->
      (forall x l y,
        In (x, l, y) right_edges -> right y) ->
      left p ->
      right cut ->
      ~ left q ->
      sss_valid_trace label_matches full_edges p t q ->
      exists t_left t_right,
        t = t_left ++ t_right /\
        sss_valid_trace label_matches left_edges p t_left cut /\
        sss_valid_trace label_matches right_edges cut t_right q.
  Proof.
    intros label_matches full_edges left_edges right_edges left right
      cut p t q Hleft_class Hleft_dst Hright_class Hright_dst
      Hleft_p Hright_cut Hq_not_left Htrace.
    revert Hleft_p.
    induction Htrace as [q| p l y r t Hedge Hmatch Htail IH];
      intros Hleft_p.
    - exfalso. now apply Hq_not_left.
    - destruct (Nat.eq_dec p cut) as [Hp_cut | Hp_not_cut].
      + subst p.
        exists [], (((cut, l), y) :: t).
        split; simpl; [reflexivity |].
        split; [constructor |].
        eapply sss_valid_trace_inside with
          (full_edges := full_edges)
          (inside := right).
        * intros x l' y' Hright_x Hin.
          eapply Hright_class; eauto.
        * exact Hright_dst.
        * exact Hright_cut.
        * econstructor; eauto.
      + assert (Hedge_left : In (p, l, y) left_edges).
        { eapply Hleft_class; eauto. }
        destruct (IH Hq_not_left (Hleft_dst p l y Hedge_left)) as
          [t_left [t_right [Ht [Hvalid_left Hvalid_right]]]].
        exists (((p, l), y) :: t_left), t_right.
        split.
        * simpl. now rewrite Ht.
        * split; [| exact Hvalid_right].
          econstructor; eauto.
  Qed.

  Lemma sss_valid_trace_nil_inv :
    forall label_matches edges p q,
      sss_valid_trace label_matches edges p [] q -> p = q.
  Proof.
    intros label_matches edges p q Htrace.
    inversion Htrace. reflexivity.
  Qed.

  Lemma sss_valid_trace_cons_inv :
    forall label_matches edges p e t q,
      sss_valid_trace label_matches edges p (e :: t) q ->
      exists l r,
        e = ((p, l), r) /\
        In (p, l, r) edges /\
        sss_edge_matches label_matches l (p, l, r) = true /\
        sss_valid_trace label_matches edges r t q.
  Proof.
    intros label_matches edges p [[src l] dst] t q Htrace.
    inversion Htrace as [| p' l' q' r' t' Hedge Hmatch Htail];
      subst.
    exists l, dst. repeat split; auto.
  Qed.

  Lemma sss_direct_edge_valid :
    forall label_matches edges p l q,
      In (p, l, q) edges ->
      sss_edge_matches label_matches l (p, l, q) = true ->
      sss_valid_trace label_matches edges p [((p, l), q)] q.
  Proof.
    intros label_matches edges p l q Hedge Hmatch.
    econstructor; eauto.
    constructor.
  Qed.

  Lemma sss_step_contains_edge :
    forall label_matches edges p l q,
      In (p, l, q) edges ->
      sss_edge_matches label_matches l (p, l, q) = true ->
      In q (sss_step label_matches edges p l).
  Proof.
    intros label_matches edges p l q Hedge Hmatch.
    unfold sss_step.
    apply nodup_In.
    apply in_map_iff.
    exists (p, l, q). split; [reflexivity |].
    apply filter_In. split; [exact Hedge |].
    simpl.
    rewrite Nat.eqb_refl. simpl.
    exact Hmatch.
  Qed.

  Lemma sss_valid_trace_to_valid_trace :
    forall (alphabet : list A) label_matches
      (edges : list (nat * option A * nat))
      (finals : nat -> bool) (states : list nat) p t q,
      sss_valid_trace label_matches edges p t q ->
      @valid_trace A
        {|
          fenfa_base :=
            {|
              enfa_state := nat;
              enfa_start := [];
              enfa_final := finals;
              enfa_step := sss_step label_matches edges
            |};
          fenfa_states := states;
          fenfa_alphabet := alphabet;
          fenfa_state_eqb := Nat.eqb;
          fenfa_state_eqb_sound := fun x y H => proj1 (Nat.eqb_eq x y) H;
          fenfa_state_eqb_complete := fun x y H => proj2 (Nat.eqb_eq x y) H
        |} p t q.
  Proof.
    intros alphabet label_matches edges finals states p t q Htrace.
    induction Htrace as [q| p l q r t Hedge Hmatch _ IH].
    - constructor.
    - econstructor; eauto.
      now apply sss_step_contains_edge.
  Qed.

  Definition label_matches_reflects_eq
      (label_matches : A -> A -> bool) : Prop :=
    (forall a, label_matches a a = true) /\
    (forall a b, label_matches a b = true -> a = b).

  (** Definition 7 language correctness needs executable boolean matching
      [label_matches] to reflect semantic equality; [label_matches_reflects_eq]
      The bridge below converts [regex_Msss] ENFA traces back into SSS
      fragment traces for the complete direction. *)
  Lemma valid_trace_to_sss_valid_trace :
    forall (alphabet : list A) label_matches
      (edges : list (nat * option A * nat))
      (finals : nat -> bool) (states : list nat) p t q,
      label_matches_reflects_eq label_matches ->
      @valid_trace A
        {|
          fenfa_base :=
            {|
              enfa_state := nat;
              enfa_start := [];
              enfa_final := finals;
              enfa_step := sss_step label_matches edges
            |};
          fenfa_states := states;
          fenfa_alphabet := alphabet;
          fenfa_state_eqb := Nat.eqb;
          fenfa_state_eqb_sound := fun x y H => proj1 (Nat.eqb_eq x y) H;
          fenfa_state_eqb_complete := fun x y H => proj2 (Nat.eqb_eq x y) H
        |} p t q ->
      sss_valid_trace label_matches edges p t q.
  Proof.
    intros alphabet label_matches edges finals states p t q Hreflect Htrace.
    induction Htrace as [q| p l q r t Hstep _ IH].
    - constructor.
    - apply sss_step_edge_witness in Hstep as
        [e [Hedge [Hsrc [Hmatch Hdst]]]].
      destruct e as [[src edge_l] dst].
      simpl in Hsrc, Hdst. subst src dst.
      destruct edge_l as [b|], l as [a|]; simpl in Hmatch; try discriminate.
      + destruct Hreflect as [_ Hsound].
        specialize (Hsound b a Hmatch). subst b.
        econstructor; eauto.
      + econstructor; eauto.
  Qed.

  Lemma regex_Msss_valid_trace_to_sss_valid :
    forall alphabet label_matches r p t q,
      label_matches_reflects_eq label_matches ->
      valid_trace (regex_Msss alphabet label_matches r) p t q ->
      sss_valid_trace
        label_matches
        (sss_edges (sss_compile r))
        p t q.
  Proof.
    intros alphabet label_matches r p t q Hreflect Htrace.
    induction Htrace as [q| p l q r' t Hstep _ IH].
    - constructor.
    - unfold regex_Msss, sss_compile in Hstep.
      simpl in Hstep.
      apply sss_step_edge_witness in Hstep as
        [e [Hedge [Hsrc [Hmatch Hdst]]]].
      destruct e as [[src edge_l] dst].
      simpl in Hsrc, Hdst. subst src dst.
      destruct edge_l as [b|], l as [a|]; simpl in Hmatch; try discriminate.
      + destruct Hreflect as [_ Hsound].
        specialize (Hsound b a Hmatch). subst b.
        econstructor; eauto.
      + econstructor; eauto.
  Qed.

  Lemma regex_Msss_accepts_word_sss_trace :
    forall alphabet label_matches r w,
      label_matches_reflects_eq label_matches ->
      enfa_accepts_word (regex_Msss alphabet label_matches r) w ->
      exists t,
        sss_valid_trace
          label_matches
          (sss_edges (sss_compile r))
          (sss_start (sss_compile r))
          t
          (sss_final (sss_compile r)) /\
        sss_trace_word t = w.
  Proof.
    intros alphabet label_matches r w Hreflect Hacc.
    unfold enfa_accepts_word in Hacc.
    destruct Hacc as [s [q [t [Hstart [Htrace [Hword Hfinal]]]]]].
    unfold regex_Msss in Hstart, Htrace, Hfinal.
    set (f := sss_compile r) in *.
    simpl in Hstart, Htrace, Hfinal.
    destruct Hstart as [Hstart | []]. subst s.
    apply Nat.eqb_eq in Hfinal. subst q.
    exists t. split.
    - subst f. eapply regex_Msss_valid_trace_to_sss_valid; eauto.
    - assert (Htw : trace_word t = sss_trace_word t).
      {
        clear Htrace Hword.
        induction t as [| [[p l] q] t IH]; simpl; auto.
        destruct l as [a|]; simpl.
        - f_equal. exact IH.
        - exact IH.
      }
      rewrite Htw in Hword. exact Hword.
  Qed.

  (** Regex -> Msss sound: a regex match gives an accepting fragment trace. *)
  Lemma sss_compile_between_sound :
    forall label_matches fresh start final r w,
      label_matches_reflects_eq label_matches ->
      matches r w ->
      exists t,
        sss_valid_trace
          label_matches
          (sss_edges (sss_compile_between fresh start final r))
          start
          t
          final /\
        sss_trace_word t = w.
  Proof.
    intros label_matches fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final w Hreflect Hmatch; inversion Hmatch; subst; simpl.
    - destruct Hreflect as [Hrefl _].
      exists [((start, None), final)]. split.
      + apply sss_direct_edge_valid; simpl; auto.
      + reflexivity.
    - destruct Hreflect as [Hrefl _].
      exists [((start, Some a), final)]. split.
      + apply sss_direct_edge_valid.
        * simpl; auto.
        * simpl. apply Hrefl.
      + reflexivity.
    - set (f1 := sss_compile_between fresh start final r1).
      set (r2_start := sss_next f1).
      set (r2_final := S r2_start).
      set (f2 := sss_compile_between (S (S r2_start)) r2_start r2_final r2).
      destruct (IH1 fresh start final w Hreflect H2) as [t [Ht Hword]].
      exists t. split.
      + eapply sss_valid_trace_edges_mono; [| exact Ht].
        intros e He. apply in_or_app. left. exact He.
      + exact Hword.
    - set (f1 := sss_compile_between fresh start final r1).
      set (r2_start := sss_next f1).
      set (r2_final := S r2_start).
      set (f2 := sss_compile_between (S (S r2_start)) r2_start r2_final r2).
      destruct
        (IH2 (S (S r2_start)) r2_start r2_final w Hreflect H2)
        as [t [Ht Hword]].
      exists ([((start, None), r2_start)] ++
              t ++ [((r2_final, None), final)]).
      split.
      + simpl.
        econstructor.
        * apply in_or_app. right. simpl. auto.
        * reflexivity.
        * eapply sss_valid_trace_app.
          -- eapply sss_valid_trace_edges_mono; [| exact Ht].
             intros e He. apply in_or_app. right. simpl. right. right.
             exact He.
          -- apply sss_direct_edge_valid.
             ++ apply in_or_app. right. simpl. auto.
             ++ reflexivity.
      + rewrite !sss_trace_word_app. simpl.
        rewrite Hword. now rewrite app_nil_r.
    - set (mid := fresh).
      set (f1 := sss_compile_between (S fresh) start mid r1).
      set (f2 := sss_compile_between (sss_next f1) mid final r2).
      destruct (IH1 (S fresh) start mid w1 Hreflect H1)
        as [t1 [Ht1 Hword1]].
      destruct (IH2 (sss_next f1) mid final w2 Hreflect H3)
        as [t2 [Ht2 Hword2]].
      exists (t1 ++ t2). split.
      + eapply sss_valid_trace_app.
        * eapply sss_valid_trace_edges_mono; [| exact Ht1].
          intros e He. apply in_or_app. left. exact He.
        * eapply sss_valid_trace_edges_mono; [| exact Ht2].
          intros e He. apply in_or_app. right. exact He.
      + rewrite sss_trace_word_app.
        now rewrite Hword1, Hword2.
    - set (body_start := fresh).
      set (body_final := S fresh).
      set (body :=
        sss_compile_between (S (S fresh)) body_start body_final r).
      exists ([((start, None), body_start)] ++
              [((body_start, None), final)]).
      split.
      + simpl.
        econstructor; simpl; eauto.
        econstructor; simpl; eauto.
        constructor.
      + reflexivity.
    - set (body_start := fresh).
      set (body_final := S fresh).
      set (body :=
        sss_compile_between (S (S fresh)) body_start body_final r).
      assert
        (Hloop :
          forall w,
            matches (Star r) w ->
            exists t,
              sss_valid_trace
                label_matches
                ([ sss_edge start None body_start;
                   sss_edge body_start None final;
                   sss_edge body_final None body_start ] ++
                 sss_edges body)
                body_start t final /\
              sss_trace_word t = w).
      {
        intros wstar Hstar.
        clear Hmatch H0 H1 H2.
        remember (Star r) as star_re eqn:Hstar_re.
        induction Hstar; inversion Hstar_re; subst.
        - exists [((body_start, None), final)]. split.
          + apply sss_direct_edge_valid; simpl; auto.
          + reflexivity.
        - destruct
            (IH (S (S fresh)) body_start body_final w0 Hreflect Hstar1)
            as [tbody [Htbody Hword1]].
          destruct (IHHstar2 eq_refl) as [trest [Hrest Hword2]].
          exists (tbody ++ [((body_final, None), body_start)] ++ trest).
          split.
          + eapply sss_valid_trace_app.
            * eapply sss_valid_trace_edges_mono; [| exact Htbody].
              intros e He. repeat right. exact He.
            * econstructor.
              -- simpl. auto.
              -- reflexivity.
              -- exact Hrest.
          + rewrite !sss_trace_word_app. simpl.
            now rewrite Hword1, Hword2.
      }
      destruct (Hloop (w1 ++ w2) Hmatch) as [tloop [Htrace Hword]].
      exists ([((start, None), body_start)] ++ tloop). split.
      + simpl.
        econstructor; simpl; eauto.
      + simpl. exact Hword.
  Qed.

  Lemma sss_compile_sound_from :
    forall label_matches fresh r w,
      label_matches_reflects_eq label_matches ->
      matches r w ->
      exists t,
        sss_valid_trace
          label_matches
          (sss_edges (sss_compile_from fresh r))
          (sss_start (sss_compile_from fresh r))
          t
          (sss_final (sss_compile_from fresh r)) /\
        sss_trace_word t = w.
  Proof.
    intros label_matches fresh r w Hreflect Hmatch.
    unfold sss_compile_from.
    rewrite sss_compile_between_start_eq.
    rewrite sss_compile_between_final_eq.
    apply sss_compile_between_sound; assumption.
  Qed.

  (** Language-equivalence specs between regex semantics and [Msss(E)]. *)
  Definition regex_Msss_language_sound_spec
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    forall w,
      matches r w ->
      enfa_accepts_word (regex_Msss alphabet label_matches r) w.

  Definition regex_Msss_language_complete_spec
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    forall w,
      enfa_accepts_word (regex_Msss alphabet label_matches r) w ->
      matches r w.

  Lemma regex_Msss_trace_word_eq :
    forall alphabet label_matches r
      (t : enfa_trace (regex_Msss alphabet label_matches r)),
      trace_word t = sss_trace_word t.
  Proof.
    intros alphabet label_matches r t.
    induction t as [| [[p l] q] t IH]; simpl; auto.
    destruct l as [a|]; simpl.
    - f_equal. exact IH.
    - exact IH.
  Qed.

  Lemma sss_valid_trace_to_regex_Msss_valid :
    forall alphabet label_matches r p t q,
      let f := sss_compile r in
      sss_valid_trace label_matches (sss_edges f) p t q ->
      valid_trace (regex_Msss alphabet label_matches r) p t q.
  Proof.
    intros alphabet label_matches r p t q f Htrace.
    unfold f in Htrace.
    induction Htrace as [q| p l q r' t Hedge Hmatch _ IH].
    - constructor.
    - unfold regex_Msss, sss_compile in *.
      simpl in *.
      econstructor; eauto.
      now apply sss_step_contains_edge.
  Qed.

  (** The proof of [regex_Msss_language_sound_spec]:
      A fragment-level sound trace embeds directly into [regex_Msss]. *)
  Theorem regex_Msss_language_sound :
    forall alphabet label_matches r,
      label_matches_reflects_eq label_matches ->
      regex_Msss_language_sound_spec alphabet label_matches r.
  Proof.
    intros alphabet label_matches r Hreflect w Hmatch.
    destruct (sss_compile_sound_from label_matches 0 r w Hreflect Hmatch)
      as [t [Htrace Hword]].
    unfold regex_Msss_language_sound_spec, enfa_accepts_word.
    set (f := sss_compile r) in *.
    exists (sss_start f), (sss_final f), t.
    repeat split.
    - unfold regex_Msss. fold f. simpl. auto.
    - apply sss_valid_trace_to_regex_Msss_valid.
      exact Htrace.
    - rewrite regex_Msss_trace_word_eq. exact Hword.
    - unfold regex_Msss. fold f. simpl.
      apply Nat.eqb_refl.
  Qed.

  (** Local inversions for the complete direction. *)
  Lemma sss_compile_empty_complete_from :
    forall label_matches fresh t,
      ~ sss_valid_trace
          label_matches
          (sss_edges (sss_compile_from fresh Empty))
          (sss_start (sss_compile_from fresh Empty))
          t
          (sss_final (sss_compile_from fresh Empty)).
  Proof.
    intros label_matches fresh t Htrace.
    simpl in Htrace.
    inversion Htrace; subst; simpl in *; try contradiction; lia.
  Qed.

  Lemma sss_compile_eps_complete_from :
    forall label_matches fresh t,
      sss_valid_trace
        label_matches
        (sss_edges (sss_compile_from fresh Eps))
        (sss_start (sss_compile_from fresh Eps))
        t
        (sss_final (sss_compile_from fresh Eps)) ->
      sss_trace_word t = [].
  Proof.
    intros label_matches fresh t Htrace.
    simpl in Htrace.
    inversion Htrace as [q| p l q r t' Hedge Hmatch Htail]; subst.
    - lia.
    - simpl in Hedge.
      destruct Hedge as [Hedge | []].
      inversion Hedge; subst. simpl.
      destruct
        (sss_valid_trace_no_edges_from
           label_matches
           [(fresh, None, S fresh)]
           (S fresh) t' (S fresh))
        as [Ht' _].
      + intros l q' Hin.
        simpl in Hin. destruct Hin as [Hin | []].
        inversion Hin; lia.
      + exact Htail.
      + now rewrite Ht'.
  Qed.

  Lemma sss_compile_atom_complete_from :
    forall label_matches fresh a t,
      sss_valid_trace
        label_matches
        (sss_edges (sss_compile_from fresh (Atom a)))
        (sss_start (sss_compile_from fresh (Atom a)))
        t
        (sss_final (sss_compile_from fresh (Atom a))) ->
      sss_trace_word t = [a].
  Proof.
    intros label_matches fresh a t Htrace.
    simpl in Htrace.
    inversion Htrace as [q| p l q r t' Hedge Hmatch Htail]; subst.
    - lia.
    - simpl in Hedge.
      destruct Hedge as [Hedge | []].
      inversion Hedge; subst. simpl.
      destruct
        (sss_valid_trace_no_edges_from
           label_matches
           [(fresh, Some a, S fresh)]
           (S fresh) t' (S fresh))
        as [Ht' _].
      + intros l q' Hin.
        simpl in Hin. destruct Hin as [Hin | []].
        inversion Hin; lia.
      + exact Htail.
      + now rewrite Ht'.
  Qed.

  (** Complete direction for boundary-aware SSS fragments. *)
  Lemma sss_compile_between_complete :
    forall label_matches fresh start final r t,
      label_matches_reflects_eq label_matches ->
      start < fresh ->
      final < fresh ->
      start <> final ->
      sss_valid_trace
        label_matches
        (sss_edges (sss_compile_between fresh start final r))
        start t final ->
      matches r (sss_trace_word t).
  Proof.
    intros label_matches fresh start final r.
    revert fresh start final.
    induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH];
      intros fresh start final t Hreflect Hstart Hfinal Hneq Htrace; simpl in Htrace.
    - inversion Htrace; subst; simpl in *; try contradiction; lia.
    - inversion Htrace as [q| p l q r' t' Hedge Hmatch Htail]; subst.
      + contradiction.
      + simpl in Hedge. destruct Hedge as [Hedge | []].
        inversion Hedge; subst. simpl.
        destruct
          (sss_valid_trace_no_edges_from
             label_matches [(start, None, q)] q t' q)
          as [Ht' _].
        * intros l q' Hin. simpl in Hin.
          destruct Hin as [Hin | []]. inversion Hin; subst; contradiction.
        * exact Htail.
        * rewrite Ht'. constructor.
    - inversion Htrace as [q| p l q r' t' Hedge Hmatch Htail]; subst.
      + contradiction.
      + simpl in Hedge. destruct Hedge as [Hedge | []].
        inversion Hedge; subst. simpl.
        destruct
          (sss_valid_trace_no_edges_from
             label_matches [(start, Some a, q)] q t' q)
          as [Ht' _].
        * intros l q' Hin. simpl in Hin.
          destruct Hin as [Hin | []]. inversion Hin; subst; contradiction.
        * exact Htail.
        * rewrite Ht'. constructor.
    - set (f1 := sss_compile_between fresh start final r1) in *.
      set (r2_start := sss_next f1) in *.
      set (r2_final := S r2_start) in *.
      set (f2 := sss_compile_between (S (S r2_start)) r2_start r2_final r2) in *.
      pose proof (sss_compile_between_next_ge fresh start final r1) as Hn1_alt.
      fold f1 in Hn1_alt. fold r2_start in Hn1_alt.
      change
        (sss_valid_trace label_matches
           (sss_edges f1 ++
            [sss_edge start None r2_start;
             sss_edge r2_final None final] ++
            sss_edges f2)
           start t final) in Htrace.
      destruct t as [| [[src l0] dst] tail].
      + apply sss_valid_trace_nil_inv in Htrace. contradiction.
      + apply sss_valid_trace_cons_inv in Htrace as
          [l [q [Hedge_eq [Hedge [Hmatch Htail]]]]].
        inversion Hedge_eq; subst src l0 dst.
        apply in_app_or in Hedge as [Hedge1 | Hedge_rest].
        * assert (Hq_owned :
            sss_owned_state fresh start final (sss_next f1) q).
          {
            destruct
              (sss_compile_between_edge_owned
                 fresh start final r1 start l q Hstart Hfinal Hedge1)
              as [_ Hdst].
            fold f1 in Hdst. exact Hdst.
          }
          assert (Hq_not_start : q <> start).
          {
            intro Hq. subst q.
            eapply sss_compile_between_no_edge_to_start
              with (fresh := fresh) (start := start) (final := final)
                   (r := r1) (p := start) (l := l); eauto.
          }
          assert
            (Htail1 :
              sss_valid_trace label_matches (sss_edges f1) q tail final).
          {
            eapply sss_valid_trace_inside with
              (full_edges :=
                sss_edges f1 ++
                [sss_edge start None r2_start;
                 sss_edge r2_final None final] ++
                sss_edges f2)
              (inside :=
                fun x =>
                  sss_owned_state fresh start final (sss_next f1) x /\
                  x <> start).
            - intros x lx y [Hx_owned Hx_ne] Hin.
              apply in_app_or in Hin as [Hin | Hin].
              + exact Hin.
              + destruct Hin as [Hbridge | [Hexit | Hin]].
                * pose proof (f_equal sss_edge_src Hbridge) as Hsrc.
                  simpl in Hsrc. subst x. contradiction.
                * pose proof (f_equal sss_edge_src Hexit) as Hsrc.
                  simpl in Hsrc.
                  subst x. unfold sss_owned_state, r2_final, r2_start in Hx_owned.
                  destruct Hx_owned as [Hx | [Hx | Hx]]; lia.
                * assert (Hr2s : r2_start < S (S r2_start)) by lia.
                  assert (Hr2f : r2_final < S (S r2_start)) by lia.
                  destruct
                    (sss_compile_between_edge_owned
                       (S (S r2_start)) r2_start r2_final r2
                       x lx y Hr2s Hr2f Hin)
                    as [Hsrc_owned _].
                  unfold sss_owned_state in Hx_owned, Hsrc_owned. lia.
            - intros x lx y Hin.
              split.
              + destruct
                  (sss_compile_between_edge_owned
                     fresh start final r1 x lx y Hstart Hfinal Hin)
                  as [_ Hdst].
                fold f1 in Hdst. exact Hdst.
              + intro Hy.
                subst y.
                eapply sss_compile_between_no_edge_to_start
                  with (fresh := fresh) (start := start) (final := final)
                       (r := r1) (p := x) (l := lx); eauto.
            - split; assumption.
            - exact Htail.
          }
          apply M_AltL.
          assert
            (Hvalid1 :
              sss_valid_trace label_matches (sss_edges f1)
                start (((start, l), q) :: tail) final).
          { econstructor; eauto. }
          exact (IH1 fresh start final (((start, l), q) :: tail)
                   Hreflect Hstart Hfinal Hneq Hvalid1).
        * destruct Hedge_rest as [Hbridge | [Hexit | Hedge2]].
          -- pose proof (f_equal sss_edge_dst Hbridge) as Hdst.
             pose proof (f_equal sss_edge_label Hbridge) as Hlab.
             simpl in Hdst, Hlab. subst q l.
             destruct
               (sss_valid_trace_exit_decompose
                  label_matches
                  (sss_edges f1 ++
                   [sss_edge start None r2_start;
                    sss_edge r2_final None final] ++
                   sss_edges f2)
                  (sss_edges f2)
                  (fun x =>
                    sss_owned_state (S (S r2_start))
                      r2_start r2_final (sss_next f2) x)
                  r2_final None final r2_start tail)
               as [t2 [Htail_eq Hvalid2]].
             ++ intros x lx y Hx_owned Hin.
                apply in_app_or in Hin as [Hin | Hin].
                ** destruct
                     (sss_compile_between_edge_owned
                        fresh start final r1 x lx y Hstart Hfinal Hin)
                     as [Hsrc_owned _].
                   fold f1 in Hsrc_owned.
                   unfold sss_owned_state in Hx_owned, Hsrc_owned. lia.
                ** destruct Hin as [Hbr | [Hex | Hin]].
                   --- pose proof (f_equal sss_edge_src Hbr) as Hsrc.
                       simpl in Hsrc.
                       unfold sss_owned_state in Hx_owned. lia.
                   --- pose proof (f_equal sss_edge_src Hex) as Hsrc.
                       pose proof (f_equal sss_edge_dst Hex) as Hdst.
                       pose proof (f_equal sss_edge_label Hex) as Hlabel.
                       simpl in Hsrc, Hdst, Hlabel.
                       right. repeat split; congruence.
                   --- left. exact Hin.
             ++ intros x lx y Hin.
                destruct
                  (sss_compile_between_edge_owned
                     (S (S r2_start)) r2_start r2_final r2
                     x lx y)
                  as [_ Hdst_owned]; try lia; eauto.
             ++ intros lx y Hin.
                 eapply sss_compile_between_no_edge_from_final
                   with (fresh := fresh) (start := start) (final := final)
                        (r := Alt r1 r2) (l := lx) (q := y); eauto.
             ++ unfold sss_owned_state. lia.
             ++ unfold sss_owned_state. auto.
             ++ exact Htail.
             ++ rewrite Htail_eq. simpl.
                rewrite sss_trace_word_app. simpl. rewrite app_nil_r.
                apply M_AltR.
                eapply IH2; try exact Hvalid2; try exact Hreflect; try lia.
          -- pose proof (f_equal sss_edge_src Hexit) as Hsrc.
             simpl in Hsrc. lia.
          -- assert (Hr2s : r2_start < S (S r2_start)) by lia.
             assert (Hr2f : r2_final < S (S r2_start)) by lia.
             destruct
               (sss_compile_between_edge_owned
                  (S (S r2_start)) r2_start r2_final r2
                  start l q Hr2s Hr2f Hedge2)
               as [Hsrc_owned _].
             unfold sss_owned_state in Hsrc_owned. lia.
    - set (mid := fresh) in *.
      set (f1 := sss_compile_between (S fresh) start mid r1) in *.
      set (f2 := sss_compile_between (sss_next f1) mid final r2) in *.
      change
        (sss_valid_trace label_matches (sss_edges f1 ++ sss_edges f2)
           start t final) in Htrace.
      destruct
        (sss_valid_trace_shared_decompose
           label_matches
           (sss_edges f1 ++ sss_edges f2)
           (sss_edges f1)
           (sss_edges f2)
           (fun x =>
             sss_owned_state (S fresh) start mid (sss_next f1) x)
           (fun x =>
             sss_owned_state (sss_next f1) mid final (sss_next f2) x)
           mid start t final)
        as [t1 [t2 [Ht [Hvalid1 Hvalid2]]]].
      + intros x lx y Hx_owned Hx_not_mid Hin.
        apply in_app_or in Hin as [Hin | Hin].
        * exact Hin.
        * assert (Hfresh2 : mid < sss_next f1) by
            (subst mid;
             pose proof
               (sss_compile_between_next_ge (S fresh) start fresh r1)
               as Hn1cat;
             change (S fresh <= sss_next f1) in Hn1cat; lia).
          assert (Hfinal2 : final < sss_next f1) by lia.
          destruct
            (sss_compile_between_edge_owned
               (sss_next f1) mid final r2 x lx y Hfresh2 Hfinal2 Hin)
            as [Hsrc_owned _].
          unfold sss_owned_state in Hx_owned, Hsrc_owned.
          subst mid. lia.
      + intros x lx y Hin.
        destruct
          (sss_compile_between_edge_owned
             (S fresh) start mid r1 x lx y)
          as [_ Hdst_owned]; try (subst mid; lia); eauto.
      + intros x lx y Hx_owned Hin.
        apply in_app_or in Hin as [Hin | Hin].
        * assert (Hstart1 : start < S fresh) by lia.
          assert (Hfinal1 : mid < S fresh) by (subst mid; lia).
          destruct (Nat.eq_dec x mid) as [Hx_mid | Hx_not_mid].
          -- subst x.
             exfalso.
             eapply sss_compile_between_no_edge_from_final
               with (fresh := S fresh) (start := start) (final := mid)
                    (r := r1) (l := lx) (q := y); eauto.
             subst mid; lia.
          -- destruct
               (sss_compile_between_edge_owned
                  (S fresh) start mid r1 x lx y Hstart1 Hfinal1 Hin)
               as [Hsrc_owned _].
             pose proof
               (sss_compile_between_next_ge (S fresh) start fresh r1)
               as Hn1cat.
             change (S fresh <= sss_next f1) in Hn1cat.
             fold f1 in Hsrc_owned.
             unfold sss_owned_state in Hx_owned, Hsrc_owned.
             subst mid.
             destruct Hx_owned as [Hx | [Hx | Hx]].
             ++ subst x.
                destruct Hsrc_owned as [Hs | [Hs | Hs]]; subst; lia.
             ++ subst x.
                destruct Hsrc_owned as [Hs | [Hs | Hs]]; subst; lia.
             ++ destruct Hsrc_owned as [Hs | [Hs | Hs]].
                ** subst x. lia.
                ** subst x. lia.
                ** destruct Hx as [Hx0 Hx1].
                   destruct Hs as [Hs0 Hs1].
                   exfalso. lia.
        * exact Hin.
      + intros x lx y Hin.
        assert (Hfresh2 : mid < sss_next f1) by
          (subst mid;
           pose proof
             (sss_compile_between_next_ge (S fresh) start fresh r1)
             as Hn1cat;
           change (S fresh <= sss_next f1) in Hn1cat; lia).
        assert (Hfinal2 : final < sss_next f1) by lia.
        destruct
          (sss_compile_between_edge_owned
             (sss_next f1) mid final r2 x lx y Hfresh2 Hfinal2 Hin)
          as [_ Hdst_owned].
        exact Hdst_owned.
      + unfold sss_owned_state. auto.
      + unfold sss_owned_state. auto.
      + unfold sss_owned_state. subst mid. lia.
      + exact Htrace.
      + rewrite Ht. rewrite sss_trace_word_app.
        apply M_Cat.
        * assert (Hstart1 : start < S fresh) by lia.
          assert (Hfinal1 : mid < S fresh) by (subst mid; lia).
          assert (Hneq1 : start <> mid) by (subst mid; lia).
          exact (IH1 (S fresh) start mid t1 Hreflect
                   Hstart1 Hfinal1 Hneq1 Hvalid1).
        * assert (Hfresh2 : mid < sss_next f1).
          {
            subst mid.
            pose proof
              (sss_compile_between_next_ge (S fresh) start fresh r1)
              as Hn1cat.
            change (S fresh <= sss_next f1) in Hn1cat. lia.
          }
          assert (Hfinal2 : final < sss_next f1) by lia.
          assert (Hneq2 : mid <> final) by (subst mid; lia).
          exact (IH2 (sss_next f1) mid final t2 Hreflect
                   Hfresh2 Hfinal2 Hneq2 Hvalid2).
    - set (body_start := fresh) in *.
      set (body_final := S fresh) in *.
      set (body :=
        sss_compile_between (S (S fresh)) body_start body_final r) in *.
      change
        (sss_valid_trace label_matches
           ([sss_edge start None body_start;
             sss_edge body_start None final;
             sss_edge body_final None body_start] ++
            sss_edges body)
           start t final) in Htrace.
      assert
        (Hloop :
          forall n tloop,
            length tloop <= n ->
            sss_valid_trace label_matches
              ([sss_edge start None body_start;
                sss_edge body_start None final;
                sss_edge body_final None body_start] ++
               sss_edges body)
              body_start tloop final ->
            matches (Star r) (sss_trace_word tloop)).
      {
        induction n as [n IHn] using lt_wf_ind.
        intros tloop Hlen Hloop_trace.
        destruct tloop as [| [[src l0] dst] tail].
        - apply sss_valid_trace_nil_inv in Hloop_trace.
          subst body_start. lia.
        - apply sss_valid_trace_cons_inv in Hloop_trace as
            [l [q [Hedge_eq [Hedge [Hmatch Htail]]]]].
          inversion Hedge_eq; subst src l0 dst.
          simpl in Hedge.
          destruct Hedge as [Hstart_edge | [Hexit | [Hback | Hbody_edge]]].
          + pose proof (f_equal sss_edge_src Hstart_edge) as Hsrc.
            simpl in Hsrc. subst body_start. lia.
          + pose proof (f_equal sss_edge_dst Hexit) as Hdst.
            pose proof (f_equal sss_edge_label Hexit) as Hlabel.
            simpl in Hdst, Hlabel. subst q l.
            destruct
              (sss_valid_trace_no_edges_from
                 label_matches
                 ([sss_edge start None body_start;
                   sss_edge body_start None final;
                   sss_edge body_final None body_start] ++
                  sss_edges body)
                 final tail final)
              as [Htail_nil _].
            * intros lx y Hin.
              eapply sss_compile_between_no_edge_from_final
                with (fresh := fresh) (start := start) (final := final)
                     (r := Star r) (l := lx) (q := y); eauto.
            * exact Htail.
            * rewrite Htail_nil. constructor.
          + pose proof (f_equal sss_edge_src Hback) as Hsrc.
            simpl in Hsrc. subst body_start body_final. lia.
          + assert (Hq_owned :
              sss_owned_state (S (S fresh)) body_start body_final
                (sss_next body) q).
            {
              destruct
                (sss_compile_between_edge_owned
                   (S (S fresh)) body_start body_final r
                   body_start l q)
                as [_ Hdst_owned]; try (subst body_start body_final; lia); eauto.
            }
            assert (Hq_not_start : q <> body_start).
            {
              intro Hq. subst q.
              eapply sss_compile_between_no_edge_to_start
                with (fresh := S (S fresh)) (start := body_start)
                     (final := body_final) (r := r)
                     (p := body_start) (l := l); eauto;
                subst body_start body_final; lia.
            }
            destruct
              (sss_valid_trace_exit_prefix_decompose
                 label_matches
                 ([sss_edge start None body_start;
                   sss_edge body_start None final;
                   sss_edge body_final None body_start] ++
                  sss_edges body)
                 (sss_edges body)
                 (fun x =>
                   sss_owned_state (S (S fresh)) body_start body_final
                     (sss_next body) x /\ x <> body_start)
                 body_final None body_start q tail final)
              as [tbody_tail [trest [Htail_eq [Hbody_tail Hrest]]]].
            * intros x lx y [Hx_owned Hx_ne] Hin.
              simpl in Hin.
              destruct Hin as [Houter | [Hdirect | [Hloop_back | Hin]]].
              -- pose proof (f_equal sss_edge_src Houter) as Hsrc.
                 simpl in Hsrc. subst x.
                 unfold sss_owned_state, body_start, body_final in Hx_owned.
                 destruct Hx_owned as [Hx | [Hx | Hx]]; lia.
              -- pose proof (f_equal sss_edge_src Hdirect) as Hsrc.
                 simpl in Hsrc. subst x. contradiction.
              -- pose proof (f_equal sss_edge_src Hloop_back) as Hsrc.
                 pose proof (f_equal sss_edge_dst Hloop_back) as Hdst.
                 pose proof (f_equal sss_edge_label Hloop_back) as Hlabel.
                 simpl in Hsrc, Hdst, Hlabel.
                 right. repeat split; congruence.
              -- left. exact Hin.
            * intros x lx y Hin.
              split.
              -- destruct
                   (sss_compile_between_edge_owned
                      (S (S fresh)) body_start body_final r x lx y)
                   as [_ Hdst_owned]; try (subst body_start body_final; lia); eauto.
              -- intro Hy. subst y.
                 eapply sss_compile_between_no_edge_to_start
                   with (fresh := S (S fresh)) (start := body_start)
                        (final := body_final) (r := r)
                        (p := x) (l := lx); eauto;
                   subst body_start body_final; lia.
            * unfold sss_owned_state. subst body_start body_final. lia.
            * split; assumption.
            * exact Htail.
            * set (tbody := ((body_start, l), q) :: tbody_tail).
              assert
                (Hbody_valid :
                  sss_valid_trace label_matches (sss_edges body)
                    body_start tbody body_final).
              {
                unfold tbody. econstructor; eauto.
              }
              assert (Hbody_match : matches r (sss_trace_word tbody)).
              {
                eapply IH; try exact Hbody_valid; try exact Hreflect;
                  subst body_start body_final; lia.
              }
              assert (Hrest_match : matches (Star r) (sss_trace_word trest)).
              {
                assert (Htrest_lt : length trest < n).
                {
                  rewrite Htail_eq in Hlen.
                  simpl in Hlen.
                  repeat rewrite length_app in Hlen.
                  simpl in Hlen. lia.
                }
                exact (IHn (length trest) Htrest_lt trest
                         (le_n (length trest)) Hrest).
              }
              assert
                (Hword_loop :
                  sss_trace_word (((body_start, l), q) :: tail) =
                  sss_trace_word tbody ++ sss_trace_word trest).
              {
                rewrite Htail_eq. unfold tbody. simpl.
                destruct l as [a0|];
                  rewrite !sss_trace_word_app; simpl;
                  try rewrite app_nil_r; reflexivity.
              }
              rewrite Hword_loop.
              destruct (sss_trace_word tbody) as [| b wbody] eqn:Hbody_word.
              -- exact Hrest_match.
              -- eapply M_StarApp.
                 ++ exact Hbody_match.
                 ++ discriminate.
                 ++ exact Hrest_match.
      }
      destruct t as [| [[src l0] dst] tail].
      + apply sss_valid_trace_nil_inv in Htrace. contradiction.
      + apply sss_valid_trace_cons_inv in Htrace as
          [l [q [Hedge_eq [Hedge [Hmatch Htail]]]]].
        inversion Hedge_eq; subst src l0 dst.
        simpl in Hedge.
        destruct Hedge as [Henter | [Hexit | [Hback | Hbody_edge]]].
        * pose proof (f_equal sss_edge_dst Henter) as Hdst.
          pose proof (f_equal sss_edge_label Henter) as Hlabel.
          simpl in Hdst, Hlabel. subst q l.
          simpl. eapply Hloop with (n := length tail); eauto; lia.
        * pose proof (f_equal sss_edge_src Hexit) as Hsrc.
          simpl in Hsrc. subst body_start. lia.
        * pose proof (f_equal sss_edge_src Hback) as Hsrc.
          simpl in Hsrc. subst body_final. lia.
        * destruct
            (sss_compile_between_edge_owned
               (S (S fresh)) body_start body_final r start l q)
            as [Hsrc_owned _]; try (subst body_start body_final; lia); eauto.
          unfold sss_owned_state in Hsrc_owned. subst body_start body_final. lia.
  Qed.

  Lemma sss_compile_complete_from_len :
    forall n label_matches fresh r t,
      length t <= n ->
      label_matches_reflects_eq label_matches ->
      sss_valid_trace
        label_matches
        (sss_edges (sss_compile_from fresh r))
        (sss_start (sss_compile_from fresh r))
        t
        (sss_final (sss_compile_from fresh r)) ->
      matches r (sss_trace_word t).
  Proof.
    intros n label_matches fresh r t _ Hreflect Htrace.
    unfold sss_compile_from in Htrace.
    rewrite sss_compile_between_start_eq in Htrace.
    rewrite sss_compile_between_final_eq in Htrace.
    eapply sss_compile_between_complete; try exact Htrace; try exact Hreflect; lia.
  Qed.

  Theorem sss_compile_complete_from :
    forall label_matches fresh r t,
      label_matches_reflects_eq label_matches ->
      sss_valid_trace
        label_matches
        (sss_edges (sss_compile_from fresh r))
        (sss_start (sss_compile_from fresh r))
        t
        (sss_final (sss_compile_from fresh r)) ->
      matches r (sss_trace_word t).
  Proof.
    intros label_matches fresh r t Hreflect Htrace.
    eapply sss_compile_complete_from_len with (n := length t);
      eauto; lia.
  Qed.

  (** Msss -> Regex complete direction and base-case entry points. *)
  Theorem regex_Msss_language_complete_empty :
    forall alphabet label_matches,
      label_matches_reflects_eq label_matches ->
      regex_Msss_language_complete_spec alphabet label_matches Empty.
  Proof.
    intros alphabet label_matches Hreflect w Hacc.
    destruct
      (regex_Msss_accepts_word_sss_trace
         alphabet label_matches Empty w Hreflect Hacc)
      as [t [Htrace _]].
    exfalso.
    eapply sss_compile_empty_complete_from; exact Htrace.
  Qed.

  Theorem regex_Msss_language_complete_eps :
    forall alphabet label_matches,
      label_matches_reflects_eq label_matches ->
      regex_Msss_language_complete_spec alphabet label_matches Eps.
  Proof.
    intros alphabet label_matches Hreflect w Hacc.
    destruct
      (regex_Msss_accepts_word_sss_trace
         alphabet label_matches Eps w Hreflect Hacc)
      as [t [Htrace Hword]].
    pose proof (sss_compile_eps_complete_from label_matches 0 t Htrace)
      as Hempty.
    rewrite <- Hword. rewrite Hempty. constructor.
  Qed.

  Theorem regex_Msss_language_complete_atom :
    forall alphabet label_matches a,
      label_matches_reflects_eq label_matches ->
      regex_Msss_language_complete_spec alphabet label_matches (Atom a).
  Proof.
    intros alphabet label_matches a Hreflect w Hacc.
    destruct
      (regex_Msss_accepts_word_sss_trace
         alphabet label_matches (Atom a) w Hreflect Hacc)
      as [t [Htrace Hword]].
    pose proof (sss_compile_atom_complete_from label_matches 0 a t Htrace)
      as Hatom.
    rewrite <- Hword. rewrite Hatom. constructor.
  Qed.

  Theorem regex_Msss_language_complete :
    forall alphabet label_matches r,
      label_matches_reflects_eq label_matches ->
      regex_Msss_language_complete_spec alphabet label_matches r.
  Proof.
    intros alphabet label_matches r Hreflect w Hacc.
    destruct
      (regex_Msss_accepts_word_sss_trace
         alphabet label_matches r w Hreflect Hacc)
      as [t [Htrace Hword]].
    unfold sss_compile in Htrace.
    pose proof
      (sss_compile_complete_from label_matches 0 r t Hreflect Htrace)
      as Hmatch.
    now rewrite Hword in Hmatch.
  Qed.

  (** Final language equivalence entry point for Definition 7. *)
  Theorem regex_Msss_language_equiv_from_specs :
    forall alphabet label_matches r,
      regex_Msss_language_sound_spec alphabet label_matches r ->
      regex_Msss_language_complete_spec alphabet label_matches r ->
      forall w,
        matches r w <->
        enfa_accepts_word (regex_Msss alphabet label_matches r) w.
  Proof.
    intros alphabet label_matches r Hsound Hcomplete w.
    split; auto.
  Qed.

  (** General [Msss] language-correctness theorem. *)
  Theorem regex_Msss_language_equiv :
    forall alphabet label_matches r w,
      label_matches_reflects_eq label_matches ->
      matches r w <->
      enfa_accepts_word (regex_Msss alphabet label_matches r) w.
  Proof.
    intros alphabet label_matches r w Hreflect.
    eapply regex_Msss_language_equiv_from_specs.
    - now apply regex_Msss_language_sound.
    - now apply regex_Msss_language_complete.
  Qed.

  Theorem regex_Msss_language_equiv_empty :
    forall alphabet label_matches w,
      label_matches_reflects_eq label_matches ->
      matches Empty w <->
      enfa_accepts_word (regex_Msss alphabet label_matches Empty) w.
  Proof.
    intros alphabet label_matches w Hreflect.
    eapply regex_Msss_language_equiv_from_specs.
    - now apply regex_Msss_language_sound.
    - now apply regex_Msss_language_complete_empty.
  Qed.

  Theorem regex_Msss_language_equiv_eps :
    forall alphabet label_matches w,
      label_matches_reflects_eq label_matches ->
      matches Eps w <->
      enfa_accepts_word (regex_Msss alphabet label_matches Eps) w.
  Proof.
    intros alphabet label_matches w Hreflect.
    eapply regex_Msss_language_equiv_from_specs.
    - now apply regex_Msss_language_sound.
    - now apply regex_Msss_language_complete_eps.
  Qed.

  Theorem regex_Msss_language_equiv_atom :
    forall alphabet label_matches a w,
      label_matches_reflects_eq label_matches ->
      matches (Atom a) w <->
      enfa_accepts_word (regex_Msss alphabet label_matches (Atom a)) w.
  Proof.
    intros alphabet label_matches a w Hreflect.
    eapply regex_Msss_language_equiv_from_specs.
    - now apply regex_Msss_language_sound.
    - now apply regex_Msss_language_complete_atom.
  Qed.

End RegexSSS.
