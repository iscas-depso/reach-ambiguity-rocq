From Linden Require Import Regex Chars.
From Warblre Require Import Numeric.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Automata Require Import PositionAutomaton.

Section LindenBridge.

  Definition linden_regex := regex char_descr.
  Definition linden_positioned_regex := positioned_regex char_descr.

  (** This module is intentionally small for now.  It fixes the intended
      alphabet type and imports the Linden/Warblre dependencies so later files
      can define a translation from Linden regexes to [linden_regex].  The
      generic [label] pass then produces [linden_positioned_regex] for the
      position-automaton construction. *)
End LindenBridge.
