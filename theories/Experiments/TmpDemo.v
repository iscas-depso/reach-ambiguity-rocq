From Stdlib Require Import List Bool.
Import ListNotations.

From PositionAutomata.Ambiguity Require Import DegreeofInfiniteAmbiguity.
From PositionAutomata.Regex Require Import RegexReDoS.
From PositionAutomata.Demos Require Import Examples.

Eval vm_compute in degree_growthb ida_example_nfa.
Eval vm_compute in ida_degree_lower_boundb ida_example_nfa.
Eval vm_compute in edab_graph ida_example_nfa.
Eval vm_compute in idab_graph ida_example_nfa.
Eval vm_compute in ida_db_graph 1 ida_example_nfa.

Eval vm_compute in regex_degree_growthb [true; false] Bool.eqb a_then_b.
Eval vm_compute in regex_degree_growthb [true] Bool.eqb ambiguous_a_star.
Eval vm_compute in regex_redosb_at_least (PolynomialAmbiguity 1) [true] Bool.eqb ambiguous_a_star.
Eval vm_compute in regex_exponential_redosb [true] Bool.eqb ambiguous_a_star.