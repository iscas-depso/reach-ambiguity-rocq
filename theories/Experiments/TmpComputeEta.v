From PositionAutomata.Demos Require Import PaperExamples.
From PositionAutomata.Regex Require Import ReachAmbiguityDrance.

Eval vm_compute in
  (eta_prefix_max paper_example1_nfa_4 paper_example1_attack_2).

Eval vm_compute in
  (eta_prefix_max
     (regex_drance_nfa
        paper_alphabet
        paper_label_matches
        paper_example1_regex_300)
     paper_example1_attack_150).
