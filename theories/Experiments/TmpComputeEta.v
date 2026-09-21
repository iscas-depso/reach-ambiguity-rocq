From PositionAutomata.Demos Require Import FolianceExamples.
From PositionAutomata.Regex Require Import FolianceProperties.

Eval vm_compute in
  (eta_prefix_max foliance_demo_nfa_4 foliance_demo_attack_2).

Eval vm_compute in
  (eta_prefix_max
     (regex_foliance_nfa
        foliance_demo_alphabet
        foliance_demo_label_matches
        foliance_demo_regex_300)
     foliance_demo_attack_150).
