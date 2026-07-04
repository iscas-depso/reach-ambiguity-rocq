# reach-ambiguity

This repository contains the Rocq formalization for Section 4 of the paper
`Ambiguity, LR(1), and ReDoS Detection`.

The development formalizes the definitions and proof structure around
reach-ambiguity, ambiguity measures, epsilon NFAs, right-linear grammars, the
Gamma construction, and the LR(1)-oriented results used in Section 4.

## Build

The default build uses Dune:

```sh
make
```

Equivalent direct command:

```sh
opam exec -- dune build
```

The `_CoqProject` path is also maintained for direct Rocq checks:

```sh
make coq
```

## Repository Layout

Rocq sources live under `theories/` and use qualified logical paths such as
`PositionAutomata.Core.Syntax` and `PositionAutomata.Section4.Section4LR`.

```text
theories/
  Core/        syntax, finite-list set utilities, graph algorithms
  Automata/    position automata, epsilon NFAs, equivalence, correctness lemmas
  Ambiguity/   ambiguity-degree machinery
  Regex/       regex semantics, ReDoS checks, SSS construction, reach examples
  Grammar/     right-linear grammar, CFG, and Gamma construction facts
  Section4/    Section 4 theorem layer, paper-order aliases, examples
  Demos/       executable examples and small sanity checks
  Experiments/ local computation probes, excluded from the default build
  Interop/     optional bridge code, excluded from the default build
```

The paper-facing entry point is:

```text
theories/Section4/Section4PaperOrder.v
```

This file indexes the Section 4 definitions, lemmas, and theorems in paper
order and points to the underlying Rocq proofs.

## Useful Commands

```sh
make
make coq
make clean
```

Common proof-hygiene checks:

```sh
rg -n "Admitted|Axiom|admit|TODO|Abort" --glob "*.v" theories
rg -n "section4_definition|section4_theorem|section4_lemma" --glob "*.v" theories
rg -n "paper_theorem|paper_lemma|paper_definition|paper_support" --glob "*.v" theories
```
