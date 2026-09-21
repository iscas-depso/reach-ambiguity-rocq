# reach-ambiguity

This repository contains the Rocq formalization of the reach-ambiguity results in the paper
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

On Windows PowerShell, do not invoke bare `dune build` from the repository
root: the root-level Dune configuration file is also named `dune`, and
PowerShell may resolve that file instead of `dune.exe`. Use the command above
or `dune.exe build` explicitly.

The `_CoqProject` path is also maintained for direct Rocq checks:

```sh
make coq
```

`make coq` deliberately keeps the generated `.vo` files under `theories/` so
that VSCoq can resolve imported modules during interactive Ctrl+Down checking.
Remove them explicitly with `make clean-coq-generated` (or `make clean`) when
they are no longer needed.

## Repository Layout

Rocq sources live under `theories/` and use qualified logical paths such as
`PositionAutomata.Core.Syntax` and `PositionAutomata.Relations.AmbiguityLR`.

```text
theories/
  Core/        syntax, finite-list set utilities, graph algorithms
  Automata/    position automata, epsilon NFAs, equivalence, correctness lemmas
  Ambiguity/   ambiguity-degree machinery
  Regex/       regex semantics, ReDoS checks, SSS construction, reach examples
  Grammar/     right-linear grammar, CFG, and Gamma construction facts
  Relations/   ambiguity/LR relations, paper-facing index, examples
  Demos/       executable examples and small sanity checks
  Experiments/ local computation probes, excluded from the default build
  Interop/     optional bridge code, excluded from the default build
```

The paper-facing entry point is:

```text
theories/Relations/FormalizationIndex.v
```

This file indexes the paper-facing definitions, lemmas, and theorems by
mathematical subject and points to the underlying Rocq proofs.

## Useful Commands

```sh
make
make coq
make clean-coq-generated
make clean
opam exec -- dune clean
opam exec -- dune build --cache=disabled
```

Common proof-hygiene checks:

```sh
rg -n "Admitted|Axiom|admit|TODO|Abort" --glob "*.v" theories
rg -n "reach_ambiguity_|formalization_" --glob "*.v" theories
```

## License

This Rocq formalization is released under the MIT License. See [LICENSE](LICENSE).
